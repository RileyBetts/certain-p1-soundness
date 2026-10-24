import P1Soundness.SoundComposition

/-!
# Dropped sanctions bit

A payment plan that only records authorisation and release is safe in a
training workflow that does not require sanctions clearance, and unsafe in a
holdout workflow that does. Both workflows share the same transitions. The
abstract machine erases the clearance bit, so the two concrete states
`released false` and `released true` look identical.

If the abstract machine meets its obligations, no refinement contract from the
holdout machine can exist: `obligations_transfer` would make the holdout safe.
-/

inductive Pay
  | start
  | auth (cleared : Bool)
  | rel (cleared : Bool)
  deriving DecidableEq

inductive AbsPay
  | start
  | auth
  | rel
  deriving DecidableEq

instance : Fintype Pay where
  elems := {Pay.start, Pay.auth false, Pay.auth true, Pay.rel false, Pay.rel true}
  complete x := by
    cases x with
    | start => decide
    | auth cleared => cases cleared <;> decide
    | rel cleared => cases cleared <;> decide

instance : Fintype AbsPay where
  elems := {AbsPay.start, AbsPay.auth, AbsPay.rel}
  complete x := by
    cases x <;> decide

namespace Sanctions

def trainStepB : Pay → Pay → Bool
  | .start, .auth false => true
  | .auth false, .rel false => true
  | _, _ => false

def trainStep (s s' : Pay) : Prop :=
  trainStepB s s' = true

lemma train_start_auth : trainStep .start (.auth false) := by
  unfold trainStep trainStepB
  rfl

lemma train_auth_rel : trainStep (.auth false) (.rel false) := by
  unfold trainStep trainStepB
  rfl

def goal : Pay → Prop
  | .rel _ => True
  | _ => False

/-- Clearance is irrelevant in the training workflow. -/
def training : PlanningModel Pay where
  init s := s = .start
  step := trainStep
  safe _ := True
  goal := goal

/-- Release without clearance violates the holdout invariant. -/
def holdSafe : Pay → Prop
  | .rel cleared => cleared = true
  | _ => True

def holdout : PlanningModel Pay where
  init s := s = .start
  step := trainStep
  safe := holdSafe
  goal := goal

def erase : Pay → AbsPay
  | .start => .start
  | .auth _ => .auth
  | .rel _ => .rel

def absStepB : AbsPay → AbsPay → Bool
  | .start, .auth => true
  | .auth, .rel => true
  | _, _ => false

def absStep (s s' : AbsPay) : Prop :=
  absStepB s s' = true

lemma abs_start_auth : absStep .start .auth := by
  unfold absStep absStepB
  rfl

lemma abs_auth_rel : absStep .auth .rel := by
  unfold absStep absStepB
  rfl

def abstract : PlanningModel AbsPay where
  init s := s = .start
  step := absStep
  safe _ := True
  goal s := s = .rel

theorem erase_forgets_clearance :
    erase (.rel false) = erase (.rel true) :=
  rfl

lemma step_of {s s' : Pay} (h : trainStep s s') :
    (s = .start ∧ s' = .auth false) ∨ (s = .auth false ∧ s' = .rel false) := by
  cases s with
  | start =>
      cases s' with
      | auth cleared =>
          cases cleared
          · exact Or.inl ⟨rfl, rfl⟩
          · simp [trainStep, trainStepB] at h
      | start => simp [trainStep, trainStepB] at h
      | rel _ => simp [trainStep, trainStepB] at h
  | auth cleared =>
      cases cleared with
      | false =>
          cases s' with
          | rel c =>
              cases c
              · exact Or.inr ⟨rfl, rfl⟩
              · simp [trainStep, trainStepB] at h
          | start => simp [trainStep, trainStepB] at h
          | auth _ => simp [trainStep, trainStepB] at h
      | true => simp [trainStep, trainStepB] at h
  | rel _ => simp [trainStep, trainStepB] at h

lemma absStep_of {s s' : AbsPay} (h : absStep s s') :
    (s = .start ∧ s' = .auth) ∨ (s = .auth ∧ s' = .rel) := by
  cases s with
  | start =>
      cases s' with
      | auth => exact Or.inl ⟨rfl, rfl⟩
      | start => simp [absStep, absStepB] at h
      | rel => simp [absStep, absStepB] at h
  | auth =>
      cases s' with
      | rel => exact Or.inr ⟨rfl, rfl⟩
      | start => simp [absStep, absStepB] at h
      | auth => simp [absStep, absStepB] at h
  | rel => simp [absStep, absStepB] at h

lemma training_reach (s : Pay) :
    training.Reach .start s ↔
      s = .start ∨ s = .auth false ∨ s = .rel false := by
  constructor
  · intro h
    induction h with
    | refl => simp
    | tail _ hstep ih =>
        have hstep := step_of hstep
        rcases ih with rfl | rfl | rfl
        · rcases hstep with ⟨_, rfl⟩ | ⟨h, _⟩
          · simp
          · cases h
        · rcases hstep with ⟨h, _⟩ | ⟨_, rfl⟩
          · cases h
          · simp
        · rcases hstep with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
  · intro h
    rcases h with rfl | rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail .refl train_start_auth
    · exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail .refl train_start_auth) train_auth_rel

lemma abstract_reach (s : AbsPay) :
    abstract.Reach .start s ↔ s = .start ∨ s = .auth ∨ s = .rel := by
  constructor
  · intro h
    induction h with
    | refl => simp
    | tail _ hstep ih =>
        have hstep := absStep_of hstep
        rcases ih with rfl | rfl | rfl
        · rcases hstep with ⟨_, rfl⟩ | ⟨h, _⟩
          · simp
          · cases h
        · rcases hstep with ⟨h, _⟩ | ⟨_, rfl⟩
          · cases h
          · simp
        · rcases hstep with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
  · intro h
    rcases h with rfl | rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail .refl abs_start_auth
    · exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail .refl abs_start_auth) abs_auth_rel

theorem training_obligations : training.Obligations where
  safety := by
    intro _ _ _ _
    simp [training]
  goalAtTerminal := by
    intro s₀ s hs₀ hreach hterm
    have hs₀' : s₀ = .start := hs₀
    subst hs₀'
    have hs := (training_reach s).1 hreach
    have hclosed : ¬ (s = .start ∨ s = .auth false) := by
      intro hopen
      rcases hopen with rfl | rfl
      · exact hterm (.auth false) train_start_auth
      · exact hterm (.rel false) train_auth_rel
    rcases hs with rfl | rfl | rfl
    · exact absurd (Or.inl rfl) hclosed
    · exact absurd (Or.inr rfl) hclosed
    · simp [training, goal]

theorem holdout_unsafe : ¬ holdout.Obligations := by
  intro h
  have hreach : holdout.Reach .start (.rel false) :=
    (training_reach (.rel false)).2 (Or.inr (Or.inr rfl))
  have hsafe := h.safety .start (.rel false) rfl hreach
  simp [holdout, holdSafe] at hsafe

theorem abstract_obligations : abstract.Obligations where
  safety := by
    intro _ _ _ _
    simp [abstract]
  goalAtTerminal := by
    intro s₀ s hs₀ hreach hterm
    have hs₀' : s₀ = .start := hs₀
    subst hs₀'
    have hs := (abstract_reach s).1 hreach
    have hclosed : ¬ (s = .start ∨ s = .auth) := by
      intro hopen
      rcases hopen with rfl | rfl
      · exact hterm .auth abs_start_auth
      · exact hterm .rel abs_auth_rel
    rcases hs with rfl | rfl | rfl
    · exact absurd (Or.inl rfl) hclosed
    · exact absurd (Or.inr rfl) hclosed
    · simp [abstract]

/-- The holdout plan has no refinement contract into the safe abstract machine,
along any simulation. The erased clearance bit is safety-relevant. -/
theorem sanctions_no_refinement (R : Pay → AbsPay → Prop) :
    ¬ RefinementContract holdout abstract R := by
  intro h
  exact holdout_unsafe (obligations_transfer h abstract_obligations)

end Sanctions
