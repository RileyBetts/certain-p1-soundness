import P1Soundness.SoundComposition

open Certain Certain.Task

/-!
# Dropped sanctions bit

One payment policy `(T, I)`. `T` allows a cleared release and an uncleared release.
`I` says a release is safe only when sanctions are clear.

The training task and the holdout task are two cases of that task type.
They share the policy. The training task starts where sanctions are already clear,
so every reachable state satisfies `I`. The holdout task starts at the beginning,
so an uncleared release is reachable and `I` fails.

The abstract task erases the clearance bit. Its own invariant holds, and no
refinement contract from the holdout task to that abstract task exists:
`obligations_transfer` would make the holdout task safe.
-/

inductive Pay
  | start
  | auth (cleared : Bool)
  | rel (cleared : Bool)
  deriving DecidableEq

inductive PayAct
  | toAuth (cleared : Bool)
  | toRel
  deriving DecidableEq

inductive AbsPay
  | start
  | auth
  | rel
  deriving DecidableEq

inductive AbsAct
  | toAuth
  | toRel
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

def payTB : Pay → PayAct → Pay → Bool
  | .start, .toAuth c, .auth c' => c == c'
  | .auth c, .toRel, .rel c' => c == c'
  | _, _, _ => false

def payT (s : Pay) (a : PayAct) (s' : Pay) : Prop :=
  payTB s a s' = true

lemma pay_start_auth (c : Bool) : payT .start (.toAuth c) (.auth c) := by
  cases c <;> rfl

lemma pay_auth_rel (c : Bool) : payT (.auth c) .toRel (.rel c) := by
  cases c <;> rfl

/-- Release is safe only when sanctions are clear. -/
def payI : Pay → Prop
  | .rel cleared => cleared = true
  | _ => True

def paymentPolicy : Policy Pay PayAct where
  T := payT
  I := payI

def released : Pay → Prop
  | .rel _ => True
  | _ => False

/-- Same policy as the holdout. Starts where clearance is already known. -/
def training : Task Pay PayAct where
  taskType := .payments
  policy := paymentPolicy
  start := .auth true
  goal := released

/-- Same policy as training. Starts at the beginning, so uncleared release is reachable. -/
def holdout : Task Pay PayAct where
  taskType := .payments
  policy := paymentPolicy
  start := .start
  goal := released

theorem shared_payment_policy : training.policy = holdout.policy := rfl

theorem shared_task_type :
    training.taskType = TaskType.payments ∧ holdout.taskType = TaskType.payments :=
  ⟨rfl, rfl⟩

def erase : Pay → AbsPay
  | .start => .start
  | .auth _ => .auth
  | .rel _ => .rel

def absTB : AbsPay → AbsAct → AbsPay → Bool
  | .start, .toAuth, .auth => true
  | .auth, .toRel, .rel => true
  | _, _, _ => false

def absT (s : AbsPay) (a : AbsAct) (s' : AbsPay) : Prop :=
  absTB s a s' = true

lemma abs_start_auth : absT .start .toAuth .auth := rfl

lemma abs_auth_rel : absT .auth .toRel .rel := rfl

/-- The coarse task drops the clearance bit and treats every state as safe. -/
def abstract : Task AbsPay AbsAct where
  taskType := .payments
  policy := { T := absT, I := fun _ => True }
  start := .start
  goal := fun s => s = .rel

theorem erase_forgets_clearance :
    erase (.rel false) = erase (.rel true) :=
  rfl

lemma payT_auth {c : Bool} {a : PayAct} {s : Pay} (h : payT (.auth c) a s) :
    a = .toRel ∧ s = .rel c := by
  cases a <;> cases s <;> simp [payT, payTB] at h
  subst h
  exact ⟨rfl, rfl⟩

lemma payT_rel {c : Bool} {a : PayAct} {s : Pay} (h : payT (.rel c) a s) : False := by
  cases c <;> cases a <;> cases s <;> unfold payT payTB at h <;> simp at h

lemma training_reach (s : Pay) :
    ReachFrom training.policy training.start s ↔
      s = .auth true ∨ s = .rel true := by
  constructor
  · intro h
    induction h with
    | refl => simp [training]
    | tail _ hstep ih =>
        rcases ih with rfl | rfl
        · obtain ⟨a, ha⟩ := hstep
          obtain ⟨rfl, rfl⟩ := payT_auth ha
          simp
        · obtain ⟨a, ha⟩ := hstep
          exact (payT_rel ha).elim
  · intro h
    rcases h with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
        ⟨.toRel, pay_auth_rel true⟩

lemma absT_start {a : AbsAct} {s : AbsPay} (h : absT .start a s) :
    a = .toAuth ∧ s = .auth := by
  cases a <;> cases s <;> simp [absT, absTB] at h
  exact ⟨rfl, rfl⟩

lemma absT_auth {a : AbsAct} {s : AbsPay} (h : absT .auth a s) :
    a = .toRel ∧ s = .rel := by
  cases a <;> cases s <;> simp [absT, absTB] at h
  exact ⟨rfl, rfl⟩

lemma absT_rel {a : AbsAct} {s : AbsPay} (h : absT .rel a s) : False := by
  cases a <;> cases s <;> simp [absT, absTB] at h

lemma abstract_reach (s : AbsPay) :
    ReachFrom abstract.policy abstract.start s ↔
      s = .start ∨ s = .auth ∨ s = .rel := by
  constructor
  · intro h
    induction h with
    | refl => simp [abstract]
    | tail _ hstep ih =>
        rcases ih with rfl | rfl | rfl
        · obtain ⟨a, ha⟩ := hstep
          obtain ⟨rfl, rfl⟩ := absT_start ha
          simp
        · obtain ⟨a, ha⟩ := hstep
          obtain ⟨rfl, rfl⟩ := absT_auth ha
          simp
        · obtain ⟨a, ha⟩ := hstep
          exact (absT_rel ha).elim
  · intro h
    rcases h with rfl | rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl ⟨.toAuth, abs_start_auth⟩
    · exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail Relation.ReflTransGen.refl ⟨.toAuth, abs_start_auth⟩)
        ⟨.toRel, abs_auth_rel⟩

theorem training_obligations : Obligations training where
  safety := by
    intro s hreach
    have hs := (training_reach s).1 hreach
    rcases hs with rfl | rfl <;> simp [training, paymentPolicy, payI]
  goalAtTerminal := by
    intro s hreach hterm
    have hs := (training_reach s).1 hreach
    rcases hs with rfl | rfl
    · exact False.elim (hterm (.rel true) ⟨.toRel, pay_auth_rel true⟩)
    · simp [training, released]

theorem holdout_unsafe : ¬ Obligations holdout := by
  intro h
  have hreach : ReachFrom holdout.policy holdout.start (.rel false) :=
    Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail Relation.ReflTransGen.refl ⟨.toAuth false, pay_start_auth false⟩)
      ⟨.toRel, pay_auth_rel false⟩
  have hsafe := h.safety (.rel false) hreach
  simp [holdout, paymentPolicy, payI] at hsafe

theorem abstract_obligations : Obligations abstract where
  safety := by
    intro _ _ 
    simp [abstract]
  goalAtTerminal := by
    intro s hreach hterm
    have hs := (abstract_reach s).1 hreach
    have hclosed : ¬ (s = .start ∨ s = .auth) := by
      intro hopen
      rcases hopen with rfl | rfl
      · exact hterm .auth ⟨.toAuth, abs_start_auth⟩
      · exact hterm .rel ⟨.toRel, abs_auth_rel⟩
    rcases hs with rfl | rfl | rfl
    · exact absurd (Or.inl rfl) hclosed
    · exact absurd (Or.inr rfl) hclosed
    · simp [abstract]

/-- The holdout task has no refinement contract into the abstract task, along any
simulation. The erased clearance bit is part of the payment policy. -/
theorem sanctions_no_refinement (R : Pay → AbsPay → Prop) :
    ¬ RefinementContract holdout abstract R := by
  intro h
  exact holdout_unsafe (obligations_transfer h abstract_obligations)

end Sanctions
