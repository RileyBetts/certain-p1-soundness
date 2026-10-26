import Mathlib.Data.Fintype.Basic

/-!
# P1 — sound composition for a finite-state task

The objects follow the CERTAIN definitions.

* A task type is one kind of regulated decision.
* A policy is the pair `(T, I)`: legal moves and the safety invariant.
  Every task of a task type is checked against that policy.
* A task is one case of one task type. It fixes the starting state and the goal `G`.
  `G` is not the task and not the policy.
* A plan is a list of actions. A step is one action in a plan.
* A certificate is accepted or refused by the checker. The gate is separate:
  it decides whether a plan may be carried out, and it does not read the library.

The proof is restricted, as before:

* state spaces are finite (`Fintype`), so the development sits in the finite fragment;
* traces are finite;
* the goal of a task is required at terminal states of `T`
  (states with no legal action);
* a refinement contract is lockstep: one concrete action step is matched by
  exactly one abstract action step. Stuttering is not proved;
* `Γ` is the discharged assumptions (start correspondence, step matching, terminals).

Not proved: that a checker implements the contract, infinite traces, stuttering,
beliefs, or an unmodelled environment.
-/

universe u

namespace Certain

/-- One kind of regulated decision. -/
inductive TaskType
  | supplierOnboarding
  | payments
  | dataAccess
  deriving DecidableEq

/-- The written rules of one task type: legal moves `T` and safety invariant `I`. -/
structure Policy (X A : Type u) where
  T : X → A → X → Prop
  I : X → Prop

/-- One legal step of a policy. A step is one action. -/
structure Step {X A : Type u} (P : Policy X A) where
  x : X
  a : A
  x' : X
  legal : P.T x a x'

/-- A plan is the list of actions the model creates. The model may revise it
by creating another list. -/
abbrev Plan (A : Type u) := List A

/-- The checker accepts a certificate, or refuses it.
Acceptance does not say that the world outside the checker is correct. -/
structure Certificate where
  accepted : Prop

def CheckerAccepts (C : Certificate) : Prop := C.accepted

/-- An abstraction kept in the library only together with an accepted certificate. -/
structure LibraryEntry where
  certificate : Certificate
  admittedByCertificate : CheckerAccepts certificate

/-- One case of one task type, created by the generator.
It fixes the starting state and the goal. It is checked against `policy`. -/
structure Task (X A : Type u) [Fintype X] where
  taskType : TaskType
  policy : Policy X A
  start : X
  goal : X → Prop

namespace Task

variable {X A : Type u} [Fintype X]

/-- A state-to-state step hides the action, for reachability. -/
def stepRel (P : Policy X A) (x x' : X) : Prop := ∃ a, P.T x a x'

/-- States reachable from `s` by legal moves of the policy. -/
def ReachFrom (P : Policy X A) (s s' : X) : Prop :=
  Relation.ReflTransGen (stepRel P) s s'

/-- Top-level safety and goal for finite traces of a task.
Safety is the policy invariant `I` on every reachable state, including the start.
The goal is required only at a reachable state with no legal move. -/
structure Obligations (task : Task X A) : Prop where
  safety : ∀ s, ReachFrom task.policy task.start s → task.policy.I s
  goalAtTerminal :
    ∀ s, ReachFrom task.policy task.start s →
      (∀ s', ¬ stepRel task.policy s s') → task.goal s

def traceStates {P : Policy X A} (x0 : X) : List (Step P) → List X
  | [] => [x0]
  | s :: rest => s.x :: traceStates s.x' rest

def chained {P : Policy X A} (x0 : X) : List (Step P) → Prop
  | [] => True
  | s :: rest => s.x = x0 ∧ chained s.x' rest

/-- The actions of a run are the plan. -/
def realizes {P : Policy X A} (plan : Plan A) (steps : List (Step P)) : Prop :=
  plan = steps.map Step.a

def RunSafe (task : Task X A) (steps : List (Step task.policy)) : Prop :=
  ∀ x ∈ traceStates task.start steps, task.policy.I x

def RunComplete (task : Task X A) (steps : List (Step task.policy)) : Prop :=
  ∃ x, (traceStates task.start steps).getLast? = some x ∧ task.goal x

/-- A plan succeeds on a task only when every run is safe and meets the goal. -/
def PlanSucceeds (task : Task X A) (plan : Plan A) : Prop :=
  ∀ steps, chained task.start steps → realizes plan steps →
    RunSafe task steps ∧ RunComplete task steps

/-- A scored plan lies in the finite fragment: states are finite by `Fintype`,
and the plan is no longer than the bound. -/
def inFiniteFragment {B : Type u} (maxLen : Nat) (plan : Plan B) : Prop :=
  plan.length ≤ maxLen

omit [Fintype X] in
lemma mem_trace_reachable {P : Policy X A} {x0 x : X} (steps : List (Step P))
    (hchain : chained x0 steps) (hx : x ∈ traceStates x0 steps) :
    ReachFrom P x0 x := by
  induction steps generalizing x0 x with
  | nil =>
      simp [traceStates] at hx
      subst hx
      exact Relation.ReflTransGen.refl
  | cons s rest ih =>
      obtain ⟨rfl, hrest⟩ := hchain
      simp [traceStates] at hx
      rcases hx with rfl | hx
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.head ⟨s.a, s.legal⟩ (ih hrest hx)

/-- Every run of a task that meets its obligations stays inside the policy invariant. -/
theorem run_safe_of_obligations (task : Task X A) (h : Obligations task)
    (steps : List (Step task.policy)) (hchain : chained task.start steps) :
    RunSafe task steps := by
  intro x hx
  exact h.safety x (mem_trace_reachable steps hchain hx)

end Task

open Task

/-- Checked refinement contract for concrete task `C` against abstract task `A`.
One concrete action is matched by exactly one abstract action.
`assumptions`, `simulation` and `terminal` are the discharged assumptions `Γ`. -/
structure RefinementContract
    {Xc Ac Xa Aa : Type u} [Fintype Xc] [Fintype Xa]
    (C : Task Xc Ac) (A : Task Xa Aa)
    (R : Xc → Xa → Prop) : Prop where
  assumptions : R C.start A.start
  simulation : ∀ s s' t a, R s t → C.policy.T s a s' →
    ∃ t' b, A.policy.T t b t' ∧ R s' t'
  terminal : ∀ s t, R s t → (∀ s', ¬ stepRel C.policy s s') →
    ∀ t', ¬ stepRel A.policy t t'
  safetyTransfer : ∀ s t, R s t → A.policy.I t → C.policy.I s
  goalTransfer : ∀ s t, R s t → A.goal t → C.goal s

/-- Relational composition of simulation relations. -/
def SimRel.comp {α β γ : Type u} (R : α → β → Prop) (S : β → γ → Prop) :
    α → γ → Prop :=
  fun a c => ∃ b, R a b ∧ S b c

lemma reach_simulated
    {Xc Ac Xa Aa : Type u} [Fintype Xc] [Fintype Xa]
    {C : Task Xc Ac} {A : Task Xa Aa} {R : Xc → Xa → Prop}
    (h : RefinementContract C A R) {s s' : Xc} {t : Xa}
    (hR : R s t) (hreach : ReachFrom C.policy s s') :
    ∃ t', ReachFrom A.policy t t' ∧ R s' t' := by
  induction hreach with
  | refl =>
      exact ⟨t, Relation.ReflTransGen.refl, hR⟩
  | tail _ hstep ih =>
      obtain ⟨t₁, ht₁, hR₁⟩ := ih
      obtain ⟨a, hT⟩ := hstep
      obtain ⟨t', _, hst, hR'⟩ := h.simulation _ _ _ a hR₁ hT
      exact ⟨t', Relation.ReflTransGen.tail ht₁ ⟨_, hst⟩, hR'⟩

/-- One checked refinement preserves the abstract obligations on the concrete task. -/
theorem obligations_transfer
    {Xc Ac Xa Aa : Type u} [Fintype Xc] [Fintype Xa]
    {C : Task Xc Ac} {A : Task Xa Aa} {R : Xc → Xa → Prop}
    (h : RefinementContract C A R) (top : Obligations A) : Obligations C := by
  refine ⟨?safety, ?goal⟩
  · intro s hreach
    obtain ⟨t, ht, hR⟩ := reach_simulated h h.assumptions hreach
    exact h.safetyTransfer s t hR (top.safety t ht)
  · intro s hreach hterm
    obtain ⟨t, ht, hR⟩ := reach_simulated h h.assumptions hreach
    have hAterm : ∀ t', ¬ stepRel A.policy t t' := h.terminal s t hR hterm
    exact h.goalTransfer s t hR (top.goalAtTerminal t ht hAterm)

/-- Simulation contracts compose. -/
theorem refinementContract_trans
    {X₁ A₁ X₂ A₂ X₃ A₃ : Type u}
    [Fintype X₁] [Fintype X₂] [Fintype X₃]
    {M₁ : Task X₁ A₁} {M₂ : Task X₂ A₂} {M₃ : Task X₃ A₃}
    {R₁₂ : X₁ → X₂ → Prop} {R₂₃ : X₂ → X₃ → Prop}
    (h₁₂ : RefinementContract M₁ M₂ R₁₂) (h₂₃ : RefinementContract M₂ M₃ R₂₃) :
    RefinementContract M₁ M₃ (SimRel.comp R₁₂ R₂₃) where
  assumptions := ⟨M₂.start, h₁₂.assumptions, h₂₃.assumptions⟩
  simulation := by
    intro s s' u a hsu hstep
    obtain ⟨t, hR, hS⟩ := hsu
    obtain ⟨t', b, ht, hR'⟩ := h₁₂.simulation s s' t a hR hstep
    obtain ⟨u', c, hu, hS'⟩ := h₂₃.simulation t t' u b hS ht
    exact ⟨u', c, hu, t', hR', hS'⟩
  terminal := by
    intro s u hsu hterm t'
    obtain ⟨t, hR, hS⟩ := hsu
    exact h₂₃.terminal t u hS (h₁₂.terminal s t hR hterm) t'
  safetyTransfer := by
    intro s u hsu hsafe
    obtain ⟨t, hR, hS⟩ := hsu
    exact h₁₂.safetyTransfer s t hR (h₂₃.safetyTransfer t u hS hsafe)
  goalTransfer := by
    intro s u hsu hgoal
    obtain ⟨t, hR, hS⟩ := hsu
    exact h₁₂.goalTransfer s t hR (h₂₃.goalTransfer t u hS hgoal)

/-- **P1.** If each refinement contract is checked, its assumptions are discharged,
and the simulation is the transitive (composed) relation, then the concrete task
preserves the top-level safety invariant and the goal. -/
theorem p1_sound_composition
    {X₁ A₁ X₂ A₂ X₃ A₃ : Type u}
    [Fintype X₁] [Fintype X₂] [Fintype X₃]
    {M₁ : Task X₁ A₁} {M₂ : Task X₂ A₂} {M₃ : Task X₃ A₃}
    {R₁₂ : X₁ → X₂ → Prop} {R₂₃ : X₂ → X₃ → Prop}
    (h₁₂ : RefinementContract M₁ M₂ R₁₂) (h₂₃ : RefinementContract M₂ M₃ R₂₃)
    (top : Obligations M₃) : Obligations M₁ :=
  obligations_transfer (refinementContract_trans h₁₂ h₂₃) top

end Certain

export Certain (p1_sound_composition obligations_transfer refinementContract_trans)
