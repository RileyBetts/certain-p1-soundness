import Mathlib.Logic.Relation

/-!
# P1 — sound composition of refinement contracts

The objects follow the CERTAIN definitions.

* A task type is one kind of regulated decision.
* A policy is the pair `(T, I)`: legal moves and the safety invariant.
  Every task of a task type is checked against that policy.
* A task is one case of one task type. It fixes the starting state and the goal `G`.
  `G` is not the task and not the policy.
* A plan is a list of actions. A step is one action in a plan.
* A certificate is accepted or refused by the checker. The gate is separate:
  it decides whether a plan may be carried out, and it does not read the library.

What is checked here, and its limits:

* obligations are task-level: every reachable state satisfies `I`, and every
  reachable state with no legal move satisfies `G`;
* a refinement contract is lockstep: each concrete step is matched by some
  abstract step. Stuttering is not covered;
* contracts compose along a chain of any length (`refines_chain_obligations`);
* a plan whose every run ends at a state with no legal move succeeds on a task
  that meets its obligations (`planSucceeds_of_obligations`);
* traces are finite. No finiteness of the state spaces is needed by any proof.

Not proved: that a checker implements the contract, stuttering, infinite traces,
beliefs, environmental assumptions `Γ`, or an unmodelled environment.
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

/-- A plan is the list of actions the model creates. -/
abbrev Plan (A : Type u) := List A

/-- The checker accepts a certificate, or refuses it. In this development the
certificate carries no data the checker inspects; `accepted` is abstract.
Acceptance does not say that the world outside the checker is correct. -/
structure Certificate where
  accepted : Prop

def CheckerAccepts (C : Certificate) : Prop := C.accepted

/-- An abstraction kept in the library only together with an accepted certificate. -/
structure LibraryEntry where
  certificate : Certificate
  admittedByCertificate : CheckerAccepts certificate

/-- One case of one task type. It fixes the starting state and the goal.
It is checked against `policy`. -/
structure Task (X A : Type u) where
  taskType : TaskType
  policy : Policy X A
  start : X
  goal : X → Prop

namespace Task

variable {X A : Type u}

/-- A state-to-state step hides the action, for reachability. -/
def stepRel (P : Policy X A) (x x' : X) : Prop := ∃ a, P.T x a x'

/-- States reachable from `s` by legal moves of the policy. -/
def ReachFrom (P : Policy X A) (s s' : X) : Prop :=
  Relation.ReflTransGen (stepRel P) s s'

/-- A state with no legal move. -/
def Terminal (P : Policy X A) (s : X) : Prop := ∀ s', ¬ stepRel P s s'

/-- Task-level safety and goal.
Safety is the policy invariant `I` on every reachable state, including the start.
The goal is required at every reachable state with no legal move. -/
structure Obligations (task : Task X A) : Prop where
  safety : ∀ s, ReachFrom task.policy task.start s → task.policy.I s
  goalAtTerminal :
    ∀ s, ReachFrom task.policy task.start s → Terminal task.policy s → task.goal s

def traceStates {P : Policy X A} (x0 : X) : List (Step P) → List X
  | [] => [x0]
  | s :: rest => s.x :: traceStates s.x' rest

/-- The state a run ends in. -/
def lastState {P : Policy X A} (x0 : X) : List (Step P) → X
  | [] => x0
  | s :: rest => lastState s.x' rest

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
  ∀ steps : List (Step task.policy), chained task.start steps → realizes plan steps →
    RunSafe task steps ∧ RunComplete task steps

/-- Every run of the plan ends at a state with no legal move. -/
def PlanRunsToTerminal (task : Task X A) (plan : Plan A) : Prop :=
  ∀ steps : List (Step task.policy), chained task.start steps → realizes plan steps →
    Terminal task.policy (lastState task.start steps)

theorem mem_trace_reachable {P : Policy X A} {x0 x : X} (steps : List (Step P))
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

theorem getLast_traceStates {P : Policy X A} (x0 : X) (steps : List (Step P)) :
    (traceStates x0 steps).getLast? = some (lastState x0 steps) := by
  induction steps generalizing x0 with
  | nil => rfl
  | cons s rest ih =>
      cases rest with
      | nil => rfl
      | cons s2 rest2 =>
          simpa [traceStates, lastState] using ih s.x'

theorem lastState_mem {P : Policy X A} (x0 : X) (steps : List (Step P)) :
    lastState x0 steps ∈ traceStates x0 steps := by
  induction steps generalizing x0 with
  | nil => simp [lastState, traceStates]
  | cons s rest ih =>
      simp only [lastState, traceStates]
      exact List.mem_cons_of_mem _ (ih s.x')

/-- Every run of a task that meets its obligations stays inside the policy invariant. -/
theorem run_safe_of_obligations (task : Task X A) (h : Obligations task)
    (steps : List (Step task.policy)) (hchain : chained task.start steps) :
    RunSafe task steps := by
  intro x hx
  exact h.safety x (mem_trace_reachable steps hchain hx)

/-- A plan whose every run ends at a terminal state succeeds on a task that meets
its obligations. This links task-level obligations to `PlanSucceeds`. -/
theorem planSucceeds_of_obligations (task : Task X A) (h : Obligations task)
    (plan : Plan A) (hterm : PlanRunsToTerminal task plan) :
    PlanSucceeds task plan := by
  intro steps hchain hreal
  refine ⟨run_safe_of_obligations task h steps hchain, ?_⟩
  refine ⟨lastState task.start steps, getLast_traceStates _ _, ?_⟩
  exact h.goalAtTerminal _
    (mem_trace_reachable steps hchain (lastState_mem _ _)) (hterm steps hchain hreal)

end Task

open Task

/-- Refinement contract for concrete task `C` against abstract task `A`, along a
relation `R` on states. There is no relation on actions: in `simulation` the
abstract action `b` is an existential witness. These fields are the contract's
own conditions. Environmental assumptions `Γ` are not modelled here. -/
structure RefinementContract
    {Xc Ac Xa Aa : Type u}
    (C : Task Xc Ac) (A : Task Xa Aa)
    (R : Xc → Xa → Prop) : Prop where
  startCorr : R C.start A.start
  simulation : ∀ s s' t a, R s t → C.policy.T s a s' →
    ∃ t' b, A.policy.T t b t' ∧ R s' t'
  terminal : ∀ s t, R s t → Terminal C.policy s → Terminal A.policy t
  safetyTransfer : ∀ s t, R s t → A.policy.I t → C.policy.I s
  goalTransfer : ∀ s t, R s t → A.goal t → C.goal s

/-- Relational composition of simulation relations. -/
def SimRel.comp {α β γ : Type u} (R : α → β → Prop) (S : β → γ → Prop) :
    α → γ → Prop :=
  fun a c => ∃ b, R a b ∧ S b c

theorem reach_simulated
    {Xc Ac Xa Aa : Type u}
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

/-- One refinement contract transfers the abstract obligations to the concrete task. -/
theorem obligations_transfer
    {Xc Ac Xa Aa : Type u}
    {C : Task Xc Ac} {A : Task Xa Aa} {R : Xc → Xa → Prop}
    (h : RefinementContract C A R) (top : Obligations A) : Obligations C := by
  refine ⟨?safety, ?goal⟩
  · intro s hreach
    obtain ⟨t, ht, hR⟩ := reach_simulated h h.startCorr hreach
    exact h.safetyTransfer s t hR (top.safety t ht)
  · intro s hreach hterm
    obtain ⟨t, ht, hR⟩ := reach_simulated h h.startCorr hreach
    exact h.goalTransfer s t hR (top.goalAtTerminal t ht (h.terminal s t hR hterm))

/-- Contracts compose. -/
theorem refinementContract_trans
    {X₁ A₁ X₂ A₂ X₃ A₃ : Type u}
    {M₁ : Task X₁ A₁} {M₂ : Task X₂ A₂} {M₃ : Task X₃ A₃}
    {R₁₂ : X₁ → X₂ → Prop} {R₂₃ : X₂ → X₃ → Prop}
    (h₁₂ : RefinementContract M₁ M₂ R₁₂) (h₂₃ : RefinementContract M₂ M₃ R₂₃) :
    RefinementContract M₁ M₃ (SimRel.comp R₁₂ R₂₃) where
  startCorr := ⟨M₂.start, h₁₂.startCorr, h₂₃.startCorr⟩
  simulation := by
    intro s s' u a hsu hstep
    obtain ⟨t, hR, hS⟩ := hsu
    obtain ⟨t', b, ht, hR'⟩ := h₁₂.simulation s s' t a hR hstep
    obtain ⟨u', c, hu, hS'⟩ := h₂₃.simulation t t' u b hS ht
    exact ⟨u', c, hu, t', hR', hS'⟩
  terminal := by
    intro s u hsu hterm
    obtain ⟨t, hR, hS⟩ := hsu
    exact h₂₃.terminal t u hS (h₁₂.terminal s t hR hterm)
  safetyTransfer := by
    intro s u hsu hsafe
    obtain ⟨t, hR, hS⟩ := hsu
    exact h₁₂.safetyTransfer s t hR (h₂₃.safetyTransfer t u hS hsafe)
  goalTransfer := by
    intro s u hsu hgoal
    obtain ⟨t, hR, hS⟩ := hsu
    exact h₁₂.goalTransfer s t hR (h₂₃.goalTransfer t u hS hgoal)

/-- **P1, two links.** Contracts `M₁ → M₂` and `M₂ → M₃`, composed by
`refinementContract_trans`, transfer the obligations of `M₃` to `M₁`. -/
theorem p1_sound_composition
    {X₁ A₁ X₂ A₂ X₃ A₃ : Type u}
    {M₁ : Task X₁ A₁} {M₂ : Task X₂ A₂} {M₃ : Task X₃ A₃}
    {R₁₂ : X₁ → X₂ → Prop} {R₂₃ : X₂ → X₃ → Prop}
    (h₁₂ : RefinementContract M₁ M₂ R₁₂) (h₂₃ : RefinementContract M₂ M₃ R₂₃)
    (top : Obligations M₃) : Obligations M₁ :=
  obligations_transfer (refinementContract_trans h₁₂ h₂₃) top

/-- A task with its state and action types, so tasks at different levels can sit
in one chain. -/
structure AnyTask where
  X : Type u
  A : Type u
  task : Task X A

/-- `C` refines `A` when some refinement contract links them. -/
def Refines (C A : AnyTask.{u}) : Prop :=
  ∃ R : C.X → A.X → Prop, RefinementContract C.task A.task R

/-- **P1, any number of links.** A chain of refinement contracts of any length,
from the concrete task `C` up to the top task `A`, transfers the obligations of
`A` to `C`. -/
theorem refines_chain_obligations {C A : AnyTask.{u}}
    (hchain : Relation.ReflTransGen Refines C A) (top : Obligations A.task) :
    Obligations C.task := by
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl => exact top
  | head hstep _ ih =>
      obtain ⟨R, hR⟩ := hstep
      exact obligations_transfer hR ih

/-- **P1 at plan level.** If the concrete task is linked to the top task by a chain
of contracts, the top task meets its obligations, and every run of a concrete plan
ends at a state with no legal move, then that plan succeeds on the concrete task. -/
theorem p1_plan_succeeds {C A : AnyTask.{u}}
    (hchain : Relation.ReflTransGen Refines C A) (top : Obligations A.task)
    (plan : Plan C.A) (hterm : PlanRunsToTerminal C.task plan) :
    PlanSucceeds C.task plan :=
  planSucceeds_of_obligations C.task (refines_chain_obligations hchain top) plan hterm

end Certain

export Certain (p1_sound_composition obligations_transfer refinementContract_trans
  refines_chain_obligations p1_plan_succeeds)
