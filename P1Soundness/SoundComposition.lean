import Mathlib.Data.Fintype.Basic

/-!
# P1 — sound composition for a finite-state planning semantics

Research proposition P1 from the CERTAIN concept note, specialised to a
deliberately restricted model:

* state spaces are finite (`Fintype`);
* a plan is the transition relation of a finite-state machine, together with
  an initial set, a safety predicate and a goal predicate;
* traces are finite paths; the goal obligation is required at terminal states
  (states with no successor);
* a refinement contract is a stutter-free forward simulation: one concrete
  step is matched by exactly one abstract step;
* environmental assumptions `Γ` are the contract hypotheses that have to be
  discharged (initial correspondence, step matching, and matching of terminals);
* the simulation used for a stack of refinements is relational composition,
  which is transitive in the sense proved by `refinementContract_trans`.

The theorem does not claim anything about infinite traces, stuttering,
probabilistic beliefs, or the fidelity of an unmodelled environment.
-/

universe u

/-- Finite-state planning model. `step` is the set of transitions admitted by the plan. -/
structure PlanningModel (σ : Type u) [Fintype σ] where
  init : σ → Prop
  step : σ → σ → Prop
  safe : σ → Prop
  goal : σ → Prop

namespace PlanningModel

variable {σ : Type u} [Fintype σ]

/-- Reachability along admitted transitions, including the zero-step path. -/
def Reach (M : PlanningModel σ) (s s' : σ) : Prop :=
  Relation.ReflTransGen M.step s s'

/-- Top-level safety and goal obligations for finite traces. -/
structure Obligations (M : PlanningModel σ) : Prop where
  safety : ∀ s₀ s, M.init s₀ → M.Reach s₀ s → M.safe s
  goalAtTerminal :
    ∀ s₀ s, M.init s₀ → M.Reach s₀ s → (∀ s', ¬ M.step s s') → M.goal s

end PlanningModel

/-- Checked refinement contract for `C` against `A` along a simulation `R`.

`assumptions`, `simulation` and `terminal` are the discharged assumptions `Γ`.
`safetyTransfer` and `goalTransfer` are the obligation maps from abstract states
to the related concrete states. -/
structure RefinementContract
    {σc σa : Type u} [Fintype σc] [Fintype σa]
    (C : PlanningModel σc) (A : PlanningModel σa)
    (R : σc → σa → Prop) : Prop where
  assumptions : ∀ s, C.init s → ∃ t, A.init t ∧ R s t
  simulation : ∀ s s' t, R s t → C.step s s' → ∃ t', A.step t t' ∧ R s' t'
  terminal : ∀ s t, R s t → (∀ s', ¬ C.step s s') → ∀ t', ¬ A.step t t'
  safetyTransfer : ∀ s t, R s t → A.safe t → C.safe s
  goalTransfer : ∀ s t, R s t → A.goal t → C.goal s

/-- Relational composition of simulation relations. -/
def SimRel.comp {α β γ : Type u} (R : α → β → Prop) (S : β → γ → Prop) :
    α → γ → Prop :=
  fun a c => ∃ b, R a b ∧ S b c

lemma reach_simulated
    {σc σa : Type u} [Fintype σc] [Fintype σa]
    {C : PlanningModel σc} {A : PlanningModel σa} {R : σc → σa → Prop}
    (h : RefinementContract C A R) {s s' : σc} {t : σa}
    (hR : R s t) (hreach : C.Reach s s') :
    ∃ t', A.Reach t t' ∧ R s' t' := by
  induction hreach with
  | refl =>
      exact ⟨t, Relation.ReflTransGen.refl, hR⟩
  | tail _ hstep ih =>
      obtain ⟨t₁, ht₁, hR₁⟩ := ih
      obtain ⟨t', hst, hR'⟩ := h.simulation _ _ _ hR₁ hstep
      exact ⟨t', Relation.ReflTransGen.tail ht₁ hst, hR'⟩

/-- One checked refinement preserves the abstract obligations. -/
theorem obligations_transfer
    {σc σa : Type u} [Fintype σc] [Fintype σa]
    {C : PlanningModel σc} {A : PlanningModel σa} {R : σc → σa → Prop}
    (h : RefinementContract C A R) (top : A.Obligations) : C.Obligations := by
  refine ⟨?safety, ?goal⟩
  · intro s₀ s hs₀ hreach
    obtain ⟨t₀, ht₀, hR₀⟩ := h.assumptions s₀ hs₀
    obtain ⟨t, ht, hR⟩ := reach_simulated h hR₀ hreach
    exact h.safetyTransfer s t hR (top.safety t₀ t ht₀ ht)
  · intro s₀ s hs₀ hreach hterm
    obtain ⟨t₀, ht₀, hR₀⟩ := h.assumptions s₀ hs₀
    obtain ⟨t, ht, hR⟩ := reach_simulated h hR₀ hreach
    have hAterm : ∀ t', ¬ A.step t t' := h.terminal s t hR hterm
    exact h.goalTransfer s t hR (top.goalAtTerminal t₀ t ht₀ ht hAterm)

/-- Simulation contracts compose. This is transitivity of the chosen simulation. -/
theorem refinementContract_trans
    {σ₁ σ₂ σ₃ : Type u} [Fintype σ₁] [Fintype σ₂] [Fintype σ₃]
    {M₁ : PlanningModel σ₁} {M₂ : PlanningModel σ₂} {M₃ : PlanningModel σ₃}
    {R₁₂ : σ₁ → σ₂ → Prop} {R₂₃ : σ₂ → σ₃ → Prop}
    (h₁₂ : RefinementContract M₁ M₂ R₁₂) (h₂₃ : RefinementContract M₂ M₃ R₂₃) :
    RefinementContract M₁ M₃ (SimRel.comp R₁₂ R₂₃) where
  assumptions := by
    intro s hs
    obtain ⟨t, ht, hR⟩ := h₁₂.assumptions s hs
    obtain ⟨u, hu, hS⟩ := h₂₃.assumptions t ht
    exact ⟨u, hu, t, hR, hS⟩
  simulation := by
    intro s s' u hsu hstep
    obtain ⟨t, hR, hS⟩ := hsu
    obtain ⟨t', ht, hR'⟩ := h₁₂.simulation s s' t hR hstep
    obtain ⟨u', hu, hS'⟩ := h₂₃.simulation t t' u hS ht
    exact ⟨u', hu, t', hR', hS'⟩
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
and the simulation is the transitive (composed) relation, then the concrete plan
preserves the top-level safety and goal obligations. -/
theorem p1_sound_composition
    {σ₁ σ₂ σ₃ : Type u} [Fintype σ₁] [Fintype σ₂] [Fintype σ₃]
    {M₁ : PlanningModel σ₁} {M₂ : PlanningModel σ₂} {M₃ : PlanningModel σ₃}
    {R₁₂ : σ₁ → σ₂ → Prop} {R₂₃ : σ₂ → σ₃ → Prop}
    (h₁₂ : RefinementContract M₁ M₂ R₁₂) (h₂₃ : RefinementContract M₂ M₃ R₂₃)
    (top : M₃.Obligations) : M₁.Obligations :=
  obligations_transfer (refinementContract_trans h₁₂ h₂₃) top
