import P1Soundness.SoundComposition

/-!
# P2 — library extension does not enlarge executable authority

The gate is a predicate of the concrete plan alone. A library is data the
proposer may consult, but it is not an input to the gate. Therefore replacing
or extending the library leaves the admitted set unchanged.

The contrasting statement `ungated_library_enlarges` shows that a check which
treats library membership itself as permission does enlarge authority.
-/

/-- A completely mediating gate. Instantiated at `PlanningModel.Obligations`. -/
def Admitted {σ α : Type u} [Fintype σ]
    (gate : PlanningModel σ → Prop) (_library : List α) (M : PlanningModel σ) : Prop :=
  gate M

/-- **P2.** Extending or replacing the library does not change admission. -/
theorem p2_library_extension_safety
    {σ α : Type u} [Fintype σ]
    (gate : PlanningModel σ → Prop) (library extra : List α) (M : PlanningModel σ) :
    Admitted gate (library ++ extra) M ↔ Admitted gate library M :=
  Iff.rfl

/-- A plan the gate rejects stays rejected after the library grows. -/
theorem p2_rejected_stays_rejected
    {σ α : Type u} [Fintype σ]
    (gate : PlanningModel σ → Prop) (library extra : List α) (M : PlanningModel σ)
    (hrej : ¬ gate M) :
    ¬ Admitted gate (library ++ extra) M :=
  hrej

/-- Names of plans, used only for the ungated contrast. -/
inductive PlanId
  | release
  | hold
  deriving DecidableEq

/-- Permission defined by library membership, with no independent gate. -/
def Ungated (library : List PlanId) (p : PlanId) : Prop :=
  p ∈ library

theorem ungated_library_enlarges :
    ¬ Ungated [] PlanId.release ∧ Ungated [PlanId.release] PlanId.release := by
  simp [Ungated]
