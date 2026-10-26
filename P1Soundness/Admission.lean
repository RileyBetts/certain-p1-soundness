import P1Soundness.SoundComposition

open Certain

/-!
# P2 — library extension does not enlarge executable authority

The gate decides whether a plan may be carried out with a certificate.
A library is the set of abstractions a certificate has admitted. It is data
the proposer may consult. It is not an argument of the gate. Replacing or
extending the library leaves the admitted set unchanged.

`ungated_library_enlarges` is the contrast: if library membership itself is
permission, adding an entry admits a plan the empty library refused.
-/

/-- The gate decides whether this plan may be carried out with this certificate.
The library is not an argument, and neither is a belief. -/
def Gate {A : Type} (planOk : Plan A → Prop) (plan : Plan A) (C : Certificate) : Prop :=
  CheckerAccepts C ∧ planOk plan

/-- A completely mediating gate. The library argument is ignored. -/
def Admitted {A : Type} (gate : Plan A → Certificate → Prop)
    (_library : List LibraryEntry) (plan : Plan A) (C : Certificate) : Prop :=
  gate plan C

/-- **P2.** Extending or replacing the library does not change admission. -/
theorem p2_library_extension_safety
    {A : Type}
    (gate : Plan A → Certificate → Prop)
    (library extra : List LibraryEntry) (plan : Plan A) (C : Certificate) :
    Admitted gate (library ++ extra) plan C ↔ Admitted gate library plan C :=
  Iff.rfl

/-- A plan the gate rejects stays rejected after the library grows. -/
theorem p2_rejected_stays_rejected
    {A : Type}
    (gate : Plan A → Certificate → Prop)
    (library extra : List LibraryEntry) (plan : Plan A) (C : Certificate)
    (hrej : ¬ gate plan C) :
    ¬ Admitted gate (library ++ extra) plan C :=
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
