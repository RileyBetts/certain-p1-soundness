import Mathlib.Data.Fintype.Basic

/-!
# P3 — reuse of an abstraction need not reduce search cost

Cost is the size of an exhaustive finite search tree, plus a refinement-check
cost when a library entry is used. Coverage is the assumption that the
abstraction applies, so the planner may search the abstract tree and pay for
one check instead of searching the concrete tree.

`p3_positive_bound` is the restricted inequality under that hypothesis.
`p3_counterexample` is a concrete case where the check costs more than it saves.
-/

/-- Nodes visited by exhaustive search of a regular tree. -/
def searchCost (branching depth : Nat) : Nat :=
  branching ^ depth

/-- Cost of using one applicable abstraction: abstract search plus one check. -/
def costWithLibrary (absBranching absDepth refineCost : Nat) : Nat :=
  searchCost absBranching absDepth + refineCost

/-- Cost of planning against the empty library. -/
def costWithoutLibrary (concBranching concDepth : Nat) : Nat :=
  searchCost concBranching concDepth

/-- **P3, positive case.** If the abstraction applies and its abstract search
plus refinement check is at most the concrete search, cost does not increase. -/
theorem p3_positive_bound
    (absBranching absDepth concBranching concDepth refineCost : Nat)
    (_coverage : True)
    (h : searchCost absBranching absDepth + refineCost ≤
        searchCost concBranching concDepth) :
    costWithLibrary absBranching absDepth refineCost ≤
      costWithoutLibrary concBranching concDepth :=
  h

/-- A covered instance where the bound holds: abstract tree `2^2`, check `1`,
concrete tree `2^5`. -/
theorem p3_positive_instance :
    costWithLibrary 2 2 1 ≤ costWithoutLibrary 2 5 := by
  decide

/-- **P3, negative case.** Coverage alone is not enough. Abstract tree `2^1`
plus a refinement check of `20` is strictly more expensive than concrete
search of `2^3`. -/
theorem p3_counterexample :
    costWithoutLibrary 2 3 < costWithLibrary 2 1 20 := by
  decide
