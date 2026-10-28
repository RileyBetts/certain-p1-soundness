/-!
# P3 — reuse of an abstraction need not reduce search cost

This cost is the size of an exhaustive finite search tree, plus one refinement
check when a library abstraction is used. It is the search term only. It is not
the four-term cost of a task, which also counts checker calls, time and GPU use.

The cost counts search nodes only. There is no probability and no expectation.
The comparison is against the empty library, not a hierarchy written in advance.

`p3_positive_bound` states the condition under which reuse does not increase
cost: abstract search plus one check is at most concrete search. It restates
that condition and does not by itself exhibit a saving.
`p3_positive_instance` exhibits a saving.
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

/-- **P3, positive case.** If abstract search plus one refinement check is at most
the concrete search, cost does not increase. -/
theorem p3_positive_bound
    (absBranching absDepth concBranching concDepth refineCost : Nat)
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

/-- **P3, negative case.** An applicable abstraction can still cost more. Abstract tree `2^1`
plus a refinement check of `20` is strictly more expensive than concrete
search of `2^3`. -/
theorem p3_counterexample :
    costWithoutLibrary 2 3 < costWithLibrary 2 1 20 := by
  decide
