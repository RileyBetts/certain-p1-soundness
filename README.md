# P1Soundness

Checked Lean 4 development for three restricted CERTAIN research propositions: sound composition, library-extension safety, and a conditional search-cost comparison, plus the sanctions-bit counterexample.

These proofs are a finite-state special case. They do not establish the general CERTAIN definitions (arbitrary horizon, stuttering steps, beliefs, or an unmodelled environment).

## Verify

The project pins Lean `v4.29.1` and Mathlib `v4.29.1` (`lean-toolchain`, `lakefile.toml`). From this directory, with [elan](https://github.com/leanprover/elan) on `PATH`:

```sh
lake exe cache get
lake build
```

`lake build` must finish with no errors. There are no `axiom` declarations and no `sorry`. A successful build means the kernel accepted every theorem below.

To inspect one result:

```sh
lake env lean P1Soundness/SoundComposition.lean
```

The same command works with `Admission.lean`, `SearchCost.lean`, or `Sanctions.lean`.

## Layout

| File | Role |
| --- | --- |
| `P1Soundness.lean` | Root imports. |
| `P1Soundness/SoundComposition.lean` | Finite-state model, refinement contract, P1. |
| `P1Soundness/Admission.lean` | P2 and the ungated contrast. |
| `P1Soundness/SearchCost.lean` | P3 bound, one saving, one increase. |
| `P1Soundness/Sanctions.lean` | Dropped sanctions bit. |

## What is assumed

`PlanningModel` is a finite state space (`Fintype`) with an initial-state predicate, a step relation, a safety predicate, and a goal predicate. Reachability is the reflexive-transitive closure of `step`. Traces are finite.

`Obligations` has two parts.

- **Safety.** Every state reachable from an initial state is safe.
- **Goal.** Every reachable state with no successor satisfies the goal. This is not “the goal holds at the last state of a nominated action list”.

`RefinementContract C A R` is a stutter-free forward simulation of concrete model `C` by abstract model `A` along relation `R`. One concrete step is matched by exactly one abstract step. The fields `assumptions`, `simulation`, and `terminal` are the discharged assumptions. `safetyTransfer` and `goalTransfer` say that safety and goal on an abstract state pass to each related concrete state. Nothing here proves that a given checker implements this contract. The caller must supply a value of type `RefinementContract`.

## Theorems and what they show

### P1 — `p1_sound_composition`

If two contracts `M₁ → M₂` and `M₂ → M₃` are given, and `M₃` meets its obligations, then `M₁` meets its obligations. The simulation used on the whole span is relational composition of the two relations. `refinementContract_trans` is the proof that those two contracts compose.

This is two links, not an arbitrary stack. A longer chain is not packaged as one theorem. Stuttering, infinite traces, and beliefs are out of scope.

The CERTAIN text names this artefact `p1_sound_composition`.

### P2 — `p2_library_extension_safety`

`Admitted gate library M` is defined as `gate M`. The library argument is ignored. Extending the library therefore does not change admission, whether or not the added entry was certified. The proof is `Iff.rfl`.

`p2_rejected_stays_rejected` is the same fact stated for a plan the gate already rejects.

`ungated_library_enlarges` is the contrast. If permission is membership of the library, then `release` is refused by the empty library and admitted once it is added.

The CERTAIN text names `p2_library_extension_safety` and `ungated_library_enlarges`.

### P3 — search cost

Cost is the number of nodes in a complete regular tree, `branching ^ depth`. Using one abstraction costs the abstract tree plus one refinement-check cost. Using none costs the concrete tree. There is no probability and no expectation.

| Theorem | Statement |
| --- | --- |
| `p3_positive_bound` | Assumes `abstract + check ≤ concrete`, and concludes the same inequality. The coverage argument has type `True`. This does not by itself exhibit a saving. |
| `p3_positive_instance` | `costWithLibrary 2 2 1 ≤ costWithoutLibrary 2 5`, checked by `decide`. This is the concrete saving. |
| `p3_counterexample` | `costWithoutLibrary 2 3 < costWithLibrary 2 1 20`, checked by `decide`. A poor step can cost more. |

The CERTAIN text names `p3_positive_bound` and `p3_counterexample`. The exhibited saving is `p3_positive_instance`, which that text does not name. The comparison is against an empty library, not against a hierarchy written in advance.

### Sanctions counterexample

Both workflows use the same two steps: `start → auth false → rel false`. The training model treats every state as safe. The holdout model treats `rel false` as unsafe.

| Theorem | Statement |
| --- | --- |
| `training_obligations` | The training model meets `Obligations`. |
| `holdout_unsafe` | The holdout model does not. `rel false` is reachable. |
| `erase_forgets_clearance` | `erase (rel false) = erase (rel true)`. |
| `sanctions_no_refinement` | For every relation `R`, there is no `RefinementContract` from the holdout model to the abstract model. The abstract model meets its obligations, so a contract would make the holdout model safe. |

The CERTAIN text names these four. The proofs do not show that putting clearance into an assumption field restores a contract. They show that this erasure does not refine.
