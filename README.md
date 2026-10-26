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
| `P1Soundness/SoundComposition.lean` | Task, policy, plan, certificate, refinement contract, P1. |
| `P1Soundness/Admission.lean` | P2 and the ungated contrast. |
| `P1Soundness/SearchCost.lean` | P3 bound, one saving, one increase. |
| `P1Soundness/Sanctions.lean` | Dropped sanctions bit. |

## What is assumed

A task type is one kind of regulated decision: supplier onboarding, payments, or data access.

A policy is the pair `(T, I)` for one task type. `T` says which action may be taken from which state. `I` is the safety invariant. Every task of that type is checked against that policy.

A task is one case of one task type. It fixes the starting state and the goal `G`. `G` says when the task is finished. It is not the policy.

A plan is a list of actions. A step is one action. A plan succeeds only when every run is safe and meets the goal. `run_safe_of_obligations` shows that a task which meets its obligations has only safe runs.

A certificate is what the checker accepts or refuses. A library entry exists only with an accepted certificate. The gate decides whether a plan may be carried out with a certificate. The library is not an argument of the gate.

State spaces are finite (`Fintype`). A scored plan is no longer than a fixed bound (`inFiniteFragment`). Traces are finite.

`Obligations` has two parts.

- **Safety.** Every state reachable from the task's start satisfies `I`.
- **Goal.** Every reachable state with no legal action satisfies `G`. This is the goal of the task's transition system, not “`G` holds at the last state of one nominated plan”.

`RefinementContract C A R` is a lockstep forward simulation of concrete task `C` by abstract task `A` along relation `R`. One concrete action is matched by exactly one abstract action. Stuttering is not proved. The fields `assumptions`, `simulation`, and `terminal` are the discharged assumptions. `safetyTransfer` and `goalTransfer` pass the abstract invariant and goal down to the related concrete state. Nothing here proves that a given checker implements this contract.

## Theorems and what they show

### P1 — `p1_sound_composition`

If two contracts `M₁ → M₂` and `M₂ → M₃` are given, and `M₃` meets its obligations, then the concrete task `M₁` meets its obligations. The simulation on the whole span is relational composition. `refinementContract_trans` proves that the two contracts compose.

This is two links, not an arbitrary stack. Stuttering, infinite traces, and beliefs are out of scope.

The CERTAIN text names this artefact `p1_sound_composition`.

### P2 — `p2_library_extension_safety`

`Admitted gate library plan C` is defined as `gate plan C`. The library is a list of abstractions admitted by a certificate, and that argument is ignored. Extending the library does not change admission. The proof is `Iff.rfl`.

`Gate planOk plan C` is the intended shape: the certificate is accepted, and the plan meets `planOk`. A belief is not an argument.

`p2_rejected_stays_rejected` is the same fact for a plan the gate already rejects.

`ungated_library_enlarges` is the contrast. If permission is membership of the library, then `release` is refused by the empty library and admitted once it is added.

The CERTAIN text names `p2_library_extension_safety` and `ungated_library_enlarges`.

### P3 — search cost

This file measures search nodes only. Cost is the number of nodes in a complete regular tree, `branching ^ depth`. Using one abstraction costs the abstract tree plus one refinement-check cost. Using none costs the concrete tree. There is no probability and no expectation. This is not the four-term cost that also counts checker calls, time and GPU use.

| Theorem | Statement |
| --- | --- |
| `p3_positive_bound` | Assumes `abstract + check ≤ concrete`, and concludes the same inequality. The coverage argument has type `True`. This does not by itself exhibit a saving. |
| `p3_positive_instance` | `costWithLibrary 2 2 1 ≤ costWithoutLibrary 2 5`, checked by `decide`. This is the concrete saving. |
| `p3_counterexample` | `costWithoutLibrary 2 3 < costWithLibrary 2 1 20`, checked by `decide`. A poor step can cost more. |

The CERTAIN text names `p3_positive_bound` and `p3_counterexample`. The exhibited saving is `p3_positive_instance`, which that text does not name. The comparison is against an empty library, not against a hierarchy written in advance.

### Sanctions counterexample

There is one payment policy. `T` allows both a cleared and an uncleared release. `I` says a release is safe only when sanctions are clear. The training task and the holdout task share that policy and the payment task type. Training starts where clearance is already known, so every reachable state satisfies `I`. Holdout starts at the beginning, so an uncleared release is reachable.

The abstract task erases the clearance bit and treats every state as safe.

| Theorem | Statement |
| --- | --- |
| `shared_payment_policy` | Training and holdout use the same policy. |
| `shared_task_type` | Both are payment tasks. |
| `training_obligations` | The training task meets `Obligations`. |
| `holdout_unsafe` | The holdout task does not. `rel false` is reachable. |
| `erase_forgets_clearance` | `erase (rel false) = erase (rel true)`. |
| `sanctions_no_refinement` | For every relation `R`, there is no `RefinementContract` from the holdout task to the abstract task. The abstract task meets its obligations, so a contract would make the holdout task safe. |

The CERTAIN text names the last four. The proofs do not show that putting clearance into an assumption field restores a contract. They show that this erasure does not refine.
