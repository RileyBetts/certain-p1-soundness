# P1Soundness

Checked Lean 4 development for three restricted CERTAIN research propositions: sound composition, library-extension safety, and a search-cost comparison, plus the sanctions-bit counterexample.

These proofs are a restricted case: task-level obligations, lockstep refinement contracts (no stuttering), finite traces. No proof uses finiteness of the state spaces. They do not establish the general CERTAIN definitions (plan-level trace inclusion, stuttering steps, beliefs, environmental assumptions `Γ`, or an unmodelled environment).

## Verify

The project pins Lean `v4.29.1` and Mathlib `v4.29.1` (`lean-toolchain`, `lakefile.toml`). From this directory, with [elan](https://github.com/leanprover/elan) on `PATH`:

```sh
lake exe cache get
lake build
```

`lake build` must finish with no errors. There are no `axiom` declarations and no `sorry`. A successful build means the kernel accepted every theorem below.

On the tagged revision, `#print axioms` reports that `p1_sound_composition` and `refines_chain_obligations` depend on no axioms, and that `p1_plan_succeeds` and `sanctions_no_refinement` depend only on `propext`, which is propositional extensionality from Lean's logic.

To inspect one result:

```sh
lake env lean P1Soundness/SoundComposition.lean
```

The same command works with `Admission.lean`, `SearchCost.lean`, or `Sanctions.lean`.

## Scope and compatibility with the full CERTAIN definitions

This is a limited result, not the WP1/WP4 solution. Each restriction is a special case of the general definitions, so the results here remain true there.

- **Lockstep contracts.** A contract that matches each concrete step by one abstract step is a stuttering simulation in which no step stutters.
- **No `Γ`.** The contracts here have no environmental assumptions; this is the general case with `Γ` taken as `True`.
- **Task-level obligations.** Obligations over all reachable states imply success for any plan whose runs end at terminal states (`planSucceeds_of_obligations`). Plan-level trace inclusion is the general target and is not proved here.
- **Abstract certificates.** `Certificate.accepted` stands for the checker's verdict. WP4 replaces it with certificate data and proves that acceptance yields a contract (`Meets`).
- **Finite traces, arbitrary state types.** Finiteness of states is not needed by these proofs, so they hold in the finite fragment as a special case.

## Layout

| File | Role |
| --- | --- |
| `P1Soundness.lean` | Root imports. |
| `P1Soundness/SoundComposition.lean` | Task, policy, plan, certificate, refinement contract, P1 (two links, any chain, plan level). |
| `P1Soundness/Admission.lean` | P2 and the ungated contrast. |
| `P1Soundness/SearchCost.lean` | P3 bound, one saving, one increase. |
| `P1Soundness/Sanctions.lean` | Dropped sanctions bit. |

## What is assumed

A task type is one kind of regulated decision: supplier onboarding, payments, or data access.

A policy is the pair `(T, I)` for one task type. `T` says which action may be taken from which state. `I` is the safety invariant. Every task of that type is checked against that policy.

A task is one case of one task type. It fixes the starting state and the goal `G`. `G` says when the task is finished. It is not the policy.

A plan is a list of actions. A step is one action. A plan succeeds only when every run is safe and meets the goal. `run_safe_of_obligations` shows that a task which meets its obligations has only safe runs. `planSucceeds_of_obligations` shows that a plan whose every run ends at a state with no legal move succeeds on such a task.

A certificate is what the checker accepts or refuses. A library entry exists only with an accepted certificate. The gate decides whether a plan may be carried out with a certificate. The library is not an argument of the gate.

Traces are finite. State spaces are arbitrary types; no proof needs them to be finite. The bound on plan length that defines the CERTAIN finite fragment is not modelled here.

`Obligations` has two parts.

- **Safety.** Every state reachable from the task's start satisfies `I`.
- **Goal.** Every reachable state with no legal action satisfies `G`. This is the goal of the task's transition system, not “`G` holds at the last state of one nominated plan”.

`RefinementContract C A R` is a lockstep forward simulation of concrete task `C` by abstract task `A` along a relation `R` on states. There is no relation on actions. `startCorr` relates the two start states. `simulation` matches each concrete step by some abstract action and state; the abstract action is an existential witness. `terminal` maps concrete terminal states to abstract terminal states. `safetyTransfer` and `goalTransfer` pass the abstract invariant and goal down to the related concrete state. These are the contract's own conditions; environmental assumptions `Γ` are not modelled. Stuttering is not covered. Nothing here proves that a given checker implements this contract: `Certificate.accepted` is abstract.

## Theorems and what they show

### P1 — `p1_sound_composition`

If two contracts `M₁ → M₂` and `M₂ → M₃` are given, and `M₃` meets its obligations, then the concrete task `M₁` meets its obligations. The simulation on the whole span is relational composition. `refinementContract_trans` proves that the two contracts compose.

`refines_chain_obligations` is the same result for a chain of any length, written as `Relation.ReflTransGen Refines`. `p1_plan_succeeds` adds the plan-level consequence: on the concrete task, a plan whose every run ends at a terminal state succeeds.

The guarantee is task-level obligation transfer. It is not plan-level trace inclusion. Stuttering, infinite traces, and beliefs are out of scope.

The CERTAIN text names `p1_sound_composition`, `refinementContract_trans`, `obligations_transfer`, `refines_chain_obligations` and `p1_plan_succeeds`.

### P2 — `p2_library_extension_safety`

`Admitted gate library plan C` is defined as `gate plan C`. The library is a list of abstractions admitted by a certificate, and that argument is ignored. Extending the library does not change admission. The proof is `Iff.rfl`: P2 holds by the definition of complete mediation.

`Gate planOk plan C` is the intended shape: the certificate is accepted, and the plan meets `planOk`. A belief is not an argument.

`p2_rejected_stays_rejected` is the same fact for a plan the gate already rejects.

`admitted_plan_succeeds` sets the gate's plan condition to `PlanSucceeds task`: an admitted plan then has an accepted certificate and succeeds on the task.

`ungated_library_enlarges` is the contrast. If permission is membership of the library, then `release` is refused by the empty library and admitted once it is added.

The CERTAIN text names `p2_library_extension_safety`, `ungated_library_enlarges` and `admitted_plan_succeeds`.

### P3 — search cost

This file measures search nodes only. Cost is the number of nodes in a complete regular tree, `branching ^ depth`. Using one abstraction costs the abstract tree plus one refinement-check cost. Using none costs the concrete tree. There is no probability and no expectation. This is not the four-term cost that also counts checker calls, time and GPU use.

| Theorem | Statement |
| --- | --- |
| `p3_positive_bound` | Assumes `abstract + check ≤ concrete`, and concludes the same inequality. This does not by itself exhibit a saving. |
| `p3_positive_instance` | `costWithLibrary 2 2 1 ≤ costWithoutLibrary 2 5`, checked by `decide`. This is the concrete saving. |
| `p3_counterexample` | `costWithoutLibrary 2 3 < costWithLibrary 2 1 20`, checked by `decide`. A poor step can cost more. |

The CERTAIN text names `p3_positive_bound`, `p3_positive_instance` and `p3_counterexample`. The comparison is against an empty library, not against a hierarchy written in advance.

### Sanctions counterexample

There is one payment policy. `T` allows both a cleared and an uncleared release, so the restriction sits in `I`, not in `T`. `I` says a release is safe only when sanctions are clear. The training task and the holdout task share that policy and the payment task type. Training starts where clearance is already known, so every reachable state satisfies `I`. Holdout starts at the beginning, so an uncleared release is reachable.

The abstract task erases the clearance bit and treats every state as safe.

| Theorem | Statement |
| --- | --- |
| `shared_payment_policy` | Training and holdout use the same policy. |
| `shared_task_type` | Both are payment tasks. |
| `training_obligations` | The training task meets `Obligations`. |
| `holdout_unsafe` | The holdout task does not. `rel false` is reachable. |
| `erase_forgets_clearance` | `erase (rel false) = erase (rel true)`. |
| `sanctions_no_refinement` | For every relation `R`, there is no `RefinementContract` from the holdout task to the abstract task. The abstract task meets its obligations, so a contract would make the holdout task safe. This rests on the holdout task being unsafe; the erased bit is how the abstraction loses the deciding fact. |

The CERTAIN text names the last four. The proofs do not show that putting clearance into an assumption field restores a contract. They show that this erasure does not refine.
