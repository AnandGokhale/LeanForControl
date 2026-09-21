# Plan: Algebraic Realization Theory

This directory develops finite-dimensional realization theory from the
structural controllability, observability, and Kalman APIs. The semantic notion
of behavior is the feedthrough matrix together with the complete sequence of
Markov parameters C A^k B; it does not depend on choosing continuous or
discrete time.

References: Kailath, *Linear Systems*; Hespanha, *Linear Systems Theory*;
Kalman, “Mathematical Description of Linear Dynamical Systems” (1963).

## Status

| Result | Public API | File | Status |
|---|---|---|---|
| Realization object (A,B,C,D) | Realization | Defs.lean | done |
| Realization controllability/observability | Realization.IsControllable, Realization.IsObservable | Defs.lean | done |
| Markov parameters | Realization.markovParameter | MarkovParameters.lean | done |
| Behavioral equivalence across dimensions | BehaviorallyEquivalent | MarkovParameters.lean | done |
| Similarity equivalence-relation API | similarRefl, Similar.symm, Similar.trans | MarkovParameters.lean | done |
| Similarity invariance | Similar.behaviorallyEquivalent | MarkovParameters.lean | done |
| Minimality invariant under similarity | Similar.isMinimal_iff | Minimal.lean | done |
| Direct controllability/observability invariance under similarity | — | planned | deferred |
| Arbitrary finite Hankel matrices | hankelMatrix | Hankel.lean | done |
| Hankel factorization | hankelMatrix_eq_observability_mul_controllability | Hankel.lean | done |
| Hankel rank bounded by state dimension | hankelMatrix_rank_le_stateDim | Minimal.lean | done |
| Full Hankel rank for controllable/observable systems | hankelMatrix_rank_eq_stateDim_of_controllable_of_observable | Minimal.lean | done |
| Canonical core realization | Realization.core | Reduction.lean | done |
| Core preserves behavior | behaviorallyEquivalent_core | Reduction.lean | done |
| Quantified semantic minimality | Realization.IsMinimal | Minimal.lean | done |
| Controllable and observable implies minimal | isMinimal_of_isControllable_of_isObservable | Minimal.lean | done |
| Minimal iff controllable and observable | isMinimal_iff_isControllable_and_isObservable | Minimality.lean | done over ℂ |
| Existence of a minimal realization | exists_behaviorallyEquivalent_isMinimal | Minimality.lean | done over ℂ |
| Minimal dimension equals state-horizon Hankel rank | hankelMatrix_rank_eq_stateDim_of_isMinimal | Minimality.lean | done over ℂ |
| Behaviorally equivalent minimal realizations have equal dimension | IsMinimal.stateDim_eq_of_behaviorallyEquivalent | Minimality.lean | done |
| Reachable-only realization reduction | — | planned | deferred; core reduction already proves the milestone |
| Observable-only realization reduction | — | planned | deferred; core reduction already proves the milestone |
| Stabilization of Hankel rank over growing horizons | — | planned |
| Uniqueness of minimal realizations up to similarity | — | planned |
| Finite determinacy of Markov data | — | planned |
| Finite Ho–Kalman synthesis | — | planned |

## Dependency graph

    Realization + Markov parameters
      ├─ behavioral equivalence
      │    ├─ similarity invariance
      │    └─ Hankel invariance
      └─ arbitrary finite Hankel matrices
           ├─ observability × controllability factorization
           ├─ rank ≤ state dimension
           └─ controllable + observable ⇒ full state-horizon rank

    K1 canonical core R/(R ∩ N)
      ├─ behavior preservation
      ├─ controllable + observable
      └─ existence of a behaviorally equivalent minimal realization

    full Hankel rank + canonical core dimension
      └─ minimal ↔ controllable ∧ observable

## File ownership

- Defs.lean: bundled realization data and thin structural predicates.
- MarkovParameters.lean: external behavior and similarity.
- Hankel.lean: finite horizons, Hankel matrices, and factorization.
- Minimal.lean: quantified minimality and the generic-field Hankel argument.
- Reduction.lean: the complex canonical core as a behavior-preserving
  realization.
- Minimality.lean: the complex converse, iff milestone, and existence.
- Examples.lean: public-API and dimension-zero regression examples.

## Deferred work

- Prove monotonicity and eventual stabilization of finite Hankel ranks, then
  package the stable rank as a behavior-level invariant independent of any
  chosen realization.
- Prove that two minimal behaviorally equivalent realizations are similar.
  The existing Similar witness and invariance theorem provide the target
  relation; the missing direction requires constructing the state isomorphism
  from reachable representatives and proving it is well-defined using
  observability.
- Add direct coordinate-transport proofs that controllability and
  observability are invariant under Similar. The current realization results
  need only behavioral and minimality invariance, so this is isolated API
  completion rather than a dependency of the milestone theorem.
- Add the remaining concrete one-state, defective-state, core-reduction, and
  nontrivial similarity examples. The current regression file covers the
  zero-dimensional edge case and the public minimal-existence API.
- Establish finite determinacy via Cayley–Hamilton before exposing any finite
  Markov-parameter equality criterion; no unproved horizon bound is built into
  behavioral equivalence.
- Investigate finite Ho–Kalman synthesis only after similarity uniqueness and
  finite determinacy are complete.
- Add standalone reachable and observable realization reductions if future
  clients need them directly. The canonical core is sufficient for the
  minimality characterization and avoids duplicating quotient arguments.
- Generalize the structural core from ℂ to arbitrary fields once the K1
  quotient layer is generalized.

## Lessons learned

- Behavioral equivalence must quantify over all Markov parameters and permit
  different state dimensions; otherwise semantic minimality cannot be stated.
- Arbitrary Hankel horizons are essential: a common horizon can be compared
  between realizations with different state dimensions.
- The canonical quotient from the structural Kalman development is the right
  reduction for the converse theorem. One dimension equality simultaneously
  forces reachability and removes every unobservable reachable state.
- Keeping the Hankel rank argument field-generic isolates the current
  complex-only dependency to the canonical reduction.
