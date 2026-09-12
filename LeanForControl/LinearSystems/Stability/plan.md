# Linear-system stability

## Status

| Topic | Status |
| --- | --- |
| Hurwitz and strict spectral-margin predicates | Proved/defined |
| Rate weakening, scalar shifts, empty dimension, scalar example | Proved |
| Transpose and characteristic-polynomial characterizations | Deferred |
| Lyapunov-equation existence and exponential estimates | Not implemented |

## Files

- `DefsHurwitz.lean`: predicates using complex eigenpairs of a real matrix mapped to ℂ.
- `Hurwitz.lean`: elementary consequences and the scalar sanity check.

## Design notes

Use Mathlib's `Matrix.map` directly for the real-to-complex embedding. Zero-dimensional
matrices satisfy every rate vacuously. Shifting by positive `α I` converts the bound
`Re μ < -α` into ordinary Hurwitz stability.

Reference: João P. Hespanha, *Linear Systems Theory* (2nd ed.), continuous-time stability.
The rate lemmas are direct consequences of the eigenpair criterion; the empty-dimension
convention is specific to this formalization. This foundation supports issue #9; the
indirect method remains tracked in `LeanForControl/Stability/plan.md`.
