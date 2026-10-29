# Plan: convex analysis — rework needed

`Analysis/ConvexAnalysis/` (subdifferentials, the proximal operator, cocoercivity of convex
gradients) was written quickly as support for proximal gradient dynamics and needs a rework before
it is part of the library proper.

Remaining work only; done items are removed.

## Known issues

| Issue | What is needed |
|---|---|
| Not imported by `LeanForControl.lean`, so CI never builds it | add the import once the files are reworked |
| No blueprint nodes | nodes for the definitions and main results |
| `ConvexOn.baillon_haddad` is not readable to a control theorist | rename to `ConvexOn.cocoercive_gradient`, keeping "Baillon–Haddad theorem" in the docstring title; rename `BaillonHaddad.lean` to match |
| An extended-valued `R : X → ℝ ∪ {+∞}` is encoded as a pair `(R, D)` (`IsClosedConvexProper R D`), because Mathlib has no convexity for `EReal`-valued functions | sanity lemmas tying the encoding to the extended-valued function: lower semicontinuity of `R` on `D` ⟺ of its `EReal` extension; `prox` of the indicator of `D` is the projection onto `D` |
| `prox` is total, with the junk value `v` when no minimizer exists | check that every result states its hypotheses so the junk value never matters |
