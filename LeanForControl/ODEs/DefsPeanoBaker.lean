import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Architect

/-!
# Definitions for the Peano-Baker series

The Peano-Baker series of a time-varying coefficient `A : ℝ → 𝔸` in a real normed algebra `𝔸`:
the solution of `Ż = A(t) Z`, `Z(t₀) = 1`, as a series of iterated integrals.  Its theory is in
`PeanoBaker.lean`; linear systems use it with `𝔸 = E →L[ℝ] E` (`LinearSystems/Solutions`).

* `peanoBakerTerm` — the `k`-th iterated-integral term of the series.
* `stateTransitionMatrix` — the series itself, `Φ(t, t₀) := ∑' k, peanoBakerTerm A k t t₀`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5.
-/

namespace LinearSystems

section BanachAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- The `k`-th term of the Peano-Baker series for a time-varying coefficient `A`:
`peanoBakerTerm A 0 t t₀ = 1` and
`peanoBakerTerm A (k+1) t t₀ = ∫ s in t₀..t, A s * peanoBakerTerm A k s t₀`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5 (Peano-Baker series). -/
@[blueprint "def:peanoBakerTerm"
  (title := "Peano--Baker term")
  (statement := /-- The $k$-th term of the Peano--Baker series for a time-varying state
    coefficient $A(t)$:
    \[
      P_0(t,t_0) := 1, \qquad
      P_{k+1}(t,t_0) := \int_{t_0}^{t} A(s)\, P_k(s,t_0)\,\mathrm{d}s.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5 (Peano-Baker series).
  -/)]
noncomputable def peanoBakerTerm (A : ℝ → 𝔸) : ℕ → ℝ → ℝ → 𝔸
  | 0,     _, _  => 1
  | k + 1, t, t₀ => ∫ s in t₀..t, A s * peanoBakerTerm A k s t₀

/-- The *state transition matrix* of a time-varying linear system `ẋ = A(t) x`, given by the
Peano-Baker series `Φ(t, t₀) := ∑' k, peanoBakerTerm A k t t₀`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.1
(Peano-Baker series). -/
@[blueprint "def:stateTransitionMatrix"
  (title := "State transition matrix")
  (statement := /-- The \emph{state transition matrix} $\Phi(t,t_0)$, given by the
    Peano--Baker series
    \[
      \Phi(t,t_0) := \sum_{k=0}^{\infty} P_k(t,t_0).
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Theorem 5.1 (Peano-Baker
    series).
  -/)]
noncomputable def stateTransitionMatrix (A : ℝ → 𝔸) (t t₀ : ℝ) : 𝔸 :=
  ∑' k, peanoBakerTerm A k t t₀

end BanachAlgebra

end LinearSystems
