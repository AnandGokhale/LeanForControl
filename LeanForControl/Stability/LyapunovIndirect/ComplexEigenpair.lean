import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Real/imaginary transport along a complexified eigenpair

If `v` is a complex eigenvector of the entrywise complexification of a real matrix `A`
with eigenvalue `μ`, then for any complex scalar `c`, the real matrix `A` maps the real
(resp. imaginary) part of `c • v` to the real (resp. imaginary) part of `c * μ • v`. This
is the shared real-vector transport fact behind both branches of Lyapunov's indirect
method: the stable branch uses it (at a time-varying `c`) to convert a growing complex
eigenmode into a real solution, and the unstable branch uses it (at `c = 1`) to split a
positive-real-part eigenvector into its real and imaginary components.

Reference: standard complex-eigenvector-to-real-vector transport for real matrices.
-/

namespace LinearSystems

open Matrix

variable {n : ℕ}

lemma matrixMulVec_re_smul_eigenpair
    (A : Matrix (Fin n) (Fin n) ℝ) (μ c : ℂ) (v : Fin n → ℂ)
    (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    (fun i ↦ (c * μ * v i).re) = A *ᵥ (fun i ↦ (c * v i).re) := by
  ext i
  have hi := congrFun heig i
  change (c * μ * v i).re = ∑ j, A i j * (c * v j).re
  change (∑ j, (A i j : ℂ) * v j) = μ * v i at hi
  rw [mul_assoc c μ (v i), ← hi]
  rw [Finset.mul_sum]
  rw [← Complex.reCLM_apply, map_sum]
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

lemma matrixMulVec_im_smul_eigenpair
    (A : Matrix (Fin n) (Fin n) ℝ) (μ c : ℂ) (v : Fin n → ℂ)
    (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    (fun i ↦ (c * μ * v i).im) = A *ᵥ (fun i ↦ (c * v i).im) := by
  ext i
  have hi := congrFun heig i
  change (c * μ * v i).im = ∑ j, A i j * (c * v j).im
  change (∑ j, (A i j : ℂ) * v j) = μ * v i at hi
  rw [mul_assoc c μ (v i), ← hi]
  rw [Finset.mul_sum]
  rw [← Complex.imCLM_apply, map_sum]
  simp only [Complex.imCLM_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

end LinearSystems
