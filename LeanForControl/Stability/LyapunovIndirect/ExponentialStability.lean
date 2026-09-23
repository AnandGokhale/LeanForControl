import LeanForControl.Analysis.SpectralRadius
import LeanForControl.LinearSystems.Stability.Continuous.Hurwitz
import LeanForControl.MatrixAlgebra.Exponential
import LeanForControl.MatrixAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# A contractive exponential block for Hurwitz matrices

This file derives a discrete contractivity consequence of the Hurwitz condition without
assuming exponential decay.  The proof first establishes the reverse direction of spectral
mapping for the matrix exponential, uses the Gelfand formula to obtain a contractive power,
and then transfers that power back from the complexification to the original real matrix.

The resulting positive integer `m` is the finite block needed to construct continuous-time
decay estimates by splitting time into intervals of length `m`.

Reference: Rudin, *Functional Analysis* (Gelfand's formula and spectral mapping); Khalil,
*Nonlinear Systems* (Hurwitz matrices and exponential stability).
-/

namespace LinearSystems

open Filter Matrix Module NormedSpace Set
open scoped Matrix.Norms.Frobenius Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {n : ℕ}

/-- Every spectral value of the exponential of a complexified Hurwitz matrix lies strictly
inside the unit disk.

Reference: standard spectral mapping for the matrix exponential and the definition of a
Hurwitz matrix. -/
private lemma norm_lt_one_of_mem_spectrum_exp_complexification
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) {z : ℂ}
    (hz : z ∈ spectrum ℂ (exp (A.map (algebraMap ℝ ℂ)))) :
    ‖z‖ < 1 := by
  obtain ⟨μ, v, hv, hAv, rfl⟩ :=
    MatrixAlgebra.exists_eigenpair_of_mem_spectrum_exp (A.map (algebraMap ℝ ℂ)) hz
  rw [Complex.norm_exp]
  exact Real.exp_lt_one_iff.mpr (by simpa using hA μ v hv hAv)

/-- The exponential of a complexified Hurwitz matrix has spectral radius strictly below
one.

Reference: standard spectral mapping for the matrix exponential. -/
lemma spectralRadius_exp_complexification_lt_one
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) :
    spectralRadius ℂ (exp (A.map (algebraMap ℝ ℂ))) < 1 := by
  by_cases hn : n = 0
  · subst n
    have heq : exp (A.map (algebraMap ℝ ℂ)) = 0 := Subsingleton.elim _ _
    rw [heq, spectrum.spectralRadius_zero]
    exact zero_lt_one
  · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    apply spectrum.spectralRadius_lt_of_forall_lt
    intro z hz
    simpa only [ENNReal.coe_lt_coe] using
      norm_lt_one_of_mem_spectrum_exp_complexification hA hz

/-- A real Hurwitz matrix has a positive integer-time exponential block with Frobenius norm
strictly below one.

This is the discrete contractivity bridge used by finite-block constructions of continuous
exponential decay.  No decay or Lyapunov-equation result is assumed in its proof.

Reference: Rudin, *Functional Analysis* (Gelfand's formula); Khalil,
*Nonlinear Systems* (Hurwitz matrices and exponential stability). -/
theorem IsHurwitz.exists_norm_exp_nat_smul_lt_one
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) :
    ∃ m : ℕ, 0 < m ∧ ‖NormedSpace.exp ((m : ℝ) • A)‖ < 1 := by
  by_cases hn : n = 0
  · subst n
    refine ⟨1, Nat.zero_lt_succ 0, ?_⟩
    rw [Subsingleton.elim (exp (((1 : ℕ) : ℝ) • A)) 0]
    norm_num
  · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    obtain ⟨m, hmpos, hm⟩ := exists_pow_norm_lt_one_of_spectralRadius_lt_one
      (exp (A.map (algebraMap ℝ ℂ))) (spectralRadius_exp_complexification_lt_one hA)
    refine ⟨m, hmpos, ?_⟩
    calc
      ‖exp ((m : ℝ) • A)‖ =
          ‖(exp ((m : ℝ) • A)).map (algebraMap ℝ ℂ)‖ :=
        (Matrix.frobenius_norm_map_eq _ (algebraMap ℝ ℂ) (fun x ↦ Complex.norm_real x)).symm
      _ = ‖exp (((m : ℝ) • A).map (algebraMap ℝ ℂ))‖ := by
        rw [MatrixAlgebra.complexification_exp]
      _ = ‖exp (m • A.map (algebraMap ℝ ℂ))‖ := by
        congr 2
        ext i j
        simp
      _ = ‖exp (A.map (algebraMap ℝ ℂ)) ^ m‖ := by
        rw [Matrix.exp_nsmul]
      _ < 1 := hm

end

end LinearSystems
