import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Architect

/-!
# Jacobian matrices

A map `F : ℝⁿ → ℝⁿ`, on `n → ℝ`, has Jacobian matrix `A` at `x` when its derivative there is
`v ↦ A v`.

* `Matrix.toCLM` — a matrix as a continuous linear map on `n → ℝ`.
* `HasJacobianAt F A x` — `F` is differentiable at `x` with Jacobian matrix `A`.
-/

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix `A` as a continuous linear map on `n → ℝ`, `x ↦ A x`. -/
noncomputable def Matrix.toCLM (A : Matrix n n ℝ) : (n → ℝ) →L[ℝ] (n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

@[simp] lemma Matrix.toCLM_apply (A : Matrix n n ℝ) (x : n → ℝ) : A.toCLM x = A *ᵥ x := rfl

/-- **Jacobian matrix**: `F` is differentiable at `x` with Jacobian matrix `A`, that is,
with derivative `v ↦ A v`. -/
@[blueprint "def:hasJacobianAt"
  (title := "Jacobian matrix")
  (statement := /-- A map $F : \mathbb{R}^n \to \mathbb{R}^n$ has Jacobian matrix
    $A \in \mathbb{R}^{n \times n}$ at $x$ if it is differentiable at $x$ with derivative
    $DF(x) v = A v$. -/)]
abbrev HasJacobianAt (F : (n → ℝ) → n → ℝ) (A : Matrix n n ℝ) (x : n → ℝ) : Prop :=
  HasFDerivAt F A.toCLM x
