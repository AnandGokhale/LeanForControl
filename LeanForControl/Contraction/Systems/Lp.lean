import LeanForControl.Contraction.Systems.ContractionBound
import LeanForControl.LinearSystems.Stability.Continuous.HurwitzLogNorm
import Architect

/-!
# Contracting systems in weighted ℓᵖ norms

Contraction of a system on `n → ℝ` in a weighted ℓᵖ norm, certified by the Jacobian matrix.  The
weighted norm enters as the distance of `ContinuousSystem.IsContractingOn`, so the system keeps its
state space; the proofs change coordinates with
`ContinuousSystem.IsContractingOn.of_oneSidedLipschitz_conj`:

* `ContinuousSystem.IsContractingOn.of_logNormLpWeight` — `μ_{p,R}(J(t, x)) ≤ -c` on an
  open convex `C` gives contraction with rate `c` in `‖x - y‖_{p, R} = ‖R (x - y)‖_p`;
* `ContinuousSystem.IsContractingOn.of_logNormL2PosDef` — `μ_{2,P^½}(J(t, x)) ≤ -c`
  gives contraction with rate `c` in `‖x - y‖_{2,P^½} = √((x - y)ᵀ P (x - y))`;
* `ContinuousSystem.exists_isContractingOn_of_isHurwitz` — an affine system `ẋ = A x + b(t)` with
  `A` Hurwitz is contracting, with a positive rate, in `‖·‖_{2,P^½}` for some `P ≻ 0`.

Reference: F. Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), Chapter 3.
-/

open Set Real Matrix
open scoped LogNorm ENNReal
open WithLp (toLp)

namespace ContinuousSystem

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {U Y : Type*}
  {s : ContinuousSystem (n → ℝ) U Y} {u : ℝ → U} {C : Set (n → ℝ)} {c : ℝ}
  {J : ℝ → (n → ℝ) → Matrix n n ℝ}

/-- **Contraction in a weighted ℓᵖ norm from the Jacobian**: on an open convex `C`, if
`μ_{p,R}(J(t, x)) ≤ -c`, the system is contracting with rate `c` in `‖x - y‖_{p, R}`. -/
@[blueprint "thm:continuousSystem-isContractingOn-of-logNormLpWeight"
  (title := "Contraction in a weighted $\\ell_p$ norm")
  (statement := /-- Let $C \subseteq \mathbb{R}^n$ be open and convex, $p \in [1, \infty]$ and $R$
    invertible.  If $x \mapsto F(t, x, u(t))$ has Jacobian matrix $J(t, x)$
    (\cref{def:hasJacobianAt}) with $\mu_{p,R}(J(t, x)) \le -c$ for every $t$ and $x \in C$, the
    system is contracting with rate $c$ on $C$ (\cref{def:continuousSystem-isContractingOn}) in
    the distance $\|R (x - y)\|_p$. -/)]
theorem IsContractingOn.of_logNormLpWeight (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {R : Matrix n n ℝ} (hR : IsUnit R) (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hF : ∀ t, ∀ x ∈ C, HasJacobianAt (s.vectorField u t) (J t x) x)
    (hμ : ∀ t, ∀ x ∈ C, μ_{p, R} (J t x) ≤ -c) :
    s.IsContractingOn u C (fun x y => ‖x - y‖_{p, R}) c := by
  -- the identity of `ℝⁿ`, from the sup norm to `‖R x‖_p`
  let e : (n → ℝ) ≃L[ℝ] WeightedNorm (toWeight p hR) :=
    (PiLp.continuousLinearEquiv p ℝ fun _ : n => ℝ).symm.trans
      (WeightedNorm.equiv (toWeight p hR))
  -- the Jacobian test gives `osL_{p,R} ≤ -c`, which is `osL ≤ -c` in the coordinates `e`
  have h := IsContractingOn.of_oneSidedLipschitz_conj (s := s) (u := u) (C := C) (c := c) e
    fun t => by
      have hb := (oneSidedLipschitzLpWeight_eq_iSup p hR hCo hCc (hF t)).trans_le
        (iSup₂_le fun x hx => EReal.coe_le_coe_iff.2 (hμ t x hx))
      rw [oneSidedLipschitzLpWeight, dif_pos hR, WeightedNorm.oneSidedLipschitz,
        Set.image_image] at hb
      exact hb
  convert h using 3 with x y
  change _ = ‖WeightedNorm.equiv (toWeight p hR) (toLp p (x - y))‖
  rw [WeightedNorm.norm_equiv]
  rfl

/-- **Contraction in the norm `√(xᵀ P x)` from the Jacobian**: on an open convex `C`, if
`μ_{2,P^½}(J(t, x)) ≤ -c`, the system is contracting with rate `c` in `‖x - y‖_{2,P^½}`. -/
@[blueprint "thm:continuousSystem-isContractingOn-of-logNormL2PosDef"
  (title := "Contraction in a weighted Euclidean norm")
  (statement := /-- Let $C \subseteq \mathbb{R}^n$ be open and convex and $P \succ 0$.  If
    $x \mapsto F(t, x, u(t))$ has Jacobian matrix $J(t, x)$ (\cref{def:hasJacobianAt}) with
    $\mu_{2,P^{1/2}}(J(t, x)) \le -c$ for every $t$ and $x \in C$, the system is contracting with
    rate $c$ on $C$ (\cref{def:continuousSystem-isContractingOn}) in the distance
    $\sqrt{(x - y)^\top P (x - y)}$. -/)]
theorem IsContractingOn.of_logNormL2PosDef {P : Matrix n n ℝ} (hP : P.PosDef)
    (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hF : ∀ t, ∀ x ∈ C, HasJacobianAt (s.vectorField u t) (J t x) x)
    (hμ : ∀ t, ∀ x ∈ C, μ_{2,P^½} (J t x) ≤ -c) :
    s.IsContractingOn u C (fun x y => ‖x - y‖_{2,P^½}) c := by
  -- the Jacobian test gives `osL_{2,P^½} ≤ -c`, which is `osL ≤ -c` in the coordinates `equiv hP`
  have h := IsContractingOn.of_oneSidedLipschitz_conj (s := s) (u := u) (C := C) (c := c)
    (WeightedEuclidean.equiv hP) fun t => by
      have hb := (oneSidedLipschitzL2PosDef_eq_iSup hP hCo hCc (hF t)).trans_le
        (iSup₂_le fun x hx => EReal.coe_le_coe_iff.2 (hμ t x hx))
      rw [oneSidedLipschitzL2PosDef, dif_pos hP] at hb
      exact hb
  -- the norm of `equiv hP (x - y)` is `‖x - y‖_{2,P^½}` by definition
  exact h

omit [DecidableEq n] in
/-- **Hurwitz affine systems are contracting**: if `F(t, x, u(t)) = A x + b(t)` with `A` Hurwitz,
the system is contracting with some rate `c > 0` in `‖x - y‖_{2,P^½}` for some `P ≻ 0`. -/
@[blueprint "thm:continuousSystem-exists-isContractingOn-of-isHurwitz"
  (title := "Hurwitz affine systems are contracting")
  (statement := /-- If the vector field is affine, $F(t, x, u(t)) = A x + b(t)$, with $A$ Hurwitz,
    there are $P \succ 0$ and $c > 0$ such that the system is contracting with rate $c$ on
    $\mathbb{R}^n$ (\cref{def:continuousSystem-isContractingOn}) in the distance
    $\sqrt{(x - y)^\top P (x - y)}$.

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Chapter 3. -/)
  (proof := /-- A Hurwitz $A$ has $\mu_{2,P^{1/2}}(A) < 0$ for some $P \succ 0$
    (\cref{thm:isHurwitz-iff-exists-logNormL2PosDef-neg}); apply
    \cref{thm:continuousSystem-isContractingOn-of-logNormL2PosDef} with the constant
    Jacobian $A$ and $c = -\mu_{2,P^{1/2}}(A)$. -/)]
theorem exists_isContractingOn_of_isHurwitz (A : Matrix n n ℝ) (b : ℝ → n → ℝ)
    (hF : ∀ t x, s.vectorField u t x = A *ᵥ x + b t) (hA : LinearSystems.IsHurwitz A) :
    ∃ P : Matrix n n ℝ, P.PosDef ∧ ∃ c, 0 < c ∧
      s.IsContractingOn u univ (fun x y => ‖x - y‖_{2,P^½}) c := by
  classical
  -- a weight `P` with `μ_{2,P^½}(A) < 0`, and the rate `c = -μ_{2,P^½}(A)`
  obtain ⟨P, hP, hμ⟩ := (isHurwitz_iff_exists_logNormL2PosDef_neg A).1 hA
  refine ⟨P, hP, -μ_{2,P^½} A, neg_pos.2 hμ, ?_⟩
  -- the Jacobian matrix of `x ↦ A x + b(t)` is `A`
  refine IsContractingOn.of_logNormL2PosDef hP isOpen_univ convex_univ (J := fun _ _ => A)
    (fun t x _ => ?_) fun _ _ _ => by rw [neg_neg]
  rw [show s.vectorField u t = fun x => A *ᵥ x + b t from funext (hF t)]
  exact A.toCLM.hasFDerivAt.add_const (b t)

end ContinuousSystem
