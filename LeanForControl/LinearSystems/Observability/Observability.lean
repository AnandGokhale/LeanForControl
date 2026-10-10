import LeanForControl.LinearSystems.Observability.Defs
import LeanForControl.MatrixAlgebra.Rank
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Architect

/-!
# Observability of a finite-dimensional linear system

Theorems about the observability matrix and predicate defined in
`LinearSystems.Observability.Defs`, for a discrete- or continuous-time linear system

  ẋ = A x ,  y = C x

The milestone theorem is
`LinearSystems.isObservable_iff_observabilityMatrix_ker_trivial`, the bridge
between the two formulations: observability is exactly the triviality of the
kernel of the observability matrix acting by `*ᵥ`.
-/

namespace LinearSystems

open Matrix

variable {𝕜 : Type*} [Semiring 𝕜]
variable {n p : ℕ}

/-- Block-row shape lemma: row `(k, i)` of the observability matrix at
column `j` is the `(i, j)` entry of `C · Aᵏ`. Holds definitionally. -/
@[simp, blueprint "lem:observabilityMatrix-apply"
  (statement := /-- Block-row entry shape: at row $(k, i)$ and column $j$,
    the observability matrix coincides with the $(i, j)$ entry of $C\, A^{k}$:
    \[
      \mathcal{O}(A, C)_{(k,i),\, j} = (C\, A^{k})_{i,\, j}.
    \] -/)
  (proof := /-- Holds definitionally by the encoding chosen for
    \cref{def:observabilityMatrix}. -/)]
lemma observabilityMatrix_apply
    (A : Matrix (Fin n) (Fin n) 𝕜) (C : Matrix (Fin p) (Fin n) 𝕜)
    (k : Fin n) (i : Fin p) (j : Fin n) :
    observabilityMatrix A C (k, i) j = (C * A ^ (k : ℕ)) i j :=
  rfl

/-- `mulVec` of the observability matrix at row `(k, i)` equals the `i`-th
coordinate of `(C · Aᵏ) *ᵥ x`. Holds definitionally and is the workhorse
behind the milestone theorem. -/
@[blueprint "lem:observabilityMatrix-mulVec-apply"
  (statement := /-- For every state $x \in \mathbb{F}^{n}$ and every
    $(k, i) \in \mathrm{Fin}\, n \times \mathrm{Fin}\, p$,
    \[
      \bigl(\mathcal{O}(A, C) \cdot x\bigr)_{(k, i)}
        = \bigl(C\, A^{k} \cdot x\bigr)_{i}.
    \]
    This is the definitional bridge that powers
    \cref{thm:isObservable-iff-ker-trivial}. -/)
  (proof := /-- Holds by definitional unfolding of $\mathcal{O}(A, C)$
    (see \cref{def:observabilityMatrix}). -/)]
lemma observabilityMatrix_mulVec_apply
    (A : Matrix (Fin n) (Fin n) 𝕜) (C : Matrix (Fin p) (Fin n) 𝕜)
    (x : Fin n → 𝕜) (k : Fin n) (i : Fin p) :
    (observabilityMatrix A C *ᵥ x) (k, i) = ((C * A ^ (k : ℕ)) *ᵥ x) i :=
  rfl

/-- **Milestone theorem.**

A finite-dimensional linear system `(A, C)` is observable in the textbook
sense (`IsObservable`) iff the observability matrix has trivial kernel under
`*ᵥ`. -/
@[blueprint "thm:isObservable-iff-ker-trivial"
  (statement := /-- A finite-dimensional linear system $(A, C)$ is observable
    in the sense of \cref{def:isObservable} if and only if the observability
    matrix $\mathcal{O}(A, C)$ has trivial kernel under matrix-vector
    multiplication:
    \[
      \mathrm{IsObservable}(A, C)
      \iff
      \bigl(\forall x,\ \mathcal{O}(A, C) \cdot x = 0 \Rightarrow x = 0\bigr).
    \] -/)
  (proof := /-- Both directions follow from the bridge
    \cref{lem:observabilityMatrix-mulVec-apply}, which identifies the
    $(k, i)$-coordinate of $\mathcal{O}(A, C) \cdot x$ with the
    $i$-coordinate of $(C\, A^{k}) \cdot x$. The forward direction reads
    the per-power kernel out of the assembled kernel coordinatewise; the
    reverse direction packs them back. -/)]
theorem isObservable_iff_observabilityMatrix_ker_trivial
    (A : Matrix (Fin n) (Fin n) 𝕜) (C : Matrix (Fin p) (Fin n) 𝕜) :
    IsObservable A C ↔
      ∀ x : Fin n → 𝕜, observabilityMatrix A C *ᵥ x = 0 → x = 0 := by
  constructor
  · -- (→) Observability implies trivial kernel of `observabilityMatrix`.
    intro hObs x hx
    refine hObs x ?_
    intro k
    funext i
    have hki : (observabilityMatrix A C *ᵥ x) (k, i) = 0 := congrFun hx (k, i)
    -- The bridge lemma identifies this coordinate with `((C · Aᵏ) *ᵥ x) i`.
    rw [observabilityMatrix_mulVec_apply] at hki
    simpa using hki
  · -- (←) Trivial kernel of `observabilityMatrix` implies observability.
    intro hKer x hx
    refine hKer x ?_
    funext ki
    obtain ⟨k, i⟩ := ki
    rw [observabilityMatrix_mulVec_apply]
    have hk : (C * A ^ (k : ℕ)) *ᵥ x = 0 := hx k
    -- Read off the `i`-th coordinate of the vanishing vector.
    have := congrFun hk i
    simpa using this

/-!
## Follow-ups for the Hautus track

The following helpers were not needed to prove
`isObservable_iff_observabilityMatrix_ker_trivial`, but will be needed before
attacking either Hautus or the rank-based reformulations:

* a rank-vs-trivial-kernel bridge for matrices of shape `Matrix (m × p) n 𝕜`,
  most naturally phrased through `Matrix.toLin'` and `LinearMap.ker`;
* block-matrix rank lemmas for stacked rows
  `[A₁ ; A₂ ; … ; Aₖ]`, lifting per-block kernels to the stack and back;
* a transition from `(C · Aᵏ) *ᵥ x = 0 ∀ k < n` to invariance of the
  unobservable subspace under `A` (Cayley–Hamilton style argument), needed
  to extract eigenvectors for the Hautus direction;
* coercion lemmas between `(C * A^k) *ᵥ x` and `C *ᵥ (A^k *ᵥ x)`, which
  are useful when restating observability in terms of trajectories rather
  than matrix powers.

These belong in `MatrixAlgebra.Rank` (matrix-level facts) and a future
`LinearSystems.Observability.Hautus` (control-level facts) once needed.
-/

end LinearSystems

/-!
## Rank-form characterization

We reopen `namespace LinearSystems` in a fresh section over `[Field 𝕜]` so
the typeclass diamond between the outer `[Semiring 𝕜]` (used for the
existing definitions and the kernel-form milestone) and the rank-side
`[Field 𝕜]` is broken: in the section below, the only scalar-typeclass on
`𝕜` is `Field`, and the `Semiring` derived from it is the canonical one,
matching the instance picked by `MatrixAlgebra.Rank`.
-/

namespace LinearSystems

open Matrix

variable {𝕜 : Type*} [Field 𝕜] {n p : ℕ}

/-- Rank-form characterization: observability is equivalent to the
observability matrix having full column rank. Chains the kernel-form
milestone with the matrix bridge from `MatrixAlgebra.Rank`. -/
@[blueprint "thm:isObservable-iff-rank"
  (statement := /-- A finite-dimensional system $(A, C)$ is observable if
    and only if the observability matrix $\mathcal{O}(A, C)$ has full column
    rank, i.e.
    \[
      \operatorname{rank} \mathcal{O}(A, C) = n,
    \]
    where $n$ is the state dimension. -/)
  (proof := /-- Chain the kernel-form milestone
    \cref{thm:isObservable-iff-ker-trivial} with the matrix-level bridge
    $\bigl(\forall x,\ M \cdot x = 0 \Rightarrow x = 0\bigr) \iff
     \operatorname{rank} M = n$ from `MatrixAlgebra.Rank`, applied with
    $M = \mathcal{O}(A, C)$. -/)]
theorem isObservable_iff_observabilityMatrix_rank_eq
    (A : Matrix (Fin n) (Fin n) 𝕜) (C : Matrix (Fin p) (Fin n) 𝕜) :
    IsObservable A C ↔ Matrix.rank (observabilityMatrix A C) = n := by
  refine (isObservable_iff_observabilityMatrix_ker_trivial A C).trans ?_
  refine (MatrixAlgebra.mulVec_kernel_trivial_iff_rank_eq_card_cols
    (observabilityMatrix A C)).trans ?_
  rw [Fintype.card_fin]

/-- Membership in the unobservable subspace means that every finite-horizon
output vanishes.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Theorem 15.7 (observability-matrix kernel);
the algebraic characterization here is a derived consequence. -/
@[blueprint "lem:mem-unobservableSubspace-iff"
  (statement := /-- A state $x$ belongs to $\mathcal N(A,C)$ if and only if
    $CA^k x=0$ for every $k=0,\ldots,n-1$. -/)]
lemma mem_unobservableSubspace_iff
    {A : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin p) (Fin n) ℂ}
    (v : Fin n → ℂ) :
    v ∈ unobservableSubspace A C
      ↔ ∀ k : Fin n, (C * A ^ (k : ℕ)) *ᵥ v = 0 := by
  simp [unobservableSubspace, Submodule.mem_iInf, LinearMap.mem_ker]

/-- The unobservable subspace is trivial exactly when the system is observable
in the textbook sense `IsObservable`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Theorem 15.7 (observability-matrix kernel);
the algebraic characterization here is a derived consequence. -/
@[blueprint "thm:unobservable-eq-bot-iff-observable"
  (statement := /-- A finite-dimensional system $(A, C)$ is observable in the
    sense of \cref{def:isObservable} if and only if its unobservable subspace
    is trivial:
    \[
      \mathcal{N}(A, C) = \{0\} \iff \mathrm{IsObservable}(A, C).
    \] -/)
  (proof := /-- Both directions are membership unfoldings of
    \cref{def:unobservableSubspace} against \cref{def:isObservable}. -/)]
theorem unobservableSubspace_eq_bot_iff_isObservable
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    unobservableSubspace A C = ⊥ ↔ IsObservable A C := by
  rw [Submodule.eq_bot_iff]
  unfold IsObservable
  refine ⟨fun h v hv => ?_, fun h v hv => ?_⟩
  · exact h v ((mem_unobservableSubspace_iff v).mpr hv)
  · exact h v ((mem_unobservableSubspace_iff v).mp hv)

/-- Cayley-Hamilton consequence: a vector in the unobservable subspace is
also annihilated by `C * A^n`, not just by `C * A^k` for `k < n`. The single
extra power closes the gap that `A`-invariance needs. -/
private lemma mulVec_aPowN_eq_zero_of_mem_unobservableSubspace
    {A : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin p) (Fin n) ℂ}
    {v : Fin n → ℂ} (hv : v ∈ unobservableSubspace A C) :
    (C * A ^ n) *ᵥ v = 0 := by
  rw [mem_unobservableSubspace_iff] at hv
  -- Cayley-Hamilton in matrix form, multiplied on the left by `C` and
  -- evaluated at `v`.
  have hCH := Matrix.aeval_self_charpoly A
  have h_apply : (C * Polynomial.aeval A A.charpoly) *ᵥ v = 0 := by
    rw [hCH, Matrix.mul_zero, Matrix.zero_mulVec]
  -- Expand `aeval` as a finite sum and use the degree of `charpoly`.
  have hdeg : A.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [Polynomial.aeval_eq_sum_range, hdeg, Finset.sum_range_succ] at h_apply
  -- Isolate the leading `A^n` term using monicity of `charpoly`.
  have hmonic : A.charpoly.coeff n = 1 := by
    have hL := A.charpoly_monic
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg] at hL
    exact hL
  rw [hmonic, one_smul, Matrix.mul_add, Matrix.add_mulVec] at h_apply
  -- The remaining sum vanishes term-by-term because each `(C * A^i) *ᵥ v = 0`.
  have hsum : (C * ∑ i ∈ Finset.range n, A.charpoly.coeff i • A ^ i) *ᵥ v = 0 := by
    rw [Matrix.mul_sum, Matrix.sum_mulVec]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Matrix.mul_smul, Matrix.smul_mulVec, hv ⟨i, hi⟩, smul_zero]
  rw [hsum, zero_add] at h_apply
  exact h_apply

/-- The unobservable subspace is `A`-invariant: applying `A` to any
unobservable state keeps it unobservable. The proof for the boundary case
`k = n - 1` uses Cayley-Hamilton through
`mulVec_aPowN_eq_zero_of_mem_unobservableSubspace`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Theorem 15.7 (observability-matrix kernel);
the algebraic characterization here is a derived consequence. -/
@[blueprint "lem:unobservableSubspace-invariant"
  (statement := /-- The unobservable subspace is closed under the action of
    $A$: for every $v \in \mathcal{N}(A, C)$, also $A\, v \in \mathcal{N}(A, C)$. -/)
  (proof := /-- For $k = 0, \dots, n-2$ this is direct from the definition.
    For $k = n - 1$ we land at $C\, A^{n}\, v$, which Cayley-Hamilton
    rewrites as a $\mathbb{C}$-linear combination of $C\, A^{i}\, v$ for
    $i < n$. Each of those is zero, so the combination is zero. -/)]
lemma A_mulVec_mem_unobservableSubspace_of_mem
    {A : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin p) (Fin n) ℂ}
    {v : Fin n → ℂ} (hv : v ∈ unobservableSubspace A C) :
    A *ᵥ v ∈ unobservableSubspace A C := by
  rw [mem_unobservableSubspace_iff]
  intro k
  -- Bridge `(C * A^k.val) *ᵥ (A *ᵥ v) = (C * A^(k.val + 1)) *ᵥ v`.
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, ← pow_succ]
  by_cases hk : k.val + 1 < n
  · exact (mem_unobservableSubspace_iff v).mp hv ⟨k.val + 1, hk⟩
  · -- `k.val + 1 = n`, so use the Cayley-Hamilton helper.
    push Not at hk
    have heq : k.val + 1 = n := by omega
    rw [heq]
    exact mulVec_aPowN_eq_zero_of_mem_unobservableSubspace hv

/-- The unobservable subspace is exactly the kernel of the observability
matrix acting by matrix-vector multiplication.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Theorem 15.7 (observability-matrix kernel);
the algebraic characterization here is a derived consequence. -/
@[blueprint "thm:unobservableSubspace-eq-ker-observabilityMatrix"
  (statement := /-- The unobservable subspace is the kernel of the
    observability matrix:
    \[
      \mathcal N(A,C)=\ker \mathcal O(A,C).
    \] -/)]
theorem unobservableSubspace_eq_ker_observabilityMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    unobservableSubspace A C =
      LinearMap.ker (observabilityMatrix A C).mulVecLin := by
  ext v
  simp only [unobservableSubspace, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h
    funext ki
    exact congrFun (h ki.1) ki.2
  · intro h k
    funext i
    exact congrFun h (k, i)

/-- The dimension of the unobservable subspace plus the rank of the
observability matrix is the state dimension.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Theorem 15.7 (observability-matrix kernel);
the algebraic characterization here is a derived consequence.
This is the rank-nullity consequence of the observability-matrix kernel description. -/
@[blueprint "thm:unobservableSubspace-finrank-add-rank"
  (statement := /-- The dimension of the unobservable subspace plus the rank
    of the observability matrix is the state dimension:
    \[
      \dim \mathcal N(A,C)+\operatorname{rank}\mathcal O(A,C)=n.
    \] -/)]
theorem finrank_unobservableSubspace_add_rank_observabilityMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    Module.finrank ℂ (unobservableSubspace A C) +
      Matrix.rank (observabilityMatrix A C) = n := by
  rw [unobservableSubspace_eq_ker_observabilityMatrix]
  have h :=
    LinearMap.finrank_range_add_finrank_ker (observabilityMatrix A C).mulVecLin
  rw [Module.finrank_pi, Fintype.card_fin] at h
  unfold Matrix.rank
  omega

/-- The unobservable subspace is contained in the output kernel.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Theorem 15.7 (observability-matrix kernel);
the algebraic characterization here is a derived consequence.
This follows from the zero-time output condition. -/
@[blueprint "lem:unobservableSubspace-le-ker-C"
  (statement := /-- The unobservable subspace is contained in the output
    kernel: $\mathcal N(A,C)\subseteq\ker C$. -/)]
lemma unobservableSubspace_le_ker_C
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    unobservableSubspace A C ≤ LinearMap.ker C.mulVecLin := by
  intro x hx
  rw [LinearMap.mem_ker]
  by_cases hn : n = 0
  · subst n
    have hx0 : x = 0 := Subsingleton.elim _ _
    rw [hx0, map_zero]
  · have h0 :=
      (show ∀ k : Fin n, (C * A ^ (k : ℕ)) *ᵥ x = 0 from
        by simpa [unobservableSubspace, Submodule.mem_iInf, LinearMap.mem_ker] using hx)
        ⟨0, Nat.pos_of_ne_zero hn⟩
    simpa using h0

/-- Every `A`-invariant subspace contained in the output kernel is contained
in the unobservable subspace.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Theorem 15.7 (observability-matrix kernel);
the algebraic characterization here is a derived consequence.
This is a derived invariant-subspace characterization. -/
@[blueprint "thm:unobservableSubspace-greatest-invariant"
  (statement := /-- Every $A$-invariant subspace contained in $\ker C$ is
    contained in the unobservable subspace. -/)]
theorem le_unobservableSubspace_of_invariant_of_le_ker
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (S : Submodule ℂ (Fin n → ℂ))
    (hA : S ∈ Module.End.invtSubmodule A.mulVecLin)
    (hC : S ≤ LinearMap.ker C.mulVecLin) :
    S ≤ unobservableSubspace A C := by
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hA
  intro x hx
  simp only [unobservableSubspace, Submodule.mem_iInf, LinearMap.mem_ker]
  intro k
  have hpow : ∀ j : ℕ, A ^ j *ᵥ x ∈ S := by
    intro j
    induction j with
    | zero => simpa using hx
    | succ j ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec]
        exact hA _ ih
  have hzero := hC (hpow k)
  rw [LinearMap.mem_ker] at hzero
  change (C * A ^ (k : ℕ)) *ᵥ x = 0
  rw [← Matrix.mulVec_mulVec]
  exact hzero

end LinearSystems
