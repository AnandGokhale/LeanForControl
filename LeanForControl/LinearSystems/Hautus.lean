import LeanForControl.LinearSystems.Controllability
import LeanForControl.LinearSystems.Observability
import LeanForControl.LinearSystems.MatrixLemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Architect

/-!
# Hautus observability lemma

For a finite-dimensional linear system over `ℂ`,

  `IsObservable A C ↔ ∀ μ ∈ ℂ, the block matrix `[μI - A; C]` has trivial kernel`.

This file proves both directions and packages them as the iff
`isObservable_iff_hautus`. The whole development is over `ℂ` (per the
project note: eigenvalues live in `ℂ`).

The structure is:

* `unobservableSubspace A C` — the `A`-invariant submodule of vectors that
  are killed by every `C * A^k`.
* Cayley-Hamilton helper: vectors in `unobservableSubspace` are killed by
  `C * A^n` too, not just `C * A^k` for `k < n`.
* `A`-invariance of `unobservableSubspace`.
* `hautusObservabilityMatrix A C μ` — the block-row matrix `[μI - A; C]`.
* Failure direction: `¬ IsObservable A C → ∃ μ, witness vector` via
  eigenvector extraction on `unobservableSubspace`.
* Converse: a Hautus-failure witness violates observability directly.
* Full iff packaged at the bottom.
-/

namespace LinearSystems

open Matrix

variable {n p : ℕ}

/-- The unobservable subspace of `(A, C)`: states that the output `C · A^k`
fails to distinguish from zero for every `k = 0, …, n-1`.

Defined as the intersection of the kernels of the linear maps
`(C · A^k).mulVecLin` for `k : Fin n`. By Cayley–Hamilton (see
`A_mulVec_mem_unobservableSubspace_of_mem`) this submodule is `A`-invariant. -/
@[blueprint "def:unobservableSubspace"
  (statement := /-- The \emph{unobservable subspace} of $(A, C)$ is the
    $A$-invariant subspace
    \[
      \mathcal{N}(A, C) \;=\;
        \{\, v \in \mathbb{C}^{n} \;:\;
            C\, A^{k}\, v = 0 \text{ for every } k = 0, 1, \dots, n - 1 \,\}.
    \]
    Equivalently, $\mathcal{N}(A, C) = \ker \mathcal{O}(A, C)$, but here it
    is phrased without naming $\mathcal{O}$ so the bridge
    \cref{thm:unobservable-eq-bot-iff-observable} reads as content. -/)]
noncomputable def unobservableSubspace
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    Submodule ℂ (Fin n → ℂ) :=
  ⨅ k : Fin n, LinearMap.ker (C * A ^ (k : ℕ)).mulVecLin

lemma mem_unobservableSubspace_iff
    {A : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin p) (Fin n) ℂ}
    (v : Fin n → ℂ) :
    v ∈ unobservableSubspace A C
      ↔ ∀ k : Fin n, (C * A ^ (k : ℕ)) *ᵥ v = 0 := by
  simp [unobservableSubspace, Submodule.mem_iInf, LinearMap.mem_ker]

/-- The unobservable subspace is trivial exactly when the system is observable
in the textbook sense `IsObservable`. -/
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
`mulVec_aPowN_eq_zero_of_mem_unobservableSubspace`. -/
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
    have hk_lt : k.val < n := k.isLt
    have heq : k.val + 1 = n := by omega
    rw [heq]
    exact mulVec_aPowN_eq_zero_of_mem_unobservableSubspace hv

/-- If the unobservable subspace is non-trivial, it contains a nonzero
eigenvector of `A` (over `ℂ`). The eigenvector lifts to the ambient space
`Fin n → ℂ` and is automatically annihilated by `C` (membership at `k = 0`). -/
private theorem exists_eigenvector_of_unobservableSubspace_neBot
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (h : unobservableSubspace A C ≠ ⊥) :
    ∃ μ : ℂ, ∃ v : Fin n → ℂ, v ≠ 0 ∧ A *ᵥ v = μ • v ∧ C *ᵥ v = 0 := by
  haveI hNontriv : Nontrivial (unobservableSubspace A C) :=
    (Submodule.nontrivial_iff_ne_bot).mpr h
  -- The ambient space `Fin n → ℂ` must itself be non-trivial, hence `0 < n`.
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      apply h
      subst hn
      rw [Submodule.eq_bot_iff]
      intro v _
      funext i
      exact i.elim0
    · exact hn
  -- Restrict `A.mulVecLin` to the (A-invariant) unobservable subspace.
  let A_res : Module.End ℂ (unobservableSubspace A C) :=
    A.mulVecLin.restrict
      (fun _ hw => A_mulVec_mem_unobservableSubspace_of_mem hw)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A_res
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, w.val, ?_, ?_, ?_⟩
  · -- The eigenvector is nonzero in the ambient space.
    intro hzero
    exact hw.2 (Subtype.ext hzero)
  · -- Lift the eigenvalue equation through `Submodule.subtype`.
    have heig : A_res w = μ • w := hw.apply_eq_smul
    have hval := congrArg Subtype.val heig
    simpa [A_res, LinearMap.restrict_apply, Matrix.mulVecLin_apply] using hval
  · -- Membership at `k = 0` reads off `C *ᵥ w.val = 0`.
    have hmem : w.val ∈ unobservableSubspace A C := w.2
    rw [mem_unobservableSubspace_iff] at hmem
    have h0 := hmem ⟨0, hn_pos⟩
    rw [show ((⟨0, hn_pos⟩ : Fin n) : ℕ) = 0 from rfl,
        pow_zero, Matrix.mul_one] at h0
    exact h0

/-- The Hautus observability matrix at `μ`,
`[μ • 1 - A; C] : Matrix (Fin n ⊕ Fin p) (Fin n) ℂ`. -/
@[blueprint "def:hautusObservabilityMatrix"
  (statement := /-- The \emph{Hautus observability matrix} of $(A, C)$ at
    a complex number $\mu$ is the block-row matrix
    \[
      H_{A, C}(\mu) \;=\; \begin{bmatrix} \mu I - A \\ C \end{bmatrix}
        \in \mathbb{C}^{(n + p) \times n} .
    \] -/)]
noncomputable def hautusObservabilityMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ) :
    Matrix (Fin n ⊕ Fin p) (Fin n) ℂ :=
  Matrix.fromRows (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A) C

/-- A vector `v` is in the kernel of `H_{A, C}(μ) *ᵥ ·` iff `v` is an
eigenvector (or zero) of `A` with eigenvalue `μ` and is annihilated by `C`. -/
@[blueprint "lem:hautus-mulVec-eq-zero-iff"
  (statement := /-- For every $\mu \in \mathbb{C}$ and $v \in \mathbb{C}^{n}$,
    \[
      H_{A, C}(\mu) \cdot v = 0
        \iff
      \bigl(A\, v = \mu\, v \;\wedge\; C\, v = 0\bigr). -/)]
lemma hautusObservabilityMatrix_mulVec_eq_zero_iff
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (μ : ℂ) (v : Fin n → ℂ) :
    hautusObservabilityMatrix A C μ *ᵥ v = 0
      ↔ A *ᵥ v = μ • v ∧ C *ᵥ v = 0 := by
  unfold hautusObservabilityMatrix
  rw [Matrix.fromRows_mulVec]
  -- Sum.elim a b = 0 ↔ a = 0 ∧ b = 0
  constructor
  · intro h
    have h1 : (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A) *ᵥ v = 0 := by
      funext i
      simpa using congrFun h (Sum.inl i)
    have h2 : C *ᵥ v = 0 := by
      funext j
      simpa using congrFun h (Sum.inr j)
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
    exact ⟨(sub_eq_zero.mp h1).symm, h2⟩
  · rintro ⟨hAv, hCv⟩
    funext x
    cases x with
    | inl i =>
      simp only [Sum.elim_inl, Pi.zero_apply]
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAv]
      simp
    | inr j =>
      simp only [Sum.elim_inr, Pi.zero_apply]
      simpa using congrFun hCv j

/-- **Failure direction of observability Hautus.** A non-observable system
admits a complex Hautus failure: some `μ ∈ ℂ` and a nonzero vector `v` such
that `[μ I - A; C] · v = 0`. -/
@[blueprint "thm:not-isObservable-implies-hautus-failure"
  (statement := /-- If $(A, C)$ is not observable, then there exists
    $\mu \in \mathbb{C}$ and a nonzero vector $v \in \mathbb{C}^{n}$ such that
    \[
      H_{A, C}(\mu) \cdot v = 0,
    \]
    i.e. $\mu$ is an eigenvalue of $A$ with an eigenvector in $\ker C$. -/)
  (proof := /-- The unobservable subspace
    \cref{def:unobservableSubspace} is nontrivial by
    \cref{thm:unobservable-eq-bot-iff-observable}. It is $A$-invariant by
    \cref{lem:unobservableSubspace-invariant}, hence finite-dimensional and
    invariant; over $\mathbb{C}$ this guarantees a nonzero eigenvector
    inside it. That vector is automatically in $\ker C$ (membership at
    $k = 0$), so it lies in the kernel of $H_{A, C}(\mu)$ via
    \cref{lem:hautus-mulVec-eq-zero-iff}. -/)]
theorem not_isObservable_implies_hautus_failure
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (h : ¬ IsObservable A C) :
    ∃ μ : ℂ, ∃ v : Fin n → ℂ,
      v ≠ 0 ∧ hautusObservabilityMatrix A C μ *ᵥ v = 0 := by
  have hN : unobservableSubspace A C ≠ ⊥ := fun hbot =>
    h ((unobservableSubspace_eq_bot_iff_isObservable A C).mp hbot)
  obtain ⟨μ, v, hne, hAv, hCv⟩ :=
    exists_eigenvector_of_unobservableSubspace_neBot A C hN
  refine ⟨μ, v, hne, ?_⟩
  rw [hautusObservabilityMatrix_mulVec_eq_zero_iff]
  exact ⟨hAv, hCv⟩

/-- **Converse direction of observability Hautus.** A Hautus failure at any
`μ ∈ ℂ` with witness `v ≠ 0` implies the system is not observable. -/
@[blueprint "thm:hautus-failure-implies-not-isObservable"
  (statement := /-- If $\mu \in \mathbb{C}$ and $v \neq 0$ satisfy
    $H_{A, C}(\mu) \cdot v = 0$, then $(A, C)$ is not observable. -/)
  (proof := /-- The witness gives $A v = \mu v$ and $C v = 0$. By induction
    on $k$, $A^{k} v = \mu^{k} v$, so $C\, A^{k}\, v = \mu^{k}\, C v = 0$ for
    every $k$. The vector $v$ is therefore in the unobservable subspace and
    is nonzero, so observability fails. -/)]
theorem hautus_failure_implies_not_isObservable
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (μ : ℂ) (v : Fin n → ℂ) (hv : v ≠ 0)
    (h : hautusObservabilityMatrix A C μ *ᵥ v = 0) :
    ¬ IsObservable A C := by
  rw [hautusObservabilityMatrix_mulVec_eq_zero_iff] at h
  obtain ⟨hAv, hCv⟩ := h
  have hpow : ∀ j : ℕ, A ^ j *ᵥ v = μ ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih,
          smul_smul]
      congr 1
      ring
  intro hObs
  apply hv
  apply hObs
  intro k
  rw [← Matrix.mulVec_mulVec, hpow, Matrix.mulVec_smul, hCv, smul_zero]

/-- **Observability Hautus lemma.** For a finite-dimensional linear system
over `ℂ`, the system is observable if and only if for every `μ ∈ ℂ`, the
Hautus block `[μ I - A; C]` has trivial kernel. -/
@[blueprint "thm:isObservable-iff-hautus"
  (statement := /-- A finite-dimensional system $(A, C)$ over $\mathbb{C}$
    is observable if and only if for every $\mu \in \mathbb{C}$ the Hautus
    matrix $H_{A, C}(\mu)$ has trivial kernel:
    \[
      \mathrm{IsObservable}(A, C)
      \iff
      \forall \mu \in \mathbb{C},\ \ker H_{A, C}(\mu) = \{0\}.
    \] -/)
  (proof := /-- Combine
    \cref{thm:not-isObservable-implies-hautus-failure} (failure direction)
    and \cref{thm:hautus-failure-implies-not-isObservable} (converse). -/)]
theorem isObservable_iff_hautus
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    IsObservable A C
      ↔ ∀ μ : ℂ,
          LinearMap.ker (hautusObservabilityMatrix A C μ).mulVecLin = ⊥ := by
  constructor
  · intro hObs μ
    rw [Matrix.ker_mulVecLin_eq_bot_iff]
    intro v hker
    by_contra hv
    exact hautus_failure_implies_not_isObservable A C μ v hv hker hObs
  · intro hHautus
    by_contra hNotObs
    obtain ⟨μ, v, hv, hker⟩ :=
      not_isObservable_implies_hautus_failure A C hNotObs
    have hμ := hHautus μ
    rw [Matrix.ker_mulVecLin_eq_bot_iff] at hμ
    exact hv (hμ v hker)

end LinearSystems

/-!
## Hautus controllability via duality

Controllability Hautus is the dual of observability Hautus. Rather than
mirror the entire eigenvector argument, we route through the bridge
`IsControllable A B ↔ IsObservable Aᵀ Bᵀ` and reuse the observability
results from above. The key matrix identity is
`(controllabilityMatrix A B)ᵀ = observabilityMatrix Aᵀ Bᵀ`, which makes
the rank-form characterizations match across the duality. -/

namespace LinearSystems

open Matrix

variable {n m : ℕ}

/-- The transpose of the controllability matrix is the observability matrix
of the transposed system: `𝒞(A, B)ᵀ = 𝒪(Aᵀ, Bᵀ)`. -/
lemma controllabilityMatrix_transpose
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    (controllabilityMatrix A B)ᵀ = observabilityMatrix Aᵀ Bᵀ := by
  ext ki j
  obtain ⟨k, i⟩ := ki
  rw [Matrix.transpose_apply, controllabilityMatrix_apply,
      observabilityMatrix_apply,
      ← Matrix.transpose_pow,
      ← Matrix.transpose_mul,
      Matrix.transpose_apply]

/-- **Duality bridge.** A linear system `(A, B)` is controllable iff the
transposed system `(Aᵀ, Bᵀ)` is observable. -/
theorem isControllable_iff_isObservable_transpose
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    IsControllable A B ↔ IsObservable Aᵀ Bᵀ := by
  rw [isControllable_iff_controllabilityMatrix_rank_eq,
      isObservable_iff_observabilityMatrix_rank_eq Aᵀ Bᵀ,
      ← controllabilityMatrix_transpose,
      Matrix.rank_transpose]

/-- The Hautus controllability matrix at `μ`, `[μI - A | B]`. -/
@[blueprint "def:hautusControllabilityMatrix"
  (statement := /-- The \emph{Hautus controllability matrix} of $(A, B)$
    at a complex number $\mu$ is the block-column matrix
    \[
      H^{\mathrm{ctrl}}_{A, B}(\mu)
        \;=\; \begin{bmatrix} \mu I - A & B \end{bmatrix}
        \in \mathbb{C}^{n \times (n + m)} .
    \] -/)]
noncomputable def hautusControllabilityMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ) :
    Matrix (Fin n) (Fin n ⊕ Fin m) ℂ :=
  Matrix.fromCols (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A) B

/-- The transpose of the Hautus controllability matrix is the Hautus
observability matrix of the transposed system. -/
lemma hautusControllabilityMatrix_transpose
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ) :
    (hautusControllabilityMatrix A B μ)ᵀ = hautusObservabilityMatrix Aᵀ Bᵀ μ := by
  unfold hautusControllabilityMatrix hautusObservabilityMatrix
  rw [Matrix.transpose_fromCols, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one]

/-- **Controllability Hautus lemma.** A finite-dimensional linear system
`(A, B)` over `ℂ` is controllable if and only if for every `μ ∈ ℂ`, the
Hautus block `[μI - A | B]` has full row rank. -/
@[blueprint "thm:isControllable-iff-hautus"
  (statement := /-- A finite-dimensional system $(A, B)$ over $\mathbb{C}$
    is controllable if and only if for every $\mu \in \mathbb{C}$ the Hautus
    matrix $H^{\mathrm{ctrl}}_{A, B}(\mu)$ has full row rank:
    \[
      \mathrm{IsControllable}(A, B)
      \iff
      \forall \mu \in \mathbb{C},\
        \operatorname{rank} H^{\mathrm{ctrl}}_{A, B}(\mu) = n.
    \] -/)
  (proof := /-- Combine the duality bridge
    \cref{thm:isControllable-iff-hautus} \emph{nope, that's the iff itself};
    actually combine \emph{the duality bridge}
    \texttt{isControllable\_iff\_isObservable\_transpose} with the
    observability Hautus iff \cref{thm:isObservable-iff-hautus}, then
    convert the kernel-form RHS to the rank form via the matrix bridge
    \texttt{mulVec\_kernel\_trivial\_iff\_rank\_eq\_card\_cols} from
    `MatrixLemmas`, and finally identify the transposed Hautus matrices. -/)]
theorem isControllable_iff_hautus
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    IsControllable A B
      ↔ ∀ μ : ℂ, Matrix.rank (hautusControllabilityMatrix A B μ) = n := by
  rw [isControllable_iff_isObservable_transpose, isObservable_iff_hautus]
  refine forall_congr' fun μ => ?_
  rw [Matrix.ker_mulVecLin_eq_bot_iff,
      LinearSystems.MatrixLemmas.mulVec_kernel_trivial_iff_rank_eq_card_cols,
      Fintype.card_fin,
      ← hautusControllabilityMatrix_transpose,
      Matrix.rank_transpose]

end LinearSystems
