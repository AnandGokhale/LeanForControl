import LeanForControl.LinearSystems.Realization.FiniteDetermination
import Mathlib.LinearAlgebra.Isomorphisms
import Architect

/-!
# Finite Ho–Kalman range/shift construction

This file establishes the canonical state-space and induced-shift core of a
finite Ho–Kalman construction.  The state space is the range of the unshifted
finite Hankel map.  Explicit kernel and range compatibility hypotheses make
the one-step shifted Hankel map descend to an endomorphism of that range.

Turning this core into a bundled realization and proving recovery of every
supplied block requires an additional finite shift-consistency theorem across
successive block columns; that work is deliberately kept separate from the
well-definedness result proved here.

Reference: Ho and Kalman, “Effective construction of linear state-variable
models from input/output functions” (1966).
-/

namespace LinearSystems

open Matrix

namespace Realization

variable {𝕜 : Type*} [Field 𝕜]
variable {m p r s : ℕ}

/-- The finite block Hankel matrix built from supplied Markov blocks, with an
explicit shift in the sequence index.

Reference: Ho and Kalman (1966). -/
def shiftedHankel (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s shift : ℕ) :
    Matrix (Fin r × Fin p) (Fin s × Fin m) 𝕜 :=
  Matrix.of fun ia jb => M (shift + (ia.1 : ℕ) + (jb.1 : ℕ)) ia.2 jb.2

/-- Compatibility conditions ensuring that the shifted Hankel map induces a
well-defined endomorphism of the unshifted Hankel range.

The kernel inclusion gives independence from the chosen input-history
representative.  The range inclusion makes the shifted image a state again.

Reference: Ho and Kalman (1966). -/
structure HankelShiftCompatible
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) : Prop where
  /-- Null histories for the unshifted Hankel matrix remain null after one
  shift. -/
  ker_le :
    LinearMap.ker (shiftedHankel M r s 0).mulVecLin ≤
      LinearMap.ker (shiftedHankel M r s 1).mulVecLin
  /-- Every shifted output history belongs to the unshifted Hankel range. -/
  range_le :
    LinearMap.range (shiftedHankel M r s 1).mulVecLin ≤
      LinearMap.range (shiftedHankel M r s 0).mulVecLin

/-- The canonical finite Ho–Kalman state space: the range of the unshifted
Hankel map.

Reference: Ho and Kalman (1966). -/
def hankelStateSpace (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) :=
  LinearMap.range (shiftedHankel M r s 0).mulVecLin

/-- The shifted Hankel map, with codomain restricted to the canonical state
space using range compatibility.

Original: finite Ho–Kalman infrastructure for LeanForControl. -/
def hankelShiftToState (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s) :
    (Fin s × Fin m → 𝕜) →ₗ[𝕜] hankelStateSpace M r s :=
  (shiftedHankel M r s 1).mulVecLin.codRestrict
    (hankelStateSpace M r s) fun u =>
      h.range_le ⟨u, rfl⟩

/-- The shifted Hankel map descends through the quotient by the unshifted
Hankel kernel.

This is the central well-definedness step of the finite Ho–Kalman
construction.

Reference: Ho and Kalman (1966). -/
def hankelShiftQuotientMap (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s) :
    ((Fin s × Fin m → 𝕜) ⧸
        LinearMap.ker (shiftedHankel M r s 0).mulVecLin) →ₗ[𝕜]
      hankelStateSpace M r s :=
  (LinearMap.ker (shiftedHankel M r s 0).mulVecLin).liftQ
    (hankelShiftToState M r s h) (by
      intro u hu
      rw [LinearMap.mem_ker] at hu ⊢
      apply Subtype.ext
      exact LinearMap.mem_ker.mp
        (h.ker_le (LinearMap.mem_ker.mpr hu)))

/-- The canonical state transition on the finite Hankel range.

Reference: Ho and Kalman (1966). -/
noncomputable def hankelStateMap
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s) :
    hankelStateSpace M r s →ₗ[𝕜] hankelStateSpace M r s :=
  (hankelShiftQuotientMap M r s h).comp
    (shiftedHankel M r s 0).mulVecLin.quotKerEquivRange.symm.toLinearMap

/-- On a state represented by an input history, the canonical state map is
exactly one Hankel shift.

Reference: Ho and Kalman (1966). -/
theorem hankelStateMap_apply_image
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (u : Fin s × Fin m → 𝕜) :
    hankelStateMap M r s h
        ⟨(shiftedHankel M r s 0).mulVecLin u, ⟨u, rfl⟩⟩ =
      ⟨(shiftedHankel M r s 1).mulVecLin u, h.range_le ⟨u, rfl⟩⟩ := by
  let y : LinearMap.range (shiftedHankel M r s 0).mulVecLin :=
    ⟨(shiftedHankel M r s 0).mulVecLin u, ⟨u, rfl⟩⟩
  change hankelStateMap M r s h y = _
  rw [hankelStateMap, LinearMap.comp_apply]
  have hrepr :
      (shiftedHankel M r s 0).mulVecLin.quotKerEquivRange.symm.toLinearMap
          y =
        (LinearMap.ker (shiftedHankel M r s 0).mulVecLin).mkQ u :=
    by
      dsimp [y]
      exact
        LinearMap.quotKerEquivRange_symm_apply_image
          (shiftedHankel M r s 0).mulVecLin u ⟨u, rfl⟩
  calc
    (hankelShiftQuotientMap M r s h)
        ((shiftedHankel M r s 0).mulVecLin.quotKerEquivRange.symm.toLinearMap
          y) =
        (hankelShiftQuotientMap M r s h)
          ((LinearMap.ker
            (shiftedHankel M r s 0).mulVecLin).mkQ u) :=
      congrArg (hankelShiftQuotientMap M r s h) hrepr
    _ = _ := rfl

/-! ## Block-column generators and input/output maps -/

/-- Embed an input vector as a history supported in one block column.

Original: finite-history plumbing for LeanForControl. -/
def hankelColumnHistory (s : ℕ) (j : Fin s) :
    (Fin m → 𝕜) →ₗ[𝕜] (Fin s × Fin m → 𝕜) where
  toFun u jb := if jb.1 = j then u jb.2 else 0
  map_add' u v := by
    ext jb
    by_cases hj : jb.1 = j <;> simp [hj]
  map_smul' a u := by
    ext jb
    by_cases hj : jb.1 = j <;> simp [hj]

/-- Multiplying a shifted block Hankel matrix by a single block-column
history extracts the corresponding block column.

Original: block-matrix plumbing for LeanForControl. -/
theorem shiftedHankel_mulVec_hankelColumnHistory
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s shift : ℕ) (j : Fin s) (u : Fin m → 𝕜) :
    (shiftedHankel M r s shift).mulVec
        (hankelColumnHistory s j u) =
      fun ia => (M (shift + (ia.1 : ℕ) + (j : ℕ))).mulVec u ia.2 := by
  ext ia
  change
    (∑ jb : Fin s × Fin m,
      M (shift + (ia.1 : ℕ) + (jb.1 : ℕ)) ia.2 jb.2 *
        (if jb.1 = j then u jb.2 else 0)) =
      ∑ b : Fin m, M (shift + (ia.1 : ℕ) + (j : ℕ)) ia.2 b * u b
  rw [Fintype.sum_prod_type]
  simp

/-- The state represented by one block column of the unshifted Hankel
matrix.

Original: canonical generator for LeanForControl's Ho–Kalman construction. -/
def hankelColumnState
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ)
    (j : Fin s) (u : Fin m → 𝕜) : hankelStateSpace M r s :=
  ⟨(shiftedHankel M r s 0).mulVecLin (hankelColumnHistory s j u),
    ⟨hankelColumnHistory s j u, rfl⟩⟩

/-- The induced Hankel state map sends each available block-column generator
to the next one.

Reference: Ho and Kalman (1966). -/
theorem hankelStateMap_apply_hankelColumnState
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (k : ℕ) (hk : k + 1 < s) (u : Fin m → 𝕜) :
    hankelStateMap M r s h
        (hankelColumnState M r s ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩ u) =
      hankelColumnState M r s ⟨k + 1, hk⟩ u := by
  change
    hankelStateMap M r s h
        ⟨(shiftedHankel M r s 0).mulVecLin
            (hankelColumnHistory s ⟨k, _⟩ u), ⟨_, rfl⟩⟩ = _
  rw [hankelStateMap_apply_image]
  apply Subtype.ext
  change
    (shiftedHankel M r s 1).mulVec
        (hankelColumnHistory s ⟨k, _⟩ u) =
      (shiftedHankel M r s 0).mulVec
        (hankelColumnHistory s ⟨k + 1, hk⟩ u)
  rw [shiftedHankel_mulVec_hankelColumnHistory,
      shiftedHankel_mulVec_hankelColumnHistory]
  ext ia
  dsimp only
  congr 2
  omega

/-- The canonical Ho–Kalman input map: an input is sent to the first block
column of the Hankel range.

Reference: Ho and Kalman (1966). -/
def hankelInputMap
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) (hs : 0 < s) :
    (Fin m → 𝕜) →ₗ[𝕜] hankelStateSpace M r s :=
  ((shiftedHankel M r s 0).mulVecLin.codRestrict
    (hankelStateSpace M r s) fun u => ⟨u, rfl⟩).comp
      (hankelColumnHistory s ⟨0, hs⟩)

/-- The input map is the zeroth block-column generator.

Original: input-generator API for LeanForControl. -/
theorem hankelInputMap_apply
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ)
    (hs : 0 < s) (u : Fin m → 𝕜) :
    hankelInputMap M r s hs u = hankelColumnState M r s ⟨0, hs⟩ u :=
  rfl

/-- Read one output block from a vector in the finite Hankel output-history
space.

Original: output-history projection for LeanForControl. -/
def hankelOutputBlock (r : ℕ) (i : Fin r) :
    (Fin r × Fin p → 𝕜) →ₗ[𝕜] (Fin p → 𝕜) where
  toFun y a := y (i, a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical Ho–Kalman output map reads the first output block of a
Hankel-range state.

Reference: Ho and Kalman (1966). -/
def hankelOutputMap
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) (hr : 0 < r) :
    hankelStateSpace M r s →ₗ[𝕜] (Fin p → 𝕜) :=
  (hankelOutputBlock r ⟨0, hr⟩).comp
    (hankelStateSpace M r s).subtype

/-- The output map applied to a block-column generator is the corresponding
Markov block applied to the input.

Reference: Ho and Kalman (1966). -/
theorem hankelOutputMap_apply_hankelColumnState
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ)
    (hr : 0 < r) (j : Fin s) (u : Fin m → 𝕜) :
    hankelOutputMap M r s hr (hankelColumnState M r s j u) =
      (M j).mulVec u := by
  ext a
  simp [hankelOutputMap, hankelOutputBlock, hankelColumnState,
    shiftedHankel_mulVec_hankelColumnHistory]

/-- Repeated application of the induced state shift sends the input generator
to the corresponding available block-column generator.

Reference: Ho and Kalman (1966). -/
theorem hankelStateMap_pow_apply_hankelInputMap
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (hs : 0 < s) (k : ℕ) (hk : k < s) (u : Fin m → 𝕜) :
    ((hankelStateMap M r s h) ^ k) (hankelInputMap M r s hs u) =
      hankelColumnState M r s ⟨k, hk⟩ u := by
  induction k with
  | zero =>
      simpa only [pow_zero, one_apply] using
        hankelInputMap_apply M r s hs u
  | succ k ih =>
      have hk' : k < s := Nat.lt_trans (Nat.lt_succ_self k) hk
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply, ih hk']
      exact hankelStateMap_apply_hankelColumnState M r s h k hk u

/-- Basis-free finite Ho–Kalman recovery: the abstract input, state, and
output maps reproduce every supplied Markov block whose column generator is
present in the finite Hankel window.

Reference: Ho and Kalman (1966). -/
@[blueprint "thm:finite-ho-kalman-markov-recovery-linear"
  (statement := /-- For every column index $k<s$, the canonical finite
    Hankel range construction satisfies $C_H A_H^k B_H=M_k$ as a linear-map
    identity. -/)]
theorem hankelOutput_statePow_input
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (hr : 0 < r) (hs : 0 < s) (k : ℕ) (hk : k < s)
    (u : Fin m → 𝕜) :
    hankelOutputMap M r s hr
        (((hankelStateMap M r s h) ^ k) (hankelInputMap M r s hs u)) =
      (M k).mulVec u := by
  rw [hankelStateMap_pow_apply_hankelInputMap M r s h hs k hk u,
    hankelOutputMap_apply_hankelColumnState]

/-- Linear-map form of finite Ho–Kalman Markov recovery.

Reference: Ho and Kalman (1966). -/
theorem hankelOutput_comp_statePow_comp_input
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (hr : 0 < r) (hs : 0 < s) (k : ℕ) (hk : k < s) :
    (hankelOutputMap M r s hr).comp
        (((hankelStateMap M r s h) ^ k).comp
          (hankelInputMap M r s hs)) =
      (M k).mulVecLin := by
  apply LinearMap.ext
  intro u
  apply funext
  intro a
  exact congrFun (hankelOutput_statePow_input M r s h hr hs k hk u) a

/-- A finite basis of the canonical Hankel state space.

Original: coordinate infrastructure for LeanForControl. -/
noncomputable def hankelStateBasis
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) :=
  Module.finBasis 𝕜 (hankelStateSpace M r s)

/-- The matrix of the canonical finite Hankel shift in range coordinates.

Reference: Ho and Kalman (1966). -/
noncomputable def hankelStateMatrix
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s) :
    Matrix (Fin (Module.finrank 𝕜 (hankelStateSpace M r s)))
      (Fin (Module.finrank 𝕜 (hankelStateSpace M r s))) 𝕜 :=
  LinearMap.toMatrix (hankelStateBasis M r s) (hankelStateBasis M r s)
    (hankelStateMap M r s h)

/-- The matrix of the canonical finite Hankel input map in range coordinates.

Reference: Ho and Kalman (1966). -/
noncomputable def hankelInputMatrix
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (hs : 0 < s) :
    Matrix (Fin (Module.finrank 𝕜 (hankelStateSpace M r s))) (Fin m) 𝕜 :=
  LinearMap.toMatrix (Pi.basisFun 𝕜 (Fin m)) (hankelStateBasis M r s)
    (hankelInputMap M r s hs)

/-- The matrix of the canonical finite Hankel output map in range coordinates.

Reference: Ho and Kalman (1966). -/
noncomputable def hankelOutputMatrix
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (hr : 0 < r) :
    Matrix (Fin p) (Fin (Module.finrank 𝕜 (hankelStateSpace M r s))) 𝕜 :=
  LinearMap.toMatrix (hankelStateBasis M r s) (Pi.basisFun 𝕜 (Fin p))
    (hankelOutputMap M r s hr)

/-- The finite Ho–Kalman realization in coordinates of the canonical Hankel
range basis.  The feedthrough matrix is supplied separately from the
state-mediated Markov blocks.

Reference: Ho and Kalman (1966). -/
noncomputable def hoKalmanRealization
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (D : Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (hr : 0 < r) (hs : 0 < s) :
    Realization 𝕜 (Module.finrank 𝕜 (hankelStateSpace M r s)) m p where
  A := hankelStateMatrix M r s h
  B := hankelInputMatrix M r s hs
  C := hankelOutputMatrix M r s hr
  D := D

/-- The coordinate state matrix acts exactly as the abstract induced Hankel
state map.

Original: coordinate infrastructure for LeanForControl. -/
theorem hankelStateMatrix_mulVec_coordinates
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (x : hankelStateSpace M r s) :
    hankelStateMatrix M r s h *ᵥ (hankelStateBasis M r s).equivFun x =
      (hankelStateBasis M r s).equivFun (hankelStateMap M r s h x) := by
  simpa [hankelStateMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (hankelStateBasis M r s)
      (hankelStateBasis M r s) (hankelStateMap M r s h) x

/-- The coordinate input matrix acts exactly as the abstract first-column
input map.

Original: coordinate infrastructure for LeanForControl. -/
theorem hankelInputMatrix_mulVec_coordinates
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (hs : 0 < s) (u : Fin m → 𝕜) :
    hankelInputMatrix M r s hs *ᵥ u =
      (hankelStateBasis M r s).equivFun (hankelInputMap M r s hs u) := by
  simpa [hankelInputMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (Pi.basisFun 𝕜 (Fin m))
      (hankelStateBasis M r s) (hankelInputMap M r s hs) u

/-- The coordinate output matrix acts exactly as the abstract first-row
output map.

Original: coordinate infrastructure for LeanForControl. -/
theorem hankelOutputMatrix_mulVec_coordinates
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (hr : 0 < r) (x : hankelStateSpace M r s) :
    hankelOutputMatrix M r s hr *ᵥ (hankelStateBasis M r s).equivFun x =
      hankelOutputMap M r s hr x := by
  simpa [hankelOutputMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (hankelStateBasis M r s)
      (Pi.basisFun 𝕜 (Fin p)) (hankelOutputMap M r s hr) x

/-- Powers of the coordinate state matrix act as powers of the abstract
induced Hankel state map.

Original: coordinate infrastructure for LeanForControl. -/
theorem hankelStateMatrix_pow_mulVec_coordinates
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s) (k : ℕ)
    (x : hankelStateSpace M r s) :
    (hankelStateMatrix M r s h ^ k) *ᵥ
        (hankelStateBasis M r s).equivFun x =
      (hankelStateBasis M r s).equivFun
        (((hankelStateMap M r s h) ^ k) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih,
        hankelStateMatrix_mulVec_coordinates, pow_succ', Module.End.mul_apply]

/-- The bundled finite Ho–Kalman realization recovers every supplied Markov
block in its valid column window.

Reference: Ho and Kalman (1966). -/
@[blueprint "thm:finite-ho-kalman-markov-recovery"
  (statement := /-- The finite Ho--Kalman realization satisfies
    $C_HA_H^kB_H=M_k$ for every $k<s$. -/)]
theorem hoKalmanRealization_markovParameter_eq
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (D : Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (hr : 0 < r) (hs : 0 < s) (k : ℕ) (hk : k < s) :
    (hoKalmanRealization M D r s h hr hs).markovParameter k = M k := by
  rw [Matrix.ext_iff_mulVec]
  intro u
  change
    (hankelOutputMatrix M r s hr * hankelStateMatrix M r s h ^ k *
        hankelInputMatrix M r s hs) *ᵥ u = M k *ᵥ u
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hankelInputMatrix_mulVec_coordinates,
    hankelStateMatrix_pow_mulVec_coordinates,
    hankelOutputMatrix_mulVec_coordinates]
  exact hankelOutput_statePow_input M r s h hr hs k hk u

/-- The dimension of the canonical finite Ho–Kalman state space is the rank
of the unshifted Hankel matrix.

Reference: Ho and Kalman (1966). -/
theorem hankelStateSpace_finrank_eq_rank
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) :
    Module.finrank 𝕜 (hankelStateSpace M r s) =
      Matrix.rank (shiftedHankel M r s 0) :=
  rfl

/-- The bundled finite Ho–Kalman realization has state dimension equal to
the rank of the unshifted finite Hankel matrix.

Reference: Ho and Kalman (1966). -/
theorem hoKalmanRealization_stateDim_eq_rank
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) :
    Module.finrank 𝕜 (hankelStateSpace M r s) =
      Matrix.rank (shiftedHankel M r s 0) :=
  hankelStateSpace_finrank_eq_rank M r s

/-! ## Synthesis from the Markov data of an existing realization -/

/-- The unshifted generic Hankel matrix specialized to a realization's
Markov sequence is its finite Hankel matrix.

Original: compatibility bridge for LeanForControl. -/
theorem shiftedHankel_markovParameter_zero_eq_hankelMatrix
    {n : ℕ} (R : Realization 𝕜 n m p) (r s : ℕ) :
    shiftedHankel R.markovParameter r s 0 = R.hankelMatrix r s := by
  ext ia jb
  simp [shiftedHankel, hankelMatrix]

/-- A finite controllability-horizon matrix acts by summing its block-column
responses.

Original: finite-horizon matrix plumbing for LeanForControl. -/
theorem controllabilityHorizon_mulVec_eq_sum
    {n : ℕ} (R : Realization 𝕜 n m p) (s : ℕ)
    (u : Fin s × Fin m → 𝕜) :
    R.controllabilityHorizon s *ᵥ u =
      ∑ k : Fin s, (R.A ^ (k : ℕ) * R.B) *ᵥ fun j => u (k, j) := by
  funext i
  rw [Finset.sum_apply]
  change
    (∑ kj : Fin s × Fin m,
      R.controllabilityHorizon s i kj * u kj) =
      ∑ k : Fin s,
        ((R.A ^ (k : ℕ) * R.B) *ᵥ fun j => u (k, j)) i
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [controllabilityHorizon, Matrix.mulVec, dotProduct,
    Matrix.of_apply]

/-- Every controllability horizon at least as long as the state dimension is
surjective for a controllable realization.

Original: horizon-extension infrastructure for LeanForControl. -/
theorem controllabilityHorizon_mulVec_surjective_of_isControllable
    {n : ℕ} (R : Realization 𝕜 n m p) (hctrl : R.IsControllable)
    {s : ℕ} (hns : n ≤ s) (x : Fin n → 𝕜) :
    ∃ u : Fin s × Fin m → 𝕜, R.controllabilityHorizon s *ᵥ u = x := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hns
  obtain ⟨u, hu⟩ := hctrl x
  refine
    ⟨fun kj =>
      Fin.addCases (fun k => u k kj.2) (fun _ => 0) kj.1, ?_⟩
  rw [controllabilityHorizon_mulVec_eq_sum, Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Fin.val_castAdd]
  have hzero :
      (∑ k : Fin t,
        (R.A ^ (Fin.natAdd n k : ℕ) * R.B) *ᵥ fun _ => 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    ext i
    simp [Matrix.mulVec]
  rw [hzero, add_zero]
  exact hu.symm

/-- The one-step shifted Hankel matrix of a realization factors as
`O_r A C_s`.

Reference: Ho and Kalman (1966). -/
theorem shiftedHankel_markovParameter_one_eq_factorization
    {n : ℕ} (R : Realization 𝕜 n m p) (r s : ℕ) :
    shiftedHankel R.markovParameter r s 1 =
      R.observabilityHorizon r * R.A * R.controllabilityHorizon s := by
  ext ia jb
  change
    (R.C * R.A ^ (1 + (ia.1 : ℕ) + (jb.1 : ℕ)) * R.B) ia.2 jb.2 =
      ((R.C * R.A ^ (ia.1 : ℕ)) * R.A *
        (R.A ^ (jb.1 : ℕ) * R.B)) ia.2 jb.2
  have hpow : 1 + (ia.1 : ℕ) + (jb.1 : ℕ) =
      (ia.1 : ℕ) + 1 + (jb.1 : ℕ) := by omega
  rw [hpow, pow_add, pow_add, pow_one]
  simp only [Matrix.mul_assoc]

/-- Controllability and observability make the consecutive finite Hankel
pair shift-compatible once the column horizon reaches the state dimension.

Reference: Ho and Kalman (1966). -/
theorem hankelShiftCompatible_markovParameter_of_isControllable_of_isObservable
    {n : ℕ} (R : Realization 𝕜 n m p)
    (hctrl : R.IsControllable) (hobs : R.IsObservable)
    (s : ℕ) (hns : n ≤ s) :
    HankelShiftCompatible R.markovParameter n s where
  ker_le := by
    intro u hu
    rw [LinearMap.mem_ker] at hu ⊢
    change (shiftedHankel R.markovParameter n s 0).mulVec u = 0 at hu
    change (shiftedHankel R.markovParameter n s 1).mulVec u = 0
    rw [shiftedHankel_markovParameter_zero_eq_hankelMatrix,
      R.hankelMatrix_eq_observability_mul_controllability] at hu
    rw [shiftedHankel_markovParameter_one_eq_factorization]
    rw [← Matrix.mulVec_mulVec] at hu
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hx : R.controllabilityHorizon s *ᵥ u = 0 := by
      apply
        (isObservable_iff_observabilityMatrix_ker_trivial R.A R.C).mp hobs
      rw [← R.observabilityHorizon_stateDim]
      exact hu
    rw [hx, Matrix.mulVec_zero, Matrix.mulVec_zero]
  range_le := by
    rintro y ⟨u, rfl⟩
    let x := R.A *ᵥ (R.controllabilityHorizon s *ᵥ u)
    obtain ⟨v, hv⟩ :=
      controllabilityHorizon_mulVec_surjective_of_isControllable
        R hctrl hns x
    refine ⟨v, ?_⟩
    change
      (shiftedHankel R.markovParameter n s 0).mulVec v =
        (shiftedHankel R.markovParameter n s 1).mulVec u
    rw [shiftedHankel_markovParameter_zero_eq_hankelMatrix,
      R.hankelMatrix_eq_observability_mul_controllability,
      shiftedHankel_markovParameter_one_eq_factorization]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    exact congrArg (R.observabilityHorizon n).mulVec hv

/-- An explicit finite-window criterion under which the Ho–Kalman
realization built from an existing realization's Markov blocks has the same
complete behavior.

The synthesized state dimension is `rank H₀`; hence finite determination
requires exactly `n + rank H₀` recovered blocks.  The hypothesis states that
this entire window lies among the `s` available block columns.

Reference: Ho and Kalman (1966); Kailath, *Linear Systems*. -/
@[blueprint "thm:finite-ho-kalman-behavioral-equivalence"
  (statement := /-- If $s\ge n+\operatorname{rank}H_0$, then the compatible
    finite Ho--Kalman realization constructed from an $n$-state realization's
    Markov data is behaviorally equivalent to the original realization. -/)]
theorem behaviorallyEquivalent_hoKalmanRealization
    {n : ℕ} (R : Realization 𝕜 n m p) (r s : ℕ)
    (h : HankelShiftCompatible R.markovParameter r s)
    (hr : 0 < r) (hs : 0 < s)
    (hwindow : n + Matrix.rank (shiftedHankel R.markovParameter r s 0) ≤ s) :
    R.BehaviorallyEquivalent
      (hoKalmanRealization R.markovParameter R.D r s h hr hs) := by
  apply behaviorallyEquivalent_of_markovParameter_eq_lt_add
  · rfl
  · intro k hk
    have hks : k < s := by
      rw [hankelStateSpace_finrank_eq_rank] at hk
      exact hk.trans_le hwindow
    exact
      (hoKalmanRealization_markovParameter_eq
        R.markovParameter R.D r s h hr hs k hks).symm

/-- A convenient realization-dimension-only sufficient window: `2*n` block
columns always contains the exact finite-determination window because every
finite Hankel rank is at most `n`.

Reference: Ho and Kalman (1966); Kailath, *Linear Systems*. -/
theorem behaviorallyEquivalent_hoKalmanRealization_of_two_mul_le
    {n : ℕ} (R : Realization 𝕜 n m p) (r s : ℕ)
    (h : HankelShiftCompatible R.markovParameter r s)
    (hr : 0 < r) (hs : 0 < s) (hwindow : n + n ≤ s) :
    R.BehaviorallyEquivalent
      (hoKalmanRealization R.markovParameter R.D r s h hr hs) := by
  apply behaviorallyEquivalent_hoKalmanRealization R r s h hr hs
  have hrank : Matrix.rank (shiftedHankel R.markovParameter r s 0) ≤ n := by
    rw [shiftedHankel_markovParameter_zero_eq_hankelMatrix]
    exact R.hankelMatrix_rank_le_stateDim r s
  omega

section Complex

variable {n : ℕ}

/-- The automatic consecutive-Hankel compatibility proof used by the
canonical positive-dimensional synthesis of a minimal realization.

Reference: Ho and Kalman (1966). -/
def minimalHoKalmanShiftCompatible
    (R : Realization ℂ n m p) (hmin : R.IsMinimal) :
    HankelShiftCompatible R.markovParameter n (n + n) :=
  let hco := (isMinimal_iff_isControllable_and_isObservable R).mp hmin
  hankelShiftCompatible_markovParameter_of_isControllable_of_isObservable
    R hco.1 hco.2 (n + n) (Nat.le_add_right n n)

/-- The canonical finite Ho–Kalman synthesis of a positive-dimensional
minimal realization, using row horizon `n` and the explicit
finite-determination column horizon `2*n`.

Reference: Ho and Kalman (1966). -/
noncomputable def minimalHoKalmanRealization
    (R : Realization ℂ n m p) (hmin : R.IsMinimal) (hn : 0 < n) :
    Realization ℂ
      (Module.finrank ℂ (hankelStateSpace R.markovParameter n (n + n))) m p :=
  hoKalmanRealization R.markovParameter R.D n (n + n)
    (minimalHoKalmanShiftCompatible R hmin) hn (by omega)

/-- The exact `n + rank H₀` recovery window of the canonical minimal
construction fits inside its `2*n` supplied block columns.

Original: finite-window arithmetic for LeanForControl. -/
theorem minimalHoKalman_window
    (R : Realization ℂ n m p) :
    n + Matrix.rank
        (shiftedHankel R.markovParameter n (n + n) 0) ≤ n + n := by
  have hrank :
      Matrix.rank (shiftedHankel R.markovParameter n (n + n) 0) ≤ n := by
    rw [shiftedHankel_markovParameter_zero_eq_hankelMatrix]
    exact R.hankelMatrix_rank_le_stateDim n (n + n)
  omega

/-- The canonical `n`-by-`2*n` finite Ho–Kalman construction preserves the
complete behavior of a positive-dimensional minimal realization.

Reference: Ho and Kalman (1966); Kailath, *Linear Systems*. -/
theorem behaviorallyEquivalent_minimalHoKalmanRealization
    (R : Realization ℂ n m p) (hmin : R.IsMinimal) (hn : 0 < n) :
    R.BehaviorallyEquivalent (minimalHoKalmanRealization R hmin hn) := by
  apply behaviorallyEquivalent_hoKalmanRealization
  exact minimalHoKalman_window R

/-- A compatible Ho–Kalman realization built from a minimal complex
realization is minimal whenever its recovery window is long enough for finite
determination.

Reference: Ho and Kalman (1966); Kailath, *Linear Systems*. -/
theorem hoKalmanRealization_isMinimal_of_isMinimal
    (R : Realization ℂ n m p) (hmin : R.IsMinimal) (r s : ℕ)
    (h : HankelShiftCompatible R.markovParameter r s)
    (hr : 0 < r) (hs : 0 < s)
    (hwindow : n + Matrix.rank (shiftedHankel R.markovParameter r s 0) ≤ s) :
    (hoKalmanRealization R.markovParameter R.D r s h hr hs).IsMinimal := by
  let S := hoKalmanRealization R.markovParameter R.D r s h hr hs
  have hbehavior : R.BehaviorallyEquivalent S :=
    behaviorallyEquivalent_hoKalmanRealization R r s h hr hs hwindow
  have hdim_le : Module.finrank ℂ (hankelStateSpace R.markovParameter r s) ≤ n := by
    rw [hankelStateSpace_finrank_eq_rank,
      shiftedHankel_markovParameter_zero_eq_hankelMatrix]
    exact R.hankelMatrix_rank_le_stateDim r s
  intro n' T hST
  exact hdim_le.trans (hmin n' T (hbehavior.trans hST))

/-- The canonical `n`-by-`2*n` synthesis of a positive-dimensional minimal
realization is minimal.

Reference: Ho and Kalman (1966); Kailath, *Linear Systems*. -/
theorem minimalHoKalmanRealization_isMinimal
    (R : Realization ℂ n m p) (hmin : R.IsMinimal) (hn : 0 < n) :
    (minimalHoKalmanRealization R hmin hn).IsMinimal := by
  apply hoKalmanRealization_isMinimal_of_isMinimal R hmin
  exact minimalHoKalman_window R

/-- Under the same explicit finite window, the synthesized Ho–Kalman
realization is controllable and observable.

Reference: Ho and Kalman (1966); Kailath, *Linear Systems*. -/
theorem hoKalmanRealization_isControllable_and_isObservable_of_isMinimal
    (R : Realization ℂ n m p) (hmin : R.IsMinimal) (r s : ℕ)
    (h : HankelShiftCompatible R.markovParameter r s)
    (hr : 0 < r) (hs : 0 < s)
    (hwindow : n + Matrix.rank (shiftedHankel R.markovParameter r s 0) ≤ s) :
    (hoKalmanRealization R.markovParameter R.D r s h hr hs).IsControllable ∧
      (hoKalmanRealization R.markovParameter R.D r s h hr hs).IsObservable :=
  (isMinimal_iff_isControllable_and_isObservable _).mp
    (hoKalmanRealization_isMinimal_of_isMinimal
      R hmin r s h hr hs hwindow)

/-- The canonical `n`-by-`2*n` synthesis is controllable and observable.

Reference: Ho and Kalman (1966); Kailath, *Linear Systems*. -/
theorem minimalHoKalmanRealization_isControllable_and_isObservable
    (R : Realization ℂ n m p) (hmin : R.IsMinimal) (hn : 0 < n) :
    (minimalHoKalmanRealization R hmin hn).IsControllable ∧
      (minimalHoKalmanRealization R hmin hn).IsObservable :=
  (isMinimal_iff_isControllable_and_isObservable _).mp
    (minimalHoKalmanRealization_isMinimal R hmin hn)

/-- For data generated by a minimal realization, the synthesized state
dimension equals the original minimal dimension and the finite Hankel rank.

Reference: Ho and Kalman (1966); Kailath, *Linear Systems*. -/
theorem hoKalmanRealization_stateDim_eq_of_isMinimal
    (R : Realization ℂ n m p) (hmin : R.IsMinimal) (r s : ℕ)
    (h : HankelShiftCompatible R.markovParameter r s)
    (hr : 0 < r) (hs : 0 < s)
    (hwindow : n + Matrix.rank (shiftedHankel R.markovParameter r s 0) ≤ s) :
    Module.finrank ℂ (hankelStateSpace R.markovParameter r s) = n := by
  let S := hoKalmanRealization R.markovParameter R.D r s h hr hs
  have hbehavior : R.BehaviorallyEquivalent S :=
    behaviorallyEquivalent_hoKalmanRealization R r s h hr hs hwindow
  apply Nat.le_antisymm
  · rw [hankelStateSpace_finrank_eq_rank,
      shiftedHankel_markovParameter_zero_eq_hankelMatrix]
    exact R.hankelMatrix_rank_le_stateDim r s
  · exact hmin _ S hbehavior

/-- The canonical positive-dimensional synthesis has exactly the original
minimal state dimension.

Reference: Ho and Kalman (1966); Kailath, *Linear Systems*. -/
theorem minimalHoKalmanRealization_stateDim_eq
    (R : Realization ℂ n m p) (hmin : R.IsMinimal) (hn : 0 < n) :
    Module.finrank ℂ
        (hankelStateSpace R.markovParameter n (n + n)) = n := by
  exact
    hoKalmanRealization_stateDim_eq_of_isMinimal R hmin n (n + n)
      (minimalHoKalmanShiftCompatible R hmin) hn (by omega)
      (minimalHoKalman_window R)

/-- **Main finite Ho–Kalman synthesis theorem.**  The canonical finite
construction from a positive-dimensional minimal realization uses only the
blocks occurring in `H₀` and `H₁` at horizons `n` and `2*n`; it preserves the
complete behavior, is controllable and observable, is minimal, and has state
dimension equal both to `n` and to the finite Hankel rank.

Reference: Ho and Kalman (1966); Kailath, *Linear Systems*. -/
@[blueprint "thm:finite-ho-kalman-synthesis"
  (statement := /-- For a positive-dimensional minimal $n$-state
    realization, the finite Ho--Kalman construction at horizons
    $(r,s)=(n,2n)$ is behaviorally equivalent, controllable, observable, and
    minimal, with state dimension $n=\operatorname{rank}H_0$. -/)]
theorem minimalHoKalmanRealization_spec
    (R : Realization ℂ n m p) (hmin : R.IsMinimal) (hn : 0 < n) :
    R.BehaviorallyEquivalent (minimalHoKalmanRealization R hmin hn) ∧
      (minimalHoKalmanRealization R hmin hn).IsControllable ∧
      (minimalHoKalmanRealization R hmin hn).IsObservable ∧
      (minimalHoKalmanRealization R hmin hn).IsMinimal ∧
      Module.finrank ℂ
          (hankelStateSpace R.markovParameter n (n + n)) = n ∧
      Module.finrank ℂ
          (hankelStateSpace R.markovParameter n (n + n)) =
        Matrix.rank
          (shiftedHankel R.markovParameter n (n + n) 0) := by
  refine
    ⟨behaviorallyEquivalent_minimalHoKalmanRealization R hmin hn,
      (minimalHoKalmanRealization_isControllable_and_isObservable
        R hmin hn).1,
      (minimalHoKalmanRealization_isControllable_and_isObservable
        R hmin hn).2,
      minimalHoKalmanRealization_isMinimal R hmin hn,
      minimalHoKalmanRealization_stateDim_eq R hmin hn,
      hankelStateSpace_finrank_eq_rank R.markovParameter n (n + n)⟩

/-- Two compatible finite Ho–Kalman constructions from the same minimal
behavior, possibly using different horizons and hence different coordinate
types, are similar after transport along their canonical dimension equality.

Reference: Ho and Kalman (1966); Kailath, *Linear Systems*. -/
theorem exists_stateDim_eq_and_similar_hoKalmanRealizations
    (R : Realization ℂ n m p) (hmin : R.IsMinimal)
    (r₁ s₁ r₂ s₂ : ℕ)
    (h₁ : HankelShiftCompatible R.markovParameter r₁ s₁)
    (h₂ : HankelShiftCompatible R.markovParameter r₂ s₂)
    (hr₁ : 0 < r₁) (hs₁ : 0 < s₁) (hr₂ : 0 < r₂) (hs₂ : 0 < s₂)
    (hw₁ : n + Matrix.rank (shiftedHankel R.markovParameter r₁ s₁ 0) ≤ s₁)
    (hw₂ : n + Matrix.rank (shiftedHankel R.markovParameter r₂ s₂ 0) ≤ s₂) :
    ∃ e : Module.finrank ℂ (hankelStateSpace R.markovParameter r₁ s₁) =
        Module.finrank ℂ (hankelStateSpace R.markovParameter r₂ s₂),
      Nonempty
        (Similar
          (e ▸ hoKalmanRealization R.markovParameter R.D r₁ s₁ h₁ hr₁ hs₁)
          (hoKalmanRealization R.markovParameter R.D r₂ s₂ h₂ hr₂ hs₂)) := by
  let S₁ := hoKalmanRealization R.markovParameter R.D r₁ s₁ h₁ hr₁ hs₁
  let S₂ := hoKalmanRealization R.markovParameter R.D r₂ s₂ h₂ hr₂ hs₂
  have hb₁ : R.BehaviorallyEquivalent S₁ :=
    behaviorallyEquivalent_hoKalmanRealization R r₁ s₁ h₁ hr₁ hs₁ hw₁
  have hb₂ : R.BehaviorallyEquivalent S₂ :=
    behaviorallyEquivalent_hoKalmanRealization R r₂ s₂ h₂ hr₂ hs₂ hw₂
  have hm₁ : S₁.IsMinimal :=
    hoKalmanRealization_isMinimal_of_isMinimal R hmin r₁ s₁ h₁ hr₁ hs₁ hw₁
  have hm₂ : S₂.IsMinimal :=
    hoKalmanRealization_isMinimal_of_isMinimal R hmin r₂ s₂ h₂ hr₂ hs₂ hw₂
  exact
    exists_stateDim_eq_and_similar_of_isMinimal_of_behaviorallyEquivalent
      S₁ S₂ hm₁ hm₂ (hb₁.symm.trans hb₂)

end Complex

end Realization

end LinearSystems
