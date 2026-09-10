import LeanForControl.LinearSystems.DefsKalmanDecomposition
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.ModularLattice
import Architect

/-!
# The finite-dimensional Kalman decomposition

For a complex finite-dimensional state-space system `(A, B, C)`, this file
constructs four coordinate sectors in the order

1. controllable-unobservable (`cuo`),
2. controllable-observable (`co`),
3. uncontrollable-unobservable (`uuo`),
4. uncontrollable-observable (`uo`).

The first and third summands make up the unobservable subspace; the first and
second make up the reachable subspace.  This ordering gives the state matrix
zero pattern

```text
[ *  *  *  * ]
[ 0  *  0  * ]
[ 0  0  *  * ]
[ 0  0  0  * ]
```

The sectors are adapted to the reachable and unobservable subspaces. The
chosen complements, and hence the adapted basis, are noncanonical and are not
individually claimed to be invariant under the state matrix. Only the forced
zero blocks displayed above are proved; starred blocks are unrestricted. The
formalization is over `ℂ`, has no feedthrough matrix `D`, and does not claim a
numerical decomposition algorithm.

Reference: Kailath, *Linear Systems*.
-/

namespace LinearSystems

open Matrix

variable {n m p : ℕ}

section RelativeDirectSum

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Addition identifies two disjoint subspaces whose supremum is `r` with
the subtype of `r`.  This is the relative version of
`Submodule.prodEquivOfIsCompl`. -/
private noncomputable def prodEquivOfDisjointSupEq
    {q₁ q₂ r : Submodule 𝕜 V} (hdisj : Disjoint q₁ q₂) (hsup : q₁ ⊔ q₂ = r) :
    (q₁ × q₂) ≃ₗ[𝕜] r := by
  let f₀ : q₁ × q₂ →ₗ[𝕜] V := q₁.subtype.coprod q₂.subtype
  let f : q₁ × q₂ →ₗ[𝕜] r := f₀.codRestrict r fun x => by
    rw [← hsup]
    exact Submodule.add_mem_sup x.1.2 x.2.2
  apply LinearEquiv.ofBijective f
  constructor
  · have hf₀ : Function.Injective f₀ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range,
        q₁.ker_subtype, q₂.ker_subtype, Submodule.prod_bot]
      rw [Submodule.range_subtype, Submodule.range_subtype]
      exact hdisj
    intro x y hxy
    apply hf₀
    exact Subtype.ext_iff.mp hxy
  · intro z
    have hz : (z : V) ∈ q₁ ⊔ q₂ := by
      rw [hsup]
      exact z.2
    obtain ⟨x, y, hxy⟩ := Submodule.mem_sup'.mp hz
    refine ⟨(x, y), Subtype.ext ?_⟩
    exact hxy

@[simp]
private lemma prodEquivOfDisjointSupEq_apply
    {q₁ q₂ r : Submodule 𝕜 V} (hdisj : Disjoint q₁ q₂) (hsup : q₁ ⊔ q₂ = r)
    (x : q₁ × q₂) :
    (prodEquivOfDisjointSupEq hdisj hsup x : V) = x.1 + x.2 :=
  rfl

end RelativeDirectSum

/-- The four Kalman coordinate sectors always exist over `ℂ`. Only vector-space
complements are used; no semisimplicity or spectral hypothesis is assumed.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "thm:kalman-subspaces-exist"
  (statement := /-- Every finite-dimensional complex state-space system has
    four coordinate sectors adapted to its reachable and unobservable
    subspaces. The complements are noncanonical vector-space complements and
    are not individually asserted to be invariant under $A$. -/)]
theorem exists_kalmanDecomposition
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    Nonempty (KalmanDecomposition A B C) := by
  let R := reachableSubspace A B
  let N := unobservableSubspace A C
  let I := R ⊓ N
  obtain ⟨co, hIco, hIcoSup⟩ :=
    IsModularLattice.exists_disjoint_and_sup_eq (a := I) (b := R) inf_le_left
  obtain ⟨uuo, hIuuo, hIuuoSup⟩ :=
    IsModularLattice.exists_disjoint_and_sup_eq (a := I) (b := N) inf_le_right
  obtain ⟨uo, huo⟩ := Submodule.exists_isCompl (R ⊔ N)
  have huuoleN : uuo ≤ N := by
    rw [← hIuuoSup]
    exact le_sup_right
  have hRuuo : Disjoint R uuo := by
    rw [disjoint_iff_inf_le]
    intro x hx
    have hxI : x ∈ I := ⟨hx.1, huuoleN hx.2⟩
    have hxbot : x ∈ I ⊓ uuo := ⟨hxI, hx.2⟩
    rw [hIuuo.eq_bot] at hxbot
    exact hxbot
  have hRuuoSup : R ⊔ uuo = R ⊔ N := by
    rw [← hIuuoSup]
    calc
      R ⊔ uuo = (R ⊔ I) ⊔ uuo := by
        rw [show R ⊔ I = R from sup_eq_left.mpr inf_le_left]
      _ = R ⊔ (I ⊔ uuo) := by rw [sup_assoc]
  exact ⟨{
    cuo := I
    co := co
    uuo := uuo
    uo := uo
    cuo_eq := rfl
    disjoint_cuo_co := hIco
    cuo_sup_co := hIcoSup
    disjoint_reachable_uuo := hRuuo
    reachable_sup_uuo := hRuuoSup
    uuo_le_unobservable := huuoleN
    cuo_sup_uuo := hIuuoSup
    isCompl_uo := huo
  }⟩

namespace KalmanDecomposition

variable {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin m) ℂ}
  {C : Matrix (Fin p) (Fin n) ℂ}

/-- The nested product of the four component spaces, in the documented order
`cuo, co, uuo, uo`.

Original: formalization infrastructure for LeanForControl. -/
abbrev Coordinates (d : KalmanDecomposition A B C) :=
  (((d.cuo × d.co) × d.uuo) × d.uo)

/-- The adapted linear equivalence from four-component coordinates to the
original state space.

Original: formalization infrastructure for LeanForControl. -/
@[blueprint "def:kalman-adapted-equivalence"
  (statement := /-- Addition of the four Kalman coordinate sectors defines a linear
    equivalence
    $X_{c\bar o}\times X_{co}\times X_{\bar c\bar o}\times X_{\bar c o}
      \simeq \mathbb{C}^{n}$.
    Choosing sector bases therefore gives an adapted basis of the original
    state space. -/)]
noncomputable def linearEquiv (d : KalmanDecomposition A B C) :
    d.Coordinates ≃ₗ[ℂ] (Fin n → ℂ) := by
  let eR : (d.cuo × d.co) ≃ₗ[ℂ] reachableSubspace A B :=
    prodEquivOfDisjointSupEq d.disjoint_cuo_co d.cuo_sup_co
  let eRN : (reachableSubspace A B × d.uuo) ≃ₗ[ℂ]
      ↥(reachableSubspace A B ⊔ unobservableSubspace A C) :=
    prodEquivOfDisjointSupEq d.disjoint_reachable_uuo d.reachable_sup_uuo
  exact
    (((eR.prodCongr (LinearEquiv.refl ℂ d.uuo)).trans eRN).prodCongr
      (LinearEquiv.refl ℂ d.uo)).trans
      (Submodule.prodEquivOfIsCompl _ _ d.isCompl_uo)

/-- The adapted equivalence reconstructs a state by adding its four sector
components.

Original: formalization infrastructure for LeanForControl. -/
@[simp]
theorem linearEquiv_apply (d : KalmanDecomposition A B C) (x : d.Coordinates) :
    d.linearEquiv x = ((x.1.1.1 : Fin n → ℂ) + x.1.1.2) + x.1.2 + x.2 := by
  rfl

/-- In adapted coordinates, a vector is reachable exactly when its two
uncontrollable coordinates vanish.

Reference: Kailath, *Linear Systems*. -/
theorem linearEquiv_mem_reachable_iff
    (d : KalmanDecomposition A B C) (x : d.Coordinates) :
    d.linearEquiv x ∈ reachableSubspace A B ↔ x.1.2 = 0 ∧ x.2 = 0 := by
  constructor
  · intro hx
    have hx' : d.linearEquiv x ∈ d.cuo ⊔ d.co := by
      rw [d.cuo_sup_co]
      exact hx
    obtain ⟨xcuo, xco, hsum⟩ := Submodule.mem_sup'.mp hx'
    let y : d.Coordinates := (((xcuo, xco), 0), 0)
    have hxy : x = y := by
      apply d.linearEquiv.injective
      rw [linearEquiv_apply, linearEquiv_apply]
      simp [y, hsum]
    constructor
    · exact congrArg (fun z : d.Coordinates => z.1.2) hxy
    · exact congrArg (fun z : d.Coordinates => z.2) hxy
  · rintro ⟨huuo, huo⟩
    rw [linearEquiv_apply, huuo, huo]
    rw [← d.cuo_sup_co]
    simpa using Submodule.add_mem_sup x.1.1.1.2 x.1.1.2.2

/-- In adapted coordinates, a vector is unobservable exactly when its two
observable coordinates vanish.

Reference: Kailath, *Linear Systems*. -/
theorem linearEquiv_mem_unobservable_iff
    (d : KalmanDecomposition A B C) (x : d.Coordinates) :
    d.linearEquiv x ∈ unobservableSubspace A C ↔ x.1.1.2 = 0 ∧ x.2 = 0 := by
  constructor
  · intro hx
    have hx' : d.linearEquiv x ∈ d.cuo ⊔ d.uuo := by
      rw [d.cuo_sup_uuo]
      exact hx
    obtain ⟨xcuo, xuuo, hsum⟩ := Submodule.mem_sup'.mp hx'
    let y : d.Coordinates := (((xcuo, 0), xuuo), 0)
    have hxy : x = y := by
      apply d.linearEquiv.injective
      rw [linearEquiv_apply, linearEquiv_apply]
      simp [y, hsum]
    constructor
    · exact congrArg (fun z : d.Coordinates => z.1.1.2) hxy
    · exact congrArg (fun z : d.Coordinates => z.2) hxy
  · rintro ⟨hco, huo⟩
    rw [linearEquiv_apply, hco, huo]
    rw [← d.cuo_sup_uuo]
    simpa using Submodule.add_mem_sup x.1.1.1.2 x.1.2.2

/-- The state endomorphism transported to the four adapted components.

Original: formalization infrastructure for LeanForControl. -/
noncomputable def stateMap (d : KalmanDecomposition A B C) :
    Module.End ℂ d.Coordinates :=
  d.linearEquiv.symm.toLinearMap.comp
    (A.mulVecLin.comp d.linearEquiv.toLinearMap)

/-- The input map transported to the four adapted components.

Original: formalization infrastructure for LeanForControl. -/
noncomputable def inputMap (d : KalmanDecomposition A B C) :
    (Fin m → ℂ) →ₗ[ℂ] d.Coordinates :=
  d.linearEquiv.symm.toLinearMap.comp B.mulVecLin

/-- The output map expressed on the four adapted components.

Original: formalization infrastructure for LeanForControl. -/
noncomputable def outputMap (d : KalmanDecomposition A B C) :
    d.Coordinates →ₗ[ℂ] (Fin p → ℂ) :=
  C.mulVecLin.comp d.linearEquiv.toLinearMap

/-- Transporting `stateMap` back to the state space recovers multiplication by
`A`.

Original: formalization infrastructure for LeanForControl. -/
theorem linearEquiv_stateMap_apply (d : KalmanDecomposition A B C)
    (x : d.Coordinates) :
    d.linearEquiv (d.stateMap x) = A *ᵥ d.linearEquiv x := by
  simp [stateMap]

/-- Transporting `inputMap` back to the state space recovers multiplication by
`B`.

Original: formalization infrastructure for LeanForControl. -/
theorem linearEquiv_inputMap_apply (d : KalmanDecomposition A B C)
    (u : Fin m → ℂ) :
    d.linearEquiv (d.inputMap u) = B *ᵥ u := by
  simp [inputMap]

/-- Evaluating the transported output map is multiplication by `C` after the
adapted equivalence.

Original: formalization infrastructure for LeanForControl. -/
@[simp]
theorem outputMap_apply (d : KalmanDecomposition A B C) (x : d.Coordinates) :
    d.outputMap x = C *ᵥ d.linearEquiv x := by
  rfl

/-- Reading the zeroth finite-horizon condition shows that `C` kills every
unobservable state, including the zero-dimensional edge case.

Original: this bridges the finite-horizon definition to the output map. -/
theorem C_mulVec_eq_zero_of_mem_unobservableSubspace
    (v : Fin n → ℂ) (hv : v ∈ unobservableSubspace A C) :
    C *ᵥ v = 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have h0 := (mem_unobservableSubspace_iff v).mp hv (⟨0, hnpos⟩ : Fin n)
    simpa using h0

/-- A vector in the controllable-unobservable component stays in that
component under `A`.

Reference: Kailath, *Linear Systems*. -/
theorem stateMap_cuo_zero_pattern (d : KalmanDecomposition A B C) (x : d.cuo) :
    let z := d.stateMap (((x, 0), 0), 0)
    z.1.1.2 = 0 ∧ z.1.2 = 0 ∧ z.2 = 0 := by
  dsimp
  have hxRN : (x : Fin n → ℂ) ∈ reachableSubspace A B := by
    have hxI : (x : Fin n → ℂ) ∈
        reachableSubspace A B ⊓ unobservableSubspace A C := by
      rw [← d.cuo_eq]
      exact x.2
    exact hxI.1
  have hxNN : (x : Fin n → ℂ) ∈ unobservableSubspace A C := by
    have hxI : (x : Fin n → ℂ) ∈
        reachableSubspace A B ⊓ unobservableSubspace A C := by
      rw [← d.cuo_eq]
      exact x.2
    exact hxI.2
  have hR : d.linearEquiv (d.stateMap (((x, 0), 0), 0)) ∈
      reachableSubspace A B := by
    rw [linearEquiv_stateMap_apply, linearEquiv_apply]
    simpa using reachableSubspace_invariant A B hxRN
  have hN : d.linearEquiv (d.stateMap (((x, 0), 0), 0)) ∈
      unobservableSubspace A C := by
    rw [linearEquiv_stateMap_apply, linearEquiv_apply]
    simpa using A_mulVec_mem_unobservableSubspace_of_mem hxNN
  have hrz := (d.linearEquiv_mem_reachable_iff _).mp hR
  have hnz := (d.linearEquiv_mem_unobservable_iff _).mp hN
  exact ⟨hnz.1, hrz.1, hrz.2⟩

/-- A vector in the controllable-observable component can acquire only
reachable coordinates under `A`.

Reference: Kailath, *Linear Systems*. -/
theorem stateMap_co_zero_pattern (d : KalmanDecomposition A B C) (x : d.co) :
    let z := d.stateMap (((0, x), 0), 0)
    z.1.2 = 0 ∧ z.2 = 0 := by
  dsimp
  have hxR : (x : Fin n → ℂ) ∈ reachableSubspace A B := by
    rw [← d.cuo_sup_co]
    exact Submodule.mem_sup_right x.2
  apply (d.linearEquiv_mem_reachable_iff _).mp
  rw [linearEquiv_stateMap_apply, linearEquiv_apply]
  simpa using reachableSubspace_invariant A B hxR

/-- A vector in the uncontrollable-unobservable component can acquire only
unobservable coordinates under `A`.

Reference: Kailath, *Linear Systems*. -/
theorem stateMap_uuo_zero_pattern (d : KalmanDecomposition A B C) (x : d.uuo) :
    let z := d.stateMap (((0, 0), x), 0)
    z.1.1.2 = 0 ∧ z.2 = 0 := by
  dsimp
  apply (d.linearEquiv_mem_unobservable_iff _).mp
  rw [linearEquiv_stateMap_apply, linearEquiv_apply]
  simpa using
    A_mulVec_mem_unobservableSubspace_of_mem (d.uuo_le_unobservable x.2)

/-- The last two component rows of the adapted input map vanish.

Reference: Kailath, *Linear Systems*. -/
theorem inputMap_zero_pattern (d : KalmanDecomposition A B C) (u : Fin m → ℂ) :
    (d.inputMap u).1.2 = 0 ∧ (d.inputMap u).2 = 0 := by
  apply (d.linearEquiv_mem_reachable_iff _).mp
  rw [linearEquiv_inputMap_apply]
  exact range_B_le_reachableSubspace A B ⟨u, rfl⟩

/-- The output map vanishes on the controllable-unobservable component.

Reference: Kailath, *Linear Systems*. -/
theorem outputMap_cuo_eq_zero (d : KalmanDecomposition A B C) (x : d.cuo) :
    d.outputMap (((x, 0), 0), 0) = 0 := by
  rw [outputMap_apply, linearEquiv_apply]
  refine C_mulVec_eq_zero_of_mem_unobservableSubspace (A := A) (C := C) _ ?_
  have hxI : (x : Fin n → ℂ) ∈
      reachableSubspace A B ⊓ unobservableSubspace A C := by
    rw [← d.cuo_eq]
    exact x.2
  simpa using hxI.2

/-- The output map vanishes on the uncontrollable-unobservable component.

Reference: Kailath, *Linear Systems*. -/
theorem outputMap_uuo_eq_zero (d : KalmanDecomposition A B C) (x : d.uuo) :
    d.outputMap (((0, 0), x), 0) = 0 := by
  rw [outputMap_apply, linearEquiv_apply]
  simpa using
    C_mulVec_eq_zero_of_mem_unobservableSubspace x (d.uuo_le_unobservable x.2)

section Matrices

open Module

variable {ιcuo ιco ιuuo ιuo : Type*}

/-- The product basis on the four component-coordinate space.

Original: formalization infrastructure for LeanForControl. -/
noncomputable def coordinateBasis (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo) :
    Basis (((ιcuo ⊕ ιco) ⊕ ιuuo) ⊕ ιuo) ℂ d.Coordinates :=
  ((bcuo.prod bco).prod buuo).prod buo

/-- The basis of the original state space obtained from bases of the four
Kalman components.

Original: formalization infrastructure for LeanForControl. -/
noncomputable def adaptedBasis (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo) :
    Basis (((ιcuo ⊕ ιco) ⊕ ιuuo) ⊕ ιuo) ℂ (Fin n → ℂ) :=
  (d.coordinateBasis bcuo bco buuo buo).map d.linearEquiv

@[simp]
private theorem coordinateBasis_apply_cuo (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo) (i : ιcuo) :
    d.coordinateBasis bcuo bco buuo buo (Sum.inl (Sum.inl (Sum.inl i))) =
      (((bcuo i, 0), 0), 0) := by
  simp [coordinateBasis]

@[simp]
private theorem coordinateBasis_apply_co (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo) (i : ιco) :
    d.coordinateBasis bcuo bco buuo buo (Sum.inl (Sum.inl (Sum.inr i))) =
      (((0, bco i), 0), 0) := by
  simp [coordinateBasis]

@[simp]
private theorem coordinateBasis_apply_uuo (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo) (i : ιuuo) :
    d.coordinateBasis bcuo bco buuo buo (Sum.inl (Sum.inr i)) =
      (((0, 0), buuo i), 0) := by
  ext <;> simp [coordinateBasis]

@[simp]
private theorem coordinateBasis_apply_uo (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo) (i : ιuo) :
    d.coordinateBasis bcuo bco buuo buo (Sum.inr i) =
      (((0, 0), 0), buo i) := by
  ext <;> simp [coordinateBasis]

@[simp]
private theorem coordinateBasis_repr_cuo (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (x : d.Coordinates) (i : ιcuo) :
    (d.coordinateBasis bcuo bco buuo buo).repr x
        (Sum.inl (Sum.inl (Sum.inl i))) = bcuo.repr x.1.1.1 i := by
  simp [coordinateBasis]

@[simp]
private theorem coordinateBasis_repr_co (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (x : d.Coordinates) (i : ιco) :
    (d.coordinateBasis bcuo bco buuo buo).repr x
        (Sum.inl (Sum.inl (Sum.inr i))) = bco.repr x.1.1.2 i := by
  simp [coordinateBasis]

@[simp]
private theorem coordinateBasis_repr_uuo (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (x : d.Coordinates) (i : ιuuo) :
    (d.coordinateBasis bcuo bco buuo buo).repr x
        (Sum.inl (Sum.inr i)) = buuo.repr x.1.2 i := by
  simp [coordinateBasis]

@[simp]
private theorem coordinateBasis_repr_uo (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (x : d.Coordinates) (i : ιuo) :
    (d.coordinateBasis bcuo bco buuo buo).repr x (Sum.inr i) =
      buo.repr x.2 i := by
  simp [coordinateBasis]

variable [Fintype ιcuo] [DecidableEq ιcuo]
  [Fintype ιco] [DecidableEq ιco]
  [Fintype ιuuo] [DecidableEq ιuuo]
  [Fintype ιuo] [DecidableEq ιuo]

/-- The state matrix in the four-component product basis.

Original: formalization infrastructure for LeanForControl. -/
noncomputable def stateMatrix (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo) :
    Matrix (((ιcuo ⊕ ιco) ⊕ ιuuo) ⊕ ιuo)
      (((ιcuo ⊕ ιco) ⊕ ιuuo) ⊕ ιuo) ℂ :=
  LinearMap.toMatrix (d.coordinateBasis bcuo bco buuo buo)
    (d.coordinateBasis bcuo bco buuo buo) d.stateMap

/-- The input matrix in the adapted state basis and the standard input
basis.

Original: formalization infrastructure for LeanForControl. -/
noncomputable def inputMatrix (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo) :
    Matrix (((ιcuo ⊕ ιco) ⊕ ιuuo) ⊕ ιuo) (Fin m) ℂ :=
  LinearMap.toMatrix (Pi.basisFun ℂ (Fin m))
    (d.coordinateBasis bcuo bco buuo buo) d.inputMap

/-- The output matrix in the standard output basis and the adapted state
basis.

Original: formalization infrastructure for LeanForControl. -/
noncomputable def outputMatrix (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo) :
    Matrix (Fin p) (((ιcuo ⊕ ιco) ⊕ ιuuo) ⊕ ιuo) ℂ :=
  LinearMap.toMatrix (d.coordinateBasis bcuo bco buuo buo)
    (Pi.basisFun ℂ (Fin p)) d.outputMap

/-- The coordinate definition of the state matrix is exactly the matrix of
`A` in the corresponding adapted basis of the original state space.

Original: formalization infrastructure for LeanForControl. -/
theorem stateMatrix_eq_toMatrix_adapted (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo) :
    d.stateMatrix bcuo bco buuo buo =
      LinearMap.toMatrix (d.adaptedBasis bcuo bco buuo buo)
        (d.adaptedBasis bcuo bco buuo buo) A.mulVecLin := by
  rfl

omit [DecidableEq ιcuo] [DecidableEq ιco] [DecidableEq ιuuo]
  [DecidableEq ιuo] in
/-- The coordinate definition of the input matrix is exactly the matrix of
`B` from the standard input basis to the adapted state basis.

Original: formalization infrastructure for LeanForControl. -/
theorem inputMatrix_eq_toMatrix_adapted (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo) :
    d.inputMatrix bcuo bco buuo buo =
      LinearMap.toMatrix (Pi.basisFun ℂ (Fin m))
        (d.adaptedBasis bcuo bco buuo buo) B.mulVecLin := by
  rfl

/-- The coordinate definition of the output matrix is exactly the matrix of
`C` from the adapted state basis to the standard output basis.

Original: formalization infrastructure for LeanForControl. -/
theorem outputMatrix_eq_toMatrix_adapted (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo) :
    d.outputMatrix bcuo bco buuo buo =
      LinearMap.toMatrix (d.adaptedBasis bcuo bco buuo buo)
        (Pi.basisFun ℂ (Fin p)) C.mulVecLin := by
  rfl

/-- The `co, cuo` block of the adapted state matrix is zero.

Reference: Kailath, *Linear Systems*. -/
theorem stateMatrix_co_cuo_eq_zero (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (i : ιco) (j : ιcuo) :
    d.stateMatrix bcuo bco buuo buo
        (Sum.inl (Sum.inl (Sum.inr i)))
        (Sum.inl (Sum.inl (Sum.inl j))) = 0 := by
  rw [stateMatrix, LinearMap.toMatrix_apply, coordinateBasis_apply_cuo,
    coordinateBasis_repr_co]
  simpa using congrArg (fun x : d.co => bco.repr x i)
    (d.stateMap_cuo_zero_pattern (bcuo j)).1

/-- The `uuo, cuo` block of the adapted state matrix is zero.

Reference: Kailath, *Linear Systems*. -/
theorem stateMatrix_uuo_cuo_eq_zero (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (i : ιuuo) (j : ιcuo) :
    d.stateMatrix bcuo bco buuo buo (Sum.inl (Sum.inr i))
        (Sum.inl (Sum.inl (Sum.inl j))) = 0 := by
  rw [stateMatrix, LinearMap.toMatrix_apply, coordinateBasis_apply_cuo,
    coordinateBasis_repr_uuo]
  simpa using congrArg (fun x : d.uuo => buuo.repr x i)
    (d.stateMap_cuo_zero_pattern (bcuo j)).2.1

/-- The `uo, cuo` block of the adapted state matrix is zero.

Reference: Kailath, *Linear Systems*. -/
theorem stateMatrix_uo_cuo_eq_zero (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (i : ιuo) (j : ιcuo) :
    d.stateMatrix bcuo bco buuo buo (Sum.inr i)
        (Sum.inl (Sum.inl (Sum.inl j))) = 0 := by
  rw [stateMatrix, LinearMap.toMatrix_apply, coordinateBasis_apply_cuo,
    coordinateBasis_repr_uo]
  simpa using congrArg (fun x : d.uo => buo.repr x i)
    (d.stateMap_cuo_zero_pattern (bcuo j)).2.2

/-- The `uuo, co` block of the adapted state matrix is zero.

Reference: Kailath, *Linear Systems*. -/
theorem stateMatrix_uuo_co_eq_zero (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (i : ιuuo) (j : ιco) :
    d.stateMatrix bcuo bco buuo buo (Sum.inl (Sum.inr i))
        (Sum.inl (Sum.inl (Sum.inr j))) = 0 := by
  rw [stateMatrix, LinearMap.toMatrix_apply, coordinateBasis_apply_co,
    coordinateBasis_repr_uuo]
  simpa using congrArg (fun x : d.uuo => buuo.repr x i)
    (d.stateMap_co_zero_pattern (bco j)).1

/-- The `uo, co` block of the adapted state matrix is zero.

Reference: Kailath, *Linear Systems*. -/
theorem stateMatrix_uo_co_eq_zero (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (i : ιuo) (j : ιco) :
    d.stateMatrix bcuo bco buuo buo (Sum.inr i)
        (Sum.inl (Sum.inl (Sum.inr j))) = 0 := by
  rw [stateMatrix, LinearMap.toMatrix_apply, coordinateBasis_apply_co,
    coordinateBasis_repr_uo]
  simpa using congrArg (fun x : d.uo => buo.repr x i)
    (d.stateMap_co_zero_pattern (bco j)).2

/-- The `co, uuo` block of the adapted state matrix is zero.

Reference: Kailath, *Linear Systems*. -/
theorem stateMatrix_co_uuo_eq_zero (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (i : ιco) (j : ιuuo) :
    d.stateMatrix bcuo bco buuo buo
        (Sum.inl (Sum.inl (Sum.inr i))) (Sum.inl (Sum.inr j)) = 0 := by
  rw [stateMatrix, LinearMap.toMatrix_apply, coordinateBasis_apply_uuo,
    coordinateBasis_repr_co]
  simpa using congrArg (fun x : d.co => bco.repr x i)
    (d.stateMap_uuo_zero_pattern (buuo j)).1

/-- The `uo, uuo` block of the adapted state matrix is zero.

Reference: Kailath, *Linear Systems*. -/
theorem stateMatrix_uo_uuo_eq_zero (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (i : ιuo) (j : ιuuo) :
    d.stateMatrix bcuo bco buuo buo (Sum.inr i)
        (Sum.inl (Sum.inr j)) = 0 := by
  rw [stateMatrix, LinearMap.toMatrix_apply, coordinateBasis_apply_uuo,
    coordinateBasis_repr_uo]
  simpa using congrArg (fun x : d.uo => buo.repr x i)
    (d.stateMap_uuo_zero_pattern (buuo j)).2

omit [DecidableEq ιcuo] [DecidableEq ιco] [DecidableEq ιuuo]
  [DecidableEq ιuo] in
/-- The `uuo` row block of the adapted input matrix is zero.

Reference: Kailath, *Linear Systems*. -/
theorem inputMatrix_uuo_eq_zero (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (i : ιuuo) (j : Fin m) :
    d.inputMatrix bcuo bco buuo buo (Sum.inl (Sum.inr i)) j = 0 := by
  rw [inputMatrix, LinearMap.toMatrix_apply, coordinateBasis_repr_uuo]
  simpa using congrArg (fun x : d.uuo => buuo.repr x i)
    (d.inputMap_zero_pattern ((Pi.basisFun ℂ (Fin m)) j)).1

omit [DecidableEq ιcuo] [DecidableEq ιco] [DecidableEq ιuuo]
  [DecidableEq ιuo] in
/-- The `uo` row block of the adapted input matrix is zero.

Reference: Kailath, *Linear Systems*. -/
theorem inputMatrix_uo_eq_zero (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (i : ιuo) (j : Fin m) :
    d.inputMatrix bcuo bco buuo buo (Sum.inr i) j = 0 := by
  rw [inputMatrix, LinearMap.toMatrix_apply, coordinateBasis_repr_uo]
  simpa using congrArg (fun x : d.uo => buo.repr x i)
    (d.inputMap_zero_pattern ((Pi.basisFun ℂ (Fin m)) j)).2

/-- The `cuo` column block of the adapted output matrix is zero.

Reference: Kailath, *Linear Systems*. -/
theorem outputMatrix_cuo_eq_zero (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (i : Fin p) (j : ιcuo) :
    d.outputMatrix bcuo bco buuo buo i
        (Sum.inl (Sum.inl (Sum.inl j))) = 0 := by
  rw [outputMatrix, LinearMap.toMatrix_apply, coordinateBasis_apply_cuo,
    Pi.basisFun_repr]
  simpa using congrFun (d.outputMap_cuo_eq_zero (bcuo j)) i

/-- The `uuo` column block of the adapted output matrix is zero.

Reference: Kailath, *Linear Systems*. -/
theorem outputMatrix_uuo_eq_zero (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo)
    (i : Fin p) (j : ιuuo) :
    d.outputMatrix bcuo bco buuo buo i (Sum.inl (Sum.inr j)) = 0 := by
  rw [outputMatrix, LinearMap.toMatrix_apply, coordinateBasis_apply_uuo,
    Pi.basisFun_repr]
  simpa using congrFun (d.outputMap_uuo_eq_zero (buuo j)) i

/-- The complete forced-zero pattern of the classical Kalman block form in
the component order `cuo, co, uuo, uo`:

`A = [* * * *; 0 * 0 *; 0 0 * *; 0 0 0 *]`,
`B = [*; *; 0; 0]`, and `C = [0 * 0 *]`.

Entries denoted by `*` are intentionally unconstrained. The named summands are
coordinate sectors; the chosen complements are not individually asserted to
be invariant under `A`.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "thm:kalman-block-matrix-zero-pattern"
  (statement := /-- In a basis adapted to the four Kalman coordinate sectors, ordered
    as controllable-unobservable, controllable-observable,
    uncontrollable-unobservable, uncontrollable-observable, the system has
    the forced-zero pattern
    \[
      A' = \begin{bmatrix} *&*&*&*\\0&*&0&*\\0&0&*&*\\0&0&0&*\end{bmatrix},
      \qquad B'=\begin{bmatrix}*\\*\\0\\0\end{bmatrix},
      \qquad C'=\begin{bmatrix}0&*&0&*\end{bmatrix}.
    \]
    Every displayed zero is asserted entrywise; starred blocks are
    unconstrained. The chosen complement sectors are not individually
    asserted to be invariant under $A$. -/)
  (proof := /-- Reachable-subspace invariance forces the lower-left state and
    input zeros, unobservable-subspace invariance forces the remaining state
    zeros, and the zeroth observability condition forces the output zeros.
    Coordinate-basis representation lemmas translate these component
    statements to individual matrix entries. -/)]
theorem kalman_block_matrix_zero_pattern (d : KalmanDecomposition A B C)
    (bcuo : Basis ιcuo ℂ d.cuo) (bco : Basis ιco ℂ d.co)
    (buuo : Basis ιuuo ℂ d.uuo) (buo : Basis ιuo ℂ d.uo) :
    (∀ i j, d.stateMatrix bcuo bco buuo buo
        (Sum.inl (Sum.inl (Sum.inr i)))
        (Sum.inl (Sum.inl (Sum.inl j))) = 0) ∧
    (∀ i j, d.stateMatrix bcuo bco buuo buo (Sum.inl (Sum.inr i))
        (Sum.inl (Sum.inl (Sum.inl j))) = 0) ∧
    (∀ i j, d.stateMatrix bcuo bco buuo buo (Sum.inr i)
        (Sum.inl (Sum.inl (Sum.inl j))) = 0) ∧
    (∀ i j, d.stateMatrix bcuo bco buuo buo (Sum.inl (Sum.inr i))
        (Sum.inl (Sum.inl (Sum.inr j))) = 0) ∧
    (∀ i j, d.stateMatrix bcuo bco buuo buo (Sum.inr i)
        (Sum.inl (Sum.inl (Sum.inr j))) = 0) ∧
    (∀ i j, d.stateMatrix bcuo bco buuo buo
        (Sum.inl (Sum.inl (Sum.inr i))) (Sum.inl (Sum.inr j)) = 0) ∧
    (∀ i j, d.stateMatrix bcuo bco buuo buo (Sum.inr i)
        (Sum.inl (Sum.inr j)) = 0) ∧
    (∀ i j, d.inputMatrix bcuo bco buuo buo (Sum.inl (Sum.inr i)) j = 0) ∧
    (∀ i j, d.inputMatrix bcuo bco buuo buo (Sum.inr i) j = 0) ∧
    (∀ i j, d.outputMatrix bcuo bco buuo buo i
        (Sum.inl (Sum.inl (Sum.inl j))) = 0) ∧
    (∀ i j, d.outputMatrix bcuo bco buuo buo i (Sum.inl (Sum.inr j)) = 0) := by
  exact ⟨d.stateMatrix_co_cuo_eq_zero bcuo bco buuo buo,
    d.stateMatrix_uuo_cuo_eq_zero bcuo bco buuo buo,
    d.stateMatrix_uo_cuo_eq_zero bcuo bco buuo buo,
    d.stateMatrix_uuo_co_eq_zero bcuo bco buuo buo,
    d.stateMatrix_uo_co_eq_zero bcuo bco buuo buo,
    d.stateMatrix_co_uuo_eq_zero bcuo bco buuo buo,
    d.stateMatrix_uo_uuo_eq_zero bcuo bco buuo buo,
    d.inputMatrix_uuo_eq_zero bcuo bco buuo buo,
    d.inputMatrix_uo_eq_zero bcuo bco buuo buo,
    d.outputMatrix_cuo_eq_zero bcuo bco buuo buo,
    d.outputMatrix_uuo_eq_zero bcuo bco buuo buo⟩

end Matrices

end KalmanDecomposition

end LinearSystems
