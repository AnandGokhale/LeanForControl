import LeanForControl.LinearSystems.Controllability.Defs
import LeanForControl.LinearSystems.Observability.Defs
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.ModularLattice
import Architect

/-!
# Definitions for the Kalman decomposition

Every `def`, `noncomputable def`, `abbrev`, and `structure` for the `KalmanDecomposition`
directory lives here, apart from the theorems proved about them (`Decomposition.lean`), per
the project convention: definitions live apart from theorems.

* `KalmanDecomposition` — the four coordinate sectors and their lattice relationships.
* `prodEquivOfDisjointSupEq` — the relative-direct-sum equivalence used to build
  `linearEquiv`; private construction machinery for that one definition, not a standalone
  result, so it lives alongside what it builds rather than in the theorem file.
* `Coordinates`, `linearEquiv` — the four-component coordinate space and its adapted
  equivalence with the original state space.
* `stateMap`, `inputMap`, `outputMap` — the system maps transported to adapted coordinates.
* `coordinateBasis`, `adaptedBasis` — bases on the coordinate space and the transported
  basis on the original state space.
* `stateMatrix`, `inputMatrix`, `outputMatrix` — the system matrices in those bases.
-/

namespace LinearSystems

variable {n m p : ℕ}

/-- A noncanonical choice of four coordinate sectors adapted to the reachable
and unobservable subspaces.

The fields record the exact lattice relationships used later; in particular,
`cuo ⊔ co` is reachable, `cuo ⊔ uuo` is unobservable, and the four spaces
together form the whole state space. No chosen complement is asserted to be
individually invariant under the state matrix.

References: Hespanha, *Linear Systems Theory*; Kailath, *Linear Systems*.

Original: this structure packages the data for the LeanForControl API. -/
@[blueprint "def:kalman-decomposition"
  (statement := /-- A Kalman decomposition of $(A,B,C)$ records four
    coordinate sectors adapted to the reachable and unobservable subspaces.
    Their direct sums recover those subspaces and the full state space. The
    chosen complements are noncanonical and are not individually asserted to
    be invariant under $A$. -/)]
structure KalmanDecomposition
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) where
  /-- The controllable-unobservable sector. -/
  cuo : Submodule ℂ (Fin n → ℂ)
  /-- A complement of `cuo` inside the reachable subspace. -/
  co : Submodule ℂ (Fin n → ℂ)
  /-- A complement of `cuo` inside the unobservable subspace. -/
  uuo : Submodule ℂ (Fin n → ℂ)
  /-- A complement of the sum of the reachable and unobservable subspaces. -/
  uo : Submodule ℂ (Fin n → ℂ)
  /-- The `cuo` sector is the intersection of the reachable and unobservable
  subspaces. -/
  cuo_eq : cuo = reachableSubspace A B ⊓ unobservableSubspace A C
  /-- The `cuo` and `co` sectors are disjoint. -/
  disjoint_cuo_co : Disjoint cuo co
  /-- The `cuo` and `co` sectors span the reachable subspace. -/
  cuo_sup_co : cuo ⊔ co = reachableSubspace A B
  /-- The reachable subspace and the `uuo` sector are disjoint. -/
  disjoint_reachable_uuo : Disjoint (reachableSubspace A B) uuo
  /-- Adding `uuo` to the reachable subspace gives the sum of the reachable
  and unobservable subspaces. -/
  reachable_sup_uuo : reachableSubspace A B ⊔ uuo =
    reachableSubspace A B ⊔ unobservableSubspace A C
  /-- The `uuo` sector lies in the unobservable subspace. -/
  uuo_le_unobservable : uuo ≤ unobservableSubspace A C
  /-- The `cuo` and `uuo` sectors span the unobservable subspace. -/
  cuo_sup_uuo : cuo ⊔ uuo = unobservableSubspace A C
  /-- The `uo` sector complements the sum of the reachable and unobservable
  subspaces. -/
  isCompl_uo : IsCompl
    (reachableSubspace A B ⊔ unobservableSubspace A C) uo

section RelativeDirectSum

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Addition identifies two disjoint subspaces whose supremum is `r` with
the subtype of `r`.  This is the relative version of
`Submodule.prodEquivOfIsCompl`.

Private construction machinery for `linearEquiv`, not a standalone result. -/
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

end Matrices

end KalmanDecomposition

end LinearSystems
