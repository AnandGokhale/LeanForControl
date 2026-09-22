import LeanForControl.LinearSystems.Basic
import Mathlib.Analysis.Complex.Basic
import Architect

/-!
# Entrywise complexification of a real matrix

Reference: standard continuous-time linear systems terminology.
-/

namespace LinearSystems

/-- The entrywise complexification of a real matrix. -/
noncomputable def complexification {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A.map (algebraMap ℝ ℂ)

end LinearSystems
