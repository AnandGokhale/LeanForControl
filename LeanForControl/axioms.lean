import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Basic
import Architect


/-!
# Smoothing of monotone functions

Two `axiom`s and one proved consequence. A Lyapunov function's sublevel data gives only
*monotone* bounds; the comparison-function machinery needs *strictly* monotone continuous ones.
These say the gap can always be closed, in either direction.

Discharging the two axioms is open work: the constructions are standard (piecewise-linear
interpolation, or integrating a positive minorant), but neither is in Mathlib.
-/

/-- A monotonically non-decreasing positive function can be lower-bounded by a strictly monotonic
continuous function. -/
@[blueprint "lem:exists-strictMono-lower-bound"
  (title := "Class $\\mathcal{K}$ minorant of a positive monotone function") (latexEnv := "lemma")
  (statement := /-- \textbf{Assumed without proof.}  Let $r > 0$ and let
    $\psi : \mathbb{R} \to \mathbb{R}$ satisfy $\psi(0) = 0$, $\psi(s) > 0$ for
    $s \in (0, r]$, and $\psi$ nondecreasing on $[0, r]$.  Then there are $b > 0$ and a
    function $f$ with $f(0) = 0$, $f(r) = b$, $f$ continuous and strictly increasing on
    $[0, r]$, and $f(s) \le \psi(s)$ for all $s \in [0, r]$.

    That is: a positive nondecreasing function admits a class $\mathcal{K}$ minorant on any
    bounded interval.  This is what turns a positive-definite $V$ into the lower comparison
    bound of \cref{thm:lyapunov-class-K-bounds}. -/)]
axiom exists_strictMono_lower_bound (r : ℝ) (hr : 0 < r) (ψ : ℝ → ℝ)
    (hψ_zero : ψ 0 = 0)
    (hψ_pos : ∀ s, 0 < s → s ≤ r → 0 < ψ s)
    (hψ_mono : ∀ s₁ s₂, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ r → ψ s₁ ≤ ψ s₂) :
    ∃ (f : ℝ → ℝ) (b : ℝ), 0 < b ∧
      f 0 = 0 ∧ f r = b ∧
      ContinuousOn f (Set.Icc 0 r) ∧
      StrictMonoOn f (Set.Icc 0 r) ∧
      ∀ s, 0 ≤ s → s ≤ r → f s ≤ ψ s


/-- A monotonically non-decreasing function starting at 0 on all of `[0, ∞)` can be
    upper-bounded by a strictly monotonic continuous function that tends to `+∞`. -/
@[blueprint "lem:exists-strictMono-upper-bound-global"
  (title := "Class $\\mathcal{K}_{\\infty}$ majorant of a monotone function") (latexEnv := "lemma")
  (statement := /-- \textbf{Assumed without proof.}  Let $\varphi : \mathbb{R} \to
    \mathbb{R}$ satisfy $\varphi(0) = 0$ and be monotone on $[0, \infty)$.  Then there is an
    $f$ with $f(0) = 0$, continuous and strictly increasing on $[0, \infty)$,
    $f(s) \to \infty$ as $s \to \infty$, and $\varphi(s) \le f(s)$ for all $s \ge 0$.

    That is: a nondecreasing function admits a class $\mathcal{K}_{\infty}$ majorant.  The
    unbounded domain is what distinguishes this from
    \cref{lem:exists-strictMono-upper-bound}, which it implies. -/)]
axiom exists_strictMono_upper_bound_global (φ : ℝ → ℝ)
    (hφ_zero : φ 0 = 0)
    (hφ_mono : MonotoneOn φ (Set.Ici 0)) :
    ∃ f : ℝ → ℝ,
      f 0 = 0 ∧
      ContinuousOn f (Set.Ici 0) ∧
      StrictMonoOn f (Set.Ici 0) ∧
      Filter.Tendsto f Filter.atTop Filter.atTop ∧
      ∀ s ≥ 0, φ s ≤ f s

/-- A monotonically non-decreasing function starting at 0 can be upper-bounded
    by a strictly monotonic continuous function.

Unlike the two axioms above this one is proved, by clamping `φ` beyond `r` and invoking the
global axiom. -/
@[blueprint "lem:exists-strictMono-upper-bound"
  (title := "Class $\\mathcal{K}$ majorant on a bounded interval")
  (latexEnv := "lemma")
  (statement := /-- Let $r > 0$ and let $\varphi$ satisfy $\varphi(0) = 0$ and be monotone on
    $[0, r]$.  Then there are $b > 0$ and an $f$ with $f(0) = 0$, $f(r) = b$, $f$ continuous and
    strictly increasing on $[0, r]$, and $\varphi(s) \le f(s)$ for all $s \in [0, r]$. -/)
  (proof := /-- Clamp $\varphi$ to $\varphi_{\mathrm{ext}}(s) = \varphi(\min(s, r))$, which
    is monotone on all of $[0,\infty)$ and still vanishes at $0$, and apply
    \cref{lem:exists-strictMono-upper-bound-global}.  Restricting the resulting majorant to
    $[0, r]$ gives $f$; $b = f(r) > 0$ because $f$ is strictly increasing from $f(0) = 0$. -/)]
lemma exists_strictMono_upper_bound (r : ℝ) (hr : 0 < r) (φ : ℝ → ℝ)
    (hφ_zero : φ 0 = 0)
    (hφ_mono : MonotoneOn φ (Set.Icc 0 r)) :
    ∃ (f : ℝ → ℝ) (b : ℝ), 0 < b ∧
      f 0 = 0 ∧ f r = b ∧
      ContinuousOn f (Set.Icc 0 r) ∧
      StrictMonoOn f (Set.Icc 0 r) ∧
      ∀ s, 0 ≤ s → s ≤ r → φ s ≤ f s := by
  -- Extend φ to [0, ∞) by clamping: φ_ext s = φ s for s ≤ r, φ r for s > r
  let φ_ext : ℝ → ℝ := fun s => if s ≤ r then φ s else φ r
  have hφ_ext_zero : φ_ext 0 = 0 := by simp [φ_ext, hr.le, hφ_zero]
  have hφ_ext_mono : MonotoneOn φ_ext (Set.Ici 0) := by
    intro s₁ hs₁ s₂ _ h_le
    simp only [φ_ext]
    split_ifs with h1 h2
    · exact hφ_mono ⟨hs₁, h_le.trans h2⟩ ⟨hs₁.trans h_le, h2⟩ h_le   -- both ≤ r
    · exact hφ_mono ⟨hs₁, h1⟩ ⟨hr.le, le_rfl⟩ h1                     -- s₁ ≤ r < s₂
    · linarith [not_le.mp h1]                -- s₁ > r, s₂ ≤ r: impossible
    · exact le_refl _                        -- both > r
  -- Apply the global axiom to φ_ext
  obtain ⟨f, hf_zero, hf_cont, hf_mono, _, hf_bound⟩ :=
    exists_strictMono_upper_bound_global φ_ext hφ_ext_zero hφ_ext_mono
  refine ⟨f, f r, ?_, hf_zero, rfl,
    hf_cont.mono Set.Icc_subset_Ici_self,
    hf_mono.mono Set.Icc_subset_Ici_self,
    fun s hs₁ hs₂ => ?_⟩
  · -- f r > 0: f strictly mono, f 0 = 0, r > 0
    have h := hf_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hr.le) hr
    linarith [hf_zero ▸ h]
  · -- φ s ≤ φ_ext s ≤ f s for s ≤ r
    have h := hf_bound s hs₁
    simp only [φ_ext, if_pos hs₂] at h
    exact h
