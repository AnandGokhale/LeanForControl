import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Order.Interval.Set.UnorderedInterval
import LeanForControl.ODEs.gronwall_bellman

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Real Interval





-- Let E be our Banach space (e.g., ℝⁿ)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- A single, generalized definition for an integral solution to an ODE
def IsIntegralSolution (t₀ t₁ : ℝ) (x : ℝ → E) (x₀ : E) (F : ℝ → E → E) : Prop :=
  ∀ t ∈ Set.Icc t₀ t₁, x t = x₀ + ∫ s in t₀..t, F s (x s)



variable {t₀ t₁ : ℝ}
variable {f g : ℝ → E → E}
variable {y z : ℝ → E}
variable {y₀ z₀ : E}
variable {L μ : ℝ}

omit [NormedSpace ℝ E] in lemma
IntervalIntegrable_of_lipschitz {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
{f : ℝ → E → E} {z : ℝ → E}
(hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))  -- f jointly continuous
  (hz : ContinuousOn z (Icc t₀ t₁)) :
  (IntervalIntegrable (fun s => f s (z s)) volume t₀ t₁)  := by
  rw [← Set.uIcc_of_le hle] at hz
  exact (hf_cont.comp_continuousOn
    (ContinuousOn.prodMk continuous_id.continuousOn hz)).intervalIntegrable


/-
  Theorem 3.4: Continuous dependence on initial states and parameters.
  Note: We simplify the domain W ⊂ ℝⁿ to the whole space E for clarity,
  assuming global Lipschitz and boundedness on the interval to avoid
  excessive local extension boilerplate.
-/
theorem continuous_dependence_ODE
    (ht : t₀ ≤ t₁)
    (hL : 0 < L)
    (hμ : 0 < μ)
    (hy : IsIntegralSolution t₀ t₁ y y₀ f)
    (hz : IsIntegralSolution t₀ t₁ z z₀ (fun s x => f s x + g s x))
    (hy_cont : ContinuousOn y (Set.Icc t₀ t₁))
    (hz_cont : ContinuousOn z (Set.Icc t₀ t₁))
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))  -- f jointly continuous
    (hgz     : IntervalIntegrable (fun s => g s (z s)) volume t₀ t₁) -- g integrable
    (hLip    : ∀ t ∈ Set.Icc t₀ t₁, LipschitzWith ⟨L, hL.le⟩ (f t))
    (hg      : ∀ t ∈ Set.Icc t₀ t₁, ∀ x : E, ‖g t x‖ ≤ μ) : -- g is bounded by μ
    ∀ t ∈ Set.Icc t₀ t₁,
      ‖y t - z t‖ ≤
        ‖y₀ - z₀‖ * Real.exp (L * (t - t₀)) +
        (μ / L) * (Real.exp (L * (t - t₀)) - 1) := by
  -- ── Continuity and integrability of ‖y - z‖ ──────────────────────────
  have hyz_cont : ContinuousOn (fun s => ‖y s - z s‖) (Icc t₀ t₁) :=
    (hy_cont.sub hz_cont).norm
  have hyz_int : IntervalIntegrable (fun s => ‖y s - z s‖) volume t₀ t₁ :=
    hyz_cont.intervalIntegrable_of_Icc ht
  have hfy :
    IntervalIntegrable (fun s => f s (y s)) volume t₀ t₁ :=
       IntervalIntegrable_of_lipschitz (t₀ := t₀) (t₁ := t₁)
      ht hf_cont hy_cont
  have hfz :
    IntervalIntegrable (fun s => f s (z s)) volume t₀ t₁ :=
       IntervalIntegrable_of_lipschitz (t₀ := t₀) (t₁ := t₁)
      ht hf_cont hz_cont
  have cont_fy : ContinuousOn (fun s => f s (y s)) (Set.Icc t₀ t₁) := by
    have h₂ : ContinuousOn (fun s : ℝ => (s, y s)) (Set.Icc t₀ t₁) := by
      exact ContinuousOn.prodMk continuousOn_id hy_cont
    exact hf_cont.comp_continuousOn h₂
  have cont_fz : ContinuousOn (fun s => f s (z s)) (Set.Icc t₀ t₁) := by
    have h₂ : ContinuousOn (fun s : ℝ => (s, z s)) (Set.Icc t₀ t₁) := by
      exact ContinuousOn.prodMk continuousOn_id hz_cont
    exact hf_cont.comp_continuousOn h₂
  have hfyz : IntervalIntegrable (fun s => ‖f s (y s) - f s (z s)‖) volume t₀ t₁ := by
      apply ContinuousOn.intervalIntegrable_of_Icc ht
      exact ((cont_fy).sub (cont_fz)).norm
-- ── Step 1: basic norm inequality for every τ ─────────────────────────
  -- ‖y τ - z τ‖ ≤ ‖y₀ - z₀‖ + μ*(τ - t₀) + L * ∫_{t₀}^{τ} ‖y s - z s‖
  have hineq_base : ∀ τ ∈ Icc t₀ t₁,
      ‖y τ - z τ‖ ≤ ‖y₀ - z₀‖ + μ * (τ - t₀) +
                    L * ∫ s in t₀..τ, ‖y s - z s‖ := by
    intro τ hτ
    have hτ0 : t₀ ≤ τ := hτ.1
    have hmem := Set.mem_Icc.mp hτ
    have hτ_uIcc : τ ∈ [[t₀, t₁]] := Set.Icc_subset_uIcc hτ
    -- solution formulas
    have hy_τ : y τ = y₀ + ∫ s in t₀..τ, f s (y s) := hy τ hτ
    have hz_τ : z τ = z₀ + ∫ s in t₀..τ, (f s (z s) + g s (z s)) := hz τ hτ
    have sub_set : Set.uIcc t₀ τ ⊆ Set.uIcc t₀ t₁ := by
      rw [Set.uIcc_of_le hτ0, Set.uIcc_of_le ht]
      exact Set.Icc_subset_Icc_right hτ.2
    have hfy_τ : IntervalIntegrable (fun s => f s (y s)) volume t₀ τ := by
      exact hfy.mono_set (Set.uIcc_subset_uIcc_left hτ_uIcc)
    have hfz_τ : IntervalIntegrable (fun s => f s (z s)) volume t₀ τ := by
      exact hfz.mono_set (Set.uIcc_subset_uIcc_left hτ_uIcc)
    have hgz_τ : IntervalIntegrable (fun s => g s (z s)) volume t₀ τ := by
      exact hgz.mono_set (Set.uIcc_subset_uIcc_left hτ_uIcc)
    have hyz_τ : IntervalIntegrable (fun s => ‖y s - z s‖) volume t₀ τ := by
      exact hyz_int.mono_set (Set.uIcc_subset_uIcc_left hτ_uIcc)
    have hfyz_τ :
      IntervalIntegrable (fun s => ‖f s (y s) - f s (z s)‖) volume t₀ τ := by
        exact hfyz.mono_set (Set.uIcc_subset_uIcc_left hτ_uIcc)
    --- Difference of solution
    have h_diff :
        y τ - z τ
          = (y₀ - z₀)
            + (∫ s in t₀..τ, f s (y s) - f s (z s))
            - ∫ s in t₀..τ, g s (z s) := by
        -- rewrite both sides
        rw [hy_τ, hz_τ]
        have h1 :
          ∫ s in t₀..τ, (f s (z s) + g s (z s))
            = (∫ s in t₀..τ, f s (z s)) + (∫ s in t₀..τ, g s (z s)) := by
          rw [intervalIntegral.integral_add hfz_τ hgz_τ]
        rw [h1]
        have h2 :
          ∫ s in t₀..τ, f s (y s) - f s (z s)
            = (∫ s in t₀..τ, f s (y s)) - (∫ s in t₀..τ, f s (z s)) := by
          rw [intervalIntegral.integral_sub hfy_τ hfz_τ]
        rw [h2]
        abel_nf
    calc ‖y τ - z τ‖
        ≤ ‖y₀ - z₀‖ + ‖∫ s in t₀..τ, (f s (y s) - f s (z s))‖ +
          ‖∫ s in t₀..τ, g s (z s)‖ := by
          rw [h_diff]
          refine le_trans (norm_sub_le _ _) ?_
          apply add_le_add_left
          exact norm_add_le _ _
      _ ≤ ‖y₀ - z₀‖ + (L * ∫ s in t₀..τ, ‖y s - z s‖ ) + μ * (τ - t₀) := by
        simp[add_assoc]
        have h3: ‖∫ s in t₀..τ, g s (z s)‖ ≤ μ * (τ - t₀):= by
              have h' := intervalIntegral.norm_integral_le_of_norm_le_const
                (fun s hs => hg s (by
                  have := uIoc_of_le hmem.1 ▸ hs  -- s ∈ Ioc t₀ t
                  exact mem_Icc.mpr ⟨this.1.le, this.2.trans hmem.2⟩) (z s))
              rw [abs_of_nonneg (sub_nonneg.mpr hmem.1)] at h'
              exact h'
        have h4 :
          ‖∫ s in t₀..τ, (f s (y s) - f s (z s))‖ ≤ ∫ s in t₀..τ, ‖f s (y s) - f s (z s)‖ := by
              apply intervalIntegral.norm_integral_le_integral_norm
              exact hmem.1
        have hpt :
          ∀ s ∈ Icc t₀ τ, ‖f s (y s) - f s (z s)‖ ≤ L * ‖y s - z s‖ := by
          intro s hs
          have hs' : s ∈ Icc t₀ t₁ := ⟨hs.1, le_trans hs.2 hmem.2⟩
          have h := (hLip s hs').dist_le_mul (y s) (z s)
          simpa [dist_eq_norm] using h
        have hLyz' :  IntervalIntegrable (fun s => L * ‖y s - z s‖) volume t₀ τ := by
          exact IntervalIntegrable.const_mul hyz_τ L
        have h4' :
          ‖∫ s in t₀..τ, (f s (y s) - f s (z s))‖
            ≤ L * ∫ s in t₀..τ, ‖y s - z s‖ := by
            have h_L_bound :
              ∫ (u : ℝ) in t₀..τ, ‖f u (y u) - f u (z u)‖ ≤ ∫ (u : ℝ) in t₀..τ, L * ‖y u - z u‖ :=
              intervalIntegral.integral_mono_on
                hmem.1
                hfyz_τ
                hLyz'
                hpt
            have h_L_bound_2 :
              ∫ (u : ℝ) in t₀..τ, L * ‖y u - z u‖ = L * ∫ (u : ℝ) in t₀..τ, ‖y u - z u‖ := by
              simp;
            linarith
        exact add_le_add h4' h3
      _ = ‖y₀ - z₀‖ + μ * (τ - t₀) + L * ∫ s in t₀..τ, ‖y s - z s‖ := by ring
  have hshift : ∀ τ ∈ Icc t₀ t₁,
      (‖y τ - z τ‖ + μ / L) ≤ (‖y₀ - z₀‖ + μ / L) +
        ∫ s in t₀..τ, L * (‖y s - z s‖ + μ / L) := by
      intro τ hτ
      have hτ0 : t₀ ≤ τ := hτ.1
      have hτ_uIcc : τ ∈ [[t₀, t₁]] := Set.Icc_subset_uIcc hτ
      have sub_set : Set.uIcc t₀ τ ⊆ Set.uIcc t₀ t₁ := by
        rw [Set.uIcc_of_le hτ0, Set.uIcc_of_le ht]
        exact Set.Icc_subset_Icc_right hτ.2
      have hyz_τ : IntervalIntegrable (fun s => ‖y s - z s‖) volume t₀ τ := by
        exact hyz_int.mono_set (Set.uIcc_subset_uIcc_left hτ_uIcc)
      have hint : ∫ s in t₀..τ, L * (‖y s - z s‖ + μ / L) =
        (L * ∫ s in t₀..τ, ‖y s - z s‖) + μ * (τ - t₀) := by
        have hsimp : ∀ s, L * (‖y s - z s‖ + μ / L) = L * ‖y s - z s‖ + μ := by
          intro s; field_simp
        simp_rw [hsimp]
        rw [intervalIntegral.integral_add (hyz_τ.const_mul L) intervalIntegrable_const,
            intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const,
            smul_eq_mul]
        field_simp
      linarith [hineq_base τ hτ]
  have hw_cont : ContinuousOn (fun τ => ‖y τ - z τ‖ + μ / L) (Icc t₀ t₁) :=
    hyz_cont.add continuousOn_const
  have hG := gronwall_const hL.le hw_cont hshift
  intro t ht_mem
  have hle := hG t ht_mem
  -- hle : ‖y t - z t‖ + μ/L ≤ (‖y₀ - z₀‖ + μ/L) * exp(L*(t-t₀))
  -- unfold to the desired bound by algebra
  have hexp : (‖y₀ - z₀‖ + μ / L) * rexp (L * (t - t₀)) =
      ‖y₀ - z₀‖ * rexp (L * (t - t₀)) + μ / L * rexp (L * (t - t₀)) := by ring
  linarith

/-

  Theorem 3.5: Continuous dependence on parameters.
  λ-dependence is modeled via the perturbation term g (i.e., g t x = f_λ t x - f_λ₀ t x).
  Lipschitz is global, matching the simplification in Theorem 3.4.
  The δ-condition is expressed as: both ‖z₀ - y₀‖ and ‖g t x‖ are bounded by α,
  where α is chosen small enough (hαε) to keep the solution within ε of y.
-/
theorem continuous_dependence_parameters
    (ht : t₀ ≤ t₁)
    (hL : 0 < L)
    (hα : 0 < α)
    -- the key δ-condition: α small enough ensures solution stays within ε
    (hαε : α * (1 + 1 / L) * Real.exp (L * (t₁ - t₀)) ≤ ε)
    (hy : IsIntegralSolution t₀ t₁ y y₀ f)
    (hz : IsIntegralSolution t₀ t₁ z z₀ (fun s x => f s x + g s x))
    (hy_cont : ContinuousOn y (Set.Icc t₀ t₁))
    (hz_cont : ContinuousOn z (Set.Icc t₀ t₁))
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hg_cont : Continuous (fun p : ℝ × E => g p.1 p.2))  -- g jointly continuous
    (hLip : ∀ t ∈ Set.Icc t₀ t₁, LipschitzWith ⟨L, hL.le⟩ (f t))
    -- both perturbation sources bounded by α (plays the role of δ in the book)
    (hg   : ∀ t ∈ Set.Icc t₀ t₁, ∀ x : E, ‖g t x‖ ≤ α)
    (hz₀  : ‖z₀ - y₀‖ ≤ α) :
    ∀ t ∈ Set.Icc t₀ t₁, ‖y t - z t‖ ≤ ε := by
  -- derive integrability of g∘z from joint continuity
  have hgz : IntervalIntegrable (fun s => g s (z s)) volume t₀ t₁ :=
    IntervalIntegrable_of_lipschitz ht hg_cont hz_cont
  intro t ht_mem
  -- apply Theorem 3.4 with μ = α
  have key := continuous_dependence_ODE ht hL hα hy hz hy_cont hz_cont
    hf_cont hgz hLip hg t ht_mem
  -- key : ‖y t - z t‖ ≤ ‖y₀ - z₀‖ * exp(L*(t-t₀)) + (α/L)*(exp(L*(t-t₀)) - 1)
  have hyz₀ : ‖y₀ - z₀‖ ≤ α := by rwa [norm_sub_rev]
  have hexp_mono : Real.exp (L * (t - t₀)) ≤ Real.exp (L * (t₁ - t₀)) := by
    gcongr; linarith [ht_mem.2]
  calc ‖y t - z t‖
      ≤ ‖y₀ - z₀‖ * Real.exp (L * (t - t₀)) +
          α / L * (Real.exp (L * (t - t₀)) - 1) := key
    _ ≤ α * Real.exp (L * (t - t₀)) +
          α / L * (Real.exp (L * (t - t₀)) - 1) := by
          gcongr
    _ = α * (1 + 1 / L) * Real.exp (L * (t - t₀)) - α / L := by
          field_simp; ring
    _ ≤ α * (1 + 1 / L) * Real.exp (L * (t₁ - t₀)) - α / L := by
          gcongr
    _ ≤ α * (1 + 1 / L) * Real.exp (L * (t₁ - t₀)) := by
          linarith [div_nonneg hα.le hL.le]
    _ ≤ ε := hαε
