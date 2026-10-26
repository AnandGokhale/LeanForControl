import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.Transform
import LeanForControl.Analysis.DiniDeriv
import Architect

/-!
# `Analysis.OneSidedLipschitz` — one-sided Lipschitz maps

On a real inner product space, `F : E → E` is *one-sided Lipschitz* on `C` with constant `c ∈ ℝ`
when `⟪F x - F y, x - y⟫ ≤ c * ‖x - y‖ ^ 2` for all `x, y ∈ C`.  Unlike `LipschitzOnWith`, the
constant may be negative.

For a vector field, the constant bounds the rate at which trajectories separate.  Two cases have
names of their own:

* `IsInfinitesimallyNonexpansiveOn F C` — one-sided Lipschitz with constant `0`;
* `IsInfinitesimallyContractingOn c F C` — one-sided Lipschitz with constant `-c`, *infinitesimally
  contracting with rate `c`*.

No regularity of `F` is assumed.

Along the flow of a field that is one-sided Lipschitz with constant `c`, two integral curves
separate at most like `e^{c t}` (`OneSidedLipschitzOnWith.norm_sub_le_exp`).  For an
infinitesimally contracting field they converge exponentially; for an infinitesimally nonexpansive
one their distance does not increase (`IsInfinitesimallyNonexpansiveOn.antitoneOn_norm_sub`).
The same bounds hold for the speed `‖F (x t)‖` along one integral curve
(`OneSidedLipschitzOnWith.speed_le_exp`,
`IsInfinitesimallyNonexpansiveOn.antitoneOn_speed`), by comparing the curve with its own time
shift.

Reference: Bullo, *Contraction Theory for Dynamical Systems* (terminology for one-sided Lipschitz
vector fields).
-/

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `F` is *one-sided Lipschitz* on `C` with constant `c`:
`⟪F x - F y, x - y⟫ ≤ c * ‖x - y‖ ^ 2` for all `x, y ∈ C`. -/
@[blueprint "def:oneSidedLipschitzOnWith"
  (title := "One-sided Lipschitz map")
  (statement := /-- On a real inner product space $E$, a map $F : E \to E$ is
    \emph{one-sided Lipschitz} on $C \subseteq E$ with constant $c \in \mathbb{R}$ when
    \[
      \langle F(x) - F(y), x - y \rangle \le c \, \|x - y\|^2 \qquad \text{for all } x, y \in C.
    \]
    The constant may be negative.  With $c = 0$, $F$ is called
    \emph{infinitesimally nonexpansive} on $C$. -/)]
def OneSidedLipschitzOnWith (c : ℝ) (F : E → E) (C : Set E) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ⟪F x - F y, x - y⟫ ≤ c * ‖x - y‖ ^ 2

/-- `F` is *infinitesimally nonexpansive* on `C`: one-sided Lipschitz with constant `0`. -/
@[blueprint "def:isInfinitesimallyNonexpansiveOn"
  (title := "Infinitesimally nonexpansive map")
  (statement := /-- A map $F$ is \emph{infinitesimally nonexpansive} on $C$ when it is one-sided
    Lipschitz on $C$ with constant $0$ (\cref{def:oneSidedLipschitzOnWith}):
    $\langle F(x) - F(y), x - y \rangle \le 0$ for all $x, y \in C$. -/)]
def IsInfinitesimallyNonexpansiveOn (F : E → E) (C : Set E) : Prop :=
  OneSidedLipschitzOnWith 0 F C

/-- `F` is *infinitesimally contracting with rate `c`* on `C`: one-sided Lipschitz with
constant `-c`. -/
@[blueprint "def:isInfinitesimallyContractingOn"
  (title := "Infinitesimally contracting map")
  (statement := /-- A map $F$ is \emph{infinitesimally contracting with rate} $c$ on $C$ when it
    is one-sided Lipschitz on $C$ with constant $-c$ (\cref{def:oneSidedLipschitzOnWith}):
    $\langle F(x) - F(y), x - y \rangle \le -c \, \|x - y\|^2$ for all $x, y \in C$. -/)]
def IsInfinitesimallyContractingOn (c : ℝ) (F : E → E) (C : Set E) : Prop :=
  OneSidedLipschitzOnWith (-c) F C


section IntegralCurves

variable {F : E → E} {C : Set E} {x y : ℝ → E} {I : Set ℝ}

/-- **Separation of trajectories.**  Two integral curves of an autonomous field that is one-sided
Lipschitz with constant `c`, on an interval and inside the region where the bound holds, separate
at most like `e^{c t}`. -/
@[blueprint "thm:oneSidedLipschitzOnWith-norm-sub-le-exp"
  (title := "One-sided Lipschitz fields separate trajectories at most exponentially")
  (statement := /-- Let $F$ be one-sided Lipschitz on $C$ with constant $c$
    (\cref{def:oneSidedLipschitzOnWith}), and let $x$, $y$ be integral curves of
    $\dot x = F(x)$ on an interval $I$ with values in $C$.  Then for $s \le t$ in $I$,
    \[
      \|x(t) - y(t)\| \le e^{c(t - s)} \, \|x(s) - y(s)\|.
    \] -/)
  (proof := /-- $\frac{d}{dt} \|x - y\|^2 = 2 \langle x - y, F(x) - F(y) \rangle
    \le 2c \, \|x - y\|^2$; Gr\"onwall's inequality gives
    $\|x(t) - y(t)\|^2 \le e^{2c(t - s)} \|x(s) - y(s)\|^2$. -/)]
theorem OneSidedLipschitzOnWith.norm_sub_le_exp {c : ℝ} (hF : OneSidedLipschitzOnWith c F C)
    (hI : I.OrdConnected) (hx : IsIntegralCurveOn x (fun _ => F) I)
    (hy : IsIntegralCurveOn y (fun _ => F) I) (hxC : Set.MapsTo x I C)
    (hyC : Set.MapsTo y I C) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    ‖x t - y t‖ ≤ Real.exp (c * (t - s)) * ‖x s - y s‖ := by
  have hsub : Set.Icc s t ⊆ I := hI.out hs ht
  -- `D⁺ ‖x - y‖² = 2⟪x - y, F x - F y⟫ ≤ 2c ‖x - y‖²`.
  have h_dini : ∀ r ∈ Set.Ico s t,
      D⁺ (fun r => ‖x r - y r‖ ^ 2) r ≤ (2 * c * ‖x r - y r‖ ^ 2 : ℝ) := by
    intro r hr
    have hr' : r ∈ I := hsub (Set.Ico_subset_Icc_self hr)
    refine (diniDerivRight_of_hasDerivWithinAt (((hx r hr').sub (hy r hr')).norm_sq
      |>.mono_of_mem_nhdsWithin (Filter.mem_of_superset (Icc_mem_nhdsGE_of_mem hr) hsub))).le.trans
      (EReal.coe_le_coe_iff.2 ?_)
    calc 2 * ⟪x r - y r, F (x r) - F (y r)⟫ = 2 * ⟪F (x r) - F (y r), x r - y r⟫ := by
          rw [real_inner_comm]
      _ ≤ 2 * (c * ‖x r - y r‖ ^ 2) := by
          gcongr
          exact hF _ (hxC hr') _ (hyC hr')
      _ = 2 * c * ‖x r - y r‖ ^ 2 := by ring
  calc ‖x t - y t‖ = √(‖x t - y t‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(‖x s - y s‖ ^ 2 * Real.exp (2 * c * (t - s))) := Real.sqrt_le_sqrt <|
        le_mul_exp_of_diniDerivRight_le
          (((hx.continuousOn.sub hy.continuousOn).norm.pow 2).mono hsub) h_dini t ⟨hst, le_rfl⟩
    _ = √((Real.exp (c * (t - s)) * ‖x s - y s‖) ^ 2) := by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    _ = Real.exp (c * (t - s)) * ‖x s - y s‖ := Real.sqrt_sq (by positivity)

/-- **Distances do not increase.**  Two integral curves of an infinitesimally nonexpansive
autonomous field, on an interval and inside the region where it is nonexpansive, do not move
apart.  The case `c = 0` of `OneSidedLipschitzOnWith.norm_sub_le_exp`. -/
@[blueprint "thm:isInfinitesimallyNonexpansiveOn-antitoneOn-norm-sub"
  (title := "Infinitesimally nonexpansive fields do not increase distances")
  (statement := /-- Let $F$ be infinitesimally nonexpansive on $C$
    (\cref{def:isInfinitesimallyNonexpansiveOn}), and let $x$, $y$ be integral curves of
    $\dot x = F(x)$ on an interval $I$ with values in $C$.  Then $t \mapsto \|x(t) - y(t)\|$ is
    nonincreasing on $I$. -/)
  (proof := /-- The case $c = 0$ of \cref{thm:oneSidedLipschitzOnWith-norm-sub-le-exp}. -/)]
theorem IsInfinitesimallyNonexpansiveOn.antitoneOn_norm_sub
    (hF : IsInfinitesimallyNonexpansiveOn F C) (hI : I.OrdConnected)
    (hx : IsIntegralCurveOn x (fun _ => F) I) (hy : IsIntegralCurveOn y (fun _ => F) I)
    (hxC : Set.MapsTo x I C) (hyC : Set.MapsTo y I C) :
    AntitoneOn (fun t => ‖x t - y t‖) I := fun s hs t ht hst => by
  simpa using OneSidedLipschitzOnWith.norm_sub_le_exp hF hI hx hy hxC hyC hs ht hst

/-- **Speed of trajectories.**  Along an integral curve of an autonomous field that is one-sided
Lipschitz with constant `c`, the speed `‖F (x t)‖` grows at most like `e^{c t}`. -/
@[blueprint "thm:oneSidedLipschitzOnWith-speed-le-exp"
  (title := "One-sided Lipschitz fields change speed at most exponentially")
  (statement := /-- Let $F$ be one-sided Lipschitz on $C$ with constant $c$
    (\cref{def:oneSidedLipschitzOnWith}), and let $x$ be an integral curve of $\dot x = F(x)$
    on an interval $I$ with values in $C$.  Then for $s \le t$ in $I$,
    \[
      \|F(x(t))\| \le e^{c(t - s)} \, \|F(x(s))\|.
    \] -/)
  (proof := /-- For $0 < h < t - s$, the time shift $r \mapsto x(r - h)$ is again an integral
    curve, so \cref{thm:oneSidedLipschitzOnWith-norm-sub-le-exp} on $[s + h, t]$ gives
    $\|x(t) - x(t - h)\| \le e^{c(t - s - h)} \|x(s + h) - x(s)\|$.  Divide by $h$ and let
    $h \to 0^+$: the two quotients tend to $\|\dot x(t)\| = \|F(x(t))\|$ and
    $\|\dot x(s)\| = \|F(x(s))\|$. -/)]
theorem OneSidedLipschitzOnWith.speed_le_exp {c : ℝ} (hF : OneSidedLipschitzOnWith c F C)
    (hI : I.OrdConnected) (hx : IsIntegralCurveOn x (fun _ => F) I) (hxC : Set.MapsTo x I C)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    ‖F (x t)‖ ≤ Real.exp (c * (t - s)) * ‖F (x s)‖ := by
  rcases hst.eq_or_lt with rfl | hlt
  · simp
  have hsub : Set.Icc s t ⊆ I := hI.out hs ht
  have hxst : IsIntegralCurveOn x (fun _ => F) (Set.Icc s t) := hx.mono hsub
  -- Comparing `x` with its time shift by `h`, on `[s + h, t]`.
  have key : ∀ h ∈ Set.Ioo 0 (t - s),
      ‖x t - x (t - h)‖ ≤ Real.exp (c * (t - (s + h))) * ‖x (s + h) - x s‖ := by
    intro h hh
    have := hF.norm_sub_le_exp (s := s + h) (t := t) Set.ordConnected_Icc
      (hxst.mono (Set.Icc_subset_Icc (by linarith [hh.1]) le_rfl))
      ((Set.vadd_Icc (-(-h)) s t ▸ hxst.comp_add (-h)).mono
        (Set.Icc_subset_Icc (by linarith) (by linarith [hh.1])))
      (fun r hr => hxC (hsub ⟨by linarith [hr.1, hh.1], hr.2⟩))
      (fun r hr => hxC (hsub ⟨by linarith [hr.1], by linarith [hr.2, hh.1]⟩))
      (Set.left_mem_Icc.2 (by linarith [hh.2])) (Set.right_mem_Icc.2 (by linarith [hh.2]))
      (by linarith [hh.2])
    simpa only [Function.comp_apply, ← sub_eq_add_neg, add_sub_cancel_right] using this
  -- The two difference quotients tend to the speeds at `s` and at `t`.
  have h_right : Filter.Tendsto (fun h => ‖x (s + h) - x s‖ / h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ‖F (x s)‖) :=
    ((hxst s (Set.left_mem_Icc.2 hst)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hlt)
      |>.tendsto_slope_zero_right.norm).congr' <|
      eventually_nhdsWithin_of_forall fun h (hh : 0 < h) => by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hh.le, inv_mul_eq_div]
  have h_left : Filter.Tendsto (fun h => ‖x t - x (t - h)‖ / h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ‖F (x t)‖) := by
    refine (((hxst t (Set.right_mem_Icc.2 hst)).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hlt)
      |>.tendsto_slope_zero_left.comp (by simpa using tendsto_neg_nhdsGT (a := (0 : ℝ)))).norm
      ).congr' <|
      eventually_nhdsWithin_of_forall fun h (hh : 0 < h) => ?_
    rw [Function.comp_apply, norm_smul, norm_inv, norm_neg, Real.norm_of_nonneg hh.le,
      norm_sub_rev, ← sub_eq_add_neg, inv_mul_eq_div]
  refine le_of_tendsto_of_tendsto h_left
    ((((by fun_prop : Continuous fun h => Real.exp (c * (t - (s + h)))).tendsto' 0 _
      (by simp)).mono_left nhdsWithin_le_nhds).mul h_right) ?_
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hlt)] with h hh
  calc ‖x t - x (t - h)‖ / h
      ≤ Real.exp (c * (t - (s + h))) * ‖x (s + h) - x s‖ / h :=
        div_le_div_of_nonneg_right (key h hh) hh.1.le
    _ = Real.exp (c * (t - (s + h))) * (‖x (s + h) - x s‖ / h) := mul_div_assoc _ _ _

/-- **Speed does not increase.**  Along an integral curve of an infinitesimally nonexpansive
autonomous field, the speed `‖F (x t)‖` does not increase.  The case `c = 0` of
`OneSidedLipschitzOnWith.speed_le_exp`. -/
@[blueprint "thm:isInfinitesimallyNonexpansiveOn-antitoneOn-speed"
  (title := "Infinitesimally nonexpansive fields do not increase speed")
  (statement := /-- Let $F$ be infinitesimally nonexpansive on $C$
    (\cref{def:isInfinitesimallyNonexpansiveOn}), and let $x$ be an integral curve of
    $\dot x = F(x)$ on an interval $I$ with values in $C$.  Then $t \mapsto \|F(x(t))\|$ is
    nonincreasing on $I$. -/)
  (proof := /-- The case $c = 0$ of \cref{thm:oneSidedLipschitzOnWith-speed-le-exp}. -/)]
theorem IsInfinitesimallyNonexpansiveOn.antitoneOn_speed
    (hF : IsInfinitesimallyNonexpansiveOn F C) (hI : I.OrdConnected)
    (hx : IsIntegralCurveOn x (fun _ => F) I) (hxC : Set.MapsTo x I C) :
    AntitoneOn (fun t => ‖F (x t)‖) I := fun s hs t ht hst => by
  simpa using OneSidedLipschitzOnWith.speed_le_exp hF hI hx hxC hs ht hst

end IntegralCurves
