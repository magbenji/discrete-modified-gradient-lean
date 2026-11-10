/-
Copyright (c) 2026 B. J. Ridenhour. Released under Apache 2.0 license as described in the file LICENSE.

# Stability and asymptotic stability (Section 5): Theorem 5.1 and Corollary 5.2
-/
import DiscreteStability.Ascent

open scoped RealInnerProductSpace Topology
open Set Metric Filter

namespace DiscreteStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **H0_Δ** (on the ball `B̄_{r₀}(x̄)`): `f` has gradient `g` there and `g` is `L`-Lipschitz there. -/
structure LocalHyp (f : E → ℝ) (g : E → E) (xbar : E) (r₀ L : ℝ) : Prop where
  r₀_pos : 0 < r₀
  L_nonneg : 0 ≤ L
  grad : ∀ z ∈ closedBall xbar r₀, HasFDerivAt f (innerSL ℝ (g z)) z
  lip : ∀ u ∈ closedBall xbar r₀, ∀ v ∈ closedBall xbar r₀, ‖g u - g v‖ ≤ L * ‖u - v‖

/-- **H1**: `x̄` is an isolated (strict) local maximum of `f`. -/
def IsolatedMax (f : E → ℝ) (xbar : E) : Prop :=
  ∃ r > 0, ∀ x, x ≠ xbar → dist x xbar ≤ r → f x < f xbar

/-- **H2**: `x̄` is an isolated critical point of `f` (gradient `g`). -/
def IsolatedCrit (g : E → E) (xbar : E) : Prop :=
  ∃ r > 0, ∀ x, x ≠ xbar → dist x xbar ≤ r → g x ≠ 0

/-- Uniform stability of `x̄` for (Δ): `δ` does not depend on the starting index `k₀`. -/
def UniformlyStable (P : ℕ → E →L[ℝ] E) (g : E → E) (xbar : E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (k₀ : ℕ) (x : ℕ → E), IsOrbit P g k₀ x →
    dist (x k₀) xbar < δ → ∀ k ≥ k₀, dist (x k) xbar < ε

/-- Uniform asymptotic stability: uniform stability plus a uniform `δ` of attraction. -/
def UniformlyAsympStable (P : ℕ → E →L[ℝ] E) (g : E → E) (xbar : E) : Prop :=
  UniformlyStable P g xbar ∧
    ∃ δ > 0, ∀ (k₀ : ℕ) (x : ℕ → E), IsOrbit P g k₀ x →
      dist (x k₀) xbar < δ → Tendsto x atTop (𝓝 xbar)

variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ L Λ : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}

theorem LocalHyp.continuousOn (hH : LocalHyp f g xbar r₀ L) : ContinuousOn f (closedBall xbar r₀) :=
  fun z hz => (hH.grad z hz).continuousAt.continuousWithinAt

theorem LocalHyp.continuousOn_grad (hH : LocalHyp f g xbar r₀ L) :
    ContinuousOn g (closedBall xbar r₀) :=
  continuousOn_of_lip hH.L_nonneg hH.lip

/-- At an interior local maximum the gradient vanishes. -/
theorem LocalHyp.grad_xbar_eq_zero (hH : LocalHyp f g xbar r₀ L) (hH1 : IsolatedMax f xbar) :
    g xbar = 0 := by
  obtain ⟨r, hr, hmax⟩ := hH1
  have hloc : IsLocalMax f xbar := by
    filter_upwards [Metric.ball_mem_nhds xbar hr] with y hy
    by_cases hyx : y = xbar
    · rw [hyx]
    · exact (hmax y hyx (le_of_lt (mem_ball.mp hy))).le
  have h0 := hloc.hasFDerivAt_eq_zero (hH.grad xbar (mem_closedBall_self hH.r₀_pos.le))
  have : ⟪g xbar, g xbar⟫ = 0 := by
    have := congrArg (fun φ => φ (g xbar)) h0
    simpa [innerSL_apply_apply] using this
  exact inner_self_eq_zero.mp this

variable [FiniteDimensional ℝ E]

/-- The barrier construction in the proof of Theorem 5.1(i): for every `R > 0` there are
`0 < ρ ≤ R` and `δ > 0` such that every orbit started in `B_δ(x̄)` stays in `B_ρ(x̄)`,
and every step satisfies the weighted ascent inequality. -/
theorem trap (hH : LocalHyp f g xbar r₀ L) (hP : ∀ k, StepBound (P k) (lo k) (hi k))
    (hΛ : ∀ k, hi k ≤ Λ) (hS1 : L * Λ ≤ 2) (hH1 : IsolatedMax f xbar) {R : ℝ} (hR : 0 < R) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ R ∧ ρ ≤ r₀ ∧ (∀ y, y ≠ xbar → dist y xbar ≤ ρ → f y < f xbar) ∧
      ∃ δ > 0, ∀ (k₀ : ℕ) (x : ℕ → E), IsOrbit P g k₀ x → dist (x k₀) xbar < δ →
        ∀ k ≥ k₀, dist (x k) xbar < ρ ∧
          f (x k) + lo k * (2 - L * hi k) / 2 * ‖g (x k)‖ ^ 2 ≤ f (x (k + 1)) := by
  obtain ⟨r₁, hr₁, hmax⟩ := hH1
  have hgx := hH.grad_xbar_eq_zero ⟨r₁, hr₁, hmax⟩
  have hL := hH.L_nonneg
  set r := min R (min r₀ r₁) with hrdef
  have hr : 0 < r := lt_min hR (lt_min hH.r₀_pos hr₁)
  have hrR : r ≤ R := min_le_left _ _
  have hrr₀ : r ≤ r₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hrr₁ : r ≤ r₁ := (min_le_right _ _).trans (min_le_right _ _)
  set ρ := r / 4 with hρdef
  have hρ : 0 < ρ := by positivity
  have hΛ0 : 0 ≤ Λ := (hP 0).hi_nonneg.trans (hΛ 0)
  have hLhi : ∀ k, L * hi k ≤ 2 := fun k =>
    (mul_le_mul_of_nonneg_left (hΛ k) hL).trans hS1
  -- each step from `B_ρ` stays in `B_r`
  have hseg : ∀ y k, dist y xbar < ρ → ∀ τ ∈ Icc (0 : ℝ) 1,
      dist (y + τ • P k (g y)) xbar < r := by
    intro y k hy τ hτ
    have hyb : y ∈ closedBall xbar r₀ := mem_closedBall.mpr (by linarith)
    have hxb : xbar ∈ closedBall xbar r₀ := mem_closedBall_self hH.r₀_pos.le
    have h1 : ‖g y‖ ≤ L * ‖y - xbar‖ := by
      have := hH.lip y hyb xbar hxb
      rwa [hgx, sub_zero] at this
    have h2 : ‖P k (g y)‖ ≤ Λ * ‖g y‖ :=
      ((hP k).norm_le _).trans (mul_le_mul_of_nonneg_right (hΛ k) (norm_nonneg _))
    have h3 : ‖P k (g y)‖ ≤ 2 * ‖y - xbar‖ := by
      calc ‖P k (g y)‖ ≤ Λ * ‖g y‖ := h2
        _ ≤ Λ * (L * ‖y - xbar‖) := mul_le_mul_of_nonneg_left h1 hΛ0
        _ = (L * Λ) * ‖y - xbar‖ := by ring
        _ ≤ 2 * ‖y - xbar‖ := mul_le_mul_of_nonneg_right hS1 (norm_nonneg _)
    rw [dist_eq_norm] at hy ⊢
    have e : y + τ • P k (g y) - xbar = (y - xbar) + τ • P k (g y) := by abel
    rw [e]
    calc ‖(y - xbar) + τ • P k (g y)‖ ≤ ‖y - xbar‖ + ‖τ • P k (g y)‖ := norm_add_le _ _
      _ = ‖y - xbar‖ + τ * ‖P k (g y)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
      _ ≤ ‖y - xbar‖ + 1 * (2 * ‖y - xbar‖) := by
          gcongr
          · exact hτ.2
      _ < r := by linarith
  -- weighted ascent at every point of `B_ρ`
  have hasc : ∀ y k, dist y xbar < ρ →
      f y + lo k * (2 - L * hi k) / 2 * ‖g y‖ ^ 2 ≤ f (y + P k (g y)) := by
    intro y k hy
    exact step_weighted (S := closedBall xbar r₀) (hP k) hL (hLhi k)
      (fun τ hτ => mem_closedBall.mpr ((hseg y k hy τ hτ).le.trans hrr₀)) hH.grad hH.lip
  -- the annulus `A = B̄_r \ B_ρ` and `m = min_A V > 0`
  have hA : IsCompact (closedBall xbar r \ ball xbar ρ) :=
    (isCompact_closedBall xbar r).diff isOpen_ball
  have hVc : ContinuousOn (fun y => f xbar - f y) (closedBall xbar r \ ball xbar ρ) :=
    continuousOn_const.sub (hH.continuousOn.mono
      (sdiff_subset.trans (closedBall_subset_closedBall hrr₀)))
  have hVpos : ∀ y ∈ closedBall xbar r \ ball xbar ρ, 0 < f xbar - f y := by
    intro y hy
    have hy1 : dist y xbar ≤ r := mem_closedBall.mp hy.1
    have hy2 : ρ ≤ dist y xbar := not_lt.mp (fun h => hy.2 (mem_ball.mpr h))
    have hne : y ≠ xbar := by
      intro h; rw [h, dist_self] at hy2; linarith
    linarith [hmax y hne (hy1.trans hrr₁)]
  obtain ⟨m, hm, hmA⟩ := exists_pos_lower_bound hA hVc hVpos
  -- `δ` with `V < m` on `B_δ`
  have hfc : ContinuousAt f xbar :=
    (hH.grad xbar (mem_closedBall_self hH.r₀_pos.le)).continuousAt
  obtain ⟨δ', hδ', hδ'f⟩ := Metric.continuousAt_iff.mp hfc m hm
  refine ⟨ρ, hρ, by linarith, by linarith,
    fun y hy hyd => hmax y hy (hyd.trans (by linarith)), min δ' ρ, lt_min hδ' hρ, ?_⟩
  intro k₀ x hx hx0
  -- invariant: `x k ∈ B_ρ` and `V(x k) < m`
  have hinv : ∀ k ≥ k₀, dist (x k) xbar < ρ ∧ f xbar - f (x k) < m := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      refine ⟨hx0.trans_le (min_le_right _ _), ?_⟩
      have := hδ'f (hx0.trans_le (min_le_left _ _))
      rw [Real.dist_eq] at this
      linarith [neg_abs_le (f (x k₀) - f xbar)]
    | succ k hk ih =>
      have hstep := hasc (x k) k ih.1
      rw [← hx k hk] at hstep
      have hw : 0 ≤ lo k * (2 - L * hi k) / 2 * ‖g (x k)‖ ^ 2 := by
        have := (hP k).lo_nonneg
        have := hLhi k
        have : 0 ≤ lo k * (2 - L * hi k) := mul_nonneg (hP k).lo_nonneg (by linarith)
        positivity
      have hV : f xbar - f (x (k + 1)) < m := by linarith [ih.2]
      refine ⟨?_, hV⟩
      have hr' : dist (x (k + 1)) xbar < r := by
        have := hseg (x k) k ih.1 1 ⟨zero_le_one, le_rfl⟩
        rwa [one_smul, ← hx k hk] at this
      by_contra hcon
      have hmem : x (k + 1) ∈ closedBall xbar r \ ball xbar ρ :=
        ⟨mem_closedBall.mpr hr'.le, fun h => hcon (mem_ball.mp h)⟩
      linarith [hmA _ hmem]
  intro k hk
  refine ⟨(hinv k hk).1, ?_⟩
  have := hasc (x k) k (hinv k hk).1
  rwa [← hx k hk] at this

/-- **Theorem 5.1(i).** Under H0_Δ, H1 and S1, `x̄` is uniformly stable. -/
theorem stable (hH : LocalHyp f g xbar r₀ L) (hP : ∀ k, StepBound (P k) (lo k) (hi k))
    (hΛ : ∀ k, hi k ≤ Λ) (hS1 : L * Λ ≤ 2) (hH1 : IsolatedMax f xbar) :
    UniformlyStable P g xbar := by
  intro ε hε
  obtain ⟨ρ, hρ, hρε, -, -, δ, hδ, htrap⟩ := trap hH hP hΛ hS1 hH1 hε
  exact ⟨δ, hδ, fun k₀ x hx hx0 k hk => ((htrap k₀ x hx hx0 k hk).1).trans_le hρε⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The convergence half of the proofs of Theorem 5.1(ii), Corollary 5.2 and Theorem 6.1:
if the iterates stay in a compact set `T` on which `x̄` is the unique maximizer of `f` and the
unique zero of `g`, and each step gains at least `w k ‖g (x k)‖²` with `∑ w k = ∞`,
then `x k → x̄`. -/
theorem tendsto_of_weighted_ascent {T : Set E} (hT : IsCompact T) (hxbarT : xbar ∈ T)
    (hf : ContinuousOn f T) (hg : ContinuousOn g T)
    (hflt : ∀ y ∈ T, y ≠ xbar → f y < f xbar) (hgne : ∀ y ∈ T, y ≠ xbar → g y ≠ 0)
    {w : ℕ → ℝ} (hw0 : ∀ k, 0 ≤ w k)
    (hw : Tendsto (fun N => ∑ k ∈ Finset.range N, w k) atTop atTop)
    {x : ℕ → E} {k₀ : ℕ} (hxT : ∀ k ≥ k₀, x k ∈ T)
    (hasc : ∀ k ≥ k₀, f (x k) + w k * ‖g (x k)‖ ^ 2 ≤ f (x (k + 1))) :
    Tendsto x atTop (𝓝 xbar) := by
  set v : ℕ → ℝ := fun k => f xbar - f (x k) with hvdef
  have hfle : ∀ y ∈ T, f y ≤ f xbar := by
    intro y hy
    by_cases h : y = xbar
    · rw [h]
    · exact (hflt y hy h).le
  have hv0 : ∀ k ≥ k₀, 0 ≤ v k := fun k hk => by
    simp only [hvdef]; linarith [hfle _ (hxT k hk)]
  have hvstep : ∀ k ≥ k₀, v (k + 1) ≤ v k - w k * ‖g (x k)‖ ^ 2 := fun k hk => by
    simp only [hvdef]; linarith [hasc k hk]
  have hvanti : ∀ k ≥ k₀, ∀ n ≥ k, v n ≤ v k := by
    intro k hk n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
      have := hvstep n (hk.trans hn)
      have := mul_nonneg (hw0 n) (sq_nonneg ‖g (x n)‖)
      linarith
  -- `V_k` gets arbitrarily small
  have hsmall : ∀ c > 0, ∃ k ≥ k₀, v k < c := by
    intro c hc
    by_contra hcon
    push Not at hcon
    obtain ⟨δ₁, hδ₁, hδ₁f⟩ := Metric.continuousWithinAt_iff.mp (hf xbar hxbarT) c hc
    have hfar : ∀ k ≥ k₀, δ₁ ≤ dist (x k) xbar := by
      intro k hk
      by_contra h
      push Not at h
      have := hδ₁f (hxT k hk) h
      rw [Real.dist_eq] at this
      have := hcon k hk
      simp only [hvdef] at this
      linarith [neg_abs_le (f (x k) - f xbar)]
    have hK : IsCompact (T \ ball xbar δ₁) := hT.diff isOpen_ball
    have hgc : ContinuousOn (fun y => ‖g y‖ ^ 2) (T \ ball xbar δ₁) :=
      ((hg.mono sdiff_subset).norm).pow 2
    have hgpos : ∀ y ∈ T \ ball xbar δ₁, 0 < ‖g y‖ ^ 2 := by
      intro y hy
      have hne : y ≠ xbar := fun h => hy.2 (h ▸ mem_ball_self hδ₁)
      have := norm_pos_iff.mpr (hgne y hy.1 hne)
      positivity
    obtain ⟨m₁, hm₁, hm₁K⟩ := exists_pos_lower_bound hK hgc hgpos
    have hdesc : ∀ N, v (k₀ + N) ≤ v k₀ - m₁ * ∑ j ∈ Finset.range N, w (k₀ + j) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        have hk : k₀ + N ≥ k₀ := Nat.le_add_right _ _
        have h1 := hvstep (k₀ + N) hk
        have h2 : m₁ ≤ ‖g (x (k₀ + N))‖ ^ 2 :=
          hm₁K _ ⟨hxT _ hk, fun h => by
            have := hfar _ hk; rw [mem_ball] at h; linarith⟩
        have h3 := mul_le_mul_of_nonneg_left h2 (hw0 (k₀ + N))
        rw [Finset.sum_range_succ, ← add_assoc]
        nlinarith [h1, h3, ih]
    have hshift : Tendsto (fun N => ∑ j ∈ Finset.range N, w (k₀ + j)) atTop atTop := by
      refine (Filter.tendsto_atTop_add_const_right _ (-(∑ k ∈ Finset.range k₀, w k))
        (hw.comp (Filter.tendsto_add_atTop_nat k₀))).congr ?_
      intro N
      simp only [Function.comp_apply]
      rw [Nat.add_comm N k₀, Finset.sum_range_add]
      ring
    obtain ⟨N, hN⟩ := (hshift.eventually_gt_atTop (v k₀ / m₁)).exists
    rw [div_lt_iff₀ hm₁] at hN
    have := hdesc N
    have := hv0 (k₀ + N) (Nat.le_add_right _ _)
    nlinarith
  -- conclude `x k → x̄`
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hK : IsCompact (T \ ball xbar ε) := hT.diff isOpen_ball
  have hVc : ContinuousOn (fun y => f xbar - f y) (T \ ball xbar ε) :=
    continuousOn_const.sub (hf.mono sdiff_subset)
  have hVpos : ∀ y ∈ T \ ball xbar ε, 0 < f xbar - f y := by
    intro y hy
    have hne : y ≠ xbar := fun h => hy.2 (h ▸ mem_ball_self hε)
    linarith [hflt y hy.1 hne]
  obtain ⟨m', hm', hm'K⟩ := exists_pos_lower_bound hK hVc hVpos
  obtain ⟨k₁, hk₁, hvk₁⟩ := hsmall m' hm'
  refine ⟨k₁, fun n hn => ?_⟩
  by_contra hcon
  have hmem : x n ∈ T \ ball xbar ε := ⟨hxT n (hk₁.trans hn), fun h => hcon (mem_ball.mp h)⟩
  have := hm'K _ hmem
  have := hvanti k₁ hk₁ n hn
  simp only [hvdef] at *
  linarith

/-- **Corollary 5.2.** Under H0_Δ, H1, H2, S1 and the weighted divergence condition
`∑ λ₁(P_k) (2 - L λₙ(P_k)) = ∞`, `x̄` is uniformly asymptotically stable. -/
theorem asympStable_weighted (hH : LocalHyp f g xbar r₀ L)
    (hP : ∀ k, StepBound (P k) (lo k) (hi k)) (hΛ : ∀ k, hi k ≤ Λ) (hS1 : L * Λ ≤ 2)
    (hH1 : IsolatedMax f xbar) (hH2 : IsolatedCrit g xbar)
    (hW : Tendsto (fun N => ∑ k ∈ Finset.range N, lo k * (2 - L * hi k)) atTop atTop) :
    UniformlyAsympStable P g xbar := by
  refine ⟨stable hH hP hΛ hS1 hH1, ?_⟩
  obtain ⟨r₂, hr₂, hcrit⟩ := hH2
  obtain ⟨ρ, hρ, hρR, hρr₀, hρmax, δ, hδ, htrap⟩ := trap hH hP hΛ hS1 hH1 hr₂
  refine ⟨δ, hδ, fun k₀ x hx hx0 => ?_⟩
  have hL := hH.L_nonneg
  have hLhi : ∀ k, L * hi k ≤ 2 := fun k =>
    (mul_le_mul_of_nonneg_left (hΛ k) hL).trans hS1
  refine tendsto_of_weighted_ascent (T := closedBall xbar ρ) (isCompact_closedBall xbar ρ)
    (mem_closedBall_self hρ.le)
    (hH.continuousOn.mono (closedBall_subset_closedBall hρr₀))
    (hH.continuousOn_grad.mono (closedBall_subset_closedBall hρr₀))
    (fun y hy hne => hρmax y hne (mem_closedBall.mp hy))
    (fun y hy hne => hcrit y hne ((mem_closedBall.mp hy).trans hρR))
    (w := fun k => lo k * (2 - L * hi k) / 2)
    (fun k => by have := mul_nonneg (hP k).lo_nonneg (by linarith [hLhi k] : 0 ≤ 2 - L * hi k)
                 positivity)
    ?_ (fun k hk => mem_closedBall.mpr (htrap k₀ x hx hx0 k hk).1.le)
    (fun k hk => (htrap k₀ x hx hx0 k hk).2)
  have : Tendsto (fun N => (1 / 2 : ℝ) * ∑ k ∈ Finset.range N, lo k * (2 - L * hi k))
      atTop atTop := hW.const_mul_atTop (by norm_num)
  refine this.congr fun N => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Theorem 5.1(ii).** Under H0_Δ, H1, H2, H3_Δ and S2, `x̄` is uniformly asymptotically
stable. (H3_Δ is stated for the lower bounds `lo k ≤ λ₁(P_k)`; taking `lo k = λ₁(P_k)` gives
the paper's `∑ λ₁(P_k) = ∞`.) -/
theorem asympStable (hH : LocalHyp f g xbar r₀ L) (hP : ∀ k, StepBound (P k) (lo k) (hi k))
    (hΛ : ∀ k, hi k ≤ Λ) {η : ℝ} (hη : 0 < η) (hS2 : L * Λ ≤ 2 - η)
    (hH1 : IsolatedMax f xbar) (hH2 : IsolatedCrit g xbar)
    (hH3 : Tendsto (fun N => ∑ k ∈ Finset.range N, lo k) atTop atTop) :
    UniformlyAsympStable P g xbar := by
  have hL := hH.L_nonneg
  apply asympStable_weighted hH hP hΛ (by linarith) hH1 hH2
  have h1 : Tendsto (fun N => η * ∑ k ∈ Finset.range N, lo k) atTop atTop :=
    hH3.const_mul_atTop hη
  refine tendsto_atTop_mono (fun N => ?_) h1
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have : L * hi k ≤ 2 - η := (mul_le_mul_of_nonneg_left (hΛ k) hL).trans hS2
  nlinarith [(hP k).lo_nonneg]

end DiscreteStability
