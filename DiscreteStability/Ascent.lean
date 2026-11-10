/-
Copyright (c) 2026 B. J. Ridenhour. Released under Apache 2.0 license as described in the file LICENSE.

# Discrete Lyapunov decrease (Section 4): Lemma 4.1 and consequences (C1)–(C3)
-/
import DiscreteStability.Basic

open scoped RealInnerProductSpace
open Set

namespace DiscreteStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Lemma 4.1 (one-step ascent).** Let `d = P (g x)`. If `∇f = g` is `L`-Lipschitz on a set `S`
containing the segment `{x + τ d : τ ∈ [0, t]}`, then for every `s ∈ [0, t]`,
`f x + s (1 - (s/2) L λₙ(P)) ⟪P g, g⟫ ≤ f (x + s d)`.
(The paper states it for `t = 1`; allowing `t ≤ 1` is used in the proof of Theorem 6.1.) -/
theorem ascent {f : E → ℝ} {g : E → E} {S : Set E} {L lo hi : ℝ} {P : E →L[ℝ] E}
    (hP : StepBound P lo hi) (hL : 0 ≤ L) {x : E} {t : ℝ}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) t, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    ∀ s ∈ Icc (0 : ℝ) t,
      f x + s * (1 - s / 2 * L * hi) * ⟪P (g x), g x⟫ ≤ f (x + s • P (g x)) := by
  intro s hs
  set d := P (g x) with hd
  set a := ⟪d, g x⟫ with ha
  have hxS : x ∈ S := by simpa using hseg 0 ⟨le_rfl, hs.1.trans hs.2⟩
  -- derivative of φ(τ) = f (x + τ d)
  have hφ : ∀ τ ∈ Icc (0 : ℝ) t,
      HasDerivAt (fun τ : ℝ => f (x + τ • d)) ⟪g (x + τ • d), d⟫ τ := by
    intro τ hτ
    have hl : HasDerivAt (fun τ : ℝ => x + τ • d) d τ := by
      simpa using ((hasDerivAt_id' τ).smul_const d).const_add x
    have := (hgrad _ (hseg τ hτ)).comp_hasDerivAt τ hl
    simpa [Function.comp_def, innerSL_apply_apply] using this
  -- ψ(τ) = φ(τ) - τ a + (L/2) τ² ‖d‖² is monotone on [0, t]
  set ψ : ℝ → ℝ := fun τ => f (x + τ • d) - τ * a + L / 2 * τ ^ 2 * ‖d‖ ^ 2 with hψdef
  have hψ : ∀ τ ∈ Icc (0 : ℝ) t, HasDerivAt ψ
      (⟪g (x + τ • d), d⟫ - 1 * a + L / 2 * ((2 : ℕ) * τ ^ (2 - 1)) * ‖d‖ ^ 2) τ := by
    intro τ hτ
    exact (((hφ τ hτ).sub ((hasDerivAt_id' τ).mul_const a)).add
      (((hasDerivAt_pow 2 τ).const_mul (L / 2)).mul_const (‖d‖ ^ 2)))
  have hmono : MonotoneOn ψ (Icc 0 t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
    · exact fun τ hτ => (hψ τ hτ).continuousAt.continuousWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      exact (hψ τ (Ioo_subset_Icc_self hτ)).hasDerivWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      have hτ' : τ ∈ Icc (0 : ℝ) t := Ioo_subset_Icc_self hτ
      have hz := hseg τ hτ'
      have h1 : -(‖g (x + τ • d) - g x‖ * ‖d‖) ≤ ⟪g (x + τ • d) - g x, d⟫ := by
        have := abs_real_inner_le_norm (g (x + τ • d) - g x) d
        linarith [neg_abs_le ⟪g (x + τ • d) - g x, d⟫]
      have h2 : ‖g (x + τ • d) - g x‖ ≤ L * ‖(x + τ • d) - x‖ := hlip _ hz _ hxS
      have h3 : ‖(x + τ • d) - x‖ = τ * ‖d‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1.le]
      rw [h3] at h2
      have h4 := mul_le_mul_of_nonneg_right h2 (norm_nonneg d)
      have h5 : ⟪g (x + τ • d) - g x, d⟫ = ⟪g (x + τ • d), d⟫ - a := by
        rw [inner_sub_left, ha, real_inner_comm d (g x)]
      norm_num
      nlinarith [h1, h4, h5]
  have hψs := hmono ⟨le_rfl, hs.1.trans hs.2⟩ hs hs.1
  simp only [hψdef, zero_smul, add_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero] at hψs
  -- use ‖d‖² ≤ hi ⟪d, g⟫
  have hnorm : ‖d‖ ^ 2 ≤ hi * ⟪P (g x), g x⟫ := hP.norm_sq_le (g x)
  have ha' : a = ⟪P (g x), g x⟫ := rfl
  have h6 := mul_le_mul_of_nonneg_left hnorm (by positivity : (0 : ℝ) ≤ L / 2 * s ^ 2)
  rw [← ha'] at h6
  nlinarith [hψs, h6]

section Consequences

variable {f : E → ℝ} {g : E → E} {S : Set E} {L lo hi : ℝ} {P : E →L[ℝ] E}

/-- The full step `[x, x + P g x]`, used with `t = 1`. -/
theorem ascent_step (hP : StepBound P lo hi) (hL : 0 ≤ L) {x : E}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    f x + (1 - L * hi / 2) * ⟪P (g x), g x⟫ ≤ f (x + P (g x)) := by
  have := ascent hP hL hseg hgrad hlip 1 ⟨zero_le_one, le_rfl⟩
  simp only [one_smul, one_mul] at this
  convert this using 2
  ring

/-- **(C3)** Under S1 (`L λₙ(P) ≤ 2`), `f` does not fall below `f x` anywhere along the step. -/
theorem segment_ge (hP : StepBound P lo hi) (hL : 0 ≤ L) (hS1 : L * hi ≤ 2) {x : E} {t : ℝ}
    (ht : t ≤ 1)
    (hseg : ∀ τ ∈ Icc (0 : ℝ) t, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    ∀ s ∈ Icc (0 : ℝ) t, f x ≤ f (x + s • P (g x)) := by
  intro s hs
  have h := ascent hP hL hseg hgrad hlip s hs
  have hs1 : s ≤ 1 := hs.2.trans ht
  have hcoef : 0 ≤ s * (1 - s / 2 * L * hi) := by
    apply mul_nonneg hs.1
    have : s * (L * hi) ≤ 2 := by nlinarith [mul_nonneg hL (hP.hi_nonneg), hs.1]
    nlinarith
  have := mul_nonneg hcoef (hP.psd (g x))
  linarith

/-- **(C1)** Under S1, `V(x_{k+1}) ≤ V(x_k)`, i.e. `f x ≤ f (x + P g x)`. -/
theorem step_mono (hP : StepBound P lo hi) (hL : 0 ≤ L) (hS1 : L * hi ≤ 2) {x : E}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    f x ≤ f (x + P (g x)) := by
  simpa using segment_ge hP hL hS1 le_rfl hseg hgrad hlip 1 ⟨zero_le_one, le_rfl⟩

/-- Weighted decrease: `f x + ½ λ₁(P) (2 - L λₙ(P)) ‖g x‖² ≤ f (x + P g x)` under S1.
This is the inequality used in Corollary 5.2. -/
theorem step_weighted (hP : StepBound P lo hi) (hL : 0 ≤ L) (hS1 : L * hi ≤ 2) {x : E}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    f x + lo * (2 - L * hi) / 2 * ‖g x‖ ^ 2 ≤ f (x + P (g x)) := by
  have h := ascent_step hP hL hseg hgrad hlip
  have hc : 0 ≤ 1 - L * hi / 2 := by linarith
  have := mul_le_mul_of_nonneg_left (hP.lower (g x)) hc
  nlinarith [this, h]

/-- **(C2)** Under S2 (`L λₙ(P) ≤ 2 - η`),
`V(x_{k+1}) ≤ V(x_k) - (η/2) λ₁(P) ‖∇f(x_k)‖²`. -/
theorem step_strict (hP : StepBound P lo hi) (hL : 0 ≤ L) {η : ℝ} (hS2 : L * hi ≤ 2 - η)
    (hη : 0 ≤ η) {x : E}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    f x + η / 2 * lo * ‖g x‖ ^ 2 ≤ f (x + P (g x)) := by
  have h := step_weighted hP hL (by linarith) hseg hgrad hlip
  have h1 : η / 2 * lo * ‖g x‖ ^ 2 ≤ lo * (2 - L * hi) / 2 * ‖g x‖ ^ 2 := by
    have := mul_nonneg hP.lo_nonneg (sq_nonneg ‖g x‖)
    nlinarith
  linarith

end Consequences

end DiscreteStability
