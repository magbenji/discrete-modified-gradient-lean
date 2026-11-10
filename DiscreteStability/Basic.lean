/-
Copyright (c) 2026 B. J. Ridenhour. Released under Apache 2.0 license as described in the file LICENSE.

# Setting and hypotheses (Section 2)

We work in a real inner product space `E` (finite-dimensional where compactness is needed,
e.g. `EuclideanSpace ℝ (Fin n)`). The objective is `f : E → ℝ` with gradient `g : E → E`,
expressed as `HasFDerivAt f (innerSL ℝ (g z)) z`, i.e. `Df(z) h = ⟪g z, h⟫`.

The step matrices are continuous linear maps `P k : E →L[ℝ] E`. Instead of eigenvalues we use
Loewner bounds: `StepBound P lo hi` says that `P` is symmetric and
`lo ‖u‖² ≤ ⟪P u, u⟫ ≤ hi ‖u‖²` for all `u`, with `0 ≤ lo ≤ hi`. For a symmetric matrix this is
exactly `lo ≤ λ₁(P)` and `λₙ(P) ≤ hi`, so taking `lo = λ₁(P)` and `hi = λₙ(P)` recovers the
paper's hypotheses; any weaker pair of bounds also works.

The iteration (Δ) started at index `k₀` is `x (k+1) = x k + P k (g (x k))` for `k ≥ k₀`.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped RealInnerProductSpace

namespace DiscreteStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `StepBound P lo hi`: `P` is symmetric and `lo • I ⪯ P ⪯ hi • I` with `0 ≤ lo ≤ hi`.
In finite dimensions this means `lo ≤ λ₁(P)` and `λₙ(P) ≤ hi`. -/
structure StepBound (P : E →L[ℝ] E) (lo hi : ℝ) : Prop where
  symm : ∀ u v, ⟪P u, v⟫ = ⟪u, P v⟫
  lo_nonneg : 0 ≤ lo
  lo_le_hi : lo ≤ hi
  lower : ∀ u, lo * ‖u‖ ^ 2 ≤ ⟪P u, u⟫
  upper : ∀ u, ⟪P u, u⟫ ≤ hi * ‖u‖ ^ 2

/-- The iteration (Δ) started at index `k₀`. -/
def IsOrbit (P : ℕ → E →L[ℝ] E) (g : E → E) (k₀ : ℕ) (x : ℕ → E) : Prop :=
  ∀ k ≥ k₀, x (k + 1) = x k + P k (g (x k))

namespace StepBound

variable {P : E →L[ℝ] E} {lo hi : ℝ}

theorem hi_nonneg (h : StepBound P lo hi) : 0 ≤ hi := h.lo_nonneg.trans h.lo_le_hi

/-- `P` is positive semidefinite. -/
theorem psd (h : StepBound P lo hi) (u : E) : 0 ≤ ⟪P u, u⟫ :=
  le_trans (mul_nonneg h.lo_nonneg (sq_nonneg _)) (h.lower u)

/-- Cauchy–Schwarz for the semi-inner product `(u, v) ↦ ⟪P u, v⟫`. -/
theorem inner_sq_le (h : StepBound P lo hi) (u v : E) :
    ⟪P u, v⟫ ^ 2 ≤ ⟪P u, u⟫ * ⟪P v, v⟫ := by
  have hs : ⟪P v, u⟫ = ⟪P u, v⟫ := (h.symm v u).trans (real_inner_comm (P u) v)
  have key : ∀ t : ℝ, 0 ≤ ⟪P v, v⟫ * (t * t) + (2 * ⟪P u, v⟫) * t + ⟪P u, u⟫ := by
    intro t
    have h0 := h.psd (u + t • v)
    have e : ⟪P (u + t • v), u + t • v⟫
        = ⟪P v, v⟫ * (t * t) + (2 * ⟪P u, v⟫) * t + ⟪P u, u⟫ := by
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hs]
      ring
    rw [e] at h0
    exact h0
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith [hd]

theorem hi_mul_inner_nonneg (h : StepBound P lo hi) (u : E) : 0 ≤ hi * ⟪P u, u⟫ :=
  mul_nonneg h.hi_nonneg (h.psd u)

/-- `P² ⪯ λₙ(P) P`: `‖P u‖² ≤ hi ⟪P u, u⟫`. -/
theorem norm_sq_le (h : StepBound P lo hi) (u : E) : ‖P u‖ ^ 2 ≤ hi * ⟪P u, u⟫ := by
  have h1 := h.inner_sq_le u (P u)
  rw [real_inner_self_eq_norm_sq] at h1
  have h2 := h.upper (P u)
  have h3 := h.psd u
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  rcases (sq_nonneg ‖P u‖).eq_or_lt with h0 | hpos
  · rw [← h0]; exact h.hi_mul_inner_nonneg u
  · have : ‖P u‖ ^ 2 * ‖P u‖ ^ 2 ≤ (hi * ⟪P u, u⟫) * ‖P u‖ ^ 2 := by nlinarith [h1, h4]
    exact le_of_mul_le_mul_right this hpos

/-- Step-length bound: `‖P u‖ ≤ hi ‖u‖`. -/
theorem norm_le (h : StepBound P lo hi) (u : E) : ‖P u‖ ≤ hi * ‖u‖ := by
  have h1 := h.norm_sq_le u
  have h2 : ⟪P u, u⟫ ≤ ‖P u‖ * ‖u‖ := real_inner_le_norm _ _
  have h3 := mul_le_mul_of_nonneg_left h2 h.hi_nonneg
  rcases (norm_nonneg (P u)).eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg h.hi_nonneg (norm_nonneg _)
  · have : ‖P u‖ * ‖P u‖ ≤ (hi * ‖u‖) * ‖P u‖ := by nlinarith [h1, h3]
    exact le_of_mul_le_mul_right this hpos

end StepBound

omit [InnerProductSpace ℝ E] in
/-- A map that is `L`-Lipschitz on `S` (in the form `‖g u - g v‖ ≤ L ‖u - v‖`) is continuous on `S`. -/
theorem continuousOn_of_lip {F : Type*} [NormedAddCommGroup F] {g : E → F} {S : Set E} {L : ℝ}
    (hL : 0 ≤ L) (h : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) : ContinuousOn g S := by
  intro z hz
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε / (L + 1), by positivity, fun {y} hy hyz => ?_⟩
  rw [dist_eq_norm] at hyz ⊢
  calc ‖g y - g z‖ ≤ L * ‖y - z‖ := h y hy z hz
    _ ≤ (L + 1) * ‖y - z‖ := by nlinarith [norm_nonneg (y - z)]
    _ < (L + 1) * (ε / (L + 1)) := by gcongr
    _ = ε := by field_simp

/-- A continuous positive function on a compact set has a positive lower bound. -/
theorem exists_pos_lower_bound {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {φ : X → ℝ} (hc : ContinuousOn φ K) (hpos : ∀ x ∈ K, 0 < φ x) :
    ∃ m > 0, ∀ x ∈ K, m ≤ φ x := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn h hc
    exact ⟨φ x₀, hpos x₀ hx₀, fun x hx => hmin hx⟩

end DiscreteStability
