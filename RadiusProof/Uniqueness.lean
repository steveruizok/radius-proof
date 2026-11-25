/-
Copyright (c) 2026 Steve Ruiz. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Steve Ruiz
-/
import RadiusProof.Basic

/-!
# Uniqueness: a rounded rectangle determines its parameters

If two admissible rounded rectangles are equal as subsets of the plane, then their half-widths,
half-heights and corner radii agree.

* The half-width is recovered as the largest real part attained: `a ∈ roundedRect a b r`, and no
  point of `roundedRect a b r` has real part exceeding `a`.
* The radius is then recovered from the top edge: the point `(a - t) + b i` belongs to
  `roundedRect a b r` (for `0 ≤ t`) if and only if `r ≤ t`. In words, the flat part of the top edge
  stops exactly `r` short of the bounding box.
-/

open Set Metric Pointwise Complex

noncomputable section

namespace RadiusProof

variable {a b r : ℝ}

theorem abs_re_le_of_mem_roundedRect {z : ℂ} (hz : z ∈ roundedRect a b r) : |z.re| ≤ a := by
  obtain ⟨k, hk, hzk⟩ := mem_roundedRect.1 hz
  have h₁ := (mem_core.1 hk).1
  have h₂ : |(z - k).re| ≤ r := (abs_re_le_norm _).trans hzk
  rw [sub_re] at h₂
  calc |z.re| = |(z.re - k.re) + k.re| := by ring_nf
    _ ≤ |z.re - k.re| + |k.re| := abs_add_le _ _
    _ ≤ a := by linarith

theorem abs_im_le_of_mem_roundedRect {z : ℂ} (hz : z ∈ roundedRect a b r) : |z.im| ≤ b := by
  obtain ⟨k, hk, hzk⟩ := mem_roundedRect.1 hz
  have h₁ := (mem_core.1 hk).2
  have h₂ : |(z - k).im| ≤ r := (abs_im_le_norm _).trans hzk
  rw [sub_im] at h₂
  calc |z.im| = |(z.im - k.im) + k.im| := by ring_nf
    _ ≤ |z.im - k.im| + |k.im| := abs_add_le _ _
    _ ≤ b := by linarith

/-- The rightmost point of the horizontal axis lies on the rounded rectangle. -/
theorem ofReal_mem_roundedRect (h : Admissible a b r) : (a : ℂ) ∈ roundedRect a b r := by
  refine mem_roundedRect.2 ⟨((a - r : ℝ) : ℂ), mem_core.2 ⟨?_, ?_⟩, ?_⟩
  · simp [abs_of_nonneg (sub_nonneg.2 h.radius_le_halfWidth)]
  · simp [h.radius_le_halfHeight]
  · simp [← ofReal_sub, abs_of_nonneg h.radius_nonneg]

/-- The topmost point of the vertical axis lies on the rounded rectangle. -/
theorem mul_I_mem_roundedRect (h : Admissible a b r) : (b : ℂ) * I ∈ roundedRect a b r := by
  refine mem_roundedRect.2 ⟨((b - r : ℝ) : ℂ) * I, mem_core.2 ⟨?_, ?_⟩, ?_⟩
  · simp [h.radius_le_halfWidth]
  · simp [abs_of_nonneg (sub_nonneg.2 h.radius_le_halfHeight)]
  · rw [← sub_mul, ← ofReal_sub, norm_mul, norm_I, mul_one, sub_sub_cancel, norm_real,
      Real.norm_of_nonneg h.radius_nonneg]

/-- The point where the top edge meets the top-right corner arc lies on the rounded rectangle. -/
theorem tangentPoint_mem_roundedRect (h : Admissible a b r) :
    ((a - r : ℝ) : ℂ) + (b : ℂ) * I ∈ roundedRect a b r := by
  refine mem_roundedRect.2 ⟨((a - r : ℝ) : ℂ) + ((b - r : ℝ) : ℂ) * I, mem_core.2 ⟨?_, ?_⟩, ?_⟩
  · simp [abs_of_nonneg (sub_nonneg.2 h.radius_le_halfWidth)]
  · simp [abs_of_nonneg (sub_nonneg.2 h.radius_le_halfHeight)]
  · rw [add_sub_add_left_eq_sub, ← sub_mul, ← ofReal_sub, norm_mul, norm_I, mul_one,
      sub_sub_cancel, norm_real, Real.norm_of_nonneg h.radius_nonneg]

/-- Along the line `Im z = b`, no point of the rounded rectangle lies strictly to the right of the
tangent point `(a - r) + b i`. -/
theorem le_of_mem_roundedRect_top {t : ℝ} (ht : 0 ≤ t)
    (hz : ((a - t : ℝ) : ℂ) + (b : ℂ) * I ∈ roundedRect a b r) : r ≤ t := by
  by_contra! hlt
  obtain ⟨k, hk, hzk⟩ := mem_roundedRect.1 hz
  obtain ⟨hkre, hkim⟩ := mem_core.1 hk
  have hkre' := (abs_le.1 hkre).2
  have hkim' := (abs_le.1 hkim).2
  set w := ((a - t : ℝ) : ℂ) + (b : ℂ) * I - k with hw
  have hwre : w.re = a - t - k.re := by simp [hw]
  have hwim : w.im = b - k.im := by simp [hw]
  have hre : 0 < w.re := by rw [hwre]; linarith
  have him : r ≤ w.im := by rw [hwim]; linarith
  have hr : 0 ≤ r := ht.trans hlt.le
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; ring
  have : r ^ 2 < ‖w‖ ^ 2 := by
    rw [hsq]; nlinarith [mul_pos hre hre, mul_le_mul him him hr (hr.trans him)]
  have : ‖w‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzk 2
  linarith

/-- **Uniqueness of parameters.** Two admissible rounded rectangles that are equal as sets have the
same half-width, half-height and corner radius. -/
theorem roundedRect_inj {a b r a' b' r' : ℝ} (h : Admissible a b r) (h' : Admissible a' b' r')
    (heq : roundedRect a b r = roundedRect a' b' r') : a = a' ∧ b = b' ∧ r = r' := by
  have ha : a = a' := by
    have h₁ := abs_re_le_of_mem_roundedRect (heq ▸ ofReal_mem_roundedRect h)
    have h₂ := abs_re_le_of_mem_roundedRect (heq.symm ▸ ofReal_mem_roundedRect h')
    simp only [ofReal_re] at h₁ h₂
    have := h.radius_nonneg; have := h'.radius_nonneg
    have := h.radius_le_halfWidth; have := h'.radius_le_halfWidth
    rw [abs_of_nonneg (by linarith)] at h₁ h₂
    linarith
  have hb : b = b' := by
    have h₁ := abs_im_le_of_mem_roundedRect (heq ▸ mul_I_mem_roundedRect h)
    have h₂ := abs_im_le_of_mem_roundedRect (heq.symm ▸ mul_I_mem_roundedRect h')
    simp only [mul_I_im, ofReal_re] at h₁ h₂
    have := h.radius_nonneg; have := h'.radius_nonneg
    have := h.radius_le_halfHeight; have := h'.radius_le_halfHeight
    rw [abs_of_nonneg (by linarith)] at h₁ h₂
    linarith
  subst ha hb
  refine ⟨rfl, rfl, le_antisymm ?_ ?_⟩
  · exact le_of_mem_roundedRect_top h'.radius_nonneg (heq.symm ▸ tangentPoint_mem_roundedRect h')
  · exact le_of_mem_roundedRect_top h.radius_nonneg (heq ▸ tangentPoint_mem_roundedRect h)

end RadiusProof

end
