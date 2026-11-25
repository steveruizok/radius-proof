/-
Copyright (c) 2026 Steve Ruiz. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Steve Ruiz
-/
import RadiusProof.Basic

/-!
# Existence: the offset of a rounded rectangle is a rounded rectangle

Let `R = roundedRect a b r` and let `d ≥ 0`. The set of points at distance at most `d` from `R`
(its closed `d`-neighbourhood, `Metric.cthickening d R`) is again a rounded rectangle, with the same
core, half-extents `a + d`, `b + d` and corner radius `r + d`.

The proof is the associativity of Minkowski addition together with the identity
`B(0, r) + B(0, d) = B(0, r + d)` for closed Euclidean discs.
-/

open Set Metric Pointwise

noncomputable section

namespace RadiusProof

/-- **Offset theorem.** The closed `d`-neighbourhood of a rounded rectangle of radius `r` is the
rounded rectangle of radius `r + d` with the same core. -/
theorem cthickening_roundedRect {a b r d : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d) :
    cthickening d (roundedRect a b r) = roundedRect (a + d) (b + d) (r + d) := by
  rw [← (isCompact_roundedRect a b r).add_closedBall_zero hd, roundedRect, roundedRect, core_add,
    add_assoc, closedBall_add_closedBall hr hd, add_zero]

/-- The outer shape of the offset theorem satisfies the same side conditions as the inner one. -/
theorem Admissible.offset {a b r d : ℝ} (h : Admissible a b r) (hd : 0 ≤ d) :
    Admissible (a + d) (b + d) (r + d) :=
  ⟨add_nonneg h.radius_nonneg hd, by linarith [h.radius_le_halfWidth],
    by linarith [h.radius_le_halfHeight]⟩

end RadiusProof

end
