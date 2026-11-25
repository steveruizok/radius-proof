/-
Copyright (c) 2026 Steve Ruiz. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Steve Ruiz
-/
import Mathlib

/-!
# Rounded rectangles in the Euclidean plane

We model the Euclidean plane as `ℂ`, whose norm is the Euclidean norm
`‖x + y i‖ = √(x² + y²)`. (The product `ℝ × ℝ` would be the wrong model: Mathlib equips it with
the supremum norm, under which every "circle" is a square and the theory below would be
false in an uninteresting way.)

A *rounded rectangle* with half-width `a`, half-height `b` and corner radius `r`, centred at the
origin, is the Minkowski sum of its *core* — the axis-aligned rectangle
`[-(a - r), a - r] × [-(b - r), b - r]` — with the closed disc of radius `r`.
Its four corners are therefore quarter circles of radius `r`, joined by straight edges, and its
bounding box is `[-a, a] × [-b, b]`.

## Main definitions

* `RadiusProof.core a b r`: the core rectangle.
* `RadiusProof.roundedRect a b r`: the rounded rectangle.
* `RadiusProof.Admissible a b r`: the side conditions `0 ≤ r ≤ a` and `r ≤ b` under which the
  three parameters describe an honest rounded rectangle.
-/

open Set Metric Pointwise Complex

noncomputable section

namespace RadiusProof

/-- The *core* of a rounded rectangle: the axis-aligned rectangle whose corners are the centres of
the four corner arcs. -/
def core (a b r : ℝ) : Set ℂ :=
  Icc (-(a - r)) (a - r) ×ℂ Icc (-(b - r)) (b - r)

/-- The rounded rectangle of half-width `a`, half-height `b` and corner radius `r`, centred at the
origin: the Minkowski sum of its core with the closed disc of radius `r`. -/
def roundedRect (a b r : ℝ) : Set ℂ :=
  core a b r + closedBall (0 : ℂ) r

/-- The parameters `(a, b, r)` describe a genuine rounded rectangle: the radius is nonnegative and
does not exceed either half-extent. -/
structure Admissible (a b r : ℝ) : Prop where
  radius_nonneg : 0 ≤ r
  radius_le_halfWidth : r ≤ a
  radius_le_halfHeight : r ≤ b

theorem mem_core {a b r : ℝ} {z : ℂ} :
    z ∈ core a b r ↔ |z.re| ≤ a - r ∧ |z.im| ≤ b - r := by
  simp [core, Complex.mem_reProdIm, abs_le]

theorem mem_roundedRect {a b r : ℝ} {z : ℂ} :
    z ∈ roundedRect a b r ↔ ∃ k ∈ core a b r, ‖z - k‖ ≤ r := by
  constructor
  · rintro ⟨k, hk, v, hv, rfl⟩
    exact ⟨k, hk, by simpa using hv⟩
  · rintro ⟨k, hk, hz⟩
    exact ⟨k, hk, z - k, by simpa using hz, by ring⟩

theorem isCompact_core (a b r : ℝ) : IsCompact (core a b r) :=
  isCompact_Icc.reProdIm isCompact_Icc

theorem isCompact_roundedRect (a b r : ℝ) : IsCompact (roundedRect a b r) :=
  (isCompact_core a b r).add (isCompact_closedBall _ _)

/-- A rounded rectangle is the closed `r`-neighbourhood of its core. -/
theorem roundedRect_eq_cthickening {a b r : ℝ} (hr : 0 ≤ r) :
    roundedRect a b r = cthickening r (core a b r) := by
  simpa [roundedRect] using (isCompact_core a b r).add_closedBall_zero hr

/-- Growing the half-extents and the radius by the same amount does not move the core. -/
@[simp]
theorem core_add (a b r d : ℝ) : core (a + d) (b + d) (r + d) = core a b r := by
  simp only [core, add_sub_add_right_eq_sub]

end RadiusProof

end
