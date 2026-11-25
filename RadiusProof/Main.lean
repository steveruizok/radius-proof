/-
Copyright (c) 2026 Steve Ruiz. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Steve Ruiz
-/
import RadiusProof.Offset
import RadiusProof.Uniqueness

/-!
# The Nested Radius Theorem

Let an admissible rounded rectangle `roundedRect a b r` (the *inner* shape) be surrounded by a
gap of uniform width `d ≥ 0`. The *outer* shape is then, by definition, the closed
`d`-neighbourhood of the inner shape. We prove that the outer shape is a rounded rectangle and
that it is the rounded rectangle with half-extents `a + d`, `b + d` and corner radius

  `R = r + d`,

and no other. Equivalently `r = R - d`. In particular:

* using the same radius for both shapes (`R = r`) is correct only when there is no gap at all;
* an outer radius smaller than the gap (`R < d`) is not the outer radius of any uniform gap
  around any admissible rounded rectangle.

## Main results

* `RadiusProof.nested_radius_theorem`: the characterisation above, as an `↔`.
* `RadiusProof.outer_radius_eq`, `RadiusProof.inner_radius_eq`: the two directions of the law.
* `RadiusProof.equal_radii_iff`: equal radii give a uniform gap only when `d = 0`.
* `RadiusProof.gap_le_outer_radius`: the gap never exceeds the outer radius.
-/

open Set Metric Pointwise

noncomputable section

namespace RadiusProof

variable {a b r d A B R : ℝ}

/-- **The Nested Radius Theorem.** Let `roundedRect a b r` be admissible, `d ≥ 0`, and
`roundedRect A B R` admissible. The outer rounded rectangle lies at uniform distance `d` from the
inner one (i.e. is its closed `d`-neighbourhood) if and only if `A = a + d`, `B = b + d` and
`R = r + d`. -/
theorem nested_radius_theorem (h : Admissible a b r) (hd : 0 ≤ d) (hO : Admissible A B R) :
    roundedRect A B R = cthickening d (roundedRect a b r) ↔
      A = a + d ∧ B = b + d ∧ R = r + d := by
  rw [cthickening_roundedRect h.radius_nonneg hd]
  constructor
  · exact roundedRect_inj hO (h.offset hd)
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- **The outer radius law.** If an admissible rounded rectangle of radius `R` surrounds an
admissible rounded rectangle of radius `r` with a uniform gap `d`, then `R = r + d`. -/
theorem outer_radius_eq (h : Admissible a b r) (hd : 0 ≤ d) (hO : Admissible A B R)
    (hgap : roundedRect A B R = cthickening d (roundedRect a b r)) : R = r + d :=
  ((nested_radius_theorem h hd hO).1 hgap).2.2

/-- **The inner radius law.** Under the same hypotheses, `r = R - d`. -/
theorem inner_radius_eq (h : Admissible a b r) (hd : 0 ≤ d) (hO : Admissible A B R)
    (hgap : roundedRect A B R = cthickening d (roundedRect a b r)) : r = R - d := by
  rw [outer_radius_eq h hd hO hgap]; ring

/-- The uniform gap around an admissible rounded rectangle is realised by an admissible rounded
rectangle, namely the one of radius `r + d`. -/
theorem exists_outer (h : Admissible a b r) (hd : 0 ≤ d) :
    ∃ A B R, Admissible A B R ∧ roundedRect A B R = cthickening d (roundedRect a b r) :=
  ⟨a + d, b + d, r + d, h.offset hd, (cthickening_roundedRect h.radius_nonneg hd).symm⟩

/-- **The equal-radius fallacy.** Giving the outer shape the same corner radius as the inner one
produces a uniform gap if and only if there is no gap. -/
theorem equal_radii_iff (h : Admissible a b r) (hd : 0 ≤ d) (hO : Admissible A B r)
    : roundedRect A B r = cthickening d (roundedRect a b r) ↔ d = 0 ∧ A = a ∧ B = b := by
  rw [nested_radius_theorem h hd hO]
  constructor
  · rintro ⟨hA, hB, hr⟩
    have hd0 : d = 0 := by linarith
    refine ⟨hd0, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩
    simp

/-- The gap never exceeds the outer radius: if `R < d`, no admissible rounded rectangle is
surrounded by `roundedRect A B R` with uniform gap `d`. -/
theorem gap_le_outer_radius (h : Admissible a b r) (hd : 0 ≤ d) (hO : Admissible A B R)
    (hgap : roundedRect A B R = cthickening d (roundedRect a b r)) : d ≤ R := by
  rw [outer_radius_eq h hd hO hgap]; linarith [h.radius_nonneg]

/-- A worked example: a card with corner radius `8` and padding `4` should sit in a container of
corner radius `12`. -/
example {A B R : ℝ} (hO : Admissible A B R)
    (hgap : roundedRect A B R = cthickening 4 (roundedRect 100 50 8)) : R = 12 := by
  have := outer_radius_eq ⟨by norm_num, by norm_num, by norm_num⟩ (by norm_num) hO hgap
  linarith

end RadiusProof

end
