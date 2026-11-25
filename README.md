# radius-proof

A machine-checked proof, in Lean 4 and Mathlib, of the corner-radius law for nested rounded
rectangles:

$$R = r + d$$

If a rounded rectangle with corner radius $r$ sits inside another rounded rectangle with a uniform
gap $d$ on every side, the outer corner radius $R$ must be $r + d$. No other radius works.

The accompanying paper is [`paper/radius.pdf`](paper/radius.pdf). It is typeset with the
LIPIcs class (`lipics-v2021.cls`, distributed under the LPPL), which is included in `paper/`.

## Statement

The plane is modelled as `ℂ`, which carries the Euclidean norm. A rounded rectangle with
half-width `a`, half-height `b` and corner radius `r` is the Minkowski sum of its core rectangle
`[-(a - r), a - r] × [-(b - r), b - r]` with the closed disc of radius `r`. The parameters are
*admissible* when `0 ≤ r ≤ min a b`. One shape surrounds another with uniform gap `d` when it is
the other's closed `d`-neighbourhood (`Metric.cthickening d`).

```lean
theorem nested_radius_theorem (h : Admissible a b r) (hd : 0 ≤ d)
    (hO : Admissible A B R) :
    roundedRect A B R = cthickening d (roundedRect a b r) ↔
      A = a + d ∧ B = b + d ∧ R = r + d
```

## Results

| Theorem | File | Statement |
| --- | --- | --- |
| `cthickening_roundedRect` | `Offset.lean` | The `d`-neighbourhood of a rounded rectangle of radius `r` is the rounded rectangle of radius `r + d`. |
| `roundedRect_inj` | `Uniqueness.lean` | An admissible rounded rectangle determines its half-width, half-height and radius. |
| `nested_radius_theorem` | `Main.lean` | The characterisation above. |
| `outer_radius_eq` / `inner_radius_eq` | `Main.lean` | `R = r + d`, equivalently `r = R - d`. |
| `equal_radii_iff` | `Main.lean` | Giving both shapes the same radius produces a uniform gap only when `d = 0`. |
| `gap_le_outer_radius` | `Main.lean` | If `R < d`, no inner rounded rectangle has a uniform gap `d` to the outer one. |

The development contains no `sorry`. `#print axioms` reports only `propext`, `Classical.choice`
and `Quot.sound` for every theorem.

## Building

Requires [elan](https://github.com/leanprover/elan).

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
lake env lean AxiomCheck.lean
```

To rebuild the paper (requires [Tectonic](https://tectonic-typesetting.github.io)):

```sh
cd paper && tectonic radius.tex
```

## Citation

See [`CITATION.cff`](CITATION.cff).

## License

The Lean development and the paper are released under the MIT license. The LIPIcs class files in
`paper/` are distributed under their own license (LPPL 1.3c).
