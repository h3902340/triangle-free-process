# Lean verification of the Family A core

This Lake project formalizes the **proved** combinatorial lemmas behind
Family A. It does **not** claim the conjectural SOTA bound
\(\alpha(A_q)=O(\sqrt{n\log n})\) or \(R(3,k)\ge(\tfrac12-o(1))k^2/\log k\)
from an explicit construction.

Pinned toolchain: Lean 4.33.0 + mathlib `v4.33.0`. There are no `sorry`s.

## Verified theorems

| Paper fact | Lean name (`R3tBound.Results`) |
|---|---|
| Fibre constraint | `fibre_constraint_empty` |
| Tight 4-interval \(\Rightarrow B=B+6\), hence empty or `univ` for \(q>3\) | `no_medium_tight_4interval` |
| Two heavy fibres cannot be \(T\)-adjacent | `heavy_fibres_T_free` |
| \(\{\pm1,\ldots,\pm d\}\)-difference-free packing | `T_diffFree_bound` |
| Parabola is Sidon in odd characteristic | `parabola_is_sidon` |
| Lift: red-independent product projects and \(\lvert I\rvert\le\ell\cdot\lvert\pi_R(I)\rvert\) | `lift_lemma` |
| Every-open-edge \(\Rightarrow\) triangle-free | `open_graph_triangle_free` |
| \(\alpha(G')\le\alpha(H)\) for \(H\le G'\) | `alpha_open_subgraph` |
| Strict mixing empties a fibre | `strictly_mixing_fibre` |
| Shifted fibres are disjoint after \(2t(t-s)\) | `shifted_fibres_disjoint` |
| Unsigned parabola codegree \(\le 1\) | `parabola_diff_unique` |
| Popular core carries half the energy | `popular_core_half_energy` |
| Affine image of `{1,…,d}` packs like the interval | `affine_interval_pack` |

Not formalized (still paper-only / conjectural): medium-fibre star
clustering, half-intersection, the Weyl estimate for approximate cylinders,
the intermediate-energy window, medium-star incidences, and the SOTA
independence-number bound for \(A_q\). See [`inverse-energy.tex`](../inverse-energy.tex).

## Build

```bash
# once: install elan, then
cd lean
lake exe cache get   # mathlib oleans
lake build
```

Or from the repo root: `./scripts/setup-lean.sh`.

CI runs the same `lake build` via `leanprover/lean-action` on the `lean/`
package directory.
