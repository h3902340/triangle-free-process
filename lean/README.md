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
| Signed parabola codegree \(\le 6\) | `signed_parabola_codegree` |
| Sidon CS: \(\sum_u D(u)^2\le|S_R||P|+6|P|(|P|-1)\) | `seed_sidon_second_moment` |
| Popular core carries half the energy | `popular_core_half_energy` |
| Affine image of `{1,…,d}` packs like the interval | `affine_interval_pack` |
| Three-quarters energy sits on multiplicity `#T/2` | `three_quarters_energy` |
| Exact cylinder over a `T`-interval packs | `exact_cylinder_interval_pack` |
| Exact cylinder over an AP of `T`-steps packs | `exact_cylinder_ap_pack` |
| Half-intersection for `3/4`-dense subsets | `half_intersection_bound` |
| High-multiplicity core has size `≤ 4E/#T²` | `high_multiplicity_core_size` |
| Almost-mixing fibre bound `q(1-1/K)` | `almost_mixing_fibre` |
| Random overlap `≤ |U|/2` when `|U|≤q/2` | `random_overlap_at_most_half` |
| Energy is the sum of pairwise intersections | `family_energy_pairwise` |
| Energy is mass plus off-diagonal intersections | `family_energy_off_diag` |
| Energy above `W+B·#T·(#T-1)` forces one heavy pair | `exists_heavy_pair` |
| Two-thirds energy on medium fibres ⇒ `#T²/9` heavy pairs | `many_heavy_pairs` |
| A vertex of heavy-pair degree `#T/9` | `exists_heavy_star_vertex` |
| Medium aligned fibres have a heavy star | `medium_aligned_star` |
| `A` misses `B+σ` \(\Rightarrow\) `|A∩(A+σ)|≤|A\B|` | `close_fibres_almost_disjoint` |
| Neighbouring independence bounds one self-translate | `shifted_close_pair` |
| Maximal energy makes every nonempty fibre equal | `maximal_energy_is_exact` |
| Fibres of size `≥ q/2` are not strictly aligned | `no_half_size_alignment` |
| Two-thirds of max energy produces the high-multiplicity core | `two_thirds_energy` |
| Mean size `≥ q/3` and alignment ⇒ two-thirds energy | `aligned_is_two_thirds` |
| Medium aligned fibres have a high-multiplicity core | `medium_aligned_core` |
| Mean size `≥ 3q/8` and alignment ⇒ three-quarters energy | `aligned_is_three_quarters` |
| Twice-random equality on half-size fibres is exact | `half_fibre_is_exact` |
| Distinct points of `{1,…,d}` differ by `±T` | `interval_T_pair_diff` |
| A heavy pair on `{1,…,d}` is one almost-disjoint translate | `heavy_pair_on_interval` |
| Off-diagonal fringe sums to `#T·W - E` | `total_fringe` |
| Star self-translates sum to at most the fringe | `star_overlap_sum` |
| Large star intersections ⇒ self-translates ≤ random | `star_overlap_below_random` |
| Family A's `T = {1,…,d}` has size `d` | `interval_T_card` |
| Out-neighbours of `s = i+1` are `{1,…,i}` | `interval_T_out` |
| An out-neighbourhood of `s = i+1` has size `≤ i` | `interval_T_out_card_le` |
| In-neighbours of `t = i+1` are `{i+2,…,d}` | `interval_T_in` |
| An in-neighbourhood of `t = i+1` has size `≤ d-i-1` | `interval_T_in_card_le` |
| Weighted lag sum `2 ∑_{t<L}(L-t)=L(L+1)` | `weighted_lag_sum` |
| Uniform below-random lags on a complete interval pack | `second_moment_pack` |
| The case `c=2`: `r ≤ (2/3)|U|²/q` yields `|U|(L+3)≤3q` | `second_moment_pack_two_thirds` |
| Sliding-window occupancy sums to `(L+1)|U|` | `window_first_moment` |
| Window energy expands as a weighted lag sum | `window_energy` |
| Window identity + CS + uniform lags pack | `window_pack` |
| Independence bounds the lower fibre by an affine shift | `low_fibre_affine_overlap` |
| A `3/4`-close in-star on `{t+1,…,t+L}` packs | `quarter_in_star_pack` |
| A `3/4`-close in-star along any AP of $T$-steps packs | `quarter_in_star_ap_pack` |
| Light-pair first moment `2 ∑ binom(d,2) ≤ t · ∑ d` | `light_pairs_first_moment` |
| Star Markov `t · #{w : t ≤ d(w)} ≤ ∑ d` | `star_markov` |
| Seed first moment `∑ D = \|S_R\| \|P\|` | `seed_degree_sum` |
| Seed heavy-star count `t · #{u : t ≤ D(u)} ≤ \|S_R\| \|P\|` | `seed_heavy_stars` |
| Seed light pairs `2 ∑_{D≤t} binom(D,2) ≤ t \|S_R\| \|P\|` | `seed_light_pairs` |

Not formalized (still paper-only / conjectural): the Weyl estimate for
horizontal packings and for AP-poor below-random star autocorrelations,
any second moment on high-vertex quadratic \(N^+\) lags, packing of
average-only / \(K=2\) medium stars, a SOTA-scale saving on the Sidon
count (the \(O(d|P|+|P|^2)\) bound is Lean and saturates),
a SOTA-scale light-star second moment (the first-moment half of
`lem:nstars` / `lem:light` is Lean and needs `t=o(1)` at `|P|∼|S_R|`),
medium-star incidences, and the SOTA independence-number bound for
\(A_q\).
The \(\Omega(|T|^2)\) star-degree count is Lean (`many_heavy_pairs`);
it is a star, not a packing.
The intermediate window is empty at mean fibre size `≥ q/3`; it remains
open on `(q^{1/3}(\log q)^{-O(1)}, q/3)`. Medium aligned fibres all have
a high-multiplicity core; that core is not packed unless the
neighbourhood is a complete *affine* AP with a uniform lag bound
(a `3/4`-close in-star along any common difference is such an AP:
`quarter_in_star_ap_pack`).
On a `T`-dense fibre some high-vertex out-neighbourhood and some
in-neighbourhood are interval-dense (item (2); `interval_T_in`);
high-vertex lags are quadratic and are not an input to `window_pack`.
A complete affine AP of uniformly below-random lags packs
(`window_pack`); high-vertex $N^+$ and AP-poor neighbourhoods still
need Weyl or a different second moment.
One heavy pair plus one almost-disjoint translate is not a packing.
An \(\Omega(|T|^2)\) star of heavy pairs is still not a packing.
A star with large intersections has below-random self-translates; that
is a discrepancy, not a packing.
See [`inverse-energy.tex`](../inverse-energy.tex).

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
