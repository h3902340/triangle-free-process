/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import R3tBound.Autocorr
import R3tBound.Cleanup
import R3tBound.Cluster
import R3tBound.Heavy
import R3tBound.Incidences
import R3tBound.Lift
import R3tBound.Mixing
import R3tBound.Sidon
import R3tBound.TightInterval

/-!
# Verified core of Family A

These are the lemmas from the paper that have complete Lean proofs.
The SOTA independence-number bound for `A_q` is *not* claimed here.
Medium-fibre clustering is a structure theorem, not a size bound:
half-intersection does not beat the random overlap on non-heavy cores.
The Weyl estimate for approximate cylinders remains paper-only.
Popular-core energy, three-quarters energy, half-intersection, almost-mixing,
affine interval packing, exact-cylinder packing (including AP supports),
the pairwise energy identity, one heavy off-diagonal pair, maximal-energy
exact cylinders, the two-thirds energy core, and the empty intermediate
window at mean size `q/3`, and `|intervalT q d| = d` are verified.
On a `T`-dense fibre the heavy-pair graph orients as `(max, min)`, so
some out-neighbourhood is interval-dense (item (2) of the packing path;
paper, using `card_intervalT`). Those high-vertex lags are quadratic
and are not an input to `pack_window`. Two-thirds energy on medium
fibres forces `Ω(|T|²)` heavy pairs and a star of degree `|T|/9`
(`card_heavy_pair_set`, `exists_heavy_star`); that is structure, not
a size bound. A complete *affine* interval of uniformly below-random
lags packs by the second-moment identity (`pack_window`). A
`3/4`-close *in-star* whose high neighbours contain an AP of
`T`-steps of length `L` is such an interval
(`pack_quarter_in_star_ap`; difference `1` is
`pack_quarter_in_star`). In-neighbours of `t = i+1` in `{1,…,d}`
are exactly `{i+2,…,d}` (`intervalT_in_mem`). High-vertex
out-neighbourhoods, AP-poor spread-out neighbourhoods (Weyl), and
average-only / `K = 2` discrepancy remain paper-only.
-/

namespace R3tBound

/-- **Fibre constraint.** A seed-independent set cannot contain both
`(x, y)` and `(x + t, y + t²)` for `t ∈ T`. -/
alias fibre_constraint_empty := fibre_constraint

/-- **Tight 4-interval.** A proper nonempty fibre cannot sit in a tight
4-interval when `q > 3`. -/
alias no_medium_tight_4interval := no_tight_4interval_of_proper

/-- **Heavy fibres.** Two heavy fibres cannot be at distance `t ∈ T`. -/
alias heavy_fibres_T_free := heavy_not_adjacent

/-- **Cycle packing.** A `{±1,…,±d}`-difference-free subset of `𝔽_q` has
size at most `q/(d+1)`. -/
alias T_diffFree_bound := diffFree_card_le

/-- **Sidon.** The parabola is a Sidon set in odd characteristic. -/
alias parabola_is_sidon := parabola_sidon

/-- **Lift.** A red-independent product set projects to a seed-independent
set and has size at most `ℓ` times the projection. -/
alias lift_lemma := lift_card

/-- **Open edges.** A graph whose every edge is open is triangle-free. -/
alias open_graph_triangle_free := openEdges_cliqueFree

/-- **Cleanup monotonicity.** `α(A_q) ≤ α(H)` when `H` is a subgraph of the
cleaned graph. -/
alias alpha_open_subgraph := alpha_le_of_open_subgraph

/-- **Strict mixing.** Energy at most random and neighbouring mass `≥ q`
force an empty fibre. -/
alias strictly_mixing_fibre := strict_mixing_empty

/-- **Shifted independence.** Neighbouring fibres are disjoint after the
quadratic increment `2t(t-s)`. -/
alias shifted_fibres_disjoint := shifted_independent

/-- **Unsigned codegree.** A nonzero difference has at most one
representation as a difference of unsigned parabola points. -/
alias parabola_diff_unique := parabola_codegree

/-- **Popular core.** The high-multiplicity set carries at least half
the fibre energy. -/
alias popular_core_half_energy := popular_core_energy

/-- **Affine packing.** Forbidden differences along an affine image of
`{1,…,d}` pack like the unscaled interval. -/
alias affine_interval_pack := affine_diffFree_card_le

/-- **Three-quarters energy.** Energy at least `3/4` of `#T · W` puts a
quarter of the energy on points of multiplicity `#T / 2`. -/
alias three_quarters_energy := three_quarters_energy_core

/-- **Exact cylinder packing.** Equal fibres along an interval of `T`-steps
have size at most `q/(d'+1)`. -/
alias exact_cylinder_interval_pack := exact_cylinder_pack

/-- **AP-support exact cylinders.** Equal fibres along an arithmetic
progression of `T`-steps pack the same way. -/
alias exact_cylinder_ap_pack := exact_cylinder_pack_ap

/-- **Half-intersection.** Two `3/4`-dense subsets that miss a shift force
`|U ∩ (U+σ)| ≤ |U|/2`. -/
alias half_intersection_bound := half_intersection

/-- **High-multiplicity core size.** The core has size at most `4E / #T²`. -/
alias high_multiplicity_core_size := high_multiplicity_core_card

/-- **Almost mixing.** Energy at most `K` times random bounds the fibre
by `q(1-1/K)`. -/
alias almost_mixing_fibre := almost_mixing_fibre_card

/-- **Random overlap.** If `|U| ≤ q/2` then `|U|²/q ≤ |U|/2`. -/
alias random_overlap_at_most_half := random_overlap_le_half

/-- **Pairwise energy.** Energy equals the sum of pairwise shifted-fibre
intersections. -/
alias family_energy_pairwise := familyEnergy_eq_pairwise

/-- **Off-diagonal energy.** Energy is neighbouring mass plus off-diagonal
intersections. -/
alias family_energy_off_diag := familyEnergy_off_diag

/-- **One heavy pair.** Energy above `W + B·#T·(#T-1)` forces an
off-diagonal intersection larger than `B`. -/
alias exists_heavy_pair := exists_heavy_off_diag_pair

/-- **Many heavy pairs.** Two-thirds energy on mean size `≥ q/3` with
fibres at most `q/2` forces `#T² / 9` heavy ordered pairs. Structure,
not a size bound. -/
alias many_heavy_pairs := card_heavy_pair_set

/-- **Heavy star.** A vertex of heavy-pair degree at least `#T / 9`. -/
alias exists_heavy_star_vertex := exists_heavy_star

/-- **Medium aligned star.** Medium aligned fibres have a heavy star.
Structure, not a size bound. -/
alias medium_aligned_star := aligned_medium_has_star

/-- **Close fibres.** If `A` misses `B+σ` then `|A ∩ (A+σ)| ≤ |A \ B|`. -/
alias close_fibres_almost_disjoint := close_sets_almost_disjoint_translates

/-- **Shifted close overlap.** Independence of neighbouring fibres bounds
the self-translate by the fringe. One pair, not a packing. -/
alias shifted_close_pair := shifted_close_overlap

/-- **Maximal energy.** Energy `#T · W` makes every nonempty shifted fibre
equal. -/
alias maximal_energy_is_exact := maximal_energy_exact_cylinder

/-- **No half-size alignment.** Fibres of size at least `q/2` cannot be
strictly aligned. -/
alias no_half_size_alignment := no_aligned_of_half_fibres

/-- **Two-thirds energy.** Energy `2 #T W / 3` puts a quarter of the
energy on multiplicity `#T / 2`. -/
alias two_thirds_energy := two_thirds_energy_core

/-- **Empty intermediate window at `3q/8`.** Mean size `≥ 3q/8` and
alignment force three-quarters energy. -/
alias aligned_is_three_quarters := aligned_implies_three_quarters

/-- **Empty intermediate window at `q/3`.** Mean size `≥ q/3` and
alignment force two-thirds energy. -/
alias aligned_is_two_thirds := aligned_implies_two_thirds

/-- **Medium aligned core.** Medium aligned fibres have a
high-multiplicity core. Structure, not a size bound. -/
alias medium_aligned_core := aligned_medium_has_core

/-- **Half-size exact.** Twice-random equality on half-size fibres is an
exact cylinder. -/
alias half_fibre_is_exact := half_fibre_energy_exact_cylinder

/-- **Interval differences.** Distinct points of `{1,…,d}` differ by an
element of `±T` when `2d ≤ q`. -/
alias interval_T_pair_diff := intervalT_pair_diff

/-- **Heavy pair on an interval.** A heavy pair in Family A is
`T`-adjacent and supplies one almost-disjoint translate. -/
alias heavy_pair_on_interval := heavy_pair_interval_overlap

/-- **Total fringe.** Off-diagonal symmetric difference sums to
`#T · W - E`. -/
alias total_fringe := sum_sdiff_off_diag

/-- **Star self-overlap.** Summed self-translates are at most the
star fringe. -/
alias star_overlap_sum := star_self_overlap_sum

/-- **Below-random star.** Large star intersections force self-translates
at most random on average. Discrepancy, not a packing. -/
alias star_overlap_below_random := star_overlap_le_random

/-- **Interval support.** Family A's `T = {1,…,d}` has size `d`. -/
alias interval_T_card := card_intervalT

/-- **Interval support bound.** A subset of `{1,…,d}` has size at most
`d` when `d < q`. -/
alias interval_T_card_le := card_le_intervalT

/-- **Oriented out-neighbourhood.** Out-neighbours of `s = i+1` in
`{1,…,d}` are exactly `{1,…,i}`. -/
alias interval_T_out := intervalT_out_mem

/-- **Oriented star sits in an interval.** A set of out-neighbours of
`s = i+1` has size at most `i`. -/
alias interval_T_out_card := card_intervalT_out

/-- **Oriented star bound.** Any out-neighbourhood of `s = i+1` has
size at most `i`. -/
alias interval_T_out_card_le := card_le_intervalT_out

/-- **Oriented in-neighbourhood.** In-neighbours of `t = i+1` in
`{1,…,d}` are exactly `{i+2,…,d}`. -/
alias interval_T_in := intervalT_in_mem

/-- **Oriented in-star sits in an interval.** A set of in-neighbours
of `t = i+1` has size at most `d-i-1`. -/
alias interval_T_in_card := card_intervalT_in

/-- **Oriented in-star bound.** Any in-neighbourhood of `t = i+1`
has size at most `d-i-1`. -/
alias interval_T_in_card_le := card_le_intervalT_in

/-- **Weighted lag sum.** `2 ∑_{t<L} (L-t) = L(L+1)`. -/
alias weighted_lag_sum := sum_range_weighted

/-- **Second-moment packing.** Uniformly below-random lags on a complete
interval give `|U| · (L + c + 1) ≤ (c + 1) q`. Not a packing of
average-only or spread-out neighbourhoods. -/
alias second_moment_pack := pack_of_second_moment

/-- **Two-thirds second-moment packing.** The case `c = 2`:
`r ≤ (2/3) |U|²/q` on every lag yields `|U|(L+3) ≤ 3q`. -/
alias second_moment_pack_two_thirds := pack_of_second_moment_two_thirds

/-- **Window first moment.** Occupancy sums to `(L+1)|U|`. -/
alias window_first_moment := sum_windowCount

/-- **Window second moment.** Occupancy energy expands as a weighted
lag sum of autocorrelations. -/
alias window_energy := window_second_moment

/-- **Window packing.** Uniformly below-random lags on a complete
interval give `|U|(L+c+1) ≤ (c+1)q`, from the window identity and
Cauchy--Schwarz. -/
alias window_pack := pack_window

/-- **Two-thirds window packing.** The case `c = 2` of `pack_window`. -/
alias window_pack_two_thirds := pack_window_two_thirds

/-- **Low-fibre affine overlap.** Independence `s - t ∈ T` bounds the
self-translate of the *lower* fibre by the affine shift `2t(s-t)`.
This is the orientation that feeds interval packing. -/
alias low_fibre_affine_overlap := shifted_close_overlap_low

/-- **Quarter-close in-star packing.** A `3/4`-close in-star whose
high neighbours contain `{t+1,…,t+L}` and whose base fibre has size
at least `q/3` packs: `|A_t|(L+4) ≤ 4q`. High-vertex
out-neighbourhoods produce quadratic lags and are not this lemma. -/
alias quarter_in_star_pack := pack_quarter_in_star

/-- **Quarter-close AP in-star packing.** The same size bound when
the high neighbours contain `{t+step,…,t+L·step}`. -/
alias quarter_in_star_ap_pack := pack_quarter_in_star_ap

end R3tBound
