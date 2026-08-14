/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
the pairwise energy identity, and one heavy off-diagonal pair are verified.
One independent pair has an almost-disjoint self-translate; that is not a
packing of the star.
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
off-diagonal intersection larger than `B`. Not an `Ω(|T|²)` star count. -/
alias exists_heavy_pair := exists_heavy_off_diag_pair

/-- **Close fibres.** If `A` misses `B+σ` then `|A ∩ (A+σ)| ≤ |A \ B|`. -/
alias close_fibres_almost_disjoint := close_sets_almost_disjoint_translates

/-- **Shifted close overlap.** Independence of neighbouring fibres bounds
the self-translate by the fringe. One pair, not a packing. -/
alias shifted_close_pair := shifted_close_overlap

end R3tBound
