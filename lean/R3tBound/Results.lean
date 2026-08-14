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
Medium-fibre clustering and the Weyl estimate for approximate cylinders
remain paper-only (`inverse-energy.tex`).
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

end R3tBound
