/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import R3tBound.Basic

/-!
# Fibre constraint

A `G_R`-independent set cannot contain both `(x, y)` and `(x + t, y + t²)`
for any `t ∈ T` with `0 ∉ T`. Equivalently, neighbouring fibres are disjoint
after a parabolic shift.
-/

namespace R3tBound

variable {q : ℕ} [Fact q.Prime]

lemma t_ne_zero_of_mem {T : Finset (ZMod q)} {t : ZMod q} (hT0 : 0 ∉ T) (ht : t ∈ T) :
    t ≠ 0 :=
  fun h => hT0 (h ▸ ht)

/-- The defining fibre constraint: no parabolic chord of length `t ∈ T`. -/
lemma fibre_constraint {T : Finset (ZMod q)} {A : Set (ZMod q × ZMod q)} {x t : ZMod q}
    (hA : IsSeedIndependent T A) (hT0 : 0 ∉ T) (ht : t ∈ T) :
    fibre A (x + t) ∩ shift (fibre A x) (t ^ 2) = ∅ := by
  ext y
  simp only [Set.mem_inter_iff, mem_fibre, mem_shift, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro hyxt hyx
  have hne : ((x + t, y) : ZMod q × ZMod q) ≠ (x, y - t ^ 2) := by
    intro h
    exact t_ne_zero_of_mem hT0 ht (by simpa using congrArg Prod.fst h)
  have hdiff : (x + t, y) - (x, y - t ^ 2) = (t, t ^ 2) := by
    simp
  have hmem : (t, t ^ 2) ∈ signedParabola T :=
    (mem_signedParabola (T := T) (p := (t, t ^ 2))).2 (Or.inl ⟨t, ht, rfl⟩)
  exact hA hyxt hyx hne (by simpa [hdiff] using hmem)

end R3tBound
