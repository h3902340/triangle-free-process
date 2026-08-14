/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import R3tBound.Mixing

/-!
# Shifted-fibre independence

Independence of two neighbouring fibres is disjointness of the
parabolically shifted sets after the quadratic increment `2t(t-s)`.
-/

namespace R3tBound

open Finset

variable {q : ℕ} [Fact q.Prime]

set_option linter.unusedSectionVars false

/-- Independence of two shifted fibres is disjointness after the quadratic shift. -/
lemma shifted_independent {T : Finset (ZMod q)}
    {A : Finset (ZMod q × ZMod q)} {x s t : ZMod q}
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q)))
    (hT0 : 0 ∉ T) (hdiff : s - t ∈ T) :
    Disjoint (shiftedFibre A x s)
      ((shiftedFibre A x t).image (fun y => y + 2 * t * (t - s))) := by
  refine disjoint_left.2 ?_
  intro y hys hyt
  rcases mem_image.1 hyt with ⟨z, hz, hzσ⟩
  have hs : (x + s, y + s ^ 2) ∈ A := mem_shiftedFibre.1 hys
  have ht : (x + t, z + t ^ 2) ∈ A := mem_shiftedFibre.1 hz
  have hne : ((x + s, y + s ^ 2) : ZMod q × ZMod q) ≠ (x + t, z + t ^ 2) := by
    intro h
    have : s = t := by simpa using congrArg Prod.fst h
    exact t_ne_zero_of_mem hT0 hdiff (by simp [this])
  have hdiff' : (x + s, y + s ^ 2) - (x + t, z + t ^ 2) = (s - t, (s - t) ^ 2) := by
    apply Prod.ext
    · simp
    · have hy : y = z + 2 * t * (t - s) := hzσ.symm
      have : y + s ^ 2 - (z + t ^ 2) = (s - t) ^ 2 := by
        calc
          y + s ^ 2 - (z + t ^ 2)
              = (z + 2 * t * (t - s) + s ^ 2) - (z + t ^ 2) := by rw [hy]
          _ = 2 * t * (t - s) + s ^ 2 - t ^ 2 := by abel
          _ = (s - t) ^ 2 := by ring
      simpa using this
  have hmem : (s - t, (s - t) ^ 2) ∈ signedParabola T :=
    (mem_signedParabola (T := T) (p := (s - t, (s - t) ^ 2))).2
      (Or.inl ⟨s - t, hdiff, rfl⟩)
  exact hA hs ht hne (by simpa [hdiff'] using hmem)

end R3tBound
