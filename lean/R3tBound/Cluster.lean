/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import R3tBound.Heavy
import R3tBound.Mixing
import R3tBound.Sidon

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

lemma card_inter_add_card_inter_le {α : Type*} [DecidableEq α]
    {A B V : Finset α} (h : Disjoint A B) :
    #(A ∩ V) + #(B ∩ V) ≤ #V := by
  have hdisj : Disjoint (A ∩ V) (B ∩ V) :=
    h.mono inf_le_left inf_le_left
  have hsub : A ∩ V ∪ B ∩ V ⊆ V := by
    intro x hx
    rcases mem_union.1 hx with hx | hx
    · exact (mem_inter.1 hx).2
    · exact (mem_inter.1 hx).2
  calc
    #(A ∩ V) + #(B ∩ V) = #(A ∩ V ∪ B ∩ V) := (card_union_of_disjoint hdisj).symm
    _ ≤ #V := card_le_card hsub

/-- Exact equal fibres forbid the quadratic translate. -/
lemma exact_cylinder_shift {T : Finset (ZMod q)}
    {A : Finset (ZMod q × ZMod q)} {x s t : ZMod q} {U : Finset (ZMod q)}
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q)))
    (hT0 : 0 ∉ T) (hdiff : s - t ∈ T)
    (hs : shiftedFibre A x s = U) (ht : shiftedFibre A x t = U) :
    Disjoint U (U.image (fun y => y + 2 * t * (t - s))) := by
  simpa [hs, ht] using shifted_independent (A := A) (x := x) (s := s) (t := t) hA hT0 hdiff

/-- Close fibres that miss a shift have almost-disjoint self-translates. -/
lemma close_sets_almost_disjoint_translates
    {A B : Finset (ZMod q)} {σ : ZMod q}
    (hdisj : Disjoint A (B.image (fun y => y + σ))) :
    #(A ∩ A.image (fun y => y + σ)) ≤ #(A \ B) := by
  classical
  have hsub : A ∩ A.image (fun y => y + σ) ⊆
      (A.image (fun y => y + σ) \ B.image (fun y => y + σ)) := by
    intro y hy
    refine mem_sdiff.2 ⟨(mem_inter.1 hy).2, ?_⟩
    intro hyB
    exact disjoint_left.1 hdisj (mem_inter.1 hy).1 hyB
  have himage :
      A.image (fun y => y + σ) \ B.image (fun y => y + σ) =
        (A \ B).image (fun y => y + σ) := by
    ext y
    simp only [mem_sdiff, mem_image]
    constructor
    · intro ⟨⟨z, hzA, hz⟩, hnot⟩
      refine ⟨z, ⟨hzA, ?_⟩, hz⟩
      intro hzB
      exact hnot ⟨z, hzB, hz⟩
    · intro ⟨z, ⟨hzA, hzB⟩, hz⟩
      refine ⟨⟨z, hzA, hz⟩, ?_⟩
      intro ⟨w, hwB, hw⟩
      have : z = w := add_left_injective σ (hz.trans hw.symm)
      exact hzB (this ▸ hwB)
  have hcard : #(A.image (fun y => y + σ) \ B.image (fun y => y + σ)) = #(A \ B) := by
    rw [himage, card_image_add]
  exact (card_le_card hsub).trans_eq hcard

/-- An affine image of a short interval of forbidden differences packs like
the unscaled interval packing. -/
theorem affine_diffFree_card_le {U : Finset (ZMod q)} {c : ZMod q} {d : ℕ}
    (hc : c ≠ 0) (hd : 0 < d) (hdq : d + 1 ≤ q)
    (hU : ∀ t : ℕ, 1 ≤ t → t ≤ d →
      ∀ x ∈ U, ∀ y ∈ U, y ≠ x + c * (t : ZMod q)) :
    #U * (d + 1) ≤ q := by
  classical
  let S := U.image fun y => c⁻¹ * y
  have hcard : #S = #U :=
    card_image_of_injective _ (mul_right_injective₀ (inv_ne_zero hc))
  have hS : ∀ ⦃x y : ZMod q⦄, x ∈ S → y ∈ S → x ≠ y →
      ∀ t : ℕ, 1 ≤ t → t ≤ d → y ≠ x + (t : ZMod q) := by
    intro x y hx hy hxy t ht1 htd hdiff
    obtain ⟨x0, hx0, rfl⟩ := mem_image.1 hx
    obtain ⟨y0, hy0, rfl⟩ := mem_image.1 hy
    have hne : y0 ≠ x0 + c * (t : ZMod q) :=
      hU t ht1 htd x0 hx0 y0 hy0
    have : y0 = x0 + c * (t : ZMod q) := by
      have hmul := congrArg (fun z => c * z) hdiff
      have hcinv : c * (c⁻¹ * y0) = y0 := by
        rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      have hcinvx : c * (c⁻¹ * x0) = x0 := by
        rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      calc
        y0 = c * (c⁻¹ * y0) := hcinv.symm
        _ = c * (c⁻¹ * x0 + (t : ZMod q)) := by rw [hmul]
        _ = c * (c⁻¹ * x0) + c * (t : ZMod q) := by ring
        _ = x0 + c * (t : ZMod q) := by rw [hcinvx]
    exact hne this
  have := diffFree_card_le (S := S) hd hdq hS
  simpa [hcard] using this

/-- An exact cylinder over an interval of `T`-steps is affine-difference-free,
hence packs by the interval lemma. -/
theorem exact_cylinder_pack
    {T : Finset (ZMod q)} {A : Finset (ZMod q × ZMod q)}
    {x t : ZMod q} {U : Finset (ZMod q)} {d' : ℕ}
    (hq : Odd q) (ht : t ≠ 0)
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q)))
    (hT0 : 0 ∉ T)
    (hd : 0 < d') (hdq : d' + 1 ≤ q)
    (hfib : ∀ k : ℕ, k ≤ d' → shiftedFibre A x (t + (k : ZMod q)) = U)
    (hT : ∀ k : ℕ, 1 ≤ k → k ≤ d' → (k : ZMod q) ∈ T) :
    #U * (d' + 1) ≤ q := by
  have hc : (-2 * t : ZMod q) ≠ 0 := by
    intro h
    have h2t : (2 : ZMod q) * t = 0 := by
      have : -((2 : ZMod q) * t) = 0 := by
        simpa [neg_mul] using h
      exact neg_eq_zero.mp this
    rcases (mul_eq_zero.mp h2t) with h2 | ht'
    · exact two_ne_zero hq h2
    · exact ht ht'
  refine affine_diffFree_card_le (U := U) (c := (-2 : ZMod q) * t) (d := d')
    hc hd hdq ?_
  intro k hk1 hkd a ha b hb heq
  have hkt : (k : ZMod q) ∈ T := hT k hk1 hkd
  have htU : shiftedFibre A x t = U := by
    simpa using hfib 0 (Nat.zero_le _)
  have hsU : shiftedFibre A x (t + (k : ZMod q)) = U := hfib k hkd
  have hdiff : (t + (k : ZMod q)) - t ∈ T := by
    simpa [add_sub_cancel_left] using hkt
  have hdisj :=
    exact_cylinder_shift (A := A) (x := x) (s := t + (k : ZMod q)) (t := t)
      (U := U) hA hT0 hdiff hsU htU
  have himg :
      b ∈ U.image (fun y => y + 2 * t * (t - (t + (k : ZMod q)))) := by
    refine mem_image.2 ⟨a, ha, ?_⟩
    have hσ :
        2 * t * (t - (t + (k : ZMod q))) = (-2 : ZMod q) * t * (k : ZMod q) := by
      ring
    rw [hσ]
    exact heq.symm
  exact disjoint_left.1 hdisj hb himg

end R3tBound
