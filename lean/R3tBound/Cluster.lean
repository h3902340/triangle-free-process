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

lemma card_inter_image_add (B V : Finset (ZMod q)) (σ : ZMod q) :
    #(B.image (fun y => y + σ) ∩ V.image (fun y => y + σ)) = #(B ∩ V) := by
  rw [← image_inter B V (add_left_injective σ), card_image_add]

/-- If `|U| ≤ q/2`, the random overlap `|U|²/q` is at most `|U|/2`.
Half-intersection therefore does not beat the random prediction on
non-heavy cores. -/
lemma random_overlap_le_half {U : Finset (ZMod q)}
    (h : 2 * #U ≤ q) : 2 * #U ^ 2 ≤ q * #U := by
  have := Nat.mul_le_mul_right (#U) h
  convert this using 1
  ring

/-- Two sets that are `3/4`-dense in `U` and miss a shift force
`|U ∩ (U+σ)| ≤ |U|/2`. -/
theorem half_intersection {U A B : Finset (ZMod q)} {σ : ZMod q}
    (hA : 3 * #U ≤ 4 * #(A ∩ U))
    (hB : 3 * #U ≤ 4 * #(B ∩ U))
    (hdisj : Disjoint A (B.image (fun y => y + σ))) :
    2 * #(U ∩ U.image (fun y => y + σ)) ≤ #U := by
  classical
  set V := U ∩ U.image (fun y => y + σ)
  set Bσ := B.image (fun y => y + σ)
  have hAV : #(A ∩ U) + #V ≤ #U + #(A ∩ V) := by
    have hunion : A ∩ U ∪ V ⊆ U := by
      intro y hy
      rcases mem_union.1 hy with hy | hy
      · exact (mem_inter.1 hy).2
      · exact (mem_inter.1 hy).1
    have : #(A ∩ U ∪ V) ≤ #U := card_le_card hunion
    have hcard := card_union_add_card_inter (A ∩ U) V
    have hinter : A ∩ U ∩ V = A ∩ V := by
      ext y
      simp [V, and_comm, and_left_comm]
    have : #(A ∩ U) + #V = #(A ∩ U ∪ V) + #(A ∩ V) := by
      simpa [hinter] using hcard.symm
    omega
  have hBV : #(B ∩ U) + #V ≤ #U + #(Bσ ∩ V) := by
    have hUσ : #(U.image (fun y => y + σ)) = #U := card_image_add U σ
    have hBσUσ : #(Bσ ∩ U.image (fun y => y + σ)) = #(B ∩ U) := by
      simpa [Bσ] using card_inter_image_add B U σ
    have hunion : Bσ ∩ U.image (fun y => y + σ) ∪ V ⊆ U.image (fun y => y + σ) := by
      intro y hy
      rcases mem_union.1 hy with hy | hy
      · exact (mem_inter.1 hy).2
      · exact (mem_inter.1 hy).2
    have : #(Bσ ∩ U.image (fun y => y + σ) ∪ V) ≤ #U := by
      simpa [hUσ] using card_le_card hunion
    have hcard := card_union_add_card_inter (Bσ ∩ U.image (fun y => y + σ)) V
    have hinter : Bσ ∩ U.image (fun y => y + σ) ∩ V = Bσ ∩ V := by
      ext y
      simp [V, Bσ, and_comm, and_left_comm]
    have : #(B ∩ U) + #V = #(Bσ ∩ U.image (fun y => y + σ) ∪ V) + #(Bσ ∩ V) := by
      rw [← hBσUσ]
      simpa [hinter] using hcard.symm
    omega
  have hsum : #(A ∩ V) + #(Bσ ∩ V) ≤ #V :=
    card_inter_add_card_inter_le hdisj
  have : #(A ∩ U) + #(B ∩ U) + #V ≤ 2 * #U := by
    omega
  have h34 : 3 * #U + 3 * #U ≤ 4 * #(A ∩ U) + 4 * #(B ∩ U) :=
    Nat.add_le_add hA hB
  have : 4 * #V ≤ 2 * #U := by
    omega
  omega

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

/-- Independence of neighbouring fibres bounds the self-translate overlap
by the fringe. This is one pair, not a packing of the star. -/
lemma shifted_close_overlap {T : Finset (ZMod q)}
    {A : Finset (ZMod q × ZMod q)} {x s t : ZMod q}
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q)))
    (hT0 : 0 ∉ T) (hdiff : s - t ∈ T) :
    #(shiftedFibre A x s ∩
        (shiftedFibre A x s).image (fun y => y + 2 * t * (t - s))) ≤
      #(shiftedFibre A x s \ shiftedFibre A x t) :=
  close_sets_almost_disjoint_translates
    (shifted_independent (A := A) (x := x) (s := s) (t := t) hA hT0 hdiff)

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

/-- An exact cylinder whose support is an arithmetic progression of `T`-steps
is affine-difference-free, hence packs by the interval lemma. -/
theorem exact_cylinder_pack_ap
    {T : Finset (ZMod q)} {A : Finset (ZMod q × ZMod q)}
    {x t a : ZMod q} {U : Finset (ZMod q)} {d' : ℕ}
    (hq : Odd q) (ht : t ≠ 0) (ha : a ≠ 0)
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q)))
    (hT0 : 0 ∉ T)
    (hd : 0 < d') (hdq : d' + 1 ≤ q)
    (hfib : ∀ k : ℕ, k ≤ d' → shiftedFibre A x (t + a * (k : ZMod q)) = U)
    (hT : ∀ k : ℕ, 1 ≤ k → k ≤ d' → a * (k : ZMod q) ∈ T) :
    #U * (d' + 1) ≤ q := by
  have hc : ((-2 : ZMod q) * t * a) ≠ 0 := by
    intro h
    have h2 : (2 : ZMod q) ≠ 0 := two_ne_zero hq
    have h2t : (2 : ZMod q) * t ≠ 0 := mul_ne_zero h2 ht
    have hneg : (-((2 : ZMod q) * t)) ≠ 0 := neg_ne_zero.mpr h2t
    have : (-((2 : ZMod q) * t)) * a = 0 := by
      simpa [neg_mul, mul_assoc] using h
    rcases mul_eq_zero.mp this with hneg' | ha'
    · exact hneg hneg'
    · exact ha ha'
  refine affine_diffFree_card_le (U := U) (c := (-2 : ZMod q) * t * a) (d := d')
    hc hd hdq ?_
  intro k hk1 hkd y hy z hz heq
  have hkt : a * (k : ZMod q) ∈ T := hT k hk1 hkd
  have htU : shiftedFibre A x t = U := by
    simpa using hfib 0 (Nat.zero_le _)
  have hsU : shiftedFibre A x (t + a * (k : ZMod q)) = U := hfib k hkd
  have hdiff : (t + a * (k : ZMod q)) - t ∈ T := by
    simpa [add_sub_cancel_left] using hkt
  have hdisj :=
    exact_cylinder_shift (A := A) (x := x) (s := t + a * (k : ZMod q)) (t := t)
      (U := U) hA hT0 hdiff hsU htU
  have himg :
      z ∈ U.image (fun w => w + 2 * t * (t - (t + a * (k : ZMod q)))) := by
    refine mem_image.2 ⟨y, hy, ?_⟩
    have hσ :
        2 * t * (t - (t + a * (k : ZMod q))) =
          (-2 : ZMod q) * t * a * (k : ZMod q) := by
      ring
    rw [hσ]
    exact heq.symm
  exact disjoint_left.1 hdisj hz himg

/-- Special case: common difference `1`. -/
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
  have ha : (1 : ZMod q) ≠ 0 := one_ne_zero
  refine exact_cylinder_pack_ap (x := x) (a := (1 : ZMod q)) hq ht ha hA hT0 hd hdq ?_ ?_
  · intro k hk
    simpa using hfib k hk
  · intro k hk1 hkd
    simpa using hT k hk1 hkd

end R3tBound
