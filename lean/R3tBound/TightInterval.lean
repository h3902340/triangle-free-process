/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import R3tBound.Fibres

/-!
# Tight 4-intervals

Corrected form of Lemma 3 in `energy-increment.tex`: a tight 4-interval
forces the first fibre to be periodic with period 6, hence empty or the
whole field when `q > 3`.
-/

namespace R3tBound

open Finset

set_option linter.unusedSectionVars false

variable {q : ℕ} [Fact q.Prime]

def fibreF (A : Finset (ZMod q × ZMod q)) (x : ZMod q) : Finset (ZMod q) :=
  (A.filter (fun p => p.1 = x)).image Prod.snd

lemma mem_fibreF {A : Finset (ZMod q × ZMod q)} {x y : ZMod q} :
    y ∈ fibreF A x ↔ (x, y) ∈ A := by
  simp [fibreF, mem_image, mem_filter]

lemma card_image_add (B : Finset (ZMod q)) (c : ZMod q) :
    #(B.image (fun y => y + c)) = #B :=
  card_image_of_injective _ (add_left_injective c)

lemma image_add_compl (B : Finset (ZMod q)) (c : ZMod q) :
    (Bᶜ).image (fun y => y + c) = (B.image (fun y => y + c))ᶜ := by
  ext y
  constructor
  · intro hy
    rcases mem_image.1 hy with ⟨z, hz, rfl⟩
    rw [mem_compl, mem_image]
    rintro ⟨w, hw, heq⟩
    have : z = w := (add_right_cancel heq).symm
    exact (mem_compl.1 hz) (this ▸ hw)
  · intro hy
    refine mem_image.2 ⟨y - c, ?_, sub_add_cancel y c⟩
    rw [mem_compl]
    intro hz
    exact mem_compl.1 hy (mem_image.2 ⟨y - c, hz, sub_add_cancel y c⟩)

lemma image_add_add (B : Finset (ZMod q)) (c d : ZMod q) :
    (B.image (fun y => y + c)).image (fun y => y + d) =
      B.image (fun y => y + (c + d)) := by
  simp [image_image]

lemma image_add_neg (B : Finset (ZMod q)) (c : ZMod q) :
    (B.image (fun y => y + c)).image (fun y => y + -c) = B := by
  simp [image_image]

lemma double_compl_shift (B : Finset (ZMod q)) (c d : ZMod q) :
    (((B.image (fun y => y + c))ᶜ).image (fun y => y + d))ᶜ =
      B.image (fun y => y + (c + d)) := by
  rw [← image_add_compl, compl_compl, image_add_add]

lemma fibreF_inter_shift {T : Finset (ZMod q)} {A : Finset (ZMod q × ZMod q)}
    {x t : ZMod q}
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q)))
    (hT0 : 0 ∉ T) (ht : t ∈ T) :
    fibreF A (x + t) ∩ (fibreF A x).image (fun y => y + t ^ 2) = ∅ := by
  apply eq_empty_of_forall_notMem
  intro y hy
  rcases mem_inter.1 hy with ⟨hyL, hyR⟩
  rcases mem_image.1 hyR with ⟨z, hz, rfl⟩
  have hin :
      (z + t ^ 2) ∈ fibre (A : Set (ZMod q × ZMod q)) (x + t) ∩
        shift (fibre (A : Set (ZMod q × ZMod q)) x) (t ^ 2) := by
    refine ⟨mem_fibre.2 (mem_fibreF.1 hyL), ?_⟩
    exact (mem_shift (B := fibre (A : Set (ZMod q × ZMod q)) x)
      (c := t ^ 2) (y := z + t ^ 2)).2
      (by simpa [mem_fibre, add_sub_cancel_right] using (mem_fibreF.1 hz))
  have hempty := fibre_constraint (A := (A : Set (ZMod q × ZMod q)))
    (x := x) (t := t) hA hT0 ht
  exact (Set.eq_empty_iff_forall_notMem.1 hempty) _ hin

lemma fibreF_card_add_le {T : Finset (ZMod q)} {A : Finset (ZMod q × ZMod q)}
    {x t : ZMod q}
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q)))
    (hT0 : 0 ∉ T) (ht : t ∈ T) :
    #(fibreF A x) + #(fibreF A (x + t)) ≤ q := by
  have hdisj := fibreF_inter_shift (A := A) (x := x) (t := t) hA hT0 ht
  have hsum := card_union_add_card_inter
    (fibreF A (x + t)) ((fibreF A x).image (fun y => y + t ^ 2))
  rw [hdisj, card_empty, add_zero, card_image_add] at hsum
  have hle :
      #(fibreF A (x + t) ∪ (fibreF A x).image (fun y => y + t ^ 2)) ≤
        Fintype.card (ZMod q) := card_le_univ _
  rw [ZMod.card] at hle
  omega

def Tight (A : Finset (ZMod q × ZMod q)) (x t : ZMod q) : Prop :=
  #(fibreF A x) + #(fibreF A (x + t)) = q

lemma tight_eq_compl {T : Finset (ZMod q)} {A : Finset (ZMod q × ZMod q)}
    {x t : ZMod q}
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q)))
    (hT0 : 0 ∉ T) (ht : t ∈ T) (hTight : Tight A x t) :
    fibreF A (x + t) = ((fibreF A x).image (fun y => y + t ^ 2))ᶜ := by
  have hdisj := fibreF_inter_shift (A := A) (x := x) (t := t) hA hT0 ht
  have hsubset :
      fibreF A (x + t) ⊆ ((fibreF A x).image (fun y => y + t ^ 2))ᶜ := by
    intro y hy
    rw [mem_compl, mem_image]
    rintro ⟨z, hz, heq⟩
    have : y ∈ fibreF A (x + t) ∩ (fibreF A x).image (fun w => w + t ^ 2) := by
      exact mem_inter.2 ⟨hy, mem_image.2 ⟨z, hz, heq⟩⟩
    simp [hdisj] at this
  have hcardC :
      #(((fibreF A x).image (fun y => y + t ^ 2))ᶜ) = q - #(fibreF A x) := by
    rw [card_compl, card_image_add, ZMod.card]
  have hcard : #(fibreF A (x + t)) =
      #(((fibreF A x).image (fun y => y + t ^ 2))ᶜ) := by
    simp only [Tight] at hTight
    omega
  exact eq_of_subset_of_card_le hsubset (by omega)

lemma one_pow_two : (1 : ZMod q) ^ 2 = 1 := by simp

lemma three_pow_two : (3 : ZMod q) ^ 2 = 9 := by
  norm_num

lemma tight_4interval_period
    {T : Finset (ZMod q)} {A : Finset (ZMod q × ZMod q)} {x : ZMod q}
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q))) (hT0 : 0 ∉ T)
    (h1 : (1 : ZMod q) ∈ T) (h3 : (3 : ZMod q) ∈ T)
    (ht01 : Tight A x 1) (ht12 : Tight A (x + 1) 1)
    (ht23 : Tight A (x + 2) 1) (ht03 : Tight A x 3) :
    fibreF A x = (fibreF A x).image (fun y => y + 6) := by
  have B1 : fibreF A (x + 1) = ((fibreF A x).image (fun y => y + 1))ᶜ := by
    simpa [one_pow_two] using
      tight_eq_compl (A := A) (x := x) (t := 1) hA hT0 h1 ht01
  have B2 : fibreF A (x + 2) = (fibreF A x).image (fun y => y + 2) := by
    have h := tight_eq_compl (A := A) (x := x + 1) (t := 1) hA hT0 h1 ht12
    have hx : x + 1 + 1 = x + 2 := by ring
    rw [one_pow_two] at h
    rw [hx] at h
    rw [h, B1]
    have hdc := double_compl_shift (fibreF A x) 1 1
    have : (1 + 1 : ZMod q) = 2 := by norm_num
    rw [this] at hdc
    exact hdc
  have B3a : fibreF A (x + 3) = ((fibreF A x).image (fun y => y + 3))ᶜ := by
    have h := tight_eq_compl (A := A) (x := x + 2) (t := 1) hA hT0 h1 ht23
    have hx : x + 2 + 1 = x + 3 := by ring
    rw [one_pow_two] at h
    rw [hx] at h
    rw [h, B2, image_add_add]
    congr 1
    congr 1
    norm_num
  have B3b : fibreF A (x + 3) = ((fibreF A x).image (fun y => y + 9))ᶜ := by
    simpa [three_pow_two] using
      tight_eq_compl (A := A) (x := x) (t := 3) hA hT0 h3 ht03
  have heq : (fibreF A x).image (fun y => y + 3) =
      (fibreF A x).image (fun y => y + 9) :=
    compl_inj_iff.1 (B3a.symm.trans B3b)
  have htrans := congrArg (fun s => s.image (fun y => y + -3)) heq
  have hL := image_add_neg (fibreF A x) 3
  have hR : ((fibreF A x).image (fun y => y + 9)).image (fun y => y + -3) =
      (fibreF A x).image (fun y => y + 6) := by
    rw [image_add_add]
    congr 1
    ring_nf
  calc
    fibreF A x = ((fibreF A x).image (fun y => y + 3)).image (fun y => y + -3) :=
      hL.symm
    _ = ((fibreF A x).image (fun y => y + 9)).image (fun y => y + -3) := htrans
    _ = (fibreF A x).image (fun y => y + 6) := hR

lemma six_ne_zero (hq : 3 < q) : (6 : ZMod q) ≠ 0 := by
  intro h
  have hP : Nat.Prime q := Fact.out
  have hdvd : q ∣ 6 := by
    have : NeZero q := inferInstance
    exact (ZMod.natCast_eq_zero_iff 6 q).1 h
  have : q ∣ 2 * 3 := by simpa using hdvd
  rcases hP.dvd_mul.1 this with h2 | h3'
  · have : q = 2 := (Nat.dvd_prime Nat.prime_two).1 h2 |>.resolve_left hP.ne_one
    omega
  · have : q = 3 := (Nat.dvd_prime Nat.prime_three).1 h3' |>.resolve_left hP.ne_one
    omega

lemma image_add_nsmul (B : Finset (ZMod q)) (c : ZMod q) (n : ℕ)
    (h : B.image (fun y => y + c) = B) :
    B.image (fun y => y + (n : ZMod q) * c) = B := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcast : ((n + 1 : ℕ) : ZMod q) * c = (n : ZMod q) * c + c := by
      rw [Nat.cast_succ, add_mul, one_mul]
    have hstep :
        B.image (fun y => y + ((n + 1 : ℕ) : ZMod q) * c) =
          (B.image (fun y => y + (n : ZMod q) * c)).image (fun y => y + c) := by
      rw [image_add_add, hcast]
    rw [hstep, ih, h]

lemma period_eq_empty_or_univ {B : Finset (ZMod q)} {c : ZMod q} (hc : c ≠ 0)
    (h : B.image (fun y => y + c) = B) : B = ∅ ∨ B = univ := by
  refine or_iff_not_imp_left.2 fun hne => ?_
  obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.2 hne
  ext y
  simp only [mem_univ, iff_true]
  have hy : y = z + ((c⁻¹ * (y - z)).val : ZMod q) * c := by
    rw [ZMod.natCast_zmod_val]
    have : c⁻¹ * (y - z) * c = y - z := by
      rw [mul_assoc, mul_comm (y - z), ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rw [this, add_sub_cancel]
  have himg := image_add_nsmul B c (c⁻¹ * (y - z)).val h
  have : y ∈ B.image (fun w => w + ((c⁻¹ * (y - z)).val : ZMod q) * c) :=
    mem_image.2 ⟨z, hz, hy.symm⟩
  rwa [himg] at this

theorem no_tight_4interval_of_proper
    {T : Finset (ZMod q)} {A : Finset (ZMod q × ZMod q)} {x : ZMod q}
    (hq : 3 < q)
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q))) (hT0 : 0 ∉ T)
    (h1 : (1 : ZMod q) ∈ T) (h3 : (3 : ZMod q) ∈ T)
    (ht01 : Tight A x 1) (ht12 : Tight A (x + 1) 1)
    (ht23 : Tight A (x + 2) 1) (ht03 : Tight A x 3) :
    fibreF A x = ∅ ∨ fibreF A x = univ :=
  period_eq_empty_or_univ (six_ne_zero hq)
    (tight_4interval_period (A := A) (x := x) hA hT0 h1 h3
      ht01 ht12 ht23 ht03).symm

end R3tBound
