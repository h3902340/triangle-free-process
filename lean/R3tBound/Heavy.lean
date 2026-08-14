/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization of the combinatorial R(3,t) notes
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import R3tBound.TightInterval

/-!
# Heavy fibres and cycle packing

A fibre larger than `q/2` cannot sit at a `T`-difference from another
heavy fibre (Family A, Lemma 4). A subset of `ℤ/qℤ` with no short
differences packs into `q/(d+1)` points (Family A, Lemma 5).
-/

namespace R3tBound

open Finset

section Prime
variable {q : ℕ} [Fact q.Prime]

/-- Two fibres of size `> q/2` cannot be at a `T`-difference. -/
theorem heavy_not_adjacent {T : Finset (ZMod q)} (h0 : 0 ∉ T)
    {A : Finset (ZMod q × ZMod q)} {x t : ZMod q} (ht : t ∈ T)
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q)))
    (hx : q / 2 < #(fibreF A x)) (hxt : q / 2 < #(fibreF A (x + t))) :
    False := by
  have hle := fibreF_card_add_le (A := A) (x := x) (t := t) hA h0 ht
  omega

end Prime

variable {q : ℕ}

/-- The Family A connection set `{1,…,d}` inside `ℤ/qℤ`. -/
def intervalT (d : ℕ) : Finset (ZMod q) :=
  (range d).image fun i : ℕ => (i + 1 : ZMod q)

lemma mem_intervalT {d : ℕ} {t : ZMod q} :
    t ∈ intervalT d ↔ ∃ i < d, t = (i + 1 : ZMod q) := by
  simp [intervalT, mem_image, mem_range, eq_comm]

lemma card_intervalT {d : ℕ} (hdq : d < q) :
    #(intervalT (q := q) d) = d := by
  have : NeZero q := ⟨Nat.ne_zero_of_lt hdq⟩
  rw [intervalT, card_image_iff.mpr ?_, card_range]
  intro a ha b hb h
  have hab : (a : ZMod q) = (b : ZMod q) := add_right_cancel h
  have ha' : a < q := (mem_range.mp ha).trans hdq
  have hb' : b < q := (mem_range.mp hb).trans hdq
  have : a % q = b % q := (ZMod.natCast_eq_natCast_iff' a b q).1 hab
  rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this

lemma card_le_intervalT {N : Finset (ZMod q)} {d : ℕ}
    (hN : N ⊆ intervalT d) (hdq : d < q) : #N ≤ d :=
  (card_le_card hN).trans_eq (card_intervalT hdq)

lemma intervalT_lt_of_double {d : ℕ} (_hdq : 2 * d ≤ q) (_hq : 0 < q) : d < q := by
  omega

lemma zero_notMem_intervalT {d : ℕ} (hdq : 2 * d ≤ q) (hq : 0 < q) :
    (0 : ZMod q) ∉ intervalT d := by
  intro h
  rcases mem_intervalT.1 h with ⟨i, hi, h0⟩
  have hcast : ((i + 1 : ℕ) : ZMod q) = 0 := by
    simpa using h0.symm
  have hdiv : (q : ℕ) ∣ i + 1 := (ZMod.natCast_eq_zero_iff (i + 1) q).1 hcast
  have hlt : i + 1 < q :=
    (Nat.succ_le_of_lt hi).trans_lt (intervalT_lt_of_double hdq hq)
  have hpos : 0 < i + 1 := Nat.succ_pos i
  have : i + 1 = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
  exact Nat.not_lt.2 (this.symm ▸ Nat.le_refl 0) hpos

/-- Distinct points of `{1,…,d}` differ by an element of `±T` as soon as
`2d ≤ q`, so every pair of `T_x`-fibres is `T`-adjacent. -/
lemma intervalT_pair_diff {d : ℕ} {s t : ZMod q}
    (hdq : 2 * d ≤ q) (hq : 0 < q)
    (hs : s ∈ intervalT d) (ht : t ∈ intervalT d) (hne : s ≠ t) :
    s - t ∈ intervalT d ∨ t - s ∈ intervalT d := by
  have := intervalT_lt_of_double hdq hq
  rcases mem_intervalT.1 hs with ⟨i, hi, rfl⟩
  rcases mem_intervalT.1 ht with ⟨j, hj, rfl⟩
  rcases lt_trichotomy i j with hij | rfl | hji
  · refine Or.inr ?_
    have hsub : ((j - i : ℕ) : ZMod q) =
        (j + 1 : ZMod q) - (i + 1 : ZMod q) := by
      have hji' : i ≤ j := Nat.le_of_lt hij
      have : ((j - i : ℕ) : ZMod q) = (j : ZMod q) - (i : ZMod q) :=
        Nat.cast_sub hji'
      simp [this, add_sub_add_right_eq_sub]
    have hpos : 0 < j - i := Nat.sub_pos_of_lt hij
    have hlt : j - i - 1 < d := by
      have : j - i ≤ j := Nat.sub_le j i
      have : j - i ≤ d := this.trans (Nat.le_of_lt hj)
      omega
    refine mem_intervalT.2 ⟨j - i - 1, hlt, ?_⟩
    have hsucc : ((j - i - 1 + 1 : ℕ) : ZMod q) = ((j - i : ℕ) : ZMod q) := by
      rw [Nat.sub_add_cancel hpos]
    simpa [hsub] using hsucc.symm
  · exact (hne rfl).elim
  · refine Or.inl ?_
    have hsub : ((i - j : ℕ) : ZMod q) =
        (i + 1 : ZMod q) - (j + 1 : ZMod q) := by
      have hij' : j ≤ i := Nat.le_of_lt hji
      have : ((i - j : ℕ) : ZMod q) = (i : ZMod q) - (j : ZMod q) :=
        Nat.cast_sub hij'
      simp [this, add_sub_add_right_eq_sub]
    have hpos : 0 < i - j := Nat.sub_pos_of_lt hji
    have hlt : i - j - 1 < d := by
      have : i - j ≤ i := Nat.sub_le i j
      have : i - j ≤ d := this.trans (Nat.le_of_lt hi)
      omega
    refine mem_intervalT.2 ⟨i - j - 1, hlt, ?_⟩
    have hsucc : ((i - j - 1 + 1 : ℕ) : ZMod q) = ((i - j : ℕ) : ZMod q) := by
      rw [Nat.sub_add_cancel hpos]
    simpa [hsub] using hsucc.symm

/-- Out-neighbours of `s = i+1` in `{1,…,d}` are exactly `{1,…,i}`.
A graph neighbourhood inside that set is therefore a subset of an
interval of length `i`. -/
lemma intervalT_out_mem {d : ℕ} {s t : ZMod q} {i : ℕ}
    (hdq : 2 * d ≤ q) (hq : 0 < q)
    (hi : i < d) (hs : s = (i + 1 : ZMod q)) :
    t ∈ intervalT d ∧ s - t ∈ intervalT d ↔ ∃ j < i, t = (j + 1 : ZMod q) := by
  have hdlt := intervalT_lt_of_double hdq hq
  have : NeZero q := ⟨ne_of_gt hq⟩
  constructor
  · intro ⟨ht, hst⟩
    rcases mem_intervalT.1 ht with ⟨j, hj, htj⟩
    rcases lt_trichotomy j i with hlt | hij | hgt
    · exact ⟨j, hlt, htj⟩
    · subst hij
      have ht0 : t = s := by simpa [hs] using htj
      have : (0 : ZMod q) ∈ intervalT d := by simpa [ht0] using hst
      exact (zero_notMem_intervalT hdq hq this).elim
    · have hts : t - s ∈ intervalT d := by
        have hpos : 0 < j - i := Nat.sub_pos_of_lt hgt
        have hlt' : j - i - 1 < d := by
          have : j - i ≤ j := Nat.sub_le j i
          have : j - i ≤ d := this.trans (Nat.le_of_lt hj)
          omega
        refine mem_intervalT.2 ⟨j - i - 1, hlt', ?_⟩
        have hsub' : ((j - i : ℕ) : ZMod q) =
            (j + 1 : ZMod q) - (i + 1 : ZMod q) := by
          have : ((j - i : ℕ) : ZMod q) = (j : ZMod q) - (i : ZMod q) :=
            Nat.cast_sub (Nat.le_of_lt hgt)
          simp [this, add_sub_add_right_eq_sub]
        have hsucc : ((j - i - 1 + 1 : ℕ) : ZMod q) = ((j - i : ℕ) : ZMod q) := by
          rw [Nat.sub_add_cancel hpos]
        calc
          t - s = (j + 1 : ZMod q) - (i + 1 : ZMod q) := by rw [htj, hs]
          _ = ((j - i : ℕ) : ZMod q) := hsub'.symm
          _ = ((j - i - 1 + 1 : ℕ) : ZMod q) := hsucc.symm
          _ = ((j - i - 1 : ℕ) : ZMod q) + 1 := by
            rw [Nat.cast_add, Nat.cast_one]
      rcases mem_intervalT.1 hst with ⟨k, hk, hkEq⟩
      rcases mem_intervalT.1 hts with ⟨k', hk', hk'Eq⟩
      have hsum0 : (s - t) + (t - s) = 0 := by abel
      have hsum : ((k + 1 + (k' + 1) : ℕ) : ZMod q) = 0 := by
        rw [Nat.cast_add, Nat.cast_succ, Nat.cast_succ, ← hkEq, ← hk'Eq, hsum0]
      have hdiv : (q : ℕ) ∣ k + 1 + (k' + 1) :=
        (ZMod.natCast_eq_zero_iff (k + 1 + (k' + 1)) q).1 hsum
      have hpos : 0 < k + 1 + (k' + 1) := by omega
      have hle : k + 1 + (k' + 1) ≤ 2 * d := by omega
      have hqeq : k + 1 + (k' + 1) = q :=
        le_antisymm (hle.trans hdq) (Nat.le_of_dvd hpos hdiv)
      have hki : k' + 1 = d := by omega
      have hdiff : ((j - i : ℕ) : ZMod q) = t - s := by
        have : ((j - i : ℕ) : ZMod q) = (j : ZMod q) - (i : ZMod q) :=
          Nat.cast_sub (Nat.le_of_lt hgt)
        rw [this, htj, hs, add_sub_add_right_eq_sub]
      have hcast : j - i = k' + 1 := by
        have h1 : j - i < q := (Nat.sub_le j i).trans_lt (hj.trans hdlt)
        have h2 : k' + 1 < q := (Nat.succ_le_of_lt hk').trans_lt hdlt
        have heq := (ZMod.natCast_eq_natCast_iff' (j - i) (k' + 1) q).1
          (hdiff.trans (hk'Eq.trans (Nat.cast_succ k').symm))
        rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at heq
      have hji : j - i < d := by omega
      omega
  · intro ⟨j, hj, htj⟩
    have ht : t ∈ intervalT d :=
      mem_intervalT.2 ⟨j, hj.trans hi, htj⟩
    have hpos : 0 < i - j := Nat.sub_pos_of_lt hj
    have hlt : i - j - 1 < d := by
      have : i - j ≤ i := Nat.sub_le i j
      have : i - j ≤ d := this.trans (Nat.le_of_lt hi)
      omega
    refine ⟨ht, mem_intervalT.2 ⟨i - j - 1, hlt, ?_⟩⟩
    have hsub : ((i - j : ℕ) : ZMod q) =
        (i + 1 : ZMod q) - (j + 1 : ZMod q) := by
      have : ((i - j : ℕ) : ZMod q) = (i : ZMod q) - (j : ZMod q) :=
        Nat.cast_sub (Nat.le_of_lt hj)
      simp [this, add_sub_add_right_eq_sub]
    have hsucc : ((i - j - 1 + 1 : ℕ) : ZMod q) = ((i - j : ℕ) : ZMod q) := by
      rw [Nat.sub_add_cancel hpos]
    calc
      s - t = (i + 1 : ZMod q) - (j + 1 : ZMod q) := by rw [hs, htj]
      _ = ((i - j : ℕ) : ZMod q) := hsub.symm
      _ = ((i - j - 1 + 1 : ℕ) : ZMod q) := hsucc.symm
      _ = ((i - j - 1 : ℕ) : ZMod q) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]

lemma card_intervalT_out {d : ℕ} {s : ZMod q} {i : ℕ}
    (hdq : 2 * d ≤ q) (hq : 0 < q)
    (hi : i < d) (hs : s = (i + 1 : ZMod q)) :
    #{t ∈ intervalT d | s - t ∈ intervalT d} = i := by
  have hdlt := intervalT_lt_of_double hdq hq
  have : NeZero q := ⟨ne_of_gt hq⟩
  let N := (range i).image fun j : ℕ => (j + 1 : ZMod q)
  have hN : N = (intervalT d).filter fun t => s - t ∈ intervalT d := by
    ext t
    simp only [N, mem_image, mem_range, mem_filter]
    constructor
    · intro ⟨j, hj, hjt⟩
      have := (intervalT_out_mem (t := t) hdq hq hi hs).2 ⟨j, hj, hjt.symm⟩
      exact ⟨this.1, this.2⟩
    · intro ht
      rcases (intervalT_out_mem (t := t) hdq hq hi hs).1 ht with ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
  have hcard : #N = i := by
    rw [card_image_iff.mpr ?_, card_range]
    intro a ha b hb h
    have hab : (a : ZMod q) = (b : ZMod q) := add_right_cancel h
    have ha' : a < q := (mem_range.mp ha).trans (hi.trans hdlt)
    have hb' : b < q := (mem_range.mp hb).trans (hi.trans hdlt)
    have : a % q = b % q := (ZMod.natCast_eq_natCast_iff' a b q).1 hab
    rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
  simpa [hN] using hcard

lemma card_le_intervalT_out {d : ℕ} {s : ZMod q} {i : ℕ} {N : Finset (ZMod q)}
    (hdq : 2 * d ≤ q) (hq : 0 < q)
    (hi : i < d) (hs : s = (i + 1 : ZMod q))
    (hN : ∀ t ∈ N, t ∈ intervalT d ∧ s - t ∈ intervalT d) :
    #N ≤ i := by
  have hsub : N ⊆ (intervalT d).filter fun t => s - t ∈ intervalT d := by
    intro t ht
    exact mem_filter.2 (hN t ht)
  exact (card_le_card hsub).trans_eq (card_intervalT_out hdq hq hi hs)

/-- Consecutive block of length `d+1` starting at `x`. -/
def block (d : ℕ) (x : ZMod q) : Finset (ZMod q) :=
  (range (d + 1)).image (fun i : ℕ => x + (i : ZMod q))

lemma card_block (d : ℕ) (x : ZMod q) (hdq : d + 1 ≤ q) :
    #(block d x) = d + 1 := by
  rw [block, card_image_iff.mpr ?_, card_range]
  intro a ha b hb h
  have hab : (a : ZMod q) = (b : ZMod q) := add_left_cancel h
  have ha' : a < q := (mem_range.mp ha).trans_le hdq
  have hb' : b < q := (mem_range.mp hb).trans_le hdq
  have : a % q = b % q := (ZMod.natCast_eq_natCast_iff' a b q).1 hab
  rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this

lemma mem_block {d : ℕ} {x y : ZMod q} :
    y ∈ block d x ↔ ∃ i < d + 1, y = x + (i : ZMod q) := by
  simp [block, mem_image, mem_range, eq_comm]

/-- A subset with no differences in `{±1,…,±d}` has size at most `q/(d+1)`. -/
theorem diffFree_card_le {S : Finset (ZMod q)} {d : ℕ}
    (_hd : 0 < d) (hdq : d + 1 ≤ q)
    (hS : ∀ ⦃x y : ZMod q⦄, x ∈ S → y ∈ S → x ≠ y →
      ∀ t : ℕ, 1 ≤ t → t ≤ d → y ≠ x + (t : ZMod q)) :
    #S * (d + 1) ≤ q := by
  have : NeZero q := ⟨by omega⟩
  have hdisj : (S : Set (ZMod q)).PairwiseDisjoint (block d) := by
    intro x hx z hz hxz
    by_contra hnd
    obtain ⟨y, hyx, hyz⟩ := not_disjoint_iff.mp hnd
    obtain ⟨i, hi, rfl⟩ := mem_block.mp hyx
    obtain ⟨j, hj, heq⟩ := mem_block.mp hyz
    have heq' : x + (i : ZMod q) = z + (j : ZMod q) := heq
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hz' : x = z + ((j - i : ℕ) : ZMod q) := by
        have hcast : ((j - i : ℕ) : ZMod q) = (j : ZMod q) - (i : ZMod q) :=
          Nat.cast_sub (Nat.le_of_lt hij)
        rw [hcast, ← add_sub_assoc]
        exact eq_sub_of_add_eq heq'
      exact hS hz hx hxz.symm (j - i)
        (Nat.succ_le_of_lt (Nat.sub_pos_of_lt hij))
        ((Nat.sub_le j i).trans (Nat.le_of_lt_succ hj)) hz'
    · exact hxz (by
        simpa [add_sub_cancel_right] using
          congrArg (fun w => w - (i : ZMod q)) heq')
    · have hx' : z = x + ((i - j : ℕ) : ZMod q) := by
        have hcast : ((i - j : ℕ) : ZMod q) = (i : ZMod q) - (j : ZMod q) :=
          Nat.cast_sub (Nat.le_of_lt hji)
        rw [hcast, ← add_sub_assoc]
        exact eq_sub_of_add_eq heq'.symm
      exact hS hx hz hxz (i - j)
        (Nat.succ_le_of_lt (Nat.sub_pos_of_lt hji))
        ((Nat.sub_le i j).trans (Nat.le_of_lt_succ hi)) hx'
  have hcard : #(S.biUnion (block d)) = #S * (d + 1) := by
    rw [card_biUnion hdisj, sum_congr rfl (fun _ _ => card_block d _ hdq), sum_const, smul_eq_mul]
  have hsub : S.biUnion (block d) ⊆ univ := fun _ _ => mem_univ _
  calc
    #S * (d + 1) = #(S.biUnion (block d)) := hcard.symm
    _ ≤ #univ := card_le_card hsub
    _ = q := (card_univ (α := ZMod q)).trans (ZMod.card q)

end R3tBound
