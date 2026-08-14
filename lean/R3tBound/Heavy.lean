/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization of the combinatorial R(3,t) notes
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
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
