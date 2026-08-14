/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Packing arithmetic for below-random interval autocorrelations

If the sliding-window second moment expands as
`(L+1) m + 2 ∑_{t<L} (L-t) r_t` and each lag satisfies
`(c+1) q r_t ≤ c m²`, Cauchy--Schwarz yields
`m · (L + c + 1) ≤ (c + 1) q`.

The window expansion itself is the standard identity
`∑_x ν(x)² = ∑_{j,k} |U ∩ (U + a(j-k))|` and is recorded in
`inverse-energy.tex`. This file verifies the size bound from that
identity.
-/

namespace R3tBound

open Finset

variable {q : ℕ}

lemma sum_range_weighted (L : ℕ) :
    2 * ∑ t ∈ range L, (L - t) = L * (L + 1) := by
  induction L with
  | zero => simp
  | succ n ih =>
    have hpt : ∀ t ∈ range n, n + 1 - t = n - t + 1 := fun t ht => by
      have : t < n := mem_range.1 ht
      omega
    have h1 : n + 1 - n = 1 := Nat.add_sub_cancel_left n 1
    have hshift : ∑ t ∈ range n, (n + 1 - t) =
        ∑ t ∈ range n, (n - t) + n := by
      rw [sum_congr rfl hpt, sum_add_distrib]
      simp [sum_const, card_range]
    rw [sum_range_succ, h1, hshift]
    have hring : 2 * (∑ t ∈ range n, (n - t) + n + 1) =
        2 * ∑ t ∈ range n, (n - t) + 2 * n + 2 := by ring
    rw [hring, ih]
    ring

lemma cL_le_succ (c L : ℕ) : c * L ≤ (c + 1) * (L + 1) :=
  (Nat.mul_le_mul_right L (Nat.le_succ c)).trans
    (Nat.mul_le_mul_left (c + 1) (Nat.le_succ L))

/-- From `(c+1)(L+1) m² ≤ (c+1) q m + c L m²`, conclude
`m (L + c + 1) ≤ (c+1) q`. -/
lemma pack_arith (q L c m : ℕ) (hm : 0 < m)
    (h : (c + 1) * (L + 1) * m ^ 2 ≤ (c + 1) * q * m + c * L * m ^ 2) :
    m * (L + c + 1) ≤ (c + 1) * q := by
  have hlin : (c + 1) * (L + 1) * m ≤ (c + 1) * q + c * L * m := by
    have hmul : ((c + 1) * (L + 1) * m) * m ≤
        ((c + 1) * q + c * L * m) * m := by
      calc
        ((c + 1) * (L + 1) * m) * m
            = (c + 1) * (L + 1) * m ^ 2 := by ring
        _ ≤ (c + 1) * q * m + c * L * m ^ 2 := h
        _ = ((c + 1) * q + c * L * m) * m := by ring
    exact Nat.le_of_mul_le_mul_right hmul hm
  have hexp : (c + 1) * (L + 1) = c * L + (L + c + 1) := by ring
  have hcoeff : (c + 1) * (L + 1) - c * L = L + c + 1 := by
    rw [hexp, Nat.add_sub_cancel_left]
  have hadd : m * ((c + 1) * (L + 1)) ≤ (c + 1) * q + m * (c * L) := by
    calc
      m * ((c + 1) * (L + 1))
          = (c + 1) * (L + 1) * m := by ring
      _ ≤ (c + 1) * q + c * L * m := hlin
      _ = (c + 1) * q + m * (c * L) := by ring
  have hsub : m * ((c + 1) * (L + 1) - c * L) =
      m * ((c + 1) * (L + 1)) - m * (c * L) :=
    Nat.mul_sub_left_distrib m _ _
  have hfinal : m * ((c + 1) * (L + 1) - c * L) ≤ (c + 1) * q := by
    rw [hsub]
    exact Nat.sub_le_iff_le_add.2 hadd
  simpa [hcoeff] using hfinal

/-- From Cauchy--Schwarz on the sliding window and a below-random bound
on each lag, `|U| · (L + c + 1) ≤ (c + 1) q`. -/
lemma pack_of_second_moment {m L c : ℕ} {r : ℕ → ℕ}
    (hCS : (L + 1) ^ 2 * m ^ 2 ≤ q * ((L + 1) * m +
      2 * ∑ t ∈ range L, (L - t) * r t))
    (hr : ∀ t ∈ range L, (c + 1) * q * r t ≤ c * m ^ 2) :
    m * (L + c + 1) ≤ (c + 1) * q := by
  have hpt : ∀ t ∈ range L,
      (c + 1) * q * ((L - t) * r t) ≤ (L - t) * (c * m ^ 2) := by
    intro t ht
    calc
      (c + 1) * q * ((L - t) * r t)
          = (L - t) * ((c + 1) * q * r t) := by ring
      _ ≤ (L - t) * (c * m ^ 2) := Nat.mul_le_mul_left _ (hr t ht)
  have h2 : (c + 1) * q * ∑ t ∈ range L, (L - t) * r t ≤
      ∑ t ∈ range L, (L - t) * (c * m ^ 2) := by
    calc
      (c + 1) * q * ∑ t ∈ range L, (L - t) * r t
          = ∑ t ∈ range L, (c + 1) * q * ((L - t) * r t) := by
            rw [mul_sum]
      _ ≤ ∑ t ∈ range L, (L - t) * (c * m ^ 2) := sum_le_sum hpt
  have hfactor : ∑ t ∈ range L, (L - t) * (c * m ^ 2) =
      c * m ^ 2 * ∑ t ∈ range L, (L - t) := by
    rw [sum_congr rfl (fun t _ => mul_comm (L - t) (c * m ^ 2)), ← mul_sum]
  have hsum : (c + 1) * q * (2 * ∑ t ∈ range L, (L - t) * r t) ≤
      c * L * (L + 1) * m ^ 2 := by
    calc
      (c + 1) * q * (2 * ∑ t ∈ range L, (L - t) * r t)
          = 2 * ((c + 1) * q * ∑ t ∈ range L, (L - t) * r t) := by ring
      _ ≤ 2 * ∑ t ∈ range L, (L - t) * (c * m ^ 2) :=
          Nat.mul_le_mul_left 2 h2
      _ = 2 * (c * m ^ 2 * ∑ t ∈ range L, (L - t)) := by rw [hfactor]
      _ = c * m ^ 2 * (2 * ∑ t ∈ range L, (L - t)) := by ring
      _ = c * m ^ 2 * (L * (L + 1)) := by rw [sum_range_weighted]
      _ = c * L * (L + 1) * m ^ 2 := by ring
  have hCS' : (c + 1) * (L + 1) ^ 2 * m ^ 2 ≤
      (c + 1) * q * ((L + 1) * m +
        2 * ∑ t ∈ range L, (L - t) * r t) := by
    calc
      (c + 1) * (L + 1) ^ 2 * m ^ 2
          = (c + 1) * ((L + 1) ^ 2 * m ^ 2) := by ring
      _ ≤ (c + 1) * (q * ((L + 1) * m +
            2 * ∑ t ∈ range L, (L - t) * r t)) :=
          Nat.mul_le_mul_left (c + 1) hCS
      _ = (c + 1) * q * ((L + 1) * m +
            2 * ∑ t ∈ range L, (L - t) * r t) := by ring
  have hcomb : (c + 1) * (L + 1) ^ 2 * m ^ 2 ≤
      (c + 1) * q * ((L + 1) * m) + c * L * (L + 1) * m ^ 2 := by
    calc
      (c + 1) * (L + 1) ^ 2 * m ^ 2
          ≤ (c + 1) * q * ((L + 1) * m +
              2 * ∑ t ∈ range L, (L - t) * r t) := hCS'
      _ = (c + 1) * q * ((L + 1) * m) +
            (c + 1) * q * (2 * ∑ t ∈ range L, (L - t) * r t) := by
          rw [mul_add]
      _ ≤ (c + 1) * q * ((L + 1) * m) + c * L * (L + 1) * m ^ 2 :=
          add_le_add le_rfl hsum
  have hcancel : (c + 1) * (L + 1) * m ^ 2 ≤
      (c + 1) * q * m + c * L * m ^ 2 := by
    have hpos : 0 < L + 1 := Nat.succ_pos L
    have : (L + 1) * ((c + 1) * (L + 1) * m ^ 2) ≤
        (L + 1) * ((c + 1) * q * m + c * L * m ^ 2) := by
      calc
        (L + 1) * ((c + 1) * (L + 1) * m ^ 2)
            = (c + 1) * (L + 1) ^ 2 * m ^ 2 := by ring
        _ ≤ (c + 1) * q * ((L + 1) * m) + c * L * (L + 1) * m ^ 2 := hcomb
        _ = (L + 1) * ((c + 1) * q * m + c * L * m ^ 2) := by ring
    exact Nat.le_of_mul_le_mul_left this hpos
  by_cases hm : m = 0
  · simp [hm]
  · exact pack_arith q L c m (Nat.pos_of_ne_zero hm) hcancel

lemma pack_of_second_moment_two_thirds {m L : ℕ} {r : ℕ → ℕ}
    (hCS : (L + 1) ^ 2 * m ^ 2 ≤ q * ((L + 1) * m +
      2 * ∑ t ∈ range L, (L - t) * r t))
    (hr : ∀ t ∈ range L, 3 * q * r t ≤ 2 * m ^ 2) :
    m * (L + 3) ≤ 3 * q :=
  pack_of_second_moment (q := q) (m := m) (L := L) (c := 2) (r := r) hCS hr

end R3tBound
