/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import R3tBound.Basic

/-!
# The parabola is a Sidon set
-/

namespace R3tBound

variable {q : ℕ} [Fact q.Prime]

lemma two_ne_zero (hq : Odd q) : (2 : ZMod q) ≠ 0 := by
  intro h
  have hP : Nat.Prime q := Fact.out
  have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).1 h
  have : q = 2 := (Nat.dvd_prime Nat.prime_two).1 hdvd |>.resolve_left hP.ne_one
  exact Nat.not_odd_iff_even.2 (by simp [this]) hq

lemma parabola_sum_of_diff {s t a b : ZMod q} (ha : a ≠ 0)
    (h1 : s - t = a) (h2 : s ^ 2 - t ^ 2 = b) :
    s + t = a⁻¹ * b := by
  have : s ^ 2 - t ^ 2 = (s - t) * (s + t) := by ring
  rw [this, h1] at h2
  exact (eq_inv_mul_iff_mul_eq₀ ha).2 (by simpa [mul_comm] using h2)

theorem parabola_sidon {s t s' t' : ZMod q} (hq : Odd q)
    (hne : s ≠ t) (hne' : s' ≠ t')
    (h : (s - t, s ^ 2 - t ^ 2) = (s' - t', s' ^ 2 - t' ^ 2)) :
    s = s' ∧ t = t' := by
  have ha : s - t ≠ 0 := sub_ne_zero.2 hne
  have h1 : s - t = s' - t' := congrArg Prod.fst h
  have h2 : s ^ 2 - t ^ 2 = s' ^ 2 - t' ^ 2 := congrArg Prod.snd h
  have hs : s + t = s' + t' := by
    have hsum := parabola_sum_of_diff (a := s - t) (b := s ^ 2 - t ^ 2) ha rfl rfl
    have hsum' := parabola_sum_of_diff (a := s' - t') (b := s' ^ 2 - t' ^ 2)
      (sub_ne_zero.2 hne') rfl rfl
    rw [h1, h2] at hsum
    exact hsum.trans hsum'.symm
  have h2ne := two_ne_zero hq
  constructor
  · have : 2 * s = 2 * s' := by linear_combination hs + h1
    exact mul_left_cancel₀ h2ne this
  · have : 2 * t = 2 * t' := by linear_combination hs - h1
    exact mul_left_cancel₀ h2ne this

end R3tBound
