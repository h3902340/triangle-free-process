/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Packing arithmetic for below-random interval autocorrelations

If the sliding-window second moment expands as
`(L+1) m + 2 ∑_{t<L} (L-t) r_t` and each lag satisfies
`(c+1) q r_t ≤ c m²`, Cauchy--Schwarz yields
`m · (L + c + 1) ≤ (c + 1) q`.

The window expansion `∑_x ν(x)² = (L+1)|U| + 2 ∑_{t<L} (L-t) r(a(t+1))`
is proved below, so the size bound is Lean from a uniform lag hypothesis.
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

/-- Reindex `∑_{j<k} g(k-j)` over `{0,…,L}` as a weighted lag sum. -/
lemma sum_strict_upper (L : ℕ) (g : ℕ → ℕ) :
    ∑ j ∈ range (L + 1), ∑ k ∈ range j, g (j - k) =
      ∑ t ∈ range L, (L - t) * g (t + 1) := by
  induction L with
  | zero => simp
  | succ n ih =>
    have hsplit :
        ∑ j ∈ range (n + 2), ∑ k ∈ range j, g (j - k) =
          ∑ j ∈ range (n + 1), ∑ k ∈ range j, g (j - k) +
            ∑ k ∈ range (n + 1), g (n + 1 - k) := by
      rw [show n + 2 = n + 1 + 1 from rfl, sum_range_succ]
    have hpt : ∀ k ∈ range (n + 1), n + 1 - k = n - k + 1 := fun k hk => by
      have : k < n + 1 := mem_range.1 hk
      omega
    have hreflect : ∑ k ∈ range (n + 1), g (n + 1 - k) =
        ∑ t ∈ range (n + 1), g (t + 1) := by
      rw [sum_congr rfl fun k hk => congrArg g (hpt k hk)]
      exact sum_range_reflect (fun i => g (i + 1)) (n + 1)
    have hwt : ∀ t ∈ range n, n + 1 - t = n - t + 1 := fun t ht => by
      have : t < n := mem_range.1 ht
      omega
    have hdecomp :
        ∑ t ∈ range n, (n + 1 - t) * g (t + 1) =
          ∑ t ∈ range n, (n - t) * g (t + 1) +
            ∑ t ∈ range n, g (t + 1) := by
      have hpt' : ∀ t ∈ range n,
          (n + 1 - t) * g (t + 1) = (n - t) * g (t + 1) + g (t + 1) :=
        fun t ht => by
          rw [hwt t ht, add_mul, one_mul]
      rw [sum_congr rfl hpt', sum_add_distrib]
    have htail : ∑ t ∈ range n, g (t + 1) + g (n + 1) =
        ∑ t ∈ range (n + 1), g (t + 1) := by
      rw [sum_range_succ]
    have hgoal :
        ∑ t ∈ range (n + 1), (n + 1 - t) * g (t + 1) =
          ∑ t ∈ range n, (n + 1 - t) * g (t + 1) + g (n + 1) := by
      rw [sum_range_succ]
      simp
    rw [hsplit, ih, hreflect, hgoal, hdecomp, ← htail]
    ac_rfl

/-- The matching lower-triangle reindex. -/
lemma sum_strict_lower (L : ℕ) (g : ℕ → ℕ) :
    ∑ j ∈ range (L + 1), ∑ k ∈ Ico (j + 1) (L + 1), g (k - j) =
      ∑ t ∈ range L, (L - t) * g (t + 1) := by
  induction L with
  | zero => simp
  | succ n ih =>
    have hsplit :
        ∑ j ∈ range (n + 2), ∑ k ∈ Ico (j + 1) (n + 2), g (k - j) =
          ∑ j ∈ range (n + 1), ∑ k ∈ Ico (j + 1) (n + 2), g (k - j) := by
      rw [show n + 2 = n + 1 + 1 from rfl, sum_range_succ]
      simp
    have hsucc : ∀ j ∈ range (n + 1),
        ∑ k ∈ Ico (j + 1) (n + 2), g (k - j) =
          ∑ k ∈ Ico (j + 1) (n + 1), g (k - j) + g (n + 1 - j) :=
      fun j hj => by
        have : j + 1 ≤ n + 1 := Nat.succ_le_of_lt (mem_range.1 hj)
        simpa [Nat.succ_eq_add_one] using
          (sum_Ico_succ_top (a := j + 1) (b := n + 1) this
            (fun k => g (k - j)))
    have hpt : ∀ j ∈ range (n + 1), n + 1 - j = n - j + 1 := fun j hj => by
      have : j < n + 1 := mem_range.1 hj
      omega
    have hreflect : ∑ j ∈ range (n + 1), g (n + 1 - j) =
        ∑ t ∈ range (n + 1), g (t + 1) := by
      rw [sum_congr rfl fun j hj => congrArg g (hpt j hj)]
      exact sum_range_reflect (fun i => g (i + 1)) (n + 1)
    have hwt : ∀ t ∈ range n, n + 1 - t = n - t + 1 := fun t ht => by
      have : t < n := mem_range.1 ht
      omega
    have hdecomp :
        ∑ t ∈ range n, (n + 1 - t) * g (t + 1) =
          ∑ t ∈ range n, (n - t) * g (t + 1) +
            ∑ t ∈ range n, g (t + 1) := by
      have hpt' : ∀ t ∈ range n,
          (n + 1 - t) * g (t + 1) = (n - t) * g (t + 1) + g (t + 1) :=
        fun t ht => by
          rw [hwt t ht, add_mul, one_mul]
      rw [sum_congr rfl hpt', sum_add_distrib]
    have htail : ∑ t ∈ range n, g (t + 1) + g (n + 1) =
        ∑ t ∈ range (n + 1), g (t + 1) := by
      rw [sum_range_succ]
    have hgoal :
        ∑ t ∈ range (n + 1), (n + 1 - t) * g (t + 1) =
          ∑ t ∈ range n, (n + 1 - t) * g (t + 1) + g (n + 1) := by
      rw [sum_range_succ]
      simp
    rw [hsplit, sum_congr rfl hsucc, sum_add_distrib, ih, hreflect, hgoal,
      hdecomp, ← htail]
    ac_rfl

section Window
set_option linter.unusedSectionVars false
variable {q : ℕ} [NeZero q]

/-- Sliding-window occupancy: how many of `x, x+a, …, x+aL` land in `U`. -/
def windowCount (U : Finset (ZMod q)) (a : ZMod q) (L : ℕ) (x : ZMod q) : ℕ :=
  ∑ j ∈ range (L + 1), if x + a * (j : ZMod q) ∈ U then 1 else 0

/-- Autocorrelation `|U ∩ (U+σ)|`. -/
def autoCorr (U : Finset (ZMod q)) (σ : ZMod q) : ℕ :=
  #{y ∈ U | y - σ ∈ U}

lemma autoCorr_zero (U : Finset (ZMod q)) : autoCorr U 0 = #U := by
  simp [autoCorr]

lemma autoCorr_eq_card_image (U : Finset (ZMod q)) (σ : ZMod q) :
    autoCorr U σ = #(U ∩ U.image (fun y => y + σ)) := by
  classical
  unfold autoCorr
  congr 1
  ext y
  simp only [mem_filter, mem_inter, mem_image]
  constructor
  · intro ⟨hyU, hyσ⟩
    exact ⟨hyU, y - σ, hyσ, sub_add_cancel y σ⟩
  · intro ⟨hyU, z, hzU, hz⟩
    refine ⟨hyU, ?_⟩
    simpa [← hz, add_sub_cancel_right] using hzU

lemma autoCorr_neg (U : Finset (ZMod q)) (σ : ZMod q) :
    autoCorr U (-σ) = autoCorr U σ := by
  classical
  have himg :
      (U.filter fun y => y - σ ∈ U).image (fun y => y - σ) =
        U.filter fun z => z + σ ∈ U := by
    ext z
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨y, ⟨hyU, hyσ⟩, rfl⟩
      exact ⟨hyσ, by simpa [sub_add_cancel] using hyU⟩
    · intro ⟨hzσ, hzU⟩
      refine ⟨z + σ, ⟨hzU, ?_⟩, add_sub_cancel_right z σ⟩
      simpa [add_sub_cancel_right] using hzσ
  have hinj : Function.Injective (fun y : ZMod q => y - σ) :=
    fun a b h => by simpa using congrArg (fun z => z + σ) h
  have hcard :
      #((U.filter fun y => y - σ ∈ U).image (fun y => y - σ)) =
        #{y ∈ U | y - σ ∈ U} :=
    card_image_of_injective _ hinj
  have hneg : U.filter (fun z => z + σ ∈ U) =
      U.filter (fun z => z - (-σ) ∈ U) := by
    refine filter_congr fun z _ => ?_
    simp [sub_neg_eq_add]
  calc
    autoCorr U (-σ) = #{z ∈ U | z - (-σ) ∈ U} := rfl
    _ = #(U.filter fun z => z + σ ∈ U) := by rw [hneg]
    _ = #((U.filter fun y => y - σ ∈ U).image (fun y => y - σ)) := by
          rw [himg]
    _ = autoCorr U σ := hcard

/-- Indicator that `x + a j` and `x + a k` both lie in `U`. -/
def winOne (U : Finset (ZMod q)) (a : ZMod q) (x : ZMod q) (j : ℕ) : ℕ :=
  if x + a * (j : ZMod q) ∈ U then 1 else 0

lemma windowCount_eq_sum (U : Finset (ZMod q)) (a : ZMod q) (L : ℕ)
    (x : ZMod q) :
    windowCount U a L x = ∑ j ∈ range (L + 1), winOne U a x j := by
  simp [windowCount, winOne]

lemma sum_winOne (U : Finset (ZMod q)) (a : ZMod q) (j : ℕ) :
    ∑ x : ZMod q, winOne U a x j = #U := by
  classical
  have hsum :=
    Fintype.sum_equiv (Equiv.addRight (a * (j : ZMod q)))
      (fun x => winOne U a x j)
      (fun y => if y ∈ U then 1 else 0)
      (fun _ => rfl)
  have hU : (univ.filter fun y : ZMod q => y ∈ U) = U := by
    ext y
    simp
  rw [hsum]
  unfold winOne at *
  -- After the equiv, the sum is `∑ y, if y ∈ U then 1 else 0`.
  change ∑ y : ZMod q, (if y ∈ U then 1 else 0) = #U
  rw [sum_ite, hU, sum_const, smul_eq_mul, mul_one, sum_const_zero, add_zero]

lemma sum_windowCount (U : Finset (ZMod q)) (a : ZMod q) (L : ℕ) :
    ∑ x : ZMod q, windowCount U a L x = (L + 1) * #U := by
  calc
    ∑ x : ZMod q, windowCount U a L x
        = ∑ x : ZMod q, ∑ j ∈ range (L + 1), winOne U a x j :=
          sum_congr rfl fun x _ => windowCount_eq_sum U a L x
    _ = ∑ j ∈ range (L + 1), ∑ x : ZMod q, winOne U a x j := by
          rw [sum_comm]
    _ = ∑ j ∈ range (L + 1), #U :=
          sum_congr rfl fun j _ => sum_winOne U a j
    _ = (L + 1) * #U := by simp [sum_const, card_range, smul_eq_mul, mul_comm]

lemma sum_winOne_mul (U : Finset (ZMod q)) (a : ZMod q) (j k : ℕ) :
    ∑ x : ZMod q, winOne U a x j * winOne U a x k =
      autoCorr U (a * ((j : ZMod q) - (k : ZMod q))) := by
  classical
  have hsum :=
    Fintype.sum_equiv (Equiv.addRight (a * (k : ZMod q)))
      (fun x => winOne U a x j * winOne U a x k)
      (fun y => winOne U a (y - a * (k : ZMod q)) j *
        winOne U a (y - a * (k : ZMod q)) k)
      (fun x => by
        simp [Equiv.addRight, add_sub_cancel_right])
  have hk : ∀ y,
      winOne U a (y - a * (k : ZMod q)) k =
        if y ∈ U then 1 else 0 := fun y => by
    simp [winOne, sub_add_cancel]
  have hj : ∀ y,
      winOne U a (y - a * (k : ZMod q)) j =
        if y - a * ((k : ZMod q) - (j : ZMod q)) ∈ U then 1 else 0 :=
    fun y => by
      have : y - a * (k : ZMod q) + a * (j : ZMod q) =
          y - a * ((k : ZMod q) - (j : ZMod q)) := by ring
      simp [winOne, this]
  have hprod : ∀ y,
      winOne U a (y - a * (k : ZMod q)) j *
          winOne U a (y - a * (k : ZMod q)) k =
        if y ∈ U then
          (if y - a * ((k : ZMod q) - (j : ZMod q)) ∈ U then 1 else 0)
        else 0 := fun y => by
    rw [hj, hk]
    by_cases hy : y ∈ U <;> simp [hy]
  have hfilter :
      ∑ y : ZMod q,
          (if y ∈ U then
            (if y - a * ((k : ZMod q) - (j : ZMod q)) ∈ U then 1 else 0)
          else 0) =
        autoCorr U (a * ((k : ZMod q) - (j : ZMod q))) := by
    have hU : (univ.filter fun y : ZMod q => y ∈ U) = U := by
      ext y
      simp
    simp only [sum_ite, hU, sum_const_zero, add_zero]
    unfold autoCorr
    simp [sum_const, smul_eq_mul]
  calc
    ∑ x : ZMod q, winOne U a x j * winOne U a x k
        = ∑ y : ZMod q,
            winOne U a (y - a * (k : ZMod q)) j *
              winOne U a (y - a * (k : ZMod q)) k := hsum
    _ = ∑ y : ZMod q,
          (if y ∈ U then
            (if y - a * ((k : ZMod q) - (j : ZMod q)) ∈ U then 1 else 0)
          else 0) :=
          sum_congr rfl fun y _ => hprod y
    _ = autoCorr U (a * ((k : ZMod q) - (j : ZMod q))) := hfilter
    _ = autoCorr U (a * ((j : ZMod q) - (k : ZMod q))) := by
          have : a * ((k : ZMod q) - (j : ZMod q)) =
              -(a * ((j : ZMod q) - (k : ZMod q))) := by ring
          rw [this, autoCorr_neg]

lemma window_second_moment (U : Finset (ZMod q)) (a : ZMod q) (L : ℕ) :
    ∑ x : ZMod q, windowCount U a L x ^ 2 =
      (L + 1) * #U +
        2 * ∑ t ∈ range L, (L - t) *
          autoCorr U (a * (t + 1 : ZMod q)) := by
  classical
  have hsq : ∀ x,
      windowCount U a L x ^ 2 =
        ∑ j ∈ range (L + 1), ∑ k ∈ range (L + 1),
          winOne U a x j * winOne U a x k := fun x => by
    have hμ := windowCount_eq_sum U a L x
    have hmul :=
      sum_mul_sum (s := range (L + 1)) (t := range (L + 1))
        (f := fun j => winOne U a x j)
        (g := fun k => winOne U a x k)
    rw [pow_two, hμ]
    exact hmul
  have hpair :
      ∑ j ∈ range (L + 1), ∑ k ∈ range (L + 1),
          autoCorr U (a * ((j : ZMod q) - (k : ZMod q))) =
        (L + 1) * #U +
          2 * ∑ t ∈ range L, (L - t) *
            autoCorr U (a * (t + 1 : ZMod q)) := by
    have hsplit : ∀ j ∈ range (L + 1),
        ∑ k ∈ range (L + 1),
            autoCorr U (a * ((j : ZMod q) - (k : ZMod q))) =
          ∑ k ∈ range j, autoCorr U (a * ((j - k : ℕ) : ZMod q)) +
            autoCorr U 0 +
              ∑ k ∈ Ico (j + 1) (L + 1),
                autoCorr U (a * ((k - j : ℕ) : ZMod q)) :=
      fun j hj => by
        have hjL : j + 1 ≤ L + 1 := Nat.succ_le_of_lt (mem_range.1 hj)
        have hunion :=
          (sum_range_add_sum_Ico
            (fun k => autoCorr U (a * ((j : ZMod q) - (k : ZMod q))))
            hjL).symm
        have hsucc : ∑ k ∈ range (j + 1),
            autoCorr U (a * ((j : ZMod q) - (k : ZMod q))) =
              ∑ k ∈ range j,
                  autoCorr U (a * ((j : ZMod q) - (k : ZMod q))) +
                autoCorr U 0 := by
          rw [sum_range_succ]
          simp
        have hlt : ∀ k ∈ range j,
            (j : ZMod q) - (k : ZMod q) = ((j - k : ℕ) : ZMod q) :=
          fun k hk => by
            have : k ≤ j := Nat.le_of_lt (mem_range.1 hk)
            exact (Nat.cast_sub (R := ZMod q) this).symm
        have hgt : ∀ k ∈ Ico (j + 1) (L + 1),
            (j : ZMod q) - (k : ZMod q) = -((k - j : ℕ) : ZMod q) :=
          fun k hk => by
            have hjk : j ≤ k := Nat.le_of_succ_le (mem_Ico.1 hk).1
            have : (k : ZMod q) - (j : ZMod q) = ((k - j : ℕ) : ZMod q) :=
              (Nat.cast_sub (R := ZMod q) hjk).symm
            rw [← this]
            ring
        have hlt' :
            ∑ k ∈ range j,
                autoCorr U (a * ((j : ZMod q) - (k : ZMod q))) =
              ∑ k ∈ range j,
                autoCorr U (a * ((j - k : ℕ) : ZMod q)) :=
          sum_congr rfl fun k hk => by rw [hlt k hk]
        have hgt' :
            ∑ k ∈ Ico (j + 1) (L + 1),
                autoCorr U (a * ((j : ZMod q) - (k : ZMod q))) =
              ∑ k ∈ Ico (j + 1) (L + 1),
                autoCorr U (a * ((k - j : ℕ) : ZMod q)) :=
          sum_congr rfl fun k hk => by
            rw [hgt k hk, mul_neg, autoCorr_neg]
        calc
          ∑ k ∈ range (L + 1),
              autoCorr U (a * ((j : ZMod q) - (k : ZMod q)))
              = ∑ k ∈ range (j + 1),
                    autoCorr U (a * ((j : ZMod q) - (k : ZMod q))) +
                  ∑ k ∈ Ico (j + 1) (L + 1),
                    autoCorr U (a * ((j : ZMod q) - (k : ZMod q))) :=
                hunion
          _ = ∑ k ∈ range j,
                  autoCorr U (a * ((j : ZMod q) - (k : ZMod q))) +
                autoCorr U 0 +
                  ∑ k ∈ Ico (j + 1) (L + 1),
                    autoCorr U (a * ((j : ZMod q) - (k : ZMod q))) := by
                rw [hsucc, add_assoc]
          _ = ∑ k ∈ range j, autoCorr U (a * ((j - k : ℕ) : ZMod q)) +
                autoCorr U 0 +
                  ∑ k ∈ Ico (j + 1) (L + 1),
                    autoCorr U (a * ((k - j : ℕ) : ZMod q)) := by
                rw [hlt', hgt']
    have hsum := sum_congr rfl hsplit
    have hdiag :
        ∑ j ∈ range (L + 1), autoCorr U 0 = (L + 1) * #U := by
      simp [autoCorr_zero, sum_const, card_range, smul_eq_mul, mul_comm]
    have hup :
        ∑ j ∈ range (L + 1),
            ∑ k ∈ range j, autoCorr U (a * ((j - k : ℕ) : ZMod q)) =
          ∑ t ∈ range L, (L - t) * autoCorr U (a * (t + 1 : ZMod q)) := by
      simpa using
        sum_strict_upper L (fun δ => autoCorr U (a * (δ : ZMod q)))
    have hlo :
        ∑ j ∈ range (L + 1),
            ∑ k ∈ Ico (j + 1) (L + 1),
              autoCorr U (a * ((k - j : ℕ) : ZMod q)) =
          ∑ t ∈ range L, (L - t) * autoCorr U (a * (t + 1 : ZMod q)) := by
      simpa using
        sum_strict_lower L (fun δ => autoCorr U (a * (δ : ZMod q)))
    calc
      ∑ j ∈ range (L + 1), ∑ k ∈ range (L + 1),
          autoCorr U (a * ((j : ZMod q) - (k : ZMod q)))
          = ∑ j ∈ range (L + 1),
              (∑ k ∈ range j, autoCorr U (a * ((j - k : ℕ) : ZMod q)) +
                autoCorr U 0 +
                  ∑ k ∈ Ico (j + 1) (L + 1),
                    autoCorr U (a * ((k - j : ℕ) : ZMod q))) :=
            hsum
      _ = ∑ j ∈ range (L + 1),
              ∑ k ∈ range j, autoCorr U (a * ((j - k : ℕ) : ZMod q)) +
            ∑ j ∈ range (L + 1), autoCorr U 0 +
              ∑ j ∈ range (L + 1),
                ∑ k ∈ Ico (j + 1) (L + 1),
                  autoCorr U (a * ((k - j : ℕ) : ZMod q)) := by
            simp [sum_add_distrib]
      _ = ∑ t ∈ range L, (L - t) * autoCorr U (a * (t + 1 : ZMod q)) +
            (L + 1) * #U +
              ∑ t ∈ range L, (L - t) * autoCorr U (a * (t + 1 : ZMod q)) := by
            rw [hup, hdiag, hlo]
      _ = (L + 1) * #U +
            2 * ∑ t ∈ range L, (L - t) *
              autoCorr U (a * (t + 1 : ZMod q)) := by
            ring
  calc
    ∑ x : ZMod q, windowCount U a L x ^ 2
        = ∑ x : ZMod q, ∑ j ∈ range (L + 1), ∑ k ∈ range (L + 1),
            winOne U a x j * winOne U a x k :=
          sum_congr rfl fun x _ => hsq x
    _ = ∑ j ∈ range (L + 1), ∑ k ∈ range (L + 1),
          ∑ x : ZMod q, winOne U a x j * winOne U a x k := by
        rw [sum_comm]
        refine sum_congr rfl fun j _ => sum_comm
    _ = ∑ j ∈ range (L + 1), ∑ k ∈ range (L + 1),
          autoCorr U (a * ((j : ZMod q) - (k : ZMod q))) :=
          sum_congr rfl fun j _ =>
            sum_congr rfl fun k _ => sum_winOne_mul U a j k
    _ = (L + 1) * #U +
          2 * ∑ t ∈ range L, (L - t) *
            autoCorr U (a * (t + 1 : ZMod q)) :=
        hpair

lemma window_cs (U : Finset (ZMod q)) (a : ZMod q) (L : ℕ) :
    (L + 1) ^ 2 * #U ^ 2 ≤
      q * ∑ x : ZMod q, windowCount U a L x ^ 2 := by
  have hCS :=
    sq_sum_le_card_mul_sum_sq (s := univ) (f := windowCount U a L)
  have hsum := sum_windowCount U a L
  have hcard : #univ = q := (card_univ (α := ZMod q)).trans (ZMod.card q)
  calc
    (L + 1) ^ 2 * #U ^ 2
        = (∑ x : ZMod q, windowCount U a L x) ^ 2 := by
          rw [hsum]; ring
    _ ≤ #univ * ∑ x : ZMod q, windowCount U a L x ^ 2 := hCS
    _ = q * ∑ x : ZMod q, windowCount U a L x ^ 2 := by rw [hcard]

/-- A complete interval of uniformly below-random lags packs. -/
lemma pack_window (U : Finset (ZMod q)) (a : ZMod q) (L c : ℕ)
    (hr : ∀ t ∈ range L,
      (c + 1) * q * autoCorr U (a * (t + 1 : ZMod q)) ≤ c * #U ^ 2) :
    #U * (L + c + 1) ≤ (c + 1) * q := by
  have hCS : (L + 1) ^ 2 * #U ^ 2 ≤
      q * ((L + 1) * #U +
        2 * ∑ t ∈ range L, (L - t) *
          autoCorr U (a * (t + 1 : ZMod q))) := by
    have := window_cs U a L
    rwa [window_second_moment] at this
  exact pack_of_second_moment (q := q) (m := #U) (L := L) (c := c)
    (r := fun t => autoCorr U (a * (t + 1 : ZMod q))) hCS hr

lemma pack_window_two_thirds (U : Finset (ZMod q)) (a : ZMod q) (L : ℕ)
    (hr : ∀ t ∈ range L,
      3 * q * autoCorr U (a * (t + 1 : ZMod q)) ≤ 2 * #U ^ 2) :
    #U * (L + 3) ≤ 3 * q :=
  pack_window (U := U) (a := a) (L := L) (c := 2) hr

end Window

end R3tBound
