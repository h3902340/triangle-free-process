/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import R3tBound.Incidences

/-!
# First-moment star counts

Paper `open-edges.tex`, Lemmas `nstars` and `light`. Double-counting
gives `∑_w d(w) ≤ |I|Δ` and therefore
`t · #{w : t ≤ d(w)} ≤ |I|Δ` and
`2 ∑_{d≤t} binom(d,2) ≤ t · |I|Δ`.
At the SOTA scale `|I| ∼ Δ` the second bound is `o(|I|²)` only for
`t = o(1)`. The SOTA light-star second moment is not claimed.
-/

namespace R3tBound

open Finset

/-- `2 * n.choose 2 = n * (n-1)`. -/
lemma two_mul_choose_two : ∀ n : ℕ, 2 * n.choose 2 = n * (n - 1)
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    have ih := two_mul_choose_two (n + 1)
    rw [Nat.choose_succ_succ (n + 1) 1, Nat.choose_one_right, Nat.mul_add, ih]
    have h1 : n + 1 - 1 = n := Nat.add_sub_cancel n 1
    have h2 : n + 2 - 1 = n + 1 := Nat.add_sub_cancel (n + 1) 1
    rw [h1, h2]
    ring

/-- If `n ≤ t` then `2 * binom(n,2) ≤ t * n`. -/
lemma two_mul_choose_two_le {n t : ℕ} (h : n ≤ t) :
    2 * n.choose 2 ≤ t * n := by
  rw [two_mul_choose_two, mul_comm t n]
  exact Nat.mul_le_mul_left n (le_trans (Nat.sub_le n 1) h)

/-- Light pairs: `2 ∑ binom(d,2) ≤ t · ∑ d` on `{w : d(w) ≤ t}`.
Paper `lem:light`, with the factor `1/2` kept. -/
theorem two_mul_sum_choose_two_le {α : Type*} (S : Finset α) (d : α → ℕ)
    (t : ℕ) (h : ∀ w ∈ S, d w ≤ t) :
    2 * ∑ w ∈ S, (d w).choose 2 ≤ t * ∑ w ∈ S, d w := by
  have hpt : ∀ w ∈ S, 2 * (d w).choose 2 ≤ t * d w := fun w hw =>
    two_mul_choose_two_le (h w hw)
  calc
    2 * ∑ w ∈ S, (d w).choose 2
        = ∑ w ∈ S, 2 * (d w).choose 2 :=
          mul_sum (s := S) (f := fun w => (d w).choose 2) (a := 2)
    _ ≤ ∑ w ∈ S, t * d w := sum_le_sum hpt
    _ = t * ∑ w ∈ S, d w :=
          (mul_sum (s := S) (f := d) (a := t)).symm

/-- Weaker form matching the stated bound of `lem:light`:
`∑ binom(d,2) ≤ t · ∑ d`. -/
theorem sum_choose_two_le {α : Type*} (S : Finset α) (d : α → ℕ) (t : ℕ)
    (h : ∀ w ∈ S, d w ≤ t) :
    ∑ w ∈ S, (d w).choose 2 ≤ t * ∑ w ∈ S, d w :=
  (Nat.le_mul_of_pos_left _ (by decide : (0 : ℕ) < 2)).trans
    (two_mul_sum_choose_two_le S d t h)

/-- Markov / `lem:nstars`: a star of size at least `t` contributes at
least `t` to the degree sum. -/
theorem t_mul_card_le_sum {α : Type*} (W : Finset α) (d : α → ℕ) (t : ℕ) :
    t * #{w ∈ W | t ≤ d w} ≤ ∑ w ∈ W, d w := by
  classical
  have hsub :
      ∑ w ∈ W.filter fun w => t ≤ d w, d w ≤ ∑ w ∈ W, d w :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ W) fun _ _ _ => Nat.zero_le _
  have hpt :
      ∑ w ∈ W.filter fun w => t ≤ d w, t ≤
        ∑ w ∈ W.filter fun w => t ≤ d w, d w :=
    sum_le_sum fun w hw => (mem_filter.1 hw).2
  have hconst :
      ∑ w ∈ W.filter fun w => t ≤ d w, t =
        t * #{w ∈ W | t ≤ d w} := by
    simp [sum_const, smul_eq_mul, mul_comm]
  exact hconst.symm.trans_le (hpt.trans hsub)

variable {q : ℕ} [Fact q.Prime]

set_option linter.unusedSectionVars false

/-- Exact first moment on the seed graph: `∑_u D(u) = |S_R| |P|`. -/
theorem seedDegree_sum (P : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q)) :
    ∑ u : ZMod q × ZMod q, seedDegree P T u =
      #(signedParabola T) * #P := by
  classical
  set S := signedParabola T
  have hμ : ∀ u, seedDegree P T u =
      ∑ p ∈ P, if p - u ∈ S then 1 else 0 := fun u =>
    seedDegree_eq_sum P T u
  have hslice : ∀ p, ∑ u : ZMod q × ZMod q,
      (if p - u ∈ S then 1 else 0) = #S := fun p => by
    have himg :
        (univ.filter fun u : ZMod q × ZMod q => p - u ∈ S) =
          S.image fun s => p - s := by
      ext u
      simp only [mem_filter, mem_univ, true_and, mem_image]
      constructor
      · intro hs
        exact ⟨p - u, hs, by abel⟩
      · rintro ⟨s, hs, rfl⟩
        simpa
    have hinj : (S.image fun s => p - s).card = #S :=
      card_image_of_injective _ fun a b h => sub_right_inj.mp h
    calc
      ∑ u : ZMod q × ZMod q, (if p - u ∈ S then 1 else 0)
          = #{u : ZMod q × ZMod q | p - u ∈ S} := by
            simp [sum_boole]
      _ = (S.image fun s => p - s).card := by
            simp [himg]
      _ = #S := hinj
  calc
    ∑ u, seedDegree P T u
        = ∑ u, ∑ p ∈ P, if p - u ∈ S then 1 else 0 :=
          sum_congr rfl fun u _ => hμ u
    _ = ∑ p ∈ P, ∑ u, if p - u ∈ S then 1 else 0 := sum_comm
    _ = ∑ p ∈ P, #S := sum_congr rfl fun p _ => hslice p
    _ = #S * #P := by
          simp [sum_const, smul_eq_mul, mul_comm]

/-- First-moment form of `lem:nstars` on the seed graph:
`∑ D ≤ 2 |T| |P|`. -/
theorem seedDegree_sum_le (P : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) :
    ∑ u : ZMod q × ZMod q, seedDegree P T u ≤ 2 * #T * #P := by
  calc
    ∑ u, seedDegree P T u
        = #(signedParabola T) * #P := seedDegree_sum P T
    _ ≤ (2 * #T) * #P := Nat.mul_le_mul_right _ (card_signedParabola_le T)
    _ = 2 * #T * #P := by ring

/-- `lem:nstars` on the seed graph: `t · #{u : t ≤ D(u)} ≤ |S_R| |P|`. -/
theorem seed_heavy_star_count (P : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (t : ℕ) :
    t * #{u : ZMod q × ZMod q | t ≤ seedDegree P T u} ≤
      #(signedParabola T) * #P := by
  classical
  simpa [seedDegree_sum P T] using
    t_mul_card_le_sum (univ : Finset (ZMod q × ZMod q)) (seedDegree P T) t

/-- `lem:light` on the seed graph, factor `1/2` kept:
`2 ∑_{D≤t} binom(D,2) ≤ t |S_R| |P|`. -/
theorem light_seed_pairs (P : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (t : ℕ) :
    2 * ∑ u ∈ univ.filter fun u : ZMod q × ZMod q => seedDegree P T u ≤ t,
          (seedDegree P T u).choose 2 ≤
      t * #(signedParabola T) * #P := by
  classical
  set S := univ.filter fun u : ZMod q × ZMod q => seedDegree P T u ≤ t
  have hbd := two_mul_sum_choose_two_le S (seedDegree P T) t fun u hu =>
    (mem_filter.1 hu).2
  have hsum : ∑ u ∈ S, seedDegree P T u ≤
      ∑ u : ZMod q × ZMod q, seedDegree P T u :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.zero_le _
  calc
    2 * ∑ u ∈ S, (seedDegree P T u).choose 2
        ≤ t * ∑ u ∈ S, seedDegree P T u := hbd
    _ ≤ t * ∑ u, seedDegree P T u := Nat.mul_le_mul_left t hsum
    _ = t * (#(signedParabola T) * #P) := by rw [seedDegree_sum]
    _ = t * #(signedParabola T) * #P := by ring

/-- If `t |S_R| < |P|` then light pairs are strictly less than `|P|²`.
At the SOTA scale `|P| ∼ |S_R|` this needs `t = o(1)`. -/
theorem light_seed_pairs_lt_sq (P : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (t : ℕ)
    (h : t * #(signedParabola T) < #P) :
    2 * ∑ u ∈ univ.filter fun u : ZMod q × ZMod q => seedDegree P T u ≤ t,
          (seedDegree P T u).choose 2 < #P * #P := by
  have hP : 0 < #P := (Nat.zero_le _).trans_lt h
  have hmul : t * #(signedParabola T) * #P < #P * #P :=
    Nat.mul_lt_mul_of_pos_right h hP
  exact (light_seed_pairs P T t).trans_lt hmul

end R3tBound
