/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import R3tBound.Sidon

/-!
# Sidon codegree of the truncated parabola

A nonzero difference has at most one representation as a difference of
two unsigned parabola points. The signed connection set `S_R` has
codegree at most 6, which yields the Cauchy--Schwarz count
`∑_u D(u)² ≤ |S_R| |P| + 6 |P|(|P|-1)`. That is `O(d|P|+|P|²)`, not
`o(|P|²)` at the SOTA scale.
-/

namespace R3tBound

open Finset

variable {q : ℕ} [Fact q.Prime]

set_option linter.unusedSectionVars false

theorem parabola_codegree {T : Finset (ZMod q)} (hq : Odd q)
    {δ : ZMod q × ZMod q} (hδ : δ ≠ 0) :
    #{p ∈ parabola T | p - δ ∈ parabola T} ≤ 1 := by
  classical
  refine card_le_one.2 ?_
  intro p hp r hr
  obtain ⟨hpT, hpδ⟩ := mem_filter.1 hp
  obtain ⟨hrT, hrδ⟩ := mem_filter.1 hr
  obtain ⟨t, ht, rfl⟩ := mem_image.1 hpT
  obtain ⟨s, hs, hps⟩ := mem_image.1 hpδ
  obtain ⟨t', ht', rfl⟩ := mem_image.1 hrT
  obtain ⟨s', hs', hps'⟩ := mem_image.1 hrδ
  have hδt : (t - s, t ^ 2 - s ^ 2) = δ := by
    have h := hps.symm
    have := congrArg (fun z : ZMod q × ZMod q => (t, t ^ 2) - z) h
    simpa [sub_sub_cancel, Prod.mk_sub_mk] using this.symm
  have hδt' : (t' - s', t' ^ 2 - s' ^ 2) = δ := by
    have h := hps'.symm
    have := congrArg (fun z : ZMod q × ZMod q => (t', t' ^ 2) - z) h
    simpa [sub_sub_cancel, Prod.mk_sub_mk] using this.symm
  have hne : t ≠ s := by
    intro h
    exact hδ (hδt.symm.trans (by simp [h]))
  have hne' : t' ≠ s' := by
    intro h
    exact hδ (hδt'.symm.trans (by simp [h]))
  have hst := parabola_sidon hq hne hne' (hδt.trans hδt'.symm)
  simp [hst.1]

lemma card_parabola (T : Finset (ZMod q)) : #(parabola T) = #T :=
  card_image_of_injective _ fun a b h => by
    simpa using congrArg Prod.fst h

lemma card_signedParabola_le (T : Finset (ZMod q)) :
    #(signedParabola T) ≤ 2 * #T := by
  have hplus : #(parabola T) = #T := card_parabola T
  have hminus : #((parabola T).image fun p => -p) ≤ #T :=
    (card_image_le).trans_eq hplus
  calc
    #(signedParabola T)
        ≤ #(parabola T) + #((parabola T).image fun p => -p) :=
          card_union_le _ _
    _ ≤ #T + #T := add_le_add hplus.le hminus
    _ = 2 * #T := by ring

/-- A nonzero quadratic over a field has at most two roots. -/
lemma at_most_two_quadratic {α β γ : ZMod q} (hα : α ≠ 0) :
    #(univ.filter fun x : ZMod q => α * x ^ 2 + β * x + γ = 0) ≤ 2 := by
  classical
  by_contra h
  have h3 : 2 < #(univ.filter fun x : ZMod q =>
      α * x ^ 2 + β * x + γ = 0) :=
    lt_of_not_ge h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := two_lt_card.1 h3
  have hx0 : α * x ^ 2 + β * x + γ = 0 := (mem_filter.1 hx).2
  have hy0 : α * y ^ 2 + β * y + γ = 0 := (mem_filter.1 hy).2
  have hz0 : α * z ^ 2 + β * z + γ = 0 := (mem_filter.1 hz).2
  have hxy' : α * (x + y) + β = 0 := by
    have hsub : α * (x ^ 2 - y ^ 2) + β * (x - y) = 0 := by
      linear_combination hx0 - hy0
    have hfac : (x - y) * (α * (x + y) + β) = 0 := by
      convert hsub using 1
      ring
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.2 hxy)
  have hxz' : α * (x + z) + β = 0 := by
    have hsub : α * (x ^ 2 - z ^ 2) + β * (x - z) = 0 := by
      linear_combination hx0 - hz0
    have hfac : (x - z) * (α * (x + z) + β) = 0 := by
      convert hsub using 1
      ring
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.2 hxz)
  have hαyz : α * (y - z) = 0 := by
    linear_combination hxy' - hxz'
  have hyz0 : y - z = 0 :=
    (mul_eq_zero.mp hαyz).resolve_left hα
  exact hyz (sub_eq_zero.mp hyz0)

lemma sum_sq_quadratic (t a b : ZMod q)
    (h : t ^ 2 + (a - t) ^ 2 = b) :
    (2 : ZMod q) * t ^ 2 + -(2 * a) * t + (a ^ 2 - b) = 0 := by
  linear_combination h

lemma plus_minus_quadratic (t t' : ZMod q) {δ : ZMod q × ZMod q}
    (h : (t, t ^ 2) - (-t', -t' ^ 2) = δ) :
    (2 : ZMod q) * t ^ 2 + -(2 * δ.1) * t + (δ.1 ^ 2 - δ.2) = 0 := by
  have h1 : t + t' = δ.1 := by
    have := congrArg Prod.fst h
    simpa [Prod.mk_sub_mk, add_comm] using this
  have h2 : t ^ 2 + t' ^ 2 = δ.2 := by
    have := congrArg Prod.snd h
    simpa [Prod.mk_sub_mk] using this
  have ht' : t' = δ.1 - t :=
    (eq_sub_iff_add_eq).2 (by simpa [add_comm] using h1)
  exact sum_sq_quadratic t δ.1 δ.2 (by simpa [ht'] using h2)

lemma minus_plus_quadratic (t t' : ZMod q) {δ : ZMod q × ZMod q}
    (h : (-t, -t ^ 2) - (t', t' ^ 2) = δ) :
    (2 : ZMod q) * t ^ 2 + (2 * δ.1) * t + (δ.1 ^ 2 + δ.2) = 0 := by
  have h1 : -t - t' = δ.1 := by
    have := congrArg Prod.fst h
    simpa [Prod.mk_sub_mk] using this
  have h2 : -t ^ 2 - t' ^ 2 = δ.2 := by
    have := congrArg Prod.snd h
    simpa [Prod.mk_sub_mk] using this
  have h1' : t + t' = -δ.1 := by
    have := congrArg (fun z => -z) h1
    simpa [neg_add, neg_neg, add_comm] using this
  have h2' : t ^ 2 + t' ^ 2 = -δ.2 := by
    have := congrArg (fun z => -z) h2
    simpa [neg_add, neg_neg, add_comm] using this
  have ht' : t' = -δ.1 - t :=
    (eq_sub_iff_add_eq).2 (by simpa [add_comm] using h1')
  have hsq : t ^ 2 + (-δ.1 - t) ^ 2 = -δ.2 := by simpa [ht'] using h2'
  have := sum_sq_quadratic t (-δ.1) (-δ.2) hsq
  simpa [neg_mul, sub_eq_add_neg] using this

/-- A nonzero difference has at most six representations as a
difference of signed parabola points. -/
theorem signedParabola_codegree {T : Finset (ZMod q)} (hq : Odd q)
    {δ : ZMod q × ZMod q} (hδ : δ ≠ 0) :
    #{s ∈ signedParabola T | s - δ ∈ signedParabola T} ≤ 6 := by
  classical
  set S := signedParabola T
  have h2 : (2 : ZMod q) ≠ 0 := two_ne_zero hq
  have hposPP : #{t ∈ T | (t, t ^ 2) - δ ∈ parabola T} ≤ 1 := by
    have himg :
        (T.filter fun t => (t, t ^ 2) - δ ∈ parabola T).image
            (fun t => (t, t ^ 2)) ⊆
          {p ∈ parabola T | p - δ ∈ parabola T} := by
      intro p hp
      rcases mem_image.1 hp with ⟨t, ht, rfl⟩
      rcases mem_filter.1 ht with ⟨htT, htδ⟩
      exact mem_filter.2 ⟨mem_image.2 ⟨t, htT, rfl⟩, htδ⟩
    have hinj :=
      card_image_of_injective (f := fun t : ZMod q => (t, t ^ 2))
        (T.filter fun t => (t, t ^ 2) - δ ∈ parabola T)
        (fun a b h => by
          have := congrArg Prod.fst h
          simpa using this)
    exact hinj.symm.trans_le
      ((card_le_card himg).trans (parabola_codegree (T := T) hq hδ))
  have hposPM : #{t ∈ T | (t, t ^ 2) - δ ∈
      (parabola T).image fun p => -p} ≤ 2 := by
    refine (card_le_card ?_).trans
      (at_most_two_quadratic (α := (2 : ZMod q)) (β := -(2 * δ.1))
        (γ := δ.1 ^ 2 - δ.2) h2)
    intro t ht
    rcases mem_filter.1 ht with ⟨htT, htδ⟩
    obtain ⟨t', ht', ht'eq⟩ : ∃ t' ∈ T, (t, t ^ 2) - δ = (-t', -t' ^ 2) := by
      rcases mem_image.1 htδ with ⟨r, hr, hreq⟩
      obtain ⟨t', ht', rfl⟩ := mem_image.1 hr
      exact ⟨t', ht', hreq.symm⟩
    have hδval : (t, t ^ 2) - (-t', -t' ^ 2) = δ := by
      rw [← ht'eq]; abel
    exact mem_filter.2 ⟨mem_univ t, plus_minus_quadratic t t' hδval⟩
  have hnegMM : #{t ∈ T | (-t, -t ^ 2) - δ ∈
      (parabola T).image fun p => -p} ≤ 1 := by
    have hδ' : (-δ) ≠ 0 := neg_ne_zero.mpr hδ
    have himg :
        (T.filter fun t => (-t, -t ^ 2) - δ ∈
            (parabola T).image fun p => -p).image
          (fun t => (t, t ^ 2)) ⊆
          {p ∈ parabola T | p - (-δ) ∈ parabola T} := by
      intro p hp
      rcases mem_image.1 hp with ⟨t, ht, rfl⟩
      rcases mem_filter.1 ht with ⟨htT, htδ⟩
      rcases mem_image.1 htδ with ⟨r, hr, hreq⟩
      refine mem_filter.2 ⟨mem_image.2 ⟨t, htT, rfl⟩, ?_⟩
      have : r = (t, t ^ 2) + δ := by
        have := congrArg (fun z => -z) hreq
        simpa [neg_neg, neg_sub, sub_eq_neg_add, add_comm] using this
      simpa [sub_neg_eq_add, this] using hr
    have hinj :=
      card_image_of_injective (f := fun t : ZMod q => (t, t ^ 2))
        (T.filter fun t => (-t, -t ^ 2) - δ ∈
          (parabola T).image fun p => -p)
        (fun a b h => by
          have := congrArg Prod.fst h
          simpa using this)
    exact hinj.symm.trans_le
      ((card_le_card himg).trans (parabola_codegree (T := T) hq hδ'))
  have hnegMP : #{t ∈ T | (-t, -t ^ 2) - δ ∈ parabola T} ≤ 2 := by
    refine (card_le_card ?_).trans
      (at_most_two_quadratic (α := (2 : ZMod q)) (β := 2 * δ.1)
        (γ := δ.1 ^ 2 + δ.2) h2)
    intro t ht
    rcases mem_filter.1 ht with ⟨htT, htδ⟩
    obtain ⟨t', ht', ht'eq⟩ := mem_image.1 htδ
    have hδval : (-t, -t ^ 2) - (t', t' ^ 2) = δ := by
      have : (-t, -t ^ 2) - δ = (t', t' ^ 2) := ht'eq.symm
      rw [← this]; abel
    exact mem_filter.2 ⟨mem_univ t, minus_plus_quadratic t t' hδval⟩
  have hpos : #{t ∈ T | (t, t ^ 2) - δ ∈ S} ≤ 3 := by
    have hsplit :
        {t ∈ T | (t, t ^ 2) - δ ∈ S} ⊆
          {t ∈ T | (t, t ^ 2) - δ ∈ parabola T} ∪
            {t ∈ T | (t, t ^ 2) - δ ∈
              (parabola T).image fun p => -p} := by
      intro t ht
      rcases mem_filter.1 ht with ⟨htT, htS⟩
      have : (t, t ^ 2) - δ ∈ parabola T ∨
          (t, t ^ 2) - δ ∈ (parabola T).image fun p => -p :=
        mem_union.1 (by simpa [S, signedParabola] using htS)
      rcases this with h | h
      · exact mem_union.2 (Or.inl (mem_filter.2 ⟨htT, h⟩))
      · exact mem_union.2 (Or.inr (mem_filter.2 ⟨htT, h⟩))
    exact (card_le_card hsplit).trans
      ((card_union_le _ _).trans (add_le_add hposPP hposPM |>.trans (by decide)))
  have hneg : #{t ∈ T | (-t, -t ^ 2) - δ ∈ S} ≤ 3 := by
    have hsplit :
        {t ∈ T | (-t, -t ^ 2) - δ ∈ S} ⊆
          {t ∈ T | (-t, -t ^ 2) - δ ∈ parabola T} ∪
            {t ∈ T | (-t, -t ^ 2) - δ ∈
              (parabola T).image fun p => -p} := by
      intro t ht
      rcases mem_filter.1 ht with ⟨htT, htS⟩
      have : (-t, -t ^ 2) - δ ∈ parabola T ∨
          (-t, -t ^ 2) - δ ∈ (parabola T).image fun p => -p :=
        mem_union.1 (by simpa [S, signedParabola] using htS)
      rcases this with h | h
      · exact mem_union.2 (Or.inl (mem_filter.2 ⟨htT, h⟩))
      · exact mem_union.2 (Or.inr (mem_filter.2 ⟨htT, h⟩))
    exact (card_le_card hsplit).trans
      ((card_union_le _ _).trans (add_le_add hnegMP hnegMM |>.trans (by decide)))
  have hcover :
      {s ∈ S | s - δ ∈ S} ⊆
        (T.filter fun t => (t, t ^ 2) - δ ∈ S).image
            (fun t => ((t, t ^ 2) : ZMod q × ZMod q)) ∪
          (T.filter fun t => (-t, -t ^ 2) - δ ∈ S).image
            (fun t => ((-t, -t ^ 2) : ZMod q × ZMod q)) := by
    intro s hs
    rcases mem_filter.1 hs with ⟨hsS, hsδ⟩
    rcases mem_signedParabola.1 hsS with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · exact mem_union.2 (Or.inl (mem_image.2 ⟨t, mem_filter.2 ⟨ht, hsδ⟩, rfl⟩))
    · exact mem_union.2 (Or.inr (mem_image.2 ⟨t, mem_filter.2 ⟨ht, hsδ⟩, rfl⟩))
  refine (card_le_card hcover).trans ?_
  refine (card_union_le _ _).trans ?_
  refine add_le_add (card_image_le.trans hpos) (card_image_le.trans hneg) |>.trans ?_
  decide

/-- Number of `S_R`-neighbours of `u` in `P`. Paper `D(u)`. -/
def seedDegree (P : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q))
    (u : ZMod q × ZMod q) : ℕ :=
  #{p ∈ P | p - u ∈ signedParabola T}

lemma seedDegree_eq_sum (P : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q))
    (u : ZMod q × ZMod q) :
    seedDegree P T u =
      ∑ p ∈ P, if p - u ∈ signedParabola T then 1 else 0 := by
  classical
  simp [seedDegree, sum_boole]

lemma card_common_seed (T : Finset (ZMod q))
    (p p' : ZMod q × ZMod q) :
    #{u : ZMod q × ZMod q | p - u ∈ signedParabola T ∧
        p' - u ∈ signedParabola T} =
      #{s ∈ signedParabola T | s - (p - p') ∈ signedParabola T} := by
  classical
  set S := signedParabola T
  have himg :
      ((univ.filter fun u : ZMod q × ZMod q =>
          p - u ∈ S ∧ p' - u ∈ S).image fun u => p - u) =
        S.filter fun s => s - (p - p') ∈ S := by
    ext s
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨u, ⟨hp, hp'⟩, rfl⟩
      refine ⟨hp, ?_⟩
      have : p - u - (p - p') = p' - u := by abel
      simpa [this] using hp'
    · intro ⟨hs, hs'⟩
      refine ⟨p - s, ?_, by abel⟩
      have hp : p - (p - s) ∈ S := by simpa using hs
      have hp' : p' - (p - s) ∈ S := by
        have : p' - (p - s) = s - (p - p') := by abel
        simpa [this] using hs'
      exact ⟨hp, hp'⟩
  have hinj :
      ((univ.filter fun u : ZMod q × ZMod q =>
          p - u ∈ S ∧ p' - u ∈ S).image fun u => p - u).card =
        (univ.filter fun u : ZMod q × ZMod q =>
          p - u ∈ S ∧ p' - u ∈ S).card :=
    card_image_of_injective _ fun a b h => sub_right_inj.mp h
  simpa [S, himg] using hinj.symm

/-- Sidon Cauchy--Schwarz: `∑_u D(u)² ≤ |S_R| |P| + 6 |P|(|P|-1)`.
This is `O(d|P|+|P|²)`, not `o(|P|²)` at the SOTA scale. -/
theorem seedDegree_sq_sum (P : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (hq : Odd q) :
    ∑ u : ZMod q × ZMod q, seedDegree P T u ^ 2 ≤
      #(signedParabola T) * #P + 6 * #P * (#P - 1) := by
  classical
  set S := signedParabola T
  have hsq : ∀ u,
      seedDegree P T u ^ 2 =
        ∑ p ∈ P, ∑ p' ∈ P,
          (if p - u ∈ S then 1 else 0) *
            (if p' - u ∈ S then 1 else 0) := fun u => by
    have hμ := seedDegree_eq_sum P T u
    have hmul :=
      sum_mul_sum (s := P) (t := P)
        (f := fun p => if p - u ∈ S then 1 else 0)
        (g := fun p' => if p' - u ∈ S then 1 else 0)
    rw [pow_two, hμ]
    exact hmul
  have hpair : ∀ p ∈ P, ∀ p' ∈ P,
      ∑ u : ZMod q × ZMod q,
          (if p - u ∈ S then 1 else 0) *
            (if p' - u ∈ S then 1 else 0) =
        #{s ∈ S | s - (p - p') ∈ S} := fun p _ p' _ => by
    have hite :
        ∑ u : ZMod q × ZMod q,
            (if p - u ∈ S then 1 else 0) *
              (if p' - u ∈ S then 1 else 0) =
          #{u : ZMod q × ZMod q | p - u ∈ S ∧ p' - u ∈ S} := by
      have hpt : ∀ u,
          (if p - u ∈ S then 1 else 0) *
              (if p' - u ∈ S then 1 else 0) =
            if p - u ∈ S ∧ p' - u ∈ S then 1 else 0 := fun u => by
        by_cases hp : p - u ∈ S <;> by_cases hp' : p' - u ∈ S <;>
          simp [hp, hp']
      rw [sum_congr rfl fun u _ => hpt u]
      simp [sum_boole]
    rw [hite, card_common_seed]
  have hsum :
      ∑ u : ZMod q × ZMod q, seedDegree P T u ^ 2 =
        ∑ p ∈ P, ∑ p' ∈ P, #{s ∈ S | s - (p - p') ∈ S} := by
    calc
      ∑ u, seedDegree P T u ^ 2
          = ∑ u, ∑ p ∈ P, ∑ p' ∈ P,
              (if p - u ∈ S then 1 else 0) *
                (if p' - u ∈ S then 1 else 0) :=
            sum_congr rfl fun u _ => hsq u
      _ = ∑ p ∈ P, ∑ p' ∈ P, ∑ u,
            (if p - u ∈ S then 1 else 0) *
              (if p' - u ∈ S then 1 else 0) := by
          rw [sum_comm]
          refine sum_congr rfl fun p _ => ?_
          rw [sum_comm]
      _ = ∑ p ∈ P, ∑ p' ∈ P, #{s ∈ S | s - (p - p') ∈ S} :=
            sum_congr rfl fun p hp =>
              sum_congr rfl fun p' hp' => hpair p hp p' hp'
  have hdiag : ∀ p ∈ P,
      #{s ∈ S | s - (p - p) ∈ S} = #S := fun p _ => by
    simp [S, sub_self]
  have hoff : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' →
      #{s ∈ S | s - (p - p') ∈ S} ≤ 6 := fun p _ p' _ hne =>
    signedParabola_codegree (T := T) hq (sub_ne_zero.2 hne)
  have hpt : ∀ p ∈ P,
      ∑ p' ∈ P, #{s ∈ S | s - (p - p') ∈ S} ≤
        #S + 6 * (#P - 1) := fun p hp => by
    have hsum' :
        ∑ p' ∈ P, #{s ∈ S | s - (p - p') ∈ S} =
          #{s ∈ S | s - (p - p) ∈ S} +
            ∑ p' ∈ P.erase p, #{s ∈ S | s - (p - p') ∈ S} :=
      (sum_erase_add (s := P) (a := p)
        (fun p' => #{s ∈ S | s - (p - p') ∈ S}) hp).symm.trans
        (add_comm _ _)
    have hrest :
        ∑ p' ∈ P.erase p, #{s ∈ S | s - (p - p') ∈ S} ≤
          6 * #(P.erase p) := by
      refine (sum_le_sum fun p' hp' =>
        hoff p hp p' (mem_of_mem_erase hp') (ne_of_mem_erase hp').symm).trans_eq ?_
      simp [sum_const, smul_eq_mul, mul_comm]
    have herase : #(P.erase p) = #P - 1 := card_erase_of_mem hp
    calc
      ∑ p' ∈ P, #{s ∈ S | s - (p - p') ∈ S}
          = #S + ∑ p' ∈ P.erase p, #{s ∈ S | s - (p - p') ∈ S} := by
            rw [hsum', hdiag p hp]
      _ ≤ #S + 6 * #(P.erase p) := Nat.add_le_add_left hrest _
      _ = #S + 6 * (#P - 1) := by rw [herase]
  have hsplit :
      ∑ p ∈ P, ∑ p' ∈ P, #{s ∈ S | s - (p - p') ∈ S} ≤
        #S * #P + 6 * #P * (#P - 1) := by
    calc
      ∑ p ∈ P, ∑ p' ∈ P, #{s ∈ S | s - (p - p') ∈ S}
          ≤ ∑ p ∈ P, (#S + 6 * (#P - 1)) := sum_le_sum hpt
      _ = #P * (#S + 6 * (#P - 1)) := by
            simp [sum_const, smul_eq_mul, mul_comm]
      _ = #S * #P + 6 * #P * (#P - 1) := by ring
  exact hsum.trans_le hsplit

end R3tBound
