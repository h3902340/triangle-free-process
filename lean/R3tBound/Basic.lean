/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Basic

/-!
# Seed Cayley graph on the truncated parabola
-/

namespace R3tBound

open Finset

variable {q : ℕ} [Fact q.Prime]

/-- The (unsigned) truncated parabola `{ (t, t²) | t ∈ T }`. -/
def parabola (T : Finset (ZMod q)) : Finset (ZMod q × ZMod q) :=
  T.image fun t => (t, t ^ 2)

/-- The signed connection set `S_R = ±{(t, t²) : t ∈ T}`. -/
def signedParabola (T : Finset (ZMod q)) : Finset (ZMod q × ZMod q) :=
  parabola T ∪ (parabola T).image fun p => -p

lemma mem_signedParabola {T : Finset (ZMod q)} {p : ZMod q × ZMod q} :
    p ∈ signedParabola T ↔
      (∃ t ∈ T, p = (t, t ^ 2)) ∨ (∃ t ∈ T, p = (-t, -t ^ 2)) := by
  simp only [signedParabola, parabola, mem_union, mem_image]
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨p', ⟨t, ht, rfl⟩, rfl⟩)
    · exact Or.inl ⟨t, ht, rfl⟩
    · exact Or.inr ⟨t, ht, by simp⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact Or.inl ⟨t, ht, rfl⟩
    · exact Or.inr ⟨(t, t ^ 2), ⟨t, ht, rfl⟩, by simp⟩

lemma zero_notMem_signedParabola {T : Finset (ZMod q)} (hT : 0 ∉ T) :
    ((0, 0) : ZMod q × ZMod q) ∉ signedParabola T := by
  intro hp
  rcases mem_signedParabola.1 hp with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
  · have ht0 : t = 0 := by
      apply_fun Prod.fst at h
      simpa using h.symm
    exact hT (ht0 ▸ ht)
  · have ht0 : t = 0 := by
      apply_fun Prod.fst at h
      have : -t = 0 := by simpa using h.symm
      exact neg_eq_zero.1 this
    exact hT (ht0 ▸ ht)

/-- A set `A ⊆ 𝔽_q²` is independent in `G_R = Cay(𝔽_q², S_R)`. -/
def IsSeedIndependent (T : Finset (ZMod q)) (A : Set (ZMod q × ZMod q)) : Prop :=
  ∀ ⦃p r : ZMod q × ZMod q⦄, p ∈ A → r ∈ A → p ≠ r → p - r ∉ signedParabola T

/-- The vertical fibre of `A` over the first coordinate `x`. -/
def fibre (A : Set (ZMod q × ZMod q)) (x : ZMod q) : Set (ZMod q) :=
  {y | (x, y) ∈ A}

set_option linter.unusedSectionVars false

lemma mem_fibre {A : Set (ZMod q × ZMod q)} {x y : ZMod q} :
    y ∈ fibre A x ↔ (x, y) ∈ A :=
  Iff.rfl

/-- Translation of a fibre by `c`. -/
def shift (B : Set (ZMod q)) (c : ZMod q) : Set (ZMod q) :=
  (fun y => y + c) '' B

lemma mem_shift {B : Set (ZMod q)} {c y : ZMod q} :
    y ∈ shift B c ↔ y - c ∈ B := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa
  · intro hy
    exact ⟨y - c, hy, by simp⟩

end R3tBound
