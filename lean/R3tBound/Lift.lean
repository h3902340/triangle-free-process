/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import R3tBound.Basic

/-!
# Lift lemma
-/

namespace R3tBound

open Finset

set_option linter.unusedSectionVars false

variable {q : ℕ} [Fact q.Prime]

/-- Red adjacency in `G₂`. -/
def RedAdj (T : Finset (ZMod q)) {ℓ : ℕ}
    (u v : (ZMod q × ZMod q) × Fin ℓ) : Prop :=
  u ≠ v ∧ u.1 - v.1 ∈ signedParabola T

def IsRedIndependent (T : Finset (ZMod q)) {ℓ : ℕ}
    (I : Set ((ZMod q × ZMod q) × Fin ℓ)) : Prop :=
  ∀ ⦃u v : (ZMod q × ZMod q) × Fin ℓ⦄, u ∈ I → v ∈ I → ¬ RedAdj T u v

def projR {ℓ : ℕ} (I : Set ((ZMod q × ZMod q) × Fin ℓ)) :
    Set (ZMod q × ZMod q) :=
  Prod.fst '' I

theorem projR_independent {T : Finset (ZMod q)} {ℓ : ℕ}
    {I : Set ((ZMod q × ZMod q) × Fin ℓ)}
    (hI : IsRedIndependent T I) :
    IsSeedIndependent T (projR I) := by
  intro p r hp hr hne hdiff
  rcases hp with ⟨u, hu, rfl⟩
  rcases hr with ⟨v, hv, rfl⟩
  exact hI hu hv ⟨fun h => hne (congrArg Prod.fst h), hdiff⟩

lemma card_le_mul_card_image_fst {ℓ : ℕ}
    (I : Finset ((ZMod q × ZMod q) × Fin ℓ)) :
    #I ≤ ℓ * #(I.image Prod.fst) := by
  have hsub : I ⊆ (I.image Prod.fst) ×ˢ (univ : Finset (Fin ℓ)) := by
    intro p hp
    exact mem_product.2 ⟨mem_image_of_mem _ hp, mem_univ _⟩
  have hle := card_le_card hsub
  have hprod : #((I.image Prod.fst) ×ˢ (univ : Finset (Fin ℓ))) =
      ℓ * #(I.image Prod.fst) := by
    rw [card_product, card_univ, Fintype.card_fin, mul_comm]
  exact hle.trans hprod.le

theorem lift_card {T : Finset (ZMod q)} {ℓ : ℕ}
    {I : Finset ((ZMod q × ZMod q) × Fin ℓ)}
    (hI : IsRedIndependent T (I : Set ((ZMod q × ZMod q) × Fin ℓ))) :
    #I ≤ ℓ * #(I.image Prod.fst) ∧
      IsSeedIndependent T (I.image Prod.fst : Set (ZMod q × ZMod q)) := by
  refine ⟨card_le_mul_card_image_fst I, ?_⟩
  have := projR_independent (I := (I : Set ((ZMod q × ZMod q) × Fin ℓ))) hI
  simpa [projR] using this

end R3tBound
