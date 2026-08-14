/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Chebyshev
import R3tBound.TightInterval

/-!
# Coverage, energy, and mixing

Energy is defined as the second moment of fibre multiplicity. A strictly
mixing fibre is empty once the neighbouring mass is at least `q`.
-/

namespace R3tBound

open Finset

variable {q : ℕ} [Fact q.Prime]

set_option linter.unusedSectionVars false

/-- The parabolically shifted fibre `A_t = B_{x+t} - t²`. -/
def shiftedFibre (A : Finset (ZMod q × ZMod q)) (x t : ZMod q) : Finset (ZMod q) :=
  (fibreF A (x + t)).image (fun y => y - t ^ 2)

lemma card_shiftedFibre (A : Finset (ZMod q × ZMod q)) (x t : ZMod q) :
    #(shiftedFibre A x t) = #(fibreF A (x + t)) :=
  card_image_of_injective _ (fun a b h => by simpa using h)

lemma mem_shiftedFibre {A : Finset (ZMod q × ZMod q)} {x t y : ZMod q} :
    y ∈ shiftedFibre A x t ↔ (x + t, y + t ^ 2) ∈ A := by
  simp [shiftedFibre, mem_fibreF, sub_eq_iff_eq_add]

/-- Neighbouring fibres, after the parabolic shift, miss `B_x`. -/
lemma shiftedFibre_disjoint_base {T : Finset (ZMod q)}
    {A : Finset (ZMod q × ZMod q)} {x t : ZMod q}
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q)))
    (hT0 : 0 ∉ T) (ht : t ∈ T) :
    Disjoint (fibreF A x) (shiftedFibre A x t) := by
  refine disjoint_left.2 ?_
  intro y hy hy'
  have hyA : (x + t, y + t ^ 2) ∈ A := mem_shiftedFibre.1 hy'
  have hin :
      y + t ^ 2 ∈
        fibre (A : Set (ZMod q × ZMod q)) (x + t) ∩
          shift (fibre (A : Set (ZMod q × ZMod q)) x) (t ^ 2) := by
    refine ⟨mem_fibre.2 hyA, ?_⟩
    exact (mem_shift (B := fibre (A : Set (ZMod q × ZMod q)) x)
      (c := t ^ 2) (y := y + t ^ 2)).2
      (by simpa [mem_fibre, add_sub_cancel_right] using (mem_fibreF.1 hy))
  exact (Set.eq_empty_iff_forall_notMem.1
    (fibre_constraint (A := (A : Set (ZMod q × ZMod q)))
      (x := x) (t := t) hA hT0 ht)) _ hin

/-- Multiplicity of a residue in a family of subsets. -/
def multiplicity {ι : Type*} (F : ι → Finset (ZMod q)) (s : Finset ι) (y : ZMod q) : ℕ :=
  #{i ∈ s | y ∈ F i}

lemma multiplicity_eq_zero_outside {ι : Type*}
    (F : ι → Finset (ZMod q)) (s : Finset ι) {y : ZMod q}
    (hy : y ∉ s.biUnion F) : multiplicity F s y = 0 := by
  simp only [multiplicity, card_eq_zero, filter_eq_empty_iff]
  intro i hi hF
  exact hy (mem_biUnion.2 ⟨i, hi, hF⟩)

/-- Neighbouring mass at `x`, as the first moment of multiplicity. -/
def coverageMass (A : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q)) (x : ZMod q) : ℕ :=
  ∑ y : ZMod q, multiplicity (shiftedFibre A x) T y

/-- Pairwise fibre energy at `x`, as the second moment of multiplicity. -/
def familyEnergy (A : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q)) (x : ZMod q) : ℕ :=
  ∑ y : ZMod q, (multiplicity (shiftedFibre A x) T y) ^ 2

lemma coverage_le_of_independent {T : Finset (ZMod q)}
    {A : Finset (ZMod q × ZMod q)} {x : ZMod q}
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q)))
    (hT0 : 0 ∉ T) :
    #(fibreF A x) + #(T.biUnion (shiftedFibre A x)) ≤ q := by
  have hdisj : ∀ t ∈ T, Disjoint (fibreF A x) (shiftedFibre A x t) :=
    fun t ht => shiftedFibre_disjoint_base hA hT0 ht
  have hU : Disjoint (fibreF A x) (T.biUnion (shiftedFibre A x)) :=
    (disjoint_biUnion_right (fibreF A x) T (shiftedFibre A x)).2 hdisj
  have huniv : #(fibreF A x ∪ T.biUnion (shiftedFibre A x)) ≤ q := by
    simpa [ZMod.card] using
      card_le_univ (fibreF A x ∪ T.biUnion (shiftedFibre A x))
  simpa [card_union_of_disjoint hU] using huniv

lemma energy_cs (A : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q)) (x : ZMod q) :
    (coverageMass A T x) ^ 2 ≤
      #(T.biUnion (shiftedFibre A x)) * familyEnergy A T x := by
  classical
  set U := T.biUnion (shiftedFibre A x)
  have hμ : coverageMass A T x = ∑ y ∈ U, multiplicity (shiftedFibre A x) T y := by
    have h0 : ∑ y ∈ Uᶜ, multiplicity (shiftedFibre A x) T y = 0 :=
      sum_eq_zero fun y hy => multiplicity_eq_zero_outside _ _ (mem_compl.1 hy)
    have hsplit := sum_add_sum_compl U (f := multiplicity (shiftedFibre A x) T)
    rw [coverageMass, ← hsplit, h0, add_zero]
  have hμ2 : familyEnergy A T x = ∑ y ∈ U, (multiplicity (shiftedFibre A x) T y) ^ 2 := by
    have h0 : ∑ y ∈ Uᶜ, (multiplicity (shiftedFibre A x) T y) ^ 2 = 0 :=
      sum_eq_zero fun y hy => by
        simp [multiplicity_eq_zero_outside _ _ (mem_compl.1 hy)]
    have hsplit := sum_add_sum_compl U
      (f := fun y => (multiplicity (shiftedFibre A x) T y) ^ 2)
    rw [familyEnergy, ← hsplit, h0, add_zero]
  have hCS := sq_sum_le_card_mul_sum_sq (s := U) (f := multiplicity (shiftedFibre A x) T)
  simpa [hμ, hμ2] using hCS

/-- Strict mixing: energy at most random and neighbouring mass `≥ q` force an empty fibre. -/
theorem strict_mixing_empty {T : Finset (ZMod q)}
    {A : Finset (ZMod q × ZMod q)} {x : ZMod q}
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q)))
    (hT0 : 0 ∉ T)
    (hE : familyEnergy A T x * q ≤ (coverageMass A T x) ^ 2)
    (hW : q ≤ coverageMass A T x) :
    fibreF A x = ∅ := by
  set W := coverageMass A T x
  set E := familyEnergy A T x
  set U := T.biUnion (shiftedFibre A x)
  have hCS : W ^ 2 ≤ #U * E := energy_cs A T x
  have hcov : #(fibreF A x) + #U ≤ q :=
    coverage_le_of_independent (A := A) (T := T) (x := x) hA hT0
  have hW' : q ≤ W := hW
  by_cases hE0 : E = 0
  · have hpow : W ^ 2 ≤ 0 := by simpa [hE0] using hCS
    have hW0 : W = 0 := (Nat.pow_eq_zero.mp (Nat.eq_zero_of_le_zero hpow)).1
    have hq0 : q ≤ 0 := hW'.trans_eq hW0
    have hqpos : 0 < q := (Fact.out : Nat.Prime q).pos
    exact (Nat.not_lt.2 hq0 hqpos).elim
  · have hEq : E * q ≤ W ^ 2 := hE
    have : E * q ≤ #U * E := hEq.trans hCS
    have hUq : q ≤ #U :=
      Nat.le_of_mul_le_mul_left (by simpa [mul_comm E] using this)
        (Nat.pos_of_ne_zero hE0)
    exact card_eq_zero.mp (by omega)

end R3tBound
