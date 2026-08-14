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

lemma coverageMass_eq_sum (A : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q))
    (x : ZMod q) :
    coverageMass A T x = ∑ t ∈ T, #(shiftedFibre A x t) := by
  classical
  unfold coverageMass multiplicity
  have h : ∀ y, #{i ∈ T | y ∈ shiftedFibre A x i} =
      ∑ i ∈ T, if y ∈ shiftedFibre A x i then 1 else 0 := fun y => by
    simp [sum_boole]
  simp_rw [h]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  simp

/-- Points whose multiplicity is at least half the mean energy per unit mass. -/
def popularCore (A : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q)) (x : ZMod q) :
    Finset (ZMod q) :=
  univ.filter fun y =>
    familyEnergy A T x ≤
      2 * coverageMass A T x * multiplicity (shiftedFibre A x) T y

lemma mem_popularCore {A : Finset (ZMod q × ZMod q)} {T : Finset (ZMod q)}
    {x y : ZMod q} :
    y ∈ popularCore A T x ↔
      familyEnergy A T x ≤
        2 * coverageMass A T x * multiplicity (shiftedFibre A x) T y := by
  simp [popularCore]

/-- Energy is at most `#T` times neighbouring mass, since each multiplicity
is at most `#T`. -/
lemma energy_le_card_mul_mass (A : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q))
    (x : ZMod q) :
    familyEnergy A T x ≤ #T * coverageMass A T x := by
  classical
  set μ := multiplicity (shiftedFibre A x) T
  have hμ : ∀ y, μ y ≤ #T := fun y => card_filter_le _ _
  calc
    familyEnergy A T x = ∑ y : ZMod q, μ y ^ 2 := rfl
    _ ≤ ∑ y : ZMod q, #T * μ y :=
      sum_le_sum fun y _ => by
        simpa [pow_two, mul_comm] using Nat.mul_le_mul_left (μ y) (hμ y)
    _ = #T * ∑ y : ZMod q, μ y := by simp [mul_sum]
    _ = #T * coverageMass A T x := by simp [coverageMass, μ]

/-- Points covered by at least half the neighbouring fibres. -/
def highMultiplicityCore (A : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q))
    (x : ZMod q) : Finset (ZMod q) :=
  univ.filter fun y => #T ≤ 2 * multiplicity (shiftedFibre A x) T y

lemma mem_highMultiplicityCore {A : Finset (ZMod q × ZMod q)}
    {T : Finset (ZMod q)} {x y : ZMod q} :
    y ∈ highMultiplicityCore A T x ↔
      #T ≤ 2 * multiplicity (shiftedFibre A x) T y := by
  simp [highMultiplicityCore]

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

/-- The popular core carries at least half the energy. -/
theorem popular_core_energy (A : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q))
    (x : ZMod q) (hW : 0 < coverageMass A T x) :
    familyEnergy A T x ≤
      2 * ∑ y ∈ popularCore A T x,
        (multiplicity (shiftedFibre A x) T y) ^ 2 := by
  classical
  set W := coverageMass A T x
  set E := familyEnergy A T x
  set μ := multiplicity (shiftedFibre A x) T
  set U := popularCore A T x
  have hEdef : E = ∑ y : ZMod q, μ y ^ 2 := rfl
  have hsplit : E = ∑ y ∈ U, μ y ^ 2 + ∑ y ∈ Uᶜ, μ y ^ 2 := by
    rw [hEdef, ← sum_add_sum_compl (s := U) (f := fun y => μ y ^ 2)]
  have hμW : ∑ y : ZMod q, μ y = W := by
    simp [W, coverageMass, μ]
  have hμWsplit : ∑ y ∈ U, μ y + ∑ y ∈ Uᶜ, μ y = W := by
    rw [← hμW, ← sum_add_sum_compl (s := U) (f := μ)]
  have hcompμ : ∑ y ∈ Uᶜ, μ y ≤ W := by omega
  by_cases hE0 : E = 0
  · have hCS : W ^ 2 ≤ #(T.biUnion (shiftedFibre A x)) * E := energy_cs A T x
    have hW0 : W = 0 := by
      have : W ^ 2 ≤ 0 := by simpa [hE0] using hCS
      exact (Nat.pow_eq_zero.mp (Nat.eq_zero_of_le_zero this)).1
    exact (Nat.lt_irrefl _ (hW0 ▸ hW)).elim
  · have hcomp : ∀ y ∈ Uᶜ, 2 * W * μ y < E := by
      intro y hy
      have : ¬ E ≤ 2 * W * μ y := by
        simpa [U, popularCore, mem_compl, μ, W, E] using hy
      exact Nat.not_le.1 this
    have hterm : ∀ y ∈ Uᶜ, 2 * W * (μ y) ^ 2 ≤ (E - 1) * μ y := by
      intro y hy
      have hle : 2 * W * μ y ≤ E - 1 :=
        Nat.le_sub_one_of_lt (hcomp y hy)
      have := Nat.mul_le_mul_right (μ y) hle
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
    have hsum : 2 * W * ∑ y ∈ Uᶜ, μ y ^ 2 ≤ (E - 1) * ∑ y ∈ Uᶜ, μ y := by
      calc
        2 * W * ∑ y ∈ Uᶜ, μ y ^ 2
            = ∑ y ∈ Uᶜ, 2 * W * (μ y) ^ 2 := by
              simp [mul_sum]
        _ ≤ ∑ y ∈ Uᶜ, (E - 1) * μ y := sum_le_sum hterm
        _ = (E - 1) * ∑ y ∈ Uᶜ, μ y := by simp [mul_sum]
    have hsum' : 2 * W * ∑ y ∈ Uᶜ, μ y ^ 2 ≤ (E - 1) * W :=
      hsum.trans (Nat.mul_le_mul_left _ hcompμ)
    have hhalf : 2 * ∑ y ∈ Uᶜ, μ y ^ 2 ≤ E - 1 := by
      have hre : 2 * W * ∑ y ∈ Uᶜ, μ y ^ 2 = (2 * ∑ y ∈ Uᶜ, μ y ^ 2) * W := by
        ac_rfl
      exact Nat.le_of_mul_le_mul_right (hre ▸ hsum') hW
    have : E ≤ 2 * ∑ y ∈ U, μ y ^ 2 := by
      have h2 : 2 * E = 2 * ∑ y ∈ U, μ y ^ 2 + 2 * ∑ y ∈ Uᶜ, μ y ^ 2 := by
        rw [hsplit, mul_add]
      have : 2 * E ≤ 2 * ∑ y ∈ U, μ y ^ 2 + (E - 1) := by
        rw [h2]; exact Nat.add_le_add_left hhalf _
      omega
    simpa [E, U, μ] using this

/-- Energy at least three-quarters of the `#T · W` maximum puts a quarter of
the energy on points of multiplicity at least `#T / 2`. This does not require
a lower bound on fibre size. -/
theorem three_quarters_energy_core (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (hW : 0 < coverageMass A T x)
    (hE : 3 * #T * coverageMass A T x ≤ 4 * familyEnergy A T x) :
    familyEnergy A T x ≤
      4 * ∑ y ∈ highMultiplicityCore A T x,
        (multiplicity (shiftedFibre A x) T y) ^ 2 := by
  classical
  set W := coverageMass A T x
  set E := familyEnergy A T x
  set μ := multiplicity (shiftedFibre A x) T
  set U := highMultiplicityCore A T x
  have hEdef : E = ∑ y : ZMod q, μ y ^ 2 := rfl
  have hsplit : E = ∑ y ∈ U, μ y ^ 2 + ∑ y ∈ Uᶜ, μ y ^ 2 := by
    rw [hEdef, ← sum_add_sum_compl (s := U) (f := fun y => μ y ^ 2)]
  have hμW : ∑ y : ZMod q, μ y = W := by
    simp [W, coverageMass, μ]
  have hcompμ : ∑ y ∈ Uᶜ, μ y ≤ W := by
    have : ∑ y ∈ U, μ y + ∑ y ∈ Uᶜ, μ y = W := by
      rw [← hμW, ← sum_add_sum_compl (s := U) (f := μ)]
    omega
  by_cases hTempty : T = ∅
  · have hW0 : W = 0 := by
      simp [W, coverageMass_eq_sum, hTempty]
    exact (Nat.lt_irrefl _ (hW0 ▸ hW)).elim
  · have hTpos : 0 < #T := card_pos.mpr (nonempty_iff_ne_empty.mpr hTempty)
    have hcomp : ∀ y ∈ Uᶜ, 2 * μ y < #T := by
      intro y hy
      have : ¬ #T ≤ 2 * μ y := by
        simpa [U, highMultiplicityCore, mem_compl, μ] using hy
      exact Nat.not_le.1 this
    have hterm : ∀ y ∈ Uᶜ, 2 * (μ y) ^ 2 ≤ (#T - 1) * μ y := by
      intro y hy
      have hle : 2 * μ y ≤ #T - 1 := Nat.le_sub_one_of_lt (hcomp y hy)
      have := Nat.mul_le_mul_right (μ y) hle
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
    have hsum : 2 * ∑ y ∈ Uᶜ, μ y ^ 2 ≤ (#T - 1) * ∑ y ∈ Uᶜ, μ y := by
      calc
        2 * ∑ y ∈ Uᶜ, μ y ^ 2
            = ∑ y ∈ Uᶜ, 2 * (μ y) ^ 2 := by
              simp [mul_sum]
        _ ≤ ∑ y ∈ Uᶜ, (#T - 1) * μ y := sum_le_sum hterm
        _ = (#T - 1) * ∑ y ∈ Uᶜ, μ y := by simp [mul_sum]
    have hsumW : 2 * ∑ y ∈ Uᶜ, μ y ^ 2 ≤ (#T - 1) * W :=
      hsum.trans (Nat.mul_le_mul_left _ hcompμ)
    have h12 : 9 * #T * W ≤ 12 * E := by
      calc
        9 * #T * W = 3 * (3 * #T * W) := by ring
        _ ≤ 3 * (4 * E) := Nat.mul_le_mul_left 3 hE
        _ = 12 * E := by ring
    have hcmp : 8 * (#T - 1) * W ≤ 9 * #T * W := by
      have : 8 * (#T - 1) ≤ 9 * #T := by
        have := hTpos
        omega
      exact Nat.mul_le_mul_right W this
    have h8 : 8 * (#T - 1) * W ≤ 12 * E := hcmp.trans h12
    have hgoal : 2 * (#T - 1) * W ≤ 3 * E := by
      have : 4 * (2 * (#T - 1) * W) ≤ 4 * (3 * E) := by
        convert h8 using 1 <;> ring
      exact Nat.le_of_mul_le_mul_left this (by decide : 0 < 4)
    have hcompE : 4 * ∑ y ∈ Uᶜ, μ y ^ 2 ≤ 3 * E := by
      have h4 : 4 * ∑ y ∈ Uᶜ, μ y ^ 2 ≤ 2 * (#T - 1) * W := by
        have := Nat.mul_le_mul_left 2 hsumW
        convert this using 1 <;> ring
      exact h4.trans hgoal
    have : E ≤ 4 * ∑ y ∈ U, μ y ^ 2 := by
      have h4 : 4 * E = 4 * ∑ y ∈ U, μ y ^ 2 + 4 * ∑ y ∈ Uᶜ, μ y ^ 2 := by
        rw [hsplit, mul_add]
      have : 4 * E ≤ 4 * ∑ y ∈ U, μ y ^ 2 + 3 * E := by
        rw [h4]; exact Nat.add_le_add_left hcompE _
      omega
    simpa [E, U, μ] using this

end R3tBound
