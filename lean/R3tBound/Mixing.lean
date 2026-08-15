/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Chebyshev
import R3tBound.TightInterval

/-!
# Coverage, energy, and mixing

Energy is defined as the second moment of fibre multiplicity, equivalently
the sum of pairwise shifted-fibre intersections. A strictly mixing fibre
is empty once the neighbouring mass is at least `q`. High energy forces
a heavy pair. Two-thirds energy on medium fibres forces
`Ω(|T|²)` heavy pairs and therefore a star; that is structure, not a
size bound.
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

/-- `1` if `y` lies in `s`, else `0`. Written as a `ℕ`-valued function so
the `if` cannot be parsed as a `Prop`-valued term. -/
def memOne (s : Finset (ZMod q)) (y : ZMod q) : ℕ :=
  if y ∈ s then 1 else 0

lemma memOne_mul (s t : Finset (ZMod q)) (y : ZMod q) :
    memOne s y * memOne t y = memOne (s ∩ t) y := by
  unfold memOne
  by_cases hs : y ∈ s <;> by_cases ht : y ∈ t <;> simp [hs, ht]

lemma sum_memOne_card (S : Finset (ZMod q)) :
    ∑ y ∈ univ, memOne S y = #S := by
  unfold memOne
  have hfilter : univ.filter (fun y => y ∈ S) = S := by
    ext y
    simp
  rw [sum_ite, hfilter, sum_const, smul_eq_mul, mul_one, sum_const_zero, add_zero]

/-- Energy is the sum of pairwise shifted-fibre intersections. -/
lemma familyEnergy_eq_pairwise (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q) :
    familyEnergy A T x =
      ∑ t ∈ T, ∑ t' ∈ T,
        #(shiftedFibre A x t ∩ shiftedFibre A x t') := by
  classical
  set F := shiftedFibre A x
  set μ := multiplicity F T
  have hμ : ∀ y, μ y = ∑ t ∈ T, memOne (F t) y := fun y => by
    simp [μ, multiplicity, memOne, sum_boole]
  have hsq : ∀ y, μ y ^ 2 =
      ∑ t ∈ T, ∑ t' ∈ T, memOne (F t ∩ F t') y := fun y => by
    have hmul :=
      sum_mul_sum (s := T) (t := T)
        (f := fun t => memOne (F t) y)
        (g := fun t' => memOne (F t') y)
    have : μ y * μ y =
        ∑ t ∈ T, ∑ t' ∈ T, memOne (F t) y * memOne (F t') y := by
      simpa [hμ] using hmul
    rw [pow_two]
    convert this using 1
    refine sum_congr rfl fun t _ => sum_congr rfl fun t' _ =>
      (memOne_mul (F t) (F t') y).symm
  calc
    familyEnergy A T x = ∑ y : ZMod q, μ y ^ 2 := rfl
    _ = ∑ y : ZMod q, ∑ t ∈ T, ∑ t' ∈ T, memOne (F t ∩ F t') y :=
        sum_congr rfl fun y _ => hsq y
    _ = ∑ t ∈ T, ∑ t' ∈ T, ∑ y : ZMod q, memOne (F t ∩ F t') y := by
        rw [sum_comm]
        refine sum_congr rfl fun t _ => sum_comm
    _ = ∑ t ∈ T, ∑ t' ∈ T, #(F t ∩ F t') := by
        refine sum_congr rfl fun t _ => sum_congr rfl fun t' _ => ?_
        simpa using sum_memOne_card (F t ∩ F t')

/-- Off-diagonal energy is total energy minus neighbouring mass. -/
lemma familyEnergy_off_diag (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q) :
    familyEnergy A T x =
      coverageMass A T x +
        ∑ t ∈ T, ∑ t' ∈ T.filter (· ≠ t),
          #(shiftedFibre A x t ∩ shiftedFibre A x t') := by
  classical
  set F := shiftedFibre A x
  have hsplit : ∀ t ∈ T,
      ∑ t' ∈ T, #(F t ∩ F t') =
        #(F t) + ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') := fun t ht => by
    have hpart :=
      (sum_filter_add_sum_filter_not T (· = t) (fun t' => #(F t ∩ F t'))).symm
    have hsing : T.filter (· = t) = {t} := by
      ext t'
      constructor
      · intro ht'
        exact mem_singleton.2 (mem_filter.1 ht').2
      · intro ht'
        exact mem_filter.2 ⟨(mem_singleton.1 ht') ▸ ht, mem_singleton.1 ht'⟩
    have hinter : F t ∩ F t = F t := inter_eq_left.mpr fun _ hy => hy
    calc
      ∑ t' ∈ T, #(F t ∩ F t')
          = ∑ t' ∈ T.filter (· = t), #(F t ∩ F t') +
              ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') := hpart
      _ = #(F t) + ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') := by
            simp [hsing, hinter]
  calc
    familyEnergy A T x
        = ∑ t ∈ T, ∑ t' ∈ T, #(F t ∩ F t') := familyEnergy_eq_pairwise A T x
    _ = ∑ t ∈ T, (#(F t) + ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t')) :=
          sum_congr rfl hsplit
    _ = (∑ t ∈ T, #(F t)) +
          ∑ t ∈ T, ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') := by
        simp [sum_add_distrib]
    _ = coverageMass A T x +
          ∑ t ∈ T, ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') := by
        rw [coverageMass_eq_sum]

/-- `#(A \ B) = #A - #(A ∩ B)`. -/
lemma card_sdiff_eq_card_sub_inter {α : Type*} [DecidableEq α]
    (A B : Finset α) : #(A \ B) = #A - #(A ∩ B) := by
  have : #(A ∩ B) + #(A \ B) = #A := card_inter_add_card_sdiff A B
  omega

/-- The total off-diagonal fringe is `#T · W - E`. High energy makes
the average fringe small. -/
lemma sum_sdiff_off_diag (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q) :
    ∑ t ∈ T, ∑ t' ∈ T.filter (· ≠ t),
        #(shiftedFibre A x t \ shiftedFibre A x t') =
      #T * coverageMass A T x - familyEnergy A T x := by
  classical
  set F := shiftedFibre A x
  set W := coverageMass A T x
  set E := familyEnergy A T x
  have hsplit : E = W + ∑ t ∈ T, ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') :=
    familyEnergy_off_diag A T x
  have hEoff :
      ∑ t ∈ T, ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') = E - W := by
    omega
  have hcard : ∀ t ∈ T, #(T.filter (· ≠ t)) = #T - 1 := fun t ht => by
    have hsub : T.filter (· ≠ t) ⊆ T.erase t := by
      intro t' ht'
      exact mem_erase.2 ⟨(mem_filter.1 ht').2, (mem_filter.1 ht').1⟩
    have hsup : T.erase t ⊆ T.filter (· ≠ t) := by
      intro t' ht'
      exact mem_filter.2 ⟨(mem_erase.1 ht').2, (mem_erase.1 ht').1⟩
    simp [Subset.antisymm hsub hsup, card_erase_of_mem ht]
  have hpt : ∀ t ∈ T,
      ∑ t' ∈ T.filter (· ≠ t), #(F t \ F t') =
        (#T - 1) * #(F t) -
          ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') := fun t ht => by
    have hle : ∀ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') ≤ #(F t) :=
      fun t' _ => card_le_card inter_subset_left
    have hsub :
        ∑ t' ∈ T.filter (· ≠ t), #(F t \ F t') =
          ∑ t' ∈ T.filter (· ≠ t), (#(F t) - #(F t ∩ F t')) :=
      sum_congr rfl fun t' _ => card_sdiff_eq_card_sub_inter (F t) (F t')
    have htsub :=
      sum_tsub_distrib (s := T.filter (· ≠ t))
        (f := fun _ => #(F t)) (g := fun t' => #(F t ∩ F t')) hle
    have hconst :
        ∑ t' ∈ T.filter (· ≠ t), #(F t) = (#T - 1) * #(F t) := by
      simp [sum_const, smul_eq_mul, hcard t ht]
    rw [hsub, htsub, hconst]
  have hle2 : ∀ t ∈ T,
      ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') ≤ (#T - 1) * #(F t) :=
    fun t ht => by
      have hle : ∀ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') ≤ #(F t) :=
        fun t' _ => card_le_card inter_subset_left
      calc
        ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t')
            ≤ ∑ t' ∈ T.filter (· ≠ t), #(F t) := sum_le_sum hle
        _ = (#T - 1) * #(F t) := by
              simp [sum_const, smul_eq_mul, hcard t ht]
  have hsum :=
    sum_tsub_distrib (s := T)
      (f := fun t => (#T - 1) * #(F t))
      (g := fun t => ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t')) hle2
  have hW : ∑ t ∈ T, (#T - 1) * #(F t) = (#T - 1) * W := by
    simp [F, W, coverageMass_eq_sum, mul_sum]
  have hEW : W ≤ E := by omega
  have hWE : E ≤ #T * W := energy_le_card_mul_mass A T x
  have hlast : (#T - 1) * W - (E - W) = #T * W - E := by
    by_cases hTempty : T = ∅
    · have hW0 : W = 0 := by simp [W, coverageMass_eq_sum, hTempty]
      have hE0 : E = 0 := by
        simp [E, familyEnergy, multiplicity, hTempty]
      simp [hW0, hE0]
    · have hTpos : 1 ≤ #T := card_pos.mpr (nonempty_iff_ne_empty.mpr hTempty)
      have hadd : (#T - 1) * W + W = #T * W := by
        calc
          (#T - 1) * W + W = (#T - 1) * W + 1 * W := by rw [one_mul]
          _ = (#T - 1 + 1) * W := (add_mul _ _ W).symm
          _ = #T * W := by rw [Nat.sub_add_cancel hTpos]
      omega
  calc
    ∑ t ∈ T, ∑ t' ∈ T.filter (· ≠ t), #(F t \ F t')
        = ∑ t ∈ T, ((#T - 1) * #(F t) -
            ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t')) :=
          sum_congr rfl hpt
    _ = ∑ t ∈ T, (#T - 1) * #(F t) -
          ∑ t ∈ T, ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') := hsum
    _ = (#T - 1) * W - (E - W) := by rw [hW, hEoff]
    _ = #T * W - E := hlast

/-- If every off-diagonal intersection is at most `B`, energy is at most
`W + B · #T · (#T-1)`. Contrapositively, larger energy forces a heavy pair. -/
lemma exists_heavy_off_diag_pair {B : ℕ}
    (A : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q)) (x : ZMod q)
    (hE : coverageMass A T x + B * #T * (#T - 1) < familyEnergy A T x) :
    ∃ t ∈ T, ∃ t' ∈ T, t ≠ t' ∧
      B < #(shiftedFibre A x t ∩ shiftedFibre A x t') := by
  classical
  set F := shiftedFibre A x
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have hle : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
      #(F t ∩ F t') ≤ B := fun t ht t' ht' hne => h t ht t' ht' hne
  have hsum :
      ∑ t ∈ T, ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') ≤
        B * #T * (#T - 1) := by
    have hterm : ∀ t ∈ T,
        ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') ≤ B * (#T - 1) := fun t ht => by
      have hcard : #(T.filter (· ≠ t)) ≤ #T - 1 := by
        have : T.filter (· ≠ t) ⊆ T.erase t := by
          intro t' ht'
          exact mem_erase.2 ⟨(mem_filter.1 ht').2, (mem_filter.1 ht').1⟩
        have : #(T.filter (· ≠ t)) ≤ #(T.erase t) := card_le_card this
        simpa [card_erase_of_mem ht] using this
      have hpt : ∀ t' ∈ T.filter (· ≠ t), #(F t ∩ F t') ≤ B := fun t' ht' =>
        hle t ht t' (mem_filter.1 ht').1 (mem_filter.1 ht').2.symm
      calc
        ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t')
            ≤ ∑ t' ∈ T.filter (· ≠ t), B := sum_le_sum hpt
        _ = B * #(T.filter (· ≠ t)) := by simp [sum_const, smul_eq_mul, mul_comm]
        _ ≤ B * (#T - 1) := Nat.mul_le_mul_left B hcard
    calc
      ∑ t ∈ T, ∑ t' ∈ T.filter (· ≠ t), #(F t ∩ F t')
          ≤ ∑ t ∈ T, B * (#T - 1) := sum_le_sum hterm
      _ = B * (#T - 1) * #T := by simp [sum_const, smul_eq_mul, mul_comm, mul_left_comm]
      _ = B * #T * (#T - 1) := by ring
  have : familyEnergy A T x ≤ coverageMass A T x + B * #T * (#T - 1) := by
    rw [familyEnergy_off_diag]
    exact Nat.add_le_add_left hsum _
  exact Nat.not_lt.2 this hE

/-- Points covered by at least half the neighbouring fibres. -/
def highMultiplicityCore (A : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q))
    (x : ZMod q) : Finset (ZMod q) :=
  univ.filter fun y => #T ≤ 2 * multiplicity (shiftedFibre A x) T y

lemma mem_highMultiplicityCore {A : Finset (ZMod q × ZMod q)}
    {T : Finset (ZMod q)} {x y : ZMod q} :
    y ∈ highMultiplicityCore A T x ↔
      #T ≤ 2 * multiplicity (shiftedFibre A x) T y := by
  simp [highMultiplicityCore]

/-- The high-multiplicity core has size at most `4E / #T²`. -/
lemma high_multiplicity_core_card (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q) :
    #(highMultiplicityCore A T x) * #T ^ 2 ≤ 4 * familyEnergy A T x := by
  classical
  set μ := multiplicity (shiftedFibre A x) T
  set U := highMultiplicityCore A T x
  have hpt : ∀ y ∈ U, #T ^ 2 ≤ 4 * μ y ^ 2 := by
    intro y hy
    have hμ : #T ≤ 2 * μ y := (mem_highMultiplicityCore (A := A) (T := T)
      (x := x) (y := y)).1 hy
    have := Nat.mul_le_mul hμ hμ
    convert this using 1 <;> ring
  have hsum : #U * #T ^ 2 ≤ 4 * ∑ y ∈ U, μ y ^ 2 := by
    calc
      #U * #T ^ 2 = ∑ y ∈ U, #T ^ 2 := by simp [sum_const, smul_eq_mul]
      _ ≤ ∑ y ∈ U, 4 * μ y ^ 2 := sum_le_sum hpt
      _ = 4 * ∑ y ∈ U, μ y ^ 2 := by simp [mul_sum]
  have hU : ∑ y ∈ U, μ y ^ 2 ≤ familyEnergy A T x := by
    have hsplit :=
      sum_add_sum_compl (s := U) (f := fun y => μ y ^ 2)
    have : familyEnergy A T x = ∑ y ∈ U, μ y ^ 2 + ∑ y ∈ Uᶜ, μ y ^ 2 := by
      simpa [familyEnergy, μ] using hsplit.symm
    omega
  exact hsum.trans (Nat.mul_le_mul_left 4 hU)

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

/-- Energy at most `K` times random forces the neighbouring union to cover
at least `q/K` residues. -/
lemma energy_implies_union_card {T : Finset (ZMod q)}
    {A : Finset (ZMod q × ZMod q)} {x : ZMod q} {K : ℕ}
    (_hK : 0 < K)
    (hE0 : familyEnergy A T x ≠ 0)
    (hE : familyEnergy A T x * q ≤ K * (coverageMass A T x) ^ 2) :
    q ≤ K * #(T.biUnion (shiftedFibre A x)) := by
  set E := familyEnergy A T x
  set W := coverageMass A T x
  set U := T.biUnion (shiftedFibre A x)
  have hCS := energy_cs A T x
  have h1 : K * W ^ 2 ≤ K * (#U * E) := Nat.mul_le_mul_left K hCS
  have h2 : E * q ≤ K * (#U * E) := hE.trans h1
  have h3 : E * q ≤ (K * #U) * E := by
    convert h2 using 1
    ring
  exact Nat.le_of_mul_le_mul_right (by simpa [mul_comm E] using h3)
    (Nat.pos_of_ne_zero hE0)

/-- Almost mixing: energy at most `K` times random bounds the fibre by
`q(1-1/K)`. The case `K = 1` is empty once neighbouring mass is `≥ q`. -/
theorem almost_mixing_fibre_card {T : Finset (ZMod q)}
    {A : Finset (ZMod q × ZMod q)} {x : ZMod q} {K : ℕ}
    (hA : IsSeedIndependent T (A : Set (ZMod q × ZMod q)))
    (hT0 : 0 ∉ T)
    (hK : 0 < K)
    (hE0 : familyEnergy A T x ≠ 0)
    (hE : familyEnergy A T x * q ≤ K * (coverageMass A T x) ^ 2) :
    K * #(fibreF A x) + q ≤ K * q := by
  set U := T.biUnion (shiftedFibre A x)
  have hU := energy_implies_union_card (A := A) (T := T) (x := x) hK hE0 hE
  have hcov := coverage_le_of_independent (A := A) (T := T) (x := x) hA hT0
  have hmul : K * (#(fibreF A x) + #U) ≤ K * q := Nat.mul_le_mul_left K hcov
  have hmul' : K * #(fibreF A x) + K * #U ≤ K * q := by
    convert hmul using 1
    ring
  have hadd : K * #(fibreF A x) + q ≤ K * #(fibreF A x) + K * #U :=
    Nat.add_le_add_left hU _
  exact hadd.trans hmul'

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

/-- Energy at least two-thirds of the `#T · W` maximum puts a quarter of
the energy on points of multiplicity at least `#T / 2`. This does not
require a lower bound on fibre size. Three-quarters is the special case
`3 #T W ≤ 4 E`. -/
theorem two_thirds_energy_core (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (hW : 0 < coverageMass A T x)
    (hE : 2 * #T * coverageMass A T x ≤ 3 * familyEnergy A T x) :
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
  · have hcomp : ∀ y ∈ Uᶜ, 2 * μ y < #T := by
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
    have hgoal : 2 * (#T - 1) * W ≤ 3 * E :=
      (Nat.mul_le_mul_right W
        (Nat.mul_le_mul_left 2 (Nat.sub_le #T 1))).trans hE
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

/-- Energy at least three-quarters of the `#T · W` maximum puts a quarter of
the energy on points of multiplicity at least `#T / 2`. Special case of
`two_thirds_energy_core`. -/
theorem three_quarters_energy_core (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (hW : 0 < coverageMass A T x)
    (hE : 3 * #T * coverageMass A T x ≤ 4 * familyEnergy A T x) :
    familyEnergy A T x ≤
      4 * ∑ y ∈ highMultiplicityCore A T x,
        (multiplicity (shiftedFibre A x) T y) ^ 2 := by
  refine two_thirds_energy_core A T x hW ?_
  have h6 : 6 * #T * coverageMass A T x ≤ 8 * familyEnergy A T x := by
    have := Nat.mul_le_mul_left 2 hE
    convert this using 1 <;> ring
  have h9 : 6 * #T * coverageMass A T x ≤ 9 * familyEnergy A T x :=
    h6.trans (Nat.mul_le_mul_right _ (by decide : 8 ≤ 9))
  have : 3 * (2 * #T * coverageMass A T x) ≤ 3 * (3 * familyEnergy A T x) := by
    convert h9 using 1 <;> ring
  exact Nat.le_of_mul_le_mul_left this (by decide : 0 < 3)

/-- Maximal energy forces every multiplicity to be `0` or `#T`. -/
lemma multiplicity_eq_zero_or_card
    (A : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q)) (x y : ZMod q)
    (hE : familyEnergy A T x = #T * coverageMass A T x) :
    multiplicity (shiftedFibre A x) T y = 0 ∨
      multiplicity (shiftedFibre A x) T y = #T := by
  classical
  set μ := multiplicity (shiftedFibre A x) T
  set W := coverageMass A T x
  set E := familyEnergy A T x
  have hμ : ∀ z, μ z ≤ #T := fun z => card_filter_le _ _
  have hpt : ∀ z, μ z ^ 2 + μ z * (#T - μ z) = #T * μ z := fun z => by
    have := hμ z
    have : μ z * μ z + μ z * (#T - μ z) = μ z * #T := by
      rw [← mul_add, Nat.add_sub_of_le this]
    simpa [pow_two, mul_comm] using this
  have hsum :
      E + ∑ z : ZMod q, μ z * (#T - μ z) = #T * W := by
    calc
      E + ∑ z : ZMod q, μ z * (#T - μ z)
          = ∑ z : ZMod q, (μ z ^ 2 + μ z * (#T - μ z)) := by
            simp [E, familyEnergy, μ, sum_add_distrib]
      _ = ∑ z : ZMod q, #T * μ z := sum_congr rfl fun z _ => hpt z
      _ = #T * W := by simp [W, coverageMass, μ, mul_sum]
  have hvan : ∑ z : ZMod q, μ z * (#T - μ z) = 0 := by
    have : E + ∑ z : ZMod q, μ z * (#T - μ z) = E := by
      simpa [hE] using hsum
    omega
  have hy : μ y * (#T - μ y) = 0 := by
    have hle :=
      single_le_sum (s := (univ : Finset (ZMod q)))
        (f := fun z => μ z * (#T - μ z))
        (fun _ _ => Nat.zero_le _) (mem_univ y)
    exact Nat.eq_zero_of_le_zero (hle.trans_eq hvan)
  rcases Nat.mul_eq_zero.1 hy with h0 | hT
  · exact Or.inl h0
  · exact Or.inr (Nat.le_antisymm (hμ y) (Nat.le_of_sub_eq_zero hT))

/-- Maximal energy makes every nonempty shifted fibre equal. -/
lemma maximal_energy_exact_cylinder
    (A : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q)) (x : ZMod q)
    (hE : familyEnergy A T x = #T * coverageMass A T x)
    {s t : ZMod q} (hs : s ∈ T) (ht : t ∈ T) :
    shiftedFibre A x s = shiftedFibre A x t := by
  classical
  set F := shiftedFibre A x
  set μ := multiplicity F T
  ext y
  constructor
  · intro hy
    have hpos : 0 < μ y :=
      card_pos.mpr ⟨s, mem_filter.2 ⟨hs, hy⟩⟩
    have hμ : μ y = #T := by
      rcases multiplicity_eq_zero_or_card A T x y hE with h0 | hT
      · exact (Nat.not_lt.2 (h0.symm ▸ Nat.le_refl 0) hpos).elim
      · exact hT
    have hfilter : T.filter (fun i => y ∈ F i) = T :=
      eq_of_subset_of_card_le (filter_subset _ _) (by
        simpa [μ, multiplicity] using hμ.symm.le)
    have ht' : t ∈ T.filter (fun i => y ∈ F i) := by
      rw [hfilter]; exact ht
    exact (mem_filter.1 ht').2
  · intro hy
    have hpos : 0 < μ y :=
      card_pos.mpr ⟨t, mem_filter.2 ⟨ht, hy⟩⟩
    have hμ : μ y = #T := by
      rcases multiplicity_eq_zero_or_card A T x y hE with h0 | hT
      · exact (Nat.not_lt.2 (h0.symm ▸ Nat.le_refl 0) hpos).elim
      · exact hT
    have hfilter : T.filter (fun i => y ∈ F i) = T :=
      eq_of_subset_of_card_le (filter_subset _ _) (by
        simpa [μ, multiplicity] using hμ.symm.le)
    have hs' : s ∈ T.filter (fun i => y ∈ F i) := by
      rw [hfilter]; exact hs
    exact (mem_filter.1 hs').2

/-- If the neighbouring mass is at least `#T · q / 2`, twice-random energy
is at least maximal energy. -/
lemma twice_random_ge_max (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (h : #T * q ≤ 2 * coverageMass A T x) :
    #T * coverageMass A T x * q ≤ 2 * (coverageMass A T x) ^ 2 := by
  have := Nat.mul_le_mul_right (coverageMass A T x) h
  convert this using 1 <;> ring

/-- Fibres of mean size at least `q/2` cannot be strictly aligned. -/
lemma no_aligned_of_large_mass (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (h : #T * q ≤ 2 * coverageMass A T x) :
    familyEnergy A T x * q ≤ 2 * (coverageMass A T x) ^ 2 := by
  have hmax := energy_le_card_mul_mass A T x
  have : familyEnergy A T x * q ≤ #T * coverageMass A T x * q :=
    Nat.mul_le_mul_right q hmax
  exact this.trans (twice_random_ge_max A T x h)

/-- Every fibre of size at least `q/2` implies the same: no strict alignment. -/
lemma no_aligned_of_half_fibres (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (h : ∀ t ∈ T, q ≤ 2 * #(shiftedFibre A x t)) :
    familyEnergy A T x * q ≤ 2 * (coverageMass A T x) ^ 2 := by
  have hW : #T * q ≤ 2 * coverageMass A T x := by
    calc
      #T * q = ∑ t ∈ T, q := by simp [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ t ∈ T, 2 * #(shiftedFibre A x t) := sum_le_sum h
      _ = 2 * ∑ t ∈ T, #(shiftedFibre A x t) := by simp [mul_sum]
      _ = 2 * coverageMass A T x := by rw [coverageMass_eq_sum]
  exact no_aligned_of_large_mass A T x hW

/-- Mean fibre size at least `3q/8` makes three-quarters of maximal energy
no larger than twice-random energy. -/
lemma three_quarters_le_twice_random (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (h : 3 * #T * q ≤ 8 * coverageMass A T x) :
    3 * #T * coverageMass A T x * q ≤ 8 * (coverageMass A T x) ^ 2 := by
  have := Nat.mul_le_mul_right (coverageMass A T x) h
  convert this using 1 <;> ring

/-- On fibres of mean size at least `3q/8`, alignment forces three-quarters
of maximal energy. Superseded for the leftover window by
`aligned_implies_two_thirds` at mean size `q/3`. -/
lemma aligned_implies_three_quarters (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (h : 3 * #T * q ≤ 8 * coverageMass A T x)
    (hE : 2 * (coverageMass A T x) ^ 2 < familyEnergy A T x * q) :
    3 * #T * coverageMass A T x ≤ 4 * familyEnergy A T x := by
  set W := coverageMass A T x
  set E := familyEnergy A T x
  have h34 : 3 * #T * W * q ≤ 8 * W ^ 2 :=
    three_quarters_le_twice_random A T x h
  have h8 : 8 * W ^ 2 < 4 * E * q := by
    have := Nat.mul_lt_mul_of_pos_right hE (by decide : 0 < 4)
    convert this using 1 <;> ring
  have hlt : 3 * #T * W * q < 4 * E * q := h34.trans_lt h8
  have hq : 0 < q := (Fact.out : Nat.Prime q).pos
  exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right (a := q) hlt)

/-- Mean fibre size at least `q/3` makes two-thirds of maximal energy
no larger than twice-random energy. -/
lemma two_thirds_le_twice_random (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (h : #T * q ≤ 3 * coverageMass A T x) :
    2 * #T * coverageMass A T x * q ≤ 6 * (coverageMass A T x) ^ 2 := by
  have := Nat.mul_le_mul_right (2 * coverageMass A T x) h
  convert this using 1 <;> ring

/-- On fibres of mean size at least `q/3`, alignment forces two-thirds
of maximal energy. The intermediate window is empty on every medium fibre. -/
lemma aligned_implies_two_thirds (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (h : #T * q ≤ 3 * coverageMass A T x)
    (hE : 2 * (coverageMass A T x) ^ 2 < familyEnergy A T x * q) :
    2 * #T * coverageMass A T x ≤ 3 * familyEnergy A T x := by
  set W := coverageMass A T x
  set E := familyEnergy A T x
  have h23 : 2 * #T * W * q ≤ 6 * W ^ 2 :=
    two_thirds_le_twice_random A T x h
  have h6 : 6 * W ^ 2 < 3 * E * q := by
    have := Nat.mul_lt_mul_of_pos_right hE (by decide : 0 < 3)
    convert this using 1 <;> ring
  have hlt : 2 * #T * W * q < 3 * E * q := h23.trans_lt h6
  exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right (a := q) hlt)

/-- Medium aligned fibres have a high-multiplicity core carrying a
quarter of the energy. This is structure, not a size bound. -/
lemma aligned_medium_has_core (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (hW : 0 < coverageMass A T x)
    (h : #T * q ≤ 3 * coverageMass A T x)
    (hE : 2 * (coverageMass A T x) ^ 2 < familyEnergy A T x * q) :
    familyEnergy A T x ≤
      4 * ∑ y ∈ highMultiplicityCore A T x,
        (multiplicity (shiftedFibre A x) T y) ^ 2 :=
  two_thirds_energy_core A T x hW (aligned_implies_two_thirds A T x h hE)

/-- Equality of twice-random with the energy upper bound, on half-size
fibres, forces maximal energy and therefore an exact cylinder. -/
lemma half_fibre_energy_exact_cylinder
    (A : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q)) (x : ZMod q)
    (h : ∀ t ∈ T, q ≤ 2 * #(shiftedFibre A x t))
    (hE : 2 * (coverageMass A T x) ^ 2 ≤ familyEnergy A T x * q)
    {s t : ZMod q} (hs : s ∈ T) (ht : t ∈ T) :
    shiftedFibre A x s = shiftedFibre A x t := by
  set W := coverageMass A T x
  set E := familyEnergy A T x
  have hmix : E * q ≤ 2 * W ^ 2 := no_aligned_of_half_fibres A T x h
  have heq : E * q = 2 * W ^ 2 := le_antisymm hmix hE
  have hW : #T * q ≤ 2 * W := by
    calc
      #T * q = ∑ u ∈ T, q := by simp [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ u ∈ T, 2 * #(shiftedFibre A x u) := sum_le_sum h
      _ = 2 * ∑ u ∈ T, #(shiftedFibre A x u) := by simp [mul_sum]
      _ = 2 * W := by
        dsimp [W]
        rw [coverageMass_eq_sum]
  have hmax : E ≤ #T * W := energy_le_card_mul_mass A T x
  have hq : 0 < q := (Fact.out : Nat.Prime q).pos
  have hEW : E = #T * W := by
    have h1 : E * q ≤ #T * W * q := Nat.mul_le_mul_right q hmax
    have h2 : #T * W * q ≤ 2 * W ^ 2 := twice_random_ge_max A T x hW
    have : E * q = #T * W * q :=
      le_antisymm h1 (by
        have : 2 * W ^ 2 = E * q := heq.symm
        exact this ▸ h2)
    exact Nat.eq_of_mul_eq_mul_right hq this
  exact maximal_energy_exact_cylinder A T x hEW hs ht

/-- Ordered pairs whose intersection is at least half the mean fibre
size: `W ≤ 2 · #T · |A_t ∩ A_{t'}|`. -/
def heavyPairSet (A : Finset (ZMod q × ZMod q)) (T : Finset (ZMod q))
    (x : ZMod q) : Finset (ZMod q × ZMod q) :=
  (T ×ˢ T).filter fun p =>
    coverageMass A T x ≤
      2 * #T * #(shiftedFibre A x p.1 ∩ shiftedFibre A x p.2)

lemma mem_heavyPairSet {A : Finset (ZMod q × ZMod q)}
    {T : Finset (ZMod q)} {x : ZMod q} {p : ZMod q × ZMod q} :
    p ∈ heavyPairSet A T x ↔
      p.1 ∈ T ∧ p.2 ∈ T ∧
        coverageMass A T x ≤
          2 * #T * #(shiftedFibre A x p.1 ∩ shiftedFibre A x p.2) := by
  constructor
  · intro hp
    rcases mem_filter.1 hp with ⟨hpT, hW⟩
    rcases mem_product.1 hpT with ⟨h1, h2⟩
    exact ⟨h1, h2, hW⟩
  · intro ⟨h1, h2, hW⟩
    exact mem_filter.2 ⟨mem_product.2 ⟨h1, h2⟩, hW⟩

lemma familyEnergy_eq_sum_product (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q) :
    familyEnergy A T x =
      ∑ p ∈ T ×ˢ T,
        #(shiftedFibre A x p.1 ∩ shiftedFibre A x p.2) := by
  rw [familyEnergy_eq_pairwise, sum_product]

lemma card_heavyPairSet_row_sum (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q) :
    #(heavyPairSet A T x) =
      ∑ s ∈ T, #{t ∈ T | (s, t) ∈ heavyPairSet A T x} := by
  classical
  unfold heavyPairSet
  rw [card_eq_sum_ones, sum_filter, sum_product]
  refine sum_congr rfl fun s hs => ?_
  rw [sum_boole]
  refine congrArg card ?_
  ext t
  simp [mem_filter, mem_product, hs]

/-- Intersections are at most `q/2` once every fibre has size `≤ q/2`. -/
lemma inter_le_half_field (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (h : ∀ t ∈ T, 2 * #(shiftedFibre A x t) ≤ q) :
    ∀ t ∈ T, ∀ t' ∈ T,
      2 * #(shiftedFibre A x t ∩ shiftedFibre A x t') ≤ q := by
  intro t ht t' ht'
  have hle : #(shiftedFibre A x t ∩ shiftedFibre A x t') ≤
      #(shiftedFibre A x t) :=
    card_le_card inter_subset_left
  exact (Nat.mul_le_mul_left 2 hle).trans (h t ht)

/-- Two-thirds energy on mean size `≥ q/3`, with fibres at most `q/2`,
forces `#T² / 9` heavy ordered pairs. Paper `lem:heavypairs`. -/
lemma card_heavy_pair_set (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (hmin : #T * q ≤ 3 * coverageMass A T x)
    (hmax : ∀ t ∈ T, ∀ t' ∈ T,
      2 * #(shiftedFibre A x t ∩ shiftedFibre A x t') ≤ q)
    (hE : 2 * #T * coverageMass A T x ≤ 3 * familyEnergy A T x) :
    #T ^ 2 ≤ 9 * #(heavyPairSet A T x) := by
  classical
  set F := shiftedFibre A x
  set W := coverageMass A T x
  set E := familyEnergy A T x
  set n := #T
  set H := heavyPairSet A T x
  set L := (T ×ˢ T).filter fun p => p ∉ H
  have hq : 0 < q := (Fact.out : Nat.Prime q).pos
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hW : 0 < W := by
    have : 0 < n * q := Nat.mul_pos hnpos hq
    exact Nat.pos_of_ne_zero fun hW0 => by
      have : n * q ≤ 0 := by simpa [W, hW0] using hmin
      exact (Nat.not_lt.2 this) (Nat.mul_pos hnpos hq)
  have hinter :
      E = ∑ p ∈ T ×ˢ T, #(F p.1 ∩ F p.2) := by
    simpa [E, F] using familyEnergy_eq_sum_product A T x
  have hpart :=
    (sum_filter_add_sum_filter_not (T ×ˢ T)
      (fun p => p ∈ H) (fun p => #(F p.1 ∩ F p.2))).symm
  have hHsub : H ⊆ T ×ˢ T := filter_subset _ _
  have hHeq : (T ×ˢ T).filter (fun p => p ∈ H) = H := by
    ext p
    constructor
    · intro hp
      exact (mem_filter.1 hp).2
    · intro hp
      exact mem_filter.2 ⟨hHsub hp, hp⟩
  have hEsplit : E =
      ∑ p ∈ H, #(F p.1 ∩ F p.2) + ∑ p ∈ L, #(F p.1 ∩ F p.2) := by
    rw [hinter, hpart, hHeq]
  have hHbd : ∀ p ∈ H, 2 * #(F p.1 ∩ F p.2) ≤ q := fun p hp => by
    have hp' := (mem_heavyPairSet (A := A) (T := T) (x := x) (p := p)).1
      (by simpa [H] using hp)
    exact hmax p.1 hp'.1 p.2 hp'.2.1
  have hHsum : 2 * ∑ p ∈ H, #(F p.1 ∩ F p.2) ≤ #H * q := by
    calc
      2 * ∑ p ∈ H, #(F p.1 ∩ F p.2)
          = ∑ p ∈ H, 2 * #(F p.1 ∩ F p.2) := by
            rw [mul_sum]
      _ ≤ ∑ p ∈ H, q := sum_le_sum hHbd
      _ = #H * q := by simp [sum_const, smul_eq_mul, mul_comm]
  have hLbd : ∀ p ∈ L, 2 * n * #(F p.1 ∩ F p.2) ≤ W := fun p hp => by
    have hpL : p ∉ H := (mem_filter.1 hp).2
    have hpT : p ∈ T ×ˢ T := (mem_filter.1 hp).1
    have hs : p.1 ∈ T := (mem_product.1 hpT).1
    have ht : p.2 ∈ T := (mem_product.1 hpT).2
    have : ¬(W ≤ 2 * n * #(F p.1 ∩ F p.2)) := by
      intro hle
      have : p ∈ H :=
        (mem_heavyPairSet (A := A) (T := T) (x := x) (p := p)).2
          ⟨hs, ht, by simpa [W, n, F] using hle⟩
      exact hpL this
    exact Nat.le_of_lt (Nat.not_le.1 this)
  have hLsum : 2 * n * ∑ p ∈ L, #(F p.1 ∩ F p.2) ≤ n ^ 2 * W := by
    have hcard : #L ≤ n ^ 2 := by
      have : L ⊆ T ×ˢ T := filter_subset _ _
      have := card_le_card this
      simpa [n, card_product, pow_two] using this
    calc
      2 * n * ∑ p ∈ L, #(F p.1 ∩ F p.2)
          = ∑ p ∈ L, 2 * n * #(F p.1 ∩ F p.2) := by
            rw [mul_sum]
      _ ≤ ∑ p ∈ L, W := sum_le_sum hLbd
      _ = #L * W := by simp [sum_const, smul_eq_mul, mul_comm]
      _ ≤ n ^ 2 * W := Nat.mul_le_mul_right W hcard
  have hLsum' : 2 * ∑ p ∈ L, #(F p.1 ∩ F p.2) ≤ n * W :=
    Nat.le_of_mul_le_mul_left (by
      calc
        n * (2 * ∑ p ∈ L, #(F p.1 ∩ F p.2))
            = 2 * n * ∑ p ∈ L, #(F p.1 ∩ F p.2) := by ring
        _ ≤ n ^ 2 * W := hLsum
        _ = n * (n * W) := by ring) hnpos
  have h2E : 2 * E ≤ #H * q + n * W := by
    calc
      2 * E
          = 2 * (∑ p ∈ H, #(F p.1 ∩ F p.2) +
              ∑ p ∈ L, #(F p.1 ∩ F p.2)) := by rw [hEsplit]
      _ = 2 * ∑ p ∈ H, #(F p.1 ∩ F p.2) +
            2 * ∑ p ∈ L, #(F p.1 ∩ F p.2) := by ring
      _ ≤ #H * q + n * W := add_le_add hHsum hLsum'
  have hnW : n * W ≤ 2 * E := by
    have : 2 * n * W ≤ 4 * E :=
      hE.trans (Nat.mul_le_mul_right E (by decide : 3 ≤ 4))
    have h2 : 2 * (n * W) ≤ 2 * (2 * E) := by
      convert this using 1 <;> ring
    exact Nat.le_of_mul_le_mul_left h2 (by decide : 0 < 2)
  have hHq : 2 * E - n * W ≤ #H * q :=
    Nat.sub_le_iff_le_add.2 h2E
  have hdouble : E ≤ 2 * (2 * E - n * W) := by
    have hsub : 2 * (2 * E - n * W) = 4 * E - 2 * n * W := by
      have h := Nat.mul_sub_left_distrib 2 (2 * E) (n * W)
      have h1 : 2 * (2 * E) = 4 * E := by ring
      have h2 : 2 * (n * W) = 2 * n * W := by ring
      rw [h, h1, h2]
    have h43 : 4 * E - 3 * E = E := by
      have : 3 * E ≤ 4 * E := Nat.mul_le_mul_right E (by decide : 3 ≤ 4)
      omega
    have hmono : 4 * E - 3 * E ≤ 4 * E - 2 * n * W :=
      Nat.sub_le_sub_left hE (4 * E)
    have : E ≤ 4 * E - 2 * n * W := by
      calc
        E = 4 * E - 3 * E := h43.symm
        _ ≤ 4 * E - 2 * n * W := hmono
    rwa [hsub]
  have hEH : E ≤ 2 * #H * q := by
    have := Nat.mul_le_mul_left 2 hHq
    exact hdouble.trans (this.trans_eq (by ring))
  have hWE : 2 * n ^ 2 * q ≤ 9 * E := by
    have hmul : 2 * n ^ 2 * q * W ≤ 9 * E * W := by
      calc
        2 * n ^ 2 * q * W
            = 2 * n * W * (n * q) := by ring
        _ ≤ 3 * E * (3 * W) := Nat.mul_le_mul hE hmin
        _ = 9 * E * W := by ring
    exact Nat.le_of_mul_le_mul_right hmul hW
  have : 2 * n ^ 2 * q ≤ 18 * #H * q := by
    have := Nat.mul_le_mul_left 9 hEH
    have h9 : 9 * E ≤ 18 * #H * q := by
      convert this using 1; ring
    exact hWE.trans h9
  have hnn : 2 * n ^ 2 ≤ 18 * #H :=
    Nat.le_of_mul_le_mul_right this hq
  have : n ^ 2 ≤ 9 * #H := by
    have h2 : 2 * n ^ 2 ≤ 2 * (9 * #H) := by
      convert hnn using 1; ring
    exact Nat.le_of_mul_le_mul_left h2 (by decide : 0 < 2)
  simpa [n, H] using this

/-- A vertex of heavy-pair degree at least `#T / 9`. Paper `lem:star`. -/
lemma exists_heavy_star (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (hn : 0 < #T)
    (hcard : #T ^ 2 ≤ 9 * #(heavyPairSet A T x)) :
    ∃ s ∈ T, #T ≤ 9 * #{t ∈ T | (s, t) ∈ heavyPairSet A T x} := by
  classical
  set n := #T
  set H := heavyPairSet A T x
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  have hdeg : ∀ s ∈ T, 9 * #{t ∈ T | (s, t) ∈ H} ≤ n - 1 :=
    fun s hs => Nat.le_pred_of_lt (h s hs)
  have hsum := card_heavyPairSet_row_sum A T x
  have h9 : 9 * #H ≤ n * (n - 1) := by
    calc
      9 * #H
          = 9 * ∑ s ∈ T, #{t ∈ T | (s, t) ∈ H} := by rw [hsum]
      _ = ∑ s ∈ T, 9 * #{t ∈ T | (s, t) ∈ H} := by rw [mul_sum]
      _ ≤ ∑ s ∈ T, (n - 1) := sum_le_sum hdeg
      _ = n * (n - 1) := by simp [sum_const, smul_eq_mul, n]
  have hlt : n * (n - 1) < n * n :=
    Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hn (by decide : 0 < 1)) hn
  have : n ^ 2 < n ^ 2 :=
    (hcard.trans h9).trans_lt (by simpa [pow_two] using hlt)
  exact (lt_irrefl _ this)

/-- Medium aligned fibres have a heavy star of degree `#T / 9`.
Structure, not a size bound. -/
lemma aligned_medium_has_star (A : Finset (ZMod q × ZMod q))
    (T : Finset (ZMod q)) (x : ZMod q)
    (hn : 0 < #T)
    (hmin : ∀ t ∈ T, q ≤ 3 * #(shiftedFibre A x t))
    (hmax : ∀ t ∈ T, 2 * #(shiftedFibre A x t) ≤ q)
    (hE : 2 * (coverageMass A T x) ^ 2 < familyEnergy A T x * q) :
    ∃ s ∈ T, #T ≤ 9 * #{t ∈ T | (s, t) ∈ heavyPairSet A T x} := by
  set W := coverageMass A T x
  set n := #T
  have hWmin : n * q ≤ 3 * W := by
    calc
      n * q = ∑ t ∈ T, q := by simp [sum_const, smul_eq_mul, mul_comm, n]
      _ ≤ ∑ t ∈ T, 3 * #(shiftedFibre A x t) := sum_le_sum hmin
      _ = 3 * ∑ t ∈ T, #(shiftedFibre A x t) := by simp [mul_sum]
      _ = 3 * W := by
        dsimp [W]
        rw [coverageMass_eq_sum]
  have hinter := inter_le_half_field A T x hmax
  have h23 : 2 * n * W ≤ 3 * familyEnergy A T x :=
    aligned_implies_two_thirds A T x hWmin hE
  exact exists_heavy_star A T x hn (card_heavy_pair_set A T x hWmin hinter h23)

end R3tBound
