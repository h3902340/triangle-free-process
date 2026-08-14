/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import R3tBound.Sidon

/-!
# Sidon codegree of the truncated parabola

A nonzero difference has at most one representation as a difference of
two unsigned parabola points.
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

end R3tBound
