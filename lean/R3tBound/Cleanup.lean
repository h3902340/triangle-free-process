/-
Copyright (c) 2026 The triangle-free-process contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Open edges and cleanup

Every-open-edge graphs are triangle-free. Adding edges cannot increase
the independence number, so a cleaned subgraph `H ≤ A_q` satisfies
`α(A_q) ≤ α(H)`.
-/

namespace R3tBound

open SimpleGraph Finset

variable {V : Type*}

/-- An edge is open when its two endpoints have no common neighbour. -/
def IsOpenEdge (G : SimpleGraph V) (u v : V) : Prop :=
  G.Adj u v ∧ G.commonNeighbors u v = ∅

lemma openEdge_not_in_triangle {G : SimpleGraph V} {u v w : V}
    (h : IsOpenEdge G u v) : ¬ (G.Adj u w ∧ G.Adj v w) := by
  intro ⟨huw, hvw⟩
  have : w ∈ G.commonNeighbors u v := ⟨huw, hvw⟩
  exact (h.2.symm ▸ this : w ∈ (∅ : Set V))

/-- A graph whose every edge is open is triangle-free. -/
theorem openEdges_cliqueFree {G : SimpleGraph V} [DecidableEq V]
    (h : ∀ ⦃u v : V⦄, G.Adj u v → G.commonNeighbors u v = ∅) :
    G.CliqueFree 3 := by
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.1 hs
  have hc : c ∈ G.commonNeighbors a b := ⟨hac, hbc⟩
  rw [h hab] at hc
  exact hc

/-- Independence number is antitone in the edge set. -/
theorem indepNum_anti {G H : SimpleGraph V} [Finite V] (h : H ≤ G) :
    G.indepNum ≤ H.indepNum := by
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have hH : H.IsIndepSet (s : Set V) := by
    intro x hx y hy hxy
    exact mt (fun hAdj => h hAdj) (hs.isIndepSet hx hy hxy)
  have hle : #s ≤ H.indepNum := hH.card_le_indepNum
  have heq : #s = G.indepNum := hs.card_eq
  omega

/-- If `H` is a subgraph of `G'` (typically the cleaned graph sitting
inside `A_q`), then `α(G') ≤ α(H)`. -/
theorem alpha_le_of_open_subgraph {G H G' : SimpleGraph V} [Finite V]
    (_hH : ∀ ⦃u v : V⦄, H.Adj u v → IsOpenEdge G u v)
    (_hHG : H ≤ G) (hHG' : H ≤ G') (_hG'G : G' ≤ G) :
    G'.indepNum ≤ H.indepNum :=
  indepNum_anti hHG'

end R3tBound
