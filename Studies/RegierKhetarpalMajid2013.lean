/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Studies.Haspelmath1997
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Regier, Khetarpal and Majid (2013): Inferring Semantic Maps

[regier-khetarpal-majid-2013] pose the inference of a semantic map as finding the fewest edges
among the semantic functions that make every attested category a connected region. Run on the
indefinite pronouns of [haspelmath-1997], their algorithm returns his map without its edge between
the irrealis and conditional functions, which [croft-poole-2008] had found unnecessary: every
attested combination of functions [stays connected without
it](##attested_connected_deleteEdges), and [no further edge can be
removed](##exists_attested_not_connected_deleteEdges).

## Implementation notes

* The attested combinations are those of the book's table of combinations, as entered in
  `Haspelmath1997.attestedCombinations`; the paper runs on the forty-language database behind it.
* The second result is that the map is minimal under removing edges, which a map with the fewest
  edges must be. On these combinations the edge between the irrealis and question functions can
  be removed in place of the one to the conditional function
  (`attested_connected_deleteEdges_question`), and the paper notes that its algorithm breaks such
  ties by the order in which it considers edges.

## References

* [regier-khetarpal-majid-2013]
* [croft-poole-2008]
* [haspelmath-1997]
-/

@[expose] public section

namespace RegierKhetarpalMajid2013

open Indefinite Haspelmath1997

/-- Every attested combination of functions is still a connected region of the map once the edge
between the irrealis and conditional functions is removed. -/
theorem attested_connected_deleteEdges : ∀ c ∈ attestedCombinations,
    ((implicationalMap.deleteEdges {s(.irrealis, .conditional)}).induce ↑c.2).Connected := by
  simp only [SimpleGraph.connected_iff_exists_forall_reachable]
  decide +kernel

theorem attested_connected_deleteEdges_question : ∀ c ∈ attestedCombinations,
    ((implicationalMap.deleteEdges {s(.irrealis, .question)}).induce ↑c.2).Connected := by
  simp only [SimpleGraph.connected_iff_exists_forall_reachable]
  decide +kernel

/-- Removing any second edge disconnects some attested combination of functions. -/
theorem exists_attested_not_connected_deleteEdges : ∀ e ∈ mapEdges, e ≠ s(.irrealis, .conditional) →
    ∃ c ∈ attestedCombinations,
      ¬ ((implicationalMap.deleteEdges {s(.irrealis, .conditional), e}).induce ↑c.2).Connected := by
  simp only [SimpleGraph.connected_iff_exists_forall_reachable]
  decide +kernel

end RegierKhetarpalMajid2013
