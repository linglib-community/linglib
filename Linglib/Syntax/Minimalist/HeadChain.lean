/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.OrdConnected
public import Mathlib.Data.List.SplitBy

/-!
# Head chains

In the Generalized Head Movement of Arregi and Pietraszko a head may share its M-value, the
morphological features that Vocabulary Insertion spells out, with the head of its complement. The
heads of a spine that share one M-value form a head chain, and a chain is pronounced at its
highest strong position, or at its highest position when none is strong. We define the chains of
a spine listed from the bottom up, for a choice of the heads that share and of the strong heads,
and the hosting they give: for each position of the spine, the head at which its chain is
pronounced.

## Main definitions

* `Minimalist.HeadChain.chains`: the head chains of a spine.
* `Minimalist.HeadChain.site`: the head at which a chain is pronounced.
* `Minimalist.HeadChain.hosts`: the head at which each position of a spine is pronounced.

## Main results

* `Minimalist.HeadChain.flatten_chains`: the chains partition the spine in order.
* `Minimalist.HeadChain.isContiguous_get_hosts`: on a spine without repeated heads, the positions
  pronounced at one head are a stretch of the spine.

## Implementation notes

A chain here is the list of its positions. The M-value the positions share, and the splitting of
a chain that leaves a terminal pronounced away from its position, are in
`Studies/ArregiPietraszko2021.lean`.

## TODO

* Chain splitting, and the hosting of a split chain.
* The comparison of this hosting with that of amalgamation
  (`DistributedMorphology.MorphosyntacticWord.hosts`) on every spine without repeated heads.

## References

* [arregi-pietraszko-2021]
-/

@[expose] public section

namespace Minimalist.HeadChain

variable {H : Type*} (shares strong : H → Prop) [DecidablePred shares] [DecidablePred strong]

/-- The head chains of a spine, lowest first: a head that shares its M-value with the head of its
complement joins the chain of the head below it. -/
def chains (s : List H) : List (List H) := s.splitBy fun _ b ↦ decide (shares b)

/-- Head Chain Pronunciation: a chain is pronounced at its highest strong position, or at its
highest position when none is strong. -/
def site (c : List H) : Option H := (c.filter (strong ·)).getLast?.or c.getLast?

/-- The host of each position of a spine: the head at which its chain is pronounced. -/
def hosts (s : List H) : List H :=
  ((chains shares s).filterMap fun c ↦ (site strong c).map (c.length, ·)).flatMap
    fun p ↦ List.replicate p.1 p.2

variable {shares strong}

theorem flatten_chains (s : List H) : (chains shares s).flatten = s := List.flatten_splitBy _ _

theorem mem_of_site {c : List H} {x : H} (h : site strong c = some x) : x ∈ c := by
  rcases Option.or_eq_some_iff.mp h with h | ⟨-, h⟩
  · exact (List.mem_filter.mp (List.mem_of_getLast? h)).1
  · exact List.mem_of_getLast? h

/-- On a spine without repeated heads, the positions pronounced at one head are a stretch of the
spine. -/
theorem isContiguous_get_hosts {s : List H} (hs : s.Nodup) :
    IsContiguous (hosts shares strong s).get := by
  refine List.isContiguous_get_flatMap_replicate ?_
  rw [← flatten_chains (shares := shares) s, List.nodup_flatten] at hs
  rw [List.Nodup, List.pairwise_map]
  refine hs.2.filterMap _ fun c c' hd p hp p' hp' he ↦ ?_
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hp'
  obtain rfl : x = x' := he
  exact hd (mem_of_site hx) (mem_of_site hx')

end Minimalist.HeadChain
