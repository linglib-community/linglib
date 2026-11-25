/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Spine.Basic
public import Linglib.Syntax.Spine.Hosting
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
* `Minimalist.HeadChain.sited`: the head chains with their sites.
* `Minimalist.HeadChain.hosts`: the head at which each position of a spine is pronounced.

## Main results

* `Minimalist.HeadChain.flatten_chains`: the chains partition the spine in order.
* `Minimalist.HeadChain.infix_of_mem_chains`: each chain is a stretch of the spine.
* `Minimalist.HeadChain.isContiguous_hosts`: on a spine without repeated heads, the hosting of
  head chains is contiguous.

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
def chains (s : Spine H) : List (List H) := s.heads.splitBy fun _ b ↦ decide (shares b)

/-- Head Chain Pronunciation: a chain is pronounced at its highest strong position, or at its
highest position when none is strong. -/
def site (c : List H) : Option H := (c.filter (strong ·)).getLast?.or c.getLast?

/-- The head chains of a spine with their sites, lowest first. -/
def sited (s : Spine H) : List (List H × H) :=
  (chains shares s).filterMap fun c ↦ (site strong c).map (c, ·)

/-- The host of each position of a spine: the head at which its chain is pronounced. -/
def hosts (s : Spine H) : List H := Spine.hosting (sited shares strong s)

variable {shares strong}

theorem flatten_chains (s : Spine H) : (chains shares s).flatten = s.heads :=
  List.flatten_splitBy _ _

theorem mem_of_site {c : List H} {x : H} (h : site strong c = some x) : x ∈ c := by
  rcases Option.or_eq_some_iff.mp h with h | ⟨-, h⟩
  · exact (List.mem_filter.mp (List.mem_of_getLast? h)).1
  · exact List.mem_of_getLast? h

/-- Each head chain is a stretch of the spine. -/
theorem infix_of_mem_chains {s : Spine H} {c : List H} (h : c ∈ chains shares s) :
    c <:+: s.heads :=
  flatten_chains (shares := shares) s ▸ List.infix_of_mem_flatten h

theorem map_fst_sited_sublist (s : Spine H) :
    ((sited shares strong s).map Prod.fst).Sublist (chains shares s) := by
  have : (fun c : List H ↦ ((site strong c).map (c, ·)).map Prod.fst) =
      Option.guard fun c ↦ (site strong c).isSome := by
    funext c
    cases h : site strong c <;> simp [Option.guard, h]
  rw [sited, List.map_filterMap, this, List.filterMap_eq_filter]
  exact List.filter_sublist

/-- On a spine without repeated heads, the hosting of head chains is contiguous. -/
theorem isContiguous_hosts {s : Spine H} (hs : s.heads.Nodup) :
    IsContiguous (hosts shares strong s).get := by
  refine Spine.isContiguous_hosting (fun w hw ↦ ?_) ?_
  · obtain ⟨c, -, hc⟩ := List.mem_filterMap.1 hw
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hc
    exact mem_of_site hx
  · rw [← flatten_chains (shares := shares) s] at hs
    rw [List.flatMap_def]
    exact hs.sublist (map_fst_sited_sublist s).flatten

end Minimalist.HeadChain
