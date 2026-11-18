/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Word

/-!
# Phonological and intonational phrases

A phonological phrase φ and an intonational phrase ι are nodes of the prosodic tree, well formed
when rooted at their level and layered. Layeredness leaves two departures from strict layering
open at the phrase. A syllable immediately under a φ, the free clitic of [selkirk-1996],
violates Exhaustivity at φ, and a φ under a φ, the phrasing that the Match Theory of
[selkirk-2011] gives to nested syntactic phrases, violates Nonrecursivity. A phrase with neither
[is a sequence of prosodic words](##Prosody.IsPhrase.isWord_of_mem_children), and an intonational
phrase with neither [a sequence of phonological
phrases](##Prosody.IsUtterance.isPhrase_of_mem_children).

## References

* [selkirk-1996]
* [selkirk-2011]
-/

@[expose] public section

namespace Prosody

variable {M : Type*} {t c : RoseTree (Constituent Level M)}

/-- A well-formed phonological phrase is a licensed tree rooted in a φ-node: a φ over nodes of
level at most φ. -/
abbrev IsPhrase : RoseTree (Constituent Level M) → Prop := IsConstituent .ph

/-- A well-formed intonational phrase, or utterance, is a licensed tree rooted in an ι-node. -/
abbrev IsUtterance : RoseTree (Constituent Level M) → Prop := IsConstituent .iota

/-- The daughters of a phonological phrase that satisfies Exhaustivity and Nonrecursivity at φ
are prosodic words. -/
theorem IsPhrase.isWord_of_mem_children (h : IsPhrase t) (he : exhaustivity .ph t = 0)
    (hn : nonrecursivity .ph t = 0) (hc : c ∈ t.children) : IsWord c :=
  ⟨(h.level_covBy_of_mem_children he hn hc).unique_left Level.om_covBy_ph,
    (h.of_mem_children hc).2⟩

/-- The daughters of an intonational phrase that satisfies Exhaustivity and Nonrecursivity at ι
are phonological phrases. -/
theorem IsUtterance.isPhrase_of_mem_children (h : IsUtterance t) (he : exhaustivity .iota t = 0)
    (hn : nonrecursivity .iota t = 0) (hc : c ∈ t.children) : IsPhrase c :=
  ⟨(h.level_covBy_of_mem_children he hn hc).unique_left Level.ph_covBy_iota,
    (h.of_mem_children hc).2⟩

end Prosody
