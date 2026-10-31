/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Word

/-!
# Phrase-level prosodic structure

This file defines the well-formed phonological and intonational phrases of the prosodic tree,
and culminative prominence at a node. A phrase is a tree rooted in a φ-node whose nodes license
their daughters by Layeredness. Recursion and level skipping are admitted.

## Main definitions

* `IsPhrase`, `IsUtterance`: well-formed phonological phrases and intonational phrases.
* `HeadUnique`: at most one child of a node heads it.

## References

* [E. Selkirk, *The Prosodic Structure of Function Words* (1996)][selkirk-1996]
* [E. Selkirk, *The Syntax-Phonology Interface* (2011)][selkirk-2011]
* [D. Büring, *Unalternative Semantics* (2015)][buring-2015]
* [D. Büring, *Intonation and Meaning* (2016)][buring-2016]
-/

@[expose] public section

namespace Prosody

/-- A well-formed phonological phrase is a licensed tree rooted in a φ-node: a φ over nodes of
level at most φ. A stray syllable under the φ is the position of the free clitic of
[selkirk-1996], and a φ under a φ is the recursive φ-structure that the Match Theory of
[selkirk-2011] maps syntactic phrases to; Nonrecursivity and Exhaustivity are violable in
[selkirk-1996]. -/
abbrev IsPhrase : Tree → Prop := IsConstituent .ph

/-- A well-formed intonational phrase, or utterance, is a licensed tree rooted in an ι-node. -/
abbrev IsUtterance : Tree → Prop := IsConstituent .iota

/-- Prominence is *culminative* at a node when at most one of its children heads it, the
configuration of one metrically strong daughter beside weak sisters that [buring-2015] annotates
on phrase markers and that the metrical trees of [buring-2016] carry as a weak–strong relation
on sisters. -/
def HeadUnique (t : Tree) : Prop :=
  (t.children.filter (fun c => c.value.isHead)).length ≤ 1

instance (t : Tree) : Decidable (HeadUnique t) :=
  inferInstanceAs (Decidable (_ ≤ _))

-- A φ over words, a recursive φ, and a φ over a stray syllable are all well-formed phrases; a
-- φ over an ι is not.
example : IsPhrase (.ph [.om [], .om []]) := by decide
example : IsPhrase (.ph [.ph [.om []], .om []]) := by decide
example : IsPhrase (.ph [.σ 1, .om []]) := by decide
example : ¬ IsPhrase (.ph [.node .iota []]) := by decide

end Prosody
