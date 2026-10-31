/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Word

/-!
# Phrase-level prosodic structure

The phonological phrase φ and the intonational phrase ι are the levels of the prosodic
hierarchy above the prosodic word. A well-formed phrase (`IsPhrase`) is a tree rooted in a
φ-node and licensed by Layeredness, so that a φ dominates prosodic words, recursive phrases, or
stray feet and syllables, the last being the position of the free clitic in [selkirk-1996]; a
well-formed utterance (`IsUtterance`) is a tree rooted in an ι-node and licensed in the same
way. Recursion and level skipping are admitted at both levels, since Nonrecursivity and
Exhaustivity are violable constraints in [selkirk-1996] rather than conditions on the carrier,
and the Match Theory of [selkirk-2011] maps syntactic phrases to recursive φ-structures.
Prominence is culminative at a node (`HeadUnique`) when at most one of its children heads it,
the configuration of one metrically strong daughter beside weak sisters that [buring-2015]
annotates on phrase markers and that the metrical trees of [buring-2016] carry as a weak–strong
relation on sisters.

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
level at most φ. -/
abbrev IsPhrase : Tree → Prop := IsConstituent .ph

/-- A well-formed intonational phrase, or utterance, is a licensed tree rooted in an ι-node. -/
abbrev IsUtterance : Tree → Prop := IsConstituent .iota

/-- Prominence is *culminative* at a node when at most one of its children heads it. -/
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
