module

public import Linglib.Data.Examples.Embick2021
public import Linglib.Morphology.DistributedMorphology.Locality

/-!
# Embick (2021): The Motivation for Roots in Distributed Morphology

This file formalizes [embick-2021]'s case for category-free roots. The Two Domains Intuition (1),
that some form–meaning connections are fixed close to a lexical primitive and others are built
compositionally, is explained not by the word, as lexicalism (5) has it, but by syntactic locality
around roots. Following [marantz-1997]'s update of [chomsky-1970], derived nominals combine the
root directly with n and gerunds nominalize a verbal structure, (8) and (9); agents are licensed
only by a Voice that selects v, the Agent-Licensing Assumption (10), so *growth* has no agentive
reading while *growing* does, and *destruction* gets one only from its encyclopedically agentive
root, (6) and (7). In the Roots-and-contexts theory of §5 the category-defining heads are cyclic:
a head attached to the categorized root may show root-determined allomorphy and a special
interpretation while an outer cyclic head may not, the generalizations (13) of
[embick-marantz-2008] and structure (14), whereas an outer noncyclic head, the tense of *ben-t* or
the aspect of *brok-en*, is still local to the root, structure (15). Since *growth* and *growing*
are both words, the word cannot be the domain; the domains are the cycles.

## Implementation notes

* Cycles and the root's domain are the substrate's `ComplexHead` API, the cyclic domains of
  [embick-2010] that the paper adopts for (14) and (15); this file contributes the heads of the
  examples, the Agent-Licensing Assumption, the rows and the predictions checked over them.
* The gerund's verbal structure is taken as v with the agent-licensing Voice above it, the second
  option of (10).
* The examples are `Data.Examples.Embick2021`.

## References

* [embick-2021]
* [chomsky-1970]
* [marantz-1997]
* [embick-marantz-2008]
* [embick-2010]
-/

@[expose] public section

namespace Embick2021

open DistributedMorphology Embick2021.Examples

/-- The heads of the examples are the categorizers, Voice, tense and aspect. -/
inductive Head
  | n
  | v
  | a
  | voice
  | tense
  | aspect
  deriving DecidableEq, Repr

/-- The category-defining heads are the cyclic heads (§5). -/
def cyclic (h : Head) : Prop := h = .n ∨ h = .v ∨ h = .a

instance : DecidablePred cyclic := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The Agent-Licensing Assumption (10): an agent is introduced by a Voice that selects v, so only
a structure with v below Voice licenses one. -/
def AgentLicensed (s : ComplexHead Root Head) : Prop :=
  ∃ i : Fin s.heads.length, s.heads[i] = .voice ∧ ∃ j < i, s.heads[j] = .v

instance (s : ComplexHead Root Head) : Decidable (AgentLicensed s) :=
  inferInstanceAs (Decidable (∃ i, _ ∧ ∃ j < i, _))

/-! ### The words -/

/-- Whether the root is encyclopedically agentive, *destroy*, or not, *grow* (§4). -/
inductive RootClass
  | agentive
  | nonagentive
  deriving DecidableEq, Repr

/-- Derived nominal, gerund, or inflected verb. -/
inductive Construction
  | derivedNominal
  | gerund
  | inflected
  deriving DecidableEq, Repr

/-- A word of the examples records its heads above the root, the root's class where the paper
gives one, its construction, and the paper's judgment of the agentive reading. -/
structure Row where
  spine : ComplexHead Root Head
  rootClass : Option RootClass
  construction : Construction
  judgment : Judgment
  deriving Repr

/-- The heads as named in the rows. -/
def headTable : List (String × Head) :=
  [("n", .n), ("v", .v), ("a", .a), ("voice", .voice), ("T", .tense), ("aspect", .aspect)]

/-- The root classes as named in the rows. -/
def rootClassTable : List (String × RootClass) :=
  [("agentive", .agentive), ("nonagentive", .nonagentive)]

/-- The constructions as named in the rows. -/
def constructionTable : List (String × Construction) :=
  [("derivedNominal", .derivedNominal), ("gerund", .gerund), ("inflected", .inflected)]

/-- The roots of the pool, indexed by first occurrence. -/
def rootNames : List String := (Examples.all.filterMap (·.feature? "root")).eraseDups

/-- A row from an example, its heads innermost first. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let root ← ex.feature? "root"
  let construction ← ex.parse? "construction" constructionTable
  pure ⟨⟨⟨rootNames.idxOf root⟩, ["h1", "h2", "h3"].filterMap (ex.parse? · headTable)⟩,
    ex.parse? "rootClass" rootClassTable, construction, ex.judgment⟩

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by decide

/-- The nominalizations of (6) and (7) and the inflected verbs of §5. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-! ### Nominalizations, (6)–(10) -/

theorem agentive_possessor_rows :
    ∀ r ∈ rows, ∀ c, r.rootClass = some c →
      (r.judgment = .acceptable ↔ (AgentLicensed r.spine ∨ c = .agentive)) := by
  decide

/-- A derived nominal is a root noun, (8): no v, so no agent-licensing Voice. -/
theorem derivedNominal_not_agentLicensed :
    ∀ r ∈ rows, r.construction = .derivedNominal → ¬ AgentLicensed r.spine := by
  decide

/-! ### Inner and outer heads, (13)–(15) -/

/-- The gerund's n is not local to the root ((9), (14)), whereas the derived nominal's n is ((8),
(13)). -/
theorem gerund_n_not_rootLocal :
    ∀ r ∈ rows, ∀ i : Fin r.spine.heads.length, r.spine.heads[i] = .n →
      (r.spine.RootLocal cyclic i ↔ r.construction = .derivedNominal) := by
  decide

/-- Tense and aspect outside the verbalizer are local to the root, (15): *ben-t*, *brok-en*. -/
theorem inflection_rootLocal :
    ∀ r ∈ rows, r.construction = .inflected → ∀ i : Fin r.spine.heads.length,
      r.spine.RootLocal cyclic i := by
  decide

end Embick2021
