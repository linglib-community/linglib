/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Logic.Function.FactorsThrough
public import Linglib.Core.Order.Cover
public import Linglib.Data.Wordlist.Booij2010
public import Linglib.Fragments.Dutch.Verbs
public import Linglib.Logic.Nonmonotonic.Inheritance
public import Linglib.Morphology.ConstructionMorphology.Schema
public import Linglib.Syntax.Cat
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.FinCases

/-!
# Booij (2010): Construction Morphology

This file formalizes the constructional schemas of Booij's programmatic article: a complex
word is a construction licensed by a schema in a hierarchical lexicon, and a schema both
motivates the words stored below it and coins new ones. The deadjectival *-ness* schema is
the abstraction over the stored nouns of the opening word set, the meet of their descriptions
(`nessSchema_body_eq_inf`), and coining is unification: unifying *carless* with the schema
returns *carlessness* (`carlessness_unifies`), the novel coin the schema generates over the
stored nouns while relating the listed *awareness* (`carlessness_generates`,
`awareness_related`). The English compound schemas form a hierarchy ordered by generality,
the right-headed schema over the nominal schema over its four subcases (`nominal_covBy_general`,
`covBy_nominal`); right-headedness is the coindexation of head and whole, shared by every
schema of the family without a Right-hand Head Rule (`compound_right_headed`), while the AN
subschema overrides the recursive-modifier default that the NN subschema inherits
(`compound_inheritance`). Dutch *-baar* is the paper's demand for default inheritance: the
hierarchy of the schema and its words is derived from their descriptions, the regular
*leesbaar* inherits the schema's transitive base (`leesbaar_inherits`), and *werkbaar*, whose
base the Dutch verb fragment records as intransitive, overrides it (`werkbaar_overrides`).
Schema unification composes *on-* prefixation with *-baar* suffixation into one schema whose
instances are exactly their common instances (`onbaar_unifies`,
`onbaarSchema_instantiates_iff`), so *onbedwingbaar* is generated over the empty lexicon, with
no intermediate *bedwingbaar* listed (`onbedwingbaar_generates`).

## Implementation notes

* The words are the CLDF forms of `Data/Wordlist/Booij2010.json`, read as slot-indexed segments
  on the flat carrier by `Data.Wordlist.Form.slots`. The *-ness* and *-baar* schemas are over the
  two slots base and affix, and the *on-V-baar* schema over prefix, base and suffix, so the
  embedding `[on [V baar]]` of the paper's display is the concatenation of three slots; the
  two-slot *-baar* schema is the three-slot one read at base and suffix
  (`baarSchema_eq_comap`).
* The compound schemas are over the category tier alone, valued in `PhraseStructure.Cat`; the
  phonological variables and the semantic relation of the paper's display are not modelled.
* A defeasible specification is an attribute beside the description: the description is
  matched monotonically by unification, the attribute inherited by default
  (`DefaultInheritance.inherited`). A regular word stores no value of its own, since the paper
  counts all its information as redundant, and the exceptional word stores the transitivity
  of its base as the Dutch verb fragment records it.
* The holistic constructions (Malay reduplication, Romance VN compounds, the intensifying
  compounds, Maale *nayi*), the phrasal constructional idioms and the inflectional schemas
  are not formalized.

## References

* [booij-2010-compass]
* [booij-2010]
-/

@[expose] public section

namespace Booij2010

open ConstructionMorphology DefaultInheritance PhraseStructure

/-! ### The deadjectival *-ness* schema -/

/-- The schema `[[x]A ness]N` of (3) over the slots base and affix: the base an open variable,
the affix pinned to *-ness*. -/
def nessSchema : Schema (Fin 2) (Flat String) := Schema.productive ![⊥, ↑"ness"]

/-- The stored nouns in *-ness*: the opening word set (1b) and *awareness* (2). -/
def nessLexicon : Set (Fin 2 → Flat String) :=
  {Wordlist.baldness.slots, Wordlist.bigness.slots, Wordlist.blackness.slots,
    Wordlist.britishness.slots, Wordlist.awareness.slots}

/-- The schema is the abstraction over the stored nouns of (1b): the meet of their descriptions
keeps the shared affix and leaves a variable where the bases differ. -/
theorem nessSchema_body_eq_inf :
    nessSchema.body = Wordlist.baldness.slots ⊓ Wordlist.bigness.slots ⊓ Wordlist.blackness.slots ⊓
      Wordlist.britishness.slots := by
  funext i
  fin_cases i <;> decide

/-- Any word whose affix is *-ness* instantiates the schema. -/
theorem ness_instantiates {w : Fin 2 → Flat String} (h : w 1 = ↑"ness") :
    nessSchema.Instantiates w := by
  intro i
  fin_cases i
  · exact bot_le
  · exact h.ge

theorem carlessness_instantiates : nessSchema.Instantiates Wordlist.carlessness.slots :=
  ness_instantiates (by decide)

/-- Coining is unification: unifying the adjective *carless* with the schema returns the
construct *carlessness*. -/
theorem carlessness_unifies :
    PartialUnify.unify nessSchema.body Wordlist.carlessness.slots =
      WithTop.some Wordlist.carlessness.slots :=
  nessSchema.instantiates_iff_unify.mp carlessness_instantiates

theorem nessSchema_isProductive : nessSchema.IsProductive := Schema.isProductive_productive _

/-- The schema's generative role: it coins the novel *carlessness* over the stored nouns, its
open base taking an unlisted adjective. -/
theorem carlessness_generates :
    nessSchema.Generates nessLexicon Wordlist.carlessness.slots :=
  nessSchema_isProductive.generates_iff.2 carlessness_instantiates

/-- The schema's relational role: it motivates the listed *awareness*. -/
theorem awareness_related : nessSchema.Relates nessLexicon Wordlist.awareness.slots :=
  ⟨by simp [nessLexicon], ness_instantiates (by decide)⟩

/-! ### The compound hierarchy

The right-headed schema for all English compounds dominates the nominal schema (6), which
dominates the NN, VN, AN and PN subcases (7). The hierarchy is derived from the schemas by
generality, and each schema is read at the positions modifier, head and whole through one
subscripting, which coindexes the head with the whole. -/

/-- The category variables of a compound schema: the modifier's `X` and the head's `Y`. -/
inductive CompoundVar | x | y
  deriving DecidableEq, Fintype

/-- The positions modifier, head and whole, subscripted as in (6): the whole shares the head's
category. -/
def compoundSub : Fin 3 → CompoundVar := ![.x, .y, .y]

/-- The compound schema with the modifier's category `x` and the head's `y`, each a variable
at `⊥`. -/
def compoundSchema (x y : Flat Cat) : Schema CompoundVar (Flat Cat) :=
  Schema.productive fun | .x => x | .y => y

/-- The nodes of the hierarchy: the right-headed schema for all compounds, the nominal schema
(6) and its four subcases (7). -/
inductive CompoundNode | general | nominal | nn | vn | an | pn
  deriving DecidableEq, Fintype

/-- The schema at each node: the general schema leaves both categories open, the nominal
schema pins the head to N, and a subcase pins the modifier too. -/
def compoundFamily : CompoundNode → Schema CompoundVar (Flat Cat)
  | .general => compoundSchema ⊥ ⊥
  | .nominal => compoundSchema ⊥ ↑Cat.N
  | .nn => compoundSchema ↑Cat.N ↑Cat.N
  | .vn => compoundSchema ↑Cat.V ↑Cat.N
  | .an => compoundSchema ↑Cat.Adj ↑Cat.N
  | .pn => compoundSchema ↑Cat.P ↑Cat.N

/-- The hierarchical lexicon of English compounds, ordered by the generality of the schemas. -/
instance : PartialOrder CompoundNode := Schema.generalityOrder compoundFamily (by decide)

instance : DecidableLE CompoundNode := fun a b ↦
  inferInstanceAs (Decidable ((compoundFamily b).body ≤ (compoundFamily a).body))

instance : DecidableLT CompoundNode := decidableLTOfDecidableLE

/-- The nominal schema (6) lies immediately below the general right-headed schema. -/
theorem nominal_covBy_general : CompoundNode.nominal ⋖ .general := by decide

/-- Each subcase of (7) lies immediately below the nominal schema (6). -/
theorem covBy_nominal :
    ∀ n : CompoundNode, n ≠ .general → n ≠ .nominal → n ⋖ .nominal := by
  decide

/-- Right-headedness needs no rule: in any instance of any schema of the family read through
the subscripting of (6), the whole's category is the head's. -/
theorem compound_right_headed (n : CompoundNode) {w : Fin 3 → Flat Cat}
    (h : (compoundFamily n).InstantiatesAt compoundSub w) : w 2 = w 1 :=
  (Schema.instantiatesAt_iff.1 h).2 (by decide)

/-- *blackbird*, an adjective and a noun making a noun, instantiates the AN subschema and not
the NN subschema. -/
theorem blackbird_instantiatesAt :
    (compoundFamily .an).InstantiatesAt compoundSub ![↑Cat.Adj, ↑Cat.N, ↑Cat.N] ∧
      ¬ (compoundFamily .nn).InstantiatesAt compoundSub ![↑Cat.Adj, ↑Cat.N, ↑Cat.N] := by
  simp only [Schema.instantiatesAt_iff]
  decide

/-- Whether the modifier may itself be a compound (8): allowed by the general schema, forbidden
at the AN subschema. -/
def recursiveModifier : CompoundNode → Option Bool
  | .general => some true
  | .an => some false
  | _ => none

/-- The NN subschema inherits the recursive modifier through the nominal schema, and the AN
subschema overrides it. -/
theorem compound_inheritance :
    inherited recursiveModifier .nn = {true} ∧ inherited recursiveModifier .an = {false} :=
  ⟨inherited_eq_singleton_of_isLeast (m := .general) (by decide) rfl,
    inherited_eq_singleton_of_eq_some rfl⟩

/-! ### Default inheritance: *-baar* and *werkbaar*

The suffix *-baar* attaches to transitive verbs, *leesbaar* from *lezen*, yet *werkbaar* is
formed on the intransitive *werken*. The words lie below the schema in the hierarchy because
they instantiate it, and the transitivity of the base is a defeasible specification that the
exceptional word overrides. -/

/-- The nodes of the *-baar* hierarchy: the schema `[V baar]A`, the regular *leesbaar* and the
exceptional *werkbaar*. -/
inductive BaarNode | schema | leesbaar | werkbaar
  deriving DecidableEq, Fintype

/-- The *-baar* schema over the slots base and affix, the base open. -/
def baarSchema : Schema (Fin 2) (Flat String) := Schema.productive ![⊥, ↑"baar"]

/-- The description at each node: the schema, or a word with no variable. -/
def baarFamily : BaarNode → Schema (Fin 2) (Flat String)
  | .schema => baarSchema
  | .leesbaar => ⟨Wordlist.leesbaar.slots, ∅⟩
  | .werkbaar => ⟨Wordlist.werkbaar.slots, ∅⟩

/-- The *-baar* hierarchy, ordered by the generality of the descriptions. -/
instance : PartialOrder BaarNode := Schema.generalityOrder baarFamily (by decide)

instance : DecidableLE BaarNode := fun a b ↦
  inferInstanceAs (Decidable ((baarFamily b).body ≤ (baarFamily a).body))

/-- Both words instantiate the schema, so the schema dominates them. -/
theorem le_schema : ∀ n : BaarNode, n ≤ .schema := by decide

/-- Whether the base verb is transitive: the schema's default is transitive, the regular
*leesbaar* stores nothing, and *werkbaar* stores the transitivity of *werken* as the Dutch verb
fragment records its basic frame. -/
def baseTransitive : BaarNode → Option Bool
  | .schema => some true
  | .leesbaar => none
  | .werkbaar => Dutch.Verbs.werken.valency.frames.head?.map fun fr ↦ decide fr.IsTransitive

/-- The regular word inherits the schema's transitive base. -/
theorem leesbaar_inherits : inherited baseTransitive .leesbaar = {true} :=
  inherited_eq_singleton_of_isLeast (m := .schema) (by decide) rfl

/-- The exceptional word overrides the inherited transitivity of its base. -/
theorem werkbaar_overrides : inherited baseTransitive .werkbaar = {false} :=
  inherited_eq_singleton_of_eq_some (by decide)

/-- The default fits the regular word: the fragment's *lezen* is transitive. -/
theorem lezen_isTransitive : ∃ fr ∈ Dutch.Verbs.lezen.valency.frames, fr.IsTransitive := by
  decide

/-! ### Schema unification: *on-* with *-baar*

Negative *on-* prefixation and deverbal *-baar* suffixation unify into one schema
`[on [V baar]A]A` (16), so *onbedwingbaar* is coined directly from the verb without the
intermediate *bedwingbaar* being listed. The unification is over the three slots prefix, base
and suffix. -/

/-- The *on-* schema `[on A]A` over prefix, base and suffix: the prefix pinned, the rest open. -/
def onSchema : Schema (Fin 3) (Flat String) := Schema.productive ![↑"on", ⊥, ⊥]

/-- The *-baar* schema over prefix, base and suffix: the suffix pinned, the rest open. -/
def baarSchema₃ : Schema (Fin 3) (Flat String) := Schema.productive ![⊥, ⊥, ↑"baar"]

/-- The unified schema `[on [V baar]A]A`: both affixes pinned, the base open. -/
def onbaarSchema : Schema (Fin 3) (Flat String) := Schema.productive ![↑"on", ⊥, ↑"baar"]

/-- The two-slot *-baar* schema of the hierarchy is the three-slot one read at base and
suffix. -/
theorem baarSchema_eq_comap : baarSchema₃.comap ![1, 2] = baarSchema :=
  Schema.ext (funext fun i ↦ by fin_cases i <;> rfl)
    (Set.ext fun i ↦ by fin_cases i <;> simp [baarSchema₃, baarSchema])

/-- The *on-* and *-baar* descriptions unify into the *on-V-baar* description (16). -/
theorem onbaar_unifies :
    PartialUnify.unify onSchema.body baarSchema₃.body = ↑onbaarSchema.body := by decide

/-- The unified schema's instances are exactly the words at once *on-* prefixed and *-baar*
suffixed. -/
theorem onbaarSchema_instantiates_iff {w : Fin 3 → Flat String} :
    onbaarSchema.Instantiates w ↔ onSchema.Instantiates w ∧ baarSchema₃.Instantiates w :=
  Schema.instantiates_iff_of_unify_eq_coe onbaar_unifies

/-- The unified schema coins *onbedwingbaar* over the empty lexicon: no intermediate
*bedwingbaar* need be listed. -/
theorem onbedwingbaar_generates : onbaarSchema.Generates ∅ Wordlist.onbedwingbaar.slots :=
  (Schema.isProductive_productive _).generates_iff.2 (by decide)

end Booij2010
