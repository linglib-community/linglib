module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.ConstructionGrammar.Constructicon
public import Linglib.Syntax.ConstructionGrammar.Licensing
public import Linglib.Semantics.ConventionalImplicature
public import Linglib.Data.Examples.GoldbergShirtz2025

/-!
# Goldberg and Shirtz (2025): The English Phrase-as-Lemma Construction

This file formalizes Goldberg and Shirtz's phrase-as-lemma (PAL) construction: a phrase used in
a slot reserved for a word ("a trickle-down policy", "the 'both sides do it' argument"), whose
lemma-like construal presents the situation type as familiar to speaker and addressee, with wit and
sarcasm as rhetorical effects of discussing the presumed familiar. Five preregistered forced-choice
surveys found PAL sentences judged to imply more common knowledge than close paraphrases, and to be
wittier and more sarcastic, robustly to PAL frequency, and found four narrowly defined subtypes
(*must-V*, *a simple ⟨PAL⟩*, *Don't ⟨PAL⟩ me*, *the old ⟨PAL⟩ N*) judged more natural than
minimally different foils.

The paper's Figure 5 network is a `Constructicon` (`figure5`): the prenominal PAL construction
inherits in normal mode from both the NN compound and adjectival modification, which conflict on
whether the output is a word and on stress (`mothers_conflict`), so PAL states exactly those
properties and inherits the rest (`inherited_palN`). The zero-level PAL and the four conventional
subtypes are joined to it by motivation links, and removing PAL leaves a phrase in a word slot
unlicensed (`pal_load_bearing`). The attested tokens of example (1) and Tables 2–3 and the
comparable constructions of section 7 are rows: PALs occupy every word-class slot and take that
slot's inflection (`rows_inflection`), and the host frame of a comparable construction need not be a
compound (`hostFrames_complete`).

## Implementation notes

Only the two thick arrows of Figure 5 are inheritance links; its thin two-headed arrows are
motivation links, which pass no information down. The experimental statistics stay in the
paper. The lemma-like familiarity is recorded as not-at-issue content, although the paper treats
it as an invited construal that speakers exploit precisely for situation types that are not
antecedently familiar.

## References

* [goldberg-shirtz-2025]
* [goldberg-1995]
* [meibauer-2007]
* [trips-kornfilt-2015]
* [sag-2012]
-/

@[expose] public section

namespace GoldbergShirtz2025

open ConstructionGrammar

/-! ### The Figure 5 constructicon -/

/-- In the prenominal PAL construction a zero-level PAL whose internal syntax
is phrasal modifies a head N, forming an N′ (the paper's structure (7),
`[N′ PAL⁰ N]`, vs. the NN compound's `[N⁰ N⁰ N⁰]`). Whether the head N is a word
is left underspecified since PALs may modify nouns with complements
("a 'don't mess with me' type of driver"). -/
def palConstruction : Construction Unit :=
  { form :=
      [ { filler := .phrasal, lex := some true }
      , { filler := .open_ .NOUN, isHead := true } ]
  , meaning := ()
  , pragmaticPoint := true }

/-- The semiproductive must-V subtype, frequently instantiated by
*must-read*, *must-see*, *must-have*. Study 5 tested only rare tokens
(≤ 10 COCA hits) against *should-V* foils. -/
def mustVerbConstruction : Construction Unit :=
  { form :=
      [ { filler := .fixed "must" }
      , { filler := .open_ .VERB }
      , { filler := .open_ .NOUN, isHead := true } ]
  , meaning := ()
  , pragmaticPoint := true }

/-- In the *a simple ⟨PAL⟩* subtype the PAL is itself the head noun, with
*simple* marking the situation type as routine ("Could've tried a simple
'I'm sorry.'"). Study 5's foils used *a short*. -/
def aSimplePALConstruction : Construction Unit :=
  { form :=
      [ { filler := .fixed "a" }
      , { filler := .fixed "simple" }
      , { filler := .phrasal, lex := some true
        , isHead := true } ]
  , meaning := ()
  , pragmaticPoint := true }

/-- In the *Don't ⟨PAL⟩ me* subtype the PAL fills a V slot, must quote the
immediately preceding discourse, and occurs in an interdiction context
(A says "you're welcome", B replies "No, don't 'you're welcome' me."). Study 5's
foils broke exactly the quote-from-context or interdiction condition. -/
def dontPALmeConstruction : Construction Unit :=
  { form :=
      [ { filler := .fixed "Don't" }
      , { filler := .phrasal, lex := some true
        , isHead := true }
      , { filler := .fixed "me" } ]
  , meaning := ()
  , pragmaticPoint := true }

/-- The *the old ⟨PAL⟩ (N)* subtype, with optional head N and *old*
marking the situation type as conventional ("my dad pulled the old 'I'm
going to the store for smokes, be back in five'"). Study 5's foils used
*the tired*. -/
def theOldPALConstruction : Construction Unit :=
  { form :=
      [ { filler := .fixed "the" }
      , { filler := .fixed "old" }
      , { filler := .phrasal, lex := some true
        , isHead := true }
      , { filler := .open_ .NOUN } ]
  , meaning := ()
  , pragmaticPoint := true }

/-- The NN compound construction is a parent of PAL, passing down internal stress and a tight
unit. -/
def nnCompound : Construction Unit :=
  { form :=
      [ { filler := .open_ .NOUN, lex := some true }
      , { filler := .open_ .NOUN, isHead := true
        , lex := some true } ]
  , meaning := () }

/-- The adjectival modification construction is a parent of PAL, passing down the prenominal
slot. -/
def adjNModification : Construction Unit :=
  { form :=
      [ { filler := .open_ .ADJ, lex := some true }
      , { filler := .open_ .NOUN, isHead := true
        , lex := some false } ]
  , meaning := () }

/-! ### Degrees of abstraction (Table 8) -/

/-- *Veggie-wrap*, a fully lexically specified noun compound (the top row
of Table 8). -/
def veggieWrapForm : TypedForm String :=
  [ { filler := .fixed "veggie" }
  , { filler := .fixed "wrap", isHead := true } ]

/-- The constructicon realizes Table 8's grid of degrees of abstraction. -/
theorem table8_specificity :
    derivedSpecificity veggieWrapForm = .lexicallySpecified ∧
    aSimplePALConstruction.specificity = .partiallyOpen ∧
    nnCompound.specificity = .fullyAbstract ∧
    palConstruction.specificity = .fullyAbstract := by decide

/-- The zero-level PAL, a phrase in a word-level position, with its familiar tokens
(*do-it-yourself*, *know-it-all*, *pay-as-you-go*). -/
def zeroLevelPAL : Construction Unit :=
  { form := [{ filler := .phrasal, lex := some true }]
  , meaning := ()
  , pragmaticPoint := true }

/-- The constructions of Figure 5. -/
inductive Figure5 where
  /-- The NN compound, N⁰ modifies N⁰. -/
  | nnCompound
  /-- Adjectival modification, Adj modifies N′. -/
  | adjN
  /-- The prenominal PAL construction, PAL⁰ modifies N, at the center of the figure. -/
  | palN
  /-- The zero-level PAL. -/
  | pal
  /-- *must-V*. -/
  | mustV
  /-- *a simple ⟨PAL⟩*. -/
  | aSimple
  /-- *Don't ⟨PAL⟩ me*. -/
  | dontMe
  /-- *the old ⟨PAL⟩ (N)*. -/
  | theOld
  deriving DecidableEq, Fintype

/-- The construction at each node of Figure 5. -/
def construction : Figure5 → Construction Unit
  | .nnCompound => nnCompound
  | .adjN => adjNModification
  | .palN => palConstruction
  | .pal => zeroLevelPAL
  | .mustV => mustVerbConstruction
  | .aSimple => aSimplePALConstruction
  | .dontMe => dontPALmeConstruction
  | .theOld => theOldPALConstruction

/-- Figure 5. The prenominal PAL construction inherits in normal mode from the NN compound and
from adjectival modification, the two thick arrows. The zero-level PAL and the conventional
subtypes are joined to it by the thin two-headed arrows, *must-V* and *Don't ⟨PAL⟩ me* through
the zero-level PAL; these motivate the subtypes and pass no information down. The caption calls
the arrows "motivation and (normal mode) inheritance links" and assigns none of the link types of
[goldberg-1995]. -/
def figure5 : Constructicon Figure5 Unit where
  cxn := construction
  mothers
    | .palN => [(.nnCompound, none), (.adjN, none)]
    | _ => []
  related
    | .palN => [(.pal, none), (.aSimple, none), (.theOld, none)]
    | .pal => [(.mustV, none), (.dontMe, none)]
    | _ => []

/-- The depth of a construction below those it inherits from. -/
def Figure5.rank : Figure5 → ℕ
  | .palN => 1
  | _ => 0

instance : PartialOrder Figure5 := figure5.partialOrder Figure5.rank (by decide)

instance : DecidableLE Figure5 := figure5.decidableLE [.nnCompound, .adjN] (by decide)

theorem isMother_iff (c m : Figure5) :
    figure5.IsMother c m ↔ c = .palN ∧ (m = .nnCompound ∨ m = .adjN) := by
  revert c m; decide

/-! ### Two mothers force normal-mode inheritance (§6)

The form-side properties at issue in Figure 5, each stated by the constructions that specify it
and inherited by `DefaultInheritance.inherited` over the network's order. PAL N's two mothers
conflict, the NN compound yielding an N⁰ with stress within the modifier and adjectival
modification an N′ with head stress, so were PAL N to state neither property it would inherit
both values of each (`mothers_conflict`): "specifications in two mother nodes may conflict with one
another", which makes complete inheritance "unsuitable whenever a node is allowed more than a
single mother". PAL N states exactly those two properties, and inherits the rest
(`inherited_palN`). -/

/-- The locus of primary stress in a modification construction is within the modifier for
compound stress (*BLACKbird*) and on the head for phrasal modification (*black BIRD*). -/
inductive StressLocus where
  | modifier
  | head
  deriving DecidableEq, Repr

/-- Position of the modifier slot relative to the head. -/
inductive ModPosition where
  | prenominal
  | postnominal
  deriving DecidableEq, Repr

/-- Whether a construction's output can recur inside the construction's own open slot. -/
inductive SelfEmbedding where
  | allowed
  | banned
  deriving DecidableEq, Repr

open DefaultInheritance

/-- A construction may state whether its output is a word. PAL N forms an N′, a phrase, with
adjectival modification and against the compound's N⁰, a word. -/
def lex : Figure5 → Option Bool
  | .nnCompound => some true
  | .adjN | .palN => some false
  | _ => none

/-- The position of the modifier slot, which both mothers state and PAL N does not. -/
def modPosition : Figure5 → Option ModPosition
  | .nnCompound | .adjN => some .prenominal
  | _ => none

/-- A construction may state the locus of primary stress. PAL N forms "a tight semantic and
phonological unit", with the stress within the PAL as in the compound, against adjectival
modification. -/
def stress : Figure5 → Option StressLocus
  | .nnCompound | .palN => some .modifier
  | .adjN => some .head
  | _ => none

/-- A construction may state whether its output self-embeds. Adjectival modification bans it,
and "like Adj + N combinations, the PAL N construction cannot be recursively embedded within
another PAL N construction". -/
def selfEmbedding : Figure5 → Option SelfEmbedding
  | .adjN => some .banned
  | _ => none

theorem mothers_conflict :
    inherited (Function.update lex .palN none) .palN = {true, false} ∧
      inherited (Function.update stress .palN none) .palN = {.modifier, .head} := by
  refine ⟨Set.ext fun v ↦ ?_, Set.ext fun v ↦ ?_⟩ <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> cases v <;> decide

theorem inherited_palN :
    inherited lex .palN = {false} ∧ inherited modPosition .palN = {.prenominal} ∧
      inherited stress .palN = {.modifier} ∧ inherited selfEmbedding .palN = {.banned} := by
  refine ⟨inherited_eq_singleton_of_eq_some rfl, Set.ext fun v ↦ ?_,
    inherited_eq_singleton_of_eq_some rfl,
    inherited_eq_singleton_of_isLeast (m := .adjN) (by decide) rfl⟩
  rw [Set.mem_singleton_iff]; cases v <;> decide

/-! ### Licensing: PAL is load-bearing

A minimal demonstration with the licensing relation (`Licenses`): the attested "a must-do task"
(the paper's ex. (1b), determiner elided) parses as a phrase-daughter in the modifier slot plus a
head noun. The constructions of Figure 5 license it through the PAL construction, and without PAL
it is rejected: the phrase-in-word-slot configuration has no other license. -/

/-- The internal syntax of the *must-do* PAL, must-V (cf. `mustVerbConstruction`, which is the
full prenominal construction). -/
def mustVCore : Construction Unit :=
  { form :=
      [ { filler := .fixed "must" }
      , { filler := .open_ .VERB, isHead := true } ]
  , meaning := () }

/-- The constructions of Figure 5 and the must-V-internal construction. -/
def demoInventory : List (Construction Unit) :=
  mustVCore ::
    [.nnCompound, .adjN, .palN, .pal, .mustV, .aSimple, .dontMe, .theOld].map construction

/-- In "must-do task" (ex. (1b), determiner elided) the PAL phrase is a constituent daughter in
the word-level modifier slot. -/
def mustDoTask : PhraseStructure.Tree Unit Morphology.Word :=
  .node () [.node () [.leaf (.mk' "must" .AUX), .leaf (.mk' "do" .VERB)], .leaf (.mk' "task" .NOUN)]

theorem demo_licenses_mustDoTask : Licenses demoInventory mustDoTask := by decide

theorem pal_load_bearing :
    ¬ Licenses (demoInventory.erase palConstruction) mustDoTask := by decide

/-- A PAL utterance has a two-part meaning. The head noun's denotation is at-issue (an instance of
the situation type), and the lemma-like construal contributes, as not-at-issue content, that the
situation type itself is presumed familiar ("presumes familiarity with 'PAL'", Figure 5).

The paper treats the familiarity as an invited *as-if* construal rather than a hard definedness
condition. Speakers exploit the construction precisely for situation types that are not
antecedently familiar (observational humor, sniglets), so common-ground satisfaction is typically
reached by accommodation or pretense, not antecedent entailment. -/
def palMeaning (W : Type*) (situationType headNoun : W → Prop) :
    ConventionalImplicature.TwoDim W (W → Prop) :=
  ⟨headNoun, situationType⟩

/-! ### Irreducibility -/

/-- The PAL construction is not fully compositional. Pairing
phrase-in-a-word-slot form with a presumed-familiarity function is a
construction-specific pragmatic function, so PAL cannot be decomposed into
the three universal combination schemata (see `Construction.IsFullyCompositional`). -/
theorem pal_irreducible :
    ¬ palConstruction.IsFullyCompositional := by decide

theorem pal_form_phrase_in_word_slot :
    ∃ s ∈ palConstruction.form, s.IsPhraseInWordSlot := by decide

/-! ### Attested tokens

PALs prototypically modify nouns but occur as head nouns, predicative adjectives, and verbs
(Table 2), and take the word-level inflection of the slot they fill (Table 3). -/

/-- The word-class slot a PAL fills. -/
inductive PALPosition where
  | prenominalModifier
  | headNoun
  | predicativeAdjective
  | verb
  deriving DecidableEq, Fintype

/-- Word-level inflection attested on a PAL. -/
inductive Inflection where
  | plural
  | agentivePlural
  | gerund
  deriving DecidableEq

/-- An affix is the inflection of a slot, nominal for the plural and agentive *-er* and verbal
for *-ing*. -/
def Inflection.position : Inflection → PALPosition
  | .plural | .agentivePlural => .headNoun
  | .gerund => .verb

/-- An attested English PAL records its slot and any inflection it carries. -/
structure Row where
  position : PALPosition
  inflection : Option Inflection
  deriving DecidableEq

def Row.ofDatum (ex : Datum) : Option Row := do
  let position ← ex.parse? "position"
    [("prenominal modifier", .prenominalModifier), ("head noun", .headNoun),
     ("predicative adjective", .predicativeAdjective), ("verb", .verb)]
  pure ⟨position, ex.parse? "inflection"
    [("plural", .plural), ("agentive -er + plural", .agentivePlural), ("gerund", .gerund)]⟩

/-- The English tokens of (1a)–(1c), Table 2, and Table 3. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- PALs are attested in every word-class slot (Table 2). -/
theorem rows_position : ∀ p : PALPosition, ∃ r ∈ rows, r.position = p := by decide

/-- A PAL takes the inflection of the slot it fills (Table 3). -/
theorem rows_inflection : ∀ r ∈ rows, ∀ i ∈ r.inflection, i.position = r.position := by decide

/-! ### Comparable constructions in other languages (section 7) -/

/-- A comparable construction is hosted by a compound(-like) frame in West Germanic and
Turkish, where the compound marker sits on the head noun, or the complement of a preposition in
Hebrew and Brazilian Portuguese. -/
inductive PALHostFrame where
  | compound
  | prepositionComplement
  deriving DecidableEq, Fintype

/-- The host frames of the German, Dutch, Afrikaans, Turkish, Hebrew, and Brazilian Portuguese
PALs of (8) and (15)–(18). -/
def hostFrames : List PALHostFrame :=
  Examples.all.filterMap fun ex ↦ ex.parse? "hostFrame"
    [("compound", .compound), ("preposition complement", .prepositionComplement)]

example : rows.length + hostFrames.length = Examples.all.length := by decide

theorem hostFrames_complete : ∀ f : PALHostFrame, f ∈ hostFrames := by decide

end GoldbergShirtz2025
