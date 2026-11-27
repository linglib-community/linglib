module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.ConstructionGrammar.Constructicon
public import Linglib.Syntax.ConstructionGrammar.Composition
public import Linglib.Logic.Nonmonotonic.Inheritance
public import Linglib.Semantics.ConventionalImplicature
public import Linglib.Data.Examples.GoldbergShirtz2025
public import Linglib.Data.Examples.Readers

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
subtypes are joined to it by motivation links.

The construction's meaning is a composition rule (`palRule`): it modifies the head noun as
postnominal modification by the same phrase does, and adds as not-at-issue content that the
situation type the phrase depicts is familiar. For a sentence pair of Table 6 the PAL and its
paraphrase get the same at-issue content and differ in that presumption (`interps_palNP`,
`interps_paraphraseNP`), and without the PAL construction the phrase in the word slot has no
reading (`interps_palNP_phrasal`). The attested tokens of example (1) and Tables 2–3 and the
comparable constructions of section 7 are rows: PALs occupy every word-class slot and take that
slot's inflection (`rows_inflection`), and the host frame of a comparable construction need not be a
compound (`hostFrames_complete`).

## Implementation notes

Only the two thick arrows of Figure 5 are inheritance links; its thin two-headed arrows are
motivation links, which pass no information down. The experimental statistics stay in the
paper. The lemma-like familiarity is recorded as not-at-issue content, although the paper treats
it as an invited construal that speakers exploit precisely for situation types that are not
antecedently familiar. The constructions inside the PAL and in the paraphrase (the verb phrase,
the infinitive, the determined noun, postnominal modification) are a minimal fragment for the one
sentence pair, and the relation `depicts` between a head noun's referent and a situation type is
left a parameter.

## References

* [goldberg-shirtz-2025]
* [goldberg-1995]
* [meibauer-2007]
* [trips-kornfilt-2015]
* [sag-2012]
-/

@[expose] public section

namespace GoldbergShirtz2025

open Examples (PALPosition Inflection PALHostFrame)

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
  , meaning := () }

/-- The semiproductive must-V subtype, frequently instantiated by
*must-read*, *must-see*, *must-have*. Study 5 tested only rare tokens
(≤ 10 COCA hits) against *should-V* foils. -/
def mustVerbConstruction : Construction Unit :=
  { form :=
      [ { filler := .fixed "must" }
      , { filler := .open_ .VERB }
      , { filler := .open_ .NOUN, isHead := true } ]
  , meaning := () }

/-- In the *a simple ⟨PAL⟩* subtype the PAL is itself the head noun, with
*simple* marking the situation type as routine ("Could've tried a simple
'I'm sorry.'"). Study 5's foils used *a short*. -/
def aSimplePALConstruction : Construction Unit :=
  { form :=
      [ { filler := .fixed "a" }
      , { filler := .fixed "simple" }
      , { filler := .phrasal, lex := some true
        , isHead := true } ]
  , meaning := () }

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
  , meaning := () }

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
  , meaning := () }

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

-- Table 8
theorem table8_specificity :
    veggieWrapForm.specificity = .lexicallySpecified ∧
    aSimplePALConstruction.specificity = .partiallyOpen ∧
    nnCompound.specificity = .fullyAbstract ∧
    palConstruction.specificity = .fullyAbstract := by decide

/-- The zero-level PAL, a phrase in a word-level position, with its familiar tokens
(*do-it-yourself*, *know-it-all*, *pay-as-you-go*). -/
def zeroLevelPAL : Construction Unit :=
  { form := [{ filler := .phrasal, lex := some true }]
  , meaning := () }

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

instance : PartialOrder Figure5 := figure5.partialOrder (by decide)

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

/-! ### The meaning of the PAL construction (§4)

A lemma presumes that the comprehender is familiar with the semantic frame it evokes, and a PAL is
treated as a lemma. The prenominal PAL construction therefore composes its two daughters as
modification does and adds, as not-at-issue content, that the situation type the phrase depicts is
familiar to speaker and addressee. The close paraphrase with a postnominal phrase composes the
same daughters to the same at-issue content and adds nothing. The pair worked through below is
from Table 6: *a 'blame the media' campaign* and *a campaign to blame the media*. -/

section Meaning

open ConventionalImplicature PhraseStructure Morphology

variable {W E S : Type}

/-- The denotations of the fragment: a situation type, a property of entities, a transitive verb,
which maps the property of its object to a situation type, and the inert words. The first two
carry not-at-issue content. -/
inductive Den (W E S : Type) where
  | sit : TwoDim W S → Den W E S
  | pred : TwoDim W (E → W → Prop) → Den W E S
  | verb : ((E → W → Prop) → S) → Den W E S
  | inert : Den W E S

variable (depicts : S → E → W → Prop) (familiar : S → W → Prop)

/-- The prenominal PAL construction of Figure 5, "PAL⁰ modifies N; presumes familiarity with
'PAL'": the head noun's property restricted to what depicts the situation type `s`, with the
familiarity of `s` as not-at-issue content. -/
def palRule : CompositionRule (Den W E S)
  | [.sit s, .pred n] => some <| .pred do
      let σ ← s
      let p ← n
      .mk (fun x ↦ p x ⊓ depicts σ x) (familiar σ)
  | _ => none

/-- Postnominal modification by a phrase restricts the head noun's property in the same way and
has no not-at-issue content of its own. -/
def postnominalRule : CompositionRule (Den W E S)
  | [.pred n, .sit s] => some <| .pred do
      let p ← n
      let σ ← s
      pure fun x ↦ p x ⊓ depicts σ x
  | _ => none

/-- A transitive verb applies to the property of its object. -/
def verbPhraseRule : CompositionRule (Den W E S)
  | [.verb v, .pred n] => some (.sit (v <$> n))
  | _ => none

/-- An inert word passes its sister's denotation up, as the determiner and infinitival *to* do
here. -/
def inertRule : CompositionRule (Den W E S)
  | [.inert, d] => some d
  | _ => none

/-- The prenominal PAL construction with its meaning. -/
def palN : Construction (CompositionRule (Den W E S)) :=
  palConstruction.map fun _ ↦ palRule depicts familiar

/-- The phrasal constructions of the paraphrase and of the inside of the PAL: postnominal
modification, the transitive verb phrase, the infinitive and the determined noun. -/
def phrasal : List (Construction (CompositionRule (Den W E S))) :=
  [ { form := [{ filler := .open_ .NOUN, isHead := true }, { filler := .phrasal }]
      meaning := postnominalRule depicts }
  , { form := [{ filler := .open_ .VERB, isHead := true }, { filler := .phrasal }]
      meaning := verbPhraseRule }
  , { form := [{ filler := .fixed "to" }, { filler := .phrasal }], meaning := inertRule }
  , { form := [{ filler := .open_ .DET }, { filler := .open_ .NOUN, isHead := true }]
      meaning := inertRule } ]

variable (blame : (E → W → Prop) → S) (media campaign : E → W → Prop)

/-- The words of the Table 6 pair. -/
def lexicon (w : Word) : Option (Den W E S) :=
  match w.form with
  | "blame" => some (.verb blame)
  | "media" => some (.pred (pure media))
  | "campaign" => some (.pred (pure campaign))
  | "the" | "to" => some .inert
  | _ => none

/-- *blame the media*. -/
def blameTheMedia : Tree Unit Word :=
  .node () [.leaf (.mk' "blame" .VERB),
    .node () [.leaf (.mk' "the" .DET), .leaf (.mk' "media" .NOUN)]]

/-- *'blame the media' campaign*, the phrase in the word-level modifier slot. -/
def palNP : Tree Unit Word := .node () [blameTheMedia, .leaf (.mk' "campaign" .NOUN)]

/-- *campaign to blame the media*, the paraphrase without a PAL. -/
def paraphraseNP : Tree Unit Word :=
  .node () [.leaf (.mk' "campaign" .NOUN), .node () [.leaf (.mk' "to" .PART), blameTheMedia]]

theorem interps_blameTheMedia :
    interps (palN depicts familiar :: phrasal depicts) (lexicon blame media campaign)
      blameTheMedia = [.sit (blame <$> pure media)] := rfl

/-- The PAL noun phrase denotes the campaigns depicting the situation type, and presumes the
situation type familiar. -/
theorem interps_palNP :
    interps (palN depicts familiar :: phrasal depicts) (lexicon blame media campaign) palNP =
      [.pred (.mk (fun x ↦ campaign x ⊓ depicts (blame media) x) (familiar (blame media)))] := by
  rw [palNP, interps_node]
  simp only [interpsList, interps_blameTheMedia]
  exact congrArg (fun p ↦ [Den.pred p]) (TwoDim.ext rfl (by simp))

/-- The paraphrase has the same at-issue content and no not-at-issue content. -/
theorem interps_paraphraseNP :
    interps (palN depicts familiar :: phrasal depicts) (lexicon blame media campaign)
        paraphraseNP =
      [.pred (pure fun x ↦ campaign x ⊓ depicts (blame media) x)] := by
  rw [paraphraseNP, interps_node]
  simp only [interpsList, interps_node, interps_blameTheMedia]
  exact congrArg (fun p ↦ [Den.pred p]) (TwoDim.ext rfl (by simp))

/-- Without the PAL construction the phrase in the word slot has no reading. -/
theorem interps_palNP_phrasal :
    interps (phrasal depicts) (lexicon blame media campaign) palNP = [] := rfl

-- Having a reading, the PAL noun phrase is licensed.
example : Licenses (palN depicts familiar :: phrasal depicts) palNP :=
  .of_interps_ne_nil (den := lexicon blame media campaign) <| by
    rw [interps_palNP]; exact List.cons_ne_nil _ _

end Meaning

theorem pal_form_phrase_in_word_slot :
    ∃ s ∈ palConstruction.form, s.IsPhraseInWordSlot := by decide

/-! ### Attested tokens

PALs prototypically modify nouns but occur as head nouns, predicative adjectives, and verbs
(Table 2), and take the word-level inflection of the slot they fill (Table 3). -/

/-- An affix is the inflection of a slot, nominal for the plural and agentive *-er* and verbal
for *-ing*. -/
def Examples.Inflection.position : Inflection → PALPosition
  | .plural | .agentivePlural => .headNoun
  | .gerund => .verb

/-- An attested English PAL records its slot and any inflection it carries. -/
structure Row where
  position : PALPosition
  inflection : Option Inflection
  deriving DecidableEq

def Row.ofDatum (ex : Datum) : Option Row := do
  let position ← (Examples.position ex)
  pure ⟨position, (Examples.inflection ex)⟩

/-- The English tokens of (1a)–(1c), Table 2, and Table 3. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

-- Table 2
theorem rows_position : ∀ p : PALPosition, ∃ r ∈ rows, r.position = p := by decide

/-- A PAL takes the inflection of the slot it fills (Table 3). -/
theorem rows_inflection : ∀ r ∈ rows, ∀ i ∈ r.inflection, i.position = r.position := by decide

/-! ### Comparable constructions in other languages (section 7) -/

/-- The host frames of the German, Dutch, Afrikaans, Turkish, Hebrew, and Brazilian Portuguese
PALs of (8) and (15)–(18). -/
def hostFrames : List PALHostFrame :=
  Examples.all.filterMap fun ex ↦ (Examples.hostFrame ex)

example : rows.length + hostFrames.length = Examples.all.length := by decide

theorem hostFrames_complete : ∀ f : PALHostFrame, f ∈ hostFrames := by decide

end GoldbergShirtz2025
