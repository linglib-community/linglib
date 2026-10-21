module

public import Linglib.Syntax.Category.Adjective.Basic
public import Linglib.Fragments.Dutch.Nouns

/-!
# Dutch adjectives

This file defines the Dutch adjective as a lexical entry and the rule for its attributive
ending. An entry is the root `Adjective` with the form it takes with the attributive ending
*-e*, where it takes one. By Broekhuis and Corver's grammar an attributive adjective takes the
ending unless its noun phrase is indefinite and its head noun a neuter singular or a neuter
non-count noun: *de oude stoel* 'the old chair', *een oude stoel*, *het oude paard* 'the old
horse', but *een oud paard*. An adjective ending in a schwa or in the long vowel written *a*,
*o* or *i*, *oranje* 'orange', *prima* 'excellent', and a substance adjective in *-en*, *gouden*
'golden', never takes the ending. The suffix *-heid* derives a common-gender noun from an
adjective, *roodheid* 'redness'. The entries are the colour, taste and evaluative adjectives
whose three forms McNally and de Swart compare, with the grammar's examples of the ending and
its exceptions.

## Main definitions

* `Dutch.Adjectives.Adjective`: the entry.
* `Dutch.Adjectives.attributive`: the attributive form of an adjective before a noun.
* `Dutch.Adjectives.heid`: the derived noun in *-heid*.

## Main results

* `Dutch.Adjectives.attributive_indefinite_neuter_singular`: the one cell of the grammar's
  table with no ending.
* `Dutch.Adjectives.oud_paard`: *een oud paard*, *het oude paard*, *oude paarden*.

## Implementation notes

* The forms of the grammar's summary table, one per definiteness, gender and number, with
  number neutralized for a non-count noun, are the values of `attributive`. The exceptions are
  entries with no inflected form rather than derived from the spelling, since the rule is
  phonological. A substance adjective is also attributive-only and non-gradable, and the entry
  records the latter with no scalar dimension.
* Which adjectives lack a noun in *-heid* is not recorded, since the paper says only that not
  all adjectives take the suffix, so `heid` is total.

## References

* [H. Broekhuis and N. Corver, *Syntax of Dutch, Volume VI: Adjectives and Adjective Phrases*
  (2026)][broekhuis-corver-2026d]
* [L. McNally and H. de Swart, *Inflection and Derivation: How Adjectives and Nouns Refer to
  Abstract Objects* (2011)][mcnally-deswart-2011]
-/

@[expose] public section

namespace Dutch.Adjectives

/-- A Dutch adjective is the root entry with its form with the attributive ending *-e*, where
it takes one. -/
structure Adjective extends _root_.Adjective where
  /-- The form with the attributive ending *-e*, `none` for an adjective that never takes it. -/
  inflected : Option String := none
  deriving DecidableEq, Repr

/-- An adjective declines when it has a form with the attributive ending. -/
def Adjective.Declines (a : Adjective) : Prop := a.inflected.isSome

instance (a : Adjective) : Decidable a.Declines := inferInstanceAs (Decidable (_ = _))

/-- An attributive adjective takes the ending unless its noun phrase is indefinite and its head
noun neuter and not plural. -/
def TakesEnding (d : Definiteness) (g : Gender.Value) (n : Number) : Prop :=
  d = .definite ∨ g = .common ∨ n = .plural

instance (d : Definiteness) (g : Gender.Value) (n : Number) : Decidable (TakesEnding d g n) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- `attributive a d g n` is the form of `a` before a noun of gender `g` and number `n` in a noun
phrase of definiteness `d`: the inflected form where the adjective declines and the phrase
takes the ending, and the bare form otherwise. -/
def attributive (a : Adjective) (d : Definiteness) (g : Gender.Value) (n : Number) : String :=
  match a.inflected with
  | some f => if TakesEnding d g n then f else a.form
  | none => a.form

/-- An adjective that does not decline keeps its form. -/
theorem attributive_of_not_declines {a : Adjective} (h : ¬ a.Declines) (d g n) :
    attributive a d g n = a.form := by
  rcases ha : a.inflected with _ | f
  · simp [attributive, ha]
  · exact absurd (by simp [Adjective.Declines, ha]) h

/-- In a definite noun phrase the ending is always present. -/
@[simp] theorem attributive_definite (a : Adjective) (g n) :
    attributive a .definite g n = a.inflected.getD a.form := by
  rcases h : a.inflected with _ | f <;> simp [attributive, h, TakesEnding]

/-- Before a noun of common gender the ending is always present. -/
@[simp] theorem attributive_common (a : Adjective) (d n) :
    attributive a d .common n = a.inflected.getD a.form := by
  rcases h : a.inflected with _ | f <;> simp [attributive, h, TakesEnding]

/-- Before a plural noun the ending is always present. -/
@[simp] theorem attributive_plural (a : Adjective) (d g) :
    attributive a d g .plural = a.inflected.getD a.form := by
  rcases h : a.inflected with _ | f <;> simp [attributive, h, TakesEnding]

/-- Before a neuter singular or non-count noun in an indefinite noun phrase the ending is
absent. -/
@[simp] theorem attributive_indefinite_neuter_singular (a : Adjective) :
    attributive a .indefinite .neuter .singular = a.form := by
  rcases h : a.inflected with _ | f <;> simp [attributive, h, TakesEnding]

/-- `heid a` is the noun in *-heid* derived from `a`, which is of common gender. -/
def heid (a : Adjective) : String := a.form ++ "heid"

/-! ### The grammar's examples -/

/-- *oud* 'old' is the adjective of the grammar's tables of the ending. -/
def oud : Adjective := { form := "oud", dimension := some .age, inflected := some "oude" }

/-- *lekker* 'tasty' is the adjective of the grammar's table for non-count nouns. -/
def lekker : Adjective :=
  { form := "lekker", dimension := some .taste, inflected := some "lekkere" }

/-- *oranje* 'orange' ends in a schwa and does not decline, *een oranje jas* 'an orange
coat'. -/
def oranje : Adjective := { form := "oranje", dimension := some .color }

/-- *prima* 'excellent' ends in the long vowel written *a* and does not decline. -/
def prima : Adjective := { form := "prima", dimension := some .quality }

/-- *albino* 'albino' ends in the long vowel written *o* and does not decline. -/
def albino : Adjective := { form := "albino" }

/-- *kaki* 'khaki' ends in the long vowel written *i* and does not decline. -/
def kaki : Adjective := { form := "kaki", dimension := some .color }

/-- *houten* 'wooden' is a substance adjective in *-en*, attributive-only and non-gradable, *de
houten kom* 'the wooden bowl' but not *de kom is houten*. -/
def houten : Adjective := { form := "houten" }

/-- *gouden* 'golden' is a substance adjective like *houten*. -/
def gouden : Adjective := { form := "gouden" }

/-- The neuter *paard* takes the bare form in an indefinite singular phrase only, *een oud paard*,
*het oude paard*, *oude paarden*. -/
theorem oud_paard :
    attributive oud .indefinite Nouns.paard.gender .singular = "oud" ∧
      attributive oud .definite Nouns.paard.gender .singular = "oude" ∧
      attributive oud .indefinite Nouns.paard.gender .plural = "oude" := by
  decide

/-- The common-gender *stoel* always takes the ending, *een oude stoel*, *de oude stoel*. -/
theorem oud_stoel :
    attributive oud .indefinite Nouns.stoel.gender .singular = "oude" ∧
      attributive oud .definite Nouns.stoel.gender .singular = "oude" := by
  decide

/-- A non-count noun patterns with the singular, *lekker bier*, *het lekkere bier*, *lekkere
rijst*. -/
theorem lekker_bier_rijst :
    attributive lekker .indefinite Nouns.bier.gender .singular = "lekker" ∧
      attributive lekker .definite Nouns.bier.gender .singular = "lekkere" ∧
      attributive lekker .indefinite Nouns.rijst.gender .singular = "lekkere" := by
  decide

/-- The exceptions keep their form before a common-gender noun, *een oranje jas*, *de gouden
ring*. -/
theorem oranje_jas_gouden_ring :
    attributive oranje .indefinite Nouns.jas.gender .singular = "oranje" ∧
      attributive gouden .definite Nouns.ring.gender .singular = "gouden" := by
  decide

/-! ### The adjectives of McNally and de Swart

The colour and taste adjectives whose uninflected nominal, *het rood* 'the red', inflected
nominal, *het rode van de aardbeien* 'the red of the strawberries', and derived nominal, *de
roodheid* 'the redness', the paper compares, and the evaluative and concrete adjectives with
which it contrasts the availability of the inflected nominal. -/

/-- *rood* 'red'. -/
def rood : Adjective := { form := "rood", dimension := some .color, inflected := some "rode" }

/-- *wit* 'white'. -/
def wit : Adjective := { form := "wit", dimension := some .color, inflected := some "witte" }

/-- *groen* 'green'. -/
def groen : Adjective :=
  { form := "groen", dimension := some .color, inflected := some "groene" }

/-- *geel* 'yellow'. -/
def geel : Adjective := { form := "geel", dimension := some .color, inflected := some "gele" }

/-- *blauw* 'blue'. -/
def blauw : Adjective :=
  { form := "blauw", dimension := some .color, inflected := some "blauwe" }

/-- *zwart* 'black'. -/
def zwart : Adjective :=
  { form := "zwart", dimension := some .color, inflected := some "zwarte" }

/-- *roze* 'pink' ends in a schwa and does not decline. -/
def roze : Adjective := { form := "roze", dimension := some .color }

/-- *mauve* 'mauve' ends in a schwa and does not decline. -/
def mauve : Adjective := { form := "mauve", dimension := some .color }

/-- *lila* 'lilac' ends in the long vowel written *a* and does not decline. -/
def lila : Adjective := { form := "lila", dimension := some .color }

/-- *bitter* 'bitter'. -/
def bitter : Adjective :=
  { form := "bitter", dimension := some .taste, inflected := some "bittere" }

/-- *zoet* 'sweet'. -/
def zoet : Adjective := { form := "zoet", dimension := some .taste, inflected := some "zoete" }

/-- *zuur* 'sour'. -/
def zuur : Adjective := { form := "zuur", dimension := some .taste, inflected := some "zure" }

/-- *zout* 'salty'. -/
def zout : Adjective := { form := "zout", dimension := some .taste, inflected := some "zoute" }

/-- *vreemd* 'strange', an evaluative adjective whose inflected nominal is frequent, *het
vreemde van dit boek* 'the strange thing about this book'. -/
def vreemd : Adjective :=
  { form := "vreemd", dimension := some .unspecified, inflected := some "vreemde" }

/-- *gezond* 'healthy', an evaluative adjective like *vreemd*. -/
def gezond : Adjective :=
  { form := "gezond", dimension := some .unspecified, inflected := some "gezonde" }

/-- *leuk* 'nice'. -/
def leuk : Adjective :=
  { form := "leuk", dimension := some .quality, inflected := some "leuke" }

/-- *bijzonder* 'special'. -/
def bijzonder : Adjective :=
  { form := "bijzonder", dimension := some .unspecified, inflected := some "bijzondere" }

/-- *dicht* 'closed', the negative pole of openness, whose inflected nominal is marginal, *het
dichte van deze doos* 'the closed thing about this box'. -/
def dicht : Adjective :=
  { form := "dicht", dimension := some .openness, polarity := .negative,
    antonymForm := some "open", inflected := some "dichte" }

/-- `inventory` lists the entries. -/
def inventory : List Adjective :=
  [oud, lekker, oranje, prima, albino, kaki, houten, gouden,
   rood, wit, groen, geel, blauw, zwart, roze, mauve, lila,
   bitter, zoet, zuur, zout, vreemd, gezond, leuk, bijzonder, dicht]

/-- The entries that do not decline are exactly those ending in a schwa, in the long vowel
written *a*, *o* or *i*, or in *-en* after a consonant. -/
theorem not_declines_iff :
    ∀ a ∈ inventory, ¬ a.Declines ↔
      a.form.toList.getLast? ∈ [some 'e', some 'a', some 'o', some 'i'] ∨
        ['e', 'n'] <:+ a.form.toList ∧
          ¬ ∃ v ∈ ['a', 'e', 'i', 'o', 'u'], [v, 'e', 'n'] <:+ a.form.toList := by
  decide

/-- *roodheid* 'redness'. -/
theorem heid_rood : heid rood = "roodheid" := rfl

end Dutch.Adjectives
