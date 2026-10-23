module

public import Linglib.Morphology.Nanosyntax.Lexicalization

/-!
# De Clercq et al. (2025): Nanosyntax: State of the art and recent developments

De Clercq, Caha, Starke and Vanden Wyngaerd present the lexicalization algorithm through case
studies, which this file runs. In the degrees of comparison the size of the root decides how
many suffixes an adjective takes, and an entry matching a larger phrase overrides the exponents
inside it. In Czech declension a root that lexicalizes the accusative by itself shrinks in the
genitive, the derivation going back to an earlier merger. A root may also store the structure
evacuation builds, the noun beside the remnant it left. Such a root lexicalizes the bare noun
and the whole structure and nothing in between, which gives Kalenjin its marked singulars and
the Friulian verb *bati* a suffix in the second person alone. A suffix may store such a
structure too, as in the Friulian verb *finî*.

## Main results

* `english_degrees`, `armenian_degrees`, `czech_degrees`: the lexicalization table of the
  degrees of comparison.
* `czech_declension`, `genitive_levels`: the genitive is *-a* in both noun classes, with the
  same structure.
* `kalenjin_number`, `peel_plural_overrides`: the root *peel* is bare in the plural and marked
  in the singular.
* `bati_present`, `fini_present`: the first and third person are alike and the second has a
  suffix more.

## Implementation notes

The chapter's prefixes are built in a workspace of their own, which the engine does not model.
The Czech superlative *nej-* is such a prefix, so `czech_degrees` shows only that the movement
steps do not derive the superlative. For Kalenjin the chapter gives no entry for the plural
suffix *-tiin* of roots like *kipaw* 'rhino', so that class is left out.

## References

* [declercq-et-al-2025]
* [starke-2018]
-/

@[expose] public section

namespace DeClercqEtAl2025

open Morphology.Nanosyntax Morphology.Exponence RoseTree

/-! ### Degrees of comparison -/

/-- The features of the adjectival sequence are the adjective, gradability, the comparative
and the superlative. -/
inductive Deg where
  | a | q | cmpr | sprl
  deriving DecidableEq, Repr

/-- English *tall* stores the gradable adjective, *-er* the comparative alone and *-est* the
superlative over the comparative. -/
def tall : RuleSet (LexicalEntry (Option Deg) String) :=
  [⟨spine .a [.q], "tall"⟩, ⟨spine .cmpr [], "er"⟩, ⟨spine .cmpr [.sprl], "est"⟩]

/-- English *bad* beside *worse*, a root storing the comparative. -/
def bad : RuleSet (LexicalEntry (Option Deg) String) :=
  [⟨spine .a [.q], "bad"⟩, ⟨spine .a [.q, .cmpr], "worse"⟩, ⟨spine .cmpr [], "er"⟩]

/-- Armenian *partsrahasag* 'tall' stores the superlative. -/
def partsrahasag : RuleSet (LexicalEntry (Option Deg) String) :=
  [⟨spine .a [.q, .cmpr, .sprl], "partsrahasag"⟩]

/-- Czech *inteligent-* stores the bare adjective, with the adjectivizer *-n* and the
comparative *-ějš* storing one feature each. -/
def inteligent : RuleSet (LexicalEntry (Option Deg) String) :=
  [⟨spine .a [], "inteligent"⟩, ⟨spine .q [], "n"⟩, ⟨spine .cmpr [], "ějš"⟩]

/-- Czech *chytr-* 'smart' stores the gradable adjective. -/
def chytr : RuleSet (LexicalEntry (Option Deg) String) :=
  [⟨spine .a [.q], "chytr"⟩, ⟨spine .cmpr [], "ějš"⟩]

/-- The sequences of the positive, the comparative and the superlative. -/
def degrees : List (List Deg) := [[.a, .q], [.a, .q, .cmpr], [.a, .q, .cmpr, .sprl]]

theorem english_degrees :
    degrees.map (exponents tall) = [some ["tall"], some ["tall", "er"], some ["tall", "est"]] ∧
      exponents bad [.a, .q, .cmpr] = some ["worse"] := by
  decide

theorem armenian_degrees :
    degrees.map (exponents partsrahasag) =
      [some ["partsrahasag"], some ["partsrahasag"], some ["partsrahasag"]] := by
  decide

theorem czech_degrees :
    degrees.map (exponents inteligent) =
        [some ["inteligent", "n"], some ["inteligent", "n", "ějš"], none] ∧
      exponents chytr [.a, .q, .cmpr] = some ["chytr", "ějš"] := by
  decide

/-! ### Czech declension -/

/-- The features of the nominal sequence are the noun, the singular, and one each for the
nominative, the accusative and the genitive. -/
inductive Case where
  | n | sg | k1 | k2 | k3
  deriving DecidableEq, Repr

/-- The suffix *-a* stores the genitive down to the singular. -/
def suffixA : LexicalEntry (Option Case) String := ⟨spine .sg [.k1, .k2, .k3], "a"⟩

/-- *chleb-* 'bread' stores the bare noun. -/
def chleb : RuleSet (LexicalEntry (Option Case) String) := [⟨spine .n [], "chleb"⟩, suffixA]

/-- *jazyk* 'tongue' stores the accusative. -/
def jazyk : RuleSet (LexicalEntry (Option Case) String) :=
  [⟨spine .n [.sg, .k1, .k2], "jazyk"⟩, suffixA]

/-- The sequences of the nominative, the accusative and the genitive. -/
def cases : List (List Case) :=
  [[.n, .sg, .k1], [.n, .sg, .k1, .k2], [.n, .sg, .k1, .k2, .k3]]

theorem czech_declension :
    cases.map (exponents chleb) =
        [some ["chleb", "a"], some ["chleb", "a"], some ["chleb", "a"]] ∧
      cases.map (exponents jazyk) = [some ["jazyk"], some ["jazyk"], some ["jazyk", "a"]] := by
  decide

theorem genitive_levels :
    lexicalize jazyk [.n, .sg, .k1, .k2, .k3] = lexicalize chleb [.n, .sg, .k1, .k2, .k3] := by
  decide

/-! ### Inverse number marking -/

/-- The features of the number sequence are the noun, the singular and the plural. -/
inductive Num where
  | n | sg | pl
  deriving DecidableEq, Repr

/-- The Kalenjin singular suffix *-yaan* stores the singular alone and the plural suffix *-een*
the plural over it. -/
def numberSuffixes : RuleSet (LexicalEntry (Option Num) String) :=
  [⟨spine .sg [], "yaan"⟩, ⟨spine .sg [.pl], "een"⟩]

/-- *peel* 'elephant' stores the noun beside the plural phrase it has evacuated from. -/
def peel : RuleSet (LexicalEntry (Option Num) String) :=
  ⟨adjoin (spine .n []) (spine .sg [.pl]), "peel"⟩ :: numberSuffixes

/-- *pata* 'duck' stores the bare noun. -/
def pata : RuleSet (LexicalEntry (Option Num) String) := ⟨spine .n [], "pata"⟩ :: numberSuffixes

/-- The sequences of the bare root, the singular and the plural. -/
def numbers : List (List Num) := [[.n], [.n, .sg], [.n, .sg, .pl]]

theorem kalenjin_number :
    numbers.map (exponents peel) = [some ["peel"], some ["peel", "yaan"], some ["peel"]] ∧
      numbers.map (exponents pata) =
        [some ["pata"], some ["pata", "yaan"], some ["pata", "een"]] := by
  decide

theorem peel_plural_overrides :
    lexicalize peel [.n, .sg, .pl] = lexicalize pata [.n, .sg, .pl] ∧
      (lexicalize peel [.n, .sg, .pl]).map List.length = some 2 := by
  decide

/-! ### The Friulian present -/

/-- The features of the verbal sequence are tense, number, person, participant and speaker. -/
inductive Phi where
  | t | num | π | part | spkr
  deriving DecidableEq, Repr

/-- The second-person suffix *-s* stores the participant alone. -/
def suffixS : LexicalEntry (Option Phi) String := ⟨spine .part [], "s"⟩

/-- Tualis Friulian *bat-* 'hit' stores the person phrase beside the speaker phrase it has
evacuated from. -/
def bat : RuleSet (LexicalEntry (Option Phi) String) :=
  [⟨adjoin (spine .t [.num, .π]) (spine .part [.spkr]), "bat"⟩, suffixS]

/-- *fin-* 'finish' stores number over tense, and its suffix *-iʃ* the speaker over a person
phrase stranded beside the participant. -/
def fin : RuleSet (LexicalEntry (Option Phi) String) :=
  [⟨spine .t [.num], "fin"⟩, ⟨merge .spkr (adjoin (spine .π []) (spine .part [])), "iʃ"⟩, suffixS]

/-- The sequences of the third, the second and the first person. -/
def persons : List (List Phi) :=
  [[.t, .num, .π], [.t, .num, .π, .part], [.t, .num, .π, .part, .spkr]]

theorem bati_present :
    persons.map (exponents bat) = [some ["bat"], some ["bat", "s"], some ["bat"]] := by
  decide

theorem fini_present :
    persons.map (exponents fin) =
      [some ["fin", "iʃ"], some ["fin", "iʃ", "s"], some ["fin", "iʃ"]] := by
  decide

end DeClercqEtAl2025
