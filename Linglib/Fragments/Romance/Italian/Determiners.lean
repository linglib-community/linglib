module

public import Linglib.Semantics.Quantification.Determiner
public import Linglib.Fragments.Romance.Italian.Gender
public import Linglib.Fragments.Romance.Italian.Phonology

/-!
# Italian determiners

This file records the Italian determiners after Maiden and Robustelli. An article agrees with its
noun in gender and number, and its variant forms depend on how the word that follows it begins,
which need not be the noun: *lo studioso famoso* but *il famoso studioso*. The partitive article
is the preposition *di* combined with the definite article, the demonstrative *quello* varies like
the definite article, and *ciascuno* and *nessuno* vary like the indefinite article. A
quantificational determiner is a `QuantityWord`, a `QuantificationalDeterminer` record with the
readings the literature makes available for it and the forms it takes in agreement.

## Main definitions

* `Italian.Determiners.definite`, `Italian.Determiners.indefinite`: the articles.
* `Italian.Determiners.combine`: a preposition combined with the definite article, on which
  `Italian.Determiners.partitive` and `Italian.Determiners.quello` are built.
* `Italian.Determiners.QuantityWord`, `Italian.Determiners.quantityWords`: the quantificational
  determiners.

## Main results

* `Italian.Determiners.combine_eq_combine_iff`: a combination keeps the forms of the definite
  article apart, so the partitive and *quello* vary exactly as the article does.
* `Italian.Determiners.QuantityWord.forall_agree_eq_iff`: *ogni* and *qualche* are invariant.
* `Italian.Determiners.isSyncretic_inventory`: the definite article marks both strengths.

## Implementation notes

The tables give the forms Maiden and Robustelli give as standard. They also report *il* beside
*lo* before *gn*, *ps*, [j] and *x*, *lo pneumatico* beside the *il pneumatico* of `Onset.of`,
*la* and *una* before a vowel, increasingly common in print, and *gli* as the plural article of
*dei* 'gods'; the elided *quest'* is optional.

## References

* [maiden-robustelli-2007]
* [schwarz-2009]
* [de-swart-sag-2002]
* [zeijlstra-2004]
-/

@[expose] public section

universe u

namespace Italian.Determiners

open Italian.Phonology (Onset)

/-! ### Articles -/

/-- The rows of the determiner tables, the singular and the plural. -/
inductive Row where
  | sg
  | pl
  deriving DecidableEq, Fintype, Repr

/-- The number of a row. -/
def Row.number : Row → Number
  | .sg => .singular
  | .pl => .plural

/-- The definite article (§4.1, p. 61). -/
def definite : Row × Gender.Value → Onset → String
  | (.sg, _), .vowel => "l'"
  | (.sg, .masculine), .consonant => "il"
  | (.sg, .masculine), _ => "lo"
  | (.sg, .feminine), _ => "la"
  | (.pl, .masculine), .consonant => "i"
  | (.pl, .masculine), _ => "gli"
  | (.pl, .feminine), _ => "le"

/-- The indefinite article, which has no plural (§4.1, p. 61). -/
def indefinite : Gender.Value → Onset → String
  | .masculine, .vowel | .masculine, .consonant => "un"
  | .masculine, _ => "uno"
  | .feminine, .vowel => "un'"
  | .feminine, _ => "una"

/-- `combine p x o` is the stem `p` combined with the definite article of the cell `x` before `o`,
as a preposition combines with it in Table 4.A (p. 63): *il* becomes *l*, *i* and *gli* stay, and
the other forms double their *l*, as in *del*, *dello* and *dell'*. -/
def combine (p : String) (x : Row × Gender.Value) (o : Onset) : String :=
  p ++ match x, o with
    | (.sg, .masculine), .consonant => "l"
    | (.pl, .masculine), o => definite (.pl, .masculine) o
    | x, o => "l" ++ definite x o

/-- The partitive article, the preposition *di* combined with the definite article (§4.20,
p. 76). -/
def partitive : Row × Gender.Value → Onset → String := combine "de"

theorem combine_eq_combine_iff (p : String) {x y : Row × Gender.Value} {o o' : Onset} :
    combine p x o = combine p y o' ↔ definite x o = definite y o' := by
  simp only [combine, String.append_right_inj]; revert x y o o'; decide

example : partitive (.pl, .masculine) .inherentlyLong = "degli" := rfl
example : combine "ne" (.sg, .feminine) .vowel = "nell'" := rfl

open Italian.Phonology in
example : [[g, l, i], [«ʎ», i], [«dʒ», «ɛ»], [j, «ɔ»]].map (definite (.sg, .masculine) ∘ Onset.of) =
    ["il", "lo", "il", "lo"] := by
  decide

/-! ### Demonstratives -/

/-- The demonstrative *questo* 'this' (§5.1, p. 81). -/
def questo : Row × Gender.Value → String
  | (.sg, .masculine) => "questo"
  | (.sg, .feminine) => "questa"
  | (.pl, .masculine) => "questi"
  | (.pl, .feminine) => "queste"

/-- The demonstrative *quello* 'that', which varies like the definite article (§5.1, p. 81). -/
def quello : Row × Gender.Value → Onset → String := combine "que"

/-! ### Quantificational determiners -/

/-- An Italian quantificational determiner, with the form it takes agreeing with a noun of
each gender before each beginning of a word; its record form is the masculine one before a
consonant. -/
structure QuantityWord extends QuantificationalDeterminer where
  /-- The form agreeing with a noun of gender `g` before a word beginning with `o`. -/
  agree : Gender.Value → Onset → String
  deriving DecidableEq

namespace QuantityWord

open scoped Denotes

attribute [coe] QuantityWord.toQuantificationalDeterminer

instance : CoeOut QuantityWord QuantificationalDeterminer := ⟨toQuantificationalDeterminer⟩

/-- A word denotes the readings of its record. -/
noncomputable instance : Denotes QuantityWord (Set Quantifier.Det.Family.{u}) where
  denote w := ⟦(w : QuantificationalDeterminer)⟧

end QuantityWord

/-- *Ogni* 'every', read as `every`, invariant, with a singular noun. -/
def ogni : QuantityWord :=
  { form := "ogni", readings := {.every}, numberRestriction := some .singular,
    agree := fun _ _ ↦ "ogni" }

/-- *Ciascuno* 'each', read as `every`, with a singular noun, varying like the indefinite article
(§9.11, p. 155). -/
def ciascuno : QuantityWord :=
  { form := "ciascun", readings := {.every}, numberRestriction := some .singular,
    agree := fun g o ↦ "ciasc" ++ indefinite g o }

/-- *Qualche* 'some', read as `Quantifier.Det.some`, invariant, with a singular noun. -/
def qualche : QuantityWord :=
  { form := "qualche", readings := {.some}, numberRestriction := some .singular,
    agree := fun _ _ ↦ "qualche" }

/-- *Nessuno* 'no', with a singular noun, varying like the indefinite article (§9.12, p. 157).
The n-word reads as `no`, a negative quantifier ([de-swart-sag-2002]), or as
`Quantifier.Det.some`, an indefinite whose negation the clause supplies ([zeijlstra-2004]). -/
def nessuno : QuantityWord :=
  { form := "nessun", readings := {.no, .some}, numberRestriction := some .singular,
    agree := fun g o ↦ "ness" ++ indefinite g o }

/-- *Tutti* 'all', read as `every`, with a plural noun. -/
def tutti : QuantityWord :=
  { form := "tutti", readings := {.every}, numberRestriction := some .plural,
    agree := fun g _ ↦ match g with | .masculine => "tutti" | .feminine => "tutte" }

/-- *Alcuni* 'some', read as `Quantifier.Det.some`, with a plural noun. -/
def alcuni : QuantityWord :=
  { form := "alcuni", readings := {.some}, numberRestriction := some .plural,
    agree := fun g _ ↦ match g with | .masculine => "alcuni" | .feminine => "alcune" }

/-- *Molti* 'many', with a plural noun and no reading, its standard being contextual like that of
English *many*. -/
def molti : QuantityWord :=
  { form := "molti", numberRestriction := some .plural,
    agree := fun g _ ↦ match g with | .masculine => "molti" | .feminine => "molte" }

/-- *Pochi* 'few', read as `few`, with a plural noun. -/
def pochi : QuantityWord :=
  { form := "pochi", readings := {.few}, numberRestriction := some .plural,
    agree := fun g _ ↦ match g with | .masculine => "pochi" | .feminine => "poche" }

/-- The quantificational determiners. -/
def quantityWords : List QuantityWord :=
  [ogni, ciascuno, qualche, nessuno, tutti, alcuni, molti, pochi]

/-- Among the quantificational determiners, *ogni* and *qualche* are invariant. -/
theorem QuantityWord.forall_agree_eq_iff :
    ∀ w ∈ quantityWords, (∀ g g' o o', w.agree g o = w.agree g' o') ↔ w = ogni ∨ w = qualche := by
  decide

/-! ### The inventory -/

/-- The inventory lists the definite article, syncretic over the use types of [schwarz-2009]
(§4.3, p. 64); the indefinite and the partitive article; *questo*, which is first-person
oriented, and *quello*, which is not (§5.3, p. 83); and the quantificational determiners. -/
def inventory : Determiner.Inventory :=
  [ .article
      { form := definite (.sg, .masculine) .consonant, definiteness := .definite,
        exponent := .dedicatedMorpheme,
        uses := {.immediateSituation, .largerSituation, .anaphoric} },
    .article
      { form := indefinite .masculine .consonant, definiteness := .indefinite,
        exponent := .dedicatedMorpheme, numberRestriction := some .singular },
    .article
      { form := partitive (.sg, .masculine) .consonant, definiteness := .indefinite,
        exponent := .dedicatedMorpheme },
    .demonstrative { form := questo (.sg, .masculine), deixis := Person.first.participantSets },
    .demonstrative
      { form := quello (.sg, .masculine) .consonant, deixis := Person.first.participantSetsᶜ } ] ++
    quantityWords.map (.quantifier ·.toQuantificationalDeterminer)

theorem isSyncretic_inventory : inventory.IsSyncretic := by decide

end Italian.Determiners
