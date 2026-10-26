module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Denotation
public import Linglib.Fragments.Romance.Italian.Gender
public import Linglib.Fragments.Romance.Italian.Phonology

/-!
# Italian determiners

This file records the Italian determiners after Maiden and Robustelli. An article agrees with its
noun in gender and number, and its variant forms depend on how the word that follows it begins,
which need not be the noun: *lo studioso famoso* but *il famoso studioso*. The partitive article
is the preposition *di* combined with the definite article, the demonstrative *quello* varies like
the definite article, and *ciascuno* and *nessuno* vary like the indefinite article. The
quantificational determiners are the carrier `QuantityWord`, whose members denote the readings the
literature makes available for them.

## Main definitions

* `Italian.Determiners.definite`, `Italian.Determiners.indefinite`: the articles.
* `Italian.Determiners.combine`: a preposition combined with the definite article, on which
  `Italian.Determiners.partitive` and `Italian.Determiners.quello` are built.
* `Italian.Determiners.QuantityWord`: the quantificational determiners.

## Main results

* `Italian.Determiners.combine_eq_combine_iff`: a combination keeps the forms of the definite
  article apart, so the partitive and *quello* vary exactly as the article does.
* `Italian.Determiners.QuantityWord.forall_form_eq_iff`: *ogni* and *qualche* are invariant.
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

/-- The quantificational determiners are *ogni* 'every', *ciascuno* 'each', *qualche* 'some',
*nessuno* 'no', *tutti* 'all', *alcuni* 'some', *molti* 'many' and *pochi* 'few'. -/
inductive QuantityWord where
  | ogni | ciascuno | qualche | nessuno | tutti | alcuni | molti | pochi
  deriving DecidableEq, Fintype, Repr

namespace QuantityWord

/-- The form agreeing with a noun of gender `g` before a word beginning with `o`. *Ciascuno* and
*nessuno* vary like the indefinite article (§9.11, p. 155, and §9.12, p. 157). -/
def form : QuantityWord → Gender.Value → Onset → String
  | .ogni, _, _ => "ogni"
  | .qualche, _, _ => "qualche"
  | .ciascuno, g, o => "ciasc" ++ indefinite g o
  | .nessuno, g, o => "ness" ++ indefinite g o
  | .tutti, .masculine, _ => "tutti"
  | .tutti, .feminine, _ => "tutte"
  | .alcuni, .masculine, _ => "alcuni"
  | .alcuni, .feminine, _ => "alcune"
  | .molti, .masculine, _ => "molti"
  | .molti, .feminine, _ => "molte"
  | .pochi, .masculine, _ => "pochi"
  | .pochi, .feminine, _ => "poche"

/-- *Ogni*, *ciascuno*, *qualche* and *nessuno* select the singular, and the rest the plural. -/
def numberRestriction : QuantityWord → Option Number
  | .ogni | .ciascuno | .qualche | .nessuno => some .singular
  | .tutti | .alcuni | .molti | .pochi => some .plural

/-- The word as a determiner record, under its masculine form before a consonant. -/
def toQuantifier (w : QuantityWord) : Quantifier :=
  { form := w.form .masculine .consonant, numberRestriction := w.numberRestriction }

/-- All the words. -/
def toList : List QuantityWord :=
  [.ogni, .ciascuno, .qualche, .nessuno, .tutti, .alcuni, .molti, .pochi]

theorem mem_toList (w : QuantityWord) : w ∈ toList := by
  revert w; decide

theorem forall_form_eq_iff (w : QuantityWord) :
    (∀ g g' o o', w.form g o = w.form g' o') ↔ w = .ogni ∨ w = .qualche := by
  revert w; decide

/-- The readings available for a word. *Ogni*, *ciascuno* and *tutti* read as `every`, *qualche*
and *alcuni* as `Quantifier.GQ.some`, and *pochi* as `few`; *molti* has no reading, its standard
being contextual like that of English *many*. The n-word *nessuno* reads as `no`, a negative
quantifier ([de-swart-sag-2002]), or as `Quantifier.GQ.some`, an indefinite whose negation the
clause supplies ([zeijlstra-2004]). -/
noncomputable instance : Denotes QuantityWord (Set Quantifier.GQ.Family.{u}) where
  denote
    | .ogni | .ciascuno | .tutti => {Quantifier.GQ.Family.every}
    | .qualche | .alcuni => {Quantifier.GQ.Family.some}
    | .nessuno => {Quantifier.GQ.Family.no, Quantifier.GQ.Family.some}
    | .pochi => {Quantifier.GQ.Family.few}
    | .molti => ∅

end QuantityWord

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
        exponent := .dedicatedMorpheme },
    .article
      { form := partitive (.sg, .masculine) .consonant, definiteness := .indefinite,
        exponent := .dedicatedMorpheme },
    .demonstrative { form := questo (.sg, .masculine), deixis := Person.first.participantSets },
    .demonstrative
      { form := quello (.sg, .masculine) .consonant, deixis := Person.first.participantSetsᶜ } ] ++
    QuantityWord.toList.map (.quantifier ·.toQuantifier)

theorem isSyncretic_inventory : inventory.IsSyncretic := by decide

end Italian.Determiners
