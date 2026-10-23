module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Denotation

/-!
# Italian determiners

This file records the Italian determiner lexicon. The quantificational determiners are the
carrier `QuantityWord`, whose masculine and feminine forms are `QuantityWord.form` and
`QuantityWord.feminine`, the invariant *ogni* and *qualche* having one form, and whose members
project to a `Quantifier` record and denote the readings the literature makes available for
them, so `⟦QuantityWord.tutti⟧` is `{every}` and *molti*, like English *many*, denotes
`∅`. The definite article *il*, *lo*, *la* and plural *i*, *gli*, *le* is one syncretic definite
over Schwarz's use types, the indefinite is *un*, *uno*, *una*, and the partitive *del*,
*dello*, *della* and plural *dei*, *degli*, *delle* is the indefinite of mass nouns and plurals.

## References

* [schwarz-2009]
* [moroney-2021]
* [chierchia-1998]
* [de-swart-sag-2002]
* [zeijlstra-2004]
-/

@[expose] public section

namespace Italian.Determiners

/-! ## Articles

The definite article *il*, *lo*, *la* and plural *i*, *gli*, *le*, one syncretic definite
covering the [schwarz-2009] use types; the indefinite *un*, *uno*, *una*; and the partitive
*del*, *dello*, *della* and plural *dei*, *degli*, *delle*, the indefinite of mass nouns and
plurals. -/

/-- The definite article with the given form. -/
def definite (form : String) : Article :=
  { form, definiteness := .definite, exponent := .dedicatedMorpheme
    uses := {.immediateSituation, .largerSituation, .anaphoric} }

/-- The indefinite article with the given form. -/
def indefinite (form : String) : Article :=
  { form, definiteness := .indefinite, exponent := .dedicatedMorpheme }

def il : Article := definite "il"
def lo : Article := definite "lo"
def la : Article := definite "la"
def i : Article := definite "i"
def gli : Article := definite "gli"
def le : Article := definite "le"
def un : Article := indefinite "un"
def uno : Article := indefinite "uno"
def una : Article := indefinite "una"
def del : Article := indefinite "del"
def dello : Article := indefinite "dello"
def della : Article := indefinite "della"
def dei : Article := indefinite "dei"
def degli : Article := indefinite "degli"
def delle : Article := indefinite "delle"

/-- All Italian article entries. -/
def allArticles : List Article :=
  [il, lo, la, i, gli, le, un, uno, una, del, dello, della, dei, degli, delle]

/-! ## Quantificational determiners -/

/-- The quantificational determiners are *ogni* 'every', *qualche* 'some', *nessuno* 'no', *tutti*
'all', *alcuni* 'some', *molti* 'many' and *pochi* 'few'. -/
inductive QuantityWord where
  | ogni | qualche | nessuno | tutti | alcuni | molti | pochi
  deriving DecidableEq, Repr, Fintype

namespace QuantityWord

/-- The masculine form, which is the citation form. -/
def form : QuantityWord → String
  | .ogni => "ogni"
  | .qualche => "qualche"
  | .nessuno => "nessuno"
  | .tutti => "tutti"
  | .alcuni => "alcuni"
  | .molti => "molti"
  | .pochi => "pochi"

/-- The feminine form, which for the invariant *ogni* and *qualche* is the citation form. -/
def feminine : QuantityWord → String
  | .ogni => "ogni"
  | .qualche => "qualche"
  | .nessuno => "nessuna"
  | .tutti => "tutte"
  | .alcuni => "alcune"
  | .molti => "molte"
  | .pochi => "poche"

/-- *Ogni*, *qualche* and *nessuno* select the singular, and the rest the plural. -/
def numberRestriction : QuantityWord → Option Number
  | .ogni | .qualche | .nessuno => some .singular
  | .tutti | .alcuni | .molti | .pochi => some .plural

/-- The word as a determiner record. -/
def toQuantifier (w : QuantityWord) : Quantifier :=
  { form := w.form, numberRestriction := w.numberRestriction }

/-- All the words. -/
def toList : List QuantityWord :=
  [.ogni, .qualche, .nessuno, .tutti, .alcuni, .molti, .pochi]

theorem feminine_eq_form_iff (w : QuantityWord) :
    w.feminine = w.form ↔ w = .ogni ∨ w = .qualche := by
  cases w <;> decide

universe u

/-- The readings available for a word. *Ogni* and *tutti* read as `every`, *qualche* and
*alcuni* as `Quantifier.GQ.some`, and *pochi* as `few`; *molti* has no reading, its standard being
contextual like that of English *many*. The n-word *nessuno* reads as `no`, a negative
quantifier ([de-swart-sag-2002]), or as `Quantifier.GQ.some`, an indefinite whose negation the
clause supplies ([zeijlstra-2004]). -/
noncomputable instance : Semantics.Denotes QuantityWord (Set Quantifier.GQ.Family.{u}) where
  denote
    | .ogni | .tutti => {Quantifier.GQ.Family.every}
    | .qualche | .alcuni => {Quantifier.GQ.Family.some}
    | .nessuno => {Quantifier.GQ.Family.no, Quantifier.GQ.Family.some}
    | .pochi => {Quantifier.GQ.Family.few}
    | .molti => ∅

end QuantityWord

/-- The Italian determiner inventory. -/
def inventory : Determiner.Inventory :=
  allArticles.map .article ++ QuantityWord.toList.map (.quantifier ·.toQuantifier)

theorem isSyncretic_inventory : inventory.IsSyncretic := by decide

end Italian.Determiners
