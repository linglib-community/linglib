module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Syntax.Feature.Person.Defs
public import Linglib.Syntax.Feature.Person.Participants

/-!
# Cantonese determiner inventory

Cantonese (Sinitic, ISO `yue`) marks definiteness with the bare classifier
phrase [Clf-N], which serves unique and anaphoric environments alike, and
marks indefiniteness with the numeral-classifier phrase [jat-Clf-N];
demonstratives form a separate paradigm. The [Clf-N]-as-definite observation
is due to Cheng and Sybesma; Jenks (§6) analyzes [Clf-N] as an ambiguous
definite parallel to English *the*.

## References

* [cheng-sybesma-1999]
* [jenks-2018], §6
-/

@[expose] public section

namespace Cantonese.Determiners

/-- The bare classifier phrase [Clf-N], the definite of unique and anaphoric environments
alike. -/
def clfN : Article :=
  { form := "Clf-N", definiteness := {.definite}, exponent := .classifierPhrase,
    uses := {.immediateSituation, .largerSituation, .anaphoric} }

/-- The numeral-classifier phrase [jat-Clf-N], the indefinite. -/
def jatClfN : Article :=
  { form := "jat-Clf-N", definiteness := {.nonSpecific, .specific},
    exponent := .numeralClassifier }

/-- *nei* 'this', the proximal demonstrative, which stands before a classifier. -/
def nei : DemonstrativeDeterminer := { form := "nei", deixis := Person.first.participantSets }

/-- *go²* 'that', the distal demonstrative, which stands before a classifier; [jenks-2018]
finds it restricted to particular anaphoric environments. -/
def go : DemonstrativeDeterminer := { form := "go2", deixis := Person.first.participantSetsᶜ }

/-- The Cantonese determiners are the syncretic [Clf-N] definite, the [jat-Clf-N] indefinite and
the demonstratives. -/
def inventory : Determiner.Inventory :=
  [.article clfN, .article jatClfN, .demonstrative nei, .demonstrative go]

theorem isSyncretic_inventory : inventory.IsSyncretic := by decide

end Cantonese.Determiners
