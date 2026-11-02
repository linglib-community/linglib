module

public import Linglib.Semantics.Quantification.Determiner
public import Linglib.Semantics.Quantification.IndeterminateQuantifier
public import Linglib.Fragments.Japanese.Coordination
public import Linglib.Fragments.Japanese.Pronouns
public import Linglib.Fragments.Japanese.Classifiers

/-!
# Japanese quantifiers

Japanese has no articles, and most of its quantifiers are built from an indeterminate pronoun of
`Japanese.Pronouns` (*dare* 'who', *dono* 'which', *nan-* 'how many') and a particle, *ka* for the
existential (*dare-ka* 'someone') and *mo* for the universal (*dare-mo* 'everyone', *dono* N *mo*
'every N'). The particles are the coordinators *ka* 'or' and *mo* 'and', and an indeterminate
quantifier applies its particle's coordination to the values its scope takes on the restrictor,
the supremum for *ka* and the infimum for *mo*, which are `Quantifier.Det.some` and `every`
(`IndeterminateQuantifier.reading`). The
remaining quantifiers are words of their own, *subete* 'all', *hotondo* 'most' and *ryōhō*
'both'. Numeral quantifiers such as *nan-nin-ka* 'several people'
float away from their noun phrase, and *dare-mo* under clausemate negation is the negative
indefinite of `Fragments/Japanese/PolarityItems.lean`. The demonstrative determiners *kono*, *sono*
and *ano* are Tsujimura's ko-so-a series before a noun.

## Main definitions

* `Japanese.Determiners.indefinites`: the indeterminate quantifiers, with the coordinators of
  `Japanese.Coordination` as their particles.
* `Japanese.Determiners.quantityWords`: the quantifiers that are words of their own.
* `Japanese.Determiners.inventory`: the determiner inventory, quantifiers and demonstratives.

## References

* [chierchia-1998]
* [kratzer-shimoyama-2002]
* [shimoyama-2006]
* [tsujimura-2014]
-/

@[expose] public section

namespace Japanese.Determiners

open Quantifier
open scoped Denotes

universe u

/-- *Dare-ka* is 'someone'. -/
def dareKa : IndeterminateQuantifier := ⟨Pronouns.dare, Coordination.ka, none⟩

/-- *Dare-mo* is 'everyone'. -/
def dareMo : IndeterminateQuantifier := ⟨Pronouns.dare, Coordination.mo, none⟩

/-- *Dono* N *mo* is 'every N'. -/
def donoMo : IndeterminateQuantifier := ⟨Pronouns.dono, Coordination.mo, none⟩

/-- *Nan-nin-ka* is 'several people', with the classifier *-nin*. -/
def nanNinKa : IndeterminateQuantifier := ⟨Pronouns.nan, Coordination.ka, some Classifiers.nin⟩

/-- `indefinites` lists the indeterminate quantifiers. -/
def indefinites : List IndeterminateQuantifier := [dareKa, dareMo, donoMo, nanNinKa]

/-- *Subete* 'all', read as `every`. -/
def subete : QuantificationalDeterminer := { form := "subete", readings := {.every} }

/-- *Hotondo* 'most', read as `most`. -/
def hotondo : QuantificationalDeterminer := { form := "hotondo", readings := {.most} }

/-- *Ryōhō* 'both', read as `both`. -/
def ryoho : QuantificationalDeterminer := { form := "ryōhō", readings := {.both} }

/-- The quantifiers that are words of their own. -/
def quantityWords : List QuantificationalDeterminer := [subete, hotondo, ryoho]

/-- この *kono* 'this (N)', near the speaker ([tsujimura-2014] (24)). -/
def kono : DemonstrativeDeterminer := { form := "kono", deixis := Person.first.participantSets }

/-- その *sono* 'that (N)', near the listener, with the so-series' further reading slightly
removed from both participants unrecorded ([tsujimura-2014] (24)). -/
def sono : DemonstrativeDeterminer := { form := "sono", deixis := Person.second.participantSets }

/-- あの *ano* 'that (N)', far from both participants ([tsujimura-2014] (24)). -/
def ano : DemonstrativeDeterminer := { form := "ano", deixis := Person.third.participantSets }

/-- The demonstrative determiners. -/
def allDemonstratives : List DemonstrativeDeterminer := [kono, sono, ano]

/-- The determiner inventory has quantifiers and demonstratives, there being no articles. -/
def inventory : Determiner.Inventory :=
  indefinites.map (.quantifier ·.toQuantifier) ++
    quantityWords.map .quantifier ++ allDemonstratives.map .demonstrative

theorem denote_dareKa : ⟦dareKa⟧ = ({Det.Family.some} : Set Det.Family.{u}) := by
  rw [← IndeterminateQuantifier.reading_of_disjunctive (q := dareKa) rfl]; rfl

theorem denote_dareMo : ⟦dareMo⟧ = ({Det.Family.every} : Set Det.Family.{u}) := by
  rw [← IndeterminateQuantifier.reading_of_conjunctive (q := dareMo) rfl]; rfl

end Japanese.Determiners
