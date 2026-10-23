module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Denotation
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
the supremum for *ka* and the infimum for *mo*, which are `Quantifier.GQ.some` and `every`
(`IndeterminateQuantifier.reading`). The
remaining quantifiers are words of their own, the carrier `QuantityWord` of *subete* 'all',
*hotondo* 'most' and *ryōhō* 'both'. Numeral quantifiers such as *nan-nin-ka* 'several people'
float away from their noun phrase, and *dare-mo* under clausemate negation is the negative
indefinite of `Fragments/Japanese/PolarityItems.lean`.

## Main definitions

* `Japanese.Determiners.indefinites`: the indeterminate quantifiers, with the coordinators of
  `Japanese.Coordination` as their particles.
* `Japanese.Determiners.QuantityWord`: the quantifiers that are words of their own.
* `Japanese.Determiners.inventory`: the determiner inventory, quantifiers only.

## References

* [chierchia-1998]
* [kratzer-shimoyama-2002]
* [shimoyama-2006]
-/

@[expose] public section

namespace Japanese.Determiners

open Quantifier
open scoped Semantics

universe u

/-- *Dare-ka* is 'someone'. -/
def dare_ka : IndeterminateQuantifier := ⟨Pronouns.dare, Coordination.ka, none⟩

/-- *Dare-mo* is 'everyone'. -/
def dare_mo : IndeterminateQuantifier := ⟨Pronouns.dare, Coordination.mo, none⟩

/-- *Dono* N *mo* is 'every N'. -/
def dono_N_mo : IndeterminateQuantifier := ⟨Pronouns.dono, Coordination.mo, none⟩

/-- *Nan-nin-ka* is 'several people', with the classifier *-nin*. -/
def nan_nin_ka : IndeterminateQuantifier := ⟨Pronouns.nan, Coordination.ka, some Classifiers.nin⟩

/-- `indefinites` lists the indeterminate quantifiers. -/
def indefinites : List IndeterminateQuantifier := [dare_ka, dare_mo, dono_N_mo, nan_nin_ka]

/-- The quantifiers that are words of their own are *subete* 'all', *hotondo* 'most' and *ryōhō*
'both'. -/
inductive QuantityWord where
  | subete | hotondo | ryoho
  deriving DecidableEq, Repr, Fintype

namespace QuantityWord

/-- The form of a word is its romanization. -/
def form : QuantityWord → String
  | .subete => "subete"
  | .hotondo => "hotondo"
  | .ryoho => "ryōhō"

/-- A word's determiner record carries its form. -/
def toQuantifier (w : QuantityWord) : Quantifier := { form := w.form }

/-- `toList` lists every word. -/
def toList : List QuantityWord := [.subete, .hotondo, .ryoho]

/-- *Subete* reads as `every`, *hotondo* as `most` and *ryōhō* as `both`. -/
noncomputable instance : Semantics.Denotes QuantityWord (Set Quantifier.GQ.Family.{u}) where
  denote
    | .subete => {Quantifier.GQ.Family.every}
    | .hotondo => {Quantifier.GQ.Family.most}
    | .ryoho => {Quantifier.GQ.Family.both}

end QuantityWord

/-- The determiner inventory has quantifiers only, there being no articles. -/
def inventory : Determiner.Inventory :=
  indefinites.map (.quantifier ·.toQuantifier) ++
    QuantityWord.toList.map (.quantifier ·.toQuantifier)

theorem denote_dare_ka : ⟦dare_ka⟧ = ({GQ.Family.some} : Set GQ.Family.{u}) := by
  rw [← IndeterminateQuantifier.reading_of_disjunctive (q := dare_ka) rfl]; rfl

theorem denote_dare_mo : ⟦dare_mo⟧ = ({GQ.Family.every} : Set GQ.Family.{u}) := by
  rw [← IndeterminateQuantifier.reading_of_conjunctive (q := dare_mo) rfl]; rfl

end Japanese.Determiners
