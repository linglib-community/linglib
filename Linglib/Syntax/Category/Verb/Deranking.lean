module

public import Linglib.Data.WALS.Features.F124A
public import Linglib.Data.WALS.Features.F128A
public import Linglib.Syntax.Category.Verb.Defs

/-!
# Balanced and deranked complements

A verb form is balanced when it can occur in an independent declarative clause and deranked when
it cannot, in the terms of Stassen and Cristofaro. This file defines the two notions on the
complement types of a verb's frames and reads off a verb entry the values of the two maps of the
World Atlas of Language Structures that classify languages by the form of a complement: the map
of utterance complements, by whether the complement of a verb such as 'say' is balanced, deranked
or either, and the map of 'want' complements, by whether the subject of the complement is left
implicit or expressed when it is the wanter.

## Main definitions

* `Clause.ComplementType.IsBalanced`: the complement types whose verb form occurs in an
  independent declarative clause.
* `Verb.utteranceComplement`: the value of a verb's complements on the map of utterance
  complements.
* `Verb.HasSubjectControl`: some complement of the verb has its subject left implicit and
  identified with the verb's subject.
* `Verb.wantComplementSubject`: the value of a verb's complements on the map of 'want'
  complement subjects, where the entry determines it.

## Implementation notes

A dependent mood counts as deranked, as the atlas counts it, since it does not occur in an
independent declarative clause; so the subjunctive is deranked although it is sentence-like.

An entry determines the value of a 'want' verb when it has a controlled complement and no finite
one, or a finite complement and no controlled one. A verb with both, as French *vouloir* with its
infinitive and its *que* clause, has both construction types only if the finite clause admits a
subject identical to the wanter, which an entry does not record, and `Verb.wantComplementSubject`
is `none` for it. The desiderative affixes and particles of the map are not verbs and have no
entry of this type.

## References

* [stassen-1985]
* [cristofaro-2013]
* [haspelmath-2013-want]
-/

@[expose] public section

namespace Clause.ComplementType

/-- A complement type is balanced when its verb form can occur in an independent declarative
clause, as the indicative and a paratactic clause can ([cristofaro-2013]). -/
def IsBalanced : ComplementType → Prop
  | indicative | paratactic => True
  | subjunctive | infinitive | nominalized | participle => False

instance : DecidablePred IsBalanced := fun c ↦ by cases c <;> unfold IsBalanced <;> infer_instance

/-- A balanced complement type is finite. -/
theorem IsBalanced.isFinite {c : ComplementType} (h : c.IsBalanced) : c.IsFinite := by
  cases c <;> trivial

end Clause.ComplementType

namespace Data.WALS

open F128A in
/-- The value of a language whose utterance complements are balanced if `b` and deranked if `d`. -/
def F128A.UtteranceComplementType.ofProps (b d : Prop) [Decidable b] [Decidable d] :
    Option UtteranceComplementType :=
  if b then some (if d then .balancedDeranked else .balanced)
  else if d then some .deranked else none

open F124A in
/-- The value of a language whose 'want' complement leaves its subject implicit if `i` and
expresses it if `o`. -/
def F124A.WantComplementSubject.ofProps (i o : Prop) [Decidable i] [Decidable o] :
    Option WantComplementSubject :=
  if i then some (if o then .bothConstructionTypesExist else .subjectIsLeftImplicit)
  else if o then some .subjectIsExpressedOvertly else none

end Data.WALS

open Data.WALS

/-- The value of a verb's clausal complements on the map of [cristofaro-2013], for a verb of
utterance: balanced, deranked or either, by the complement types its frames restrict them to. -/
def Verb.utteranceComplement (v : Verb) : Option F128A.UtteranceComplementType :=
  F128A.UtteranceComplementType.ofProps (∃ c ∈ v.valency.codings, c.IsBalanced)
    (∃ c ∈ v.valency.codings, ¬ c.IsBalanced)

/-- Some complement of the verb is controlled by its subject, whose own subject is then left
implicit. -/
def Verb.HasSubjectControl (v : Verb) : Prop :=
  ∃ d ∈ v.valency.diatheses, d.controllerRole = some .S ∨ d.controllerRole = some .A

instance (v : Verb) : Decidable v.HasSubjectControl :=
  inferInstanceAs (Decidable (∃ d ∈ v.valency.diatheses, _))

/-- The value of a verb's complements on the map of [haspelmath-2013-want], for a verb meaning
'want', where the entry determines it: the subject is left implicit when the verb has a
controlled complement and no finite one, and expressed, by person marking on the complement's
verb at least, when it has a finite complement and no controlled one. -/
def Verb.wantComplementSubject (v : Verb) : Option F124A.WantComplementSubject :=
  if v.HasSubjectControl ∧ (∃ c ∈ v.valency.codings, c.IsFinite) then none
  else F124A.WantComplementSubject.ofProps v.HasSubjectControl (∃ c ∈ v.valency.codings, c.IsFinite)
