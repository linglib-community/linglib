module

public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Data.Examples.Bruening2021
public import Linglib.Semantics.Composition.Tree
public import Linglib.Syntax.Minimalist.Category.Basic

/-!
# Bruening (2021): implicit arguments in English double object constructions

An implicit second object of an English double object construction, like an implicit direct
object or PP of the prepositional frame, is definite or indefinite as the verb dictates and
licenses sluicing; an implicit first object is always definite and never does. Bruening
concludes that the verb selects the second object and Appl the first. An argument of the verb is
left implicit by a head ∃ or ι adjoined to it, an argument of Appl only by a passive head
ApplPass, which binds it as a definite.

An implicit argument here is a diathesis of an English verb leaving a complement of its double
object or prepositional frame unexpressed, so the four patterns of the paper's §2.4 are theorems
over the whole lexicon.

## Main definitions

* `Argument.leaveImplicit`: the voice leaving an internal argument of a ditransitive implicit.
* `observed`: the interpretations the lexicon gives an implicit argument.
* `Binder`, `interps`, `Sluices`: the heads that leave an argument implicit, the
  interpretations they give an argument of each head, and whether it licenses sluicing.

## Main results

* `observed_firstObject`, `observed_of_ne_firstObject`: an implicit first object is definite,
  any other implicit argument definite or indefinite.
* `interps_eq_observed_iff`: these interpretations single out Appl as the head of the first
  object and the verb as that of the others.
* `sluiced_rows`: the sluicing judgments of (10) and (11) follow.
* `objectDrop_secondObject`, `dropsInBothFrames`: a verb with an implicit transitive object has
  no implicit second object, and no verb drops its direct object in both frames, except *write*.

## Implementation notes

The fragment places an implicit argument where the construction it is understood in would
express it, so an alternating verb's implicit goal is a first object or a PP as its entry says.
Semantic types are those of `Montague.Ty`, in which events share the type `e` with individuals.

## TODO

Appendix A's varieties of definite first objects and Appendix B's verbs with two implicit
arguments are not formalized.

## References

* [bruening-2021]
* [larson-1988]
* [marantz-1993]
* [pesetsky-1995]
* [pylkkanen-2008]
-/

@[expose] public section

namespace Bruening2021

open English.Verbs Minimalist Montague PhraseStructure.Tree

/-! ### Implicit arguments -/

/-- The internal arguments of a ditransitive, the first and second objects of the double object
construction and the direct object and PP of the prepositional frame. -/
inductive Argument where
  | firstObject
  | secondObject
  | directObject
  | pp
  deriving DecidableEq, Fintype, Repr

namespace Argument

/-- The voice leaving the argument unexpressed in its construction, interpreted as `a`. -/
def leaveImplicit : Argument → ImplicitInterp → Voice
  | firstObject, a => .leaveImplicit .np_np 0 (some a)
  | secondObject, a => .leaveImplicit .np_np 1 (some a)
  | directObject, a => .leaveImplicit .np_pp 0 (some a)
  | pp, a => .leaveImplicit .np_pp 1 (some a)

/-- The argument a feature of the examples names. -/
def ofString? : String → Option Argument
  | "firstObject" => some firstObject
  | "secondObject" => some secondObject
  | "directObject" => some directObject
  | "pp" => some pp
  | _ => none

/-- In Bruening's analysis the first object is the argument of Appl, merged in its specifier
above the verb phrase, and every other argument is the verb's. -/
def host : Argument → Cat
  | firstObject => .Appl
  | _ => .V

end Argument

/-- The interpretations an implicit argument receives across the English verb lexicon. -/
def observed (x : Argument) : Finset ImplicitInterp :=
  Finset.univ.filter fun a ↦ ∃ v ∈ verbs, v.Alternates (x.leaveImplicit a)

theorem observed_firstObject : observed .firstObject = {.def} := by decide +kernel

theorem observed_of_ne_firstObject {x : Argument} (hx : x ≠ .firstObject) :
    observed x = {.indef, .def} := by
  cases x <;> first | exact absurd rfl hx | decide +kernel

/-! ### ∃, ι, Pass and ApplPass -/

/-- The heads that leave an argument implicit, ∃ and ι adjoined to the verb and the passive
heads Pass and ApplPass projecting over Voice and Appl. -/
inductive Binder where
  | existential
  | iota
  | pass
  | applPass
  deriving DecidableEq, Fintype, Repr

namespace Binder

/-- The head whose argument the binder closes off. -/
def head : Binder → Cat
  | existential | iota => .V
  | pass => .Voice
  | applPass => .Appl

/-- ∃ and Pass bind their argument as an indefinite, ι and ApplPass as a definite. -/
def interp : Binder → ImplicitInterp
  | existential | pass => .indef
  | iota | applPass => .def

/-- Pass and ApplPass head phrases of their own; ∃ and ι form a complex head with the verb. -/
def Projects : Binder → Prop
  | pass | applPass => True
  | existential | iota => False

instance : DecidablePred Projects := fun b ↦ by cases b <;> unfold Projects <;> infer_instance

end Binder

/-- The interpretations available to an implicit argument of the head `h`. -/
def interps (h : Cat) : Finset ImplicitInterp :=
  (Finset.univ.filter (·.head = h)).image Binder.interp

/-- An implicit argument of `h` licenses sluicing when a binder that does not project can close
it off. Ellipsis needs a correlate in the elided clause for every maximal projection of the
antecedent, which a sluice has for a head adjoined to the verb but not for PassP or ApplPassP. -/
def Sluices (h : Cat) : Prop := ∃ b : Binder, b.head = h ∧ ¬ b.Projects

instance (h : Cat) : Decidable (Sluices h) := inferInstanceAs (Decidable (∃ _, _))

/-- The interpretations an implicit argument shows are those available to an argument of its
head, and of no other head. The verb chooses ∃ or ι for its own arguments, so their
interpretations vary from verb to verb, while ApplPass alone closes off the first object. An
analysis on which the verb selects the first object, as Pesetsky's and Larson's do, predicts
indefinite implicit first objects; a small-clause analysis, on which the verb selects neither,
predicts no lexical variation in the second. -/
theorem interps_eq_observed_iff (x : Argument) (h : Cat) :
    interps h = observed x ↔ h = x.host := by
  rcases eq_or_ne x .firstObject with rfl | hx
  · rw [observed_firstObject]
    cases h <;> decide
  · rw [observed_of_ne_firstObject hx]
    cases x <;> cases h <;> first | exact absurd rfl hx | decide

/-- In (10) and (11) every verb leaves the sluiced argument implicit, and the sluice is
acceptable exactly when that argument's head licenses sluicing. -/
theorem sluiced_rows : ∀ v ∈ verbs, .np_np ∈ v.valency.frames → ∀ row ∈ Examples.all,
    row.feature? "verb" = some v.form → ∀ x,
      (row.feature? "sluiced").bind Argument.ofString? = some x →
        (∃ a, v.Alternates (x.leaveImplicit a)) ∧
          (row.judgment = .acceptable ↔ Sluices x.host) := by
  decide +kernel

/-! ### Implicit direct objects -/

/-- A verb leaving its transitive object implicit does not leave its second double object implicit,
except *write* (fn. 7). -/
theorem objectDrop_secondObject :
    (verbs.filter fun v ↦ (∃ a, v.Alternates (Argument.secondObject.leaveImplicit a)) ∧
      ∃ a, v.Alternates (.leaveImplicit .np 0 (some a))).map (·.form) = ["write"] := by
  decide +kernel

-- (7), (8)
theorem melt_build : ∀ v ∈ [melt, build],
    (∃ a, v.Alternates (.leaveImplicit .np 0 (some a))) ∧ .np_np ∈ v.valency.frames := by
  decide +kernel

theorem combine?_appl :
    Ty.combine? (Ty.eet ⇒ .e ⇒ .e ⇒ Ty.et) Ty.eet = some (.e ⇒ .e ⇒ Ty.et) ∧
      Ty.combine? (Ty.eet ⇒ .e ⇒ .e ⇒ Ty.et) Ty.et = none := by
  decide

/-- No verb but *write* leaves its direct object implicit both in the double object and in the
prepositional frame. -/
theorem dropsInBothFrames :
    (verbs.filter fun v ↦ (∃ a, v.Alternates (Argument.secondObject.leaveImplicit a)) ∧
      ∃ a, v.Alternates (Argument.directObject.leaveImplicit a)).map (·.form) = ["write"] := by
  decide +kernel

-- (63), (65)
theorem implicit_rows : ∀ v ∈ verbs, .np_np ∈ v.valency.frames → ∀ row ∈ Examples.all,
    row.feature? "verb" = some v.form → ∀ x,
      (row.feature? "implicit").bind Argument.ofString? = some x →
        (row.judgment = .acceptable ↔ ∃ a, v.Alternates (x.leaveImplicit a)) := by
  decide +kernel

end Bruening2021
