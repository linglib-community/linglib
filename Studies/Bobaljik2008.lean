module

public import Mathlib.Order.UpperLower.Basic
public import Linglib.Semantics.ArgumentStructure.Valency
public import Linglib.Syntax.Case.Dependent
public import Linglib.Syntax.Minimalist.Probe.Basic
public import Linglib.Languages.HindiUrdu.Case

/-!
# Bobaljik (2008): Where's Phi? Agreement as a Postsyntactic Operation

[bobaljik-2008] proposes that the controller of agreement on the finite verb is the highest
accessible noun phrase in the domain of the verb, and that a noun phrase is accessible by its
morphological case. The categories of morphological case are those of [marantz-1991]'s
realization hierarchy, ordered for agreement the other way round: unmarked case is more
accessible than dependent case, and dependent case more accessible than lexical case. A language
whose verb agrees fixes a category `t`, and a noun phrase is accessible when the category of its
case is at least `t`. Since morphological case is assigned after the syntax, agreement, which
feeds on it, is postsyntactic as well.

For noun phrases `xs`, listed from the highest down, with their cases `s`, we define
`controller t xs s` as the search of the probe relativized to accessibility. A noun phrase is
the controller exactly when it is accessible and no noun phrase above it is, so an inaccessible
noun phrase is invisible to the search and does not intervene; and a language that makes more
categories accessible keeps a controller wherever it had one. The sets of categories a language
can make accessible are the nonempty sets closed upward in the order.

With case assigned by the dependent case rules, an accusative case system gives subject
agreement whatever is accessible, and an ergative one gives absolutive agreement when only
unmarked case is accessible and subject agreement when dependent case is accessible too, so
ergative agreement over accusative case is not derived. Below a subject with lexical case the
object controls agreement unless lexical case is itself accessible. In Hindi-Urdu, where only
unmarked case is accessible, the object controls agreement under an ergative or a dative
subject, the subject where it is unmarked, and no argument where the subject is ergative and the
object bears *ko*. In Nepali, where dependent case is accessible too, the subject controls
agreement whether it is nominative or ergative, and the object under a dative subject.

## Implementation notes

The domain of the verb is the list of noun phrases given; the conditions on domains that
long-distance agreement shows are not formalized. Case is assigned by the rules of
`Syntax/Case/Dependent.lean`, and case valued by agreement with a functional head, which those
rules also provide for, counts as unmarked.

The rules of a Hindi-Urdu clause are read off the markers of `HindiUrdu.coreMarker`: the high
dependent case where the subject takes *ne*, and the low one where the object takes *ko*. With
*ko* a lexical case the rules would leave the subject of a perfective clause without a competitor
and so without its ergative. In a language where only unmarked case is accessible the choice
between the two categories for *ko* does not otherwise affect the controller.

## References

* [bobaljik-2008]
* [marantz-1991]
-/

@[expose] public section

namespace Bobaljik2008

open Case DependentCase Minimalist

/-- (13): The categories of morphological case, in their order of accessibility for agreement,
with lexical case the least accessible and unmarked case the most. -/
inductive CaseCategory where
  | lexical
  | dependent
  | unmarked
  deriving DecidableEq, Repr, Fintype

namespace CaseCategory

instance : LinearOrder CaseCategory := LinearOrder.lift' (·.ctorIdx) (by decide)

/-- The category of a case, by what valued it. -/
def ofMechanism : Mechanism → CaseCategory
  | .lexical => .lexical
  | .dependent => .dependent
  | .unmarked | .functional => .unmarked

end CaseCategory

/-- The sets of categories that a language can make accessible, the categories at or above one
of them, are the nonempty sets closed upward. -/
theorem exists_eq_Ici_iff {s : Set CaseCategory} :
    (∃ t, s = Set.Ici t) ↔ IsUpperSet s ∧ s.Nonempty := by
  refine ⟨?_, fun ⟨hs, hne⟩ ↦ ?_⟩
  · rintro ⟨t, rfl⟩
    exact ⟨IsUpperSet.Ici t, t, Set.self_mem_Ici⟩
  · obtain ⟨t, ht, hmin⟩ := wellFounded_lt.has_min s hne
    exact ⟨t, Set.Subset.antisymm (fun x hx ↦ not_lt.1 (hmin x hx)) (hs.Ici_subset ht)⟩

-- (17): no language agrees with ergatives and not with absolutives
example : ¬ ∃ t, ({.dependent} : Set CaseCategory) = Set.Ici t := fun h ↦ by
  have := (exists_eq_Ici_iff.1 h).1 (show CaseCategory.dependent ≤ .unmarked by decide)
    (Set.mem_singleton _)
  simp at this

/-! ### The controller of agreement -/

variable {α : Type*} (t : CaseCategory) (s : α → FeatureSlot (Flat (Case × Mechanism)))

/-- A noun phrase is accessible, in a language whose least accessible category is `t`, when the
category of its case is at least `t`. -/
def Accessible (x : α) : Prop := ∃ v ∈ (s x).value?, t ≤ .ofMechanism v.2

instance : DecidablePred (Accessible t s) := fun _ ↦ inferInstanceAs (Decidable (∃ v ∈ _, _))

variable {t s} in
theorem Accessible.mono {t' : CaseCategory} (h : t' ≤ t) {x : α} (hx : Accessible t s x) :
    Accessible t' s x :=
  let ⟨v, hv, hle⟩ := hx
  ⟨v, hv, h.trans hle⟩

/-- (3): The controller of agreement is the highest accessible noun phrase of the domain `xs`,
which lists its noun phrases from the highest down. -/
def controller (xs : List α) : Option α := (Probe.relativized (Accessible t s)).search xs

variable {t s} {xs : List α} {x : α}

/-- A noun phrase controls agreement exactly when it is accessible and no noun phrase above it
is: inaccessible noun phrases are invisible and do not intervene. -/
theorem controller_eq_some_iff :
    controller t s xs = some x ↔
      Accessible t s x ∧ ∃ l₁ l₂, xs = l₁ ++ x :: l₂ ∧ ∀ y ∈ l₁, ¬ Accessible t s y :=
  Probe.search_eq_some_iff_closest

-- agreement is default exactly when no noun phrase is accessible
theorem controller_eq_none_iff : controller t s xs = none ↔ ∀ x ∈ xs, ¬ Accessible t s x :=
  Probe.search_eq_none_iff

-- a language that makes more categories accessible keeps a controller where it had one
theorem controller_isSome_mono {t' : CaseCategory} (h : t' ≤ t)
    (hx : (controller t s xs).isSome) : (controller t' s xs).isSome :=
  Probe.search_isSome_mono (fun _ _ ha ↦ Accessible.mono h ha) hx

/-- The controller of agreement in a clause on the arguments `xs`, listed from the highest down
and assigned case by the rules `r`, `lex` giving their lexical cases. -/
def clauseController (r : Rules) (t : CaseCategory) (lex : ArgumentRole → Option Case)
    (xs : List ArgumentRole) : Option ArgumentRole :=
  controller t (r.assign lex xs) xs

/-- Whether the argument bearing role `r` controls agreement in some clause of the given
alignment, in a language whose least accessible category is `t`, the arguments of a clause
listed from the external one down. -/
def controls (a : Alignment.AlignmentType) (t : CaseCategory) (r : ArgumentRole) : Bool :=
  decide (∃ v : ArgumentStructure.Valency,
    clauseController (.ofAlignment a) t (fun _ ↦ none)
      ([.external, .internal].filterMap v.role) = some r)

/-! ### The predicted agreement alignments -/

-- (27): an accusative case system gives subject agreement at every setting
theorem isAccusative_controls_accusative (t : CaseCategory) :
    Alignment.IsAccusative (controls .accusative t) := by
  cases t <;> decide

-- (27): an ergative case system gives absolutive agreement when only unmarked case is accessible
theorem isErgative_controls_ergative_unmarked :
    Alignment.IsErgative (controls .ergative .unmarked) := by
  decide

-- (27): an ergative case system gives subject agreement when dependent case is accessible
theorem isAccusative_controls_ergative_dependent :
    Alignment.IsAccusative (controls .ergative .dependent) := by
  decide

/-- No setting derives ergative agreement from accusative case. -/
theorem not_isErgative_controls_accusative (t : CaseCategory) :
    ¬ Alignment.IsErgative (controls .accusative t) :=
  (isAccusative_controls_accusative t).not_isErgative

/-! ### Case against grammatical function -/

/-- Below a subject with lexical case, as the dative subjects of Icelandic, the object controls
agreement unless lexical case is itself accessible. -/
theorem clauseController_lexical_subject (a : Alignment.AlignmentType) (c : Case)
    (t : CaseCategory) (ht : t ≠ .lexical) :
    clauseController (.ofAlignment a) t (fun r ↦ if r = .A then some c else none) [.A, .P] =
      some .P := by
  cases a <;> cases t <;> first | exact absurd rfl ht | rfl

/-! ### Hindi-Urdu -/

/-- The dependent case rules of a Hindi-Urdu clause, read off its markers: the ergative on the
higher noun phrase where the subject takes *ne*, and the accusative on the lower one where the
object takes *ko*. -/
def hindiRules (a : Aspect.Perfectivity) (markedObject : Bool) : Rules where
  high := (HindiUrdu.coreMarker a markedObject .A).map fun _ ↦ .erg
  low := (HindiUrdu.coreMarker a markedObject .P).map fun _ ↦ .acc
  unmarked := some .nom

/-- The controller of agreement in a Hindi-Urdu clause with a subject and an object, where only
unmarked case is accessible. -/
def hindiController (a : Aspect.Perfectivity) (markedObject : Bool)
    (lex : ArgumentRole → Option Case := fun _ ↦ none) : Option ArgumentRole :=
  clauseController (hindiRules a markedObject) .unmarked lex [.A, .P]

/-- (21): In the perfective the unmarked object controls agreement under the ergative subject,
and no argument does where the object bears *ko*; in the imperfective the unmarked subject does,
whether or not the object is unmarked too. -/
theorem hindiController_eq (a : Aspect.Perfectivity) (markedObject : Bool) :
    hindiController a markedObject =
      match a, markedObject with
      | .perfective, false => some .P
      | .perfective, true => none
      | .imperfective, _ => some .A := by
  cases a <;> cases markedObject <;> rfl

-- (21e): under a dative subject the unmarked object controls agreement
theorem hindiController_dative_subject (a : Aspect.Perfectivity) :
    hindiController a false (fun r ↦ if r = .A then some .dat else none) = some .P := by
  cases a <;> rfl

/-! ### Nepali -/

-- (24): where dependent case is accessible the subject controls agreement, nominative or ergative
theorem nepali_subject :
    clauseController (.ofAlignment .neutral) .dependent (fun _ ↦ none) [.A, .P] = some .A ∧
      clauseController (.ofAlignment .ergative) .dependent (fun _ ↦ none) [.A, .P] = some .A := by
  decide

-- (26): under a dative subject the nominative object controls agreement
theorem nepali_dative_subject :
    clauseController (.ofAlignment .neutral) .dependent (fun r ↦ if r = .A then some .dat else none)
      [.A, .P] = some .P :=
  clauseController_lexical_subject .neutral .dat .dependent (by decide)

end Bobaljik2008
