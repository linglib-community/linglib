module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic

/-!
# Minimal pronouns

A minimal pronoun is a bare D head with unvalued φ-features, `[D, uφ]`, valued by its
antecedent. Kratzer takes reflexives, controlled PRO and bound-variable pronouns to be one such
object, and Safir concludes that all anaphoric diversity is morphological: a language's
vocabulary items realize the valued pronoun according to the context it is bound in, and where
no item is conditioned on that context the elsewhere item applies, yielding the shape of the
referential pronoun. English has a null item for controlled subjects and a reflexive item for
local binding; a language without the null item has overt PRO.

## Main definitions

* `MinimalPronoun.Context`: the binding contexts an item can be conditioned on
* `MinimalPronoun.Form`: the shapes a minimal pronoun takes, null, pronominal or reflexive
* `MinimalPronoun.Vocabulary`: a language's items for minimal pronouns and its elsewhere form
* `Vocabulary.realize`, `Vocabulary.controlForm`: the form in a context, by the Subset Principle
* `Vocabulary.syncretic`: the contexts whose form is the referential pronoun's

## Main results

* `Vocabulary.some_realize`: the elsewhere form is the Subset Principle's elsewhere item
* `Vocabulary.realize_eq_elsewhere`: a context no item applies to gets the elsewhere form
* `Vocabulary.exists_null_item_of_controlForm_eq_null`: silent PRO needs a null item

## Implementation notes

The free, referential pronoun is not a context: it is what no context conditions, the elsewhere
form. The elsewhere form is a field of the vocabulary rather than an item, so that every
vocabulary realizes every context; `some_realize` identifies it with the empty-site item of
Distributed Morphology. Safir states the variation as shape conditions at Spell-Out; the
vocabulary-item formulation is Landau's and Ostrove's. The theory of control that consumes
minimal pronouns, Landau's two tiers, is in `Studies/Landau2015.lean`.

## References

* [kratzer-1998]
* [kratzer-2009]
* [safir-2014]
* [landau-2015]
* [halle-marantz-1993]
* [ostrove-2026]
-/

@[expose] public section

namespace Binding.MinimalPronoun

open DistributedMorphology

/-- The binding contexts a vocabulary item for minimal pronouns can be conditioned on. -/
inductive Context where
  /-- The subject of a controlled clause, English PRO. -/
  | controlledSubject
  /-- Bound within its local domain, the English reflexive. -/
  | locallyBound
  /-- Bound from outside its local domain, a bound-variable pronoun. -/
  | boundVariable
  deriving DecidableEq, Repr, Fintype

/-- The shapes a minimal pronoun takes. -/
inductive Form where
  /-- Silent, as English PRO. -/
  | null
  /-- A pronoun, with the shape of the referential pronoun. -/
  | pronoun
  /-- A reflexive anaphor, as English *himself* or San Martín Peras Mixtec *mí* with a clitic. -/
  | reflexive
  deriving DecidableEq, Repr

/-- A language's vocabulary for minimal pronouns consists of the items that realize the valued
pronoun in binding contexts and the elsewhere form, which realizes it where no item applies. -/
structure Vocabulary (E : Type*) where
  /-- The items, each conditioned on binding contexts. -/
  items : Morphology.Exponence.RuleSet (VocabularyItem Context E)
  /-- The elsewhere form, the shape of the referential pronoun. -/
  elsewhere : E

namespace Vocabulary

variable {E : Type*} (v : Vocabulary E) {c : Context}

/-- The form of the minimal pronoun in a context is the exponent of the most specific item that
applies there, by the Subset Principle, and the elsewhere form where none does. -/
def realize (c : Context) : E :=
  (subsetPrinciple v.items (.ofBundle {c})).getD v.elsewhere

/-- The form of a controlled subject, silent PRO or an overt pronoun. -/
def controlForm : E := v.realize .controlledSubject

/-- The contexts in which the minimal pronoun is syncretic with the referential pronoun are those
whose form is the elsewhere form. -/
def syncretic [DecidableEq E] : Finset Context := {c | v.realize c = v.elsewhere}

variable {v}

@[simp]
theorem mem_syncretic [DecidableEq E] : c ∈ v.syncretic ↔ v.realize c = v.elsewhere := by
  simp [syncretic]

/-- The elsewhere form is the elsewhere item of the Subset Principle: realizing a context is
selecting among the items followed by the item of empty site. -/
theorem some_realize (c : Context) :
    some (v.realize c) = subsetPrinciple (v.items ++ [∅ ⟷ v.elsewhere]) (.ofBundle {c}) := by
  have happ : Morphology.Exponence.RuleSet.applicable (v.items ++ [∅ ⟷ v.elsewhere])
      (.ofBundle {c} : Neighborhood (Finset Context)) =
      v.items.applicable (.ofBundle {c}) ++ [∅ ⟷ v.elsewhere] := by
    simp [Morphology.Exponence.RuleSet.applicable, List.filter_append,
      VocabularyItem.applies_iff]
  simp only [realize, subsetPrinciple, Morphology.Exponence.RuleSet.realize,
    Morphology.Exponence.RuleSet.selectBy, happ, List.argmax_concat]
  cases (v.items.applicable (.ofBundle {c})).argmax VocabularyItem.specificity with
  | none => rfl
  | some i => simp

/-- A context that no item applies to gets the elsewhere form. -/
theorem realize_eq_elsewhere (h : ∀ i ∈ v.items, ¬ Morphology.Exponence.Applies i (.ofBundle {c})) :
    v.realize c = v.elsewhere := by
  have : subsetPrinciple v.items (.ofBundle {c}) = none :=
    Morphology.Exponence.RuleSet.realize_eq_none_iff.2 <| List.filter_eq_nil_iff.2 fun i hi ↦ by
      simpa using h i hi
  simp [realize, this]

theorem exists_item_of_realize_ne (h : v.realize c ≠ v.elsewhere) :
    ∃ i ∈ v.items, Morphology.Exponence.Applies i (.ofBundle {c}) ∧ i.exponent = v.realize c := by
  cases hs : subsetPrinciple v.items (.ofBundle {c}) with
  | none => exact absurd (by simp [realize, hs]) h
  | some e =>
    obtain ⟨i, hi, he, hsub⟩ := subsetPrinciple_winner_mem hs
    exact ⟨i, hi, hsub, by simp [realize, hs, he]⟩

/-- Silent PRO needs a null item: where the elsewhere form is overt, a controlled subject is
null only through an item for that context whose exponent is null. -/
theorem exists_null_item_of_controlForm_eq_null {v : Vocabulary Form}
    (he : v.elsewhere ≠ .null) (h : v.controlForm = .null) :
    ∃ i ∈ v.items, Morphology.Exponence.Applies i (.ofBundle {.controlledSubject}) ∧
      i.exponent = .null := by
  obtain ⟨i, hi, hs, hx⟩ := exists_item_of_realize_ne (h ▸ he.symm : v.controlForm ≠ _)
  exact ⟨i, hi, hs, hx.trans h⟩

end Vocabulary

end Binding.MinimalPronoun
