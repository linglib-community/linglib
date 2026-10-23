module

public import Linglib.Data.Examples.Guerrini2026
public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Genericity.NominalMappingParameter
public import Linglib.Core.Data.Set.Functor

/-!
# Guerrini (2026): Distributive Kind Predication

Guerrini explains why generalizations with kind-denoting plurals, English bare plurals and
Italian definite plurals, are distributed unlike singular indefinite generics: they can also be
accidental, cumulative and near-universal in episodic sentences. Such a sentence is structurally
ambiguous, (28). In the Bona Fide Generic parse the kind restricts a modalized universal `Gen`, as
a singular indefinite does; in Distributive Kind Predication the predicate distributes over the
kind's members at the evaluation world, as with a definite plural, so the generalization can be
accidental. Which parses a nominal has follows from what it denotes, (10), and with the Nominal
Mapping Parameter, (145), from the language and the noun's number.

## Main definitions

* `bonaFideGeneric`, `distributiveKindPred`, `cumulativeKindPred`: the kind parses.
* `cumulativeBelowGen`: the rival with the cumulative operator below `Gen`, (74c).
* `Parse.Available`: the parses a nominal has.

## Main results

* `distributiveKindPred_of_bonaFideGeneric`, `not_bonaFideGeneric_of_exception`: the generic
  parse entails distribution at the actual world and fails at an accessible exception, (53).
* `forall_of_cumulativeBelowGen`: the rival makes every member relate to every location, the
  reason the paper rejects it for *elephants live in Africa and Asia*.
* `Parse.available_iff`: the singular indefinite, whose kind formation is undefined, (16), has
  only `Gen` and the existential of Derived Property Predication.

## Implementation notes

`Gen` is the paper's black box: a universal over the worlds an accessibility relation reaches and
over the members of the kind there, so its law-likeness is a frame condition rather than a
normality ordering. Kinds are represented by their sum at each world, a finite set of atoms, which
is what `DIST` and the cumulative operator see. Homogeneity and its removal by *all* and *always*
(section 3.3, Table 3), the subjunctive diagnostic (section 3.5), and the epistemic-adjective
argument for a separate property parse (section 5.2.2) are recorded in the rows but not
formalized, since they need a trivalent `Gen` and a mood licensing substrate.

## References

* [guerrini-2026]
* [chierchia-1998]
* [beck-sauerland-2000]
-/

@[expose] public section

namespace Guerrini2026

open ModalLogic Genericity
open SetRel

variable {Atom W : Type*} (R : SetRel W W) (k : W → Finset Atom) (P : Atom → W → Prop) {w : W}

/-! ### The two parses of a generalization, section 3.2 -/

/-- In the Bona Fide Generic parse (29) the kind restricts `Gen`, a universal over the worlds `R`
accesses and the members of the kind there, so the kind's world variable stays bound. -/
def bonaFideGeneric (w : W) : Prop := □[R] (fun v ↦ ∀ a ∈ k v, P a v) w

/-- In Distributive Kind Predication (30) the kind is interpreted at the evaluation world and the
predicate distributes over its members. -/
abbrev distributiveKindPred (w : W) : Prop := ∀ a ∈ k w, P a w

/-- The generic parse is Distributive Kind Predication at every accessible world (28). -/
theorem bonaFideGeneric_iff :
    bonaFideGeneric R k P w ↔ ∀ v, w ~[R] v → distributiveKindPred k P v :=
  Iff.rfl

theorem distributiveKindPred_of_bonaFideGeneric [R.IsRefl]
    (h : bonaFideGeneric R k P w) : distributiveKindPred k P w :=
  h w (R.refl w)

/-- In the accidental case (53), distribution over the actual members says nothing about other
worlds, so it survives an exception at an accessible world, which falsifies the generic parse. -/
theorem not_bonaFideGeneric_of_exception {v : W} (hv : w ~[R] v) {a : Atom} (ha : a ∈ k v)
    (hp : ¬ P a v) : ¬ bonaFideGeneric R k P w :=
  fun h ↦ hp (h v hv a ha)

/-- The singular indefinite generic, (19) and (31), is `Gen` over the noun's property. -/
def singularIndefiniteGeneric (N : Atom → W → Prop) (w : W) : Prop :=
  □[R] (fun v ↦ ∀ a, N a v → P a v) w

/-- The generic parse of a kind-denoting plural is the singular indefinite generic over
membership in the kind (28a), which is why the two have very similar meanings. -/
theorem bonaFideGeneric_iff_singularIndefiniteGeneric :
    bonaFideGeneric R k P w ↔ singularIndefiniteGeneric R P (fun a v ↦ a ∈ k v) w :=
  Iff.rfl

/-! ### Cumulativity, section 4 -/

variable {Loc : Type*} (S : Atom → Loc → Prop) (locs : Finset Loc)

/-- Cumulative Kind Predication (74b) relates the kind's sum at the evaluation world to the
locations by [beck-sauerland-2000]'s cumulative operator. -/
abbrev cumulativeKindPred (w : W) : Prop := Set.LiftRel S ↑(k w) ↑locs

/-- With the cumulative operator below `Gen` (74c), `Gen` ranges over the sub-pluralities of the
kind, so every nonempty sample of the kind at every accessible world relates cumulatively to the
locations. -/
def cumulativeBelowGen (w : W) : Prop :=
  □[R] (fun v ↦ ∀ X ⊆ k v, X.Nonempty → Set.LiftRel S ↑X ↑locs) w

/-- (74c) is the strong reading. Taken at a singleton sample, it makes every member of the kind
relate to every location, so it is false of elephants and Africa and Asia. -/
theorem forall_of_cumulativeBelowGen [R.IsRefl] (h : cumulativeBelowGen R k S locs w)
    {a : Atom} (ha : a ∈ k w) {l : Loc} (hl : l ∈ locs) : S a l := by
  obtain ⟨b, hb, hab⟩ := (h w (R.refl w) {a} (Finset.singleton_subset_iff.2 ha)
    (Finset.singleton_nonempty a)).2 l hl
  rwa [Finset.mem_singleton.1 hb] at hab

theorem cumulativeKindPred_of_cumulativeBelowGen [R.IsRefl] (hne : (k w).Nonempty)
    (h : cumulativeBelowGen R k S locs w) : cumulativeKindPred k S locs w :=
  h w (R.refl w) (k w) subset_rfl hne

/-! ### Derived Property Predication, section 5.3 -/

/-- Derived Property Predication (105b) is the low-scoped existential over a property. -/
def dpp (N : Atom → W → Prop) (w : W) : Prop := ∃ a, N a w ∧ P a w

/-- The near-universal reading of an episodic bare plural is Distributive Kind Predication and
the existential one Derived Property Predication over the same noun (105); the first entails the
second once the kind has members. -/
theorem dpp_of_distributiveKindPred (hne : (k w).Nonempty)
    (h : distributiveKindPred k P w) : dpp P (fun a v ↦ a ∈ k v) w :=
  let ⟨a, ha⟩ := hne
  ⟨a, ha, h a ha⟩

/-! ### Which parses a nominal has, sections 2 and 5.4 -/

/-- The nominal expressions of (145) and (31). -/
inductive Nominal
  | englishBarePlural
  | italianDefinitePlural
  | italianBarePlural
  | singularIndefinite
  deriving DecidableEq

namespace Nominal

/-- Under [chierchia-1998]'s Nominal Mapping Parameter (146), English nouns can be kinds or
properties and Italian nouns are properties. -/
def mapping : Nominal → NominalMapping
  | .italianDefinitePlural | .italianBarePlural => .predOnly
  | _ => .argAndPred

/-- A nominal is definite when it carries the definite article, Italian's kind-forming operator
(13). -/
def definite : Nominal → Bool
  | .italianDefinitePlural => true
  | _ => false

/-- The noun's number, which decides whether kind formation is defined for it (16). -/
def number : Nominal → Number
  | .singularIndefinite => .singular
  | _ => .plural

/-- The expression denotes a kind when the parameter or the article makes kind formation
available and the noun is plural, (10a) and (16). -/
def CanDenoteKind (n : Nominal) : Prop :=
  n.mapping.CanDenoteKind (n.definite = true) ∧ n.number = .plural

/-- The expression denotes a property when the parameter allows it and no article has formed a
kind (145). -/
def CanDenoteProperty (n : Nominal) : Prop :=
  n.mapping.CanDenoteProperty ∧ n.definite = false

instance : DecidablePred CanDenoteKind := fun n ↦ by unfold CanDenoteKind; infer_instance
instance : DecidablePred CanDenoteProperty := fun n ↦ by unfold CanDenoteProperty; infer_instance

end Nominal

/-- The operator that takes the subject in (28), (74b), and (105). -/
inductive Parse
  | gen
  | dist
  | cumul
  | dpp
  deriving DecidableEq

/-- `DIST` and the cumulative operator apply to a sum and so need a kind, the existential of
Derived Property Predication needs a property, and `Gen` takes either (10). -/
def Parse.Available (n : Nominal) : Parse → Prop
  | .gen => n.CanDenoteKind ∨ n.CanDenoteProperty
  | .dist | .cumul => n.CanDenoteKind
  | .dpp => n.CanDenoteProperty

instance (n : Nominal) : DecidablePred (Parse.Available n) := fun p ↦ by
  cases p <;> unfold Parse.Available <;> infer_instance

/-- By (145) and Tables 1 and 2, the English bare plural has all four parses, the Italian
definite plural the three kind parses, and the Italian bare plural and the singular indefinite,
which cannot denote a kind, only `Gen` and the existential, so no accidental or cumulative
generalization. -/
theorem Parse.available_iff (p : Parse) :
    p.Available .englishBarePlural ∧ (p.Available .italianDefinitePlural ↔ p ≠ .dpp) ∧
      (p.Available .italianBarePlural ↔ p = .gen ∨ p = .dpp) ∧
      (p.Available .singularIndefinite ↔ p = .gen ∨ p = .dpp) := by
  cases p <;> decide

end Guerrini2026
