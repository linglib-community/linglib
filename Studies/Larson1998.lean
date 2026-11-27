module

public import Linglib.Data.Examples.Larson1998
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.ArgumentStructure.EventIdentification
public import Linglib.Semantics.Quantifier.Basic
public import Mathlib.Basic.Rel

/-!
# Larson (1998): Events and Modification in Nominals

On Larson's analysis a noun is a relation of individuals to events and an adjective a set of
individuals and events. An adjective modifies a noun at the individual or at the event, and
[both readings are intersective](##Larson1998.isIntersective_ofEvent).

With the event closed, a noun holds of the domain of its relation, and a noun modified at the
event holds of [the preimage of the adjective](##Larson1998.dom_ofEvent). Nouns with the same
domain [can differ in that preimage](##Larson1998.exists_dom_eq_dom_ofEvent_ne), so this reading
is [not a function of the noun's extension](##Larson1998.exists_not_factorsThrough_dom_ofEvent).
An adjective that holds of no event, or of no individual, has one reading, and [a coordination
has the readings its conjuncts share](##Larson1998.isFalseOn_inter_of_notMem_inter). Under a
universal quantifier over events, [a modified nominal does not entail the bare
one](##Larson1998.exists_modifiedNominal_every_not_predicateNominal).

## Implementation notes

* The comparison class of an adjective is left out.
* A reading excluded on pragmatic grounds is an empty relation.
* Where the event quantifier is suppressed, the event is closed existentially. The generic
  quantifier is a determiner denotation on events, with *some* and *every* the instances
  considered.

## TODO

* The contrast of *the invisible visible stars* with *the visible invisible stars* is not derived.
* The adverbial readings in predicate position and those of the adjectives of infrequency are not
  formalized.

## References

* [larson-1998]
* [davidson-1967]
* [siegel-1976]
* [chierchia-1995a]
-/

@[expose] public section

namespace Larson1998

open Modifier ArgumentStructure Quantifier
open scoped SetRel

variable {X Ev : Type*}

/-! ### The two rules of modification -/

/-- The first rule of (12c): the adjective, a set of things, is predicated of the individual of
the noun. -/
def ofIndividual (A : Set (X ⊕ Ev)) : Modifier (SetRel X Ev) :=
  intersective (Prod.fst ⁻¹' (Sum.inl ⁻¹' A))

/-- The second rule of (12c): the adjective is predicated of the event of the noun. -/
def ofEvent (A : Set (X ⊕ Ev)) : Modifier (SetRel X Ev) :=
  intersective (Prod.snd ⁻¹' (Sum.inr ⁻¹' A))

variable {A B : Set (X ⊕ Ev)} {R S : SetRel X Ev} {x : X} {e : Ev}

@[simp] theorem mem_ofIndividual : x ~[ofIndividual A R] e ↔ .inl x ∈ A ∧ x ~[R] e := Iff.rfl

@[simp] theorem mem_ofEvent : x ~[ofEvent A R] e ↔ .inr e ∈ A ∧ x ~[R] e := Iff.rfl

-- The second rule is Event Identification of the noun with the adjective.
theorem mem_ofEvent_iff_eventIdentification :
    x ~[ofEvent A R] e ↔ eventIdentification (· ~[R] ·) (.inr · ∈ A) x e :=
  and_comm

theorem isIntersective_ofIndividual (A : Set (X ⊕ Ev)) : IsIntersective (ofIndividual A) :=
  intersective_isIntersective _

/-- There are no nonintersective readings (§3.1): predicated of the event as of the individual,
the adjective is intersected with the noun, on dancings in place of dancers. -/
theorem isIntersective_ofEvent (A : Set (X ⊕ Ev)) : IsIntersective (ofEvent A) :=
  intersective_isIntersective _

-- A beautiful dancer is a dancer on either reading.
theorem ofEvent_subset (A : Set (X ⊕ Ev)) (R : SetRel X Ev) : ofEvent A R ⊆ R :=
  (isIntersective_ofEvent A).isSubsective R

/-! ### The event closed

The individuals a noun is true of are the domain of its relation. -/

-- The projection formula: read of the individual, the adjective is conjoined with the closed
-- noun, the predicate conjunction of the predicative adjectives (§2.0).
theorem dom_ofIndividual (A : Set (X ⊕ Ev)) (R : SetRel X Ev) :
    (ofIndividual A R).dom = Sum.inl ⁻¹' A ∩ R.dom :=
  Set.ext fun _ ↦ ⟨fun ⟨e, ha, hr⟩ ↦ ⟨ha, e, hr⟩, fun ⟨ha, e, hr⟩ ↦ ⟨e, ha, hr⟩⟩

-- Read of the event, the modified noun is true of the individuals the noun relates to an event
-- in the adjective, the preimage of the adjective under the noun.
theorem dom_ofEvent (A : Set (X ⊕ Ev)) (R : SetRel X Ev) :
    (ofEvent A R).dom = R.preimage (Sum.inr ⁻¹' A) :=
  Set.ext fun _ ↦ Iff.rfl

-- §2.1: read of the individual, the adjective may be substituted between coextensive nouns.
theorem factorsThrough_dom_ofIndividual (A : Set (X ⊕ Ev)) :
    Function.FactorsThrough (fun R : SetRel X Ev ↦ (ofIndividual A R).dom) SetRel.dom :=
  fun R S h ↦ by simp only [dom_ofIndividual, h]

/-- (11), for nouns as §3 carries it over from verbs and adverbs: that the dancers are the singers
does not make the beautiful dancers the beautiful singers when the adjective is predicated of
the event, on first-order grounds and with no appeal to other worlds. -/
theorem exists_dom_eq_dom_ofEvent_ne :
    ∃ (X Ev : Type) (dancing singing : SetRel X Ev) (beautiful : Set (X ⊕ Ev)),
      dancing.dom = singing.dom ∧
        (ofEvent beautiful dancing).dom ≠ (ofEvent beautiful singing).dom := by
  refine ⟨Unit, Bool, {p | p.2 = true}, {p | p.2 = false}, {.inr true},
    Set.ext fun _ ↦ ⟨fun _ ↦ ⟨false, rfl⟩, fun _ ↦ ⟨true, rfl⟩⟩, fun h ↦ ?_⟩
  obtain ⟨e, hb, he⟩ : () ∈ (ofEvent {.inr true} {p : Unit × Bool | p.2 = false}).dom :=
    h ▸ ⟨true, rfl, rfl⟩
  simp_all

/-- The reading on which the adjective is predicated of the event is not a function of the
extension of the noun, so an analysis on which the adjective is a function of the noun must take
the noun's intension, as the one in (3) does. -/
theorem exists_not_factorsThrough_dom_ofEvent :
    ∃ (X Ev : Type) (A : Set (X ⊕ Ev)),
      ¬ Function.FactorsThrough (fun R : SetRel X Ev ↦ (ofEvent A R).dom) SetRel.dom := by
  obtain ⟨X, Ev, R, S, A, h, hne⟩ := exists_dom_eq_dom_ofEvent_ne
  exact ⟨X, Ev, A, fun hf ↦ hne (hf h)⟩

-- (13): the two readings come apart, the dancing beautiful and the dancer not.
theorem exists_dom_ofEvent_not_subset_dom_ofIndividual :
    ∃ (X Ev : Type) (A : Set (X ⊕ Ev)) (R : SetRel X Ev),
      ¬ (ofEvent A R).dom ⊆ (ofIndividual A R).dom :=
  ⟨Unit, Unit, {.inr ()}, Set.univ, fun h ↦ by
    have hx : () ∈ (ofEvent ({.inr ()} : Set (Unit ⊕ Unit)) (Set.univ : SetRel Unit Unit)).dom :=
      ⟨(), rfl, trivial⟩
    obtain ⟨_, ha, _⟩ := h hx
    exact Sum.inl_ne_inr ha⟩

/-! ### Sortal restrictions and coordination -/

/-- The two parameters of a noun that an adjective may be predicated of. -/
inductive Parameter
  | individual
  | event
  deriving DecidableEq, Fintype

/-- The reading on which the adjective is predicated of a parameter. -/
def reading : Parameter → Set (X ⊕ Ev) → Modifier (SetRel X Ev)
  | .individual => ofIndividual
  | .event => ofEvent

/-- An adjective is false on a parameter when it holds nothing of that sort, as *aged* holds no
event and *former* no individual. -/
def IsFalseOn (A : Set (X ⊕ Ev)) : Parameter → Prop
  | .individual => Sum.inl ⁻¹' A = ∅
  | .event => Sum.inr ⁻¹' A = ∅

-- (15), (16): an adjective false on a parameter has no reading there.
theorem reading_eq_empty {p : Parameter} (h : IsFalseOn A p) (R : SetRel X Ev) :
    reading p A R = ∅ := by
  cases p <;> exact Set.eq_empty_iff_forall_notMem.2 fun ⟨x, e⟩ h' ↦
    Set.eq_empty_iff_forall_notMem.1 h _ h'.1

/-- (17), (18): the coordination of two adjectives is their intersection, so it is false on every
parameter outside the ones its conjuncts share, and a strictly intersective adjective beside a
strictly nonintersective one leaves no reading. -/
theorem isFalseOn_inter_of_notMem_inter {s t : Finset Parameter} (hA : ∀ p ∉ s, IsFalseOn A p)
    (hB : ∀ p ∉ t, IsFalseOn B p) {p : Parameter} (hp : p ∉ s ∩ t) : IsFalseOn (A ∩ B) p := by
  rw [Finset.mem_inter, not_and_or] at hp
  rcases hp with h | h
  · cases p <;> exact Set.subset_empty_iff.1 fun _ h' ↦ (hA _ h).subset h'.1
  · cases p <;> exact Set.subset_empty_iff.1 fun _ h' ↦ (hB _ h).subset h'.2

/-! ### The examples -/

/-- The name of a parameter in the rows. -/
def Parameter.name : Parameter → String
  | .individual => "individual"
  | .event => "event"

/-- The parameters each adjective of the examples may be predicated of: the ambiguous ones of
(1) and (2), *aged* and *blonde* of individuals only, *former* and *fast* of events only. -/
def lexicon : List (String × Finset Parameter) :=
  [("beautiful", Finset.univ), ("intelligent", Finset.univ), ("skillful", Finset.univ),
    ("good", Finset.univ), ("diligent", Finset.univ), ("old", Finset.univ),
    ("aged", {.individual}), ("blonde", {.individual}), ("former", {.event}),
    ("fast", {.event})]

/-- The parameters the adjectives of a row share. -/
def shared? (e : Datum) : Option (Finset Parameter) :=
  (e.parseAll? "adjective" lexicon).map fun l ↦ l.foldr (· ∩ ·) Finset.univ

-- (1), (2), (15)–(17): a row is accepted exactly when its adjectives share a parameter.
theorem rows_predicted :
    Datum.Checks shared? (fun s ↦ .ofProp s.Nonempty) Examples.all 11 := by
  decide

-- The readings the paper reports, twenty over the rows, are those of the shared parameters.
theorem readings_predicted :
    (∀ e ∈ Examples.all, ∀ s ∈ shared? e, ∀ p : Parameter,
        ∀ j ∈ e.readings.lookup p.name, j.band = .ofProp (p ∈ s)) ∧
      (Examples.all.map fun e ↦ (e.readings.filter fun r ↦
        r.1 ∈ [Parameter.individual.name, Parameter.event.name]).length).sum = 20 := by
  decide

/-! ### The event quantifier -/

section Quantifier

variable (Γ : Det Ev) (Con : SetRel X Ev)

/-- (19c): a predicate nominal under the event quantifier, the contextually relevant events with
the individual being events of the noun. -/
def predicateNominal (R : SetRel X Ev) (x : X) : Prop :=
  Γ (Con.image {x}) (R.image {x})

/-- (20c): a modified predicate nominal, the noun joining the restriction and the adjective the
scope. -/
def modifiedNominal (A : Set (X ⊕ Ev)) (R : SetRel X Ev) (x : X) : Prop :=
  Γ ((Con ∩ R).image {x}) (Sum.inr ⁻¹' A)

variable {Con}

-- With an existential quantifier (20c) is the preimage of the adjective under the noun on the
-- relevant events.
theorem modifiedNominal_some :
    modifiedNominal Det.some Con A R x ↔ x ∈ (Con ∩ R).preimage (Sum.inr ⁻¹' A) :=
  ⟨fun ⟨e, ⟨_, rfl, hr⟩, ha⟩ ↦ ⟨e, ha, hr⟩, fun ⟨e, ha, hr⟩ ↦ ⟨e, ⟨x, rfl, hr⟩, ha⟩⟩

-- With a universal quantifier it is the core.
theorem modifiedNominal_every :
    modifiedNominal Det.every Con A R x ↔ x ∈ (Con ∩ R).core (Sum.inr ⁻¹' A) :=
  ⟨fun h _ hr ↦ h ⟨x, rfl, hr⟩, fun h _ ⟨_, hx, hr⟩ ↦ h (hx ▸ hr)⟩

-- With an existential quantifier a beautiful dancer is a dancer.
theorem predicateNominal_of_modifiedNominal_some (h : modifiedNominal Det.some Con A R x) :
    predicateNominal Det.some Con R x :=
  h.imp fun _ h ↦ ⟨SetRel.image_subset_image_left Set.inter_subset_left h.1,
    SetRel.image_subset_image_left Set.inter_subset_right h.1⟩

-- The universal reading gives the existential one of an individual with a relevant event of the
-- noun.
theorem modifiedNominal_some_of_every (h : modifiedNominal Det.every Con A R x)
    (hx : x ∈ (Con ∩ R).dom) : modifiedNominal Det.some Con A R x :=
  hx.imp fun _ hr ↦ ⟨⟨x, rfl, hr⟩, h ⟨x, rfl, hr⟩⟩

/-- With a quantifier that lacks existential import, (20c) does not entail (19c): of someone who
never dances, every relevant dancing is beautiful, and not every relevant event is a dancing. -/
theorem exists_modifiedNominal_every_not_predicateNominal :
    ∃ (X Ev : Type) (Con R : SetRel X Ev) (A : Set (X ⊕ Ev)) (x : X),
      modifiedNominal Det.every Con A R x ∧ ¬ predicateNominal Det.every Con R x :=
  ⟨Unit, Unit, Set.univ, ∅, Set.univ, (), fun _ _ ↦ trivial,
    fun h ↦ (h ⟨(), rfl, trivial⟩ : () ∈ SetRel.image ∅ {()}).elim fun _ h ↦ h.2⟩

end Quantifier

end Larson1998
