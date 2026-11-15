module

public import Linglib.Data.Examples.Larson1998
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.ArgumentStructure.EventIdentification
public import Linglib.Semantics.Quantification.Basic

/-!
# Events and modification in nominals

[larson-1998] carries [davidson-1967]'s event argument into the noun: *dancer* holds of an
individual and a dancing, an adjective is a predicate of things of either sort, and an adjective
beside a noun is predicated of the individual or of the event. *Olga is a beautiful dancer* is
then ambiguous without any ambiguity in *beautiful*, and
[both readings are intersective](##Larson1998.isIntersective_ofEvent) on the noun. Nouns true of
the same individuals [need not stay so](##Larson1998.exists_coextensive_not_ofEvent) once an
adjective is predicated of their events, though no worlds are in play, and
[no function on the nouns' extensions](##Larson1998.exists_forall_ne_ofEvent) gives that reading,
which is why the analysis of [siegel-1976] takes intensions. An adjective false of one sort has
one reading, and [a coordination has the readings its conjuncts
share](##Larson1998.isFalseOn_inf_of_notMem_inter). With the generic quantifier of
[chierchia-1995a] over the events, the noun restricts and the adjective is the scope, and
[the modified nominal no longer entails the bare
one](##Larson1998.exists_modifiedNominal_every_not_predicateNominal) unless the quantifier has
existential import.

## Implementation notes

The comparison class of an adjective is left out, as it is in the paper's own logical forms once
the rules are stated. A reading the paper marks as excluded on pragmatic grounds, an aged
presidency or a former Jerry, is here a reading true of nothing. Where the paper suppresses the
event quantifier the statements below close the event existentially, as [davidson-1967] does;
the generic quantifier is a determiner denotation on events, with *some* and *every* as the two
instances considered.

## TODO

The contrast between *the invisible visible stars* and *the visible invisible stars*, with the
generic quantifier close to the noun, is not derived: neither *some* nor *every* separates the
two orders. The adverbial readings that survive in predicate position (*Dancer's Delight is
fast*) and those of the adjectives of infrequency (*an occasional customer*), which the paper
leaves open, are not formalized.

## References

* [larson-1998]
* [davidson-1967]
* [siegel-1976]
* [chierchia-1995a]
-/

@[expose] public section

namespace Larson1998

open Modifier ArgumentStructure Quantifier

variable {X Ev : Type*}

/-! ### The two rules of modification -/

/-- The first rule of (12c): the adjective, a predicate of things, is predicated of the
individual of the noun. -/
def ofIndividual (A : X ⊕ Ev → Prop) : Modifier (X → Ev → Prop) :=
  intersective fun x _ ↦ A (.inl x)

/-- The second rule of (12c): the adjective is predicated of the event of the noun. -/
def ofEvent (A : X ⊕ Ev → Prop) : Modifier (X → Ev → Prop) :=
  fun N ↦ eventIdentification N fun e ↦ A (.inr e)

variable {A B : X ⊕ Ev → Prop} {N N' : X → Ev → Prop} {x : X} {e : Ev}

@[simp] theorem ofIndividual_apply : ofIndividual A N x e ↔ A (.inl x) ∧ N x e := Iff.rfl

@[simp] theorem ofEvent_apply : ofEvent A N x e ↔ N x e ∧ A (.inr e) := Iff.rfl

theorem ofEvent_eq_intersective : ofEvent A = intersective fun (_ : X) e ↦ A (.inr e) := by
  funext N x e
  exact propext and_comm

theorem isIntersective_ofIndividual (A : X ⊕ Ev → Prop) : IsIntersective (ofIndividual A) :=
  intersective_isIntersective _

/-- There are no nonintersective readings (§3.1): predicated of the event as of the individual,
the adjective is intersected with the noun, on dancings in place of dancers. -/
theorem isIntersective_ofEvent (A : X ⊕ Ev → Prop) : IsIntersective (ofEvent A) :=
  ofEvent_eq_intersective ▸ intersective_isIntersective _

-- A beautiful dancer is a dancer on either reading.
theorem ofEvent_le (A : X ⊕ Ev → Prop) (N : X → Ev → Prop) : ofEvent A N ≤ N :=
  (isIntersective_ofEvent A).isSubsective N

/-! ### Substitution -/

-- The reading of the individual is the predicate conjunction of the predicative adjectives
-- (§2.0).
theorem exists_ofIndividual : (∃ e, ofIndividual A N x e) ↔ A (.inl x) ∧ ∃ e, N x e := by
  simp

-- §2.1: read of the individual, the adjective may be substituted between coextensive nouns.
theorem exists_ofIndividual_congr (h : ∀ x, (∃ e, N x e) ↔ ∃ e, N' x e) (x : X) :
    (∃ e, ofIndividual A N x e) ↔ ∃ e, ofIndividual A N' x e := by
  rw [exists_ofIndividual, exists_ofIndividual, h]

/-- (11): that the dancers are the singers does not make the beautiful dancers the beautiful
singers when the adjective is predicated of the event, on first-order grounds and with no
appeal to other worlds. -/
theorem exists_coextensive_not_ofEvent :
    ∃ (X Ev : Type) (dancing singing : X → Ev → Prop) (beautiful : X ⊕ Ev → Prop),
      (∀ x, (∃ e, dancing x e) ↔ ∃ e, singing x e) ∧
        ¬ ∀ x, (∃ e, ofEvent beautiful dancing x e) ↔ ∃ e, ofEvent beautiful singing x e := by
  refine ⟨Unit, Bool, fun _ e ↦ e = true, fun _ e ↦ e = false, fun t ↦ t = .inr true,
    fun _ ↦ ⟨fun _ ↦ ⟨false, rfl⟩, fun _ ↦ ⟨true, rfl⟩⟩, fun h ↦ ?_⟩
  obtain ⟨e, he, hb⟩ := (h ()).1 ⟨true, rfl, rfl⟩
  simp_all

/-- No function on the extensions of nouns gives the reading on which the adjective is
predicated of the event, so an analysis on which the adjective is such a function must take
their intensions (§2.1). -/
theorem exists_forall_ne_ofEvent :
    ∃ (X Ev : Type) (A : X ⊕ Ev → Prop), ∀ F : Modifier (X → Prop),
      ∃ N : X → Ev → Prop, (fun x ↦ ∃ e, ofEvent A N x e) ≠ F fun x ↦ ∃ e, N x e := by
  obtain ⟨X, Ev, dancing, singing, A, hco, hne⟩ := exists_coextensive_not_ofEvent
  refine ⟨X, Ev, A, fun F ↦ by_contra fun hF ↦ ?_⟩
  have h : ∀ N : X → Ev → Prop, (fun x ↦ ∃ e, ofEvent A N x e) = F fun x ↦ ∃ e, N x e :=
    fun N ↦ by_contra fun hN ↦ hF ⟨N, hN⟩
  have hext : (fun x ↦ ∃ e, dancing x e) = fun x ↦ ∃ e, singing x e :=
    funext fun x ↦ propext (hco x)
  exact hne fun x ↦ iff_of_eq (congrFun ((h dancing).trans (hext ▸ (h singing).symm)) x)

-- (13): the two readings come apart, the dancing beautiful and the dancer not.
theorem exists_ofEvent_not_ofIndividual :
    ∃ (X Ev : Type) (A : X ⊕ Ev → Prop) (N : X → Ev → Prop) (x : X),
      (∃ e, ofEvent A N x e) ∧ ¬ ∃ e, ofIndividual A N x e :=
  ⟨Unit, Unit, fun t ↦ t = .inr (), fun _ _ ↦ True, (), ⟨(), trivial, rfl⟩,
    fun ⟨_, h, _⟩ ↦ nomatch h⟩

/-! ### Sortal restrictions and coordination -/

/-- The two parameters of a noun that an adjective may be predicated of. -/
inductive Parameter
  | individual
  | event
  deriving DecidableEq, Fintype

/-- The reading on which the adjective is predicated of a parameter. -/
def reading : Parameter → (X ⊕ Ev → Prop) → Modifier (X → Ev → Prop)
  | .individual => ofIndividual
  | .event => ofEvent

/-- An adjective is false on a parameter when it is true of nothing of that sort, as *aged* is of
no event and *former* of no individual. -/
def IsFalseOn (A : X ⊕ Ev → Prop) : Parameter → Prop
  | .individual => ∀ x, ¬ A (.inl x)
  | .event => ∀ e, ¬ A (.inr e)

-- (15), (16): an adjective false on a parameter has no reading there.
theorem reading_eq_bot {p : Parameter} (h : IsFalseOn A p) (N : X → Ev → Prop) :
    reading p A N = ⊥ := by
  funext x e
  cases p
  · exact eq_false fun h' ↦ h x h'.1
  · exact eq_false fun h' ↦ h e h'.2

/-- (17), (18): the coordination of two adjectives is their meet, so it is false on every
parameter outside the ones its conjuncts share, and a strictly intersective adjective beside a
strictly nonintersective one leaves no reading. -/
theorem isFalseOn_inf_of_notMem_inter {s t : Finset Parameter} (hA : ∀ p ∉ s, IsFalseOn A p)
    (hB : ∀ p ∉ t, IsFalseOn B p) {p : Parameter} (hp : p ∉ s ∩ t) : IsFalseOn (A ⊓ B) p := by
  rw [Finset.mem_inter, not_and_or] at hp
  rcases hp with h | h
  · cases p
    · exact fun x h' ↦ hA _ h x h'.1
    · exact fun e h' ↦ hA _ h e h'.1
  · cases p
    · exact fun x h' ↦ hB _ h x h'.2
    · exact fun e h' ↦ hB _ h e h'.2

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

variable (Γ : Det Ev) (Con : X → Ev → Prop)

/-- (19c): a predicate nominal under the event quantifier, the contextually relevant events with
the individual being events of the noun. -/
def predicateNominal (N : X → Ev → Prop) (x : X) : Prop :=
  Γ {e | Con x e} {e | N x e}

/-- (20c): a modified predicate nominal, the noun joining the restriction and the adjective the
scope. -/
def modifiedNominal (A : X ⊕ Ev → Prop) (N : X → Ev → Prop) (x : X) : Prop :=
  Γ {e | Con x e ∧ N x e} {e | A (.inr e)}

variable {Con}

-- With an existential quantifier (20c) is the event reading over the relevant events.
theorem modifiedNominal_some :
    modifiedNominal Det.some Con A N x ↔ ∃ e, Con x e ∧ ofEvent A N x e :=
  ⟨fun ⟨e, ⟨hc, hn⟩, ha⟩ ↦ ⟨e, hc, hn, ha⟩, fun ⟨e, hc, hn, ha⟩ ↦ ⟨e, ⟨hc, hn⟩, ha⟩⟩

-- With an existential quantifier a beautiful dancer is a dancer.
theorem predicateNominal_of_modifiedNominal_some (h : modifiedNominal Det.some Con A N x) :
    predicateNominal Det.some Con N x :=
  h.imp fun _ h ↦ ⟨h.1.1, h.1.2⟩

/-- With a quantifier that lacks existential import, (20c) does not entail (19c): of someone who
never dances, every relevant dancing is beautiful, and not every relevant event is a dancing. -/
theorem exists_modifiedNominal_every_not_predicateNominal :
    ∃ (X Ev : Type) (Con N : X → Ev → Prop) (A : X ⊕ Ev → Prop) (x : X),
      modifiedNominal Det.every Con A N x ∧ ¬ predicateNominal Det.every Con N x :=
  ⟨Unit, Unit, fun _ _ ↦ True, fun _ _ ↦ False, fun _ ↦ True, (), fun _ h ↦ h.2.elim,
    fun h ↦ @h () trivial⟩

end Quantifier

end Larson1998
