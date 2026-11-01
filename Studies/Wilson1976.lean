module

public import Linglib.Data.Examples.Wilson1976
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Wilson (1976): The o/a distinction in Hawaiian possessives

This file formalizes Wilson's account of the Hawaiian possessive particles in *o* (*koʻu* 'my')
and in *a* (*kaʻu* 'my'): the particle is determined by the possessive relationship, not by the
possessed noun.

## Main definitions

* `Relationship.hawaiian`: the particle of a relationship, rules (1)–(3) (p. 43).
* `Relationship.fijian`: the Fijian prefix of a relationship (p. 47).

## Implementation notes

The relationship of an example is the group under which the paper lists it; for the minimal
pairs on p. 41 it is read off the gloss by the criteria of pp. 43–45.

## References

* [wilson-1976]
-/

@[expose] public section

namespace Wilson1976

/-! ### Relationships and particles -/

/-- The vowel of a Hawaiian possessive particle. -/
inductive Marker where
  | o
  | a
  deriving DecidableEq, Repr

/-- A use of the possessed by the possessor that a controlled relationship can specify. -/
inductive Use where
  | location
  | food
  | drink
  deriving DecidableEq, Repr

/-- A possessive relationship, uncontrolled or controlled with an optional use (pp. 46–47). -/
inductive Relationship where
  | notControlled
  | controlled (use : Option Use)
  deriving DecidableEq, Repr

/-- The prefixes of Fijian possessives. -/
inductive FijianMarker where
  | no
  | ke
  | me
  deriving DecidableEq, Repr

namespace Relationship

/-- The Hawaiian particle of a relationship is *a* if the relationship is controlled and not
locational, and *o* otherwise. -/
def hawaiian : Relationship → Marker
  | notControlled => .o
  | controlled (some .location) => .o
  | controlled _ => .a

/-- The Fijian prefix of a relationship is *me-* for drink, *no-* if the relationship is controlled
and not food, and *ke-* otherwise. -/
def fijian : Relationship → FijianMarker
  | notControlled => .ke
  | controlled (some .food) => .ke
  | controlled (some .drink) => .me
  | controlled _ => .no

/-- The particle predicted by control alone, as in earlier relation-based accounts. -/
def controlOnly : Relationship → Marker
  | notControlled => .o
  | controlled _ => .a

end Relationship

/-- The groups under which the paper lists its examples (pp. 43–45). -/
inductive Group where
  | inanimate
  | body
  | kin
  | agency
  | instigated
  | offspring
  | ownership
  | location
  deriving DecidableEq, Repr

/-- The relationship of a group (pp. 43–45). -/
def Group.relationship : Group → Relationship
  | .inanimate | .body | .kin | .agency => .notControlled
  | .instigated | .offspring | .ownership => .controlled none
  | .location => .controlled (some .location)

/-! ### The examples -/

/-- The group under which an example is listed. -/
def group (d : Datum) : Option Group :=
  d.parse? "relationship" [("inanimate", .inanimate), ("body", .body), ("kin", .kin),
    ("agency", .agency), ("instigated", .instigated), ("offspring", .offspring),
    ("ownership", .ownership), ("location", .location)]

/-- The particle of a Hawaiian example. -/
def marker (d : Datum) : Option Marker :=
  d.parse? "marker" [("o", .o), ("a", .a)]

/-- The prefix of a Fijian example. -/
def fijianMarker (d : Datum) : Option FijianMarker :=
  d.parse? "marker" [("no", .no), ("ke", .ke), ("me", .me)]

/-- The possessed noun of an example. -/
def possessed (d : Datum) : Option String :=
  d.feature? "possessed"

/-- The Hawaiian examples. -/
def hawaiianData : List Datum :=
  Examples.all.filter (·.language = .hawaiian)

/-- The Fijian examples. -/
def fijianData : List Datum :=
  Examples.all.filter (·.language = .fijian)

/-! ### The relation-based account -/

/-- Rules (1)–(3) predict the particle of every Hawaiian example. -/
theorem hawaiian_marker_eq :
    ∀ d ∈ hawaiianData, (group d).isSome ∧ marker d = (group d).map (·.relationship.hawaiian) := by
  decide +kernel

theorem exists_minimal_pair :
    ∃ d ∈ hawaiianData, ∃ d' ∈ hawaiianData, possessed d = possessed d' ∧ marker d ≠ marker d' := by
  decide +kernel

/-- No assignment of particles to nouns fits the examples (p. 41). -/
theorem not_exists_nounClass :
    ¬ ∃ f : String → Marker, ∀ d ∈ hawaiianData, marker d = (possessed d).map f := by
  rintro ⟨f, hf⟩
  obtain ⟨d, hd, d', hd', hp, hm⟩ := exists_minimal_pair
  exact hm (by rw [hf d hd, hf d' hd', hp])

/-- An account by control alone mispredicts (p. 43). -/
theorem exists_ne_controlOnly :
    ∃ d ∈ hawaiianData, marker d ≠ (group d).map (·.relationship.controlOnly) := by
  decide +kernel

/-! ### The feature-based noun class theory -/

/-- The semantic features of the feature-based noun class theory (p. 40). -/
inductive Feature where
  | importantInOldCulture
  | inCloseContactWithBody
  | inherited
  | portable
  | animalUsedForRiding
  | subordinateToPossessor
  deriving DecidableEq, Repr

/-- The particle a feature value predicts (p. 40). -/
def Feature.predicts : Feature → Bool → Marker
  | .portable, b | .subordinateToPossessor, b => if b then .a else .o
  | _, b => if b then .o else .a

/-- The feature values of *spear* (p. 41). -/
def spear : List (Feature × Bool) :=
  [(.importantInOldCulture, true), (.inCloseContactWithBody, true), (.inherited, true),
    (.portable, true), (.subordinateToPossessor, true)]

/-- The feature-based theory predicts both particles for *spear* (p. 41). -/
theorem spear_predicts_both :
    Marker.o ∈ spear.map (fun p ↦ p.1.predicts p.2) ∧
      Marker.a ∈ spear.map (fun p ↦ p.1.predicts p.2) := by
  decide

/-! ### Fijian -/

/-- The Fijian examples, and Hawaiian *o* with Fijian *no-* for locations (p. 47). -/
theorem fijian_marker_eq :
    ∀ d ∈ fijianData,
      (group d).isSome ∧ fijianMarker d = (group d).map (·.relationship.fijian) := by
  decide +kernel

theorem not_forall_o_iff_ke : ¬ ∀ r : Relationship, r.hawaiian = .o ↔ r.fijian = .ke :=
  fun h ↦ absurd ((h (.controlled (some .location))).1 rfl) (by decide)

end Wilson1976
