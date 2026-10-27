module

public import Linglib.Fragments.Dutch.Adpositions
public import Linglib.Syntax.WordOrder

/-!
# Helmantel 2002: interactions in the Dutch adpositional domain

Helmantel's dissertation sorts the core Dutch adpositions by the path specification in their
denotation. A narrow locative, *in*, *op*, *achter*, denotes a location with no path; a point
locative, *naar*, *tot*, *van*, denotes a point on a path and is inherently directional; an
extended locative, *door*, *langs*, *om*, denotes a location with extension along a path. Five
distributional tests separate the three classes, and the classification has a syntactic
correlate. Directionality sits in a functional projection above the adposition, the
directionality phrase, whose head the adposition moves to. An inherently directional adposition
checks the directionality itself and leaves its complement where the adposition selects it,
which is the prepositional order; any other adposition in a directional phrase moves its
complement to the specifier of the directionality phrase as well, which is the postpositional
order. The postpositional order is thus derived from the prepositional one, never the reverse,
and the adpositions with a postpositional use are a subset of the prepositions.

The complement in the specifier of the directionality phrase receives a path interpretation, and
that specifier is the one position from which an element leaves the phrase, Van Riemsdijk's
escape hatch. So the complement of a postpositional phrase is interpreted as the path travelled,
is extractable, and cannot be a bare mass noun, while the complement of a prepositional phrase
is a location, stays inside the phrase, and is unrestricted.

The classification is checked against the Dutch adposition fragment: the point locatives are the
grammar's inherently directional prepositions and have no postpositional use, the narrow
locatives are locational before their complement, and the grammar reads the path a narrow
locative's postposition denotes as a goal and an extended locative's as a route or a source, which
is the difference the length-modification test tracks. The two core adpositions the
classification leaves out, *met* and *zonder*, are the fragment's non-spatial ones.

## Main definitions

* `narrowLocatives`, `pointLocatives`, `extendedLocatives`: the classification of the core
  adpositions, over the fragment's entries.
* `DPRaises`, `linearization`: the complement's movement to the specifier of the directionality
  phrase, and the order of the adposition and its complement that results.

## Implementation notes

* The classes are the dissertation's lists of core adpositions, as lists of fragment entries;
  the grammar's *over* 'across' is the one the dissertation classifies. The remaining, younger
  adpositions are left unclassified, as the dissertation leaves them.
* The directionality phrase is modelled by two parameters, whether it is projected and whether
  the adposition is inherently directional; the adposition's own movement to its head, the
  dimensionality requirement on the complement and its consequences for mass nouns, and the
  complex adpositional phrases of the second half of the dissertation are described here and not
  formalized.

## References

* [M. Helmantel, *Interactions in the Dutch Adpositional Domain* (2002)][helmantel-2002]
* [H. van Riemsdijk, *A Case Study in Syntactic Markedness: The Binding Nature of Prepositional
  Phrases* (1978)][van-riemsdijk-1978]
* [R. S. Kayne, *The Antisymmetry of Syntax* (1994)][kayne-1994]
-/

@[expose] public section

namespace Helmantel2002

open Dutch.Adpositions

/-! ### The classification of the core adpositions -/

/-- The narrow locative adpositions, whose denotation has no path specification. -/
def narrowLocatives : List Dutch.Adposition :=
  [achter, beneden, bij, binnen, boven, buiten, in_, naast, onder, op, tussen]

/-- The point locative adpositions, whose complement is a point on a path, are the inherently
directional adpositions. -/
def pointLocatives : List Dutch.Adposition := [naar, tot, van]

/-- The extended locative adpositions, whose complement extends along a path. -/
def extendedLocatives : List Dutch.Adposition :=
  [door, langs, om, over₁, rond, uit, via]

theorem classes_spatial :
    ∀ a ∈ narrowLocatives ++ pointLocatives ++ extendedLocatives, a.IsSpatial := by
  decide

theorem met_zonder_not_spatial : ¬ met.IsSpatial ∧ ¬ zonder.IsSpatial := by
  decide

/-- A point locative is one of the grammar's directional prepositions. -/
theorem pointLocative_directional :
    ∀ a ∈ pointLocatives, ∃ d ∈ a.direction .pre, d ≠ .place := by
  decide

/-- A narrow locative is locational before its complement. -/
theorem narrowLocative_locational : ∀ a ∈ narrowLocatives, a.direction .pre = some .place := by
  decide

/-- A point locative is a preposition only: an inherently directional adposition checks the
directionality itself and never raises its complement. -/
theorem pointLocative_linearization : ∀ a ∈ pointLocatives, a.linearization = {.pre} := by
  decide

/-- The postposition of a narrow locative denotes a goal path, *de berg op* 'up the mountain':
the complement is read as the path and the location the preposition denotes as its endpoint,
which is why a length modifier can measure it. -/
theorem narrowLocative_direction_post :
    ∀ a ∈ narrowLocatives, a.IsPostposition → a.direction .post = some .goal := by
  decide

/-- The postposition of an extended locative denotes a route or a source path, *het bos door*
'through the woods', never a goal: the complement already extends along the path. -/
theorem extendedLocative_direction_post :
    ∀ a ∈ extendedLocatives, a.IsPostposition → ∃ d ∈ a.direction .post, d ≠ .goal := by
  decide

/-! ### The directionality phrase -/

section DirP

variable (dirP inherent : Prop) [Decidable dirP] [Decidable inherent]

/-- The complement moves to the specifier of the directionality phrase when the phrase is
projected and the adposition is not inherently directional; an inherently directional adposition
checks the directionality by moving to the head alone and leaves its complement in place. -/
def DPRaises : Prop := dirP ∧ ¬ inherent

instance : Decidable (DPRaises dirP inherent) := inferInstanceAs (Decidable (_ ∧ _))

/-- The adposition follows its complement when the complement has raised, and precedes it
otherwise. -/
def linearization : Adposition.Linearization :=
  if DPRaises dirP inherent then .post else .pre

variable {dirP inherent}

/-- The postpositional order is a directional phrase whose adposition is not inherently
directional, so the postpositional order is derived from the prepositional one and the
postpositions are a subset of the prepositions. -/
theorem linearization_eq_post_iff : linearization dirP inherent = .post ↔ dirP ∧ ¬ inherent := by
  unfold linearization DPRaises; split <;> simp [*]

/-- An inherently directional adposition is a preposition. -/
theorem linearization_eq_pre_of_inherent (h : inherent) : linearization dirP inherent = .pre := by
  unfold linearization DPRaises; split <;> simp_all

theorem dirP_of_linearization_eq_post (h : linearization dirP inherent = .post) : dirP :=
  (linearization_eq_post_iff.1 h).1

/-- The complement sits in the specifier of the directionality phrase exactly in the
postpositional order. That specifier is the one position from which an element leaves the
phrase, the escape hatch Van Riemsdijk's Head Constraint allows, and the position in which the
complement is read as the path travelled; so the complement of a postpositional phrase is
extractable and a path, and the complement of a prepositional phrase is neither. -/
theorem dpRaises_iff_linearization_eq_post :
    DPRaises dirP inherent ↔ linearization dirP inherent = .post :=
  linearization_eq_post_iff.symm

end DirP

end Helmantel2002
