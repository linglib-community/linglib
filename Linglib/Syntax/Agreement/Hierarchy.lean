module

public import Mathlib.Order.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# The Agreement Hierarchy

A controller such as Russian *vrač* 'doctor' denoting a woman, or British English *committee*,
admits two agreements: syntactic agreement follows the feature value the controller is
assigned, semantic agreement its meaning. [corbett-1979] ranges the targets of agreement in
four positions, the attributive modifier, the predicate, the relative pronoun and the personal
pronoun, and claims that the likelihood of semantic agreement never decreases from one to the
next. A record of that likelihood maps each position to a value, or to `none` where it records
nothing, and the claim is that it is monotone where it records a value: for a record `f` and any
default `d`, `MonotoneOn (fun i ↦ (f i).getD d) {i | (f i).isSome}`. The likelihood is graded
by `Availability`, along which admitting semantic agreement is monotone
(`Availability.monotone_allows_semantic`) and admitting syntactic agreement antitone
(`Availability.antitone_allows_syntactic`).

## Implementation notes

* The attributive is the least position, the order in which [corbett-1991] prints the
  hierarchy; [corbett-2006] prints the same ranking with `>`, for decreasing canonicity. With
  the attributive least, the claim of the hierarchy is monotonicity.
* A record keeps `none` at a position where agreement does not apply or there are no data, since
  a value there would be a datum the source does not give. The hierarchy's claim reads the
  record with a default on the positions it records, as mathlib reads `Polynomial.degree` with
  `Polynomial.natDegree`; the default is never compared, and every result of mathlib's
  `MonotoneOn` (composition along the positions, restriction to fewer of them) applies without
  a predicate of the hierarchy's own. A record with a value everywhere is a total map, and its
  claim is `Monotone`.
* `Availability` has the five degrees that [corbett-1991]'s summary of the evidence shades.

## References

* [corbett-1979]
* [corbett-1983]
* [corbett-1991]
* [corbett-2006]
-/

@[expose] public section

namespace Agreement

/-- A position of the Agreement Hierarchy ([corbett-1979]). -/
inductive Position where
  /-- The attributive modifier (French *un bon livre*). -/
  | attributive
  /-- The predicate, a finite verb or a predicate adjective (Russian *kniga interesna*). -/
  | predicate
  /-- The relative pronoun (German *der ~ die ~ das*). -/
  | relativePronoun
  /-- The personal pronoun (English *he ~ she ~ it*). -/
  | personalPronoun
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The Agreement Hierarchy as a chain:
`attributive < predicate < relativePronoun < personalPronoun`. -/
instance : LinearOrder Position := LinearOrder.lift' Position.ctorIdx (by decide)

/-- Whether an agreement form follows the feature value the controller is assigned or the
controller's meaning. -/
inductive Kind where
  | syntactic
  | semantic
  deriving DecidableEq, Repr, Fintype

/-- Syntactic agreement lies below semantic agreement, so that a map to agreements is
monotone when it never trades semantic agreement for syntactic. -/
instance : LinearOrder Kind := LinearOrder.lift' Kind.ctorIdx (by decide)

/-- The availability of semantic agreement at a position of a hierarchy, in the five degrees
of [corbett-1991]'s summary of hybrid nouns, ordered by the likelihood of semantic
agreement. -/
inductive Availability where
  | syntacticOnly
  | mostlySyntactic
  | both
  | mostlySemantic
  | semanticOnly
  deriving DecidableEq, Repr, Fintype

namespace Availability

/-- Availabilities are ordered by the likelihood of semantic agreement. -/
instance : LinearOrder Availability := LinearOrder.lift' Availability.ctorIdx (by decide)

/-- Which agreement an availability admits: each, unless only the other is found. -/
def Allows (a : Availability) : Kind → Prop
  | .syntactic => a ≠ .semanticOnly
  | .semantic => a ≠ .syntacticOnly

instance (a : Availability) : DecidablePred a.Allows
  | .syntactic => inferInstanceAs (Decidable (a ≠ .semanticOnly))
  | .semantic => inferInstanceAs (Decidable (a ≠ .syntacticOnly))

theorem monotone_allows_semantic : Monotone (Allows · .semantic) :=
  (by decide : ∀ a b : Availability, a ≤ b → a.Allows .semantic → b.Allows .semantic)

theorem antitone_allows_syntactic : Antitone (Allows · .syntactic) :=
  (by decide : ∀ a b : Availability, a ≤ b → b.Allows .syntactic → a.Allows .syntactic)

end Availability

end Agreement
