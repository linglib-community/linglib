module

public import Mathlib.Algebra.Group.Action.Defs
public import Linglib.Semantics.Negation.Polarity
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Logic.Aristotelian.Basic
public import Linglib.Semantics.Degree.Boundedness
public import Linglib.Semantics.Degree.Comparison
public import Mathlib.Order.Interval.Set.Disjoint

/-!
# Antonymy

The members of an antonym pair, *tall* and *short* or *happy* and *unhappy*, measure the same
degrees under inverse orderings, so an adjective's `Polarity` says which member it is, and
`negative * p` is the polarity of the antonym of a `p` adjective. Polarity acts on
[boundedness](##Boundedness.negative_smul) and on [comparisons](##Comparison.negative_smul) through
the order dual. The positive forms of the members are
[contradictory](##AntonymForm.isCompl_contradictoryDenotation), as *clean* and *dirty* are, or
[contrary](##AntonymForm.isContrary_contraryDenotation), as *tall* and *short* are, two cells of
the Aristotelian square. The contrary case is a `ThresholdPair` on a linearly ordered scale, and
[its gap](##ThresholdPair.gap_nonempty_iff) keeps *not unhappy* apart from *happy* in the quadruplet
`AntonymForm`.

## References

* [kennedy-2007]
* [kennedy-mcnally-2005]
* [cruse-1986]
* [horn-1989]
* [krifka-2007b]
-/

@[expose] public section

/-! ### Polarity -/

/-- The negative member of an antonym pair measures on the dual scale; two inversions restore the
ordering, so the antonym of *short* is *tall*. Markedness is a separate matter, since equipollent
pairs like *hot* and *cold* have no unmarked member. Sentential negation acts on the adjective's
denotation by complement instead, so *not short* is the contradictory of *short* and does not
entail *tall* (`AntonymForm.contraryDenotation`). -/
instance : MulAction Polarity Boundedness :=
  .ofEndHom (Polarity.lift ⟨Boundedness.dual, Boundedness.dual_involutive.comp_self⟩)

@[simp] theorem Boundedness.negative_smul (b : Boundedness) : Polarity.negative • b = b.dual :=
  rfl

/-- The negative member of an antonym pair compares on the reversed scale, so its comparison is
the dual one, so that *shorter* is `Polarity.negative • Comparison.gt`. -/
instance : MulAction Polarity Comparison :=
  .ofEndHom (Polarity.lift ⟨Comparison.dual, Comparison.dual_involutive.comp_self⟩)

@[simp] theorem Comparison.negative_smul (c : Comparison) : Polarity.negative • c = c.dual :=
  rfl

/-! ### The two-threshold model of a contrary pair -/

/-- The two thresholds of a contrary antonym pair (*happy* and *unhappy*) are `pos` for the
positive form, true above it, and `neg` for the negative form, true below it. That the lower
threshold does not exceed the upper is a hypothesis where a gap is needed, not a stored
invariant. -/
structure ThresholdPair (D : Type*) where
  pos : D
  neg : D
  deriving Repr, DecidableEq

namespace ThresholdPair
variable {D : Type*} [Preorder D] (tp : ThresholdPair D)

/-- The gap of a pair is the region that is neither positive nor negative, from the lower
threshold to the upper. -/
def gap : Set D := Set.Icc tp.neg tp.pos

theorem mem_gap {d : D} : d ∈ tp.gap ↔ tp.neg ≤ d ∧ d ≤ tp.pos := Iff.rfl

/-- A pair leaves a gap exactly when its lower threshold does not exceed its upper one. -/
theorem gap_nonempty_iff : tp.gap.Nonempty ↔ tp.neg ≤ tp.pos := Set.nonempty_Icc

end ThresholdPair

/-! ### The quadruplet -/

/-- An antonym form is one of the four surface forms that sentential negation generates from an
antonym pair, *happy*, *not happy*, *unhappy* and *not unhappy*. The type carries no
semantics; a contradictory account collapses the four to two denotations and a contrary
account keeps four, and each is a function on it. -/
inductive AntonymForm where
  | positive       -- *happy*
  | notPositive    -- *not happy*
  | negative       -- *unhappy*
  | notNegative    -- *not unhappy*
  deriving Repr, DecidableEq, Fintype

namespace AntonymForm

/-- `flip` exchanges the two poles of the quadruplet, *happy* with *unhappy* and *not happy*
with *not unhappy*. -/
def flip : AntonymForm → AntonymForm
  | .positive    => .negative
  | .negative    => .positive
  | .notPositive => .notNegative
  | .notNegative => .notPositive

theorem flip_involutive : Function.Involutive flip := fun f ↦ by cases f <;> rfl

@[simp] theorem flip_flip (f : AntonymForm) : f.flip.flip = f := flip_involutive f

/-- The sign acts on the quadruplet by exchanging its poles. -/
instance : MulAction Polarity AntonymForm :=
  .ofEndHom (Polarity.lift ⟨flip, flip_involutive.comp_self⟩)

@[simp] theorem negative_smul (f : AntonymForm) : Polarity.negative • f = f.flip := rfl

/-- The simple form of a pole, *happy* for *not unhappy* and *unhappy* for *not happy*, which the
negated form of the other pole shares its contradictory denotation with
(`contradictoryDenotation_simple`). -/
def simple : AntonymForm → AntonymForm
  | .positive | .notNegative => .positive
  | .negative | .notPositive => .negative

section Denotation
variable {D : Type*}

/-- The contradictory denotation of a form, given the extension `U` of the positive pole: the
prefix and the particle both negate by complement, so that the four forms collapse to two, *happy*
and *not unhappy* on `U`, *not happy* and *unhappy* off it. This is the literal semantics
[krifka-2007b] attributes to a pair before pragmatic strengthening, with `U` the degrees above
the border. -/
def contradictoryDenotation (U : Set D) : AntonymForm → Set D
  | .positive | .notNegative => U
  | .notPositive | .negative => Uᶜ

/-- The contrary denotation of a form on a threshold pair, whose gap lifts *not unhappy* away from
*happy* and *not happy* away from *unhappy*. This is the lexical semantics of [horn-1989]'s
contrary analysis, on which a negated form covers the gap and the opposite pole; [krifka-2007b]
argues against it and derives the gap pragmatically from `contradictoryDenotation`. -/
def contraryDenotation [Preorder D] (tp : ThresholdPair D) : AntonymForm → Set D
  | .positive => Set.Ioi tp.pos
  | .notPositive => Set.Iic tp.pos
  | .negative => Set.Iio tp.neg
  | .notNegative => Set.Ici tp.neg

instance decidableMemContradictoryDenotation (U : Set D) [DecidablePred (· ∈ U)] :
    ∀ f, DecidablePred (· ∈ contradictoryDenotation U f)
  | .positive | .notNegative => fun d ↦ inferInstanceAs (Decidable (d ∈ U))
  | .notPositive | .negative => fun d ↦ inferInstanceAs (Decidable (d ∉ U))

/-- Each negated form is synonymous with the simple form of the other pole. -/
@[simp] theorem contradictoryDenotation_simple (U : Set D) (f : AntonymForm) :
    contradictoryDenotation U f.simple = contradictoryDenotation U f := by
  cases f <;> rfl

/-- The negative form is the complement of the positive form, so the pair is contradictory. -/
theorem isCompl_contradictoryDenotation (U : Set D) :
    IsCompl (contradictoryDenotation U .positive) (contradictoryDenotation U .negative) :=
  isCompl_compl

variable [LinearOrder D] (tp : ThresholdPair D)

instance decidableMemContraryDenotation :
    ∀ f, DecidablePred (· ∈ contraryDenotation tp f)
  | .positive => fun d ↦ inferInstanceAs (Decidable (tp.pos < d))
  | .notPositive => fun d ↦ inferInstanceAs (Decidable (d ≤ tp.pos))
  | .negative => fun d ↦ inferInstanceAs (Decidable (d < tp.neg))
  | .notNegative => fun d ↦ inferInstanceAs (Decidable (tp.neg ≤ d))

/-- What *not unhappy* adds to *happy* under the strengthened denotation is the gap. -/
theorem contraryDenotation_notNegative_diff_positive :
    contraryDenotation tp .notNegative \ contraryDenotation tp .positive = tp.gap := by
  rw [contraryDenotation, contraryDenotation, Set.sdiff_eq, Set.compl_Ioi,
    Set.Ici_inter_Iic, ThresholdPair.gap]

/-- What *not happy* adds to *unhappy* under the strengthened denotation is the gap too. -/
theorem contraryDenotation_notPositive_diff_negative :
    contraryDenotation tp .notPositive \ contraryDenotation tp .negative = tp.gap := by
  rw [contraryDenotation, contraryDenotation, Set.sdiff_eq, Set.compl_Iio, Set.inter_comm,
    Set.Ici_inter_Iic, ThresholdPair.gap]

open Aristotelian in
/-- With a pair that leaves a gap the positive and negative forms are disjoint but not
exhaustive, so the pair is contrary. -/
theorem isContrary_contraryDenotation (h : tp.neg ≤ tp.pos) :
    IsContrary (contraryDenotation tp .positive) (contraryDenotation tp .negative) :=
  ⟨Set.Ioi_disjoint_Iio_of_le h, fun hco ↦ by
    have hmem :
        tp.neg ∈ contraryDenotation tp .positive ⊔ contraryDenotation tp .negative := by
      rw [hco.eq_top]; trivial
    exact hmem.elim (fun hp ↦ h.not_gt hp) (lt_irrefl _)⟩

end Denotation

end AntonymForm
