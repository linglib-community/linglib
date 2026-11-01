module

public import Mathlib.Algebra.Group.Action.Defs
public import Linglib.Semantics.Polarity.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Logic.Aristotelian.Basic
public import Linglib.Semantics.Degree.Boundedness
public import Linglib.Semantics.Degree.Comparison
public import Mathlib.Order.Interval.Set.Disjoint

/-!
# Antonymy

This file defines the vocabulary of an antonym pair of gradable adjectives, *tall* and *short*
or *happy* and *unhappy*. Following Kennedy (2007) and Kennedy and McNally (2005), the two
members measure the same degrees under inverse orderings, so an adjective's `Polarity` is which
member it is, `positive` for the member measuring in the scale's increasing direction (*tall*)
and `negative` for the inverted one (*short*). Inverting twice restores the ordering, so
`negative * p` is the polarity of the antonym of a `p` adjective, and polarity acts on scale
boundedness and on comparisons through the order dual. The positive forms of the members are
contradictory (*clean* and *dirty*) or contrary (*tall* and *short*, which leave a gap), two
cells of the Aristotelian square in the sense of Cruse and Horn; a lexical pair is contradictory
when its poles take complementary standards, `Degree.AntonymPair.ComplementaryStandards`.

The contrary case is modelled by a `Degree.ThresholdPair` on a linearly ordered scale, the
positive form true above its upper threshold and the negative form below its lower one, and
`Degree.AntonymForm` is the quadruplet *happy*, *not happy*, *unhappy*, *not unhappy* that
sentential negation generates from a pair, with a contradictory denotation on one threshold,
where *not unhappy* collapses to *happy*, and a strengthened denotation on a pair, where the gap
keeps them apart, as in Krifka's account. Evaluative valence, whether a predicate denotes a good
or a bad property, is a second axis on which the poles differ, distinct from polarity.

## Main definitions

* The actions of `Polarity` on `Boundedness` and on `Comparison`, the negative polarity by the
  order dual.
* `EvaluativeValence`: whether a gradable predicate denotes a good, a bad or a neutral property.
* `ThresholdPair` and its `ThresholdPair.gap`, the interval between the two thresholds.
* `AntonymForm` with `AntonymForm.contradictoryDenotation`, `AntonymForm.strengthenedDenotation` and
  `AntonymForm.complexity`.

## Main results

* `AntonymForm.contradictoryDenotation_notPositive`: contradictory negation is the complement, so
  double negation eliminates.
* `ThresholdPair.gap_nonempty_iff`, `AntonymForm.strengthenedDenotation_notNegative_diff_positive`,
  `AntonymForm.strengthenedDenotation_notPositive_diff_negative`: a pair leaves a gap when its lower
  threshold does not exceed its upper one, and the gap is what each negated form adds to the
  opposite simple form.
* `isCompl_contradictoryDenotation`, `isContrary_strengthenedDenotation`: the two denotations
  realize the two cells of the Aristotelian square.

## References

* [kennedy-2007]
* [kennedy-mcnally-2005]
* [cruse-1986]
* [horn-1989]
* [krifka-2007b]
* [tessler-franke-2019]
* [nouwen-2024]
-/

@[expose] public section

namespace Degree

/-! ### Polarity -/

/-- The negative member of an antonym pair measures on the dual scale; two inversions restore the
ordering, so the antonym of *short* is *tall*. Markedness is a separate matter, since equipollent
pairs like *hot* and *cold* have no unmarked member. Sentential negation acts on the adjective's
denotation by complement instead, so *not short* is the contradictory of *short* and does not
entail *tall* (`AntonymForm.strengthenedDenotation`). -/
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

/-! ### Evaluative valence -/

/-- The evaluative valence of a gradable predicate records whether it denotes a good, a bad or
an evaluatively neutral property, which is distinct from scalar polarity ([nouwen-2024]).
Negative valence yields high-degree intensifiers and positive valence moderate-degree ones, which
Nouwen explains by the Goldilocks effect, the negative evaluation of a scale's extremes. -/
inductive EvaluativeValence where
  | positive
  | negative
  | neutral
  deriving Repr, DecidableEq

/-- The valence of the opposite pole of an antonym pair swaps positive and negative and keeps
neutral. -/
def EvaluativeValence.flip : EvaluativeValence → EvaluativeValence
  | .positive => .negative
  | .negative => .positive
  | .neutral => .neutral

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

/-- The morphosyntactic complexity of a form, the number of negations counted as
[krifka-2007b] orders them, `0 < 2 < 3 < 5`, matching [tessler-franke-2019]'s utterance cost. -/
def complexity : AntonymForm → Nat
  | .positive    => 0
  | .negative    => 2
  | .notPositive => 3
  | .notNegative => 5

section Denotation
variable {D : Type*}

/-- The contradictory denotation of a form on a single threshold `θ`, which both poles share, so
that the four forms collapse to two, *happy* and *not unhappy* above it, *not happy* and
*unhappy* at or below it. This is the literal semantics [krifka-2007b] attributes to a pair
before pragmatic strengthening. -/
def contradictoryDenotation [Preorder D] (θ : D) : AntonymForm → Set D
  | .positive | .notNegative => Set.Ioi θ
  | .notPositive | .negative => Set.Iic θ

/-- The strengthened denotation of a form on a threshold pair, whose gap lifts *not unhappy*
away from *happy* and *not happy* away from *unhappy*. This is the effective semantics after
strengthening ([krifka-2007b]) or the lexical one ([alexandropoulou-gotzner-2024a]). -/
def strengthenedDenotation [Preorder D] (tp : ThresholdPair D) : AntonymForm → Set D
  | .positive => Set.Ioi tp.pos
  | .notPositive => Set.Iic tp.pos
  | .negative => Set.Iio tp.neg
  | .notNegative => Set.Ici tp.neg

variable [LinearOrder D] (θ : D) (tp : ThresholdPair D)

instance decidableMemContradictoryDenotation :
    ∀ f, DecidablePred (· ∈ contradictoryDenotation θ f)
  | .positive | .notNegative => fun d ↦ inferInstanceAs (Decidable (θ < d))
  | .notPositive | .negative => fun d ↦ inferInstanceAs (Decidable (d ≤ θ))

instance decidableMemStrengthenedDenotation :
    ∀ f, DecidablePred (· ∈ strengthenedDenotation tp f)
  | .positive => fun d ↦ inferInstanceAs (Decidable (tp.pos < d))
  | .notPositive => fun d ↦ inferInstanceAs (Decidable (d ≤ tp.pos))
  | .negative => fun d ↦ inferInstanceAs (Decidable (d < tp.neg))
  | .notNegative => fun d ↦ inferInstanceAs (Decidable (tp.neg ≤ d))

theorem contradictoryDenotation_synonymy :
    contradictoryDenotation θ .negative = contradictoryDenotation θ .notPositive ∧
      contradictoryDenotation θ .notNegative = contradictoryDenotation θ .positive :=
  ⟨rfl, rfl⟩

/-- Contradictory negation is the complement of the positive form, so double negation
eliminates and *not unhappy* is *happy*, the puzzle Krifka solves pragmatically. -/
theorem contradictoryDenotation_notPositive :
    contradictoryDenotation θ .notPositive = (contradictoryDenotation θ .positive)ᶜ :=
  Set.compl_Ioi.symm

/-- What *not unhappy* adds to *happy* under the strengthened denotation is the gap. -/
theorem strengthenedDenotation_notNegative_diff_positive :
    strengthenedDenotation tp .notNegative \ strengthenedDenotation tp .positive = tp.gap := by
  rw [strengthenedDenotation, strengthenedDenotation, Set.sdiff_eq, Set.compl_Ioi,
    Set.Ici_inter_Iic, ThresholdPair.gap]

/-- What *not happy* adds to *unhappy* under the strengthened denotation is the gap too. -/
theorem strengthenedDenotation_notPositive_diff_negative :
    strengthenedDenotation tp .notPositive \ strengthenedDenotation tp .negative = tp.gap := by
  rw [strengthenedDenotation, strengthenedDenotation, Set.sdiff_eq, Set.compl_Iio, Set.inter_comm,
    Set.Ici_inter_Iic, ThresholdPair.gap]

/-- With one threshold the negative form is the complement of the positive form, so the pair is
contradictory. -/
theorem isCompl_contradictoryDenotation :
    IsCompl (contradictoryDenotation θ .positive) (contradictoryDenotation θ .negative) :=
  contradictoryDenotation_notPositive θ ▸ isCompl_compl

open Aristotelian in
/-- With a pair that leaves a gap the positive and negative forms are disjoint but not
exhaustive, so the pair is contrary. -/
theorem isContrary_strengthenedDenotation (h : tp.neg ≤ tp.pos) :
    IsContrary (strengthenedDenotation tp .positive) (strengthenedDenotation tp .negative) :=
  ⟨Set.Ioi_disjoint_Iio_of_le h, fun hco ↦ by
    have hmem :
        tp.neg ∈ strengthenedDenotation tp .positive ⊔ strengthenedDenotation tp .negative := by
      rw [hco.eq_top]; trivial
    exact hmem.elim (fun hp ↦ h.not_gt hp) (lt_irrefl _)⟩

end Denotation

end AntonymForm

end Degree
