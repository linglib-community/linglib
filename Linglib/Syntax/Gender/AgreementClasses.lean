module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.Comparable
public import Mathlib.SetTheory.Cardinal.Finite
public import Linglib.Core.Data.Setoid.Basic
public import Linglib.Core.Logic.Function.FactorsThrough
public import Linglib.Morphology.Paradigm.Polarity
public import Linglib.Syntax.Gender.Basic

/-!
# Agreement classes and target genders

This file defines the agreement classes of a language's nouns and the target genders of its
agreement targets, and classifies the map between the target genders of two numbers, in the
lattice of partitions.

An agreement class is a set of nouns that take the same agreement forms on every target in
every morphosyntactic form, and the controller genders of a language are its agreement
classes. The forms a target shows are its target genders, and the agreement classes are the
meet of the partitions they induce; there may be fewer target genders than controller genders,
Romanian having three of the latter over two of the former in each number. The partitions of
the genders by two numbers' target genders are equal, as in French, the singular's strictly
finer, as in German, or incomparable, as in Romanian or Lak. A strictly finer plural would
distinguish more target genders, which Greenberg's universal 37 excludes.

## Main definitions

* `Gender.agreementClasses`: the kernel of the noun-level agreement map.
* `Gender.targetGenders`: the range of the agreement map restricted to one target.
* `Gender.Parallel`, `Gender.Convergent`, `Gender.Crossed`: the partitions of two numbers'
  target genders are equal, the first strictly finer, or incomparable.

## Main results

* `Gender.agreementClasses_eq_iInf`, `Gender.faithful_iff_iInf_eq_bot`: the agreement classes
  are the meet of the targets' partitions, and controller genders are faithful exactly when
  that meet is discrete.
* `Gender.card_quotient_agreementClasses`: the controller genders are as many as the
  agreement map has values.
* `Gender.card_range_le_prod`: the controller genders are at most the product over the
  targets of the target genders.
* `Gender.agreementClasses_eq_ker_of_faithful`: under faithful agreement mediated by an
  assignment, the agreement classes are the assignment's genders.
* `Gender.convergent_or_parallel_or_convergent_or_crossed`: every map between two numbers'
  target genders is parallel, crossed, or convergent in one direction.
* `Gender.Convergent.card_range_lt`: a convergent map distinguishes strictly fewer target
  genders in the second number.
* `Morphology.Polar.faithful`, `Morphology.Polar.parallel`: a polar exponent of gender and
  number separates the genders and is a parallel system.

## Implementation notes

* The index `T` of the agreement map is whatever the map is restricted to: a target
  category, a morphosyntactic form, or a pair of the two, so that target genders can be
  counted per target as well as per number across targets.
* An assignment `N → G` gives every noun one controller gender, the Canonical Gender
  Principle of [corbett-fedden-2016].
* The relations between two numbers take any controllers; the fragments state them of their
  genders rather than their nouns.
* The kernel of a map is the syncretism of `Morphology/Paradigm/Basic.lean`, read here over the
  controllers a target agrees with rather than over the cells of a paradigm.
* Subgenders, agreement classes differing on a minority of forms, inquorate genders, small
  closed classes whose pattern mixes other genders, and overdifferentiated targets are the
  steps from agreement classes to controller genders that remain to be defined; until then
  the agreement classes of a fragment are its controller genders only when the fragment
  records no such class.

## References

* [corbett-1991] — chapter 6
* [zaliznjak-1964] — agreement classes
* [corbett-fedden-2016] — the Canonical Gender Principle
* [greenberg-1963] — Universal 37: the plural never distinguishes more genders than the
  singular
* [corbett-1998] — polarity
-/

@[expose] public section

namespace Gender

variable {N T F : Type*}

/-- Two nouns fall in one of Zaliznjak's agreement classes when they take the same form on
every target in every morphosyntactic form. -/
abbrev agreementClasses (agr : N → T → F) : Setoid N := Setoid.ker agr

/-- The agreement classes are the meet of the partitions the targets induce. -/
theorem agreementClasses_eq_iInf (agr : N → T → F) :
    agreementClasses agr = ⨅ t, Setoid.ker (agr · t) :=
  Setoid.ker_pi fun t n ↦ agr n t

/-- Controller genders are faithful exactly when the targets' partitions meet in the discrete
one. -/
theorem faithful_iff_iInf_eq_bot {agr : N → T → F} :
    Faithful agr ↔ ⨅ t, Setoid.ker (agr · t) = ⊥ := by
  rw [← agreementClasses_eq_iInf]
  exact Setoid.ker_eq_bot_iff.symm

/-- The controller genders, being the agreement classes, are as many as the agreement map
has values. -/
theorem card_quotient_agreementClasses (agr : N → T → F) :
    Nat.card (Quotient (agreementClasses agr)) = Nat.card (Set.range agr) :=
  Nat.card_congr (Setoid.quotientKerEquivRange agr)

/-- The target genders of a target are the forms it shows. -/
abbrev targetGenders (agr : N → T → F) (t : T) : Set F := Set.range (agr · t)

/-- The controller genders are at most the product of the target genders over the targets. -/
theorem card_range_le_prod [Finite N] [Fintype T] (agr : N → T → F) :
    Nat.card (Set.range agr) ≤ ∏ t, Nat.card (targetGenders agr t) := by
  rw [← Nat.card_pi]
  exact Nat.card_le_card_of_injective (fun f t ↦ ⟨f.1 t, f.2.imp fun n hn ↦ congrFun hn t⟩)
    fun f g h ↦ Subtype.ext (funext fun t ↦ congrArg Subtype.val (congrFun h t))

/-- Under faithful agreement mediated by an assignment, the agreement classes are the
assignment's genders. -/
theorem agreementClasses_eq_ker_of_faithful {G : Type*} {assign : N → G}
    {nounAgr : N → T → F} {agr : G → T → F} (med : nounAgr = agr ∘ assign)
    (faith : Faithful agr) : agreementClasses nounAgr = Setoid.ker assign :=
  med ▸ Setoid.ker_comp_of_injective assign faith

section NumberMap

variable {G F' : Type*} {sg : G → F} {pl : G → F'}

/-- The map between the target genders of two numbers is parallel when they partition the
genders alike. -/
def Parallel (sg : G → F) (pl : G → F') : Prop := Setoid.ker sg = Setoid.ker pl

/-- Convergent when the first number's partition is strictly finer, so that it determines the
second but not conversely. -/
def Convergent (sg : G → F) (pl : G → F') : Prop := Setoid.ker sg < Setoid.ker pl

/-- Crossed when neither partition refines the other. -/
def Crossed (sg : G → F) (pl : G → F') : Prop :=
  IncompRel (· ≤ ·) (Setoid.ker sg) (Setoid.ker pl)

/-- Every map between two numbers' target genders is convergent, parallel, convergent the other
way, or crossed. -/
theorem convergent_or_parallel_or_convergent_or_crossed (sg : G → F) (pl : G → F') :
    Convergent sg pl ∨ Parallel sg pl ∨ Convergent pl sg ∨ Crossed sg pl :=
  lt_or_eq_or_gt_or_incompRel _ _

theorem parallel_iff_factorsThrough :
    Parallel sg pl ↔ Function.FactorsThrough pl sg ∧ Function.FactorsThrough sg pl :=
  le_antisymm_iff

theorem convergent_iff_factorsThrough :
    Convergent sg pl ↔ Function.FactorsThrough pl sg ∧ ¬ Function.FactorsThrough sg pl :=
  lt_iff_le_not_ge

theorem crossed_iff_factorsThrough :
    Crossed sg pl ↔ ¬ Function.FactorsThrough pl sg ∧ ¬ Function.FactorsThrough sg pl :=
  Iff.rfl

/-- A convergent map distinguishes strictly fewer target genders in the second number. -/
theorem Convergent.card_range_lt [Finite G] (h : Convergent sg pl) :
    Nat.card (Set.range pl) < Nat.card (Set.range sg) := by
  rw [← Nat.card_congr (Setoid.quotientKerEquivRange pl),
    ← Nat.card_congr (Setoid.quotientKerEquivRange sg)]
  exact Setoid.card_quotient_strictAnti h

variable [Fintype G] [DecidableEq F] [DecidableEq F']

instance : Decidable (Parallel sg pl) := decidable_of_iff _ parallel_iff_factorsThrough.symm

instance : Decidable (Convergent sg pl) := decidable_of_iff _ convergent_iff_factorsThrough.symm

instance : Decidable (Crossed sg pl) := decidable_of_iff _ crossed_iff_factorsThrough.symm

end NumberMap

end Gender

/-! ### Polarity

A polar exponent of gender and number, the Somali article, is syncretic across the numbers and
within neither ([corbett-1991] chapter 7; [corbett-1998]), so it separates the genders and is a
parallel system. -/

namespace Morphology.Polar

variable {G T F : Type*} {f : G → T → F}

theorem faithful [Nonempty T] (h : Polar f) : Gender.Faithful f :=
  fun _ _ e ↦ h.injective (Classical.arbitrary T) (congrFun e _)

/-- A polar exponent is a parallel system, each number separating every gender. -/
theorem parallel (h : Polar f) (t t' : T) : Gender.Parallel (f · t) (f · t') :=
  (Setoid.ker_eq_bot_iff.2 (h.injective t)).trans (Setoid.ker_eq_bot_iff.2 (h.injective t')).symm

end Morphology.Polar
