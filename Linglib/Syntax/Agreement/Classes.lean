module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.Comparable
public import Mathlib.SetTheory.Cardinal.Finite
public import Linglib.Core.Data.Setoid.Basic
public import Linglib.Core.Logic.Function.FactorsThrough
public import Linglib.Syntax.Gender.Basic

/-!
# Agreement classes and target genders

This file defines the agreement classes of a language's nouns and the target genders of its
agreement targets, and classifies the map between the target genders of two numbers, all in the
lattice of partitions of the nouns.

An agreement class is a set of nouns that take the same agreement forms on every target in
every morphosyntactic form, and the controller genders of a language are its agreement
classes. Each target partitions the nouns by the forms it shows, its target genders, and the
agreement classes are the meet of these partitions; there may be fewer target genders than
controller genders, Romanian having three of the latter over two of the former in each number.
The partitions of the singular and the plural are equal, as in French, the singular's strictly
finer, as in German, or incomparable, as in Romanian or Lak. A strictly finer plural would
distinguish more target genders, which Greenberg's universal 37 excludes.

## Main definitions

* `Gender.agreementClasses`: the kernel of the noun-level agreement map.
* `Gender.targetGenders`: the range of the agreement map restricted to one target.
* `Gender.Parallel`, `Gender.Convergent`, `Gender.Crossed`: the partitions of two numbers'
  target genders are equal, the first strictly finer, or incomparable.
* `Gender.Polar`: an exponent of two features whose polar opposites coincide.

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
* `Gender.Polar.card_le_two`, `Gender.Polar.parallel`: polarity forces two-valued features
  and is a parallel system.

## Implementation notes

* The index `T` of the agreement map is whatever the map is restricted to: a target
  category, a morphosyntactic form, or a pair of the two, so that target genders can be
  counted per target as well as per number across targets.
* The kernel of a map is the syncretism of `Morphology/Paradigm/Basic.lean`, read here over the
  nouns a target agrees with rather than over the cells of a paradigm.
* Subgenders, agreement classes differing on a minority of forms, inquorate genders, small
  closed classes whose pattern mixes other genders, and overdifferentiated targets are the
  steps from agreement classes to controller genders that remain to be defined; until then
  the agreement classes of a fragment are its controller genders only when the fragment
  records no such class.

## References

* [corbett-1991] — chapter 6
* [zaliznjak-1964] — agreement classes
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

theorem agreementClasses_eq_ker_of_faithful {G : Type*} {assign : N → G}
    {nounAgr : N → T → F} {agr : G → T → F} (med : nounAgr = agr ∘ assign)
    (faith : Faithful agr) : agreementClasses nounAgr = Setoid.ker assign :=
  Setoid.ext fun a b ↦ by
    rw [Setoid.ker_def, Setoid.ker_def, med, Function.comp_apply, Function.comp_apply,
      faith.eq_iff]

section NumberMap

variable {F' : Type*} {sg : N → F} {pl : N → F'}

/-- The map between the target genders of two numbers is parallel when they partition the
nouns alike. -/
def Parallel (sg : N → F) (pl : N → F') : Prop := Setoid.ker sg = Setoid.ker pl

/-- Convergent when the first number's partition is strictly finer, so that it determines the
second but not conversely. -/
def Convergent (sg : N → F) (pl : N → F') : Prop := Setoid.ker sg < Setoid.ker pl

/-- Crossed when neither partition refines the other. -/
def Crossed (sg : N → F) (pl : N → F') : Prop :=
  IncompRel (· ≤ ·) (Setoid.ker sg) (Setoid.ker pl)

/-- Every map between two numbers' target genders is convergent, parallel, convergent the other
way, or crossed. -/
theorem convergent_or_parallel_or_convergent_or_crossed (sg : N → F) (pl : N → F') :
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
theorem Convergent.card_range_lt [Finite N] (h : Convergent sg pl) :
    Nat.card (Set.range pl) < Nat.card (Set.range sg) := by
  rw [← Nat.card_congr (Setoid.quotientKerEquivRange pl),
    ← Nat.card_congr (Setoid.quotientKerEquivRange sg)]
  exact Setoid.card_quotient_strictAnti h

variable [Fintype N] [DecidableEq F] [DecidableEq F']

instance : Decidable (Parallel sg pl) := decidable_of_iff _ parallel_iff_factorsThrough.symm

instance : Decidable (Convergent sg pl) := decidable_of_iff _ convergent_iff_factorsThrough.symm

instance : Decidable (Crossed sg pl) := decidable_of_iff _ crossed_iff_factorsThrough.symm

end NumberMap

/-! ### Polarity

A fusional exponent of two features, gender and number in the Somali article, is polar when
changing either value alone changes the form and changing both restores it, so that the polar
opposites are identical ([corbett-1991] chapter 7; [corbett-1998]). A polar exponent is
syncretic across the numbers and within neither, so it is a parallel system, and it confines
both features to two values. -/

section Polar

variable {G : Type*}

/-- An exponent of two features is polar when two cells share a form exactly when they
differ in both features or in neither. -/
def Polar (f : G → T → F) : Prop :=
  ∀ g g' t t', f g t = f g' t' ↔ (g = g' ↔ t = t')

variable {f : G → T → F}

instance [Fintype G] [Fintype T] [DecidableEq G] [DecidableEq T] [DecidableEq F] :
    Decidable (Polar f) := by
  unfold Polar; infer_instance

theorem Polar.flip (h : Polar f) : Polar (flip f) :=
  fun t t' g g' ↦ (h g g' t t').trans Iff.comm

theorem Polar.injective (h : Polar f) (t : T) : Function.Injective (f · t) :=
  fun _ _ e ↦ ((h _ _ t t).mp e).mpr rfl

theorem Polar.faithful [Nonempty T] (h : Polar f) : Faithful f :=
  fun _ _ e ↦ h.injective (Classical.arbitrary T) (congrFun e _)

/-- A polar exponent admits at most two values of either feature, since with three values of
one feature two of them would share a form. -/
theorem Polar.card_le_two [Fintype G] [Nontrivial T] (h : Polar f) :
    Fintype.card G ≤ 2 := by
  by_contra hc
  obtain ⟨g₁, g₂, g₃, h₁₂, h₁₃, h₂₃⟩ := Fintype.two_lt_card_iff.mp (not_le.mp hc)
  obtain ⟨t, t', ht⟩ := exists_pair_ne T
  have e₁ : f g₁ t = f g₂ t' := (h g₁ g₂ t t').mpr (iff_of_false h₁₂ ht)
  have e₃ : f g₃ t = f g₂ t' := (h g₃ g₂ t t').mpr (iff_of_false h₂₃.symm ht)
  exact h₁₃ (h.injective t (e₁.trans e₃.symm))

theorem Polar.card_le_two' [Fintype T] [Nontrivial G] (h : Polar f) : Fintype.card T ≤ 2 :=
  h.flip.card_le_two

theorem Polar.card_eq_two [Fintype G] [Nontrivial G] [Nontrivial T] (h : Polar f) :
    Fintype.card G = 2 :=
  le_antisymm h.card_le_two Fintype.one_lt_card

/-- A polar exponent is a parallel system, each number separating every value. -/
theorem Polar.parallel (h : Polar f) (t t' : T) : Parallel (f · t) (f · t') :=
  (Setoid.ker_eq_bot_iff.2 (h.injective t)).trans (Setoid.ker_eq_bot_iff.2 (h.injective t')).symm

end Polar

end Gender
