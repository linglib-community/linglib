module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.Setoid.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Linglib.Core.Logic.Function.FactorsThrough
public import Linglib.Syntax.Gender.Basic

/-!
# Agreement classes and target genders

This file defines the agreement classes of a language's nouns and the target genders of its
agreement targets, and classifies the map between the target genders of two numbers.

An agreement class is a set of nouns that take the same agreement forms on every target in
every morphosyntactic form, and the controller genders of a language are its agreement
classes. A target gender is a form an agreeing target distinguishes, and there may be fewer
target genders than controller genders: Romanian has three of the latter over two of the
former in each number. The target genders of the singular and the plural determine one
another, as in French, the singular's determine the plural's without the converse, as in
German, or neither determines the other, as in Romanian or Lak.

## Main definitions

* `Gender.agreementClasses`: the kernel of the noun-level agreement map.
* `Gender.targetGenders`: the range of the agreement map restricted to one target.
* `Gender.Parallel`, `Gender.Convergent`, `Gender.Crossed`: the map between the target
  genders of two numbers, as each factors through the other or not.
* `Gender.Polar`: an exponent of two features whose polar opposites coincide.

## Main results

* `Gender.card_quotient_agreementClasses`: the controller genders are as many as the
  agreement map has values.
* `Gender.card_range_le_prod`: the controller genders are at most the product over the
  targets of the target genders.
* `Gender.parallel_iff_ker_eq`, `Gender.convergent_iff_ker_lt`: the map between two numbers'
  target genders is the order of their kernels.
* `Gender.Polar.card_le_two`, `Gender.Polar.parallel`: polarity forces two-valued features
  and is a parallel system.

## Implementation notes

* The index `T` of the agreement map is whatever the map is restricted to: a target
  category, a morphosyntactic form, or a pair of the two, so that target genders can be
  counted per target as well as per number across targets.
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

theorem card_quotient_agreementClasses (agr : N → T → F) :
    Nat.card (Quotient (agreementClasses agr)) = Nat.card (Set.range agr) :=
  Nat.card_congr (Setoid.quotientKerEquivRange agr)

/-- The target genders of a target are the forms it shows. -/
abbrev targetGenders (agr : N → T → F) (t : T) : Set F := Set.range (agr · t)

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

variable {F' : Type*}

/-- The map between the target genders of two numbers is parallel when each determines the
other. -/
def Parallel (sg : N → F) (pl : N → F') : Prop :=
  Function.FactorsThrough pl sg ∧ Function.FactorsThrough sg pl

/-- Convergent when the first determines the second but not conversely. -/
def Convergent (sg : N → F) (pl : N → F') : Prop :=
  Function.FactorsThrough pl sg ∧ ¬ Function.FactorsThrough sg pl

/-- Crossed when neither determines the other. -/
def Crossed (sg : N → F) (pl : N → F') : Prop :=
  ¬ Function.FactorsThrough pl sg ∧ ¬ Function.FactorsThrough sg pl

theorem parallel_iff_ker_eq {sg : N → F} {pl : N → F'} :
    Parallel sg pl ↔ Setoid.ker sg = Setoid.ker pl :=
  (le_antisymm_iff (a := Setoid.ker sg) (b := Setoid.ker pl)).symm

theorem convergent_iff_ker_lt {sg : N → F} {pl : N → F'} :
    Convergent sg pl ↔ Setoid.ker sg < Setoid.ker pl :=
  (lt_iff_le_not_ge (a := Setoid.ker sg) (b := Setoid.ker pl)).symm

variable [Fintype N] [DecidableEq F] [DecidableEq F'] (sg : N → F) (pl : N → F')

instance : Decidable (Parallel sg pl) := by
  unfold Parallel; infer_instance

instance : Decidable (Convergent sg pl) := by
  unfold Convergent; infer_instance

instance : Decidable (Crossed sg pl) := by
  unfold Crossed; infer_instance

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

theorem Polar.parallel (h : Polar f) (t t' : T) : Parallel (f · t) (f · t') :=
  ⟨fun _ _ e ↦ congrArg (f · t') (h.injective t e),
    fun _ _ e ↦ congrArg (f · t) (h.injective t' e)⟩

end Polar

end Gender
