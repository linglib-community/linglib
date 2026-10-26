/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Algebra.Notation.Indicator

/-!
# Trivalent propositions

A trivalent proposition is a function `W → SignType`, true, false or undefined at each world.
Its worlds split into a positive extension, a negative extension and a gap, and Beaver and
Krahmer's assertion operator applied pointwise collapses the gap into the negative extension.
Strong Kleene conjunction and disjunction of propositions are the pointwise `⊓` and `⊔`. A
trivalent proposition is also a conditional event in de Finetti's sense, fixed by where it is
defined and where it is true. This file adds the extensions, bivalence, the conditional-event
decomposition, and the three families of trivalent quantifiers.

## Main definitions

* `Trivalent.posExt`, `Trivalent.negExt`, `Trivalent.gapExt`: the three extensions.
* `Trivalent.IsBivalent`: the proposition is never `0`.
* `Trivalent.forallWeak`, `Trivalent.existsWeak`: the Weak Kleene quantifiers, undefined as
  soon as any instance is.
* `Trivalent.forallStrong`, `Trivalent.existsStrong`: the Strong Kleene quantifiers, the
  indexed `⊓` and `⊔`.
* `Trivalent.forallHaug`, `Trivalent.existsHaug`: Haug's quantifiers, undefined only when
  every instance is, with `existsHaug_meetWeak_presuppose` as Quantifier Projection.

## Main results

* `Trivalent.indicator_support_ofProp_eq_one`, `Trivalent.indicator_ofProp_eq_indicator_ofProp_iff`:
  every trivalent proposition is the conditional event of its truth on its definedness, and two
  conditional events coincide exactly when they have the same condition and agree on it.

Each family is the quantifier of a theory of how a presupposition projects from the scope of a
quantifier. Over the domain's subtype, the Weak Kleene quantifiers project universally, as
Chemla's experiments support, Haug's existentially, as Mayr and Sauerland argue for a semantic
projection that pragmatics then strengthens, and the Strong Kleene existential of Kleene and Fox
is defined exactly where some instance is true or every instance is false; Spector and Sudo
delimit when each reading surfaces.

## Implementation notes

The Strong Kleene quantifiers are explicit definitions rather than `⨅` and `⨆`, because a
`CompleteLinearOrder` instance on `SignType` would carry a second `LinearOrder` parent that
instance search prefers, making every later `⊓` noncomputable.

## References

* [beaver-krahmer-2001]
* [kriz-2016]
* [haug-2014]
* [coppock-beaver-2015]
* [chemla-2009a]
* [mayr-sauerland-2015]
* [spector-sudo-2017]
* [fox-2013]
* [de-finetti-1936]
-/

@[expose] public section


namespace Trivalent

open SignType

variable {W : Type*}

/-! ### Extensions -/

/-- The positive extension collects the worlds where the proposition is true. -/
def posExt (p : W → SignType) : Set W := {w | p w = 1}

/-- The negative extension collects the worlds where the proposition is false. -/
def negExt (p : W → SignType) : Set W := {w | p w = -1}

/-- The extension gap collects the worlds where the proposition is neither true nor false. -/
def gapExt (p : W → SignType) : Set W := {w | p w = 0}

@[simp] theorem mem_posExt {p : W → SignType} {w : W} :
    w ∈ posExt p ↔ p w = 1 := Iff.rfl

@[simp] theorem mem_negExt {p : W → SignType} {w : W} :
    w ∈ negExt p ↔ p w = -1 := Iff.rfl

@[simp] theorem mem_gapExt {p : W → SignType} {w : W} :
    w ∈ gapExt p ↔ p w = 0 := Iff.rfl

instance (p : W → SignType) : DecidablePred (· ∈ posExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = 1))

instance (p : W → SignType) : DecidablePred (· ∈ negExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = -1))

instance (p : W → SignType) : DecidablePred (· ∈ gapExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = 0))

theorem posExt_union_negExt (p : W → SignType) : posExt p ∪ negExt p = Function.support p := by
  ext w; cases h : p w <;> simp [h]

theorem posExt_subset_support (p : W → SignType) : posExt p ⊆ Function.support p :=
  fun w (h : p w = 1) ↦ by simp [Function.mem_support, h]

theorem negExt_subset_support (p : W → SignType) : negExt p ⊆ Function.support p :=
  fun w (h : p w = -1) ↦ by simp [Function.mem_support, h]

theorem support_inter_compl_posExt (p : W → SignType) :
    Function.support p ∩ (posExt p)ᶜ = negExt p := by
  ext w; cases h : p w <;> simp [h]

theorem posExt_union_negExt_union_gapExt (p : W → SignType) :
    posExt p ∪ negExt p ∪ gapExt p = Set.univ := by
  ext w
  simp only [Set.mem_union, mem_posExt, mem_negExt, mem_gapExt, Set.mem_univ,
    iff_true]
  cases p w <;> simp

theorem disjoint_posExt_negExt (p : W → SignType) :
    Disjoint (posExt p) (negExt p) := by
  rw [Set.disjoint_left]
  intro w hw hw'
  rw [mem_posExt] at hw
  rw [mem_negExt, hw] at hw'
  cases hw'

/-- A proposition is bivalent if it takes no `0` value. -/
def IsBivalent (p : W → SignType) : Prop :=
  ∀ w, p w = 1 ∨ p w = -1

theorem isBivalent_iff_gapExt_eq_empty (p : W → SignType) :
    IsBivalent p ↔ gapExt p = ∅ := by
  simp only [IsBivalent, Set.eq_empty_iff_forall_notMem, mem_gapExt]
  exact forall_congr' fun w => by cases p w <;> simp

theorem isBivalent_iff_forall_ne_zero (p : W → SignType) :
    IsBivalent p ↔ ∀ w, p w ≠ 0 :=
  forall_congr' fun w => by cases p w <;> simp

theorem IsBivalent.ne_zero {p : W → SignType} (h : IsBivalent p) (w : W) : p w ≠ 0 :=
  (isBivalent_iff_forall_ne_zero p).1 h w

/-! ### Presupposition and assertion

A proposition defined where `A` holds and asserting `B` there is the indicator
`{w | A w}.indicator fun w ↦ ofProp (B w)`: the classical value of `B` on `A` and `0` elsewhere.
Its defined region is its `Function.support`, and an indicator of an indicator is the indicator
of the intersection (`Set.indicator_indicator`). -/

section Indicator

variable {s : Set W} {f : W → SignType} {w : W}

@[simp] theorem support_ofProp (B : W → Prop) [DecidablePred B] :
    Function.support (fun w ↦ SignType.ofProp (B w)) = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ SignType.ofProp_ne_zero

@[simp] theorem indicator_apply_eq_one_iff : s.indicator f w = 1 ↔ w ∈ s ∧ f w = 1 := by
  by_cases h : w ∈ s <;> simp [h]

@[simp] theorem indicator_apply_eq_neg_one_iff : s.indicator f w = -1 ↔ w ∈ s ∧ f w = -1 := by
  by_cases h : w ∈ s <;> simp [h]

theorem support_eq_compl_gapExt (p : W → SignType) : Function.support p = (gapExt p)ᶜ := rfl

end Indicator

/-! ### Conditional events

A trivalent proposition is fixed by where it is defined and where it is true, and every such pair
arises: the indicator of `B` on `A` is defined on `A` and true on `A ∩ B`. So trivalent
propositions are the conditional events `B | A` of [de-finetti-1936], conditional assertions of a
two-valued content on a two-valued condition, and two of them coincide exactly when they have the
same condition and agree on it. -/

section ConditionalEvent

/-- Every trivalent proposition is the conditional event of its truth on its definedness. -/
theorem indicator_support_ofProp_eq_one (p : W → SignType) :
    (Function.support p).indicator (fun w ↦ ofProp (p w = 1)) = p := by
  funext w
  by_cases h : p w = 0
  · rw [Set.indicator_of_notMem (by simpa using h), h]
  · rw [Set.indicator_of_mem h]
    cases hp : p w <;> simp_all

/-- Two conditional events coincide exactly when they have the same condition and agree on it. -/
theorem indicator_ofProp_eq_indicator_ofProp_iff {A A' : Set W} {B B' : W → Prop}
    [DecidablePred B] [DecidablePred B'] :
    (A.indicator fun w ↦ ofProp (B w)) = A'.indicator (fun w ↦ ofProp (B' w)) ↔
      A = A' ∧ A ∩ {w | B w} = A' ∩ {w | B' w} := by
  constructor
  · intro h
    have hsupp := congrArg Function.support h
    have hpos := congrArg posExt h
    simp only [Set.support_indicator, support_ofProp, Set.inter_univ] at hsupp
    refine ⟨hsupp, ?_⟩
    simpa [Set.ext_iff, posExt] using hpos
  · rintro ⟨rfl, h⟩
    funext w
    by_cases hw : w ∈ A
    · have := Set.ext_iff.1 h w
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hw, true_and] at this
      simp [hw, this]
    · simp [hw]

end ConditionalEvent

/-! ### Extensions under assertion

Asserting a proposition pointwise, `fun w ↦ ofProp (p w = 1)`, keeps its positive extension and
moves its gap into the negative extension. Conjoining it with a two-valued `R` keeps its gap only
where `R` holds. -/

@[simp] theorem posExt_ofProp_eq_one (p : W → SignType) :
    posExt (fun w ↦ ofProp (p w = 1)) = posExt p := by
  ext w; simp

@[simp] theorem negExt_ofProp_eq_one (p : W → SignType) :
    negExt (fun w ↦ ofProp (p w = 1)) = negExt p ∪ gapExt p := by
  ext w; cases h : p w <;> simp [h]

@[simp] theorem gapExt_ofProp_eq_one (p : W → SignType) :
    gapExt (fun w ↦ ofProp (p w = 1)) = ∅ := by
  ext w; simp

@[simp] theorem posExt_ofProp_inf (R : W → Prop) [DecidablePred R] (p : W → SignType) :
    posExt (fun w ↦ ofProp (R w) ⊓ p w) = {w | R w} ∩ posExt p := by
  ext w; by_cases h : R w <;> simp [h]

@[simp] theorem negExt_ofProp_inf (R : W → Prop) [DecidablePred R] (p : W → SignType) :
    negExt (fun w ↦ ofProp (R w) ⊓ p w) = {w | R w}ᶜ ∪ negExt p := by
  ext w; by_cases h : R w <;> simp [h]

@[simp] theorem gapExt_ofProp_inf (R : W → Prop) [DecidablePred R] (p : W → SignType) :
    gapExt (fun w ↦ ofProp (R w) ⊓ p w) = {w | R w} ∩ gapExt p := by
  ext w; simp [and_comm]

/-- Composing with a function undefined exactly at `0` preserves the gap. -/
theorem gapExt_comp {f : SignType → SignType} (hf : ∀ a, f a = 0 ↔ a = 0) (p : W → SignType) :
    gapExt (f ∘ p) = gapExt p := by
  ext w; simp [hf]

/-- Composing with a function that is never `0` leaves no gap. -/
theorem isBivalent_comp {f : SignType → SignType} (hf : ∀ a, f a ≠ 0) (p : W → SignType) :
    IsBivalent (f ∘ p) :=
  (isBivalent_iff_forall_ne_zero _).2 fun _ ↦ hf _

theorem isBivalent_ofProp_eq_one (p : W → SignType) : IsBivalent fun w ↦ ofProp (p w = 1) :=
  fun w ↦ by by_cases h : p w = 1 <;> simp [h]

/-! ### Quantifiers

Like the binary connectives, the trivalent quantifiers come in rival families that share one
truth rule and differ only in where undefinedness projects, which `forallWith` and
`existsWith` make definitional: a family is fixed by its definedness condition. The Weak
Kleene quantifiers are undefined as soon as any instance is; the Strong Kleene quantifiers
are defined whenever the instances settle the value, the indexed `⊓` and `⊔`; and the
quantifiers of [haug-2014], adopted by [coppock-beaver-2015] and [cooper-2023], are undefined
only when every instance is, so that a quantified presupposition projects existentially.
Restricted to a pair of instances the families are the binary connectives — Weak Kleene
`meetWeak`, Strong Kleene `⊓`, and, for Haug's quantifier, Belnap's skip-undefined
`meetBelnap` (`forallHaug_pair`). Middle Kleene reads its operands left to right, so it has
no order-free quantifier. -/

open Classical in
/-- `forallWith D p` is the universal quantifier undefined unless `D` holds, and otherwise false
exactly when some instance is. All the families share this truth rule
(`forallWith_eq_forallWith_of_defined`). -/
noncomputable def forallWith {ι : Sort*} (D : Prop) (p : ι → SignType) : SignType :=
  if D then if ∃ i, p i = -1 then -1 else 1 else 0

/-- `existsWith D p` is the existential quantifier of the family whose definedness condition
is `D`, the dual of `forallWith`. -/
noncomputable def existsWith {ι : Sort*} (D : Prop) (p : ι → SignType) : SignType :=
  -forallWith D fun i ↦ -p i

section WithFamilies

variable {ι : Sort*} {D D' : Prop} {p : ι → SignType}

theorem forallWith_eq_zero_iff : forallWith D p = 0 ↔ ¬D := by
  unfold forallWith; split_ifs <;> simp_all

theorem forallWith_eq_neg_one_iff : forallWith D p = -1 ↔ D ∧ ∃ i, p i = -1 := by
  unfold forallWith; split_ifs <;> simp_all

theorem forallWith_eq_one_iff : forallWith D p = 1 ↔ D ∧ ∀ i, p i ≠ -1 := by
  unfold forallWith; split_ifs <;> simp_all

theorem existsWith_eq_zero_iff : existsWith D p = 0 ↔ ¬D := by
  simp [existsWith, SignType.neg_eq_zero_iff, forallWith_eq_zero_iff]

theorem existsWith_eq_one_iff : existsWith D p = 1 ↔ D ∧ ∃ i, p i = 1 := by
  simp [existsWith, neg_eq_iff_eq_neg, forallWith_eq_neg_one_iff]

theorem existsWith_eq_neg_one_iff : existsWith D p = -1 ↔ D ∧ ∀ i, p i ≠ 1 := by
  simp [existsWith, neg_eq_iff_eq_neg, forallWith_eq_one_iff]

theorem forallWith_eq_forallWith_of_defined (hD : D) (hD' : D') :
    forallWith D p = forallWith D' p := by
  unfold forallWith
  rw [ite_eq_left hD, ite_eq_left hD']

theorem forallWith_congr (h : D ↔ D') : forallWith D p = forallWith D' p :=
  eq_of_eq_zero_iff_of_eq_one_iff
    (by rw [forallWith_eq_zero_iff, forallWith_eq_zero_iff, h])
    (by rw [forallWith_eq_one_iff, forallWith_eq_one_iff, h])

theorem existsWith_congr (h : D ↔ D') : existsWith D p = existsWith D' p :=
  congrArg Neg.neg (forallWith_congr h)

end WithFamilies

/-- The Weak Kleene universal quantifier is undefined when any instance is, and otherwise
classical. -/
noncomputable def forallWeak {ι : Sort*} (p : ι → SignType) : SignType :=
  forallWith (∀ i, p i ≠ 0) p

/-- The Weak Kleene existential quantifier is the dual of `forallWeak`. -/
noncomputable def existsWeak {ι : Sort*} (p : ι → SignType) : SignType :=
  existsWith (∀ i, p i ≠ 0) p

section WeakQuantifiers

variable {ι : Sort*} {p : ι → SignType}

@[simp] theorem forallWeak_eq_zero_iff : forallWeak p = 0 ↔ ∃ i, p i = 0 := by
  rw [forallWeak, forallWith_eq_zero_iff, not_forall]
  simp

@[simp] theorem forallWeak_eq_one_iff : forallWeak p = 1 ↔ ∀ i, p i = 1 := by
  rw [forallWeak, forallWith_eq_one_iff]
  constructor
  · rintro ⟨hd, hf⟩ i
    cases h : p i
    · exact absurd h (hd i)
    · exact absurd h (hf i)
    · rfl
  · exact fun h => ⟨fun i ↦ by rw [h i]; decide, fun i ↦ by rw [h i]; decide⟩

@[simp] theorem forallWeak_eq_neg_one_iff :
    forallWeak p = -1 ↔ (∀ i, p i ≠ 0) ∧ ∃ i, p i = -1 := by
  rw [forallWeak, forallWith_eq_neg_one_iff]

@[simp] theorem existsWeak_eq_zero_iff : existsWeak p = 0 ↔ ∃ i, p i = 0 := by
  rw [existsWeak, existsWith_eq_zero_iff, not_forall]
  simp

@[simp] theorem existsWeak_eq_one_iff :
    existsWeak p = 1 ↔ (∀ i, p i ≠ 0) ∧ ∃ i, p i = 1 := by
  rw [existsWeak, existsWith_eq_one_iff]

@[simp] theorem existsWeak_eq_neg_one_iff : existsWeak p = -1 ↔ ∀ i, p i = -1 := by
  rw [existsWeak, existsWith_eq_neg_one_iff]
  constructor
  · rintro ⟨hd, hf⟩ i
    cases h : p i
    · exact absurd h (hd i)
    · rfl
    · exact absurd h (hf i)
  · exact fun h => ⟨fun i ↦ by rw [h i]; decide, fun i ↦ by rw [h i]; decide⟩

end WeakQuantifiers

/-- The Strong Kleene universal quantifier is the indexed `⊓`, false when any instance is, true
when all are, and undefined otherwise. -/
noncomputable def forallStrong {ι : Sort*} (p : ι → SignType) : SignType :=
  forallWith ((∃ i, p i = -1) ∨ ∀ i, p i = 1) p

/-- The Strong Kleene existential quantifier is the dual of `forallStrong`, the indexed
`⊔`. -/
noncomputable def existsStrong {ι : Sort*} (p : ι → SignType) : SignType :=
  existsWith ((∃ i, p i = 1) ∨ ∀ i, p i = -1) p

section StrongQuantifiers

variable {ι : Sort*} {p : ι → SignType}

@[simp] theorem forallStrong_eq_neg_one_iff : forallStrong p = -1 ↔ ∃ i, p i = -1 := by
  rw [forallStrong, forallWith_eq_neg_one_iff, and_iff_right_iff_imp]
  exact fun h => .inl h

@[simp] theorem forallStrong_eq_one_iff : forallStrong p = 1 ↔ ∀ i, p i = 1 := by
  rw [forallStrong, forallWith_eq_one_iff]
  constructor
  · rintro ⟨⟨i, hi⟩ | h, hf⟩
    · exact absurd hi (hf i)
    · exact h
  · exact fun h => ⟨.inr h, fun i ↦ by rw [h i]; decide⟩

@[simp] theorem forallStrong_eq_zero_iff :
    forallStrong p = 0 ↔ (∀ i, p i ≠ -1) ∧ ∃ i, p i = 0 := by
  rw [forallStrong, forallWith_eq_zero_iff, not_or, not_exists, not_forall]
  refine and_congr_right fun hne => exists_congr fun i => ?_
  cases h : p i <;> simp_all

@[simp] theorem existsStrong_eq_one_iff : existsStrong p = 1 ↔ ∃ i, p i = 1 := by
  rw [existsStrong, existsWith_eq_one_iff, and_iff_right_iff_imp]
  exact fun h => .inl h

@[simp] theorem existsStrong_eq_neg_one_iff : existsStrong p = -1 ↔ ∀ i, p i = -1 := by
  rw [existsStrong, existsWith_eq_neg_one_iff]
  constructor
  · rintro ⟨⟨i, hi⟩ | h, hf⟩
    · exact absurd hi (hf i)
    · exact h
  · exact fun h => ⟨.inr h, fun i ↦ by rw [h i]; decide⟩

@[simp] theorem existsStrong_eq_zero_iff :
    existsStrong p = 0 ↔ (∀ i, p i ≠ 1) ∧ ∃ i, p i = 0 := by
  rw [existsStrong, existsWith_eq_zero_iff, not_or, not_exists, not_forall]
  refine and_congr_right fun hne => exists_congr fun i => ?_
  cases h : p i <;> simp_all

theorem existsStrong_ne_zero_iff : existsStrong p ≠ 0 ↔ (∃ i, p i = 1) ∨ ∀ i, p i ≠ 0 := by
  rw [ne_eq, existsStrong_eq_zero_iff, not_and_or, not_forall_not, not_exists]

/-- The Strong Kleene quantifiers are dual under Kleene's negation. -/
theorem neg_forallStrong : -forallStrong p = existsStrong fun i ↦ -p i :=
  SignType.eq_of_eq_one_iff_of_eq_neg_one_iff (by simp) (by simp)

end StrongQuantifiers

/-- Haug's universal quantifier skips undefined instances — undefined only when every
instance is, false when some instance is, and true otherwise. -/
noncomputable def forallHaug (p : W → SignType) : SignType :=
  forallWith (∃ w, p w ≠ 0) p

/-- The dual of `forallHaug`. -/
noncomputable def existsHaug (p : W → SignType) : SignType :=
  existsWith (∃ w, p w ≠ 0) p

section HaugQuantifiers

variable {p : W → SignType}

@[simp] theorem forallHaug_eq_zero_iff : forallHaug p = 0 ↔ ∀ w, p w = 0 := by
  rw [forallHaug, forallWith_eq_zero_iff, not_exists]
  simp

@[simp] theorem forallHaug_eq_neg_one_iff : forallHaug p = -1 ↔ ∃ w, p w = -1 := by
  rw [forallHaug, forallWith_eq_neg_one_iff, and_iff_right_iff_imp]
  rintro ⟨w, hw⟩
  exact ⟨w, hw ▸ by decide⟩

@[simp] theorem forallHaug_eq_one_iff :
    forallHaug p = 1 ↔ (∃ w, p w ≠ 0) ∧ ∀ w, p w ≠ -1 := by
  rw [forallHaug, forallWith_eq_one_iff]

@[simp] theorem existsHaug_eq_zero_iff : existsHaug p = 0 ↔ ∀ w, p w = 0 := by
  rw [existsHaug, existsWith_eq_zero_iff, not_exists]
  simp

@[simp] theorem existsHaug_eq_one_iff : existsHaug p = 1 ↔ ∃ w, p w = 1 := by
  rw [existsHaug, existsWith_eq_one_iff, and_iff_right_iff_imp]
  rintro ⟨w, hw⟩
  exact ⟨w, hw ▸ by decide⟩

@[simp] theorem existsHaug_eq_neg_one_iff :
    existsHaug p = -1 ↔ (∃ w, p w ≠ 0) ∧ ∀ w, p w ≠ 1 := by
  rw [existsHaug, existsWith_eq_neg_one_iff]

end HaugQuantifiers

/-! ### Each family restricted to a pair is its binary connective

One lemma carries the correspondence: the gap-policy quantifier at a pair of instances is
the gap-policy connective at the matching policy (`forallWith_pair`), and each family's
pair lemma instantiates it. -/

section Pairs

variable (a b : SignType)

theorem forallWith_pair {D : Prop} [Decidable D] :
    forallWith D (fun i : Bool => bif i then a else b) = meetWith D a b := by
  refine eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_
  · rw [forallWith_eq_zero_iff, meetWith_eq_zero_iff]
  · rw [forallWith_eq_one_iff, meetWith_eq_one_iff, Bool.forall_bool]
    exact and_congr_right fun _ => and_comm

theorem existsWith_pair {D : Prop} [Decidable D] :
    existsWith D (fun i : Bool => bif i then a else b) = joinWith D a b := by
  refine eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_
  · rw [existsWith_eq_zero_iff, joinWith_eq_zero_iff]
  · rw [existsWith_eq_one_iff, joinWith_eq_one_iff, Bool.exists_bool]
    exact and_congr_right fun _ => or_comm

theorem forallWeak_pair : forallWeak (fun i : Bool => bif i then a else b) = meetWeak a b :=
  (forallWith_congr (Bool.forall_bool.trans and_comm)).trans
    ((forallWith_pair a b).trans (meetWeak_eq_meetWith a b).symm)

theorem existsWeak_pair : existsWeak (fun i : Bool => bif i then a else b) = joinWeak a b :=
  (existsWith_congr (Bool.forall_bool.trans and_comm)).trans
    ((existsWith_pair a b).trans (joinWeak_eq_joinWith a b).symm)

theorem forallStrong_pair :
    forallStrong (fun i : Bool => bif i then a else b) = a ⊓ b :=
  (forallWith_congr
      (or_congr (Bool.exists_bool.trans or_comm) (Bool.forall_bool.trans and_comm))).trans
    ((forallWith_pair a b).trans (inf_eq_meetWith a b).symm)

theorem existsStrong_pair :
    existsStrong (fun i : Bool => bif i then a else b) = a ⊔ b :=
  (existsWith_congr
      (or_congr (Bool.exists_bool.trans or_comm) (Bool.forall_bool.trans and_comm))).trans
    ((existsWith_pair a b).trans (sup_eq_joinWith a b).symm)

theorem forallHaug_pair :
    forallHaug (fun i : Bool => bif i then a else b) = meetBelnap a b :=
  (forallWith_congr (Bool.exists_bool.trans or_comm)).trans
    ((forallWith_pair a b).trans (meetBelnap_eq_meetWith a b).symm)

theorem existsHaug_pair :
    existsHaug (fun i : Bool => bif i then a else b) = joinBelnap a b :=
  (existsWith_congr (Bool.exists_bool.trans or_comm)).trans
    ((existsWith_pair a b).trans (joinBelnap_eq_joinWith a b).symm)

end Pairs

theorem existsHaug_presuppose_ne_neg_one (p : W → SignType) :
    existsHaug (fun w => (p w ⊔ 0)) ≠ -1 := by
  simp

/-- Quantifier Projection ([coppock-beaver-2015]'s appendix) lets a presupposition under the
existential project as an existentially quantified presupposition, over bivalent `φ` and
`ψ`. -/
theorem existsHaug_meetWeak_presuppose {φ ψ : W → SignType} (hφ : IsBivalent φ)
    (hψ : IsBivalent ψ) :
    existsHaug (fun w => meetWeak (φ w ⊔ 0) (ψ w)) =
      meetWeak (existsHaug fun w => (φ w ⊔ 0))
        (existsHaug fun w => meetWeak (φ w) (ψ w)) := by
  refine eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_
  · simp only [existsHaug_eq_zero_iff, meetWeak_eq_zero_iff, sup_zero_eq_zero_iff, hφ.ne_zero,
      hψ.ne_zero, or_false]
    exact ⟨Or.inl, fun h => h.elim id fun h w => (h w).elim⟩
  · simp only [existsHaug_eq_one_iff, meetWeak_eq_one_iff, sup_zero_eq_one_iff]
    exact ⟨fun ⟨w, h⟩ => ⟨⟨w, h.1⟩, w, h⟩, fun h => h.2⟩

end Trivalent
