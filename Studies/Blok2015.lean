module

public import Linglib.Data.Examples.Blok2015
public import Linglib.Data.Examples.Readers
public import Linglib.Fragments.Dutch.NumeralModifiers
public import Linglib.Fragments.Dutch.PolarityItems
public import Linglib.Semantics.PolarityItem.Licensing
public import Linglib.Semantics.Quantification.Counting
public import Studies.CoppockBrochhagen2013
public import Mathlib.Order.UpperLower.Basic
public import Linglib.Data.Examples.Languages

/-!
# Blok (2015): The semantics and pragmatics of directional numeral modifiers

This file formalizes Blok's account of numeral modifiers built on directional prepositions, such
as *up to*, in a semantics where a sentence raises a set of possibilities. *Up to n* raises *at
least m* for each $m$ from the lowest positive point $s$ of the scale to $n$, so it asserts only
*at least s*, and [exhaustifying its possibilities against the question of how
many](##Blok2015.sUnion_exh_upTo) adds the upper bound. A modifier of Nouwen's Class B must raise
more than one possibility, which [fails at the bottom of the scale](##Blok2015.nontrivial_upTo)
and which [the Maxim of Interactive Sincerity cannot
enforce](##Blok2015.forall_interactiveSincerity_upTo_iff). Asserting a lower bound, *up to* is
upward entailing and, unlike *at most*, [licenses no negative polarity
item](##Blok2015.admits_hoeven). [The paper's judgments follow](##Blok2015.judgment_rows).

## Implementation notes

* Worlds are counts, one for each number, as in the paper's simplified model, and a proposition
  is a `Set (Set ℕ)`: the library's `Question` is closed downward and would merge the nested
  possibilities of *up to*. The choice functions of the entries are dropped, since applying them
  pointwise yields the set they choose from (`CoppockBrochhagen2013.range_choice_apply`).
* *At most* is Coppock and Brochhagen's entry on the one-sided answers to the question of how
  many, ranked by their lower bounds.
* The account covers the Fragment's Class B modifiers that set an upper bound, checked against
  their Fragment readings, and a modifier is directional when its entry is built on a directional
  preposition. A row's number is counted in the unit of its scale: eggs one by one, cake by the
  slice, an absence by the day.
* The scope of a modified numeral is the cardinal quantifier of what the sentence asserts, as a
  licenser indexed by its finite restrictor, as the library's licensing contexts are.

## Errata

* (45) states the range requirement as $s \ne n$, which admits $s > n$, where *up to n* raises
  no possibility at all; the discussion of (23b) counts that case as a violation too, and the
  requirement is $s < n$.

## TODO

* The evaluative adverbs, which target what a sentence asserts, and the plurals and modals that
  supply a range of values are not formalized.
* The examples in languages other than English and Dutch are not recorded, their modifiers having
  no Fragment entries.

## References

* [D. Blok, *The semantics and pragmatics of directional numeral modifiers* (2015)][blok-2015]
* [E. Coppock and T. Brochhagen, *Raising and resolving issues with scalar modifiers*
  (2013)][coppock-brochhagen-2013]
* [B. Schwarz, B. Buccola and M. Hamilton, *Two types of class B numeral modifiers: A reply to
  Nouwen 2010* (2012)][schwarz-buccola-hamilton-2012]
* [T. van der Wouden, *Negative Contexts: Collocation, Polarity and Multiple Negation*
  (1997)][vanderwouden-1997]
-/

@[expose] public section

namespace Blok2015

open Set Quantifier PolarityItem NaturalLogic Inquisitive.Unrestricted CoppockBrochhagen2013

variable {s n m : ℕ}

/-! ### The two denotations -/

/-- *Up to `n`*, on a scale whose lowest positive point is `s`, raises the possibility that at
least `m` hold for each `m` from `s` to `n`. -/
def upTo (s n : ℕ) : Set (Set ℕ) := Ici '' Icc s n

/-- The question of how many, with a possibility for each lower bound. -/
def howMany : Set (Set ℕ) := range Ici

/-- *At most `n`* is [coppock-brochhagen-2013]'s entry on the question of how many, with the
answers ranked by their lower bounds. -/
def atMost (n : ℕ) : Set (Set ℕ) :=
  atMostInq (ranking (oneSided id)) (range (oneSided id)) (oneSided id n)

-- (43c)
theorem atMost_eq (n : ℕ) : atMost n = (Icc · n) '' Iic n :=
  atMostInq_oneSided_id n

theorem mem_sUnion_upTo : m ∈ ⋃₀ upTo s n ↔ s ≤ m ∧ s ≤ n := by
  simp only [upTo, sUnion_image, mem_iUnion, mem_Icc, mem_Ici, exists_prop]
  exact ⟨fun ⟨k, ⟨hsk, hkn⟩, hkm⟩ ↦ ⟨hsk.trans hkm, hsk.trans hkn⟩,
    fun ⟨hsm, hsn⟩ ↦ ⟨s, ⟨le_rfl, hsn⟩, hsm⟩⟩

-- (49)
theorem sUnion_upTo (h : s ≤ n) : ⋃₀ upTo s n = Ici s := by
  ext; rw [mem_sUnion_upTo, mem_Ici, and_iff_left h]

theorem sUnion_atMost : ⋃₀ atMost n = Iic n := by
  ext k
  simp only [atMost_eq, sUnion_image, mem_iUnion, mem_Iic, mem_Icc, exists_prop]
  exact ⟨fun ⟨m, _, hk⟩ ↦ hk.2, fun hk ↦ ⟨0, Nat.zero_le n, Nat.zero_le k, hk⟩⟩

theorem isUpperSet_sUnion_upTo : IsUpperSet (⋃₀ upTo s n) := fun _ _ hab h ↦
  mem_sUnion_upTo.2 ⟨(mem_sUnion_upTo.1 h).1.trans hab, (mem_sUnion_upTo.1 h).2⟩

/-! ### The implicated upper bound -/

private theorem exh_howMany_Ici : Exhaustification.exh howMany (Ici m) = {m} := by
  ext k
  simp only [howMany, Exhaustification.mem_exh_range_iff, mem_Ici, Ici_subset_Ici,
    mem_singleton_iff]
  exact ⟨fun ⟨hk, h⟩ ↦ le_antisymm (h k le_rfl) hk, by rintro rfl; exact ⟨le_rfl, fun _ ↦ id⟩⟩

-- (50), (51)
theorem exh_upTo_howMany :
    Exhaustification.exh howMany '' upTo s n = (fun m ↦ {m}) '' Icc s n := by
  simp only [upTo, image_image, exh_howMany_Ici]

/-- *Up to n* asserts only its lower bound, and exhaustifying its possibilities against the
question of how many adds the upper bound `n` (51). -/
theorem sUnion_exh_upTo : ⋃₀ (Exhaustification.exh howMany '' upTo s n) = Icc s n := by
  rw [exh_upTo_howMany, sUnion_image, biUnion_of_singleton]

/-! ### The range requirement -/

/-- *Up to n* raises more than one possibility exactly when `n` lies above the lowest point `s`
of the scale, so it fails the range requirement at the bottom of the scale, whatever the grain of
the scale (23b), (25b), (27b). The condition is `s < n`, not the `s ≠ n` of (45). -/
theorem nontrivial_upTo : (upTo s n).Nontrivial ↔ s < n := by
  rw [upTo, image_nontrivial Ici_injective, ← not_subsingleton_iff, subsingleton_Icc_iff, not_le]

-- (29)
theorem nontrivial_atMost : (atMost n).Nontrivial ↔ 0 < n := by
  rw [atMost_eq]
  refine ⟨fun h ↦ Nat.pos_of_ne_zero ?_, fun h ↦ ?_⟩
  · rintro rfl
    exact h.not_subsingleton (Subsingleton.image (fun a ha b hb ↦
      (Nat.le_zero.1 ha).trans (Nat.le_zero.1 hb).symm) _)
  · refine ⟨Icc 0 n, mem_image_of_mem _ (mem_Iic.2 n.zero_le),
      Icc n n, mem_image_of_mem _ (mem_Iic.2 le_rfl), fun he ↦ h.not_ge ?_⟩
    exact (he ▸ (⟨le_rfl, n.zero_le⟩ : 0 ∈ Icc 0 n) : 0 ∈ Icc n n).1

/-- [coppock-brochhagen-2013]'s Maxim of Interactive Sincerity holds of *up to n* whatever the
speaker knows exactly when *up to n* fails the range requirement: the maxim is silent on (52),
which the range requirement rules out. -/
theorem forall_interactiveSincerity_upTo_iff : (∀ k, InteractiveSincerity (upTo s n) k) ↔ n ≤ s :=
  by rw [CoppockBrochhagen2013.forall_interactiveSincerity_iff, nontrivial_upTo, not_lt]

-- (53a)
theorem forall_interactiveSincerity_atMost_iff :
    (∀ k, InteractiveSincerity (atMost n) k) ↔ n = 0 := by
  rw [CoppockBrochhagen2013.forall_interactiveSincerity_iff, nontrivial_atMost, not_lt,
    Nat.le_zero]

/-! ### Monotonicity -/

/-- The licenser a sentence raising `P` places over its scope, indexed by its finite restrictor:
the cardinal quantifier of what the sentence asserts. -/
def scopeLicenser (P : Set (Set ℕ)) : Licenser :=
  .classical ⟨FinitePredicate, fun p ↦ Set p.ι, fun _ ↦ Prop,
    fun p ↦ (NumberTree.cardinal (⋃₀ P)).toDet p.A⟩

section Monotonicity

variable {ι : Type} [Finite ι] {A : Set ι}

omit [Finite ι] in
-- (31)
theorem toDet_sUnion_upTo (h : s ≤ n) :
    ((NumberTree.cardinal (⋃₀ upTo s n)).toDet : Det ι) = Det.atLeast s := by
  rw [sUnion_upTo h]; rfl

omit [Finite ι] in
-- (30)
theorem toDet_sUnion_atMost :
    ((NumberTree.cardinal (⋃₀ atMost n)).toDet : Det ι) = Det.atMost n := by
  rw [sUnion_atMost]; rfl

theorem scopeMonotone_upTo : ((NumberTree.cardinal (⋃₀ upTo s n)).toDet : Det ι).ScopeMonotone :=
  NumberTree.ScopeMonotone.toDet fun _ _ h ↦ isUpperSet_sUnion_upTo (Nat.le_succ _) h

end Monotonicity

theorem not_carries_scopeLicenser_upTo (r : Negation.Strength) :
    ¬ (scopeLicenser (upTo s n)).Carries r := fun h ↦
  h.weak.2 fun p ↦ scopeMonotone_upTo p.A

theorem carries_scopeLicenser_atMost_iff {r : Negation.Strength} :
    (scopeLicenser (atMost n)).Carries r ↔ r = .weak := by
  rw [scopeLicenser, Licenser.carries_classical_iff]
  constructor
  · rintro ⟨h, -⟩
    by_contra hr
    have hf := (Signature.holdsFor_antiAdd_iff.1 ((h.toSignature_of_le (s := .antiAdditive)
      (by revert hr; cases r <;> decide)) ⟨⟨Unit, ∅⟩⟩)).2
    exact (eq_iff_iff.1 hf).1 (by simp [NumberTree.toDet_apply, sUnion_atMost])
  · rintro rfl
    refine ⟨fun p ↦ Signature.holdsFor_anti_iff.2 ?_, fun hm ↦ ?_⟩
    · show Antitone ((NumberTree.cardinal (⋃₀ atMost n)).toDet p.A)
      rw [toDet_sUnion_atMost]; exact Det.scopeAntitone_atMost n p.A
    · have := hm ⟨⟨Fin (n + 1), univ⟩⟩ (empty_subset (univ : Set (Fin (n + 1))))
        (by simp [toDet_sUnion_atMost, Det.atMost_apply])
      simp [toDet_sUnion_atMost, Det.atMost_apply] at this

private theorem admits_hoeven_iff {F : OperatorFamily} :
    (Licenser.classical F).Admits Dutch.PolarityItems.hoeven ↔
      (Licenser.classical F).Carries .weak := by
  rw [Licenser.admits_iff_licenses rfl (Or.inl rfl)]
  simp [Licenser.Licenses, Dutch.PolarityItems.hoeven, Licenser.LicensesFreeChoice,
    Licenser.LicensesByRelevance]

/-! ### The modifiers -/

/-- The possibilities a modifier that sets an upper bound raises with the number `n`, on a scale
whose lowest positive point is `s`: those of *up to* for a directional modifier and those of *at
most* for any other. -/
def raised (w : Numerals.NumeralModifier) (s n : ℕ) : Set (Set ℕ) :=
  if w.kind = some .directional then upTo s n else atMost n

/-- The modifiers the account covers in the language of a row: the Fragment's Class B modifiers
that set an upper bound. -/
def upperBounded (l : Glottocode) : List Numerals.NumeralModifier :=
  (List.lookup l [(.english, [English.NumeralModifiers.atMost,
      English.NumeralModifiers.maximally, English.NumeralModifiers.upTo]),
    (.dutch, [Dutch.NumeralModifiers.maximaal, Dutch.NumeralModifiers.tot])]).getD []

open scoped Denotes in
theorem mem_upperBounded {l : Glottocode} {w : Numerals.NumeralModifier}
    (h : w ∈ upperBounded l) :
    ⟦w⟧ = {Degree.Comparison.le.modifier} ∧ w.modifierClass = some .classB := by
  unfold upperBounded at h
  simp only [List.lookup] at h
  split at h
  · simp only [Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  split at h
  · simp only [Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact ⟨rfl, rfl⟩
  simp at h

/-- Read as a quantifier, *maximaal n* asserts the downward entailing *at most n* and admits the
weak negative polarity item *hoeven*, while *tot n* asserts the upward entailing *at least s* and
does not admit it (34). -/
theorem admits_hoeven :
    (scopeLicenser (raised Dutch.NumeralModifiers.maximaal s n)).Admits
        Dutch.PolarityItems.hoeven ∧
      ¬ (scopeLicenser (raised Dutch.NumeralModifiers.tot s n)).Admits
        Dutch.PolarityItems.hoeven :=
  ⟨admits_hoeven_iff.2 (carries_scopeLicenser_atMost_iff.2 rfl),
    fun h ↦ not_carries_scopeLicenser_upTo .weak (admits_hoeven_iff.1 h)⟩

/-! ### The judgments -/

/-- The diagnostics of the paper's examples: a continuation *if any*, a contrast with *no-one*,
a continuation that cancels or reinforces the upper bound, a bare sentence, a continuation naming
the precise number `v`, and a negative polarity item in the scope that needs the strength `r`. -/
inductive Diagnostic where
  | ifAny | butNone | upperBound | range
  | precise (v : ℕ)
  | npi (r : Negation.Strength)
  deriving DecidableEq, Repr

/-- What the account predicts felicitous of a sentence raising `P`. *If any* needs asserted
content compatible with none and the contrast with *no-one* content that excludes none.
Cancelling or reinforcing the upper bound needs a bound that is implicated and not asserted: the
content exhaustified against the question of how many is bounded above, and the asserted content
is not. A bare sentence needs more than one possibility, a precise continuation sincerity in a
speaker who knows the number, and a negative polarity item a scope that carries the strength it
needs. -/
def Felicitous (P : Set (Set ℕ)) : Diagnostic → Prop
  | .ifAny => 0 ∈ ⋃₀ P
  | .butNone => 0 ∉ ⋃₀ P
  | .upperBound => ¬ BddAbove (⋃₀ P) ∧ BddAbove (⋃₀ (Exhaustification.exh howMany '' P))
  | .range => P.Nontrivial
  | .precise v => InteractiveSincerity P {v}
  | .npi r => (scopeLicenser P).Carries r

theorem bddAbove_sUnion_upTo_iff : BddAbove (⋃₀ upTo s n) ↔ n < s := by
  refine ⟨fun ⟨b, hb⟩ ↦ not_le.1 fun h ↦ ?_,
    fun h ↦ ⟨0, fun _ hk ↦ absurd (mem_sUnion_upTo.1 hk).2 (not_le.2 h)⟩⟩
  have hs : s ≤ b := hb (mem_sUnion_upTo.2 ⟨le_rfl, h⟩)
  exact (Nat.lt_succ_self b).not_ge (hb (mem_sUnion_upTo.2 ⟨hs.trans b.le_succ, h⟩))

instance : ∀ t, Decidable (Felicitous (upTo s n) t)
  | .ifAny => decidable_of_iff (s = 0 ∧ s ≤ n) (by simp only [Felicitous, mem_sUnion_upTo]; omega)
  | .butNone => decidable_of_iff (¬ (s = 0 ∧ s ≤ n))
      (by simp only [Felicitous, mem_sUnion_upTo]; omega)
  | .upperBound => decidable_of_iff (s ≤ n) (by
      rw [Felicitous, bddAbove_sUnion_upTo_iff, sUnion_exh_upTo, not_lt, and_iff_left bddAbove_Icc])
  | .range => decidable_of_iff (s < n) nontrivial_upTo.symm
  | .precise v => decidable_of_iff (n ≤ s)
      (by rw [Felicitous, interactiveSincerity_singleton_iff, nontrivial_upTo, not_lt])
  | .npi r => isFalse (not_carries_scopeLicenser_upTo r)

instance : ∀ t, Decidable (Felicitous (atMost n) t)
  | .ifAny => isTrue (by simp [Felicitous, sUnion_atMost])
  | .butNone => isFalse (by simp [Felicitous, sUnion_atMost])
  | .upperBound => isFalse fun h ↦ h.1 (sUnion_atMost ▸ bddAbove_Iic)
  | .range => decidable_of_iff (0 < n) nontrivial_atMost.symm
  | .precise v => decidable_of_iff (n = 0)
      (by rw [Felicitous, interactiveSincerity_singleton_iff, nontrivial_atMost]; omega)
  | .npi _ => decidable_of_iff _ carries_scopeLicenser_atMost_iff.symm

instance (w : Numerals.NumeralModifier) (t : Diagnostic) :
    Decidable (Felicitous (raised w s n) t) :=
  if h : w.kind = some .directional then
    decidable_of_iff (Felicitous (upTo s n) t) (by simp only [raised, h, ↓reduceIte])
  else decidable_of_iff (Felicitous (atMost n) t) (by simp only [raised, h, ↓reduceIte])

/-- The modifier a row names, among those the account covers in its language. -/
def modifier? (e : Datum) : Option Numerals.NumeralModifier :=
  (e.feature? "modifier").bind fun f ↦ (upperBounded e.language).find? (·.form = f)

/-- The diagnostic a row names; a negative polarity item needs the strength its Fragment entry
records. -/
def diagnostic? (e : Datum) : Option Diagnostic :=
  match e.feature? "test" with
  | some "ifAny" => some .ifAny
  | some "butNone" => some .butNone
  | some "evenMore" | some "noMore" => some .upperBound
  | some "range" => some .range
  | some "precise" => (e.nat? "precise").map .precise
  | some "npi" =>
      ((e.parse? "npi" [("hoeven", Dutch.PolarityItems.hoeven)]).bind (·.licensor)).map .npi
  | _ => none

/-- Every row is felicitous exactly when the account predicts it, for the modifier it names, read
off the Fragment, with its number on a scale whose lowest positive point the row gives. -/
theorem judgment_rows :
    ∀ e ∈ Examples.all, ∃ w ∈ modifier? e, ∃ t ∈ diagnostic? e, ∃ s ∈ e.nat? "scaleBottom",
      ∃ n ∈ e.nat? "numeral", (e.JudgedFelicitous ↔ Felicitous (raised w s n) t) := by
  decide +kernel

end Blok2015
