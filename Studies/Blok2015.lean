module

public import Linglib.Data.Examples.Blok2015
public import Linglib.Data.Examples.Readers
public import Linglib.Fragments.Dutch.NumeralModifiers
public import Linglib.Fragments.Dutch.PolarityItems
public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Semantics.Quantification.Counting
public import Studies.CoppockBrochhagen2013
public import Mathlib.Order.UpperLower.Basic

/-!
# Blok (2015): The semantics and pragmatics of directional numeral modifiers

This file formalizes Blok's account of numeral modifiers built on directional prepositions, such
as *up to*, in a semantics where a sentence raises a set of possibilities. *Up to n* raises *at
least m* for each $m$ from the lowest positive point $s$ of the scale to $n$, so it asserts only
*at least s*, and [exhaustifying its possibilities against the question of how
many](##Blok2015.sUnion_exh_upTo) adds the upper bound. A modifier of Nouwen's Class B must raise
more than one possibility, which [fails at the bottom of the scale](##Blok2015.nontrivial_upTo)
and which [the Maxim of Interactive Sincerity cannot
enforce](##Blok2015.interactiveSincerity_bottom). Asserting a lower bound, *up to* is upward
entailing and, unlike *at most*, [licenses no negative polarity
item](##Blok2015.admits_hoeven). [The paper's judgments follow](##Blok2015.judgment_rows).

## Implementation notes

* Worlds are counts, one for each number, as in the paper's simplified model, and a proposition
  is a `Set (Set ℕ)`: the library's `Question` is closed downward and would merge the nested
  possibilities of *up to*. The choice functions of the entries are dropped, since applying them
  pointwise yields the set they choose from (`CoppockBrochhagen2013.range_choice_apply`).
* *At most* is Coppock and Brochhagen's entry on the one-sided answers to the question of how
  many, ranked by their lower bounds.
* A modifier is directional when its Fragment entry is built on a directional preposition. A
  row's number is counted in the unit of its scale: eggs one by one, cake by the slice, an
  absence by the day.
* The scope of a modified numeral is the cardinal quantifier of what the sentence asserts, over a
  finite domain with more individuals than the numeral names, so that *at most n* is not
  trivially true.

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

private theorem Ici_diff_sUnion_howMany : Ici m \ ⋃₀ {q ∈ howMany | ¬ Ici m ⊆ q} = {m} := by
  ext k
  refine ⟨fun ⟨hk, hnot⟩ ↦ ?_, ?_⟩
  · by_contra hne
    have hlt : m < k := lt_of_le_of_ne hk (Ne.symm hne)
    exact hnot ⟨Ici k, ⟨⟨k, rfl⟩, fun h ↦ (Ici_subset_Ici.1 h).not_gt hlt⟩, mem_Ici.2 le_rfl⟩
  · rintro rfl
    refine ⟨mem_Ici.2 le_rfl, ?_⟩
    rintro ⟨_, ⟨⟨j, rfl⟩, hj⟩, hkj⟩
    exact hj (Ici_subset_Ici.2 hkj)

-- (50), (51)
theorem exh_upTo_howMany : exh (upTo s n) howMany = (fun m ↦ {m}) '' Icc s n := by
  simp only [exh, upTo, image_image, Ici_diff_sUnion_howMany]

/-- *Up to n* asserts only its lower bound, and exhaustifying its possibilities against the
question of how many adds the upper bound `n` (51). -/
theorem sUnion_exh_upTo : ⋃₀ exh (upTo s n) howMany = Icc s n := by
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
  have hinj : InjOn (Icc · n) (Iic n) := fun a ha b hb (h : Icc a n = Icc b n) ↦
    le_antisymm (h ▸ (⟨le_rfl, hb⟩ : b ∈ Icc b n) : b ∈ Icc a n).1
      (h ▸ (⟨le_rfl, ha⟩ : a ∈ Icc a n) : a ∈ Icc b n).1
  have hIic : (Iic n).Nontrivial ↔ 0 < n := by
    rw [← not_subsingleton_iff, show Iic n = Icc 0 n by ext; simp, subsingleton_Icc_iff, not_le]
  exact ⟨fun h ↦ hIic.1 (nontrivial_of_image _ _ h), fun h ↦ (hIic.2 h).image_of_injOn hinj⟩

/-- *Up to one* on the whole numbers and *at most zero* each raise a single possibility, so they
satisfy [coppock-brochhagen-2013]'s Maxim of Interactive Sincerity whatever the speaker knows;
the maxim cannot rule them out, and the range requirement does (52), (53a). -/
theorem interactiveSincerity_bottom (k : Set ℕ) :
    (InteractiveSincerity (upTo 1 1) k ∧ ¬ (upTo 1 1).Nontrivial) ∧
      InteractiveSincerity (atMost 0) k ∧ ¬ (atMost 0).Nontrivial := by
  have h₁ : ¬ (upTo 1 1).Nontrivial := by simp [nontrivial_upTo]
  have h₀ : ¬ (atMost 0).Nontrivial := by simp [nontrivial_atMost]
  exact ⟨⟨fun h ↦ absurd h h₁, h₁⟩, fun h ↦ absurd h h₀, h₀⟩

/-! ### Monotonicity -/

section Monotonicity

variable {ι : Type} [Finite ι] {A : Set ι}

/-- The licenser over the scope of a sentence raising `P` with the restrictor `A`: the cardinal
quantifier of what the sentence asserts. -/
def scopeLicenser (P : Set (Set ℕ)) (A : Set ι) : Licenser :=
  .ofOperator ((NumberTree.cardinal (⋃₀ P)).toDet A)

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

theorem not_carries_scopeLicenser_upTo (r : Negation.Strength) :
    ¬ (scopeLicenser (upTo s n) A).Carries r := fun h ↦
  (Licenser.carries_ofOperator_iff.1 h.weak).2 (scopeMonotone_upTo A)

theorem carries_scopeLicenser_atMost (hA : n < A.ncard) :
    (scopeLicenser (atMost n) A).Carries .weak := by
  rw [scopeLicenser, Licenser.carries_ofOperator_iff, toDet_sUnion_atMost]
  refine ⟨Signature.holdsFor_anti_iff.2 (Det.scopeAntitone_atMost n A), fun hm ↦ hA.not_ge ?_⟩
  simpa [Det.atMost_apply] using hm (empty_subset A) (by simp [Det.atMost_apply])

private theorem admits_hoeven_iff {σ : Type} [Lattice σ] [BoundedOrder σ] {f : σ → Prop} :
    (Licenser.ofOperator f).Admits Dutch.PolarityItems.hoeven ↔
      (Licenser.ofOperator f).Carries .weak := by
  rw [Licenser.admits_iff_licenses rfl (Or.inl rfl)]
  simp [Licenser.Licenses, Dutch.PolarityItems.hoeven, Licenser.ofOperator,
    Licenser.LicensesFreeChoice, Licenser.LicensesByRelevance]

end Monotonicity

/-! ### The modifiers -/

/-- The possibilities a modifier that sets an upper bound raises with the number `n`, on a scale
whose lowest positive point is `s`: those of *up to* for a directional modifier and those of *at
most* for any other. -/
def raised (w : Numerals.NumeralModifier) (s n : ℕ) : Set (Set ℕ) :=
  if w.kind = some .directional then upTo s n else atMost n

/-- Read as a quantifier over more individuals than its numeral names, *maximaal n* asserts the
downward entailing *at most n* and admits the weak negative polarity item *hoeven*, while *tot n*
asserts the upward entailing *at least s* and does not admit it (34). -/
theorem admits_hoeven {ι : Type} [Finite ι] {A : Set ι} (hA : n < A.ncard) :
    (scopeLicenser (raised Dutch.NumeralModifiers.maximaal s n) A).Admits
        Dutch.PolarityItems.hoeven ∧
      ¬ (scopeLicenser (raised Dutch.NumeralModifiers.tot s n) A).Admits
        Dutch.PolarityItems.hoeven :=
  ⟨admits_hoeven_iff.2 (carries_scopeLicenser_atMost hA),
    fun h ↦ not_carries_scopeLicenser_upTo .weak (admits_hoeven_iff.1 h)⟩

/-! ### The judgments -/

/-- The diagnostics of the paper's examples: a continuation *if any*, a contrast with *no-one*,
a continuation that cancels or reinforces the upper bound, a bare sentence, a continuation naming
the precise number `v`, and a weak negative polarity item in the scope. -/
inductive Diagnostic where
  | ifAny | butNone | upperBound | range
  | precise (v : ℕ)
  | npi
  deriving DecidableEq, Repr

/-- What the account predicts felicitous with the number `n`. *If any* needs content compatible
with none and the contrast with *no-one* content that excludes none; cancelling or reinforcing
the upper bound needs content that does not settle it. A bare sentence needs more than one
possibility, a precise continuation sincerity in a speaker who knows the number, and a weak
negative polarity item a scope that is downward and not upward entailing over every domain with
more individuals than `n`. -/
def Felicitous (P : Set (Set ℕ)) (n : ℕ) : Diagnostic → Prop
  | .ifAny => 0 ∈ ⋃₀ P
  | .butNone => 0 ∉ ⋃₀ P
  | .upperBound => n + 1 ∈ ⋃₀ P
  | .range => P.Nontrivial
  | .precise v => InteractiveSincerity P {v}
  | .npi => ∀ (ι : Type) [Finite ι] (A : Set ι), n < A.ncard → (scopeLicenser P A).Carries .weak

theorem not_felicitous_upTo_npi : ¬ Felicitous (upTo s n) n .npi := fun h ↦
  not_carries_scopeLicenser_upTo .weak (h (Fin (n + 1)) univ (by simp [ncard_univ]))

instance : ∀ t, Decidable (Felicitous (upTo s n) n t)
  | .ifAny => decidable_of_iff (s = 0 ∧ s ≤ n) (by simp only [Felicitous, mem_sUnion_upTo]; omega)
  | .butNone => decidable_of_iff (¬ (s = 0 ∧ s ≤ n))
      (by simp only [Felicitous, mem_sUnion_upTo]; omega)
  | .upperBound => decidable_of_iff (s ≤ n) (by simp only [Felicitous, mem_sUnion_upTo]; omega)
  | .range => decidable_of_iff (s < n) nontrivial_upTo.symm
  | .precise v => decidable_of_iff (n ≤ s)
      (by rw [Felicitous, interactiveSincerity_singleton_iff, nontrivial_upTo, not_lt])
  | .npi => isFalse not_felicitous_upTo_npi

instance : ∀ t, Decidable (Felicitous (atMost n) n t)
  | .ifAny => isTrue (by simp [Felicitous, sUnion_atMost])
  | .butNone => isFalse (by simp [Felicitous, sUnion_atMost])
  | .upperBound => isFalse (by simp [Felicitous, sUnion_atMost])
  | .range => decidable_of_iff (0 < n) nontrivial_atMost.symm
  | .precise v => decidable_of_iff (n = 0)
      (by rw [Felicitous, interactiveSincerity_singleton_iff, nontrivial_atMost]; omega)
  | .npi => isTrue fun _ _ _ hA ↦ carries_scopeLicenser_atMost hA

instance (w : Numerals.NumeralModifier) (t : Diagnostic) :
    Decidable (Felicitous (raised w s n) n t) :=
  if h : w.kind = some .directional then
    decidable_of_iff (Felicitous (upTo s n) n t) (by simp only [raised, h, ↓reduceIte])
  else decidable_of_iff (Felicitous (atMost n) n t) (by simp only [raised, h, ↓reduceIte])

/-- The Fragment's numeral modifiers in the language of a row. -/
def inventory : Glottocode → List Numerals.NumeralModifier
  | "stan1293" => English.NumeralModifiers.inventory
  | "dutc1256" => Dutch.NumeralModifiers.inventory
  | _ => []

/-- The modifier a row names, looked up in the Fragment of its language. -/
def modifier? (e : Datum) : Option Numerals.NumeralModifier :=
  (e.feature? "modifier").bind fun f ↦ (inventory e.language).find? (·.form = f)

/-- The diagnostic a row names. A negative polarity item is read when its Fragment entry needs
weak strength. -/
def diagnostic? (e : Datum) : Option Diagnostic :=
  match e.feature? "test" with
  | some "ifAny" => some .ifAny
  | some "butNone" => some .butNone
  | some "evenMore" | some "noMore" => some .upperBound
  | some "range" => some .range
  | some "precise" => (e.nat? "precise").map .precise
  | some "npi" => (e.parse? "npi" [("hoeven", Dutch.PolarityItems.hoeven)]).bind fun i ↦
      if i.licensor = some .weak then some .npi else none
  | _ => none

/-- Every row is felicitous exactly when the account predicts it, for the modifier it names, read
off the Fragment, with its number on a scale whose lowest positive point the row gives. -/
theorem judgment_rows :
    ∀ e ∈ Examples.all, ∃ w ∈ modifier? e, ∃ t ∈ diagnostic? e, ∃ s ∈ e.nat? "scaleBottom",
      ∃ n ∈ e.nat? "numeral", (e.JudgedFelicitous ↔ Felicitous (raised w s n) n t) := by
  decide +kernel

end Blok2015
