module

public import Linglib.Data.Examples.Blok2015
public import Studies.CoppockBrochhagen2013
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Data.Set.Lattice.Image

/-!
# Blok (2015): The semantics and pragmatics of directional numeral modifiers

This file formalizes the paper's account of directional numeral modifiers, the prepositions of
direction used to modify a numeral, such as *up to*. They differ from the other modifiers that
set an upper bound, such as *at most*: their lower bound cannot be cancelled and their upper
bound can, they are odd with the lowest number of a scale, and they do not license negative
polarity items. The paper derives the differences from two claims. A directional modifier
asserts a lower bound and only implicates its upper bound, and every Class B modifier needs a
range of values to quantify over.

The implementation follows the paper's, in unrestricted inquisitive semantics. A sentence
denotes a set of possibilities. *Up to n* raises the possibilities that at least `m` hold, for
`m` from the bottom `s` of the scale to `n`, so its informational content is that at least `s`
hold (`sUnion_upTo`), with no upper bound. Exhaustifying each possibility against the question
of how many leaves the possibilities of exactly `m`, and the upper bound `n` is an implicature
(`sUnion_exh_upTo`). *At most n*, on Coppock and Brochhagen's analysis, raises the
possibilities between `m` and `n`, so its content is the upper bound and is compatible with
zero (`sUnion_atMost`). The range requirement is that the sentence raise more than one
possibility, which fails for *up to* at the bottom of the scale and for *at most 0*
(`nontrivial_upTo`, `nontrivial_atMost`). The paper's judgments on the two kinds of modifier
are checked against these predictions (`judgment_rows`).

## Implementation notes

Worlds are counts, as in the paper's simplified model with one world for each number. A
proposition is a `Set (Set ℕ)` and not the library's `Question`, which is downward closed and
identifies a proposition with its maximal possibilities, while the possibilities of *up to*
are nested. *At most* is Coppock and Brochhagen's entry on the question of how many with
one-sided answers (`atMost_eq`), and exhaustification is theirs too. The bottom of the scale is
`1` in the rows, the whole numbers.

## References

* [D. Blok, *The semantics and pragmatics of directional numeral modifiers* (2015)][blok-2015]
* [E. Coppock and T. Brochhagen, *Raising and resolving issues with scalar modifiers*
  (2013)][coppock-brochhagen-2013]
* [B. Schwarz, B. Buccola and M. Hamilton, *Two types of class B numeral modifiers: A reply to
  Nouwen 2010* (2012)][schwarz-buccola-hamilton-2012]
-/

@[expose] public section

namespace Blok2015

open Set

variable {s n m : ℕ}

/-! ### The two denotations -/

/-- (45): *up to `n`* on a scale with bottom `s` raises the possibilities that at least `m`
hold, for each `m` from `s` to `n`. -/
def upTo (s n : ℕ) : Set (Set ℕ) := Ici '' Icc s n

open CoppockBrochhagen2013 (atMostInq ranking oneSided) in
/-- *At most `n`* (43c) is [coppock-brochhagen-2013]'s entry on the question of how many, with
an answer `Ici m` for each lower bound `m`. -/
def atMost (n : ℕ) : Set (Set ℕ) :=
  atMostInq (ranking (oneSided id)) (range (oneSided id)) (oneSided id n)

theorem atMost_eq (n : ℕ) : atMost n = (Icc · n) '' Iic n :=
  CoppockBrochhagen2013.atMostInq_oneSided_id n

theorem sUnion_upTo (h : s ≤ n) : ⋃₀ upTo s n = Ici s := by
  ext k
  simp only [upTo, sUnion_image, mem_iUnion, mem_Icc, mem_Ici, exists_prop]
  exact ⟨fun ⟨m, hm, hk⟩ ↦ hm.1.trans hk, fun hk ↦ ⟨s, ⟨le_rfl, h⟩, hk⟩⟩

theorem sUnion_atMost : ⋃₀ atMost n = Iic n := by
  ext k
  simp only [atMost_eq, sUnion_image, mem_iUnion, mem_Iic, mem_Icc, exists_prop]
  exact ⟨fun ⟨m, _, hk⟩ ↦ hk.2, fun hk ↦ ⟨0, Nat.zero_le n, Nat.zero_le k, hk⟩⟩

/-! ### The implicated upper bound -/

/-- (51): the question of how many, with a possibility for each lower bound. -/
def howMany : Set (Set ℕ) := range Ici

theorem Ici_diff_sUnion_howMany : Ici m \ ⋃₀ {q ∈ howMany | ¬ Ici m ⊆ q} = {m} := by
  ext k
  refine ⟨fun ⟨hk, hnot⟩ ↦ ?_, ?_⟩
  · by_contra hne
    have hlt : m < k := lt_of_le_of_ne hk (Ne.symm hne)
    exact hnot ⟨Ici k, ⟨⟨k, rfl⟩, fun h ↦ (Ici_subset_Ici.1 h).not_gt hlt⟩, mem_Ici.2 le_rfl⟩
  · rintro rfl
    refine ⟨mem_Ici.2 le_rfl, ?_⟩
    rintro ⟨_, ⟨⟨j, rfl⟩, hj⟩, hkj⟩
    exact hj (Ici_subset_Ici.2 hkj)

/-- Exhaustification turns the possibilities of *up to `n`* into those of exactly `m`, for `m`
from the bottom of the scale to `n` (50), (51). -/
theorem exh_upTo_howMany :
    Inquisitive.Unrestricted.exh (upTo s n) howMany = (fun m ↦ {m}) '' Icc s n := by
  simp only [Inquisitive.Unrestricted.exh, upTo, image_image, Ici_diff_sUnion_howMany]

theorem sUnion_exh_upTo : ⋃₀ Inquisitive.Unrestricted.exh (upTo s n) howMany = Icc s n := by
  rw [exh_upTo_howMany, sUnion_image, biUnion_of_singleton]

/-! ### The range requirement -/

theorem nontrivial_upTo : (upTo s n).Nontrivial ↔ s < n := by
  rw [upTo, image_nontrivial Ici_injective, ← not_subsingleton_iff, subsingleton_Icc_iff, not_le]

theorem nontrivial_atMost : (atMost n).Nontrivial ↔ 0 < n := by
  rw [atMost_eq]
  have hinj : InjOn (Icc · n) (Iic n) := fun a ha b hb (h : Icc a n = Icc b n) ↦
    le_antisymm (h ▸ (⟨le_rfl, hb⟩ : b ∈ Icc b n) : b ∈ Icc a n).1
      (h ▸ (⟨le_rfl, ha⟩ : a ∈ Icc a n) : a ∈ Icc b n).1
  have hIic : (Iic n).Nontrivial ↔ 0 < n := by
    rw [← not_subsingleton_iff, show Iic n = Icc 0 n by ext; simp, subsingleton_Icc_iff, not_le]
  exact ⟨fun h ↦ hIic.1 (nontrivial_of_image _ _ h), fun h ↦ (hIic.2 h).image_of_injOn hinj⟩

/-! ### Monotonicity

The asserted content of *up to* is closed upward and that of *at most* downward, so only
*at most* is downward monotone and licenses negative polarity items. -/

theorem isUpperSet_sUnion_upTo : IsUpperSet (⋃₀ upTo s n) :=
  isUpperSet_sUnion fun _ ⟨m, _, hm⟩ ↦ hm ▸ isUpperSet_Ici m

theorem isLowerSet_sUnion_atMost : IsLowerSet (⋃₀ atMost n) :=
  sUnion_atMost ▸ isLowerSet_Iic n

theorem not_isLowerSet_sUnion_upTo (hs : 0 < s) (h : s ≤ n) : ¬ IsLowerSet (⋃₀ upTo s n) := by
  rw [sUnion_upTo h]
  exact fun hl ↦ hs.ne' (Nat.le_zero.1 (hl (Nat.zero_le s) (mem_Ici.2 le_rfl)))

/-! ### The judgments -/

/-- The diagnostics of the paper's examples are a continuation *if any*, a contrast with
*no-one*, a continuation that cancels or reinforces the upper bound, a bare sentence testing
the range requirement, and a negative polarity item. -/
inductive Test where
  | ifAny | butNone | upperBound | range | npi
  deriving DecidableEq, Repr

/-- The diagnostic a row's feature names. -/
def testOf : String → Option Test
  | "ifAny" => some .ifAny
  | "butNone" => some .butNone
  | "evenMore" | "noMore" => some .upperBound
  | "range" => some .range
  | "npi" => some .npi
  | _ => none

/-- The possibilities a modifier raises with the number `n` on the scale of the whole numbers,
by whether the modifier is directional. -/
def proposition (directional : Bool) (n : ℕ) : Set (Set ℕ) :=
  if directional then upTo 1 n else atMost n

/-- What the account predicts acceptable. *If any* needs content compatible with zero and the
contrast with *no-one* content that excludes it. Cancelling or reinforcing the upper bound needs
a bound that is not asserted. A bare sentence needs more than one possibility, and a negative
polarity item downward monotone content. -/
def Predicted (P : Set (Set ℕ)) (n : ℕ) : Test → Prop
  | .ifAny => 0 ∈ ⋃₀ P
  | .butNone => 0 ∉ ⋃₀ P
  | .upperBound => n + 1 ∈ ⋃₀ P
  | .range => P.Nontrivial
  | .npi => IsLowerSet (⋃₀ P)

theorem predicted_upTo_iff (t : Test) :
    Predicted (upTo 1 n) n t ↔ (t = .butNone ∨ t = .upperBound ∧ 1 ≤ n ∨ t = .range ∧ 1 < n ∨
      t = .npi ∧ n = 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : upTo 1 0 = ∅ := by simp [upTo]
    cases t <;> simp [Predicted, h, IsLowerSet]
  · have hU := sUnion_upTo (s := 1) hn
    have hL : ¬ IsLowerSet (Ici 1 : Set ℕ) := hU ▸ not_isLowerSet_sUnion_upTo Nat.one_pos hn
    cases t <;> simp [Predicted, hU, nontrivial_upTo, hn.ne', Nat.one_le_iff_ne_zero, hL]

theorem predicted_atMost_iff (t : Test) :
    Predicted (atMost n) n t ↔ (t = .ifAny ∨ t = .range ∧ 0 < n ∨ t = .npi) := by
  cases t <;> simp [Predicted, sUnion_atMost, nontrivial_atMost, isLowerSet_Iic]

instance (d : Bool) (t : Test) : Decidable (Predicted (proposition d n) n t) := by
  cases d
  · exact decidable_of_iff _ (predicted_atMost_iff t).symm
  · exact decidable_of_iff _ (predicted_upTo_iff t).symm

theorem judgment_rows :
    ∀ row ∈ Examples.all, ∃ t, (row.feature? "test").bind testOf = some t ∧
      ∃ n, row.nat? "numeral" = some n ∧
        (row.judgment = .acceptable ↔
          Predicted (proposition (row.feature? "directional" = some "+") n) n t) := by
  decide +kernel

end Blok2015
