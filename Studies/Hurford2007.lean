/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Numeral.Grammar
public import Linglib.Fragments.English.Numerals
public import Linglib.Fragments.Welsh.Numerals

/-!
# Hurford (2007): A performed practice explains a linguistic universal

This file formalizes Hurford's explanation of the Packing Strategy by the practice of counting.
A counter moves one object at a time and says the next numeral, guided by two maxims: go as far as
the recited sequence allows before setting a group aside, and gather what has been counted into
one group whenever the language has a word for a group of that size. Neither maxim compares the
numeral with any other, yet [each move keeps the numeral
packed](##Numeral.Number.Packed.next), so [counting reaches the numeral that dividing by the
highest multiplier builds](##deleteOne_count). English *twenty one hundred*, one of Hurford's
rare exceptions, is rejected, and [counting forward from *two thousand and ninety nine* does not
reach it](##English.next_twoThousandNinetyNine).

## Implementation notes

The English and Welsh numerals are built from the words of the fragments; the Mixtec and
Hawaiian ones are numerals over numbers, with the three multipliers of the Mixtec example and
the seven Hurford lists for Hawaiian. A counter says a single group as the bare multiplier, so
counting is compared with other numerals up to whether *one* is pronounced. `count` at 0 is the
junk value *one*.

## TODO

The French illustration, *soixante-dix* over \**cinquante vingt*, needs a lexicon whose
well-formed PHRASEs exclude *septante*, which a list of multipliers does not express. The starred
and unstarred numerals are typed here as trees rather than read from `Data/Examples` rows, and
the Mixtec and Hawaiian words have no fragment.

## References

* [hurford-2007]
* [hurford-1975]
-/

@[expose] public section

namespace Hurford2007

open Numeral Number

universe u

variable {α : Type u} (v : α → ℕ) (D M : List α)

/-! ### Counting -/

/-- `amass v M x e` is one group of a multiplier of `x` objects, when there is such a multiplier,
and otherwise `e`, Hurford's maxim "Minimize the number of entities you are dealing with". -/
def amass (x : ℕ) (e : Number α) : Number α :=
  (M.find? (v · = x)).elim e fun m ↦ .phrase (.base m)

/-- `next v D M e` is the numeral a counter at `e` reaches by moving one more object. The counter
says the next word of the recited sequence `D`; past the groups set aside the object opens a
remainder, and a remainder that fills a group of its own adds one to the count of groups, the
maxim "Go as far as you can with the resources you have". The outcome is amassed at every
level. -/
def next : Number α → Number α
  | .digit d => amass v M (v d + 1) ((D[v d]?).elim (.digit d) .digit)
  | .phrase p => amass v M (p.value v + 1) ((D[0]?).elim (.phrase p) fun o ↦ .add p (.digit o))
  | .add (.base m) r => amass v M (v m + r.value v + 1) <|
      if r.value v + 1 = v m then
        .phrase (.mul (amass v M 2 ((D[1]?).elim (.digit m) .digit)) m)
      else .add (.base m) (next r)
  | .add (.mul n m) r => amass v M (n.value v * v m + r.value v + 1) <|
      if r.value v + 1 = v m then .phrase (.mul (next n) m) else .add (.mul n m) (next r)

/-- `count v D M x` is the numeral reached by counting `x` objects one at a time, starting from
the first word of the recited sequence. -/
def count [Inhabited α] (x : ℕ) : Number α :=
  (next v D M)^[x - 1] (.digit (D.getI 0))

variable {v D M} {x : ℕ} {e : Number α}

/-- A numeral a counter may hold for `x` objects: packed, generated and of value `x`. -/
private def Holds (e : Number α) (x : ℕ) : Prop :=
  e.Packed v M ∧ e.Generated D M ∧ e.value v = x

private theorem holds_amass (he : (∀ m ∈ M, v m ≠ x) → Holds (v := v) (D := D) (M := M) e x) :
    Holds (v := v) (D := D) (M := M) (amass v M x e) x := by
  unfold amass
  cases h : M.find? (v · = x) with
  | none => exact he fun m hm ↦ by simpa using List.find?_eq_none.1 h m hm
  | some m =>
    have hm := List.mem_of_find?_eq_some h
    have hx : v m = x := by simpa using List.find?_some h
    exact ⟨isHighestUnder_self hm, hm, hx⟩

private theorem holds_digit (hS : IsSystem v D M) (hx : ∀ m ∈ M, x + 1 < v m) :
    Holds (v := v) (D := D) (M := M) ((D[x]?).elim e .digit) (x + 1) := by
  obtain ⟨m₀, hm₀, hm₀D⟩ := hS.exists_value_le
  have hk : x < D.length := by have := hx m₀ hm₀; omega
  rw [List.getElem?_eq_getElem hk]
  exact ⟨fun m hm ↦ by rw [hS.value_getElem]; exact hx m hm, List.getElem_mem hk,
    hS.value_getElem x hk⟩

private theorem holds_next (hS : IsSystem v D M) :
    ∀ {e : Number α}, e.Packed v M → e.Generated D M →
      Holds (v := v) (D := D) (M := M) (next v D M e) (e.value v + 1)
  | .digit d, hp, _ => holds_amass fun hne ↦ holds_digit hS fun m hm ↦
      lt_of_le_of_ne (hp m hm) (hne m hm).symm
  | .phrase p, hp, hg => holds_amass fun hne ↦ by
    have hm := Phrase.Packed.isHighestUnder hp
    have hone := holds_digit (e := .phrase p) (x := 0) hS fun m hm ↦ hS.one_lt_value m hm
    obtain ⟨m₀, hm₀, hm₀D⟩ := hS.exists_value_le
    have hk : 0 < D.length := by have := hS.one_lt_value m₀ hm₀; omega
    rw [List.getElem?_eq_getElem hk] at hone ⊢
    obtain ⟨hop, hog, hov⟩ := hone
    have hov : v D[0] = 1 := hov
    exact ⟨⟨hp, hop, by simpa [Number.value, hov] using hm.succ hne,
      by simpa [Number.value, hov] using hS.one_lt_value _ hm.mem⟩, ⟨hg, hog⟩,
      by simp [Number.value, hov]⟩
  | .add (.base m) r, ⟨hpb, hr, (hm : IsHighestUnder v M (v m + r.value v) m),
      (hlt : r.value v < v m)⟩, ⟨gm, gr⟩ => holds_amass fun hne ↦ by
    have hm' := hm.succ hne
    split_ifs with h
    · have h2 : Holds (v := v) (D := D) (M := M)
          (amass v M 2 ((D[1]?).elim (.digit m) .digit)) 2 :=
        holds_amass fun hne2 ↦ holds_digit hS fun m' hm' ↦
          lt_of_le_of_ne (hS.one_lt_value m' hm') (hne2 m' hm').symm
      obtain ⟨h2p, h2g, h2v⟩ := h2
      refine ⟨⟨?_, h2p⟩, ⟨h2g, gm⟩, ?_⟩
      · rw [h2v]; rwa [show v m + r.value v + 1 = 2 * v m by omega] at hm'
      · simp only [Number.value, Phrase.value, h2v]; omega
    · obtain ⟨hnp, hng, hnv⟩ := holds_next hS hr gr
      exact ⟨⟨hpb, hnp, by simpa [Phrase.value, Phrase.head, hnv, Nat.add_assoc] using hm',
        by simp only [hnv, Phrase.head]; omega⟩, ⟨gm, hng⟩,
        by simp only [Number.value, Phrase.value, hnv]; omega⟩
  | .add (.mul n m) r, ⟨⟨hpm, hn⟩, hr,
      (hm : IsHighestUnder v M (n.value v * v m + r.value v) m), (hlt : r.value v < v m)⟩,
      ⟨⟨gn, gm⟩, gr⟩ => holds_amass fun hne ↦ by
    have hm' := hm.succ hne
    split_ifs with h
    · obtain ⟨hnp, hng, hnv⟩ := holds_next hS hn gn
      refine ⟨⟨?_, hnp⟩, ⟨hng, gm⟩, ?_⟩
      · rw [hnv]
        rwa [show n.value v * v m + r.value v + 1 = (n.value v + 1) * v m by
          rw [Nat.add_one_mul]; omega] at hm'
      · simp only [Number.value, Phrase.value, hnv, Nat.add_one_mul]; omega
    · obtain ⟨hnp, hng, hnv⟩ := holds_next hS hr gr
      exact ⟨⟨⟨hpm, hn⟩, hnp, by simpa [Phrase.value, Phrase.head, hnv, Nat.add_assoc] using hm',
        by simp only [hnv, Phrase.head]; omega⟩, ⟨⟨gn, gm⟩, hng⟩,
        by simp only [Number.value, Phrase.value, hnv]; omega⟩

/-- Counting preserves the Packing Strategy: a counter at a packed numeral who moves one more
object, guided only by the two maxims, reaches a packed numeral. -/
theorem _root_.Numeral.Number.Packed.next (hS : IsSystem v D M) (hp : e.Packed v M)
    (hg : e.Generated D M) : (next v D M e).Packed v M :=
  (holds_next hS hp hg).1

theorem _root_.Numeral.Number.Generated.next (hS : IsSystem v D M) (hp : e.Packed v M)
    (hg : e.Generated D M) : (next v D M e).Generated D M :=
  (holds_next hS hp hg).2.1

theorem value_next (hS : IsSystem v D M) (hp : e.Packed v M) (hg : e.Generated D M) :
    (next v D M e).value v = e.value v + 1 :=
  (holds_next hS hp hg).2.2

section count

variable [Inhabited α]

private theorem holds_count (hS : IsSystem v D M) (hx : 0 < x) :
    Holds (v := v) (D := D) (M := M) (count v D M x) x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one.2 hx
  induction k with
  | zero =>
    have := holds_digit (e := .digit default) (x := 0) hS fun m hm ↦ hS.one_lt_value m hm
    obtain ⟨m₀, hm₀, hm₀D⟩ := hS.exists_value_le
    have hk : 0 < D.length := by have := hS.one_lt_value m₀ hm₀; omega
    rw [List.getElem?_eq_getElem hk] at this
    simpa [count, List.getI_eq_getElem _ hk] using this
  | succ k ih =>
    obtain ⟨hp, hg, hv⟩ := ih k.succ_pos
    have := holds_next hS hp hg
    rw [hv] at this
    rwa [count, Nat.add_sub_cancel, Function.iterate_succ_apply']

theorem packed_count (hS : IsSystem v D M) (hx : 0 < x) : (count v D M x).Packed v M :=
  (holds_count hS hx).1

theorem generated_count (hS : IsSystem v D M) (hx : 0 < x) : (count v D M x).Generated D M :=
  (holds_count hS hx).2.1

theorem value_count (hS : IsSystem v D M) (hx : 0 < x) : (count v D M x).value v = x :=
  (holds_count hS hx).2.2

/-- Counting `x` objects one at a time reaches the numeral that dividing `x` by the highest
multiplier that fits builds from the top down, up to whether *one* is pronounced. -/
theorem deleteOne_count (hS : IsSystem v D M) (hx : 0 < x) :
    (count v D M x).deleteOne v = ofValue v D M x := by
  rw [← (packed_count hS hx).ofValue_value hS (generated_count hS hx), value_count hS hx]

theorem _root_.Numeral.Number.Packed.deleteOne_count_value (hS : IsSystem v D M)
    (hp : e.Packed v M) (hg : e.Generated D M) :
    (count v D M (e.value v)).deleteOne v = e.deleteOne v := by
  rw [deleteOne_count hS (value_pos hS hg), hp.ofValue_value hS hg]

end count

/-! ### English -/

namespace English

open _root_.English.Numerals

/-- The English numerals over the words of the fragment. -/
abbrev Num := Number Numeral

theorem isSystem : IsSystem Numeral.value digits multipliers :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- *five million, two thousand, six hundred* is `[[five million] [[two thousand] [six hundred]]]`.
-/
def fiveMillionTwoThousandSixHundred : Num :=
  .add (.mul (.digit five) million) (.add (.mul (.digit two) thousand)
    (.phrase (.mul (.digit six) hundred)))

/-- \**six hundred, two thousand, five million* packs the same PHRASEs the other way round. -/
def sixHundredTwoThousandFiveMillion : Num :=
  .add (.mul (.digit six) hundred) (.add (.mul (.digit two) thousand)
    (.phrase (.mul (.digit five) million)))

/-- *six hundred thousand* is `[[six hundred] thousand]`. -/
def sixHundredThousand : Num :=
  .phrase (.mul (.phrase (.mul (.digit six) hundred)) thousand)

/-- \**six thousand hundred* is `[[six thousand] hundred]`. -/
def sixThousandHundred : Num :=
  .phrase (.mul (.phrase (.mul (.digit six) thousand)) hundred)

/-- *ninety nine* is `[[nine ten] nine]`. -/
def ninetyNine : Num := .add (.mul (.digit nine) ten) (.digit nine)

/-- *two thousand and ninety nine* is `[[two thousand] [ninety nine]]`. -/
def twoThousandNinetyNine : Num := .add (.mul (.digit two) thousand) ninetyNine

/-- \**twenty hundred and ninety nine* is `[[twenty hundred] [ninety nine]]`. -/
def twentyHundredNinetyNine : Num :=
  .add (.mul (.phrase (.mul (.digit two) ten)) hundred) ninetyNine

/-- *two thousand, one hundred* is `[[two thousand] [one hundred]]`. -/
def twoThousandOneHundred : Num :=
  .add (.mul (.digit two) thousand) (.phrase (.mul (.digit one) hundred))

/-- *twenty one hundred* is `[[twenty-one] hundred]`, twenty-one hundreds. -/
def twentyOneHundred : Num :=
  .phrase (.mul (.add (.mul (.digit two) ten) (.digit one)) hundred)

example : (count Numeral.value digits multipliers 5002600).deleteOne Numeral.value =
    fiveMillionTwoThousandSixHundred.deleteOne Numeral.value :=
  Packed.deleteOne_count_value (e := fiveMillionTwoThousandSixHundred) isSystem
    (by decide) (by decide)

example : sixHundredTwoThousandFiveMillion.value Numeral.value =
    fiveMillionTwoThousandSixHundred.value Numeral.value := by decide

example : ¬ sixHundredTwoThousandFiveMillion.Packed Numeral.value multipliers := by decide

example : sixHundredThousand.Packed Numeral.value multipliers := by decide

example : sixThousandHundred.value Numeral.value = sixHundredThousand.value Numeral.value := by
  decide

example : ¬ sixThousandHundred.Packed Numeral.value multipliers := by decide

example : ¬ twentyHundredNinetyNine.Packed Numeral.value multipliers := by decide

/-- A counter with nine hundreds, nine tens and nine who moves one more object has ten hundreds,
and gathers them into a *thousand*. -/
example : next Numeral.value digits multipliers (.add (.mul (.digit nine) hundred) ninetyNine) =
    .phrase (.base thousand) := by decide

/-- A counter with two tens and nine who moves one more object has three tens. -/
example : next Numeral.value digits multipliers (.add (.mul (.digit two) ten) (.digit nine)) =
    .phrase (.mul (.digit three) ten) := by decide

example : twentyOneHundred.value Numeral.value = twoThousandOneHundred.value Numeral.value := by
  decide

/-- The Packing Strategy rejects *twenty one hundred*, which English allows, one of the rare
counterexamples to its prediction that each number has a single numeral. -/
theorem not_packed_twentyOneHundred : ¬ twentyOneHundred.Packed Numeral.value multipliers := by
  decide

/-- Counting forward from *two thousand and ninety nine* gives *two thousand, one hundred*, not
*twenty one hundred*. -/
theorem next_twoThousandNinetyNine :
    next Numeral.value digits multipliers twoThousandNinetyNine =
      twoThousandOneHundred.deleteOne Numeral.value := by
  decide

end English

/-! ### Welsh -/

namespace Welsh

open _root_.Welsh.Numerals

/-- *pedwar ar bymtheg*, four on fifteen, is 19. -/
def nineteen : Number Numeral := .add (.base pymtheg) (.digit pedwar)

/-- The numerals from 16 to 19 are built on *pymtheg*. -/
example : next Numeral.value digits multipliers (.phrase (.base pymtheg)) =
    .add (.base pymtheg) (.digit un) := by decide

/-- *ugain* takes over at 20. -/
example : next Numeral.value digits multipliers nineteen = .phrase (.base ugain) := by decide

/-- After 20 Welsh counts in twenties, not in fifteens. -/
example : next Numeral.value digits multipliers (.add (.base ugain) nineteen) =
    .phrase (.mul (.digit dau) ugain) := by decide

end Welsh

/-! ### Mixtec -/

namespace Mixtec

/-- The digits of the example run to fourteen. -/
def digits : List ℕ := List.range' 1 14

/-- The multipliers of the example are *šiaʼu* 15, *šiko* 20 and *tuu* 400. -/
def multipliers : List ℕ := [15, 20, 400]

theorem isSystem : IsSystem id digits multipliers := ⟨by decide, by decide, by decide, by decide⟩

/-- *šiaʼu kuu*, fifteen and four, is 19. -/
def nineteen : Number ℕ := .add (.base 15) (.digit 4)

/-- *šiaʼu kuu tuu šiaʼu kuu šiko šiaʼu kuu*, nineteen four-hundreds, nineteen twenties and
nineteen, is 7999. -/
def numeral7999 : Number ℕ := .add (.mul nineteen 400) (.add (.mul nineteen 20) nineteen)

/-- `transposed` has the two multipliers of `numeral7999` in each other's places. -/
def transposed : Number ℕ := .add (.mul nineteen 20) (.add (.mul nineteen 400) nineteen)

example : (count id digits multipliers 7999).deleteOne id = numeral7999 :=
  Packed.deleteOne_count_value (e := numeral7999) isSystem (by decide) (by decide)

example : transposed.value id = numeral7999.value id := by decide

example : ¬ transposed.Packed id multipliers := by decide

end Mixtec

/-! ### Hawaiian -/

namespace Hawaiian

/-- The digits run to nine. -/
def digits : List ℕ := List.range' 1 9

/-- The Hawaiian multipliers are 10, 20, 40, 400, 4000, 40,000 and 400,000. -/
def multipliers : List ℕ := [10, 20, 40, 400, 4000, 40000, 400000]

theorem isSystem : IsSystem id digits multipliers := ⟨by decide, by decide, by decide, by decide⟩

/-- The numeral for 609,751 is one 400,000, five 40,000s, two 4000s, four 400s, three 40s,
twenty, ten and one. -/
def numeral609751 : Number ℕ :=
  .add (.mul (.digit 1) 400000) <|
  .add (.mul (.digit 5) 40000) <|
  .add (.mul (.digit 2) 4000) <|
  .add (.mul (.digit 4) 400) <|
  .add (.mul (.digit 3) 40) <|
  .add (.base 20) <|
  .add (.base 10) (.digit 1)

example : (count id digits multipliers 609751).deleteOne id = numeral609751.deleteOne id :=
  Packed.deleteOne_count_value (e := numeral609751) isSystem (by decide) (by decide)

end Hawaiian

end Hurford2007
