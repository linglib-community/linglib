/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Numeral.Composition
public import Mathlib.Data.List.MinMax

/-!
# Hurford (2007): A performed practice explains a linguistic universal

This file formalizes Hurford's explanation of the Packing Strategy by the practice of counting.
A counter moves one object at a time and says the next numeral, guided by two maxims: go as far as
the recited sequence allows before setting a group aside, and gather what has been counted into
one group whenever the language has a word for a group of that size. Neither maxim compares the
numeral with any other, yet [each move keeps the numeral
packed](##Numeral.Number.Packed.next), so [counting reaches exactly the numerals the Packing
Strategy admits](##range_count). English *twenty one hundred*, one of Hurford's rare exceptions,
is rejected, and [counting forward from *two thousand and ninety nine* does not reach
it](##English.next_twoThousandNinetyNine).

## Implementation notes

The trees use the 1975 grammar of `Numeral`, so a DIGIT is a tally and a PHRASE of a bare M is
`[one M]`. English *million* is the base-power M of value `10 ^ 6`, since the Packing Strategy
compares only values. The Mixtec bases are the three of the example, the Hawaiian ones the seven
Hurford lists, and the Welsh ones those of his remarks on *pymtheg*.

## TODO

The French illustration, *soixante-dix* over \**cinquante vingt*, needs a lexicon whose
well-formed PHRASEs exclude *septante*, which a set of Ms does not express. The starred and
unstarred numerals are typed here as trees rather than read from `Data/Examples` rows.

## References

* [hurford-2007]
* [hurford-1975]
-/

@[expose] public section

namespace Hurford2007

open Numeral Number

variable {L : List M} {e : Number}

/-! ### Counting -/

/-- `amass L e` gathers the objects of `e` into one group of a base of `L`, when `L` has a base
of that many objects, Hurford's maxim "Minimize the number of entities you are dealing with". -/
def amass (L : List M) (e : Number) : Number :=
  (L.find? (·.value = e.value)).elim e fun m ↦ .phrase (.mk .one m)

/-- `next L e` is the numeral a counter at `e` reaches by moving one more object. The counter says
the next word of the recited sequence; past its end the object opens a remainder beside the groups
set aside, and a remainder that fills a group of its own adds one to the count of groups, the maxim
"Go as far as you can with the resources you have". The outcome is amassed at every level. -/
def next (L : List M) : Number → Number
  | .one => amass L (.oneAnd .one)
  | .oneAnd r => amass L (.oneAnd (.oneAnd r))
  | .phrase p => amass L (.phraseAnd p .one)
  | .phraseAnd (.mk n m) r =>
    amass L <| if r.value + 1 = m.value then .phrase (.mk (next L n) m)
      else .phraseAnd (.mk n m) (next L r)

/-- `count L v` is the numeral reached by counting `v` objects one at a time, starting from
*one*. -/
def count (L : List M) (v : ℕ) : Number :=
  (next L)^[v - 1] .one

@[simp] theorem value_amass (L : List M) (e : Number) : (amass L e).value = e.value := by
  unfold amass
  cases h : L.find? (·.value = e.value) with
  | none => rfl
  | some m => simpa [Number.value, Phrase.value] using List.find?_some h

private theorem packed_amass {v : ℕ} (hv : e.value = v)
    (he : (∀ m ∈ L, m.value ≠ v) → e.Packed {m | m ∈ L}) : (amass L e).Packed {m | m ∈ L} := by
  unfold amass
  cases h : L.find? (·.value = e.value) with
  | none => exact he fun m hm ↦ by simpa [hv] using List.find?_eq_none.1 h m hm
  | some m => exact packed_phrase_iff.2 (Phrase.packed_mk_one (List.mem_of_find?_eq_some h))

private theorem isHighestUnder_succ {m : M} {v : ℕ} (hm : m.IsHighestUnder {m | m ∈ L} v)
    (hne : ∀ m ∈ L, m.value ≠ v + 1) : m.IsHighestUnder {m | m ∈ L} (v + 1) := by
  obtain ⟨hmL, hmv, hub⟩ := M.isHighestUnder_iff.1 hm
  exact M.isHighestUnder_iff.2 ⟨hmL, by omega, fun m' hm' h ↦ hub m' hm' (by
    have := hne m' hm'; omega)⟩

@[simp] theorem value_next (L : List M) : ∀ e : Number, (next L e).value = e.value + 1
  | .one => by simp [next, Number.value]
  | .oneAnd r => by simp [next, Number.value]; omega
  | .phrase p => by simp [next, Number.value]
  | .phraseAnd (.mk n m) r => by
    rw [next, value_amass]
    split_ifs with h
    · simp only [Number.value, Phrase.value, value_next L n, Nat.add_one_mul]; omega
    · simp only [Number.value, Phrase.value, value_next L r]; omega

/-- Counting preserves the Packing Strategy: a counter at a packed numeral who moves one more
object, guided only by the two maxims, reaches a packed numeral. -/
theorem _root_.Numeral.Number.Packed.next :
    ∀ {e : Number}, e.Packed {m | m ∈ L} → (next L e).Packed {m | m ∈ L}
  | .one, _ => packed_amass (v := 2) rfl fun hne ↦
      ⟨fun m hm ↦ by have := m.one_lt_value; have := hne m hm; simp only [Number.value]; omega,
        trivial⟩
  | .oneAnd r, ⟨hlow, hr⟩ => packed_amass (v := 1 + r.value + 1) (by simp [Number.value]; omega)
      fun hne ↦ ⟨fun m hm ↦ by
        have := hlow m hm; have := hne m hm; simp only [Number.value]; omega, hlow, hr⟩
  | .phrase (.mk n m), ⟨hm, hn⟩ => packed_amass (v := n.value * m.value + 1) rfl fun hne ↦
      ⟨isHighestUnder_succ hm hne, m.one_lt_value, hn, trivial⟩
  | .phraseAnd (.mk n m) r, ⟨hm, hr, hn, hrp⟩ => by
    rw [Hurford2007.next]
    refine packed_amass (v := n.value * m.value + r.value + 1) ?_ fun hne ↦ ?_
    · split_ifs with h
      · simp only [Number.value, Phrase.value, value_next, Nat.add_one_mul]; omega
      · simp only [Number.value, Phrase.value, value_next]; omega
    · have hm' := isHighestUnder_succ hm hne
      split_ifs with h
      · refine ⟨?_, hn.next⟩
        rwa [value_next, show (n.value + 1) * m.value = n.value * m.value + r.value + 1 by
          rw [Nat.add_one_mul]; omega]
      · exact ⟨by rwa [value_next], by rw [value_next]; omega, hn, hrp.next⟩

theorem value_count (L : List M) {v : ℕ} (hv : 0 < v) : (count L v).value = v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one.2 hv
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [count, Nat.add_sub_cancel, Function.iterate_succ_apply', value_next]
    exact congrArg (· + 1) (ih k.succ_pos)

theorem packed_count (L : List M) (v : ℕ) : (count L v).Packed {m | m ∈ L} := by
  unfold count
  induction v - 1 with
  | zero => trivial
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.next

theorem _root_.Numeral.Number.Packed.count_value (hL : Set.InjOn M.value {m | m ∈ L})
    (he : e.Packed {m | m ∈ L}) : count L e.value = e :=
  (packed_count L _).eq_of_value_eq hL he (value_count L e.value_pos)

/-- Over bases with distinct values, the numerals counting reaches are exactly the ones the Packing
Strategy admits. -/
theorem range_count (hL : Set.InjOn M.value {m | m ∈ L}) :
    Set.range (count L) = {e | e.Packed {m | m ∈ L}} :=
  Set.ext fun _ ↦ ⟨fun ⟨v, hv⟩ ↦ hv ▸ packed_count L v, fun he ↦ ⟨_, he.count_value hL⟩⟩

/-- `digit d` is the tally of `d` marks. -/
abbrev digit (d : ℕ) : Number := .tally (d - 1)

/-! ### English -/

namespace English

/-- *hundred* is the M of value `10 ^ 2`. -/
abbrev hundred : M := .tenPow 1

/-- *thousand* is the M of value `10 ^ 3`. -/
abbrev thousand : M := .tenPow 2

/-- *million* is the M of value `10 ^ 6`. [hurford-1975] builds it on *thousand*, with (31),
p. 35, raising the exponent by one in American English. -/
abbrev million : M := .tenPow 5

/-- The English bases are *ten*, *hundred*, *thousand* and *million*. -/
def bases : List M := [.ten, hundred, thousand, million]

theorem injOn_bases : Set.InjOn M.value {m | m ∈ bases} :=
  fun _ ha _ hb ↦ List.inj_on_of_nodup_map (by decide) ha hb

/-- *five million, two thousand, six hundred* is `[[five million] [[two thousand] [six hundred]]]`.
-/
def fiveMillionTwoThousandSixHundred : Number :=
  .phraseAnd (.mk (digit 5) million)
    (.phraseAnd (.mk (digit 2) thousand) (.phrase (.mk (digit 6) hundred)))

/-- \**six hundred, two thousand, five million* packs the same PHRASEs the other way round. -/
def sixHundredTwoThousandFiveMillion : Number :=
  .phraseAnd (.mk (digit 6) hundred)
    (.phraseAnd (.mk (digit 2) thousand) (.phrase (.mk (digit 5) million)))

/-- *six hundred thousand* is `[[six hundred] thousand]`. -/
def sixHundredThousand : Number :=
  .phrase (.mk (.phrase (.mk (digit 6) hundred)) thousand)

/-- \**six thousand hundred* is `[[six thousand] hundred]`. -/
def sixThousandHundred : Number :=
  .phrase (.mk (.phrase (.mk (digit 6) thousand)) hundred)

/-- *ninety nine* is `[[nine ten] nine]`. -/
def ninetyNine : Number := .phraseAnd (.mk (digit 9) .ten) (digit 9)

/-- *two thousand and ninety nine* is `[[two thousand] [ninety nine]]`. -/
def twoThousandNinetyNine : Number := .phraseAnd (.mk (digit 2) thousand) ninetyNine

/-- \**twenty hundred and ninety nine* is `[[twenty hundred] [ninety nine]]`. -/
def twentyHundredNinetyNine : Number :=
  .phraseAnd (.mk (.phrase (.mk (digit 2) .ten)) hundred) ninetyNine

/-- *two thousand, one hundred* is `[[two thousand] [one hundred]]`. -/
def twoThousandOneHundred : Number :=
  .phraseAnd (.mk (digit 2) thousand) (.phrase (.mk (digit 1) hundred))

/-- *twenty one hundred* is `[[twenty-one] hundred]`, twenty-one hundreds. -/
def twentyOneHundred : Number :=
  .phrase (.mk (.phraseAnd (.mk (digit 2) .ten) (digit 1)) hundred)

example : count bases 5002600 = fiveMillionTwoThousandSixHundred :=
  Packed.count_value injOn_bases (e := fiveMillionTwoThousandSixHundred) (by decide)

example : sixHundredTwoThousandFiveMillion.value = fiveMillionTwoThousandSixHundred.value := rfl

example : ¬ sixHundredTwoThousandFiveMillion.Packed {m | m ∈ bases} := by decide

example : count bases 600000 = sixHundredThousand :=
  Packed.count_value injOn_bases (e := sixHundredThousand) (by decide)

example : sixThousandHundred.value = sixHundredThousand.value := rfl

example : ¬ sixThousandHundred.Packed {m | m ∈ bases} := by decide

example : ¬ twentyHundredNinetyNine.Packed {m | m ∈ bases} := by decide

/-- A counter with nine hundreds, nine tens and nine who moves one more object has ten hundreds,
and gathers them into a *thousand*. -/
example : next bases (.phraseAnd (.mk (digit 9) hundred) ninetyNine) =
    .phrase (.mk .one thousand) := by decide

example : twentyOneHundred.value = twoThousandOneHundred.value := rfl

/-- The Packing Strategy rejects *twenty one hundred*, which English allows, one of the rare
counterexamples to its prediction that each number has a single numeral. -/
theorem not_packed_twentyOneHundred : ¬ twentyOneHundred.Packed {m | m ∈ bases} := by decide

/-- Counting forward from *two thousand and ninety nine* gives *two thousand, one hundred*, not
*twenty one hundred*. -/
theorem next_twoThousandNinetyNine : next bases twoThousandNinetyNine = twoThousandOneHundred := by
  decide

end English

/-! ### Welsh -/

namespace Welsh

/-- *pymtheg* is the base 15. -/
def fifteen : M := .base 15

/-- *ugain* is the base 20. -/
def twenty : M := .base 20

/-- The Welsh bases are *deg* 10, *pymtheg* 15, *ugain* 20 and *cant* 100. -/
def bases : List M := [.base 10, fifteen, twenty, .base 100]

/-- *pedwar ar bymtheg*, four on fifteen, is 19. -/
def nineteen : Number := .phraseAnd (.mk .one fifteen) (digit 4)

/-- The numerals from 16 to 19 are built on *pymtheg*. -/
example : next bases (.phrase (.mk .one fifteen)) = .phraseAnd (.mk .one fifteen) .one := by decide

/-- *ugain* takes over at 20. -/
example : next bases nineteen = .phrase (.mk .one twenty) := by decide

/-- After 20 Welsh counts in twenties, not in fifteens. -/
example : next bases (.phraseAnd (.mk .one twenty) nineteen) = .phrase (.mk (digit 2) twenty) := by
  decide

end Welsh

/-! ### Mixtec -/

namespace Mixtec

/-- *šiaʼu* is the base 15. -/
def fifteen : M := .base 15

/-- *šiko* is the base 20. -/
def twenty : M := .base 20

/-- *tuu* is the base 400. -/
def fourHundred : M := .base 400

/-- The bases of the example are 15, 20 and 400. -/
def bases : List M := [fifteen, twenty, fourHundred]

theorem injOn_bases : Set.InjOn M.value {m | m ∈ bases} :=
  fun _ ha _ hb ↦ List.inj_on_of_nodup_map (by decide) ha hb

/-- *šiaʼu kuu*, fifteen and four, is 19. -/
def nineteen : Number := .phraseAnd (.mk .one fifteen) (digit 4)

/-- *šiaʼu kuu tuu šiaʼu kuu šiko šiaʼu kuu*, nineteen four-hundreds, nineteen twenties and
nineteen, is 7999. -/
def numeral7999 : Number :=
  .phraseAnd (.mk nineteen fourHundred) (.phraseAnd (.mk nineteen twenty) nineteen)

/-- `transposed` has the two Ms of `numeral7999` in each other's places. -/
def transposed : Number :=
  .phraseAnd (.mk nineteen twenty) (.phraseAnd (.mk nineteen fourHundred) nineteen)

example : count bases 7999 = numeral7999 :=
  Packed.count_value injOn_bases (e := numeral7999) (by decide)

example : transposed.value = numeral7999.value := rfl

example : ¬ transposed.Packed {m | m ∈ bases} := by decide

end Mixtec

/-! ### Hawaiian -/

namespace Hawaiian

/-- The Hawaiian bases are 10, 20, 40, 400, 4000, 40,000 and 400,000. -/
def bases : List M :=
  [.base 10, .base 20, .base 40, .base 400, .base 4000, .base 40000, .base 400000]

theorem injOn_bases : Set.InjOn M.value {m | m ∈ bases} :=
  fun _ ha _ hb ↦ List.inj_on_of_nodup_map (by decide) ha hb

/-- The numeral for 609,751 is one 400,000, five 40,000s, two 4000s, four 400s, three 40s,
twenty, ten and one. -/
def numeral609751 : Number :=
  .phraseAnd (.mk .one (.base 400000)) <|
  .phraseAnd (.mk (digit 5) (.base 40000)) <|
  .phraseAnd (.mk (digit 2) (.base 4000)) <|
  .phraseAnd (.mk (digit 4) (.base 400)) <|
  .phraseAnd (.mk (digit 3) (.base 40)) <|
  .phraseAnd (.mk .one (.base 20)) <|
  .phraseAnd (.mk .one (.base 10)) .one

example : count bases 609751 = numeral609751 :=
  Packed.count_value injOn_bases (e := numeral609751) (by decide)

end Hawaiian

end Hurford2007
