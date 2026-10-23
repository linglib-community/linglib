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
A counter goes as far as the recited sequence allows, sets what has been counted aside as a group,
gathers the groups into one of the next base up once there are enough of them, and counts the
groups and the remainder the same way. `count` computes the outcome over a language's list of
bases, and the numerals the Packing Strategy admits are exactly the ones counting produces.
Hurford's English, Mixtec and Hawaiian illustrations are packed and their starred rearrangements
are not, while English *twenty one hundred*, one of his rare exceptions, is attested but rejected.

## Main definitions

* `count`: counting with a list of bases

## Main results

* `packed_count`: counting reaches a packed numeral
* `packed_iff_eq_count`: the packed numerals are the outcomes of counting
* `Mixtec.count_eq_numeral7999`, `Hawaiian.count_eq_numeral609751`: counting reaches the paper's
  Mixtec and Hawaiian numerals
* `English.not_packed_twentyOneHundred`: the Packing Strategy rejects *twenty one hundred*

## Implementation notes

The trees use the 1975 grammar of `Numeral`, so a DIGIT is a tally and a PHRASE of a bare M is
`[one M]`. English *million* is the base-power M of value `10 ^ 6`, since the Packing Strategy
compares only values. The Mixtec bases are the three of the example and the Hawaiian ones the
seven Hurford lists.

## References

* [hurford-2007]
* [hurford-1975]
-/

@[expose] public section

namespace Hurford2007

open Numeral Number

/-! ### Counting -/

/-- `count L v` counts `v` objects with the bases `L`. When every base exceeds `v` it recites the
counting sequence up to `v`; otherwise it sets aside as many groups of the highest base that fits
as possible, and counts the groups and the remainder the same way. -/
def count (L : List M) (v : ℕ) : Number :=
  match h : (L.filter (·.value ≤ v)).argmax M.value with
  | none => .tally (v - 1)
  | some m =>
    have hm : m.value ≤ v := by simpa using (List.mem_filter.1 (List.argmax_mem h)).2
    if v % m.value = 0 then .phrase (.mk (count L (v / m.value)) m)
    else .phraseAnd (.mk (count L (v / m.value)) m) (count L (v % m.value))
termination_by v
decreasing_by
  all_goals have := m.one_lt_value
  · exact Nat.div_lt_self (by omega) this
  · exact Nat.div_lt_self (by omega) this
  · exact (Nat.mod_lt _ (by omega)).trans_le hm

/-- Counting reaches a packed numeral for every positive number. -/
theorem packed_count (L : List M) {v : ℕ} (hv : 0 < v) :
    (count L v).Packed {m | m ∈ L} ∧ (count L v).value = v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  rw [count]
  split
  · next h =>
    have hlow : ∀ m ∈ L, v < m.value := fun m hm ↦ by
      have := List.argmax_eq_none.1 h
      by_contra hmv
      have : m ∈ L.filter (·.value ≤ v) := List.mem_filter.2 ⟨hm, by simpa using hmv⟩
      simp_all
    exact ⟨packed_tally_iff.2 fun m hm ↦ by have := hlow m hm; omega, by simp; omega⟩
  · next m h =>
    have hmL := List.mem_filter.1 (List.argmax_mem h)
    have hmv : m.value ≤ v := by simpa using hmL.2
    have hm : m.IsHighestUnder {m | m ∈ L} v := M.isHighestUnder_iff.2 ⟨hmL.1, hmv,
      fun m' hm' hv' ↦ List.le_of_mem_argmax (List.mem_filter.2 ⟨hm', by simpa using hv'⟩) h⟩
    have h1 := m.one_lt_value
    have ihn := ih (v / m.value) (Nat.div_lt_self hv h1) (Nat.div_pos hmv (by omega))
    split_ifs with hr
    · exact packed_phrase hm (Nat.dvd_of_mod_eq_zero hr) ihn.1 ihn.2
    · have ihr := ih (v % m.value) ((Nat.mod_lt _ (by omega)).trans_le hmv) (by omega)
      exact packed_phraseAnd hm ihn.1 ihn.2 ihr.1 ihr.2

/-- Over bases with distinct values, the numerals the Packing Strategy admits are exactly the ones
counting produces. -/
theorem packed_iff_eq_count {L : List M} (hL : Set.InjOn M.value {m | m ∈ L}) {e : Number} :
    e.Packed {m | m ∈ L} ↔ e = count L e.value := by
  obtain ⟨hc, hcv⟩ := packed_count L e.value_pos
  exact ⟨fun he ↦ he.eq_of_value_eq hL hc hcv.symm, fun he ↦ he ▸ hc⟩

theorem count_eq_of_packed {L : List M} (hL : Set.InjOn M.value {m | m ∈ L}) {e : Number} {v : ℕ}
    (he : e.Packed {m | m ∈ L}) (hv : e.value = v) : count L v = e :=
  hv ▸ ((packed_iff_eq_count hL).1 he).symm

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

/-- *two thousand, one hundred* is `[[two thousand] [one hundred]]`. -/
def twoThousandOneHundred : Number :=
  .phraseAnd (.mk (digit 2) thousand) (.phrase (.mk (digit 1) hundred))

/-- *twenty one hundred* is `[[twenty-one] hundred]`, twenty-one hundreds. -/
def twentyOneHundred : Number :=
  .phrase (.mk (.phraseAnd (.mk (digit 2) .ten) (digit 1)) hundred)

theorem count_eq_fiveMillionTwoThousandSixHundred :
    count bases 5002600 = fiveMillionTwoThousandSixHundred :=
  count_eq_of_packed injOn_bases (by decide) rfl

example : sixHundredTwoThousandFiveMillion.value = fiveMillionTwoThousandSixHundred.value := rfl

theorem not_packed_sixHundredTwoThousandFiveMillion :
    ¬ sixHundredTwoThousandFiveMillion.Packed {m | m ∈ bases} := by decide

theorem count_eq_sixHundredThousand : count bases 600000 = sixHundredThousand :=
  count_eq_of_packed injOn_bases (by decide) rfl

example : sixThousandHundred.value = sixHundredThousand.value := rfl

theorem not_packed_sixThousandHundred : ¬ sixThousandHundred.Packed {m | m ∈ bases} := by decide

theorem count_eq_twoThousandOneHundred : count bases 2100 = twoThousandOneHundred :=
  count_eq_of_packed injOn_bases (by decide) rfl

example : twentyOneHundred.value = twoThousandOneHundred.value := rfl

/-- The Packing Strategy rejects *twenty one hundred*, which English allows, one of the rare
counterexamples to its prediction that each number has a single numeral. -/
theorem not_packed_twentyOneHundred : ¬ twentyOneHundred.Packed {m | m ∈ bases} := by decide

end English

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

/-- The sisters of the recursive NUMBERs are the highest-valued the lexicon allows below the
value of the dominating node. -/
theorem count_eq_numeral7999 : count bases 7999 = numeral7999 :=
  count_eq_of_packed injOn_bases (by decide) rfl

example : transposed.value = numeral7999.value := rfl

theorem not_packed_transposed : ¬ transposed.Packed {m | m ∈ bases} := by decide

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

theorem count_eq_numeral609751 : count bases 609751 = numeral609751 :=
  count_eq_of_packed injOn_bases (by decide) rfl

end Hawaiian

end Hurford2007
