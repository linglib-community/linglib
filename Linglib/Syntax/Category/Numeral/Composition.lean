/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Nat.Hyperoperation
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.List.Nodup

/-!
# Hurford's universal numeral grammar

This file defines Hurford's phrase-structure grammar of numerals and his Packing Strategy, the
constraint that selects one well-formed numeral for each number. A NUMBER is *one* or a PHRASE,
optionally followed by another NUMBER, and denotes the sum of its parts. A PHRASE is a NUMBER
followed by an M and denotes their product. An M is a lexical base such as *ten*, or a NUMBER
followed by an M, and denotes the second raised to the power of the first. The Packing Strategy
requires the sister of every NUMBER to have the highest value the lexicon allows under the value
of the node above it. Dividing by the highest base that fits and treating quotient and remainder
the same way [builds a packed numeral](##Numeral.Number.packed_ofValue), and over bases with
distinct values [every packed numeral is built so](##Numeral.Number.Packed.ofValue_value).

## Main definitions

* `Number`, `Phrase`, `M`: the three categories, with their `value`s
* `M.IsHighestUnder`: the highest-valued lexical M under a ceiling
* `Number.Packed`, `Phrase.Packed`: the Packing Strategy relative to a lexicon of Ms
* `Number.ofValue`: the packed numeral of a given value

## Implementation notes

A base is a row of any number of marks above one. A lexicon is a list of Ms, taken as given, so
the Packing Strategy is checked at NUMBERs and PHRASEs only. `Number.Packed` bounds the M of a
PHRASE by the value of the NUMBER above it, which selects the same NUMBERs as Hurford's bound by
the PHRASE's own value. `Number.ofValue L 0` is the junk value *one*.

## References

* [hurford-1975]
* [hurford-2007]
-/

@[expose] public section

namespace Numeral

/-! ### The phrase-structure categories -/

mutual
/-- A NUMBER is *one* or a PHRASE, optionally followed by another NUMBER, rule (2a) of
[hurford-1975], p. 19. -/
inductive Number where
  /-- *one*, a single mark, is a NUMBER. -/
  | one : Number
  /-- *one* followed by a NUMBER is a NUMBER. -/
  | oneAnd (rest : Number) : Number
  /-- A PHRASE is a NUMBER. -/
  | phrase (p : Phrase) : Number
  /-- A PHRASE followed by a NUMBER is a NUMBER, as in *twenty-three*. -/
  | phraseAnd (p : Phrase) (rest : Number) : Number
  deriving DecidableEq, Repr

/-- A PHRASE is a NUMBER followed by an M, as in *two hundred*, rule (2b). -/
inductive Phrase where
  | mk (n : Number) (m : M) : Phrase
  deriving DecidableEq, Repr

/-- An M is a lexical base or a NUMBER followed by an M, as *hundred* is `[two ten]`, rule (2c). -/
inductive M where
  /-- A lexical base is a row of `b` marks, *ten* in English and 2, 5 or 20 in some other
  languages ([hurford-1975], p. 21). -/
  | base (b : ℕ) (hb : 1 < b := by decide) : M
  /-- A NUMBER followed by an M is an M. -/
  | mk (n : Number) (m : M) : M
  deriving DecidableEq, Repr
end

/-! ### The projection rules -/

mutual
/-- The value of a NUMBER is the sum of its immediate constituents, (23) of [hurford-1975],
pp. 29–30. -/
def Number.value : Number → ℕ
  | .one => 1
  | .oneAnd rest => 1 + rest.value
  | .phrase p => p.value
  | .phraseAnd p rest => p.value + rest.value

/-- The value of a PHRASE is the product of its immediate constituents. -/
def Phrase.value : Phrase → ℕ
  | .mk n m => n.value * m.value

/-- The value of an M is its second constituent raised to the power of its first. -/
def M.value : M → ℕ
  | .base b _ => b
  | .mk n m => m.value ^ n.value
end

/-- *ten* is the base of ten marks. -/
def M.ten : M := .base 10

@[simp] theorem M.value_ten : M.ten.value = 10 := rfl

/-! ### One operation at three levels

The single projection rule (29) of [hurford-1975], p. 34, values a node of depth `d` with
immediate constituents of values `x` and `y` as `CALCULATE+ d x y`, the depth being 1 at NUMBERs,
2 at PHRASEs and 3 at Ms by the convention (28). CALCULATE, (26) on p. 32, starts from `y` and
applies the operation of depth `d - 1` to it `x` times at depth 1 and `x - 1` times above, depth
0 being incrementing, so that for `x ≥ 1` it is `hyperoperation d y x`. Its fourth argument is
the sign `+`, which `-` replaces for the inverse operations. -/

theorem Number.value_phraseAnd_eq_hyperoperation (p : Phrase) (rest : Number) :
    (phraseAnd p rest).value = hyperoperation 1 rest.value p.value := by
  rw [hyperoperation_one, value, add_comm]

theorem Phrase.value_mk_eq_hyperoperation (n : Number) (m : M) :
    (mk n m).value = hyperoperation 2 m.value n.value := by
  rw [hyperoperation_two, value, mul_comm]

theorem M.value_mk_eq_hyperoperation (n : Number) (m : M) :
    (mk n m).value = hyperoperation 3 m.value n.value := by
  rw [hyperoperation_three, value]

/-! ### Values -/

theorem M.value_pos : ∀ m : M, 0 < m.value
  | .base _ hb => Nat.zero_lt_of_lt hb
  | .mk _ m => Nat.pow_pos m.value_pos

mutual
theorem Number.value_pos : ∀ n : Number, 0 < n.value
  | .one => Nat.one_pos
  | .oneAnd _ => Nat.add_pos_left Nat.one_pos _
  | .phrase p => p.value_pos
  | .phraseAnd p _ => Nat.add_pos_left p.value_pos _

theorem Phrase.value_pos : ∀ p : Phrase, 0 < p.value
  | .mk n m => Nat.mul_pos n.value_pos m.value_pos
end

theorem M.one_lt_value : ∀ m : M, 1 < m.value
  | .base _ hb => hb
  | .mk n m => m.one_lt_value.trans_le (Nat.le_self_pow n.value_pos.ne' _)

/-- `tally n` is the NUMBER `[one [one ... one]]` of `n + 1` marks, the structure of the digits
*one* to *nine* ([hurford-1975], p. 23). -/
def Number.tally : ℕ → Number
  | 0 => .one
  | n + 1 => .oneAnd (tally n)

@[simp] theorem Number.value_tally (n : ℕ) : (tally n).value = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tally, value, ih, add_comm]

theorem Number.range_value : Set.range value = {n | 0 < n} := by
  ext n
  refine ⟨fun ⟨e, he⟩ ↦ he ▸ e.value_pos, fun hn ↦ ⟨tally (n - 1), ?_⟩⟩
  simp only [value_tally]
  exact Nat.sub_add_cancel hn

/-- `tenPow k` is the M of value `10 ^ (k + 1)`, *ten* or `[k + 1 ten]`, *thousand* being
`[three ten]` ([hurford-1975], p. 23). -/
def M.tenPow : ℕ → M
  | 0 => .ten
  | k + 1 => .mk (.tally (k + 1)) .ten

@[simp] theorem M.value_tenPow (k : ℕ) : (tenPow k).value = 10 ^ (k + 1) := by
  cases k with
  | zero => rfl
  | succ k => simp [tenPow, value]

theorem Phrase.value_tally_tenPow (m k : ℕ) :
    (Phrase.mk (.tally m) (.tenPow k)).value = (m + 1) * 10 ^ (k + 1) := by
  simp [value]

/-! ### The Packing Strategy -/

variable {L : List M} {v : ℕ} {m : M} {e : Number}

/-- `m` is the highest-valued M of the lexicon `L` whose value does not exceed the ceiling `v`. -/
structure M.IsHighestUnder (L : List M) (v : ℕ) (m : M) : Prop where
  mem : m ∈ L
  value_le : m.value ≤ v
  le_value : ∀ m' ∈ L, m'.value ≤ v → m'.value ≤ m.value

instance M.decidableIsHighestUnder (L : List M) (v : ℕ) (m : M) :
    Decidable (m.IsHighestUnder L v) :=
  decidable_of_iff (m ∈ L ∧ m.value ≤ v ∧ ∀ m' ∈ L, m'.value ≤ v → m'.value ≤ m.value)
    ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

/-- `highestUnder L v` is an M of `L` of the highest value not above `v`, if any M fits. -/
def M.highestUnder (L : List M) (v : ℕ) : Option M :=
  (L.filter (·.value ≤ v)).argmax value

theorem M.highestUnder_eq_none : highestUnder L v = none ↔ ∀ m ∈ L, v < m.value := by
  simp [highestUnder, List.filter_eq_nil_iff]

theorem M.isHighestUnder_of_highestUnder_eq_some (h : highestUnder L v = some m) :
    m.IsHighestUnder L v :=
  have hm := List.mem_filter.1 (List.argmax_mem h)
  ⟨hm.1, by simpa using hm.2,
    fun _ hm' hv ↦ List.le_of_mem_argmax (List.mem_filter.2 ⟨hm', by simpa using hv⟩) h⟩

theorem M.IsHighestUnder.highestUnder_eq (hL : (L.map value).Nodup) (h : m.IsHighestUnder L v) :
    highestUnder L v = some m := by
  cases h' : highestUnder L v with
  | none => exact absurd h.value_le (highestUnder_eq_none.1 h' m h.mem).not_ge
  | some m' =>
    have hm' := isHighestUnder_of_highestUnder_eq_some h'
    exact congrArg some (List.inj_on_of_nodup_map hL hm'.mem h.mem
      ((h.le_value m' hm'.mem hm'.value_le).antisymm (hm'.le_value m h.mem h.value_le)))

/-- A NUMBER is packed relative to the lexicon `L` when the sister of every NUMBER in it has the
highest possible value, the Packing Strategy (82) of [hurford-1975], p. 67. After *one* that holds
only where no lexical M fits under the whole; a PHRASE sister has the highest lexical M under the
NUMBER's value, and leaves a remainder below that M. -/
def Number.Packed (L : List M) : Number → Prop
  | .one => True
  | .oneAnd rest => (∀ m ∈ L, 1 + rest.value < m.value) ∧ rest.Packed L
  | .phrase (.mk n m) => m.IsHighestUnder L (n.value * m.value) ∧ n.Packed L
  | .phraseAnd (.mk n m) rest =>
      m.IsHighestUnder L (n.value * m.value + rest.value) ∧ rest.value < m.value ∧
        n.Packed L ∧ rest.Packed L

/-- The Packing Strategy is decidable. -/
instance Number.decidablePacked (L : List M) : DecidablePred (Packed L)
  | .one => inferInstanceAs (Decidable True)
  | .oneAnd r =>
    haveI := decidablePacked L r
    inferInstanceAs (Decidable ((∀ m ∈ L, 1 + r.value < m.value) ∧ r.Packed L))
  | .phrase (.mk n m) =>
    haveI := decidablePacked L n
    inferInstanceAs (Decidable (m.IsHighestUnder L (n.value * m.value) ∧ n.Packed L))
  | .phraseAnd (.mk n m) r =>
    haveI := decidablePacked L n
    haveI := decidablePacked L r
    inferInstanceAs (Decidable (m.IsHighestUnder L (n.value * m.value + r.value) ∧
      r.value < m.value ∧ n.Packed L ∧ r.Packed L))

theorem Number.packed_tally_iff {n : ℕ} : (tally n).Packed L ↔ ∀ m ∈ L, n + 1 < m.value := by
  induction n with
  | zero =>
    simp only [tally, Packed, true_iff]
    exact fun m _ ↦ by have := m.one_lt_value; omega
  | succ n ih =>
    simp only [tally, Packed, value_tally, ih]
    exact ⟨fun h m hm ↦ by have := h.1 m hm; omega,
      fun h ↦ ⟨fun m hm ↦ by have := h m hm; omega, fun m hm ↦ by have := h m hm; omega⟩⟩

theorem Number.Packed.eq_tally : ∀ {e : Number}, e.Packed L → (∀ m ∈ L, e.value < m.value) →
    e = tally (e.value - 1)
  | .one, _, _ => rfl
  | .oneAnd r, ⟨_, hr⟩, hlow => by
    have hr' := hr.eq_tally fun m hm ↦ by have := hlow m hm; simp only [value] at this; omega
    obtain ⟨k, hk⟩ : ∃ k, r.value = k + 1 := ⟨r.value - 1, by have := r.value_pos; omega⟩
    simp only [value, hk, Nat.add_sub_cancel] at hr' ⊢
    rw [show 1 + (k + 1) - 1 = k + 1 by omega, hr']
    rfl
  | .phrase (.mk _ m), ⟨hm, _⟩, hlow => absurd (hlow m hm.mem) hm.value_le.not_gt
  | .phraseAnd (.mk _ m) _, ⟨hm, _⟩, hlow => absurd (hlow m hm.mem) hm.value_le.not_gt

/-! ### The packed numeral of a value -/

/-- `ofValue L v` is the packed NUMBER of value `v` over the lexicon `L`. Where no M fits under
`v` it is a tally; otherwise it is as many of the highest M that fits as go into `v`, followed by
the remainder, the multiplier and the remainder being built the same way. -/
def Number.ofValue (L : List M) (v : ℕ) : Number :=
  match h : M.highestUnder L v with
  | none => tally (v - 1)
  | some m =>
    if v % m.value = 0 then phrase (.mk (ofValue L (v / m.value)) m)
    else phraseAnd (.mk (ofValue L (v / m.value)) m) (ofValue L (v % m.value))
termination_by v
decreasing_by
  all_goals
    have := m.one_lt_value
    have := (M.isHighestUnder_of_highestUnder_eq_some h).value_le
  · exact Nat.div_lt_self (by omega) ‹1 < m.value›
  · exact Nat.div_lt_self (by omega) ‹1 < m.value›
  · exact (Nat.mod_lt _ (by omega)).trans_le this

theorem Number.ofValue_of_forall_lt (h : ∀ m ∈ L, v < m.value) : ofValue L v = tally (v - 1) := by
  rw [ofValue]
  split
  · rfl
  · next m hm =>
    have hm := M.isHighestUnder_of_highestUnder_eq_some hm
    exact absurd hm.value_le (h m hm.mem).not_ge

theorem Number.ofValue_of_highestUnder_eq_some (h : M.highestUnder L v = some m) :
    ofValue L v = if v % m.value = 0 then phrase (.mk (ofValue L (v / m.value)) m)
      else phraseAnd (.mk (ofValue L (v / m.value)) m) (ofValue L (v % m.value)) := by
  rw [ofValue]
  split
  · next h' => simp [h] at h'
  · next m' h' => obtain rfl : m' = m := Option.some.inj (h'.symm.trans h); rfl

private theorem Number.ofValue_spec (L : List M) (hv : 0 < v) :
    (ofValue L v).Packed L ∧ (ofValue L v).value = v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  cases h : M.highestUnder L v with
  | none =>
    have hlow := M.highestUnder_eq_none.1 h
    rw [ofValue_of_forall_lt hlow, value_tally, packed_tally_iff]
    exact ⟨fun m hm ↦ by have := hlow m hm; omega, by omega⟩
  | some m =>
    have hm := M.isHighestUnder_of_highestUnder_eq_some h
    have h1 := m.one_lt_value
    have hmv := hm.value_le
    obtain ⟨hn, hnv⟩ := ih (v / m.value) (Nat.div_lt_self hv h1) (Nat.div_pos hmv (by omega))
    rw [ofValue_of_highestUnder_eq_some h]
    split_ifs with hr
    · simp only [Packed, value, Phrase.value, hnv, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hr),
        and_true]
      exact ⟨hm, hn⟩
    · obtain ⟨hr', hrv⟩ := ih (v % m.value) ((Nat.mod_lt _ (by omega)).trans_le hmv) (by omega)
      simp only [Packed, value, Phrase.value, hnv, hrv, Nat.div_add_mod', and_true]
      exact ⟨hm, Nat.mod_lt _ m.value_pos, hn, hr'⟩

/-- The numeral built by dividing by the highest base that fits is packed. -/
theorem Number.packed_ofValue (L : List M) (hv : 0 < v) : (ofValue L v).Packed L :=
  (ofValue_spec L hv).1

@[simp] theorem Number.value_ofValue (L : List M) (hv : 0 < v) : (ofValue L v).value = v :=
  (ofValue_spec L hv).2

/-- Over Ms with distinct values, a packed NUMBER is the one built from its value: its M is the
highest that fits, its multiplier the quotient and its remainder the remainder. -/
theorem Number.Packed.ofValue_value (hL : (L.map M.value).Nodup) :
    ∀ {e : Number}, e.Packed L → ofValue L e.value = e
  | .one, he => by
    exact ofValue_of_forall_lt fun m _ ↦ m.one_lt_value
  | .oneAnd r, he => by
    have hlow : ∀ m ∈ L, (oneAnd r).value < m.value := he.1
    rw [ofValue_of_forall_lt hlow, ← he.eq_tally hlow]
  | .phrase (.mk n m), ⟨hm, hn⟩ => by
    change ofValue L (n.value * m.value) = _
    rw [ofValue_of_highestUnder_eq_some (hm.highestUnder_eq hL)]
    simp only [Nat.mul_mod_left, ite_true, Nat.mul_div_cancel _ m.value_pos, hn.ofValue_value hL]
  | .phraseAnd (.mk n m) r, ⟨hm, hr, hn, hrp⟩ => by
    change ofValue L (n.value * m.value + r.value) = _
    rw [ofValue_of_highestUnder_eq_some (hm.highestUnder_eq hL)]
    have hmod : (n.value * m.value + r.value) % m.value = r.value := by
      rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hr]
    have hdiv : (n.value * m.value + r.value) / m.value = n.value := by
      rw [Nat.mul_comm, Nat.mul_add_div m.value_pos, Nat.div_eq_of_lt hr, Nat.add_zero]
    simp only [hmod, hdiv, r.value_pos.ne', ite_false, hn.ofValue_value hL, hrp.ofValue_value hL]

theorem Number.Packed.eq_of_value_eq (hL : (L.map M.value).Nodup) {e e' : Number}
    (he : e.Packed L) (he' : e'.Packed L) (h : e.value = e'.value) : e = e' := by
  rw [← he.ofValue_value hL, h, he'.ofValue_value hL]

/-- Given Ms with distinct values, every positive number has exactly one packed NUMBER, as (82)
requires ([hurford-1975], p. 75). -/
theorem Number.existsUnique_packed (hL : (L.map M.value).Nodup) (hv : 0 < v) :
    ∃! e : Number, e.Packed L ∧ e.value = v :=
  ⟨ofValue L v, ⟨packed_ofValue L hv, value_ofValue L hv⟩, fun _ ⟨he, h⟩ ↦
    he.eq_of_value_eq hL (packed_ofValue L hv) (h.trans (value_ofValue L hv).symm)⟩

/-! ### Hurford's formulation

[hurford-1975]'s (82) rules out a node of value `x` whose daughters are a NUMBER and a sister of
value `y` when some well-formed structure of a category other than NUMBER that the node expands
to has a value `z` with `y < z ≤ x`. At a PHRASE the sister is its M, so (82) is `Phrase.Packed`;
at a NUMBER the sister is a single mark or a PHRASE, and (82) agrees with `Number.Packed`. -/

/-- A PHRASE is packed relative to `L` when its M is the highest lexical M under its value and its
NUMBER is packed. -/
def Phrase.Packed (L : List M) : Phrase → Prop
  | .mk n m => m.IsHighestUnder L (n.value * m.value) ∧ n.Packed L

@[simp] theorem Number.packed_phrase_iff {p : Phrase} : (phrase p).Packed L ↔ p.Packed L := by
  cases p; rfl

theorem Phrase.packed_mk_one {m : M} (hm : m ∈ L) : (mk .one m).Packed L :=
  ⟨⟨hm, by simp [Number.value], fun _ _ h ↦ by simpa [Number.value] using h⟩, trivial⟩

/-- A mark is the sister of a NUMBER in a packed NUMBER exactly when no packed PHRASE fits under
the whole. -/
theorem Number.packed_oneAnd_iff {r : Number} :
    (oneAnd r).Packed L ↔
      r.Packed L ∧ ∀ q : Phrase, q.Packed L → q.value ≤ (oneAnd r).value → q.value ≤ 1 := by
  simp only [Packed, Number.value]
  refine ⟨fun ⟨hlow, hr⟩ ↦ ⟨hr, fun ⟨n, m⟩ ⟨hm, _⟩ hq ↦ ?_⟩, fun ⟨hr, hq⟩ ↦ ⟨fun m hm ↦ ?_, hr⟩⟩
  · have := hlow m hm.mem
    have := Nat.le_mul_of_pos_left m.value n.value_pos
    simp only [Phrase.value] at hq ⊢
    omega
  · by_contra hmv
    have := hq _ (Phrase.packed_mk_one hm) (by simp only [Phrase.value, Number.value]; omega)
    simp only [Phrase.value, Number.value, one_mul] at this
    have := m.one_lt_value
    omega

/-- A PHRASE is the sister of a NUMBER in a packed NUMBER exactly when it is packed and no packed
PHRASE has a higher value not above the whole. -/
theorem Number.packed_phraseAnd_iff {p : Phrase} {r : Number} :
    (phraseAnd p r).Packed L ↔ p.Packed L ∧ r.Packed L ∧
      ∀ q : Phrase, q.Packed L → q.value ≤ (phraseAnd p r).value → q.value ≤ p.value := by
  obtain ⟨n, m⟩ := p
  simp only [Packed, Number.value, Phrase.value]
  have h1 := m.one_lt_value
  have hnm := Nat.le_mul_of_pos_left m.value n.value_pos
  constructor
  · rintro ⟨hm, hr, hn, hrp⟩
    obtain ⟨hmL, -, hub⟩ := hm
    refine ⟨⟨⟨hmL, hnm, fun m' hm' h ↦ hub m' hm' (by omega)⟩, hn⟩, hrp,
      fun ⟨n', m'⟩ ⟨hm', _⟩ hq ↦ ?_⟩
    simp only [Phrase.value] at hq ⊢
    obtain ⟨hm'L, hm'v, hub'⟩ := hm'
    by_cases hle : m.value ≤ n'.value * m'.value
    · have hmm : m'.value = m.value :=
        le_antisymm (hub m' hm'L (by omega)) (hub' m hmL hle)
      rw [hmm] at hq ⊢
      have : n'.value * m.value < (n.value + 1) * m.value := by rw [Nat.succ_mul]; omega
      exact Nat.mul_le_mul_right _ (by have := Nat.lt_of_mul_lt_mul_right this; omega)
    · omega
  · rintro ⟨⟨hm, hn⟩, hrp, hq⟩
    obtain ⟨hmL, -, hub⟩ := hm
    have hhigh : ∀ m' ∈ L, m'.value ≤ n.value * m.value + r.value → m'.value ≤ m.value := by
      intro m' hm' h
      by_contra hlt
      have hq' := hq _ (Phrase.packed_mk_one hm') (by simp only [Phrase.value, Number.value]; omega)
      simp only [Phrase.value, Number.value, one_mul] at hq'
      exact hlt (hub m' hm' hq')
    refine ⟨⟨hmL, by omega, hhigh⟩, lt_of_not_ge fun hr ↦ ?_, hn, hrp⟩
    obtain ⟨k, hk, hkv⟩ : ∃ k : Number, k.Packed L ∧ k.value = n.value + 1 :=
      ⟨_, packed_ofValue L n.value.succ_pos, value_ofValue L n.value.succ_pos⟩
    have hkm : k.value * m.value ≤ n.value * m.value + r.value := by rw [hkv, Nat.succ_mul]; omega
    have hq' := hq ⟨k, m⟩
      ⟨⟨hmL, Nat.le_mul_of_pos_left _ k.value_pos, fun m' hm' h ↦ hhigh m' hm' (h.trans hkm)⟩,
        hk⟩ hkm
    simp only [Phrase.value, hkv, Nat.succ_mul] at hq'
    omega

end Numeral
