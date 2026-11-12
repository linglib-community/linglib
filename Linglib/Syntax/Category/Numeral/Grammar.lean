/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.List.Nodup
public import Mathlib.Order.Defs.Unbundled

/-!
# The grammar of numerals

A recursive numeral system builds its numerals from two stocks of morphemes, the digits and the
multipliers, by Hurford's phrase-structure rules: a NUMBER is a digit or a PHRASE, optionally
followed by another NUMBER, and denotes the sum of its parts; a PHRASE is a multiplier, optionally
preceded by a NUMBER, and denotes their product. The rules generate many numerals for each
number. Hurford's Packing Strategy selects among them by requiring the sister of every NUMBER to
have the highest value the multipliers allow under the value of the node above it. Dividing by
the highest multiplier that fits and treating quotient and remainder the same way [builds a packed
numeral](##Numeral.Number.packed_ofValue), and where the digits are a counting sequence and the
multipliers have distinct values [every packed numeral is built
so](##Numeral.Number.Packed.ofValue_value), up to whether *one* is pronounced before a multiplier.

## Main definitions

* `Number α`, `Phrase α`: the two categories over morphemes `α`, with `value` and `yield`
* `Number.Generated`: the numerals over given digits and multipliers
* `IsHighestUnder`: a multiplier of the highest value under a ceiling
* `Number.Packed`, `Phrase.Packed`: the Packing Strategy
* `Number.ofValue`: the packed numeral of a given value
* `Number.deleteOne`: the numeral with every *one* before a multiplier unpronounced

## Implementation notes

The leaves of a numeral are morphemes, and a function `v` gives the number each denotes, so the
same numeral can be read over a language's words or over bare numbers. Digits and multipliers are
lists; the theorems about `ofValue` take the digits to be a counting sequence, the word at
position `k` denoting `k + 1`. `ofValue` returns a junk digit where the digits run out. The
rule PHRASE − NUMBER of the later literature is not included.

## References

* [hurford-1975]
* [hurford-2007]
* [denic-szymanik-2024]
-/

@[expose] public section

namespace Numeral

universe u

variable {α : Type u}

/-! ### The phrase-structure categories -/

mutual
/-- A NUMBER is a digit or a PHRASE, optionally followed by another NUMBER. -/
inductive Number (α : Type u) where
  /-- A digit is a NUMBER. -/
  | digit (d : α) : Number α
  /-- A PHRASE is a NUMBER. -/
  | phrase (p : Phrase α) : Number α
  /-- A PHRASE followed by a NUMBER is a NUMBER, as in *twenty-three*. -/
  | add (p : Phrase α) (n : Number α) : Number α
  deriving DecidableEq, Repr

/-- A PHRASE is a multiplier, optionally preceded by a NUMBER, as in *two hundred*. -/
inductive Phrase (α : Type u) where
  /-- A multiplier is a PHRASE, as *ten* is. -/
  | base (m : α) : Phrase α
  /-- A NUMBER followed by a multiplier is a PHRASE. -/
  | mul (n : Number α) (m : α) : Phrase α
  deriving DecidableEq, Repr
end

/-- The multiplier a PHRASE is built on. -/
def Phrase.head : Phrase α → α
  | .base m | .mul _ m => m

mutual
/-- The morphemes of a NUMBER in order. -/
def Number.yield : Number α → List α
  | .digit d => [d]
  | .phrase p => p.yield
  | .add p n => p.yield ++ n.yield

/-- The morphemes of a PHRASE in order. -/
def Phrase.yield : Phrase α → List α
  | .base m => [m]
  | .mul n m => n.yield ++ [m]
end

variable (v : α → ℕ) (D M : List α)

mutual
/-- The value of a NUMBER is the sum of its immediate constituents, where `v` gives the values of
the morphemes. -/
def Number.value : Number α → ℕ
  | .digit d => v d
  | .phrase p => p.value
  | .add p n => p.value + n.value

/-- The value of a PHRASE is the product of its immediate constituents. -/
def Phrase.value : Phrase α → ℕ
  | .base m => v m
  | .mul n m => n.value * v m
end

mutual
/-- A NUMBER is generated from the digits `D` and the multipliers `M`. -/
def Number.Generated : Number α → Prop
  | .digit d => d ∈ D
  | .phrase p => p.Generated
  | .add p n => p.Generated ∧ n.Generated

/-- A PHRASE is generated from the digits `D` and the multipliers `M`. -/
def Phrase.Generated : Phrase α → Prop
  | .base m => m ∈ M
  | .mul n m => n.Generated ∧ m ∈ M
end

mutual
/-- Whether a NUMBER is generated from given digits and multipliers is decidable. -/
def Number.decGenerated [DecidableEq α] : (e : Number α) → Decidable (e.Generated D M)
  | .digit d => inferInstanceAs (Decidable (d ∈ D))
  | .phrase p => Phrase.decGenerated p
  | .add p n =>
    haveI := Phrase.decGenerated p
    haveI := Number.decGenerated n
    inferInstanceAs (Decidable (p.Generated D M ∧ n.Generated D M))

/-- Whether a PHRASE is generated from given digits and multipliers is decidable. -/
def Phrase.decGenerated [DecidableEq α] : (p : Phrase α) → Decidable (p.Generated D M)
  | .base m => inferInstanceAs (Decidable (m ∈ M))
  | .mul n m =>
    haveI := Number.decGenerated n
    inferInstanceAs (Decidable (n.Generated D M ∧ m ∈ M))
end

instance [DecidableEq α] : DecidablePred (Number.Generated D M) := Number.decGenerated D M

/-- How many of its multiplier a PHRASE counts. -/
def Phrase.count : Phrase α → ℕ
  | .base _ => 1
  | .mul n _ => n.value v

variable {v D M} {x : ℕ} {m : α} {e e' : Number α} {p : Phrase α}

theorem Phrase.value_eq_count_mul : ∀ p : Phrase α, p.value v = p.count v * v p.head
  | .base _ => (Nat.one_mul _).symm
  | .mul _ _ => rfl

/-! ### The Packing Strategy -/

variable (v M) in
/-- `m` is a multiplier of the highest value not above the ceiling `x`. -/
def IsHighestUnder (x : ℕ) (m : α) : Prop :=
  MaximalFor (fun m ↦ m ∈ M ∧ v m ≤ x) v m

theorem isHighestUnder_iff :
    IsHighestUnder v M x m ↔ m ∈ M ∧ v m ≤ x ∧ ∀ m' ∈ M, v m' ≤ x → v m' ≤ v m :=
  ⟨fun h ↦ ⟨h.1.1, h.1.2, fun m' hm' hx ↦ (le_total (v m) (v m')).elim (h.2 ⟨hm', hx⟩) id⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨⟨h₁, h₂⟩, fun j hj _ ↦ h₃ j hj.1 hj.2⟩⟩

theorem IsHighestUnder.mem (h : IsHighestUnder v M x m) : m ∈ M := h.1.1

theorem IsHighestUnder.value_le (h : IsHighestUnder v M x m) : v m ≤ x := h.1.2

theorem IsHighestUnder.le_value (h : IsHighestUnder v M x m) {m' : α} (hm' : m' ∈ M)
    (hx : v m' ≤ x) : v m' ≤ v m :=
  (isHighestUnder_iff.1 h).2.2 m' hm' hx

theorem isHighestUnder_self (hm : m ∈ M) : IsHighestUnder v M (v m) m :=
  isHighestUnder_iff.2 ⟨hm, le_rfl, fun _ _ h ↦ h⟩

/-- A multiplier that is highest under a ceiling is highest under any lower ceiling it fits. -/
theorem IsHighestUnder.of_le {y : ℕ} (h : IsHighestUnder v M x m) (hy : y ≤ x) (hm : v m ≤ y) :
    IsHighestUnder v M y m :=
  isHighestUnder_iff.2 ⟨h.mem, hm, fun _ hm' h' ↦ h.le_value hm' (h'.trans hy)⟩

/-- Raising the ceiling by one changes the highest multiplier only where a multiplier has exactly
the new value. -/
theorem IsHighestUnder.succ (h : IsHighestUnder v M x m) (hx : ∀ m' ∈ M, v m' ≠ x + 1) :
    IsHighestUnder v M (x + 1) m :=
  isHighestUnder_iff.2 ⟨h.mem, h.value_le.trans x.le_succ, fun m' hm' h' ↦
    h.le_value hm' (Nat.lt_succ_iff.1 (lt_of_le_of_ne h' (hx m' hm')))⟩

instance (x : ℕ) (m : α) [DecidableEq α] : Decidable (IsHighestUnder v M x m) :=
  decidable_of_iff _ isHighestUnder_iff.symm

variable (v M) in
/-- `highestUnder v M x` is a multiplier of the highest value not above `x`, if any fits. -/
def highestUnder (x : ℕ) : Option α :=
  (M.filter (v · ≤ x)).argmax v

theorem highestUnder_eq_none : highestUnder v M x = none ↔ ∀ m ∈ M, x < v m := by
  simp [highestUnder, List.filter_eq_nil_iff]

theorem isHighestUnder_of_highestUnder_eq_some (h : highestUnder v M x = some m) :
    IsHighestUnder v M x m :=
  have hm := List.mem_filter.1 (List.argmax_mem h)
  isHighestUnder_iff.2 ⟨hm.1, by simpa using hm.2,
    fun _ hm' hx ↦ List.le_of_mem_argmax (List.mem_filter.2 ⟨hm', by simpa using hx⟩) h⟩

theorem IsHighestUnder.highestUnder_eq (hM : (M.map v).Nodup) (h : IsHighestUnder v M x m) :
    highestUnder v M x = some m := by
  cases h' : highestUnder v M x with
  | none => exact absurd h.value_le (highestUnder_eq_none.1 h' m h.mem).not_ge
  | some m' =>
    have hm' := isHighestUnder_of_highestUnder_eq_some h'
    exact congrArg some (List.inj_on_of_nodup_map hM hm'.mem h.mem
      ((h.le_value hm'.mem hm'.value_le).antisymm (hm'.le_value h.mem h.value_le)))

variable (v M) in
mutual
/-- A NUMBER is packed when the sister of every NUMBER in it has the highest possible value,
the Packing Strategy (82) of [hurford-1975], p. 67. A digit is packed only where no multiplier
fits under it; a PHRASE followed by a NUMBER has the highest multiplier under the value of the
whole, and leaves a remainder below that multiplier. -/
def Number.Packed : Number α → Prop
  | .digit d => ∀ m ∈ M, v d < v m
  | .phrase p => p.Packed
  | .add p n => p.Packed ∧ n.Packed ∧ IsHighestUnder v M (p.value v + n.value v) p.head ∧
      n.value v < v p.head

/-- A PHRASE is packed when its multiplier is the highest under its value and its NUMBER is
packed. -/
def Phrase.Packed : Phrase α → Prop
  | .base m => IsHighestUnder v M (v m) m
  | .mul n m => IsHighestUnder v M (n.value v * v m) m ∧ n.Packed
end

mutual
/-- The Packing Strategy is decidable. -/
def Number.decPacked [DecidableEq α] : (e : Number α) → Decidable (e.Packed v M)
  | .digit d => inferInstanceAs (Decidable (∀ m ∈ M, v d < v m))
  | .phrase p => Phrase.decPacked p
  | .add p n =>
    haveI := Phrase.decPacked p
    haveI := Number.decPacked n
    inferInstanceAs (Decidable (p.Packed v M ∧ n.Packed v M ∧
      IsHighestUnder v M (p.value v + n.value v) p.head ∧ n.value v < v p.head))

/-- The Packing Strategy is decidable. -/
def Phrase.decPacked [DecidableEq α] : (p : Phrase α) → Decidable (p.Packed v M)
  | .base m => inferInstanceAs (Decidable (IsHighestUnder v M (v m) m))
  | .mul n m =>
    haveI := Number.decPacked n
    inferInstanceAs (Decidable (IsHighestUnder v M (n.value v * v m) m ∧ n.Packed v M))
end

instance [DecidableEq α] : DecidablePred (Number.Packed v M) := Number.decPacked

instance [DecidableEq α] : DecidablePred (Phrase.Packed v M) := Phrase.decPacked

theorem Phrase.Packed.isHighestUnder : ∀ {p : Phrase α}, p.Packed v M →
    IsHighestUnder v M (p.value v) p.head
  | .base _, h => h
  | .mul _ _, h => h.1

/-! ### One before a multiplier -/

variable (v) in
mutual
/-- `deleteOne` leaves every *one* before a multiplier unpronounced, so that `[one M]` is the
bare multiplier, Hurford's 1-Deletion. -/
def Number.deleteOne : Number α → Number α
  | .digit d => .digit d
  | .phrase p => .phrase p.deleteOne
  | .add p n => .add p.deleteOne n.deleteOne

/-- `deleteOne` on a PHRASE. -/
def Phrase.deleteOne : Phrase α → Phrase α
  | .base m => .base m
  | .mul n m => if n.value v = 1 then .base m else .mul n.deleteOne m
end

/-! ### The packed numeral of a value -/

variable (v D M) in
/-- `ofValue v D M x` is the packed NUMBER of value `x`. Where no multiplier fits under `x` it
is the digit at position `x` of the counting sequence `D`; otherwise it is as many of the highest
multiplier that fits as go into `x`, followed by the remainder, the count and the remainder
being built the same way and a count of one being left unpronounced. -/
def Number.ofValue [Inhabited α] (x : ℕ) : Number α :=
  match h : highestUnder v M x with
  | none => .digit (D.getI (x - 1))
  | some m =>
    if _ : 1 < v m then
      let p : Phrase α := if x / v m = 1 then .base m else .mul (ofValue (x / v m)) m
      if x % v m = 0 then .phrase p else .add p (ofValue (x % v m))
    else .digit m
termination_by x
decreasing_by
  all_goals have := (isHighestUnder_of_highestUnder_eq_some h).value_le
  · exact Nat.div_lt_self (by omega) ‹1 < v m›
  · exact (Nat.mod_lt _ (by omega)).trans_le this

variable (v D M) in
/-- The digits `D` and the multipliers `M` form a numeral system under `v` when the digits are a
counting sequence, the word at position `k` denoting `k + 1`, that reaches a multiplier, and the
multipliers denote distinct numbers above one. -/
structure IsSystem : Prop where
  value_getElem : ∀ k (h : k < D.length), v D[k] = k + 1
  one_lt_value : ∀ m ∈ M, 1 < v m
  exists_value_le : ∃ m ∈ M, v m ≤ D.length + 1
  nodup : (M.map v).Nodup

section ofValue

variable [Inhabited α]

theorem Number.ofValue_of_forall_lt (h : ∀ m ∈ M, x < v m) :
    ofValue v D M x = .digit (D.getI (x - 1)) := by
  rw [ofValue]
  split
  · rfl
  · next m hm =>
    have hm := isHighestUnder_of_highestUnder_eq_some hm
    exact absurd hm.value_le (h m hm.mem).not_ge

theorem Number.ofValue_of_highestUnder_eq_some (h : highestUnder v M x = some m) (h1 : 1 < v m) :
    ofValue v D M x =
      if x % v m = 0 then
        .phrase (if x / v m = 1 then .base m else .mul (ofValue v D M (x / v m)) m)
      else .add (if x / v m = 1 then .base m else .mul (ofValue v D M (x / v m)) m)
        (ofValue v D M (x % v m)) := by
  rw [ofValue]
  split
  · next h' => simp [h] at h'
  · next m' h' =>
    obtain rfl : m' = m := Option.some.inj (h'.symm.trans h)
    simp only [h1, dite_true]

/-- The numeral built on `c` of the multiplier `m` and a remainder `r` below `m`. -/
theorem Number.ofValue_mul_add (hS : IsSystem v D M) {c r : ℕ}
    (hm : IsHighestUnder v M (c * v m + r) m) (hr : r < v m) :
    ofValue v D M (c * v m + r) =
      if r = 0 then .phrase (if c = 1 then .base m else .mul (ofValue v D M c) m)
      else .add (if c = 1 then .base m else .mul (ofValue v D M c) m) (ofValue v D M r) := by
  have h1 := hS.one_lt_value m hm.mem
  rw [ofValue_of_highestUnder_eq_some (hm.highestUnder_eq hS.nodup) h1, Nat.mul_add_mod',
    Nat.mod_eq_of_lt hr, Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr,
    Nat.add_zero]

private theorem Number.ofValue_spec (hS : IsSystem v D M) (hx : 0 < x) :
    (ofValue v D M x).Packed v M ∧ (ofValue v D M x).value v = x ∧
      (ofValue v D M x).Generated D M := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  cases h : highestUnder v M x with
  | none =>
    have hlow := highestUnder_eq_none.1 h
    obtain ⟨m₀, hm₀, hm₀D⟩ := hS.exists_value_le
    have hk : x - 1 < D.length := by have := hlow m₀ hm₀; omega
    rw [ofValue_of_forall_lt hlow, List.getI_eq_getElem _ hk]
    refine ⟨fun m hm ↦ ?_, ?_, List.getElem_mem hk⟩
    · rw [hS.value_getElem]; have := hlow m hm; omega
    · rw [Number.value, hS.value_getElem]; omega
  | some m =>
    have hm := isHighestUnder_of_highestUnder_eq_some h
    have h1 := hS.one_lt_value m hm.mem
    have hmx := hm.value_le
    have hq : 0 < x / v m := Nat.div_pos hmx (by omega)
    obtain ⟨hqp, hqv, hqg⟩ := ih (x / v m) (Nat.div_lt_self hx h1) hq
    have hP : ∀ p : Phrase α,
        p = (if x / v m = 1 then .base m else .mul (ofValue v D M (x / v m)) m) →
        p.Packed v M ∧ p.value v = x / v m * v m ∧ p.Generated D M ∧ p.head = m := by
      rintro p rfl
      split_ifs with hq1
      · exact ⟨isHighestUnder_self hm.mem, by rw [hq1, Nat.one_mul]; rfl, hm.mem, rfl⟩
      · refine ⟨⟨?_, hqp⟩, by rw [Phrase.value, hqv], ⟨hqg, hm.mem⟩, rfl⟩
        rw [hqv]
        exact hm.of_le (Nat.div_mul_le_self x _) (Nat.le_mul_of_pos_left _ hq)
    obtain ⟨hpp, hpv, hpg, hph⟩ := hP _ rfl
    rw [ofValue_of_highestUnder_eq_some h h1]
    by_cases hr : x % v m = 0
    · simp only [hr, ↓reduceIte]
      exact ⟨hpp, by rw [Number.value, hpv, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hr)], hpg⟩
    · simp only [hr, ↓reduceIte]
      obtain ⟨hrp, hrv, hrg⟩ := ih (x % v m) ((Nat.mod_lt _ (by omega)).trans_le hmx) (by omega)
      refine ⟨⟨hpp, hrp, ?_, ?_⟩, by rw [Number.value, hpv, hrv, Nat.div_add_mod'], hpg, hrg⟩
      · rw [hpv, hrv, hph, Nat.div_add_mod']; exact hm
      · rw [hrv, hph]; exact Nat.mod_lt _ (by omega)

/-- The numeral built by dividing by the highest multiplier that fits is packed. -/
theorem Number.packed_ofValue (hS : IsSystem v D M) (hx : 0 < x) :
    (ofValue v D M x).Packed v M :=
  (ofValue_spec hS hx).1

@[simp] theorem Number.value_ofValue (hS : IsSystem v D M) (hx : 0 < x) :
    (ofValue v D M x).value v = x :=
  (ofValue_spec hS hx).2.1

theorem Number.generated_ofValue (hS : IsSystem v D M) (hx : 0 < x) :
    (ofValue v D M x).Generated D M :=
  (ofValue_spec hS hx).2.2

end ofValue

theorem Number.value_pos (hS : IsSystem v D M) :
    ∀ {e : Number α}, e.Generated D M → 0 < e.value v
  | .digit d, hg => by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
    rw [Number.value, hS.value_getElem]; omega
  | .phrase (.base m), hg => Nat.zero_lt_of_lt (hS.one_lt_value m hg)
  | .phrase (.mul _ m), hg =>
    Nat.mul_pos (value_pos hS hg.1) (Nat.zero_lt_of_lt (hS.one_lt_value m hg.2))
  | .add _ _, hg => Nat.add_pos_right _ (value_pos hS hg.2)

/-- In a numeral system a packed NUMBER is the one built from its value, up to whether *one* is
pronounced before a multiplier: its multiplier is the highest that fits, its count the quotient
and its remainder the remainder. -/
theorem Number.Packed.ofValue_value [Inhabited α] (hS : IsSystem v D M) :
    ∀ {e : Number α}, e.Packed v M → e.Generated D M →
      ofValue v D M (e.value v) = e.deleteOne v
  | .digit d, hp, hg => by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
    rw [Number.value, ofValue_of_forall_lt hp, hS.value_getElem, Nat.add_sub_cancel,
      List.getI_eq_getElem _ hk]
    rfl
  | .phrase (.base m), (hp : IsHighestUnder v M (v m) m), _ => by
    have := ofValue_mul_add hS (c := 1) (r := 0) (by simpa using hp)
      (Nat.zero_lt_of_lt (hS.one_lt_value m hp.mem))
    simpa [Number.value, Phrase.value, Number.deleteOne, Phrase.deleteOne] using this
  | .phrase (.mul q m), ⟨hm, hq⟩, ⟨gq, _⟩ => by
    have := ofValue_mul_add hS (c := q.value v) (r := 0) (by simpa using hm)
      (Nat.zero_lt_of_lt (hS.one_lt_value m hm.mem))
    simpa [Number.value, Phrase.value, Number.deleteOne, Phrase.deleteOne,
      hq.ofValue_value hS gq] using this
  | .add (.base m) n, ⟨_, hn, (hm : IsHighestUnder v M (v m + n.value v) m),
      (hr : n.value v < v m)⟩, ⟨_, gn⟩ => by
    have := ofValue_mul_add hS (c := 1) (r := n.value v) (by simpa using hm) hr
    simpa [Number.value, Phrase.value, Number.deleteOne, Phrase.deleteOne, (value_pos hS gn).ne',
      hn.ofValue_value hS gn] using this
  | .add (.mul q m) n, ⟨⟨_, hq⟩, hn, (hm : IsHighestUnder v M (q.value v * v m + n.value v) m),
      (hr : n.value v < v m)⟩, ⟨⟨gq, _⟩, gn⟩ => by
    have := ofValue_mul_add hS (c := q.value v) (r := n.value v) hm hr
    simpa [Number.value, Phrase.value, Number.deleteOne, Phrase.deleteOne, (value_pos hS gn).ne',
      hq.ofValue_value hS gq, hn.ofValue_value hS gn] using this

/-- In a numeral system two packed NUMBERs of one value differ at most in whether *one* is
pronounced before a multiplier, so the Packing Strategy leaves one numeral for each number, as
(82) requires ([hurford-1975], p. 75). -/
theorem Number.Packed.deleteOne_eq_of_value_eq [Inhabited α] (hS : IsSystem v D M)
    (he : e.Packed v M) (he' : e'.Packed v M) (hg : e.Generated D M) (hg' : e'.Generated D M)
    (h : e.value v = e'.value v) : e.deleteOne v = e'.deleteOne v := by
  rw [← he.ofValue_value hS hg, h, he'.ofValue_value hS hg']

/-! ### Hurford's formulation

[hurford-1975]'s (82) rules out a node of value `x` whose daughters are a NUMBER and a sister of
value `y` when some well-formed structure of a category other than NUMBER that the node expands
to has a value `z` with `y < z ≤ x`. At a NUMBER the sister is a digit or a PHRASE, and (82)
agrees with `Number.Packed`. -/

/-- A digit is packed exactly when no packed PHRASE fits under it. -/
theorem Number.packed_digit_iff {d : α} :
    (digit d).Packed v M ↔ ∀ q : Phrase α, q.Packed v M → v d < q.value v :=
  ⟨fun h _ hq ↦ (h _ hq.isHighestUnder.mem).trans_le hq.isHighestUnder.value_le,
    fun h m hm ↦ h (.base m) (isHighestUnder_self hm)⟩

theorem Phrase.count_pos (hS : IsSystem v D M) : ∀ {p : Phrase α}, p.Generated D M → 0 < p.count v
  | .base _, _ => Nat.one_pos
  | .mul _ _, hg => Number.value_pos hS hg.1

/-- A PHRASE followed by a NUMBER is packed exactly when both are and no packed PHRASE has a
higher value not above the whole. -/
theorem Number.packed_add_iff [Inhabited α] (hS : IsSystem v D M) {n : Number α}
    (hg : p.Generated D M) :
    (add p n).Packed v M ↔ p.Packed v M ∧ n.Packed v M ∧
      ∀ q : Phrase α, q.Packed v M → q.Generated D M →
        q.value v ≤ p.value v + n.value v → q.value v ≤ p.value v := by
  have hc := Phrase.count_pos hS hg
  constructor
  · rintro ⟨hp, hn, hm, hlt⟩
    refine ⟨hp, hn, fun q hq _ hle ↦ ?_⟩
    have hqm := hq.isHighestUnder
    rw [p.value_eq_count_mul] at hle ⊢
    by_cases h : v p.head ≤ q.value v
    · have hv : v q.head = v p.head :=
        (hm.le_value hqm.mem (hqm.value_le.trans (by rwa [← p.value_eq_count_mul] at hle))).antisymm
          (hqm.le_value hm.mem h)
      rw [q.value_eq_count_mul, hv] at hle ⊢
      have : q.count v * v p.head < (p.count v + 1) * v p.head := by rw [Nat.add_one_mul]; omega
      exact Nat.mul_le_mul_right _ (Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_right this))
    · exact (Nat.lt_of_not_ge h).le.trans (Nat.le_mul_of_pos_left _ hc)
  · rintro ⟨hp, hn, hq⟩
    have hm := hp.isHighestUnder
    have h1 := hS.one_lt_value _ hm.mem
    have hhigh : ∀ m' ∈ M, v m' ≤ p.value v + n.value v → v m' ≤ v p.head := fun m' hm' h ↦
      hm.le_value hm' (hq (.base m') (isHighestUnder_self hm') hm' h)
    refine ⟨hp, hn, isHighestUnder_iff.2 ⟨hm.mem, hm.value_le.trans (Nat.le_add_right _ _), hhigh⟩,
      lt_of_not_ge fun hr ↦ ?_⟩
    have hk : (p.count v + 1) * v p.head ≤ p.value v + n.value v := by
      rw [p.value_eq_count_mul, Nat.add_one_mul]; omega
    have := hq (.mul (ofValue v D M (p.count v + 1)) p.head)
      ⟨by rw [value_ofValue hS (Nat.succ_pos _)]
          exact isHighestUnder_iff.2 ⟨hm.mem, Nat.le_mul_of_pos_left _ (Nat.succ_pos _),
            fun m' hm' h ↦ hhigh m' hm' (h.trans hk)⟩,
        packed_ofValue hS (Nat.succ_pos _)⟩
      ⟨generated_ofValue hS (Nat.succ_pos _), hm.mem⟩
      (by rw [Phrase.value, value_ofValue hS (Nat.succ_pos _)]; exact hk)
    rw [Phrase.value, value_ofValue hS (Nat.succ_pos _), p.value_eq_count_mul,
      Nat.add_one_mul] at this
    omega

end Numeral
