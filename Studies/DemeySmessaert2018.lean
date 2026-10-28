module

public import Linglib.Core.Order.Hom.CompleteLattice
public import Linglib.Logic.Aristotelian.Morphism
public import Linglib.Logic.Aristotelian.Square
public import Linglib.Logic.Modal.Basic
public import Linglib.Semantics.Quantification.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Log

/-!
# Demey and Smessaert 2018

Demey and Smessaert compute the bitstring semantics of a finite fragment of a logic from the
partition it induces, whose cells are the consistent conjunctions of its formulas and their
negations: here `Finpartition.minterms` and `BooleanSubalgebra.toSetOfMinterms`. [Any bitstring
semantics of the same length relabels its bit positions](##exists_equiv_eq_toSetOfMinterms_trans).
A fragment of $m$ formulas whose partition has $n$ cells has $\lceil \log_2 n \rceil \le m \le 2^n$
and $\lceil \log_2 m \rceil \le n \le 2^m$, the lower bounds attained [by binary
digits](##card_parts_minterms_digit) and [by any $m$ subsets of
$\lceil \log_2 m \rceil$ points](##card_parts_minterms_eq_clog). The partition depends on the
logic: existential import empties the first-order cell where *all* and *no* both hold, so [the
first-order X of opposition is not Aristotelian isomorphic to the syllogistic
square](##isEmpty_aristotelianIso_categorical). Conversely the strong and weak
Jacoby–Sesmat–Blanché hexagons of S5 are Aristotelian isomorphic, but with three cells against
four [they are not Boolean isomorphic](##isEmpty_booleanIso_jsb).

## Implementation notes

* A proposition over `p` and `q` is the finset of valuations making it true.
* A fragment is an indexed family, and its size the number of its values. The paper's fragments
  are sets of formulas, tacitly pairwise non-equivalent, so its families are injective.
* The lower bound of Theorem 4 is attained in the algebra of subsets of `n` points, by the binary
  digits of the points: the low digits are the paper's atoms `p₁, …, pₖ`, the top digit its
  formula splitting the first `n - 2 ^ k` of their cells.
* A categorical statement depends only on which of the four regions of `S` and `P` are inhabited,
  so a proposition is a set of patterns of inhabited regions, each read on its canonical model. A
  first-order pattern is nonempty; a syllogistic one inhabits `S`.
* An S5 proposition over `p` is a set of world types, a type recording the value of `p` at the
  evaluation world and the values it takes across the worlds.

## Errata

* Footnote 19 claims that every permutation of the bitstrings of length `n` preserves the
  Aristotelian relations, and footnote 26 defines permutation variants by such permutations. Only
  permutations of the bit positions do: swapping `100` and `010` turns the subalternation of `100`
  to `101` into the contradiction of `010` and `101`. Read literally, every bitstring semantics of
  length `n` is a permutation variant, so Theorem 3's uniqueness clause holds trivially; Theorem 3
  here relabels positions.
* Section 5.2 writes `□p ∨ (¬p ∨ ◇p)` for the octagon's `□p ∨ (¬p ∧ ◇p)`, and `Π_S5(F₂)` for
  the first-order partition `Π_FOL(F₂)`.

## TODO

* The sharper bounds of Section 3.3 for contingent fragments closed under negation,
  $2 \lceil \log_2 n \rceil \le m \le 2^n - 2$ and $\lceil \log_2 (m + 2) \rceil \le n \le 2^{m/2}$.
* Section 5.1's characterization: a JSB hexagon is strong iff it is Boolean closed.
* The Buridan octagons of Section 5.2, whose partitions have four, five or six cells, and the
  public announcement logic fragment of Section 6.

## References

* [demey-smessaert-2018]
-/

@[expose] public section

namespace DemeySmessaert2018

open Finset Function Aristotelian BooleanSubalgebra ModalLogic Quantifier Quantifier.GQ SetRel

/-! ### Partitions (Section 3.1) -/

/-- The proposition `p` holds at the valuations that make `p` true. -/
def p : Finset (Bool × Bool) := univ.filter (·.1)

/-- The proposition `q` holds at the valuations that make `q` true. -/
def q : Finset (Bool × Bool) := univ.filter (·.2)

/-- The fragment of Example 2 is `{p ∧ q, ¬p ∨ ¬q, p ∨ q, ¬p ∧ ¬q}`. -/
def example2 : Fin 4 → Finset (Bool × Bool) := ![p ⊓ q, pᶜ ⊔ qᶜ, p ⊔ q, pᶜ ⊓ qᶜ]

-- Example 2: three of the sixteen conjunctions are consistent.
theorem parts_minterms_example2 :
    (Finpartition.minterms example2).parts = {p ⊓ q, (p ⊔ q) ⊓ (pᶜ ⊔ qᶜ), pᶜ ⊓ qᶜ} := by
  decide

-- Theorem 1: the closure of Example 2 has eight elements.
example : Nat.card (closure (Set.range example2)) = 8 := by
  rw [card_closure, parts_minterms_example2]
  decide

/-! ### Minimality and fragment size (Sections 3.2 and 3.3) -/

section Bounds

variable {α ι κ : Type*} [BooleanAlgebra α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  {φ : ι → α}

-- Theorem 3: a bitstring semantics, an order isomorphism onto the sets of bit positions from a
-- Boolean subalgebra containing the fragment, has at least as many positions as there are cells.
theorem card_parts_minterms_le_card [Fintype κ] {L : BooleanSubalgebra α}
    (hL : Set.range φ ⊆ L) (β : L ≃o Set κ) :
    #(Finpartition.minterms φ).parts ≤ Fintype.card κ := by
  have : Finite L := .of_equiv _ β.toEquiv.symm
  have h := Nat.card_le_card_of_injective _ (inclusion_injective (closure_le.2 hL))
  rw [card_closure, Nat.card_congr β.toEquiv, Nat.card_eq_fintype_card, Fintype.card_set] at h
  exact (Nat.pow_le_pow_iff_right one_lt_two).1 h

-- Theorem 3: with no more positions than cells, its domain is the closure.
theorem closure_eq_of_card_le [Fintype κ] {L : BooleanSubalgebra α} (hL : Set.range φ ⊆ L)
    (β : L ≃o Set κ) (h : Fintype.card κ ≤ #(Finpartition.minterms φ).parts) :
    closure (Set.range φ) = L := by
  have : Finite L := .of_equiv _ β.toEquiv.symm
  have hle := closure_le.2 hL
  have hc : Nat.card L ≤ Nat.card (closure (Set.range φ)) := by
    rw [card_closure, Nat.card_congr β.toEquiv, Nat.card_eq_fintype_card, Fintype.card_set]
    exact Nat.pow_le_pow_right two_pos h
  refine le_antisymm hle fun x hx ↦ ?_
  obtain ⟨ψ, hψ⟩ := ((inclusion_injective hle).bijective_of_nat_card_le hc).2 ⟨x, hx⟩
  have hψx : (ψ : α) = x := congrArg Subtype.val hψ
  exact hψx ▸ ψ.2

/-- **Theorem 3**: a bitstring semantics on the closure is `toSetOfMinterms` followed by a
relabelling of the bit positions. -/
theorem exists_equiv_eq_toSetOfMinterms_trans (β : closure (Set.range φ) ≃o Set κ) :
    ∃ e : (Finpartition.minterms φ).parts ≃ κ, β = (toSetOfMinterms φ).trans e.toOrderIsoSet := by
  obtain ⟨e, he⟩ := Equiv.toOrderIsoSet_surjective ((toSetOfMinterms φ).symm.trans β)
  exact ⟨e, by rw [he]; ext; simp⟩

variable (φ) in
-- Theorem 4, lower bound: a partition of `n` cells needs `⌈log₂ n⌉` formulas.
theorem clog_card_parts_minterms_le :
    Nat.clog 2 #(Finpartition.minterms φ).parts ≤ Fintype.card ι :=
  Nat.clog_le_of_le_pow (Finpartition.card_parts_minterms_le_two_pow φ)

variable (φ) in
-- Theorem 5, lower bound: `m` formulas need `⌈log₂ m⌉` bit positions.
theorem clog_card_range_le_card_parts_minterms :
    Nat.clog 2 (Nat.card (Set.range φ)) ≤ #(Finpartition.minterms φ).parts :=
  Nat.clog_le_of_le_pow (Finpartition.card_range_le_two_pow_card_parts_minterms φ)

end Bounds

/-- The `j`-th binary digit of the points `0, …, n - 1`, as the set of points where it is `1`. -/
def digit (n : ℕ) (j : Fin (Nat.clog 2 n)) : Finset (Fin n) := univ.filter fun x ↦ x.1.testBit j

-- Theorem 4: the digits are distinct, so they are `⌈log₂ n⌉` formulas.
theorem digit_injective (n : ℕ) : Injective (digit n) := by
  intro j j' h
  have hj : 2 ^ j.1 < n := Nat.pow_lt_of_lt_clog j.2
  have h1 : (⟨2 ^ j.1, hj⟩ : Fin n) ∈ digit n j := by simp [digit, Nat.testBit_two_pow_self]
  rw [h] at h1
  simp only [digit, mem_filter, mem_univ, true_and, Nat.testBit_two_pow, decide_eq_true_eq] at h1
  exact Fin.ext h1

/-- **Theorem 4**, lower bound attained: the `⌈log₂ n⌉` binary digits of `n` points have `n`
cells. -/
theorem card_parts_minterms_digit (n : ℕ) : #(Finpartition.minterms (digit n)).parts = n := by
  refine le_antisymm ((Finpartition.card_parts_le_card _).trans_eq (by simp)) ?_
  set bits : Fin n → Fin (Nat.clog 2 n) → Bool := fun x j ↦ x.1.testBit j
  have hbits : Injective bits := fun x y h ↦ Fin.ext <| Nat.eq_of_testBit_eq fun i ↦ by
    by_cases hi : i < Nat.clog 2 n
    · exact congrFun h ⟨i, hi⟩
    have hn : n ≤ 2 ^ i := (Nat.le_pow_clog one_lt_two n).trans
      (Nat.pow_le_pow_right two_pos (not_lt.1 hi))
    rw [Nat.testBit_lt_two_pow (x.2.trans_le hn), Nat.testBit_lt_two_pow (y.2.trans_le hn)]
  rw [Finpartition.card_parts_minterms]
  calc n = #(univ.image bits) := by
        rw [card_image_of_injective _ hbits, card_univ, Fintype.card_fin]
    _ ≤ _ := card_le_card fun σ hσ ↦ ?_
  obtain ⟨x, -, rfl⟩ := mem_image.1 hσ
  exact mem_filter.2 ⟨mem_univ _,
    ne_empty_of_mem (a := x) (mem_minterm.2 fun j ↦ by simp [digit, bits])⟩

-- Theorem 4, upper bound attained: all `2 ^ n` subsets of `n` points have `n` cells.
theorem card_parts_minterms_id (β : Type*) [Fintype β] [DecidableEq β] :
    #(Finpartition.minterms (id : Finset β → Finset β)).parts = Fintype.card β := by
  refine le_antisymm ((Finpartition.card_parts_le_card _).trans_eq (by simp)) ?_
  have := Finpartition.card_range_le_two_pow_card_parts_minterms (id : Finset β → Finset β)
  rwa [Set.range_id, Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_finset,
    Nat.pow_le_pow_iff_right one_lt_two] at this

/-- The atom `pᵢ` of propositional logic over `m` atoms holds at the valuations making it true. -/
def atom (m : ℕ) (i : Fin m) : Finset (Fin m → Bool) := univ.filter (· i)

-- Theorem 5, upper bound attained: `m` atoms have `2 ^ m` cells.
theorem card_parts_minterms_atom (m : ℕ) : #(Finpartition.minterms (atom m)).parts = 2 ^ m := by
  rw [Finpartition.card_parts_minterms, bot_eq_empty,
    filter_true_of_mem fun σ _ ↦ ne_empty_of_mem (a := σ) (mem_minterm.2 fun i ↦ by simp [atom])]
  simp

/-- **Theorem 5**, lower bound attained: any `m` distinct subsets of `⌈log₂ m⌉` points have
`⌈log₂ m⌉` cells. -/
theorem card_parts_minterms_eq_clog {m : ℕ} {φ : Fin m → Finset (Fin (Nat.clog 2 m))}
    (hφ : Injective φ) : #(Finpartition.minterms φ).parts = Nat.clog 2 m := by
  refine le_antisymm ((Finpartition.card_parts_le_card _).trans_eq (by simp)) ?_
  simpa [Set.card_range_of_injective hφ] using clog_card_range_le_card_parts_minterms φ

/-! ### Existential import (Section 4) -/

/-- In the canonical model of a set of regions, each region recording whether an individual is `S`
and whether it is `P`, the individuals are the regions and `S` holds of those inside `S`. -/
def InS (m : Finset (Bool × Bool)) (r : m) : Prop := r.1.1 = true

/-- In the canonical model of a set of regions, `P` holds of the regions inside `P`. -/
def InP (m : Finset (Bool × Bool)) (r : m) : Prop := r.1.2 = true

instance (m : Finset (Bool × Bool)) : DecidablePred (InS m) :=
  fun _ ↦ inferInstanceAs (Decidable (_ = _))

instance (m : Finset (Bool × Bool)) : DecidablePred (InP m) :=
  fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- A first-order model has an individual. -/
def IsFOLPattern (m : Finset (Bool × Bool)) : Prop := m.Nonempty

/-- A model of syllogistics has an individual in `S`. -/
def IsSYLPattern (m : Finset (Bool × Bool)) : Prop := ∃ r ∈ m, r.1 = true

instance : DecidablePred IsFOLPattern := fun _ ↦ inferInstanceAs (Decidable (Finset.Nonempty _))

instance : DecidablePred IsSYLPattern := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The categorical statements *all*, *no*, *some* and *not all* `S` are `P`, each the set of
models of a logic where it holds, the models being the patterns satisfying `L`. -/
def categorical (L : Finset (Bool × Bool) → Prop) [DecidablePred L] : Fin 4 → Finset {m // L m} :=
  ![univ.filter fun m ↦ every (InS m.1) (InP m.1), univ.filter fun m ↦ no (InS m.1) (InP m.1),
    univ.filter fun m ↦ GQ.some (InS m.1) (InP m.1),
    univ.filter fun m ↦ ¬ every (InS m.1) (InP m.1)]

/-- The categorical statements as a square, with corners `A`, `E`, `I` and `O`. -/
def categoricalSquare (L : Finset (Bool × Bool) → Prop) [DecidablePred L] :
    Square (Finset {m // L m}) :=
  ⟨categorical L 0, categorical L 1, categorical L 2, categorical L 3⟩

-- Section 4: `A` and `E` split first-order models into four cells.
theorem card_parts_minterms_fol :
    #(Finpartition.minterms ![categorical IsFOLPattern 0, categorical IsFOLPattern 1]).parts =
      4 := by
  decide

-- Section 4: `A` and `E` split syllogistic models into three cells.
theorem card_parts_minterms_syl :
    #(Finpartition.minterms ![categorical IsSYLPattern 0, categorical IsSYLPattern 1]).parts =
      3 := by
  decide

-- The fourth first-order cell, where `A` and `E` both hold, has nothing in `S`.
theorem inf_categorical_fol :
    categorical IsFOLPattern 0 ⊓ categorical IsFOLPattern 1 =
      univ.filter fun m ↦ ¬ IsSYLPattern m.1 := by
  ext m
  simp only [categorical, inf_eq_inter, mem_inter, mem_filter, mem_univ, true_and, IsSYLPattern,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨fun ⟨hA, hE⟩ ⟨r, hr, hS⟩ ↦ a_e_contrary _ _ hA hE ⟨r, hr⟩ hS,
    fun h ↦ ⟨fun r hr ↦ (h ⟨r.1, r.2, hr⟩).elim, fun r hr ↦ (h ⟨r.1, r.2, hr⟩).elim⟩⟩

-- In syllogistics the categorical statements form a square of opposition.
theorem squareRelations_syl : SquareRelations (categoricalSquare IsSYLPattern) := by
  refine .of_disjoint ?_ ?_ (disjoint_left.2 fun m hA hE ↦ ?_)
  · ext m
    simp [categoricalSquare, categorical, no_contradicts_some]
  · ext m
    simp [categoricalSquare, categorical]
  · obtain ⟨r, hr, hS⟩ := m.2
    simp only [categoricalSquare, categorical, mem_filter, mem_univ, true_and,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hA hE
    exact a_e_contrary _ _ hA hE ⟨r, hr⟩ hS

-- In first-order logic no two categorical statements are contrary.
theorem not_isContrary_fol (i j : Fin 4) :
    ¬ IsContrary (categorical IsFOLPattern i) (categorical IsFOLPattern j) := by
  revert i j
  simp only [IsContrary, codisjoint_iff]
  decide

/-- The first-order X of opposition is not Aristotelian isomorphic to the syllogistic square,
whose universal statements are contrary. -/
theorem isEmpty_aristotelianIso_categorical :
    IsEmpty (AristotelianIso (categorical IsFOLPattern) (categorical IsSYLPattern)) := by
  refine ⟨fun e ↦ not_isContrary_fol _ _ ((e.symm.map_isContrary 0 1).1 ?_)⟩
  refine ⟨squareRelations_syl.contraryAE, ?_⟩
  simp only [codisjoint_iff]
  decide

/-! ### Strong and weak Jacoby–Sesmat–Blanché hexagons (Section 5.1) -/

/-- An S5 world type records the value of `p` at the evaluation world and the set of values `p`
takes across the worlds, which contains it. -/
abbrev S5Type := {t : Bool × Finset Bool // t.1 ∈ t.2}

/-- In the canonical model of a type, the worlds are the values of `p` it realizes, each seeing
every one. -/
def access (t : S5Type) : SetRel Bool Bool := {wv | wv.1 ∈ t.1.2 ∧ wv.2 ∈ t.1.2}

instance (t : S5Type) (w v : Bool) : Decidable (w ~[access t] v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `p` holds at the evaluation world. -/
def atP : Finset S5Type := univ.filter fun t ↦ t.1.1 = true

/-- `□p` holds at the evaluation world. -/
def boxP : Finset S5Type := univ.filter fun t ↦ □[access t] (· = true) t.1.1

/-- `□¬p` holds at the evaluation world. -/
def boxNotP : Finset S5Type := univ.filter fun t ↦ □[access t] (· = false) t.1.1

/-- `◇p` holds at the evaluation world. -/
def diaP : Finset S5Type := univ.filter fun t ↦ ◇[access t] (· = true) t.1.1

/-- `◇¬p` holds at the evaluation world. -/
def diaNotP : Finset S5Type := univ.filter fun t ↦ ◇[access t] (· = false) t.1.1

/-- The strong JSB hexagon `{□p, □¬p, ◇p, ◇¬p, ◇p ∧ ◇¬p, □p ∨ □¬p}`. -/
def strongJSB : Fin 6 → Finset S5Type :=
  ![boxP, boxNotP, diaP, diaNotP, diaP ⊓ diaNotP, boxP ⊔ boxNotP]

/-- The weak JSB hexagon `{□p, □¬p, ◇p, ◇¬p, p ∧ ◇¬p, ¬p ∨ □p}`. -/
def weakJSB : Fin 6 → Finset S5Type :=
  ![boxP, boxNotP, diaP, diaNotP, atP ⊓ diaNotP, atPᶜ ⊔ boxP]

-- Section 5.1: the contrariety triangle of the strong hexagon is exhaustive.
theorem sup_strongJSB_eq_top : strongJSB 0 ⊔ strongJSB 1 ⊔ strongJSB 4 = ⊤ := by
  decide

-- Section 5.1: the contrariety triangle of the weak hexagon is not.
theorem sup_weakJSB_ne_top : weakJSB 0 ⊔ weakJSB 1 ⊔ weakJSB 4 ≠ ⊤ := by
  decide

-- Section 5.1: the strong hexagon's partition has three cells.
theorem card_parts_minterms_strongJSB : #(Finpartition.minterms strongJSB).parts = 3 := by
  decide +kernel

-- Section 5.1: the weak hexagon's partition has four cells.
theorem card_parts_minterms_weakJSB : #(Finpartition.minterms weakJSB).parts = 4 := by
  decide +kernel

/-- The strong and weak JSB hexagons are Aristotelian isomorphic by the paper's `ρ`, which matches
their corners in order. -/
def jsbIso : AristotelianIso strongJSB weakJSB where
  toEquiv := .refl _
  map_disjoint := by decide
  map_codisjoint := by simp only [codisjoint_iff]; decide
  map_lt := by decide

/-- The strong and weak JSB hexagons are not Boolean isomorphic. -/
theorem isEmpty_booleanIso_jsb : IsEmpty (BooleanIso strongJSB weakJSB) :=
  ⟨fun e ↦ absurd ((nonempty_orderIso_closure_iff _ _).1 ⟨e.closureIso⟩) <| by
    rw [card_parts_minterms_strongJSB, card_parts_minterms_weakJSB]; decide⟩

end DemeySmessaert2018
