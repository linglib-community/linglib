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
square](##isEmpty_aristotelianIso_categoricalModels). Conversely the strong and weak
Jacoby–Sesmat–Blanché hexagons of S5 are Aristotelian isomorphic, but with three cells against
four [they are not Boolean isomorphic](##isEmpty_booleanIso_jsbModels). In any Boolean algebra
[a JSB hexagon is Boolean closed iff its contrariety triangle is
exhaustive](##isBooleanClosed_jsbHexagon_iff), the strong case.

## Implementation notes

* A proposition over `p` and `q` is the finset of valuations making it true.
* A fragment is an indexed family, and its size the number of its values. The paper's fragments
  are sets of formulas, tacitly pairwise non-equivalent, so its families are injective.
* The lower bound of Theorem 4 is attained in the algebra of subsets of `n` points, by the binary
  digits of the points: the low digits are the paper's atoms `p₁, …, pₖ`, the top digit its
  formula splitting the first `n - 2 ^ k` of their cells.
* The cells are counted on finitely many model types and transferred to the models. A
  categorical statement holds of a model iff it holds of the canonical model of the regions of `S`
  and `P` the model inhabits (`categoricalModels_eq`), and over a domain of at least four
  individuals every nonempty set of regions is some model's, so the diagram over sets of regions
  is Boolean isomorphic to the diagram over models (`BooleanIso.ofSurjective`). Likewise an S5
  formula over `p` depends only on the value of `p` at the evaluation world and the values it
  takes, and two worlds realize every such type.

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

-- Theorem 5, lower bound attained: any `m` distinct subsets of `⌈log₂ m⌉` points have
-- `⌈log₂ m⌉` cells.
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

-- Section 4: the syllogistic cells are the vertices of the triangle of opposition.
theorem parts_minterms_syl :
    (Finpartition.minterms ![categorical IsSYLPattern 0, categorical IsSYLPattern 1]).parts =
      univ.image (categoricalSquare IsSYLPattern).triangle := by
  set sq := categoricalSquare IsSYLPattern
  have hd : Pairwise (Function.onFun Disjoint ![sq.A, sq.E]) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    exacts [absurd rfl hij, squareRelations_syl.contraryAE, squareRelations_syl.contraryAE.symm,
      absurd rfl hij]
  have hsup : univ.sup ![sq.A, sq.E] = sq.A ⊔ sq.E := by simp [Fin.univ_succ]
  have himage : univ.image ![sq.A, sq.E] = {sq.A, sq.E} := by
    ext x
    simp [Fin.exists_fin_succ, eq_comm]
  have hne : sq.A ≠ ⊥ ∧ sq.E ≠ ⊥ ∧ sq.I ⊓ sq.O ≠ ⊥ := by decide
  change (Finpartition.minterms ![sq.A, sq.E]).parts = _
  have hbot : ⊥ ∉ insert (sq.I ⊓ sq.O) ({sq.A, sq.E} : Finset _) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hne.2.2.symm, hne.1.symm, hne.2.1.symm⟩
  rw [Finpartition.parts_minterms_of_pairwise_disjoint hd, hsup, himage,
    ← squareRelations_syl.inf_IO_eq, erase_eq_of_notMem hbot]
  ext x
  simp only [mem_insert, mem_singleton, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | rfl | rfl)
    exacts [⟨.IO, rfl⟩, ⟨.A, rfl⟩, ⟨.E, rfl⟩]
  · rintro ⟨t, rfl⟩
    cases t <;> simp [Square.triangle]

-- Section 4: so `A` and `E` split syllogistic models into three cells.
theorem card_parts_minterms_syl :
    #(Finpartition.minterms ![categorical IsSYLPattern 0, categorical IsSYLPattern 1]).parts =
      3 := by
  have hne : ∀ t, (categoricalSquare IsSYLPattern).triangle t ≠ ⊥ := by decide
  have hinj : Function.Injective (categoricalSquare IsSYLPattern).triangle := fun s t hst ↦ by
    by_contra h
    have hdis : Disjoint ((categoricalSquare IsSYLPattern).triangle s)
        ((categoricalSquare IsSYLPattern).triangle t) :=
      squareRelations_syl.pairwise_disjoint_triangle h
    rw [← hst] at hdis
    exact hne s (disjoint_self.1 hdis)
  rw [parts_minterms_syl, card_image_of_injective _ hinj]
  decide

-- In first-order logic no two categorical statements are contrary.
theorem not_isContrary_fol (i j : Fin 4) :
    ¬ IsContrary (categorical IsFOLPattern i) (categorical IsFOLPattern j) := by
  revert i j
  simp only [IsContrary, codisjoint_iff]
  decide

-- Section 4: on patterns, the first-order X is not Aristotelian isomorphic to the syllogistic
-- square, whose universal statements are contrary.
theorem isEmpty_aristotelianIso_categorical :
    IsEmpty (AristotelianIso (categorical IsFOLPattern) (categorical IsSYLPattern)) := by
  refine ⟨fun e ↦ not_isContrary_fol _ _ ((e.symm.map_isContrary 0 1).1 ?_)⟩
  refine ⟨squareRelations_syl.contraryAE, ?_⟩
  simp only [codisjoint_iff]
  decide

section Models

variable {D : Type*}

open Classical in
/-- The regions a model inhabits, the model interpreting `S` and `P` over the domain `D`. -/
noncomputable def regions (m : (D → Prop) × (D → Prop)) : Finset (Bool × Bool) :=
  univ.filter fun r ↦ ∃ x, (m.1 x ↔ r.1 = true) ∧ (m.2 x ↔ r.2 = true)

theorem mem_regions {m : (D → Prop) × (D → Prop)} {r : Bool × Bool} :
    r ∈ regions m ↔ ∃ x, (m.1 x ↔ r.1 = true) ∧ (m.2 x ↔ r.2 = true) := by
  simp [regions]

/-- The categorical statements over the first-order models with domain `D`. -/
def categoricalModels (D : Type*) : Fin 4 → Set ((D → Prop) × (D → Prop)) :=
  ![{m | every m.1 m.2}, {m | no m.1 m.2}, {m | GQ.some m.1 m.2}, {m | ¬ every m.1 m.2}]

/-- The categorical statements over the models of syllogistics with domain `D`, where something is
`S`. -/
def sylModels (D : Type*) : Fin 4 → Set {m : (D → Prop) × (D → Prop) // ∃ x, m.1 x} :=
  fun i ↦ Subtype.val ⁻¹' categoricalModels D i

/-- The region each categorical statement is about, and whether it says the region is inhabited. -/
private def region : Fin 4 → (Bool × Bool) × Bool :=
  ![((true, false), false), ((true, true), false), ((true, true), true), ((true, false), true)]

private theorem mem_categorical_iff {L : Finset (Bool × Bool) → Prop} [DecidablePred L]
    (i : Fin 4) (n : {n // L n}) :
    n ∈ categorical L i ↔ ((region i).1 ∈ n.1 ↔ (region i).2 = true) := by
  have key : ∀ (i : Fin 4) (n : {n : Finset (Bool × Bool) // True}),
      n ∈ categorical (fun _ ↦ True) i ↔ ((region i).1 ∈ n.1 ↔ (region i).2 = true) := by
    decide
  refine Iff.trans ?_ (key i ⟨n.1, trivial⟩)
  fin_cases i <;> simp [categorical]

private theorem mem_categoricalModels_iff (i : Fin 4) (m : (D → Prop) × (D → Prop)) :
    m ∈ categoricalModels D i ↔ ((region i).1 ∈ regions m ↔ (region i).2 = true) := by
  fin_cases i <;> simp [categoricalModels, region, mem_regions, every, no, GQ.some]

/-- The type of a first-order model over a nonempty domain is the set of regions it inhabits. -/
noncomputable def folType [Nonempty D] (m : (D → Prop) × (D → Prop)) :
    {n // IsFOLPattern n} :=
  ⟨regions m, by
    classical
    obtain ⟨x⟩ := ‹Nonempty D›
    exact ⟨(decide (m.1 x), decide (m.2 x)), mem_regions.2 ⟨x, by simp, by simp⟩⟩⟩

/-- The type of a model of syllogistics is the set of regions it inhabits. -/
noncomputable def sylType (m : {m : (D → Prop) × (D → Prop) // ∃ x, m.1 x}) :
    {n // IsSYLPattern n} :=
  ⟨regions m.1, by
    classical
    obtain ⟨x, hx⟩ := m.2
    exact ⟨(true, decide (m.1.2 x)), mem_regions.2 ⟨x, by simp [hx], by simp⟩, rfl⟩⟩

-- Section 4: a categorical statement holds of a first-order model iff it holds of the canonical
-- model of the model's type.
theorem categoricalModels_eq [Nonempty D] :
    categoricalModels D = fun i ↦ folType ⁻¹' ↑(categorical IsFOLPattern i) := by
  funext i
  ext m
  exact (mem_categoricalModels_iff i m).trans (mem_categorical_iff i (folType m)).symm

-- Section 4: likewise for the models of syllogistics.
theorem sylModels_eq : sylModels D = fun i ↦ sylType ⁻¹' ↑(categorical IsSYLPattern i) := by
  funext i
  ext m
  exact (mem_categoricalModels_iff i m.1).trans (mem_categorical_iff i (sylType m)).symm

-- Over a domain of at least four individuals, every nonempty set of regions is a model's.
theorem exists_regions_eq [Fintype D] (hD : 4 ≤ Fintype.card D) {n : Finset (Bool × Bool)}
    (hn : n.Nonempty) : ∃ m : (D → Prop) × (D → Prop), regions m = n := by
  obtain ⟨e⟩ : Nonempty (n ↪ D) := Function.Embedding.nonempty_of_card_le <| by
    rw [Fintype.card_coe]
    exact (card_le_univ n).trans (by simpa using hD)
  have : Nonempty n := hn.coe_sort
  have hg := Function.invFun_surjective e.injective
  refine ⟨(fun x ↦ (Function.invFun e x).1.1 = true, fun x ↦ (Function.invFun e x).1.2 = true),
    Finset.ext fun r ↦ ⟨fun hr ↦ ?_, fun hr ↦ ?_⟩⟩
  · obtain ⟨x, h₁, h₂⟩ := mem_regions.1 hr
    have : (Function.invFun e x).1 = r := Prod.ext (Bool.eq_iff_iff.2 h₁) (Bool.eq_iff_iff.2 h₂)
    exact this ▸ (Function.invFun e x).2
  · obtain ⟨x, hx⟩ := hg ⟨r, hr⟩
    exact mem_regions.2 ⟨x, by simp [hx], by simp [hx]⟩

theorem folType_surjective [Fintype D] [Nonempty D] (hD : 4 ≤ Fintype.card D) :
    Surjective (folType (D := D)) := fun n ↦
  let ⟨m, hm⟩ := exists_regions_eq hD n.2
  ⟨m, Subtype.ext hm⟩

theorem sylType_surjective [Fintype D] (hD : 4 ≤ Fintype.card D) :
    Surjective (sylType (D := D)) := fun n ↦ by
  obtain ⟨m, hm⟩ := exists_regions_eq hD (n.2.imp fun r ⟨hr, _⟩ ↦ hr)
  obtain ⟨r, hr, hS⟩ := n.2
  obtain ⟨x, hx, -⟩ := mem_regions.1 (hm ▸ hr)
  exact ⟨⟨m, x, hx.2 hS⟩, Subtype.ext hm⟩

/-- Over a domain of at least four individuals, the first-order models realize every pattern. -/
noncomputable def categoricalModelsIso [Fintype D] [Nonempty D] (hD : 4 ≤ Fintype.card D) :
    BooleanIso (categorical IsFOLPattern) (categoricalModels D) :=
  (categoricalModels_eq (D := D)).symm ▸ BooleanIso.ofSurjective folType (folType_surjective hD)

/-- Over a domain of at least four individuals, the models of syllogistics realize every
pattern. -/
noncomputable def sylModelsIso [Fintype D] (hD : 4 ≤ Fintype.card D) :
    BooleanIso (categorical IsSYLPattern) (sylModels D) :=
  (sylModels_eq (D := D)).symm ▸ BooleanIso.ofSurjective sylType (sylType_surjective hD)

/-- Over any domain of at least four individuals, the first-order X of opposition is not
Aristotelian isomorphic to the syllogistic square. -/
theorem isEmpty_aristotelianIso_categoricalModels [Fintype D] (hD : 4 ≤ Fintype.card D) :
    IsEmpty (AristotelianIso (categoricalModels D) (sylModels D)) := by
  have : Nonempty D := (Fintype.card_pos_iff (α := D)).1 (by omega)
  exact ⟨fun e ↦ isEmpty_aristotelianIso_categorical.false
    ((categoricalModelsIso hD : AristotelianIso _ _).trans
      (e.trans ((sylModelsIso hD).symm : AristotelianIso _ _)))⟩

end Models

/-! ### Strong and weak Jacoby–Sesmat–Blanché hexagons (Section 5.1) -/

section JSB

variable {α : Type*} [BooleanAlgebra α] [DecidableEq α] {a b c : α}

/-- The Jacoby–Sesmat–Blanché hexagon on a contrariety triangle `a`, `b`, `c`, in the paper's
order `a`, `b`, `¬b`, `¬a`, `c`, `¬c`. -/
def jsbHexagon (a b c : α) : Fin 6 → α := ![a, b, bᶜ, aᶜ, c, cᶜ]

/-- A diagram is Boolean closed when every contingent element of its closure is a corner. -/
def IsBooleanClosed {ι : Type*} (φ : ι → α) : Prop :=
  ∀ x ∈ closure (Set.range φ), x ≠ ⊥ → x ≠ ⊤ → x ∈ Set.range φ

omit [DecidableEq α] in
theorem closure_jsbHexagon :
    closure (Set.range (jsbHexagon a b c)) = closure (Set.range ![a, b, c]) := by
  have h₀ : a ∈ closure (Set.range ![a, b, c]) := subset_closure ⟨0, rfl⟩
  have h₁ : b ∈ closure (Set.range ![a, b, c]) := subset_closure ⟨1, rfl⟩
  have h₂ : c ∈ closure (Set.range ![a, b, c]) := subset_closure ⟨2, rfl⟩
  refine le_antisymm (closure_le.2 ?_) (closure_le.2 ?_) <;> rintro _ ⟨i, rfl⟩ <;> fin_cases i
  exacts [h₀, h₁, compl_mem h₁, compl_mem h₀, h₂, compl_mem h₂, subset_closure ⟨0, rfl⟩,
    subset_closure ⟨1, rfl⟩, subset_closure ⟨4, rfl⟩]

variable (hab : Disjoint a b) (hac : Disjoint a c) (hbc : Disjoint b c)
include hab hac hbc

-- Section 5.1: the cells of a JSB hexagon are the corners of its contrariety triangle and the
-- complement of their join.
theorem parts_minterms_jsbHexagon :
    (Finpartition.minterms (jsbHexagon a b c)).parts =
      (insert (a ⊔ b ⊔ c)ᶜ ({a, b, c} : Finset α)).erase ⊥ := by
  have hsup : univ.sup ![a, b, c] = a ⊔ b ⊔ c := by
    rw [Fin.univ_succ, sup_cons, Fin.univ_succ, map_cons, sup_cons]
    simp [sup_assoc]
  have himage : univ.image ![a, b, c] = {a, b, c} := by
    ext x
    simp [Fin.exists_fin_succ, eq_comm]
  rw [parts_minterms_eq_of_closure_eq closure_jsbHexagon,
    Finpartition.parts_minterms_of_pairwise_disjoint, hsup, himage]
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | simp only [Function.onFun]
  all_goals first | assumption | exact Disjoint.symm ‹_›

variable (ha : a ≠ ⊥) (hb : b ≠ ⊥) (hc : c ≠ ⊥)
include ha hb hc

-- Section 5.1: a JSB hexagon has three cells when strong, its contrariety triangle exhaustive,
-- and four when weak.
theorem card_parts_minterms_jsbHexagon :
    #(Finpartition.minterms (jsbHexagon a b c)).parts = if a ⊔ b ⊔ c = ⊤ then 3 else 4 := by
  have ne {x y : α} (hx : x ≠ ⊥) (h : Disjoint x y) : x ≠ y := fun hxy ↦ hx (by
    rw [← hxy] at h; exact disjoint_self.1 h)
  have h3 : #({a, b, c} : Finset α) = 3 :=
    card_eq_three.2 ⟨a, b, c, ne ha hab, ne ha hac, ne hb hbc, rfl⟩
  rw [parts_minterms_jsbHexagon hab hac hbc]
  split_ifs with hs
  · rw [hs, compl_top, erase_insert_eq_erase, erase_eq_of_notMem]
    · exact h3
    simp [ha.symm, hb.symm, hc.symm]
  · have hd : (a ⊔ b ⊔ c)ᶜ ≠ ⊥ := fun h ↦ hs (compl_eq_bot.1 h)
    have hdis {x : α} (hx : x ≤ a ⊔ b ⊔ c) : Disjoint x (a ⊔ b ⊔ c)ᶜ :=
      disjoint_compl_right.mono_left hx
    have hbot : ⊥ ∉ insert (a ⊔ b ⊔ c)ᶜ ({a, b, c} : Finset α) := by
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hd.symm, ha.symm, hb.symm, hc.symm⟩
    rw [erase_eq_of_notMem hbot, card_insert_of_notMem]
    · rw [h3]
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨(ne ha (hdis (le_sup_left.trans le_sup_left))).symm,
      (ne hb (hdis (le_sup_right.trans le_sup_left))).symm, (ne hc (hdis le_sup_right)).symm⟩

/-- **Section 5.1**: a JSB hexagon is Boolean closed iff it is strong. -/
theorem isBooleanClosed_jsbHexagon_iff :
    IsBooleanClosed (jsbHexagon a b c) ↔ a ⊔ b ⊔ c = ⊤ := by
  have hmem (i : Fin 6) : jsbHexagon a b c i ∈ closure (Set.range (jsbHexagon a b c)) :=
    subset_closure ⟨i, rfl⟩
  have ha' : a ≤ a ⊔ b ⊔ c := le_sup_left.trans le_sup_left
  have hb' : b ≤ a ⊔ b ⊔ c := le_sup_right.trans le_sup_left
  refine ⟨fun h ↦ by_contra fun hs ↦ ?_, fun hs x hx hx₀ hx₁ ↦ ?_⟩
  · -- the complement of the join is a contingent element of the closure and no corner
    have below {x : α} (hx : x ≤ a ⊔ b ⊔ c) (hx' : x ≤ (a ⊔ b ⊔ c)ᶜ) : x = ⊥ :=
      le_bot_iff.1 <| (le_inf hx hx').trans (inf_compl_self _).le
    obtain ⟨i, hi⟩ := h _ (compl_mem (sup_mem (sup_mem (hmem 0) (hmem 1)) (hmem 4)))
      (fun h ↦ hs (compl_eq_bot.1 h)) fun h ↦ ha <| le_bot_iff.1 <| ha'.trans_eq (compl_eq_top.1 h)
    fin_cases i
    · exact ha (below ha' (show a = _ from hi).le)
    · exact hb (below hb' (show b = _ from hi).le)
    · exact ha (hab.eq_bot_of_le (ha'.trans_eq (compl_injective (show bᶜ = _ from hi)).symm))
    · exact hb (hab.symm.eq_bot_of_le (hb'.trans_eq (compl_injective (show aᶜ = _ from hi)).symm))
    · exact hc (below le_sup_right (show c = _ from hi).le)
    · exact ha (hac.eq_bot_of_le (ha'.trans_eq (compl_injective (show cᶜ = _ from hi)).symm))
  · -- each corner of the triangle lies below `x` or is disjoint from it
    have cell (y : α) (hy : y = a ∨ y = b ∨ y = c) : x ⊓ y = y ∨ x ⊓ y = ⊥ := by
      refine (le_or_disjoint_of_mem_minterms hx ?_).imp inf_eq_right.2 fun h ↦ h.symm.eq_bot
      rw [parts_minterms_jsbHexagon hab hac hbc]
      rcases hy with rfl | rfl | rfl <;> simp [ha, hb, hc]
    have split : x = x ⊓ a ⊔ x ⊓ b ⊔ x ⊓ c := by
      rw [← inf_sup_left, ← inf_sup_left, hs, inf_top_eq]
    have key {y z : α} (h : y ⊔ z = ⊤) (hyz : Disjoint y z) : zᶜ = y :=
      (IsCompl.of_eq hyz.eq_bot h).eq_compl.symm
    rcases cell a (by simp) with h₁ | h₁ <;> rcases cell b (by simp) with h₂ | h₂ <;>
      rcases cell c (by simp) with h₃ | h₃ <;> rw [h₁, h₂, h₃] at split <;>
      (try simp only [bot_sup_eq, sup_bot_eq] at split) <;> subst split
    · exact absurd hs hx₁
    · exact ⟨5, key hs (hac.sup_left hbc)⟩
    · exact ⟨2, key (by rw [← hs]; ac_rfl) (hab.sup_left hbc.symm)⟩
    · exact ⟨0, rfl⟩
    · exact ⟨3, key (by rw [← hs]; ac_rfl) (hab.symm.sup_left hac.symm)⟩
    · exact ⟨1, rfl⟩
    · exact ⟨4, rfl⟩
    · exact absurd rfl hx₀

end JSB

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

-- Section 5.1: the strong hexagon is the JSB hexagon on `□p`, `□¬p` and `◇p ∧ ◇¬p`.
theorem strongJSB_eq : strongJSB = jsbHexagon boxP boxNotP (diaP ⊓ diaNotP) := by
  funext i
  fin_cases i <;> decide

-- Section 5.1: the weak hexagon is the JSB hexagon on `□p`, `□¬p` and `p ∧ ◇¬p`.
theorem weakJSB_eq : weakJSB = jsbHexagon boxP boxNotP (atP ⊓ diaNotP) := by
  funext i
  fin_cases i <;> decide

-- Section 5.1: the contrariety triangle of the strong hexagon is exhaustive.
theorem sup_strongJSB_eq_top : strongJSB 0 ⊔ strongJSB 1 ⊔ strongJSB 4 = ⊤ := by
  decide

-- Section 5.1: the contrariety triangle of the weak hexagon is not.
theorem sup_weakJSB_ne_top : weakJSB 0 ⊔ weakJSB 1 ⊔ weakJSB 4 ≠ ⊤ := by
  decide

-- Section 5.1: the strong hexagon's partition has three cells.
theorem card_parts_minterms_strongJSB : #(Finpartition.minterms strongJSB).parts = 3 := by
  rw [strongJSB_eq, card_parts_minterms_jsbHexagon (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  split_ifs with h
  · rfl
  · exact absurd sup_strongJSB_eq_top h

-- Section 5.1: the weak hexagon's partition has four cells.
theorem card_parts_minterms_weakJSB : #(Finpartition.minterms weakJSB).parts = 4 := by
  rw [weakJSB_eq, card_parts_minterms_jsbHexagon (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  split_ifs with h
  · exact absurd h sup_weakJSB_ne_top
  · rfl

-- Section 5.1: the strong hexagon is Boolean closed.
theorem isBooleanClosed_strongJSB : IsBooleanClosed strongJSB := by
  rw [strongJSB_eq]
  exact (isBooleanClosed_jsbHexagon_iff (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).2 sup_strongJSB_eq_top

-- Section 5.1: the weak hexagon is not.
theorem not_isBooleanClosed_weakJSB : ¬ IsBooleanClosed weakJSB := by
  rw [weakJSB_eq, isBooleanClosed_jsbHexagon_iff (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  exact sup_weakJSB_ne_top

/-- The strong and weak JSB hexagons are Aristotelian isomorphic by the paper's `ρ`, which matches
their corners in order. -/
def jsbIso : AristotelianIso strongJSB weakJSB where
  toEquiv := .refl _
  map_disjoint := by decide
  map_codisjoint := by simp only [codisjoint_iff]; decide
  map_lt := by decide

-- Section 5.1: on types, the strong and weak hexagons are not Boolean isomorphic.
theorem isEmpty_booleanIso_jsb : IsEmpty (BooleanIso strongJSB weakJSB) :=
  ⟨fun e ↦ absurd ((nonempty_orderIso_closure_iff _ _).1 ⟨e.closureIso⟩) <| by
    rw [card_parts_minterms_strongJSB, card_parts_minterms_weakJSB]; decide⟩

section S5Models

variable {W : Type*}

open Classical in
/-- The type of a pointed S5 model, a valuation of `p` on the worlds `W` with an evaluation world:
the value of `p` there and the values it takes across the worlds. -/
noncomputable def s5Type (m : (W → Prop) × W) : S5Type :=
  ⟨(decide (m.1 m.2), univ.filter fun b ↦ ∃ v, (m.1 v ↔ b = true)),
    mem_filter.2 ⟨mem_univ _, m.2, by simp⟩⟩

/-- The strong JSB hexagon over pointed S5 models with worlds `W`, every world seeing every one. -/
def strongJSBModels (W : Type*) : Fin 6 → Set ((W → Prop) × W) :=
  ![{m | □[Set.univ] m.1 m.2}, {m | □[Set.univ] m.1ᶜ m.2}, {m | ◇[Set.univ] m.1 m.2},
    {m | ◇[Set.univ] m.1ᶜ m.2}, {m | ◇[Set.univ] m.1 m.2 ∧ ◇[Set.univ] m.1ᶜ m.2},
    {m | □[Set.univ] m.1 m.2 ∨ □[Set.univ] m.1ᶜ m.2}]

/-- The weak JSB hexagon over pointed S5 models with worlds `W`. -/
def weakJSBModels (W : Type*) : Fin 6 → Set ((W → Prop) × W) :=
  ![{m | □[Set.univ] m.1 m.2}, {m | □[Set.univ] m.1ᶜ m.2}, {m | ◇[Set.univ] m.1 m.2},
    {m | ◇[Set.univ] m.1ᶜ m.2}, {m | m.1 m.2 ∧ ◇[Set.univ] m.1ᶜ m.2},
    {m | ¬ m.1 m.2 ∨ □[Set.univ] m.1 m.2}]

private theorem mem_atP {t : S5Type} : t ∈ atP ↔ t.1.1 = true := by revert t; decide
private theorem mem_boxP {t : S5Type} : t ∈ boxP ↔ false ∉ t.1.2 := by revert t; decide
private theorem mem_boxNotP {t : S5Type} : t ∈ boxNotP ↔ true ∉ t.1.2 := by revert t; decide
private theorem mem_diaP {t : S5Type} : t ∈ diaP ↔ true ∈ t.1.2 := by revert t; decide
private theorem mem_diaNotP {t : S5Type} : t ∈ diaNotP ↔ false ∈ t.1.2 := by revert t; decide

-- Section 5.1: each formula of the strong hexagon holds of a pointed S5 model iff it holds of the
-- canonical model of the model's type.
theorem strongJSBModels_eq :
    strongJSBModels W = fun i ↦ s5Type ⁻¹' ↑(strongJSB i) := by
  funext i
  ext m
  fin_cases i <;> simp [strongJSBModels, strongJSB, s5Type, mem_boxP, mem_boxNotP, mem_diaP,
    mem_diaNotP, Box, Diamond]

-- Section 5.1: likewise for the weak hexagon.
theorem weakJSBModels_eq : weakJSBModels W = fun i ↦ s5Type ⁻¹' ↑(weakJSB i) := by
  funext i
  ext m
  fin_cases i <;> simp [weakJSBModels, weakJSB, s5Type, mem_atP, mem_boxP, mem_boxNotP,
    mem_diaP, mem_diaNotP, Box, Diamond]

-- With at least two worlds, every S5 type is a pointed model's.
theorem s5Type_surjective [Fintype W] (hW : 2 ≤ Fintype.card W) : Surjective (s5Type (W := W)) := by
  rintro ⟨⟨a, s⟩, ha⟩
  obtain ⟨e⟩ : Nonempty (s ↪ W) := Function.Embedding.nonempty_of_card_le <| by
    rw [Fintype.card_coe]
    exact (card_le_univ s).trans (by simpa using hW)
  have : Nonempty s := ⟨⟨a, ha⟩⟩
  have hg := Function.invFun_surjective e.injective
  have hw : Function.invFun e (e ⟨a, ha⟩) = ⟨a, ha⟩ := Function.leftInverse_invFun e.injective _
  refine ⟨(fun v ↦ (Function.invFun e v).1 = true, e ⟨a, ha⟩), Subtype.ext <| Prod.ext ?_ ?_⟩
  · simp [s5Type, hw]
  · ext b
    simp only [s5Type, mem_filter, mem_univ, true_and]
    refine ⟨fun ⟨v, hv⟩ ↦ ?_, fun hb ↦ ?_⟩
    · exact (Bool.eq_iff_iff.2 hv) ▸ (Function.invFun e v).2
    · obtain ⟨v, hv⟩ := hg ⟨b, hb⟩
      exact ⟨v, by simp [hv]⟩

/-- Pointed S5 models with at least two worlds realize every type of the strong hexagon. -/
noncomputable def strongJSBModelsIso [Fintype W] (hW : 2 ≤ Fintype.card W) :
    BooleanIso strongJSB (strongJSBModels W) :=
  (strongJSBModels_eq (W := W)).symm ▸ BooleanIso.ofSurjective s5Type (s5Type_surjective hW)

/-- Pointed S5 models with at least two worlds realize every type of the weak hexagon. -/
noncomputable def weakJSBModelsIso [Fintype W] (hW : 2 ≤ Fintype.card W) :
    BooleanIso weakJSB (weakJSBModels W) :=
  (weakJSBModels_eq (W := W)).symm ▸ BooleanIso.ofSurjective s5Type (s5Type_surjective hW)

/-- Over pointed S5 models with at least two worlds, the strong and weak JSB hexagons are
Aristotelian isomorphic by the paper's `ρ`. -/
noncomputable def jsbModelsIso [Fintype W] (hW : 2 ≤ Fintype.card W) :
    AristotelianIso (strongJSBModels W) (weakJSBModels W) :=
  (((strongJSBModelsIso hW).symm : AristotelianIso _ _).trans jsbIso).trans (weakJSBModelsIso hW)

/-- Over pointed S5 models with at least two worlds, the strong and weak JSB hexagons are not
Boolean isomorphic. -/
theorem isEmpty_booleanIso_jsbModels [Fintype W] (hW : 2 ≤ Fintype.card W) :
    IsEmpty (BooleanIso (strongJSBModels W) (weakJSBModels W)) :=
  ⟨fun e ↦ isEmpty_booleanIso_jsb.false
    ((strongJSBModelsIso hW).trans (e.trans (weakJSBModelsIso hW).symm))⟩

end S5Models

end DemeySmessaert2018
