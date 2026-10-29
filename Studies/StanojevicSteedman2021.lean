module

public import Mathlib.Combinatorics.Enumerative.Schroder
public import Mathlib.Data.List.Permutation
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.SuccPred.Nat
public import Linglib.Syntax.CCG.Grammar
public import Studies.Cinque2005

/-!
# Stanojević and Steedman (2021): Formal Basis of a Language Universal

This file formalizes [stanojevic-steedman-2021]'s proof of the universal [steedman-2020]
proposes: over a natural order of dominance, a chain of first-order categories
`X₁|X₂, X₂|X₃, …, Xₙ|Xₙ₊₁` each realizable with either slash direction, combinatory categorial
grammar derives all and only the separable permutations of the canonical linearization. The
chain is the multimodal grammar `nodGrammar` over the lexicon giving word `i` both `Xᵢ/Xᵢ₊₁`
and `Xᵢ\Xᵢ₊₁`, and the separable permutations of a span are `SepPerm`, the separating-tree
characterization of [bose-buss-lubiw-1998]: a singleton, or two contiguous parts of the span
concatenated in canonical or inverted order. Completeness (`derives_of_sepPerm`) is the
paper's three lemmas in one induction, canonical splits combining by forward and inverted
splits by backward composition; soundness (`sepPerm_of_derives`) is the rule induction, in
which application and second-order composition never fire over a first-order chain; the
universal is `derives_fwd_iff` with its mirror `derives_bwd_iff`.

The enumeration `sepPerms` lists the separable permutations of a span by their separating
trees and makes `SepPerm` decidable. Over four elements it has the third large Schröder number
of members, twenty-two of the twenty-four orders (`card_sepPerms_four`); the two orders it
excludes, 2413 and 3142, are the noun-phrase and verb-cluster orders unattested in the surveys
of [cinque-2005], [nchare-2012] and [abels-2016], and the grammar does not derive them
(`not_derives_2413`, `not_derives_3142`). Every order of demonstrative, numeral, adjective
and noun that [cinque-2005] attests is separable, and the non-separable orders are exactly
the paper's (g) and (j) (`cinque_attested_separable`, `cinque_not_sepPerm_iff`). The chance
that a theory excluding two of the twenty-four orders survives twenty-one attested ones
sampled uniformly is the paper's one in a hundred (`chanceUnfalsified_two_of_twentyfour`).

## Implementation notes

The paper's Theorem 3, that the separable permutations of `n` elements number the
`(n - 1)`th large Schröder number of [shapiro-stephens-1991], is stated at `n = 4` against
mathlib's `Nat.largeSchroder`; the general count goes through the normal-form separating trees
of the paper's fourth section and is not formalized. The pattern-avoidance characterization of
[west-1996] and the extension to second-order categories and type-raising are not
formalized. The dominance relation is the first-order case of [koller-kuhlmann-2009]'s
dependency structures for CCG. The tokens are the chain positions themselves, so a derived
string is the permutation it realizes.

## References

* [stanojevic-steedman-2021]
* [steedman-2020]
* [bose-buss-lubiw-1998]
* [shapiro-stephens-1991]
* [west-1996]
* [koller-kuhlmann-2009]
* [cinque-2005]
* [nchare-2012]
* [abels-2016]
-/

@[expose] public section

namespace StanojevicSteedman2021

open CCG

/-! ### The natural order of dominance -/

/-- The forward realization `Xᵢ/Xᵢ₊₁` of chain position `i`. -/
def fwd (i : ℕ) : Cat ℕ := .rslash (.atom i) .dot (.atom (i + 1))

/-- The backward realization `Xᵢ\Xᵢ₊₁` of chain position `i`. -/
def bwd (i : ℕ) : Cat ℕ := .lslash (.atom i) .dot (.atom (i + 1))

/-- The natural-order-of-dominance lexicon over `n` words gives each position both slash
realizations of its chain category, the paper's order-free `|`. -/
def nodLexicon (n : ℕ) : List (ℕ × Cat ℕ) :=
  (List.range n).flatMap fun i ↦ [(i + 1, fwd (i + 1)), (i + 1, bwd (i + 1))]

/-- The NOD grammar is the multimodal grammar over the chain lexicon. The start atom plays no
role in the span-level claims. -/
def nodGrammar (n : ℕ) : Grammar ℕ ℕ := .multimodal (nodLexicon n) 1 2

theorem mem_nodLexicon {n m : ℕ} (h1 : 1 ≤ m) (hn : m ≤ n) :
    (m, fwd m) ∈ nodLexicon n ∧ (m, bwd m) ∈ nodLexicon n := by
  have : m - 1 ∈ List.range n := List.mem_range.mpr (by omega)
  constructor <;> [refine List.mem_flatMap.mpr ⟨m - 1, this, ?_⟩;
    refine List.mem_flatMap.mpr ⟨m - 1, this, ?_⟩] <;>
    simp [show m - 1 + 1 = m from by omega]

/-! ### Separable permutations -/

/-- The separable permutations of the span `i…j`, by separating trees. Each is a singleton, or
two contiguous parts of the span concatenated in canonical (`pos`) or inverted (`neg`) order. -/
inductive SepPerm : ℕ → ℕ → List ℕ → Prop where
  /-- A single word is a separable permutation of its own span. -/
  | single (i : ℕ) : SepPerm i i [i]
  /-- Contiguous parts in canonical order. -/
  | pos {i j k : ℕ} {u v : List ℕ} :
      SepPerm i j u → SepPerm (j + 1) k v → SepPerm i k (u ++ v)
  /-- Contiguous parts in inverted order. -/
  | neg {i j k : ℕ} {u v : List ℕ} :
      SepPerm i j u → SepPerm (j + 1) k v → SepPerm i k (v ++ u)

theorem SepPerm.le {i j : ℕ} {l : List ℕ} (h : SepPerm i j l) : i ≤ j := by
  induction h with
  | single => omega
  | pos _ _ ih1 ih2 => omega
  | neg _ _ ih1 ih2 => omega

theorem SepPerm.eq_single {i : ℕ} {l : List ℕ} (h : SepPerm i i l) : l = [i] := by
  cases h with
  | single => rfl
  | pos hu hv => have := hu.le; have := hv.le; omega
  | neg hu hv => have := hu.le; have := hv.le; omega

theorem SepPerm.perm {i j : ℕ} {l : List ℕ} (h : SepPerm i j l) :
    l.Perm (List.range' i (j + 1 - i)) := by
  induction h with
  | single i => simp
  | @pos i j k u v hu hv ihu ihv =>
    have h1 : i + (j + 1 - i) = j + 1 := by have := hu.le; omega
    have h2 : j + 1 - i + (k + 1 - (j + 1)) = k + 1 - i := by have := hu.le; have := hv.le; omega
    exact (ihu.append ihv).trans (List.Perm.of_eq (by rw [← h2, ← List.range'_append_1, h1]))
  | @neg i j k u v hu hv ihu ihv =>
    have h1 : i + (j + 1 - i) = j + 1 := by have := hu.le; omega
    have h2 : j + 1 - i + (k + 1 - (j + 1)) = k + 1 - i := by have := hu.le; have := hv.le; omega
    exact List.perm_append_comm.trans
      ((ihu.append ihv).trans (List.Perm.of_eq (by rw [← h2, ← List.range'_append_1, h1])))

/-- The separable permutations of `i…j` listed by their separating trees, with `fuel` bounding
the span length. -/
def sepPermsAux : ℕ → ℕ → ℕ → Finset (List ℕ)
  | 0, _, _ => ∅
  | fuel + 1, i, j =>
    if j < i then ∅ else if i = j then {[i]} else
      (Finset.Ico i j).biUnion fun k ↦
        (sepPermsAux fuel i k ×ˢ sepPermsAux fuel (k + 1) j).image (fun p ↦ p.1 ++ p.2) ∪
        (sepPermsAux fuel i k ×ˢ sepPermsAux fuel (k + 1) j).image (fun p ↦ p.2 ++ p.1)

/-- The separable permutations of the span `i…j`. -/
def sepPerms (i j : ℕ) : Finset (List ℕ) := sepPermsAux (j + 1 - i) i j

theorem mem_sepPermsAux {fuel i j : ℕ} (hf : j + 1 - i ≤ fuel) {l : List ℕ} :
    l ∈ sepPermsAux fuel i j ↔ SepPerm i j l := by
  induction fuel generalizing i j l with
  | zero =>
    simp only [sepPermsAux, Finset.notMem_empty, false_iff]
    intro h; have := h.le; omega
  | succ fuel ih =>
    simp only [sepPermsAux]
    split_ifs with hlt heq
    · simp only [Finset.notMem_empty, false_iff]
      intro h; have := h.le; omega
    · subst heq
      simp only [Finset.mem_singleton]
      exact ⟨fun h ↦ h ▸ .single _, SepPerm.eq_single⟩
    · simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_union, Finset.mem_image,
        Finset.mem_product, Prod.exists]
      constructor
      · rintro ⟨k, ⟨hik, hkj⟩, ⟨u, v, ⟨hu, hv⟩, rfl⟩ | ⟨u, v, ⟨hu, hv⟩, rfl⟩⟩
        · exact .pos ((ih (by omega)).mp hu) ((ih (by omega)).mp hv)
        · exact .neg ((ih (by omega)).mp hu) ((ih (by omega)).mp hv)
      · intro h
        cases h with
        | single => exact absurd rfl heq
        | @pos _ k _ u v hu hv =>
          have := hu.le; have := hv.le
          exact ⟨k, ⟨by omega, by omega⟩,
            Or.inl ⟨u, v, ⟨(ih (by omega)).mpr hu, (ih (by omega)).mpr hv⟩, rfl⟩⟩
        | @neg _ k _ u v hu hv =>
          have := hu.le; have := hv.le
          exact ⟨k, ⟨by omega, by omega⟩,
            Or.inr ⟨u, v, ⟨(ih (by omega)).mpr hu, (ih (by omega)).mpr hv⟩, rfl⟩⟩

theorem mem_sepPerms {i j : ℕ} {l : List ℕ} : l ∈ sepPerms i j ↔ SepPerm i j l :=
  mem_sepPermsAux le_rfl

instance (i j : ℕ) (l : List ℕ) : Decidable (SepPerm i j l) :=
  decidable_of_iff _ mem_sepPerms

/-- The separable permutations of `1…4` number the third large Schröder number, twenty-two of
the twenty-four orders, which is Theorem 3 at four elements. -/
theorem card_sepPerms_four : (sepPerms 1 4).card = Nat.largeSchroder 3 := by
  rw [show Nat.largeSchroder 3 = 22 by
    simp [Nat.largeSchroder_succ, ← Finset.Iio_add_one_eq_Iic, Nat.Iio_eq_range,
      Finset.sum_range_succ]]
  decide

theorem not_sepPerm_2413 : ¬ SepPerm 1 4 [2, 4, 1, 3] := by decide

theorem not_sepPerm_3142 : ¬ SepPerm 1 4 [3, 1, 4, 2] := by decide

/-! ### Completeness

Every separable permutation of the span `i…j` is derivable at both slashings of the span
category `Xᵢ|Xⱼ₊₁`, the paper's three lemmas in one induction: canonical splits combine by
(possibly crossing) forward composition, inverted splits by backward composition, and the
strengthened both-slashes hypothesis feeds the harmonic and crossing cases alike. -/

theorem derives_of_sepPerm {n i j : ℕ} {l : List ℕ} (h1 : 1 ≤ i) (hn : j ≤ n)
    (h : SepPerm i j l) :
    (nodGrammar n).Derives (.rslash (.atom i) .dot (.atom (j + 1))) l ∧
    (nodGrammar n).Derives (.lslash (.atom i) .dot (.atom (j + 1))) l := by
  induction h with
  | single m =>
    obtain ⟨hf, hb⟩ := mem_nodLexicon h1 hn
    exact ⟨.lex hf, .lex hb⟩
  | @pos i j k u v hu hv ihu ihv =>
    obtain ⟨huf, hub⟩ := ihu h1 (by have := hv.le; omega)
    obtain ⟨hvf, hvb⟩ := ihv (by omega) hn
    exact ⟨.forward [⟨.right, .dot, .atom (k + 1)⟩] huf hvf (by simp [nodGrammar]),
      .forward [⟨.left, .dot, .atom (k + 1)⟩] huf hvb (by simp [nodGrammar])⟩
  | @neg i j k u v hu hv ihu ihv =>
    obtain ⟨huf, hub⟩ := ihu h1 (by have := hv.le; omega)
    obtain ⟨hvf, hvb⟩ := ihv (by omega) hn
    exact ⟨.backward [⟨.right, .dot, .atom (k + 1)⟩] hvf hub (by simp [nodGrammar]),
      .backward [⟨.left, .dot, .atom (k + 1)⟩] hvb hub (by simp [nodGrammar])⟩

/-! ### Soundness

Everything derivable over the NOD grammar is a span category `Xᵢ|Xⱼ₊₁` over a separable
permutation of `i…j`. All derivable categories are first-order, so application, which needs
an atomic secondary, and second-order composition, which needs a second-order secondary,
never fire. -/

theorem sepPerm_of_derives {n : ℕ} {c : Cat ℕ} {w : List ℕ}
    (h : (nodGrammar n).Derives c w) :
    ∃ i j, 1 ≤ i ∧ j ≤ n ∧ SepPerm i j w ∧
      (c = .rslash (.atom i) .dot (.atom (j + 1)) ∨
       c = .lslash (.atom i) .dot (.atom (j + 1))) := by
  induction h with
  | @lex w' c' hmem =>
    obtain ⟨m, hm, hentry⟩ := List.mem_flatMap.mp hmem
    have hm' := List.mem_range.mp hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hentry
    rcases hentry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨m + 1, m + 1, by omega, by omega, .single _, Or.inl rfl⟩
    · exact ⟨m + 1, m + 1, by omega, by omega, .single _, Or.inr rfl⟩
  | @forward x y m β _ _ _ _ _ iha ihb =>
    obtain ⟨i, j, hi, hj, hsep, hcat⟩ := iha
    obtain ⟨i', j', hi', hj', hsep', hcat'⟩ := ihb
    obtain ⟨rfl, rfl, rfl⟩ : x = .atom i ∧ m = .dot ∧ y = .atom (j + 1) := by simpa using hcat
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (j + 1 = i' ∧ β = [⟨.right, .dot, .atom (j' + 1)⟩]) ∨
        (j + 1 = i' ∧ β = [⟨.left, .dot, .atom (j' + 1)⟩]) := by
      simpa [Cat.atom_pushArgs_eq_iff] using hcat'
    · exact ⟨i, j', hi, hj', .pos hsep hsep', Or.inl rfl⟩
    · exact ⟨i, j', hi, hj', .pos hsep hsep', Or.inr rfl⟩
  | @backward x y m β _ _ _ _ _ iha ihb =>
    obtain ⟨i, j, hi, hj, hsep, hcat⟩ := iha
    obtain ⟨i', j', hi', hj', hsep', hcat'⟩ := ihb
    obtain ⟨rfl, rfl, rfl⟩ : x = .atom i' ∧ m = .dot ∧ y = .atom (j' + 1) := by
      simpa using hcat'
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (j' + 1 = i ∧ β = [⟨.right, .dot, .atom (j + 1)⟩]) ∨
        (j' + 1 = i ∧ β = [⟨.left, .dot, .atom (j + 1)⟩]) := by
      simpa [Cat.atom_pushArgs_eq_iff] using hcat
    · exact ⟨i', j, hi', hj, .neg hsep' hsep, Or.inl rfl⟩
    · exact ⟨i', j, hi', hj, .neg hsep' hsep, Or.inr rfl⟩

/-! ### The universal -/

theorem derives_fwd_iff {n i j : ℕ} {l : List ℕ} (h1 : 1 ≤ i) (hn : j ≤ n) :
    (nodGrammar n).Derives (.rslash (.atom i) .dot (.atom (j + 1))) l ↔ SepPerm i j l := by
  refine ⟨fun h ↦ ?_, fun h ↦ (derives_of_sepPerm h1 hn h).1⟩
  obtain ⟨i', j', -, -, hsep, hcat | hcat⟩ := sepPerm_of_derives h
  · obtain ⟨rfl, rfl⟩ : i = i' ∧ j = j' := by simpa using hcat
    exact hsep
  · exact absurd hcat (by simp)

theorem derives_bwd_iff {n i j : ℕ} {l : List ℕ} (h1 : 1 ≤ i) (hn : j ≤ n) :
    (nodGrammar n).Derives (.lslash (.atom i) .dot (.atom (j + 1))) l ↔ SepPerm i j l := by
  refine ⟨fun h ↦ ?_, fun h ↦ (derives_of_sepPerm h1 hn h).2⟩
  obtain ⟨i', j', -, -, hsep, hcat | hcat⟩ := sepPerm_of_derives h
  · exact absurd hcat (by simp)
  · obtain ⟨rfl, rfl⟩ : i = i' ∧ j = j' := by simpa using hcat
    exact hsep

theorem perm_of_derives {n i j : ℕ} {l : List ℕ} (h1 : 1 ≤ i) (hn : j ≤ n)
    (h : (nodGrammar n).Derives (.rslash (.atom i) .dot (.atom (j + 1))) l) :
    l.Perm (List.range' i (j + 1 - i)) :=
  ((derives_fwd_iff h1 hn).mp h).perm

theorem not_derives_2413 :
    ¬ (nodGrammar 4).Derives (.rslash (.atom 1) .dot (.atom 5)) [2, 4, 1, 3] :=
  mt (derives_fwd_iff le_rfl le_rfl).mp not_sepPerm_2413

theorem not_derives_3142 :
    ¬ (nodGrammar 4).Derives (.rslash (.atom 1) .dot (.atom 5)) [3, 1, 4, 2] :=
  mt (derives_fwd_iff le_rfl le_rfl).mp not_sepPerm_3142

/-! ### The typological record -/

/-- The position of a nominal category in the natural order of dominance of the paper's (1),
which orders demonstrative, numeral, adjective and noun. -/
def nominalRank : Minimalist.Cat → ℕ
  | .Dem => 1
  | .Num => 2
  | .A => 3
  | .N => 4
  | _ => 0

theorem cinque_attested_separable :
    ∀ r ∈ Cinque2005.table, r.Attested → SepPerm 1 4 (r.order.map nominalRank) := by
  decide

theorem cinque_not_sepPerm_iff :
    ∀ r ∈ Cinque2005.table, ¬ SepPerm 1 4 (r.order.map nominalRank) ↔
      r.order = [.Num, .N, .Dem, .A] ∨ r.order = [.A, .Dem, .N, .Num] := by
  decide

/-- The chance that a theory excluding `e` of `N` equiprobable orders is not falsified by `a`
attested orders sampled without replacement: the sets of `a` orders consistent with the theory
over all sets of `a` orders. -/
def chanceUnfalsified (N e a : ℕ) : ℚ := ((N - e).choose a : ℚ) / N.choose a

/-- Excluding two of the twenty-four orders and surviving twenty-one attested ones has a
chance of about one in a hundred, the paper's (19). -/
theorem chanceUnfalsified_two_of_twentyfour : chanceUnfalsified 24 2 21 = 11 / 1012 := by
  rw [chanceUnfalsified, show 24 - 2 = 22 from rfl, show Nat.choose 22 21 = 22 by decide,
    show Nat.choose 24 21 = 2024 by decide]
  norm_num

-- (20)
theorem chanceUnfalsified_two_of_twentyfour' : chanceUnfalsified 24 2 22 = 1 / 276 := by
  rw [chanceUnfalsified, show 24 - 2 = 22 from rfl, show Nat.choose 22 22 = 1 by decide,
    show Nat.choose 24 22 = 276 by decide]
  norm_num

end StanojevicSteedman2021
