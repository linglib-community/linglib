module

public import Mathlib.Data.Finset.Interval
public import Linglib.Semantics.Quantification.Witness
public import Linglib.Semantics.Quantification.Counting
public import Mathlib.Data.Finset.Powerset

/-!
# Lücking and Ginzburg (2022): Referential Transparency as the Proper Treatment for Quantification

This file formalizes the denotations of quantified noun phrases in the referential
transparency theory of [lucking-ginzburg-2022]. In place of the sets of sets of generalized
quantifier theory ([barwise-cooper-1981]), a quantified noun phrase denotes a set of ordered
bipartitions of the head noun's extension into a reference set and its complement set, the
quantifier word acting as a sieve on them through a descriptive condition on the two
cardinalities (`sieve`). Such a condition is a quantifier on [van-benthem-1984]'s tree of numbers
(`Quantifier.NumberTree`), and the sieve reads only the row of the tree at the size of the noun
(`sieve_eq_iff`), which yields the paper's count of `2 ^ (k + 1) - 1` denotations over a noun
with `k` instances (`card_Ioc_antidiagonal`). A verb phrase predicates on the
reference set and anti-predicates on the complement set (`AntiPredication`), so the sentence is
true exactly when the condition holds of the sizes of `N \ VP` and `N ∩ VP`
(`exists_antiPredication_iff`). So referential transparency has the truth conditions of the tree
quantifier of its condition (`exists_antiPredication_iff_toGQ`), which recovers the paper's claim
that the set-up entails the conservativity universal (`livesOn_toGQ`), and the surviving reference
sets are exactly the witness sets of [barwise-cooper-1981] (`mem_sieve_iff_witness`). The
quantifier perspective, whether the bipartition with an empty reference set survives the sieve,
gates anaphora to the complement set (the paper's (47), `CompsetAccessible`,
`compsetAccessible_sieve`). The paper's minimal pair (43a) ~ (44): *few* and *a few* share their
condition, but *a few* carries a reference individual, so its denotation lacks the
empty-reference bipartition and the complement set is inaccessible whatever the condition
(`compsetAccessible_few`, `not_compsetAccessible_refind`).

## Implementation notes

An ordered bipartition of `S` (the paper's (15)) is determined by its reference set `R ⊆ S`, the
complement set being `S \ R`, so a denotation is a `Finset (Finset α)` of reference sets and the
bipartitions of `S` are its powerset. A condition on the cardinalities of the complement and
reference sets is a `NumberTree`, whose coordinates are `|A \ B|` and `|A ∩ B|`, in the order
of the paper's (18), so the paper's *every*, *no* and *some* are the tree's `all`, `no` and
`some`. *Few* takes the proportional sense of (38a), its *much smaller* weakened to a strict
comparison; the cardinal sense of (38b), *few* against a contextual standard, is not represented.
The contextual standard of *many* is a parameter. Anti-predication, the negation of a plural type
on the complement set, is read distributively as the paper's gloss of (55b) does. The quantifier
perspective is derived from the denotation as the proposition that the empty reference set is in
it, where the paper carries it as a lexical feature; its third value for degenerate denotations
collapses into inaccessibility, which gates anaphora identically. The count of §4.8 is read off
the paper's enumeration for two individuals, the non-empty selections of cardinality types; the
paper's own gloss of the subtraction speaks of the empty set. Negation of a noun phrase, which
the paper's (49) shows to flip accessibility, the dialogue and gesture data, the
clarification-request diagnostics, and the type-theoretic encoding are not represented.

## TODO

Read as the cardinal condition `|refset| < 100`, *fewer than 100* in the paper's (43d) keeps the
empty reference set, so the derived perspective makes the complement set accessible where the
paper marks the anaphora bad; the paper's lexical feature can stipulate its way past the case.

The paper's count of 63 quantifiers on a two-element domain (§4.8) multiplies the per-noun count
over the subsets of the domain rather than over their sizes, so it distinguishes the two
singletons, against its own restriction to quantitative quantifiers in the same section.

## References

* [lucking-ginzburg-2022]
* [barwise-cooper-1981]
* [van-benthem-1984]
* [keenan-stavi-1986]
-/

@[expose] public section

namespace LuckingGinzburg2022

open Finset Quantifier Quantifier.NP Quantifier.NumberTree
open scoped Finset

variable {α : Type*} [DecidableEq α] {q : NumberTree} [DecidableRel q] {S R : Finset α}

/-! ### The sieve -/

/-- The ordered bipartitions of the head noun's extension `S` (the paper's (15)) sifted by the
condition `q` on the sizes of the complement set and the reference set: the reference sets
`R ⊆ S` with `q |S \ R| |R|`. -/
def sieve (q : NumberTree) [DecidableRel q] (S : Finset α) : Finset (Finset α) :=
  S.powerset.filter fun R ↦ q #(S \ R) #R

@[simp] theorem mem_sieve : R ∈ sieve q S ↔ R ⊆ S ∧ q #(S \ R) #R := by simp [sieve]

theorem sieve_congr {q' : NumberTree} [DecidableRel q']
    (h : ∀ a b, a + b = #S → (q a b ↔ q' a b)) : sieve q S = sieve q' S := by
  ext R
  simp only [mem_sieve]
  refine and_congr_right fun hR ↦ h _ _ ?_
  rw [card_sdiff_of_subset hR, Nat.sub_add_cancel (card_le_card hR)]

/-! ### Descriptive quantifier conditions -/

/-- The condition of *many* (the paper's (39)), a reference set exceeding a contextual standard
`θ`; a cardinal quantifier. -/
def many (θ : ℕ) : NumberTree := cardinal (Set.Ioi θ)

instance (θ : ℕ) : DecidableRel (many θ) := fun _ b ↦ inferInstanceAs (Decidable (θ < b))

/-! ### Quantifier perspective and complement-set anaphora -/

/-- The complement set of a denotation is available to anaphora (the paper's (47)) when the
bipartition with an empty reference set is in the denotation, the value `refset = ∅` of the
quantifier perspective (48). -/
def CompsetAccessible (D : Finset (Finset α)) : Prop := ∅ ∈ D

instance (D : Finset (Finset α)) : Decidable (CompsetAccessible D) :=
  inferInstanceAs (Decidable (∅ ∈ D))

theorem compsetAccessible_sieve : CompsetAccessible (sieve q S) ↔ q #S 0 := by
  simp [CompsetAccessible]

/-- *Every N* makes the complement set inaccessible, the noun being nonempty, as in the paper's
(49a), *All music lovers admire Reger. #They love Mozart.* -/
theorem not_compsetAccessible_all (hS : S.Nonempty) :
    ¬ CompsetAccessible (sieve NumberTree.all S) := fun h ↦
  hS.card_pos.ne' ((compsetAccessible_sieve (q := NumberTree.all)).1 h)

/-- *No N* makes the complement set accessible, the empty reference set being its denotation
(§4.3). -/
theorem compsetAccessible_no : CompsetAccessible (sieve NumberTree.no S) :=
  compsetAccessible_sieve.2 rfl

/-- *Many N* makes the complement set inaccessible, as in the paper's (43b), *Many music lovers
admire Reger. #They prefer Mozart.* -/
theorem not_compsetAccessible_many (θ : ℕ) : ¬ CompsetAccessible (sieve (many θ) S) := fun h ↦
  Nat.not_lt_zero θ ((compsetAccessible_sieve (q := many θ)).1 h)

/-- *Few N* makes the complement set accessible, the noun being nonempty, as in the paper's
(43a), *Few music lovers admire Reger. They prefer Mozart.* -/
theorem compsetAccessible_few (hS : S.Nonempty) : CompsetAccessible (sieve NumberTree.few S) :=
  compsetAccessible_sieve.2 hS.card_pos

/-- The reference individual of *a few* (the paper's (46)) requires a nonempty reference set,
which removes the empty-reference bipartition from a denotation. -/
def refind (D : Finset (Finset α)) : Finset (Finset α) := D.erase ∅

/-- A denotation with a reference individual never makes its complement set accessible, so *a few*
blocks the anaphora of (44). -/
theorem not_compsetAccessible_refind (D : Finset (Finset α)) : ¬ CompsetAccessible (refind D) :=
  notMem_erase _ _

/-! ### Predication and anti-predication -/

/-- Two-headed predication (§4.5): the verb phrase holds throughout the reference set and fails
throughout the complement set. -/
def AntiPredication (B : α → Prop) (S R : Finset α) : Prop :=
  (∀ a ∈ R, B a) ∧ ∀ a ∈ S \ R, ¬ B a

variable {B : α → Prop} [DecidablePred B]

theorem antiPredication_iff (hR : R ⊆ S) : AntiPredication B S R ↔ R = S.filter B := by
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ext fun a ↦ ?_, fun h ↦ h ▸ ⟨fun a ha ↦ (mem_filter.1 ha).2,
    fun a ha hB ↦ (mem_sdiff.1 ha).2 (mem_filter.2 ⟨(mem_sdiff.1 ha).1, hB⟩)⟩⟩
  simp only [mem_filter]
  exact ⟨fun ha ↦ ⟨hR ha, h₁ a ha⟩,
    fun ⟨haS, haB⟩ ↦ by_contra fun haR ↦ h₂ a (mem_sdiff.2 ⟨haS, haR⟩) haB⟩

/-- Some surviving bipartition of *q N VP* is anti-predicated iff the condition holds of the sizes
of `N \ VP` and `N ∩ VP` (§4.5). -/
theorem exists_antiPredication_iff :
    (∃ R ∈ sieve q S, AntiPredication B S R) ↔ q #(S \ S.filter B) #(S.filter B) :=
  ⟨fun ⟨_, hR, h⟩ ↦ (antiPredication_iff (mem_sieve.1 hR).1).1 h ▸ (mem_sieve.1 hR).2,
    fun hq ↦ ⟨S.filter B, mem_sieve.2 ⟨filter_subset _ _, hq⟩,
      (antiPredication_iff (filter_subset _ _)).2 rfl⟩⟩

omit [DecidableEq α] in
private theorem ncard_mem_and : {x | x ∈ S ∧ B x}.ncard = #(S.filter B) := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter]

theorem exists_antiPredication_iff_toGQ :
    (∃ R ∈ sieve q S, AntiPredication B S R) ↔ q.toGQ (· ∈ S) B := by
  rw [exists_antiPredication_iff, toGQ_apply, ncard_mem_and, ncard_mem_and, filter_not]

omit [DecidableEq α] [DecidableRel q] in
theorem livesOn_toGQ : LivesOn (q.toGQ (· ∈ S)) (· ∈ S) :=
  (conservative_toGQ q).livesOn _

/-! ### Witness sets -/

/-- The surviving reference sets (17) are exactly the [barwise-cooper-1981] witness sets of the tree
quantifier on the head noun. -/
theorem mem_sieve_iff_witness :
    R ∈ sieve q S ↔ Witness (q.toGQ (· ∈ S)) (· ∈ S) (· ∈ R) := by
  simp only [mem_sieve, Witness, toGQ_apply, ncard_mem_and, subset_iff]
  refine and_congr_right fun hR ↦ ?_
  rw [filter_not, filter_mem_eq_inter, inter_eq_right.2 fun _ h ↦ hR h]

/-! ### Complexity -/

/-- The points of row `k` of the tree a condition selects, the denotation on a noun with `k`
instances up to the choice of reference sets. -/
def row (q : NumberTree) [DecidableRel q] (k : ℕ) : Finset (ℕ × ℕ) :=
  (antidiagonal k).filter fun p ↦ q p.1 p.2

theorem sieve_eq_iff {q' : NumberTree} [DecidableRel q'] :
    sieve q S = sieve q' S ↔ row q #S = row q' #S := by
  refine ⟨fun h ↦ ?_, fun h ↦ sieve_congr fun a b hab ↦ ?_⟩
  · ext ⟨a, b⟩
    simp only [row, mem_filter, mem_antidiagonal]
    refine and_congr_right fun hab ↦ ?_
    obtain ⟨R, hR, hb⟩ := exists_subset_card_eq (s := S) (n := b) (by omega)
    have ha : #(S \ R) = a := by rw [card_sdiff_of_subset hR]; omega
    simpa [hR, ha, hb] using congrArg (R ∈ ·) h
  · simpa [row, hab] using congrArg ((a, b) ∈ ·) h

/-- The nonempty sets of points of row `k` number `2 ^ (k + 1) - 1`, the possible denotations over a
noun with `k` instances (§4.8). -/
theorem card_Ioc_antidiagonal (k : ℕ) : #(Ioc ∅ (antidiagonal k)) = 2 ^ (k + 1) - 1 := by
  rw [card_Ioc_finset (empty_subset _), Nat.card_antidiagonal, card_empty, Nat.sub_zero]

/-- The paper's count of quantifiers on a domain `M` (§4.8): a nonempty selection of a row for
each subset of the domain, taken as a head noun's extension. -/
def domainCount (M : Finset α) : ℕ := ∏ R ∈ M.powerset, (2 ^ (#R + 1) - 1)

/-- The seven denotations over two individuals enumerated in §4.8. -/
example : #(Ioc ∅ (antidiagonal 2)) = 7 := by decide

/-- The paper's `1 × 3 × 3 × 7 = 63` quantifiers on a domain of two individuals, against the 512
conservative ones it cites, the `2 ^ 3 ^ 2` of [keenan-stavi-1986]. -/
example : domainCount (univ : Finset (Fin 2)) = 63 ∧ 63 < 2 ^ 3 ^ 2 := by decide

end LuckingGinzburg2022
