module

public import Linglib.Semantics.Quantifier.Global
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Westerståhl (2017): Sameness

Westerståhl asks what it means for a quantifier, given on every universe, to be the same
quantifier on each. Two properties bear on the question. A quantifier is closed under isomorphism
when equivalent universes give it the same value on matching arguments. It satisfies extension
when its value at given arguments does not change as the universe grows around them. The paper's
proposal is to take the two together as the definition of sameness. For determiner denotations
that is `Quantifier.Det.Family.Constant`, invariance along every embedding of universes.

This file states extension for quantifiers of type ⟨1⟩, the global quantifiers of
`Quantifier/Global.lean`, and proves the paper's results about them on finite universes. An
isomorphism-closed quantifier that satisfies extension holds of a set according to its size alone.
Among the isomorphism-closed quantifiers that are monotone on every universe, those satisfying
extension are the quantifier that never holds and the quantifiers *at least `k`*. Every
isomorphism-closed quantifier is nonetheless recovered from one that satisfies both properties:
its relativization is a conservative constant determiner denotation, and the quantifier is that
denotation with the universe as restrictor.

For the monotone quantifiers the paper proposes a weaker condition. Such a quantifier holds of the
sets with at least `f n` members on a universe of `n` individuals, and it is smooth when adding
one individual to the universe leaves `f` unchanged or raises it by one. The universal quantifier
and *more than half* are smooth. Of the paper's two test quantifiers, the first is *more than
half*, and the second, which differs from it on universes of odd size, is not smooth. The
quantifier that is universal on universes of even size and existential on the others is not
smooth either.

## Implementation notes

The paper states extension for an inclusion `M ⊆ M'` of universes. A type is not a subset of
another type, so extension is stated here, as in `Quantifier/Global.lean`, for a subset `M` of a
universe `β` and the universe `↥M`. Universes are finite types, as throughout that file, which is
the paper's setting for its results on monotone quantifiers.

A quantifier that never holds on a universe of `n` individuals has minimum size `n + 1`; `Smooth`
is stated for any function, and the minimum sizes below satisfy `f n ≤ n + 1`.

## TODO

* That extension is closed under the Boolean operations, and that the quantifier *more than half*
  does not satisfy it.
* The paper's Proposition 2, on the operations of relational type that are invariant under
  permutations and satisfy extension, and its Proposition 3, on the monotone quantifiers that
  relativize.

## References

* [westerstahl-2017]
* [feferman-1999]
* [peters-westerstahl-2006]
* [van-benthem-1984]
-/

@[expose] public section

namespace Westerstahl2017

open Quantifier

universe u

variable {Q : Quantifier.Family.{u}}

/-! ### Extension -/

/-- Section 4: a global quantifier satisfies extension when, for `B` inside `M ⊆ β`, it holds of
`B` on the universe `M` exactly when it holds of `B` on `β`. -/
def Ext (Q : Quantifier.Family.{u}) : Prop :=
  ∀ ⦃β : Type u⦄ [Finite β] (M B : Set β), B ⊆ M → (Q M (Subtype.val ⁻¹' B) ↔ Q β B)

/-- (5-b): the quantifier *at least `k`*, which holds of the sets with at least `k` members. -/
def atLeast (k : ℕ) : Quantifier.Family.{u} := fun _ _ B ↦ k ≤ B.ncard

/-- (5-c): the universal quantifier, which holds of the whole universe. -/
def all : Quantifier.Family.{u} := fun _ _ B ↦ B = Set.univ

-- (5-b)
theorem ext_atLeast (k : ℕ) : Ext (atLeast.{u} k) := fun _ _ M B hB ↦ by
  simp only [atLeast]
  rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective (by simpa using hB)]

-- (5-d)
theorem ext_bot : Ext (⊥ : Quantifier.Family.{u}) := fun _ _ _ _ _ ↦ Iff.rfl

-- (5-d)
theorem ext_top : Ext (⊤ : Quantifier.Family.{u}) := fun _ _ _ _ _ ↦ Iff.rfl

-- (5-c)
theorem not_ext_all : ¬ Ext all.{u} := fun h ↦
  Set.empty_ne_univ <| (h (∅ : Set PUnit.{u + 1}) ∅ subset_rfl).1 <|
    Set.eq_univ_of_forall fun x ↦ (Set.notMem_empty _ x.2).elim

theorem iff_of_ncard_eq (hI : Q.Isom) (hE : Ext Q) {α β : Type u} [Finite α] [Finite β]
    {B : Set α} {C : Set β} (h : B.ncard = C.ncard) : Q α B ↔ Q β C := by
  have hB := hE B B subset_rfl
  have hC := hE C C subset_rfl
  rw [Subtype.coe_preimage_self] at hB hC
  rw [← hB, ← hC]
  obtain ⟨e⟩ : Nonempty (↥B ≃ ↥C) := Finite.card_eq.1 h
  simpa using hI e Set.univ

/-- Proposition 4: an isomorphism-closed quantifier that is monotone on every finite universe
satisfies extension if and only if it never holds or is *at least `k`* for some `k`. -/
theorem ext_iff_eq_bot_or_atLeast (hI : Q.Isom) (hm : ∀ (α : Type u) [Finite α], Monotone (Q α)) :
    Ext Q ↔ Q = ⊥ ∨ ∃ k, Q = atLeast k := by
  refine ⟨fun hE ↦ ?_, ?_⟩
  · let s : Set ℕ := {b | ∃ (α : Type u) (_ : Finite α) (B : Set α), B.ncard = b ∧ Q α B}
    have key (α : Type u) [Finite α] (B : Set α) : Q α B ↔ B.ncard ∈ s :=
      ⟨fun h ↦ ⟨α, inferInstance, B, rfl, h⟩,
        fun ⟨β, _, C, hC, h⟩ ↦ (iff_of_ncard_eq hI hE hC).1 h⟩
    have hs : IsUpperSet s := by
      intro b c hbc hb
      induction c, hbc using Nat.le_induction with
      | base => exact hb
      | succ c _ ih =>
        obtain ⟨α, _, B, hB, hQ⟩ := ih
        have h₁ : (some '' B : Set (Option α)).ncard = c := by
          rw [Set.ncard_image_of_injective _ (Option.some_injective α), hB]
        refine ⟨Option α, inferInstance, insert none (some '' B), ?_,
          hm _ (Set.subset_insert _ _) ((iff_of_ncard_eq hI hE (hB.trans h₁.symm)).1 hQ)⟩
        rw [Set.ncard_insert_of_notMem (by simp), h₁]
    rcases hs.eq_empty_or_Ici with h0 | ⟨k, hk⟩
    · exact .inl <| eq_bot_iff.2 <| Quantifier.Family.le_def.2 fun α _ B h ↦
        absurd ((key α B).1 h) (by rw [h0]; exact Set.notMem_empty _)
    · exact .inr ⟨k, funext fun α ↦ funext fun _ ↦ funext fun B ↦
        propext ((key α B).trans (by rw [hk]; rfl))⟩
  · rintro (rfl | ⟨k, rfl⟩)
    exacts [ext_bot, ext_atLeast k]

/-- Section 9: an isomorphism-closed quantifier is recovered from its relativization, a
conservative constant determiner denotation, by taking the universe as the restrictor. -/
theorem constant_rel_and_atUniv_rel (hI : Q.Isom) :
    Q.rel.Conservative ∧ Q.rel.Constant ∧ Q.rel.atUniv = Q :=
  ⟨Q.conservative_rel, hI.constant_rel, hI.atUniv_rel⟩

/-! ### Smooth quantifiers -/

/-- Section 8.1: the monotone quantifier with minimum size `f n` on a universe of `n`
individuals. -/
def ofMinSize (f : ℕ → ℕ) : Quantifier.Family.{u} := fun α _ B ↦ f (Nat.card α) ≤ B.ncard

/-- Section 8.1: a minimum size is smooth when adding one individual to the universe leaves it
unchanged or raises it by one. -/
def Smooth (f : ℕ → ℕ) : Prop := ∀ n, f n ≤ f (n + 1) ∧ f (n + 1) ≤ f n + 1

/-- Section 4, (5-f): the Rescher quantifier *more than half*, which holds of the sets with more
members than their complement. -/
def rescher : Quantifier.Family.{u} := fun _ _ B ↦ Bᶜ.ncard < B.ncard

/-- Section 7: the minimum size of the first test quantifier. -/
def test1 (n : ℕ) : ℕ := if n % 2 = 0 then (n + 2) / 2 else (n + 1) / 2

/-- Section 7: the minimum size of the second test quantifier. -/
def test2 (n : ℕ) : ℕ := if n % 2 = 0 then (n + 2) / 2 else (n - 1) / 2

/-- Section 7: the minimum size of the quantifier that is universal on universes of even size and
existential on the others. -/
def allEven (n : ℕ) : ℕ := if n % 2 = 0 then n else 1

/-- Section 7: the first test quantifier is *more than half*. -/
theorem ofMinSize_test1 : ofMinSize.{u} test1 = rescher := by
  funext α _ B
  have h := Set.ncard_add_ncard_compl B
  simp only [ofMinSize, rescher, test1, eq_iff_iff]
  split <;> omega

-- Section 8.1
theorem smooth_id : Smooth id := fun n ↦ by simp

/-- Section 8.1: *more than half* is smooth. -/
theorem smooth_test1 : Smooth test1 := fun n ↦ by
  simp only [test1]
  split <;> split <;> omega

/-- Section 8.1: the second test quantifier is not smooth, its minimum size rising by two from a
universe of three individuals to one of four. -/
theorem not_smooth_test2 : ¬ Smooth test2 := fun h ↦ by
  have := (h 3).2
  simp [test2] at this

-- Section 8.1
theorem not_smooth_allEven : ¬ Smooth allEven := fun h ↦ by
  have := (h 2).1
  simp [allEven] at this

end Westerstahl2017
