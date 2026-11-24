module

public import Linglib.Semantics.Quantifier.Global

/-!
# Westerståhl (2017): Sameness

Westerståhl asks what it means for a quantifier, given on every universe, to be the same
quantifier on each. Two properties bear on the question. A quantifier is closed under isomorphism
when equivalent universes give it the same value on matching arguments. It satisfies extension
when its value at given arguments does not change as the universe grows around them. The paper's
proposal is to take the two together as the definition of sameness. For determiner denotations
that is `Quantifier.Det.Family.Constant`, invariance along every embedding of universes.

This file proves the paper's results about quantifiers of type ⟨1⟩, the global quantifiers of
`Quantifier/Global.lean`, on finite universes. An isomorphism-closed quantifier is given by a tree
of numbers, and it satisfies extension when that tree is cardinal and is monotone when the tree is
scope monotone. Among the isomorphism-closed quantifiers that are monotone on every universe, those
satisfying extension are the quantifier that never holds and the quantifiers *at least `k`*. Every
isomorphism-closed quantifier is nonetheless recovered from one that satisfies both properties: its
relativization is a conservative constant determiner denotation, and the quantifier is that
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
another type, so `Quantifier.Family.Ext` is stated for a subset `M` of a universe `β` and the
universe `↥M`. Universes are finite types, as throughout that file, which is
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

open Quantifier Quantifier.NumberTree

universe u

variable {Q : Quantifier.Family.{u}}

/-! ### Extension -/

/-- (5-b): the quantifier *at least `k`*, the determiner denotation *at least `k`* with the
universe as its restrictor. -/
def atLeast (k : ℕ) : Quantifier.Family.{u} := (Det.Family.atLeast k).atUniv

/-- (5-c): the universal quantifier, *every* with the universe as its restrictor. -/
def all : Quantifier.Family.{u} := Det.Family.every.atUniv

theorem atLeast_apply (k : ℕ) (α : Type u) [Finite α] (B : Set α) :
    atLeast k α B ↔ k ≤ B.ncard := by
  simp [atLeast, Det.Family.atUniv, Det.Family.atLeast, Det.atLeast_apply]

theorem all_apply (α : Type u) [Finite α] (B : Set α) : all α B ↔ B = Set.univ := by
  simp [all, Det.Family.atUniv, Det.Family.every, Det.every, Set.univ_subset_iff]

-- (5-b)
theorem ext_atLeast (k : ℕ) : (atLeast.{u} k).Ext := fun _ _ M B hB ↦ by
  rw [atLeast_apply, atLeast_apply,
    Set.ncard_preimage_of_injective_subset_range Subtype.val_injective (by simpa using hB)]

-- (5-d)
theorem ext_bot : (⊥ : Quantifier.Family.{u}).Ext := fun _ _ _ _ _ ↦ Iff.rfl

-- (5-d)
theorem ext_top : (⊤ : Quantifier.Family.{u}).Ext := fun _ _ _ _ _ ↦ Iff.rfl

-- (5-c)
theorem not_ext_all : ¬ all.{u}.Ext := fun h ↦
  Set.empty_ne_univ <| (all_apply _ _).1 <| (h (∅ : Set PUnit.{u + 1}) ∅ subset_rfl).1 <|
    (all_apply _ _).2 <| Set.eq_univ_of_forall fun x ↦ (Set.notMem_empty _ x.2).elim

/-- Proposition 4: an isomorphism-closed quantifier that is monotone on every finite universe
satisfies extension if and only if it never holds or is *at least `k`* for some `k`. -/
theorem ext_iff_eq_bot_or_atLeast (hI : Q.Isom) (hm : ∀ (α : Type u) [Finite α], Monotone (Q α)) :
    Q.Ext ↔ Q = ⊥ ∨ ∃ k, Q = atLeast k := by
  refine ⟨fun hE ↦ ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hI.ext_iff.1 hE
    have hup : IsUpperSet s := scopeMonotone_cardinal_iff.1 (hs ▸ hI.monotone_iff.1 hm)
    rw [hI.eq_atUniv_toFamily, ← hs]
    rcases hup.eq_empty_or_Ici with rfl | ⟨k, rfl⟩
    exacts [.inl rfl, .inr ⟨k, rfl⟩]
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

/-- Section 4, (5-f): the Rescher quantifier *more than half*, *most* with the universe as its
restrictor. -/
def rescher : Quantifier.Family.{u} := Det.Family.most.atUniv

theorem rescher_apply (α : Type u) [Finite α] (B : Set α) :
    rescher α B ↔ Bᶜ.ncard < B.ncard := by
  simp [rescher, Det.Family.atUniv, Det.Family.most, Det.most_apply, Set.compl_eq_univ_sdiff]

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
  rw [eq_iff_iff, rescher_apply]
  simp only [ofMinSize, test1]
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
