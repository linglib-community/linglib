/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar.Regular
public import Linglib.Core.Computability.InductiveInference
public import Mathlib.Computability.MyhillNerode

/-!
# Gold (1967): Language identification in the limit

A learner receives information about an unknown language at each moment and guesses the language;
it succeeds if its guesses are eventually constant and correct. From a text, which presents only
members of the language, [the finite languages can be identified](##identifiable_finite) but
[no proper superclass of them can](##not_identifiable_of_finite_ssubset), so that not even
[the regular languages](##not_identifiable_isRegular) are identifiable, and so not the context-free
languages. From an informant, which also says which strings are not members,
[any countable class can be identified](##exists_identifiesFromInformant_of_countable), by guessing
the first language in an enumeration that agrees with the information so far. Since children
appear to learn from positive instances alone, Gold concludes that if a text is all they have, the
possible natural languages, if they include an infinite one, cannot include all the finite ones.

## Implementation notes

Identifiability here is what Gold calls ineffective: a guessing rule is any function, so the choice
of naming relation does not arise and only arbitrary text and arbitrary informant are considered.
Table I's positive results for effective guessing rules are not formalized, nor is its anomalous
row, which turns on primitive recursive text.

## References

* [gold-1967]
-/

@[expose] public section

namespace Gold1967

open InductiveInference Set Filter

variable {α : Type*}

/-! ### Text -/

/-- Theorem I.6: from an arbitrary text the finite languages are identifiable, by guessing that the
language consists of the strings that have occurred so far. -/
theorem identifiable_finite : Identifiable {L : Set α | L.Finite} := by
  refine ⟨content, fun L hL t ht ↦ ?_⟩
  filter_upwards [Text.eventually_subset_content_take hL ht.symm.subset] with n hn
  exact Subset.antisymm (ht ▸ t.content_take_subset n) hn

/-- Theorems I.8 and I.9 as stated for ineffective identification in §8: every proper superclass of
the finite languages is not identifiable from text, so the class of possible natural languages, if
it contains languages of infinite cardinality, cannot contain all languages of finite cardinality
when a text is all the child receives (§4). -/
theorem not_identifiable_of_finite_ssubset [Countable α] {𝓛 : Set (Set α)}
    (h : {L : Set α | L.Finite} ⊂ 𝓛) : ¬Identifiable 𝓛 := by
  obtain ⟨L, hL, hinf⟩ := exists_of_ssubset h
  exact not_identifiable_of_finite_subsets hL hinf fun T _ hT ↦ h.subset hT

/-! ### The classes of Table I -/

section Classes

variable {σ : Type*}

/-- Every finite language is regular: its left quotients are subsets of the finitely many suffixes
of its members. -/
theorem isRegular_of_finite {L : Set (List σ)} (hL : L.Finite) : Language.IsRegular L := by
  have hS : (⋃ u ∈ L, {v | v ∈ u.tails}).Finite := hL.biUnion fun u _ ↦ List.finite_toSet _
  refine Language.isRegular_iff_finite_range_leftQuotient.mpr (hS.finite_subsets.subset ?_)
  rintro _ ⟨w, rfl⟩ v hv
  exact mem_biUnion (show w ++ v ∈ L from hv) (by simp)

theorem isRegular_univ : Language.IsRegular (univ : Set (List σ)) := by
  refine Language.isRegular_iff_finite_range_leftQuotient.mpr ((finite_singleton univ).subset ?_)
  rintro _ ⟨w, rfl⟩
  exact eq_univ_of_forall fun v ↦ mem_univ (w ++ v)

/-- The dividing line of Table I for text lies below the regular languages. -/
theorem not_identifiable_isRegular [Countable σ] [Nonempty σ] :
    ¬Identifiable {L : Set (List σ) | Language.IsRegular L} :=
  not_identifiable_of_finite_subsets (L := univ) isRegular_univ infinite_univ
    fun _ _ hT ↦ isRegular_of_finite hT

theorem not_identifiable_isContextFree [Finite σ] [Nonempty σ] :
    ¬Identifiable {L : Set (List σ) | Language.IsContextFree L} := fun h ↦
  not_identifiable_isRegular (h.mono fun _ hL ↦ Language.IsRegular.isContextFree hL)

end Classes

/-! ### Informant -/

/-- An **informant** for `L` says of every string whether it belongs to `L`: `Sum.inl x` presents
`x` as a member and `Sum.inr x` as a nonmember. -/
def IsInformant (i : Stream' (α ⊕ α)) (L : Set α) : Prop :=
  L = {x | Sum.inl x ∈ i} ∧ Lᶜ = {x | Sum.inr x ∈ i}

/-- A guessing rule **identifies** `L` **from an informant** when on every informant for `L` its
guesses are eventually `L`. -/
def IdentifiesFromInformant (φ : List (α ⊕ α) → Set α) (L : Set α) : Prop :=
  ∀ i, IsInformant i L → ∀ᶠ n in atTop, φ (i.take n) = L

/-- A language agrees with finite information when it contains the strings presented as members
and excludes those presented as nonmembers. -/
private def Agrees (l : List (α ⊕ α)) (A : Set α) : Prop :=
  (∀ x, Sum.inl x ∈ l → x ∈ A) ∧ ∀ x, Sum.inr x ∈ l → x ∉ A

private theorem mem_take_of_mem {β : Type*} {s : Stream' β} {b : β} {n k : ℕ}
    (hb : b = s.get k) (hn : k < n) : b ∈ s.take n :=
  List.mem_of_getElem? (hb ▸ Stream'.getElem?_take hn)

private theorem mem_of_mem_take {β : Type*} {s : Stream' β} {b : β} {n : ℕ}
    (hb : b ∈ s.take n) : b ∈ s := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
  have hn : k < n := by simpa using hk
  have := Stream'.getElem?_take (s := s) hn
  rw [List.getElem?_eq_getElem hk] at this
  exact ⟨k, Option.some_inj.mp this⟩

/-- §8: from an informant every countable class is identifiable, by identification by enumeration:
guess the first language of an enumeration that agrees with the information. Whereas a language
properly containing the unknown one is never contradicted by a text, an informant eventually
contradicts every other language. -/
theorem exists_identifiesFromInformant_of_countable {𝓛 : Set (Set α)} (hc : 𝓛.Countable) :
    ∃ φ, ∀ L ∈ 𝓛, IdentifiesFromInformant φ L := by
  classical
  rcases 𝓛.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ ↦ ∅, by simp⟩
  obtain ⟨A, rfl⟩ := hc.exists_eq_range hne
  refine ⟨fun l ↦ if h : ∃ k, Agrees l (A k) then A (Nat.find h) else ∅, ?_⟩
  rintro _ ⟨z', rfl⟩ i ⟨hpos, hneg⟩
  have hz : ∃ z, A z = A z' := ⟨z', rfl⟩
  have hAz : A (Nat.find hz) = A z' := Nat.find_spec hz
  have hagree : ∀ n, Agrees (i.take n) (A (Nat.find hz)) := fun n ↦ by
    rw [hAz]
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · rw [hpos]; exact mem_of_mem_take hx
    · have : x ∈ (A z')ᶜ := by rw [hneg]; exact mem_of_mem_take hx
      exact this
  have hrej : ∀ᶠ n in atTop, ∀ k ∈ Finset.range (Nat.find hz), ¬Agrees (i.take n) (A k) := by
    refine (Finset.eventually_all _).mpr fun k hk ↦ ?_
    have hne : A k ≠ A z' := Nat.find_min hz (Finset.mem_range.mp hk)
    obtain ⟨x, hx⟩ : ∃ x, ¬(x ∈ A k ↔ x ∈ A z') := by
      by_contra hall
      exact hne (Set.ext fun x ↦ by_contra fun h ↦ hall ⟨x, h⟩)
    by_cases hxz : x ∈ A z'
    · obtain ⟨m, hm⟩ : Sum.inl x ∈ i := by rw [hpos] at hxz; exact hxz
      filter_upwards [eventually_gt_atTop m] with n hn hagr
      exact hx ⟨fun _ ↦ hxz, fun _ ↦ hagr.1 x (mem_take_of_mem hm hn)⟩
    · obtain ⟨m, hm⟩ : Sum.inr x ∈ i := by
        have : x ∈ (A z')ᶜ := hxz
        rw [hneg] at this; exact this
      filter_upwards [eventually_gt_atTop m] with n hn hagr
      exact hx ⟨fun hk' ↦ absurd hk' (hagr.2 x (mem_take_of_mem hm hn)), fun h ↦ absurd h hxz⟩
  filter_upwards [hrej] with n hn
  have hex : ∃ k, Agrees (i.take n) (A k) := ⟨_, hagree n⟩
  have hfind : Nat.find hex = Nat.find hz :=
    (Nat.find_eq_iff hex).mpr ⟨hagree n, fun k hk ↦ hn k (Finset.mem_range.mpr hk)⟩
  simp only [hex, ↓reduceDIte, hfind, hAz]

end Gold1967
