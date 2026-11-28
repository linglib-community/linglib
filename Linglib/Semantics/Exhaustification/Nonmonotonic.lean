module

public import Linglib.Logic.Nonmonotonic.Preferential
public import Linglib.Core.Order.OfLowerSets.Defs
public import Linglib.Semantics.Exhaustification.MinimalWorlds
public import Mathlib.Order.SymmDiff

/-!
# Exhaustification as nonmonotonic consequence

Exhaustification and premise semantics describe the same structure. The order of the alternatives,
`u ≤ₐ[ALT] v`, is the ordering `≤[ALT]` that the alternatives induce as a family of sets, read in
the other direction, and the ordering that their negations induce as premises. The minimal-world
exhaustifier therefore keeps the best worlds of the prejacent, with the prejacent as modal base
and the negated alternatives as ordering source. Read as a relation between a prejacent and what
its exhaustification entails, `exhMW ALT φ ⊆ ψ`, minimal-world exhaustification is a preferential
consequence relation exactly when the order of the alternatives is well-founded, as it is over
finitely many alternatives.

A property `P : W → Set E` of individuals that varies with the world gives two families of
propositions for a set `s` of individuals: that an individual of `s` lacks the property, and that
it has it. As premises, the first family ranks a world lower when fewer individuals of `s` have
the property, and the second when more do.

## Main results

* `Exhaustification.exhMW_eq_minimals`: the minimal worlds are the best worlds of the prejacent
  under the premise set of the negated alternatives.
* `Exhaustification.atBotOn_satisfied_iff`: what holds toward the bottom of the prejacent is what
  holds at its minimal worlds exactly when every world of the prejacent lies above a minimal one.
* `Exhaustification.isPreferential_exhMW_iff`: minimal-world exhaustification is a preferential
  consequence relation exactly when the order of the alternatives is well-founded.
* `Exhaustification.isPreferential_exhMW`: over finitely many alternatives it is.
* `Exhaustification.ofLowerSets_image_union_le_iff`: under the premises that some individuals lack
  a property and others have it, a world is at least as good as another when fewer of the first
  and more of the second have the property in it.

## References

* [kratzer-1981]
* [spector-2016]
* [kraus-lehmann-magidor-1990]
-/

@[expose] public section

open scoped PremiseOrdering

namespace Exhaustification

variable {W : Type*} {ALT : Set (Set W)} {φ : Set W} {u v w : W}

/-! ### The two orderings -/

/-- The order of the alternatives is the ordering they induce as a family of sets, reversed. -/
theorem le_iff_ofLowerSets_le : (u ≤ₐ[ALT] v) ↔ (v ≤[ALT] u) := Iff.rfl

variable (ALT φ) in
/-- Minimal worlds are Kratzer's best worlds of the prejacent, with the negated alternatives as
the premises. -/
theorem exhMW_eq_minimals : exhᵐʷ ALT φ = (≤[compl '' ALT]).minimals φ := by
  have key (u v : W) : (≤[compl '' ALT]).le u v ↔ satisfied ALT u ⊆ satisfied ALT v :=
    (Preorder.ofLowerSets_image_compl_le_iff ALT u v).trans satisfied_subset_satisfied.symm
  ext u
  simp only [mem_exhMW, MinimalFor, Preorder.mem_minimals_iff, key]

/-! ### Exhaustification as a consequence relation -/

/-- What holds toward the bottom of the prejacent, ranked by the alternatives true at a world, is
what holds at its minimal worlds exactly when every world of the prejacent lies above a minimal
one. -/
theorem atBotOn_satisfied_iff :
    Filter.atBotOn (satisfied ALT) φ = Filter.principal (exhᵐʷ ALT φ) ↔
      ∀ u ∈ φ, ∃ v ∈ exhᵐʷ ALT φ, v ≤ₐ[ALT] u :=
  Filter.atBotOn_eq_principal_iff.trans <| forall₂_congr fun _ _ ↦ exists_congr fun _ ↦
    and_congr_right fun _ ↦ satisfied_subset_satisfied

/-- Over finitely many alternatives, what holds toward the bottom of the prejacent is what holds
at its minimal worlds. -/
theorem atBotOn_satisfied (hfin : ALT.Finite) (φ : Set W) :
    Filter.atBotOn (satisfied ALT) φ = Filter.principal (exhᵐʷ ALT φ) :=
  atBotOn_satisfied_iff.2 fun _ hu ↦ exists_mem_exhMW_le hfin hu

variable (ALT) in
/-- Minimal-world exhaustification, read as the relation between a prejacent and what its
exhaustification entails, is a preferential consequence relation exactly when the order of the
alternatives is well-founded. -/
theorem isPreferential_exhMW_iff :
    (Nonmonotonic.IsPreferential fun φ ψ ↦ exhᵐʷ ALT φ ⊆ ψ) ↔
      WellFounded (≤[compl '' ALT]).lt := by
  rw [show (fun φ ψ ↦ exhᵐʷ ALT φ ⊆ ψ) = fun φ ψ ↦ (≤[compl '' ALT]).minimals φ ⊆ ψ from
    funext₂ fun φ ψ ↦ by rw [exhMW_eq_minimals]]
  exact Nonmonotonic.isPreferential_minimals_iff

/-- Minimal-world exhaustification over finitely many alternatives, read as the relation between
a prejacent and what its exhaustification entails, is a preferential consequence relation. -/
theorem isPreferential_exhMW (hfin : ALT.Finite) :
    Nonmonotonic.IsPreferential fun φ ψ ↦ exhᵐʷ ALT φ ⊆ ψ := by
  have h := Nonmonotonic.isPreferential_atBotOn (satisfied ALT)
  simp only [atBotOn_satisfied hfin, Filter.mem_principal] at h
  exact h

/-! ### The orderings of a property

A property `P : W → Set E` of individuals that varies with the world gives two families of
propositions for a set `s` of individuals: that an individual of `s` lacks the property, and that
it has it. As premises, the first family ranks a world lower when fewer individuals of `s` have
the property, and the second when more do. The two families together rank worlds by both at
once. -/

section Property

variable {E : Type*} (P : W → Set E) (s pos neg : Set E) (v w : W)

theorem ofLowerSets_image_notMem_le_iff :
    (v ≤[(fun x ↦ {u | x ∉ P u}) '' s] w) ↔ P v ∩ s ⊆ P w ∩ s := by
  rw [Preorder.ofLowerSets_image_le_iff]
  exact ⟨fun h x hx ↦ ⟨by_contra fun hw ↦ h x hx.2 hw hx.1, hx.2⟩,
    fun h x hx hw hv ↦ hw (h ⟨hv, hx⟩).1⟩

theorem ofLowerSets_image_mem_le_iff :
    (v ≤[(fun x ↦ {u | x ∈ P u}) '' s] w) ↔ P w ∩ s ⊆ P v ∩ s := by
  rw [Preorder.ofLowerSets_image_le_iff]
  exact ⟨fun h x hx ↦ ⟨h x hx.2 hx.1, hx.2⟩, fun h x hx hw ↦ (h ⟨hw, hx⟩).1⟩

/-- Under the premises that the individuals of `pos` lack the property and those of `neg` have it,
a world is at least as good as another when fewer individuals of `pos` and more of `neg` have the
property in it. -/
theorem ofLowerSets_image_union_le_iff :
    (v ≤[(fun x ↦ {u | x ∉ P u}) '' pos ∪ (fun x ↦ {u | x ∈ P u}) '' neg] w) ↔
      P v ∩ pos ⊆ P w ∩ pos ∧ P w ∩ neg ⊆ P v ∩ neg := by
  rw [← ofLowerSets_image_notMem_le_iff, ← ofLowerSets_image_mem_le_iff]
  simp only [Preorder.ofLowerSets_le_iff, Set.mem_union]
  exact ⟨fun h ↦ ⟨fun s hs ↦ h s (.inl hs), fun s hs ↦ h s (.inr hs)⟩,
    fun h s hs ↦ hs.elim (h.1 s) (h.2 s)⟩

open Set symmDiff in
/-- The premises that the individuals of `pos` lack a property and those of `neg` have it are
unchanged when the property is flipped within `N` and `pos` and `neg` are exchanged on `N`. -/
theorem image_notMem_union_image_mem_symmDiff (N : Set E) :
    (fun x ↦ {u | x ∉ N ∆ P u}) '' (pos \ N ∪ neg ∩ N) ∪
        (fun x ↦ {u | x ∈ N ∆ P u}) '' (neg \ N ∪ pos ∩ N) =
      (fun x ↦ {u | x ∉ P u}) '' pos ∪ (fun x ↦ {u | x ∈ P u}) '' neg := by
  have hin {x : E} (hx : x ∈ N) (u : W) : x ∈ N ∆ P u ↔ x ∉ P u := by
    simp only [mem_symmDiff]; tauto
  have hout {x : E} (hx : x ∉ N) (u : W) : x ∈ N ∆ P u ↔ x ∈ P u := by
    simp only [mem_symmDiff]; tauto
  ext s
  simp only [mem_union, mem_image, mem_sdiff, mem_inter_iff]
  constructor
  · rintro (⟨x, ⟨hp, hx⟩ | ⟨hn, hx⟩, rfl⟩ | ⟨x, ⟨hn, hx⟩ | ⟨hp, hx⟩, rfl⟩)
    · exact .inl ⟨x, hp, by simp only [hout hx]⟩
    · exact .inr ⟨x, hn, by simp only [hin hx, not_not]⟩
    · exact .inr ⟨x, hn, by simp only [hout hx]⟩
    · exact .inl ⟨x, hp, by simp only [hin hx]⟩
  · rintro (⟨x, hp, rfl⟩ | ⟨x, hn, rfl⟩)
    · by_cases hx : x ∈ N
      · exact .inr ⟨x, .inr ⟨hp, hx⟩, by simp only [hin hx]⟩
      · exact .inl ⟨x, .inl ⟨hp, hx⟩, by simp only [hout hx]⟩
    · by_cases hx : x ∈ N
      · exact .inl ⟨x, .inr ⟨hn, hx⟩, by simp only [hin hx, not_not]⟩
      · exact .inr ⟨x, .inl ⟨hn, hx⟩, by simp only [hout hx]⟩

end Property

end Exhaustification
