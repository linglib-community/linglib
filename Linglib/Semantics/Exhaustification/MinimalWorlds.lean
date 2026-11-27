module

public import Linglib.Semantics.Exhaustification.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Set.Finite.Powerset
public import Linglib.Core.Order.Minimals
public import Linglib.Logic.Nonmonotonic.PremiseOrdering.Defs
public import Mathlib.Order.SymmDiff

/-!
# Minimal-world exhaustification

A set `ALT` of alternatives orders the worlds: `w ≤[ALT] u` when `w` verifies every alternative
that `u` verifies. Exhaustification `exh ALT φ` keeps the greatest worlds of the prejacent `φ` in
this order, those verifying only alternatives every world of `φ` verifies. The minimal-world
exhaustifier `exhMW ALT φ` keeps the maximal ones, those whose set of true alternatives
`{a ∈ ALT | w ∈ a}` is minimal among the worlds of the prejacent. A greatest world is maximal, and
where there is one the maximal worlds are the greatest. In the order of the negated alternatives,
`≤[compl '' ALT]`, these are the least and the minimal worlds: Kratzer's best worlds, with the
prejacent as modal base and the negated alternatives as ordering source. Over finitely many
alternatives every world of the prejacent lies below a maximal one, so a satisfiable prejacent has
minimal worlds. A minimal cover is a set of worlds of the prejacent that represents the minimal
worlds up to having the same true alternatives; the exhaustifiers by innocent exclusion and
innocent inclusion are computed from one.

## Main definitions

* `Exhaustification.exhMW`: the prejacent worlds whose set of true alternatives is minimal.
* `Exhaustification.IsMinimalCover`: a set of prejacent worlds representing the minimal ones.

## Main results

* `Exhaustification.mem_exh_iff_forall_le`, `Exhaustification.mem_exhMW_iff_forall_le`:
  exhaustification keeps the greatest worlds of the prejacent and the minimal-world exhaustifier
  the maximal ones.
* `Exhaustification.exh_subset_exhMW`, `Exhaustification.exhMW_eq_exh_of_nonempty`: a greatest
  world is maximal, and where there is one the two exhaustifiers agree.
* `Exhaustification.exhMW_eq_minimals`: the minimal worlds are the best worlds of the prejacent
  under the premise set of the negated alternatives.
* `Exhaustification.exists_mem_exhMW_le`: over finitely many alternatives, every world of the
  prejacent lies below a minimal world.
* `Exhaustification.ofLowerSets_image_union_le_iff`: under the premises that some individuals lack a
  property and others have it, a world is at least as good as another when fewer of the first and
  more of the second have the property in it.
* `Exhaustification.image_notMem_union_image_mem_symmDiff`: those premises are unchanged when the
  property is flipped within a set `N` and the two sets of individuals are exchanged on `N`.

## References

* [groenendijk-stokhof-1984]
* [spector-2016]
* [kratzer-1981]
-/

@[expose] public section

open scoped PremiseOrdering

namespace Exhaustification

variable {W : Type*} (ALT : Set (Set W)) (φ : Set W)

/-- The minimal-world exhaustifier keeps the prejacent worlds whose set of true alternatives is
minimal among the prejacent's worlds. -/
def exhMW : Set W := {u | MinimalFor (· ∈ φ) (fun w ↦ {a ∈ ALT | w ∈ a}) u}

variable {ALT φ} {u w : W}

theorem mem_exhMW : u ∈ exhMW ALT φ ↔ MinimalFor (· ∈ φ) (fun w ↦ {a ∈ ALT | w ∈ a}) u :=
  Iff.rfl

theorem exhMW_subset : exhMW ALT φ ⊆ φ := fun _ h ↦ h.1

/-- Exhaustification keeps the greatest worlds of the prejacent: those verifying only alternatives
that every world of the prejacent verifies. -/
theorem mem_exh_iff_forall_le : u ∈ exh ALT φ ↔ u ∈ φ ∧ ∀ v ∈ φ, v ≤[ALT] u :=
  ⟨fun h ↦ ⟨h.1, fun _ hv q hq huq ↦ h.2 q hq huq hv⟩,
    fun h ↦ ⟨h.1, fun q hq huq _ hv ↦ h.2 _ hv q hq huq⟩⟩

/-- The minimal-world exhaustifier keeps the maximal worlds of the prejacent: those above every
world of the prejacent that they lie below. -/
theorem mem_exhMW_iff_forall_le :
    u ∈ exhMW ALT φ ↔ u ∈ φ ∧ ∀ v ∈ φ, (u ≤[ALT] v) → (v ≤[ALT] u) :=
  ⟨fun ⟨hu, h⟩ ↦ ⟨hu, fun v hv huv ↦ (Preorder.ofLowerSets_le_iff_subset ALT v u).2
      (h hv ((Preorder.ofLowerSets_le_iff_subset ALT u v).1 huv))⟩,
    fun ⟨hu, h⟩ ↦ ⟨hu, fun v hv hvu ↦ (Preorder.ofLowerSets_le_iff_subset ALT v u).1
      (h v hv ((Preorder.ofLowerSets_le_iff_subset ALT u v).2 hvu))⟩⟩

variable (ALT φ) in
/-- A greatest world of the prejacent is maximal. -/
theorem exh_subset_exhMW : exh ALT φ ⊆ exhMW ALT φ := fun _ hu ↦
  mem_exhMW_iff_forall_le.2 ⟨hu.1, fun v hv _ ↦ (mem_exh_iff_forall_le.1 hu).2 v hv⟩

variable (ALT φ) in
/-- When the prejacent is consistent with the denial of every alternative it does not entail,
minimal-world exhaustification denies them all too ([spector-2016]). -/
theorem exhMW_eq_exh_of_nonempty (h : (exh ALT φ).Nonempty) : exhMW ALT φ = exh ALT φ := by
  obtain ⟨w, hw⟩ := h
  refine (exh_subset_exhMW ALT φ).antisymm' fun u hu ↦ ?_
  obtain ⟨huφ, hmax⟩ := mem_exhMW_iff_forall_le.1 hu
  obtain ⟨hwφ, hgreatest⟩ := mem_exh_iff_forall_le.1 hw
  have hwu : w ≤[ALT] u := hmax w hwφ (hgreatest u huφ)
  exact mem_exh_iff_forall_le.2 ⟨huφ, fun v hv a ha hua ↦ hgreatest v hv a ha (hwu a ha hua)⟩

theorem mem_exhMW_iff_minimal : u ∈ exhMW ALT φ ↔ u ∈ φ ∧
    Minimal (· ∈ (fun w ↦ {a ∈ ALT | w ∈ a}) '' φ) ({a ∈ ALT | u ∈ a}) := by
  refine ⟨fun h ↦ ⟨h.1, ⟨u, h.1, rfl⟩, ?_⟩, fun ⟨hu, h⟩ ↦ ⟨hu, fun v hv hvu ↦ h.2 ⟨v, hv, rfl⟩ hvu⟩⟩
  rintro _ ⟨v, hv, rfl⟩ hvu
  exact h.2 hv hvu

variable (ALT φ) in
/-- Minimal worlds are Kratzer's best worlds of the prejacent, with the negated alternatives as
the premises. -/
theorem exhMW_eq_minimals :
    exhMW ALT φ = (≤[compl '' ALT]).minimals φ := by
  have key (u v : W) : (≤[compl '' ALT]).le u v ↔
      {a ∈ ALT | u ∈ a} ⊆ {a ∈ ALT | v ∈ a} :=
    (Preorder.ofLowerSets_image_compl_le_iff ALT u v).trans
      (Preorder.ofLowerSets_le_iff_subset ALT v u)
  ext u
  simp only [mem_exhMW, MinimalFor, Preorder.mem_minimals_iff, key]

/-- Over finitely many alternatives, every world of the prejacent lies below a minimal world,
one verifying only alternatives that it verifies. -/
theorem exists_mem_exhMW_le (hfin : ALT.Finite) (hw : w ∈ φ) : ∃ u ∈ exhMW ALT φ, w ≤[ALT] u := by
  obtain ⟨u, ⟨hu, huw⟩, hmin⟩ := Set.Finite.exists_minimalFor' (fun w ↦ {a ∈ ALT | w ∈ a})
    {v | v ∈ φ ∧ {a ∈ ALT | v ∈ a} ⊆ {a ∈ ALT | w ∈ a}}
    (hfin.finite_subsets.subset (Set.image_subset_iff.2 fun _ _ _ h ↦ h.1)) ⟨w, hw, le_rfl⟩
  exact ⟨u, ⟨hu, fun v hv hvu ↦ hmin ⟨hv, hvu.trans huw⟩ hvu⟩, fun a ha hua ↦ (huw ⟨ha, hua⟩).2⟩

theorem exhMW_nonempty (hfin : ALT.Finite) (hφ : φ.Nonempty) : (exhMW ALT φ).Nonempty :=
  let ⟨_, hw⟩ := hφ
  let ⟨u, hu, _⟩ := exists_mem_exhMW_le hfin hw
  ⟨u, hu⟩

theorem exhMW_univ : exhMW Set.univ φ = φ := by
  refine Set.Subset.antisymm (fun _ h ↦ h.1) fun u hu ↦ ⟨hu, fun v _ hvu ↦ ?_⟩
  obtain rfl : u = v := (hvu (a := {v}) ⟨trivial, rfl⟩).2
  exact le_rfl

/-- Over finitely many worlds and alternatives, membership in the minimal worlds is decidable. -/
instance [Fintype W] {ι : Type*} [Fintype ι] {f : ι → Set W} [∀ i, DecidablePred (· ∈ f i)]
    [DecidablePred (· ∈ φ)] : DecidablePred (· ∈ exhMW (Set.range f) φ) := fun u ↦
  decidable_of_iff (u ∈ φ ∧ ∀ v, v ∈ φ → (∀ i, v ∈ f i → u ∈ f i) → ∀ i, u ∈ f i → v ∈ f i) <| by
    simp only [mem_exhMW, MinimalFor, Set.subset_def, Set.mem_ofPred_eq, Set.mem_range,
      and_imp, forall_exists_index, forall_apply_eq_imp_iff, exists_apply_eq_apply, true_and]

instance [Fintype W] {ι : Type*} [Fintype ι] {f : ι → Set W} [∀ i, DecidablePred (· ∈ f i)]
    {A : Set ι} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ φ)] :
    DecidablePred (· ∈ exhMW (f '' A) φ) := fun u ↦
  decidable_of_iff (u ∈ φ ∧ ∀ v, v ∈ φ → (∀ i, i ∈ A → v ∈ f i → u ∈ f i) →
      ∀ i, i ∈ A → u ∈ f i → v ∈ f i) <| by
    simp only [mem_exhMW, MinimalFor, Set.subset_def, Set.mem_ofPred_eq, Set.mem_image,
      and_imp, forall_exists_index, forall_apply_eq_imp_iff₂]
    exact and_congr_right fun _ ↦ forall₂_congr fun v _ ↦
      ⟨fun h hvu i hi hui ↦ ⟨⟨i, hi, rfl⟩, h (fun a ha hva ↦ (hvu a ha hva).2) i hi hui⟩,
        fun h hvu i hi hui ↦ (h (fun a ha hva ↦ ⟨⟨a, ha, rfl⟩, hvu a ha hva⟩) i hi hui).2⟩

/-! ### Representative minimal worlds -/

variable (ALT φ) in
/-- A set of prejacent worlds represents the minimal worlds when every prejacent world lies below
one of its members and no member lies strictly below another. -/
structure IsMinimalCover (M : Set W) : Prop where
  /-- The members are worlds of the prejacent. -/
  mem : ∀ v ∈ M, v ∈ φ
  /-- Every world of the prejacent lies below a member. -/
  le : ∀ w ∈ φ, ∃ v ∈ M, w ≤[ALT] v
  /-- A member below another is above it. -/
  antisymm : ∀ v ∈ M, ∀ u ∈ M, (v ≤[ALT] u) → (u ≤[ALT] v)

variable {M : Set W}

theorem IsMinimalCover.exhMW_eq (hM : IsMinimalCover ALT φ M) :
    exhMW ALT φ = {u | u ∈ φ ∧ ∃ v ∈ M, {a ∈ ALT | v ∈ a} =
      {a ∈ ALT | u ∈ a}} := by
  ext u
  refine ⟨fun ⟨hu, hmin⟩ ↦ ⟨hu, ?_⟩, fun ⟨hu, v, hv, hvu⟩ ↦ ⟨hu, fun x hx hxu ↦ ?_⟩⟩
  · obtain ⟨v, hv, hvu⟩ := hM.le u hu
    have hvu := (Preorder.ofLowerSets_le_iff_subset ALT u v).1 hvu
    exact ⟨v, hv, hvu.antisymm (hmin (hM.mem v hv) hvu)⟩
  · obtain ⟨v', hv', hv'x⟩ := hM.le x hx
    have hv'x := (Preorder.ofLowerSets_le_iff_subset ALT x v').1 hv'x
    exact hvu.ge.trans (((Preorder.ofLowerSets_le_iff_subset ALT v' v).1 (hM.antisymm v hv v' hv'
      ((Preorder.ofLowerSets_le_iff_subset ALT v v').2 (hv'x.trans (hxu.trans hvu.ge))))).trans
        hv'x)

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
