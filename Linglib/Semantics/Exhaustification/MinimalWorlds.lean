module

public import Linglib.Semantics.Exhaustification.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Set.Finite.Powerset

/-!
# Minimal-world exhaustification

A set `ALT` of alternatives orders the worlds: `u ≤ₐ[ALT] v` when every alternative true at `u`
is true at `v`, that is, when `satisfied ALT u ⊆ satisfied ALT v`. Exhaustification `exh ALT φ`
keeps the least worlds of the prejacent `φ` in this order, those verifying only alternatives every
world of `φ` verifies. The minimal-world exhaustifier `exhMW ALT φ` keeps the minimal ones. A
least world is minimal, and where there is one the minimal worlds are the least. Over finitely
many alternatives every world of the prejacent lies above a minimal one, so a satisfiable
prejacent has minimal worlds. A minimal cover is a set of worlds of the prejacent
that represents the minimal worlds up to having the same true alternatives; the exhaustifiers by
innocent exclusion and innocent inclusion are computed from one.

## Main definitions

* `Exhaustification.AltLE`, with notation `u ≤ₐ[ALT] v`: the order of the alternatives.
* `Exhaustification.exhMW`: the prejacent worlds whose set of true alternatives is minimal.
* `Exhaustification.IsMinimalCover`: a set of prejacent worlds representing the minimal ones.

## Main results

* `Exhaustification.mem_exh_iff_forall_le`, `Exhaustification.mem_exhMW_iff_forall_le`:
  exhaustification keeps the least worlds of the prejacent and the minimal-world exhaustifier
  the minimal ones.
* `Exhaustification.exh_subset_exhMW`, `Exhaustification.exhMW_eq_exh_of_nonempty`: a least world
  is minimal, and where there is one the two exhaustifiers agree.
* `Exhaustification.exists_mem_exhMW_le`: over finitely many alternatives, every world of the
  prejacent lies above a minimal world.

## References

* [groenendijk-stokhof-1984]
* [spector-2016]
-/

@[expose] public section

namespace Exhaustification

/-- The order of the alternatives: `u` lies below `v` when every alternative true at `u` is true
at `v`. -/
abbrev AltLE {W : Type*} (ALT : Set (Set W)) (u v : W) : Prop := ∀ a ∈ ALT, u ∈ a → v ∈ a

@[inherit_doc] scoped notation:50 u " ≤ₐ[" ALT "] " v => AltLE ALT u v

variable {W : Type*} (ALT : Set (Set W)) (φ : Set W)

/-- The minimal-world exhaustifier keeps the prejacent worlds whose set of true alternatives is
minimal among the prejacent's worlds. -/
def exhMW : Set W := {u | MinimalFor (· ∈ φ) (satisfied ALT) u}

@[inherit_doc] scoped notation "exhᵐʷ" => exhMW

variable {ALT φ} {u w : W}

theorem mem_exhMW : u ∈ exhᵐʷ ALT φ ↔ MinimalFor (· ∈ φ) (satisfied ALT) u :=
  Iff.rfl

theorem exhMW_subset : exhᵐʷ ALT φ ⊆ φ := fun _ h ↦ h.1

/-- The order of the alternatives is the pullback of inclusion along `satisfied`. -/
theorem satisfied_subset_satisfied {u v : W} : satisfied ALT u ⊆ satisfied ALT v ↔ u ≤ₐ[ALT] v :=
  ⟨fun h _ ha hu ↦ (h ⟨ha, hu⟩).2, fun h a ha ↦ ⟨ha.1, h a ha.1 ha.2⟩⟩

/-- Exhaustification keeps the least worlds of the prejacent: those verifying only alternatives
that every world of the prejacent verifies. -/
theorem mem_exh_iff_forall_le : u ∈ exh ALT φ ↔ u ∈ φ ∧ ∀ v ∈ φ, u ≤ₐ[ALT] v :=
  ⟨fun h ↦ ⟨h.1, fun _ hv q hq huq ↦ h.2 q hq huq hv⟩,
    fun h ↦ ⟨h.1, fun q hq huq _ hv ↦ h.2 _ hv q hq huq⟩⟩

/-- The minimal-world exhaustifier keeps the minimal worlds of the prejacent: those below every
world of the prejacent that lies below them. -/
theorem mem_exhMW_iff_forall_le :
    u ∈ exhᵐʷ ALT φ ↔ u ∈ φ ∧ ∀ v ∈ φ, (v ≤ₐ[ALT] u) → (u ≤ₐ[ALT] v) :=
  ⟨fun ⟨hu, h⟩ ↦ ⟨hu, fun v hv huv ↦ (satisfied_subset_satisfied (u := u) (v := v)).1
      (h hv ((satisfied_subset_satisfied (u := v) (v := u)).2 huv))⟩,
    fun ⟨hu, h⟩ ↦ ⟨hu, fun v hv hvu ↦ (satisfied_subset_satisfied (u := u) (v := v)).2
      (h v hv ((satisfied_subset_satisfied (u := v) (v := u)).1 hvu))⟩⟩

variable (ALT φ) in
/-- A least world of the prejacent is minimal. -/
theorem exh_subset_exhMW : exh ALT φ ⊆ exhᵐʷ ALT φ := fun _ hu ↦
  mem_exhMW_iff_forall_le.2 ⟨hu.1, fun v hv _ ↦ (mem_exh_iff_forall_le.1 hu).2 v hv⟩

variable (ALT φ) in
/-- When the prejacent is consistent with the denial of every alternative it does not entail,
minimal-world exhaustification denies them all too ([spector-2016]). -/
theorem exhMW_eq_exh_of_nonempty (h : (exh ALT φ).Nonempty) : exhᵐʷ ALT φ = exh ALT φ := by
  obtain ⟨w, hw⟩ := h
  refine (exh_subset_exhMW ALT φ).antisymm' fun u hu ↦ ?_
  obtain ⟨huφ, hmax⟩ := mem_exhMW_iff_forall_le.1 hu
  obtain ⟨hwφ, hgreatest⟩ := mem_exh_iff_forall_le.1 hw
  have hwu : u ≤ₐ[ALT] w := hmax w hwφ (hgreatest u huφ)
  exact mem_exh_iff_forall_le.2 ⟨huφ, fun v hv a ha hua ↦ hgreatest v hv a ha (hwu a ha hua)⟩

theorem mem_exhMW_iff_minimal : u ∈ exhᵐʷ ALT φ ↔ u ∈ φ ∧
    Minimal (· ∈ (satisfied ALT) '' φ) (satisfied ALT u) := by
  refine ⟨fun h ↦ ⟨h.1, ⟨u, h.1, rfl⟩, ?_⟩, fun ⟨hu, h⟩ ↦ ⟨hu, fun v hv hvu ↦ h.2 ⟨v, hv, rfl⟩ hvu⟩⟩
  rintro _ ⟨v, hv, rfl⟩ hvu
  exact h.2 hv hvu

/-- Over finitely many alternatives, every world of the prejacent lies above a minimal world,
one verifying only alternatives that it verifies. -/
theorem exists_mem_exhMW_le (hfin : ALT.Finite) (hw : w ∈ φ) : ∃ u ∈ exhᵐʷ ALT φ, u ≤ₐ[ALT] w := by
  obtain ⟨u, ⟨hu, huw⟩, hmin⟩ := Set.Finite.exists_minimalFor' (satisfied ALT)
    {v | v ∈ φ ∧ satisfied ALT v ⊆ satisfied ALT w}
    (hfin.finite_subsets.subset (Set.image_subset_iff.2 fun _ _ _ h ↦ h.1)) ⟨w, hw, le_rfl⟩
  exact ⟨u, ⟨hu, fun v hv hvu ↦ hmin ⟨hv, hvu.trans huw⟩ hvu⟩, fun a ha hua ↦ (huw ⟨ha, hua⟩).2⟩

theorem exhMW_nonempty (hfin : ALT.Finite) (hφ : φ.Nonempty) : (exhᵐʷ ALT φ).Nonempty :=
  let ⟨_, hw⟩ := hφ
  let ⟨u, hu, _⟩ := exists_mem_exhMW_le hfin hw
  ⟨u, hu⟩

theorem exhMW_univ : exhᵐʷ Set.univ φ = φ := by
  refine Set.Subset.antisymm (fun _ h ↦ h.1) fun u hu ↦ ⟨hu, fun v _ hvu ↦ ?_⟩
  obtain rfl : u = v := (hvu (a := {v}) ⟨trivial, rfl⟩).2
  exact le_rfl

/-- Over finitely many worlds and alternatives, membership in the minimal worlds is decidable. -/
instance [Fintype W] {ι : Type*} [Fintype ι] {f : ι → Set W} [∀ i, DecidablePred (· ∈ f i)]
    [DecidablePred (· ∈ φ)] : DecidablePred (· ∈ exhᵐʷ (Set.range f) φ) := fun u ↦
  decidable_of_iff (u ∈ φ ∧ ∀ v, v ∈ φ → (∀ i, v ∈ f i → u ∈ f i) → ∀ i, u ∈ f i → v ∈ f i) <| by
    simp only [mem_exhMW, MinimalFor, Set.subset_def, Set.mem_ofPred_eq, Set.mem_range,
      and_imp, forall_exists_index, forall_apply_eq_imp_iff, exists_apply_eq_apply, true_and]

instance [Fintype W] {ι : Type*} [Fintype ι] {f : ι → Set W} [∀ i, DecidablePred (· ∈ f i)]
    {A : Set ι} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ φ)] :
    DecidablePred (· ∈ exhᵐʷ (f '' A) φ) := fun u ↦
  decidable_of_iff (u ∈ φ ∧ ∀ v, v ∈ φ → (∀ i, i ∈ A → v ∈ f i → u ∈ f i) →
      ∀ i, i ∈ A → u ∈ f i → v ∈ f i) <| by
    simp only [mem_exhMW, MinimalFor, Set.subset_def, Set.mem_ofPred_eq, Set.mem_image,
      and_imp, forall_exists_index, forall_apply_eq_imp_iff₂]
    exact and_congr_right fun _ ↦ forall₂_congr fun v _ ↦
      ⟨fun h hvu i hi hui ↦ ⟨⟨i, hi, rfl⟩, h (fun a ha hva ↦ (hvu a ha hva).2) i hi hui⟩,
        fun h hvu i hi hui ↦ (h (fun a ha hva ↦ ⟨⟨a, ha, rfl⟩, hvu a ha hva⟩) i hi hui).2⟩

/-! ### Representative minimal worlds -/

variable (ALT φ) in
/-- A set of prejacent worlds represents the minimal worlds when every prejacent world lies above
one of its members and no member lies strictly below another. -/
structure IsMinimalCover (M : Set W) : Prop where
  /-- The members are worlds of the prejacent. -/
  mem : ∀ v ∈ M, v ∈ φ
  /-- Every world of the prejacent lies above a member. -/
  le : ∀ w ∈ φ, ∃ v ∈ M, v ≤ₐ[ALT] w
  /-- A member above another is below it. -/
  antisymm : ∀ v ∈ M, ∀ u ∈ M, (u ≤ₐ[ALT] v) → (v ≤ₐ[ALT] u)

variable {M : Set W}

theorem IsMinimalCover.exhMW_eq (hM : IsMinimalCover ALT φ M) :
    exhᵐʷ ALT φ = {u | u ∈ φ ∧ ∃ v ∈ M, satisfied ALT v =
      satisfied ALT u} := by
  ext u
  refine ⟨fun ⟨hu, hmin⟩ ↦ ⟨hu, ?_⟩, fun ⟨hu, v, hv, hvu⟩ ↦ ⟨hu, fun x hx hxu ↦ ?_⟩⟩
  · obtain ⟨v, hv, hvu⟩ := hM.le u hu
    have hvu := (satisfied_subset_satisfied (u := v) (v := u)).2 hvu
    exact ⟨v, hv, hvu.antisymm (hmin (hM.mem v hv) hvu)⟩
  · obtain ⟨v', hv', hv'x⟩ := hM.le x hx
    have hv'x := (satisfied_subset_satisfied (u := v') (v := x)).2 hv'x
    exact hvu.ge.trans (((satisfied_subset_satisfied (u := v) (v := v')).2 (hM.antisymm v hv v' hv'
      ((satisfied_subset_satisfied (u := v') (v := v)).1 (hv'x.trans (hxu.trans hvu.ge))))).trans
        hv'x)

end Exhaustification
