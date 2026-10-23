module

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Order.Antichain
public import Mathlib.Order.Preorder.Finite

/-!
# Natural selections from families of sets

A selection rule picks a set of labels from any family of sets of labels. It is natural when it
commutes with every relabeling whose preimage carries one antichain bijectively onto another, and
consistent when on a finite nonempty antichain it picks within some member. Taking the
intersection is natural and consistent, and every natural consistent rule picks within it, while
choosing one member is consistent but not natural. So on a finite antichain the intersection is
the greatest set a natural consistent rule selects; in particular the elements in every maximal
set meeting a condition are the greatest such selection from those maximal sets.

## Main definitions

* `Set.IsNaturalSelection`, `Set.IsConsistentSelection`

## Main statements

* `Set.isGreatest_sInter`: on a finite antichain, the intersection is the greatest set a natural
  consistent rule selects.
* `Set.not_isNaturalSelection_choose`: choosing a member is not natural.

## Implementation notes

The rule is a family `F : ∀ A : Type u, Set (Set A) → Set A` over all label types, so that
naturality can compare a family with its copies in larger types. The upper bound comes from a
cyclic cover: the family `N 0, …, N n` sits inside copies `A × Fin (n + 1)` whose shift permutes
the members cyclically, so a natural rule that picks a label outside some member picks every copy
of it, and no member of the cover then contains its pick.
-/

@[expose] public section

namespace Set

universe u

/-- A selection rule is natural when it commutes with every relabeling whose preimage carries one
antichain bijectively onto another. -/
def IsNaturalSelection (F : ∀ A : Type u, Set (Set A) → Set A) : Prop :=
  ∀ ⦃A A' : Type u⦄ (f : A → A') ⦃𝓚 : Set (Set A)⦄ ⦃𝓚' : Set (Set A')⦄,
    IsAntichain (· ⊆ ·) 𝓚' → BijOn (preimage f) 𝓚' 𝓚 → F A 𝓚 = f ⁻¹' F A' 𝓚'

/-- A selection rule is consistent when on every finite nonempty antichain it selects within some
member. -/
def IsConsistentSelection (F : ∀ A : Type u, Set (Set A) → Set A) : Prop :=
  ∀ ⦃A : Type u⦄ ⦃𝓚 : Set (Set A)⦄, IsAntichain (· ⊆ ·) 𝓚 → 𝓚.Finite → 𝓚.Nonempty →
    ∃ K ∈ 𝓚, F A 𝓚 ⊆ K

/-! ### The cyclic cover -/

private theorem bijOn_preimage_range {α β ι : Type*} {g : α → β} {T : ι → Set β}
    {M : ι → Set α} (σ : ι ≃ ι) (hM : Function.Injective M) (h : ∀ i, g ⁻¹' T i = M (σ i)) :
    BijOn (preimage g) (range T) (range M) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨σ i, (h i).symm⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩ hii'
    rw [h, h] at hii'
    rw [σ.injective (hM hii')]
  · rintro _ ⟨j, rfl⟩
    exact ⟨_, ⟨σ.symm j, rfl⟩, by rw [h, σ.apply_symm_apply]⟩

section Cover

variable {A : Type u} {n : ℕ} {N : Fin (n + 1) → Set A}

/-- In copy `j`, the `i`-th member of the cover is the `(i + j)`-th member of `N`. -/
private def cyclicCover (N : Fin (n + 1) → Set A) (i : Fin (n + 1)) : Set (A × Fin (n + 1)) :=
  {p | p.1 ∈ N (i + p.2)}

private theorem preimage_copy_zero (i : Fin (n + 1)) :
    (fun x : A ↦ (x, (0 : Fin (n + 1)))) ⁻¹' cyclicCover N i = N i := by
  ext; simp [cyclicCover]

private theorem preimage_shift (i : Fin (n + 1)) :
    (fun p : A × Fin (n + 1) ↦ (p.1, p.2 + 1)) ⁻¹' cyclicCover N i = cyclicCover N (i + 1) := by
  ext; simp [cyclicCover, add_comm (1 : Fin (n + 1)), add_assoc]

private theorem cyclicCover_injective (hN : Function.Injective N) :
    Function.Injective (cyclicCover N) :=
  fun i i' h ↦ hN (by rw [← preimage_copy_zero (N := N) i, h, preimage_copy_zero])

private theorem isAntichain_range_cyclicCover (hN : Function.Injective N)
    (h : IsAntichain (· ⊆ ·) (range N)) : IsAntichain (· ⊆ ·) (range (cyclicCover N)) := by
  rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩ hne hsub
  refine h ⟨i, rfl⟩ ⟨i', rfl⟩ (fun heq ↦ hne (congrArg _ (hN heq))) ?_
  rw [← preimage_copy_zero (N := N) i, ← preimage_copy_zero (N := N) i']
  exact preimage_mono hsub

end Cover

/-! ### The intersection is the greatest natural consistent selection -/

variable {F : ∀ A : Type u, Set (Set A) → Set A}

theorem IsNaturalSelection.subset_sInter (hnat : IsNaturalSelection F)
    (hcons : IsConsistentSelection F) {A : Type u} {𝓚 : Set (Set A)}
    (h𝓚 : IsAntichain (· ⊆ ·) 𝓚) (hfin : 𝓚.Finite) : F A 𝓚 ⊆ ⋂₀ 𝓚 := by
  intro a ha K₁ hK₁
  obtain ⟨m, e, hrange⟩ := Set.Finite.fin_embedding hfin
  cases m with
  | zero => obtain ⟨i, -⟩ := hrange ▸ hK₁; exact i.elim0
  | succ n =>
    set N : Fin (n + 1) → Set A := ⇑e
    have hN : Function.Injective N := e.injective
    set 𝓚' := range (cyclicCover N)
    have h𝓚' : IsAntichain (· ⊆ ·) 𝓚' := isAntichain_range_cyclicCover hN (hrange ▸ h𝓚)
    have hzero : F A 𝓚 = (fun x : A ↦ (x, (0 : Fin (n + 1)))) ⁻¹' F _ 𝓚' :=
      hnat _ h𝓚' (hrange ▸ bijOn_preimage_range (.refl _) hN preimage_copy_zero)
    have hshift : F _ 𝓚' = (fun p : A × Fin (n + 1) ↦ (p.1, p.2 + 1)) ⁻¹' F _ 𝓚' :=
      hnat _ h𝓚' <|
        bijOn_preimage_range (Equiv.addRight 1) (cyclicCover_injective hN) preimage_shift
    have hall (j : Fin (n + 1)) : (a, j) ∈ F _ 𝓚' := by
      induction j using Fin.induction with
      | zero => rwa [hzero] at ha
      | succ j ih =>
        rw [hshift] at ih
        simpa [Fin.coeSucc_eq_succ] using ih
    obtain ⟨_, ⟨i, rfl⟩, hsub⟩ := hcons h𝓚' (finite_range _) (range_nonempty _)
    obtain ⟨i₁, rfl⟩ := hrange ▸ hK₁
    simpa [cyclicCover] using hsub (hall (i₁ - i))

theorem isNaturalSelection_sInter : IsNaturalSelection fun A (𝓚 : Set (Set A)) ↦ ⋂₀ 𝓚 := by
  intro A A' f 𝓚 𝓚' _ hbij
  simp only [preimage_sInter, ← hbij.image_eq, sInter_image]

theorem isConsistentSelection_sInter :
    IsConsistentSelection fun A (𝓚 : Set (Set A)) ↦ ⋂₀ 𝓚 := by
  rintro A 𝓚 - - ⟨K, hK⟩
  exact ⟨K, hK, sInter_subset_of_mem hK⟩

/-- On a finite antichain, the intersection is the greatest set a natural consistent rule
selects. -/
theorem isGreatest_sInter {A : Type u} {𝓚 : Set (Set A)} (h𝓚 : IsAntichain (· ⊆ ·) 𝓚)
    (hfin : 𝓚.Finite) :
    IsGreatest ((fun F ↦ F A 𝓚) '' {F | IsNaturalSelection F ∧ IsConsistentSelection F})
      (⋂₀ 𝓚) :=
  ⟨⟨_, ⟨isNaturalSelection_sInter, isConsistentSelection_sInter⟩, rfl⟩,
    by rintro _ ⟨F, ⟨hnat, hcons⟩, rfl⟩; exact hnat.subset_sInter hcons h𝓚 hfin⟩

open scoped Classical in
/-- Choosing a member of the family is consistent but not natural, since on two disjoint options
it selects one of them, outside their intersection. -/
theorem not_isNaturalSelection_choose :
    ¬ IsNaturalSelection.{0} fun _ 𝓚 ↦ if h : 𝓚.Nonempty then h.some else ∅ := by
  intro hnat
  have hcons : IsConsistentSelection.{0} fun _ 𝓚 ↦ if h : 𝓚.Nonempty then h.some else ∅ :=
    fun _ _ _ _ h ↦ ⟨h.some, h.some_mem, by simp [h]⟩
  have h𝓚 : IsAntichain (· ⊆ ·) ({{true}, {false}} : Set (Set Bool)) := by
    simp [IsAntichain, Set.Pairwise]
  have := hnat.subset_sInter hcons h𝓚 (by simp)
  have hne : ({{true}, {false}} : Set (Set Bool)).Nonempty := ⟨_, mem_insert _ _⟩
  simp only [hne, dite_true] at this
  have h := hne.some_mem
  simp only [mem_insert_iff, mem_singleton_iff] at h
  rcases h with h | h <;> rw [h] at this <;> simp at this

theorem isGreatest_setOf_forall_maximal {α : Type u} {s : Set α} {P : Set α → Prop}
    (hs : s.Finite) (hP : ∀ X, P X → X ⊆ s) (hne : ∃ X, P X) :
    IsGreatest ((fun F ↦ F _ {X | Maximal P X}) ''
        {F | IsNaturalSelection F ∧ IsConsistentSelection F})
      {a ∈ s | ∀ X, Maximal P X → a ∈ X} := by
  have hfin' : {X | P X}.Finite := hs.finite_subsets.subset hP
  obtain ⟨X, hX⟩ := hne
  obtain ⟨K, -, hK⟩ := Set.Finite.exists_le_maximal hfin' hX
  have heq : {a ∈ s | ∀ X, Maximal P X → a ∈ X} = ⋂₀ {X | Maximal P X} :=
    ext fun a ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨hP K hK.1 (h K hK), h⟩⟩
  rw [heq]
  exact isGreatest_sInter (setOfPred_maximal_antichain P)
    (hfin'.subset fun _ h ↦ h.1)

end Set
