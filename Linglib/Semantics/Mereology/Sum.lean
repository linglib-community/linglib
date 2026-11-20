module

public import Linglib.Semantics.Mereology.Basic

/-!
# Sums and the principles of part structures

A sum of a region, in Tarski's sense, is a bound of its members each of whose non-null parts
overlaps one of them. It [overlaps exactly what its members overlap](##Mereology.IsSum.overlap_iff),
which is the other definition of sum in use, and the two definitions agree in a part structure
that is strongly supplemented: whatever is not part of `y` has a non-null part that does not
overlap `y`. There [a sum is a least upper bound](##Mereology.IsSum.isLUB), so a predicate has at
most one. Two further principles are stated here: the product of two overlapping individuals,
and that a binary join is a sum. Boolean algebras satisfy all three. Closure of a
predicate under the sums of its inhabited subpredicates is cumulative reference in its general
form, and [the predicates so closed are the fixed points](##Mereology.sumClosed_iff) of algebraic
closure under arbitrary sums, which on a finite predicate is
closure under binary sums (`Mereology.sumClosure_eq_supClosure`).

## Implementation notes

The second clause of a sum ranges over non-null parts, as `Overlap` relates non-null parts. On a
carrier without a null individual this is Tarski's definition; on a carrier with one, his
definition holds of nothing, since the null individual overlaps nothing, and the present one
holds of least upper bounds in a Boolean algebra.

## References

* [champollion-krifka-2016], [champollion-2017], [krifka-1989], [krifka-1998]
-/

@[expose] public section

namespace Mereology

variable {α : Type*}

/-- Without a null individual, two elements overlap iff they share a part. -/
theorem overlap_iff_exists_le [PartialOrder α] [NoBotOrder α] {x y : α} :
    Overlap x y ↔ ∃ z, z ≤ x ∧ z ≤ y :=
  ⟨fun ⟨z, _, hzx, hzy⟩ ↦ ⟨z, hzx, hzy⟩, fun ⟨z, hzx, hzy⟩ ↦ ⟨z, not_isBot z, hzx, hzy⟩⟩

/-! ### Sums -/

section Sum

variable [PartialOrder α] {P Q : Set α} {s t x y : α}

/-- `t` is a sum of the region `P` ([champollion-krifka-2016]) if it lies above each member and
each of its non-null parts overlaps one of them. -/
def IsSum (P : Set α) (t : α) : Prop :=
  (∀ x ∈ P, x ≤ t) ∧ ∀ y ≤ t, ¬ IsBot y → ∃ x ∈ P, Overlap y x

/-- Every individual is the sum of itself. -/
theorem isSum_singleton (x : α) : IsSum {x} x :=
  ⟨fun _ h ↦ (Set.mem_singleton_iff.1 h).le, fun _ hy hy0 ↦ ⟨x, rfl, .of_le hy0 hy⟩⟩

/-- A sum overlaps exactly what its members overlap. -/
theorem IsSum.overlap_iff (h : IsSum P t) (w : α) : Overlap w t ↔ ∃ x ∈ P, Overlap w x :=
  ⟨fun ⟨p, hp, hpw, hpt⟩ ↦ let ⟨x, hx, ho⟩ := h.2 p hpt hp; ⟨x, hx, ho.mono hpw le_rfl⟩,
    fun ⟨x, hx, ho⟩ ↦ ho.mono le_rfl (h.1 x hx)⟩

/-- A sum of sums of subregions of `P` is a sum of a subregion of `P`. -/
theorem IsSum.bind {R : α → Set α} (ht : IsSum Q t) (hQ : ∀ q ∈ Q, IsSum (R q) q) :
    IsSum (⋃ q ∈ Q, R q) t :=
  ⟨fun _ hx ↦ let ⟨q, hq, hx⟩ := Set.mem_iUnion₂.1 hx; ((hQ q hq).1 _ hx).trans (ht.1 q hq),
    fun y hy hy0 ↦
      let ⟨q, hq, p, hp0, hpy, hpq⟩ := ht.2 y hy hy0
      let ⟨x, hx, ho⟩ := (hQ q hq).2 p hpq hp0
      ⟨x, Set.mem_iUnion₂.2 ⟨q, hq, hx⟩, ho.mono hpy le_rfl⟩⟩

end Sum

/-! ### Strong supplementation and products -/

/-- A part structure is strongly supplemented if whatever is not part of `y` has a non-null part
that does not overlap `y`. -/
class StronglySupplemented (α : Type*) [PartialOrder α] : Prop where
  exists_not_overlap ⦃x y : α⦄ : ¬ x ≤ y → ∃ z ≤ x, ¬ IsBot z ∧ ¬ Overlap z y

/-- A part structure has products if two overlapping individuals have a greatest common part. -/
class HasProducts (α : Type*) [PartialOrder α] : Prop where
  exists_isGLB ⦃x y : α⦄ : Overlap x y → ∃ p, IsGLB {x, y} p

/-- In a part structure with binary sums, the join of two individuals is their sum: each of its
non-null parts overlaps one of the two. Boolean algebras and classical mereologies satisfy this;
the lattice of three atoms any two of which join to the top does not. -/
class SupIsSum (α : Type*) [SemilatticeSup α] : Prop where
  isSum_sup (x y : α) : IsSum {x, y} (x ⊔ y)

export SupIsSum (isSum_sup)

section Principles

variable [PartialOrder α] {P : Set α} {s t x y : α}

/-- The product of two overlapping individuals is non-null. -/
theorem Overlap.exists_isGLB [HasProducts α] (h : Overlap x y) :
    ∃ p, ¬ IsBot p ∧ IsGLB {x, y} p :=
  let ⟨p, hp⟩ := HasProducts.exists_isGLB h
  let ⟨_, hq, hqx, hqy⟩ := h
  ⟨p, fun hb ↦ hq (hb.mono (hp.2 (by rintro _ (rfl | rfl) <;> assumption))), hp⟩

variable [StronglySupplemented α]

/-- In a strongly supplemented part structure, `x` is part of whatever all its non-null parts
overlap. -/
theorem le_of_forall_overlap (h : ∀ z ≤ x, ¬ IsBot z → Overlap z y) : x ≤ y := by
  by_contra hxy
  obtain ⟨z, hzx, hz, hzy⟩ := StronglySupplemented.exists_not_overlap hxy
  exact hzy (h z hzx hz)

/-- A proper part of `y` leaves a non-null part of `y` that it does not overlap, weak
supplementation. -/
theorem exists_not_overlap_of_lt (h : x < y) : ∃ z ≤ y, ¬ IsBot z ∧ ¬ Overlap z x :=
  StronglySupplemented.exists_not_overlap h.not_ge

/-- Two individuals that overlap the same things are identical. -/
theorem eq_of_forall_overlap_iff (h : ∀ w, Overlap w x ↔ Overlap w y) : x = y :=
  le_antisymm (le_of_forall_overlap fun z hz hz0 ↦ (h z).1 (.of_le hz0 hz))
    (le_of_forall_overlap fun z hz hz0 ↦ (h z).2 (.of_le hz0 hz))

/-- In a strongly supplemented part structure, a sum is what overlaps exactly what the members
overlap. -/
theorem isSum_iff_forall_overlap :
    IsSum P t ↔ ∀ w, Overlap w t ↔ ∃ x ∈ P, Overlap w x :=
  ⟨IsSum.overlap_iff, fun h ↦ ⟨fun x hx ↦ le_of_forall_overlap fun z hz hz0 ↦
    (h z).2 ⟨x, hx, .of_le hz0 hz⟩, fun y hy hy0 ↦ (h y).1 (.of_le hy0 hy)⟩⟩

/-- In a strongly supplemented part structure, a sum is a least upper bound. -/
theorem IsSum.isLUB (h : IsSum P t) : IsLUB P t :=
  ⟨fun _ hx ↦ h.1 _ hx, fun _ hw ↦ le_of_forall_overlap fun y hy hy0 ↦
    let ⟨_, hx, ho⟩ := h.2 y hy hy0
    ho.mono le_rfl (hw hx)⟩

/-- In a strongly supplemented part structure, a region has at most one sum. -/
theorem IsSum.unique (hs : IsSum P s) (ht : IsSum P t) : s = t := hs.isLUB.unique ht.isLUB

end Principles

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] {P : Set α} {t : α}

instance : StronglySupplemented α where
  exists_not_overlap x y h := ⟨x \ y, sdiff_le, by rwa [isBot_iff_eq_bot, sdiff_eq_bot_iff],
    overlap_iff_not_disjoint.not_left.2 disjoint_sdiff_self_left⟩

/-- In a Boolean algebra the sums are the least upper bounds. -/
theorem isSum_iff_isLUB : IsSum P t ↔ IsLUB P t := by
  refine ⟨IsSum.isLUB, fun h ↦ ⟨fun x hx ↦ h.1 hx, fun y hy hy0 ↦ ?_⟩⟩
  by_contra! hno
  refine hy0 (isBot_iff_eq_bot.2 ?_)
  have ht : t ≤ t \ y := h.2 fun x hx ↦
    le_sdiff.2 ⟨h.1 hx, (overlap_iff_not_disjoint.not_left.1 (hno x hx)).symm⟩
  exact (disjoint_sdiff_self_right.mono_right ht).eq_bot_of_le hy

instance : SupIsSum α where
  isSum_sup _ _ := isSum_iff_isLUB.2 isLUB_pair

end GeneralizedBooleanAlgebra

instance [SemilatticeInf α] : HasProducts α where
  exists_isGLB x y _ := ⟨x ⊓ y, isGLB_pair⟩

/-! ### Closure under sums -/

section SumClosed

variable [PartialOrder α] {P : Set α} {x : α}

/-- A region is closed under sums if it has every sum of its nonempty subregions, cumulative
reference in the form that covers infinite sums ([champollion-krifka-2016]). -/
def SumClosed (P : Set α) : Prop :=
  ∀ Q ⊆ P, Q.Nonempty → ∀ t, IsSum Q t → t ∈ P

/-- The closure of `P` under sums ([champollion-krifka-2016]) is the region of the sums of the
nonempty subregions of `P`. -/
def sumClosure (P : Set α) : Set α :=
  {x | ∃ Q ⊆ P, Q.Nonempty ∧ IsSum Q x}

theorem subset_sumClosure : P ⊆ sumClosure P := fun x h ↦
  ⟨{x}, Set.singleton_subset_iff.2 h, Set.singleton_nonempty x, isSum_singleton x⟩

/-- The closure of a region under sums is closed under sums. -/
theorem sumClosed_sumClosure (P : Set α) : SumClosed (sumClosure P) := by
  intro Q hQ ⟨q₀, hq₀⟩ t ht
  have hQ' : ∀ q ∈ Q, ∃ R : Set α, R ⊆ P ∧ R.Nonempty ∧ IsSum R q := fun q hq ↦ hQ hq
  choose! R hRP hRne hR using hQ'
  obtain ⟨y, hy⟩ := hRne q₀ hq₀
  exact ⟨⋃ q ∈ Q, R q, Set.iUnion₂_subset hRP, ⟨y, Set.mem_iUnion₂.2 ⟨q₀, hq₀, hy⟩⟩, ht.bind hR⟩

/-- A region is closed under sums iff its closure under sums adds nothing to it, as the plural of
a cumulative mass noun adds nothing. -/
theorem sumClosed_iff : SumClosed P ↔ sumClosure P ⊆ P :=
  ⟨fun h _ ⟨Q, hQ, hne, hx⟩ ↦ h Q hQ hne _ hx, fun h Q hQ hne _ ht ↦ h ⟨Q, hQ, hne, ht⟩⟩

end SumClosed

section SupIsSum

variable [SemilatticeSup α] {P : Set α} {x : α}

/-- A region closed under sums is cumulative. -/
theorem SumClosed.cum [SupIsSum α] (h : SumClosed P) : CUM P :=
  fun x hx y hy ↦ h {x, y} (by rintro _ (rfl | rfl) <;> assumption) (Set.insert_nonempty _ _) _
    (isSum_sup x y)

/-- The closure under binary sums lies in the closure under sums. -/
theorem supClosure_subset_sumClosure [SupIsSum α] : supClosure P ⊆ sumClosure P :=
  supClosure_min subset_sumClosure (sumClosed_sumClosure P).cum

/-- The closure of a finite region under sums lies in its closure under binary sums. -/
theorem sumClosure_subset_supClosure [StronglySupplemented α] (hP : P.Finite) :
    sumClosure P ⊆ supClosure P := by
  rintro x ⟨Q, hQ, ⟨q, hq⟩, hx⟩
  have hfin : Q.Finite := hP.subset hQ
  have hne : hfin.toFinset.Nonempty := ⟨q, hfin.mem_toFinset.2 hq⟩
  have hlub : IsLUB Q (hfin.toFinset.sup' hne id) := by
    simpa using Finset.isLUB_sup' hne
  rw [hx.isLUB.unique hlub]
  exact finsetSup'_mem_supClosure hne fun y hy ↦ hQ (hfin.mem_toFinset.1 hy)

/-- The two algebraic closures of a finite region agree. -/
theorem sumClosure_eq_supClosure [StronglySupplemented α] [SupIsSum α] (hP : P.Finite) :
    sumClosure P = supClosure P :=
  (sumClosure_subset_supClosure hP).antisymm supClosure_subset_sumClosure

end SupIsSum

end Mereology
