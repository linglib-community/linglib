module

public import Linglib.Semantics.Mereology.Basic

/-!
# Classical mereology

Classical extensional mereology is a partial order in which every inhabited predicate has a
unique sum in Tarski's sense, a bound each of whose parts overlaps a member. Weak and strong
supplementation and the absence of a null individual are theorems, a proper part
[has a unique remainder](##Mereology.IsClassicalMereology.existsUnique_remainder), and two
overlapping individuals have a product, so classical mereologies satisfy the principles Boolean
algebras do: `HasRemainders`, `StronglySupplemented` and `HasProducts`. The nonempty subsets of
a set with two elements or more form a classical mereology whose sums are unions.

## Implementation notes

Classical mereology is defined, as in Champollion's book, by unique sums; Hovda compares the
alternative axiomatizations. Since `Overlap` excludes null parts, the element of a one-point
carrier is null, so the trivial model is not a classical mereology.

## References

* [champollion-krifka-2016], [champollion-2017], [hovda-2009], [krifka-1989], [krifka-1998]
-/

@[expose] public section

namespace Mereology

variable {α β : Type*}

/-! ### The remainder principle

A proper part of a whole is completed to the whole by a remainder that does not overlap it.
This is the remainder principle of [krifka-1998], the relative complementarity of
[krifka-1989], and the unique separation of [champollion-2017]. Boolean algebras satisfy it with
the difference `y \ x`, and so do classical mereologies (`IsClassicalMereology.exists_remainder`).
The sources also require the remainder to be unique; the results below need only existence. -/

/-- A part structure has remainders if every proper part `x` of `y` is completed to `y` by a
part that does not overlap `x`. -/
class HasRemainders (α : Type*) [SemilatticeSup α] : Prop where
  exists_remainder : ∀ ⦃x y : α⦄, x < y → ∃ z, ¬ Overlap z x ∧ x ⊔ z = y

instance [GeneralizedBooleanAlgebra α] : HasRemainders α where
  exists_remainder _ y h :=
    ⟨y \ _, overlap_iff_not_disjoint.not_left.2 disjoint_sdiff_self_left,
      sup_sdiff_cancel_right h.le⟩

/-! ### Strong supplementation and products

Two further principles hold both of Boolean algebras and of classical mereologies: whatever is
not part of `y` has a part that does not overlap `y`, and two overlapping individuals have a
greatest common part, their product. -/

/-- A part structure is strongly supplemented if whatever is not part of `y` has a non-null part
that does not overlap `y`. -/
class StronglySupplemented (α : Type*) [PartialOrder α] : Prop where
  exists_not_overlap ⦃x y : α⦄ : ¬ x ≤ y → ∃ z ≤ x, ¬ IsBot z ∧ ¬ Overlap z y

/-- A part structure has products if two overlapping individuals have a greatest common part. -/
class HasProducts (α : Type*) [PartialOrder α] : Prop where
  exists_isGLB ⦃x y : α⦄ : Overlap x y → ∃ p, IsGLB {x, y} p

/-- In a strongly supplemented part structure, `x` is part of whatever all its non-null parts
overlap. -/
theorem le_of_forall_overlap [PartialOrder α] [StronglySupplemented α] {x y : α}
    (h : ∀ z ≤ x, ¬ IsBot z → Overlap z y) : x ≤ y := by
  by_contra hxy
  obtain ⟨z, hzx, hz, hzy⟩ := StronglySupplemented.exists_not_overlap hxy
  exact hzy (h z hzx hz)

/-- The product of two overlapping individuals is non-null. -/
theorem Overlap.exists_isGLB [PartialOrder α] [HasProducts α] {x y : α} (h : Overlap x y) :
    ∃ p, ¬ IsBot p ∧ IsGLB {x, y} p :=
  let ⟨p, hp⟩ := HasProducts.exists_isGLB h
  let ⟨_, hq, hqx, hqy⟩ := h
  ⟨p, fun hb ↦ hq (hb.mono (hp.2 (by rintro _ (rfl | rfl) <;> assumption))), hp⟩

instance [GeneralizedBooleanAlgebra α] : StronglySupplemented α where
  exists_not_overlap x y h := ⟨x \ y, sdiff_le, by rwa [isBot_iff_eq_bot, sdiff_eq_bot_iff],
    overlap_iff_not_disjoint.not_left.2 disjoint_sdiff_self_left⟩

instance [SemilatticeInf α] : HasProducts α where
  exists_isGLB x y _ := ⟨x ⊓ y, isGLB_pair⟩

/-! ### Classical mereology

Classical extensional mereology is the system of [champollion-krifka-2016] and
[champollion-2017]: a partial order in which every inhabited predicate has a unique sum in
Tarski's sense. Weak and strong supplementation, the remainder principle and the absence of a
null individual are theorems; [hovda-2009] compares this axiomatization with others. Binary sums
are fusions of pairs (`IsClassicalMereology.toSemilatticeSup`), and the nonempty subsets of a set
with two elements or more form a classical mereology. -/

section Classical

variable [PartialOrder α]

/-- `t` is a sum of the `P`-elements in Tarski's sense if it lies above each of them and each of
its parts overlaps one of them. -/
def IsFusion (P : α → Prop) (t : α) : Prop :=
  (∀ x, P x → x ≤ t) ∧ ∀ y, y ≤ t → ∃ x, P x ∧ Overlap y x

/-- A partial order is a classical extensional mereology if every inhabited predicate has a
unique sum. -/
class IsClassicalMereology (α : Type*) [PartialOrder α] : Prop where
  existsUnique_isFusion : ∀ P : α → Prop, (∃ x, P x) → ∃! t, IsFusion P t

namespace IsClassicalMereology

variable [IsClassicalMereology α] {x y u : α}

theorem exists_isFusion (P : α → Prop) (h : ∃ x, P x) : ∃ t, IsFusion P t :=
  (existsUnique_isFusion P h).exists

theorem not_isBot (x : α) : ¬ IsBot x := fun hx ↦ by
  obtain ⟨t, ht⟩ := exists_isFusion (· = x) ⟨x, rfl⟩
  obtain ⟨_, rfl, w, hw, -, hwx⟩ := ht.2 t le_rfl
  exact hw (hx.mono hwx)

theorem overlap_iff : Overlap x y ↔ ∃ z, z ≤ x ∧ z ≤ y :=
  ⟨fun ⟨z, _, hzx, hzy⟩ ↦ ⟨z, hzx, hzy⟩, fun ⟨z, hzx, hzy⟩ ↦ ⟨z, not_isBot z, hzx, hzy⟩⟩

theorem isFusion_eq (x : α) : IsFusion (· = x) x :=
  ⟨fun _ h ↦ h.le, fun z hz ↦ ⟨x, rfl, z, not_isBot z, le_rfl, hz⟩⟩

end IsClassicalMereology

variable [IsClassicalMereology α] {P : α → Prop} {s t x y u : α}

theorem IsFusion.unique (hs : IsFusion P s) (ht : IsFusion P t) : s = t :=
  let ⟨x, hx, _⟩ := hs.2 s le_rfl
  (IsClassicalMereology.existsUnique_isFusion P ⟨x, hx⟩).unique hs ht

theorem IsClassicalMereology.weak_supplementation (h : x < y) : ∃ z ≤ y, ¬ Overlap z x := by
  by_contra! hall
  exact h.ne ((IsClassicalMereology.isFusion_eq x).unique
    ⟨fun _ h' ↦ h' ▸ h.le, fun z hz ↦ ⟨x, rfl, hall z hz⟩⟩)

theorem IsFusion.isLUB (h : IsFusion P t) : IsLUB {x | P x} t := by
  refine ⟨fun a ha ↦ h.1 a ha, fun w hw ↦ ?_⟩
  obtain ⟨v, hv⟩ :=
    IsClassicalMereology.exists_isFusion (fun u ↦ u = w ∨ u = t) ⟨w, Or.inl rfl⟩
  have hwv : w ≤ v := hv.1 w (Or.inl rfl)
  have htv : t ≤ v := hv.1 t (Or.inr rfl)
  suffices hvw : v = w by rw [hvw] at htv; exact htv
  by_contra hne
  obtain ⟨s, hsv, hsw⟩ :=
    IsClassicalMereology.weak_supplementation (lt_of_le_of_ne hwv (Ne.symm hne))
  obtain ⟨u, hu, p, hp, hps, hpu⟩ := hv.2 s hsv
  rcases hu with rfl | rfl
  · exact hsw ⟨p, hp, hps, hpu⟩
  · obtain ⟨a, hPa, q, hq, hqp, hqa⟩ := h.2 p hpu
    exact hsw ⟨q, hq, hqp.trans hps, hqa.trans (hw hPa)⟩

namespace IsClassicalMereology

theorem strong_supplementation (h : ¬ y ≤ u) : ∃ v ≤ y, ¬ Overlap v u := by
  obtain ⟨s, hs⟩ := exists_isFusion (fun w ↦ w = y ∨ w = u) ⟨y, .inl rfl⟩
  have hus : u < s := lt_of_le_of_ne (hs.1 u (.inr rfl)) fun he ↦ h (he ▸ hs.1 y (.inl rfl))
  obtain ⟨w, hws, hwu⟩ := weak_supplementation hus
  obtain ⟨p, rfl | rfl, hov⟩ := hs.2 w hws
  · obtain ⟨v, hv, hvw, hvy⟩ := hov
    exact ⟨v, hvy, fun ⟨q, hq, hqv, hqu⟩ ↦ hwu ⟨q, hq, hqv.trans hvw, hqu⟩⟩
  · exact absurd hov hwu

theorem exists_remainder (h : x < y) : ∃ z, ¬ Overlap z x ∧ IsLUB {x, z} y := by
  obtain ⟨w₀, hw₀y, hw₀x⟩ := weak_supplementation h
  obtain ⟨z, hz⟩ := exists_isFusion (fun w ↦ w ≤ y ∧ ¬ Overlap w x) ⟨w₀, hw₀y, hw₀x⟩
  have hzy : z ≤ y := hz.isLUB.2 fun _ hw ↦ hw.1
  refine ⟨z, fun ⟨q, hq, hqz, hqx⟩ ↦ ?_, ⟨?_, fun u hu ↦ ?_⟩⟩
  · obtain ⟨r, ⟨_, hrx⟩, v, hv, hvq, hvr⟩ := hz.2 q hqz
    exact hrx ⟨v, hv, hvr, hvq.trans hqx⟩
  · rintro _ (rfl | rfl)
    exacts [h.le, hzy]
  · by_contra hyu
    obtain ⟨v, hvy, hvu⟩ := strong_supplementation hyu
    have hvz : v ≤ z := hz.isLUB.1
      ⟨hvy, fun ⟨q, hq, hqv, hqx⟩ ↦ hvu ⟨q, hq, hqv, hqx.trans (hu (.inl rfl))⟩⟩
    exact hvu ⟨v, not_isBot v, le_rfl, hvz.trans (hu (.inr rfl))⟩

/-- A classical mereology has no bottom element. -/
instance : NoBotOrder α := ⟨fun x ↦ not_forall.1 (not_isBot x)⟩

instance : StronglySupplemented α where
  exists_not_overlap _ _ h :=
    let ⟨v, hv, ho⟩ := strong_supplementation h
    ⟨v, hv, not_isBot v, ho⟩

theorem remainder_unique {z z' : α} (hz : ¬ Overlap z x) (hlub : IsLUB {x, z} y)
    (hz' : ¬ Overlap z' x) (hlub' : IsLUB {x, z'} y) : z = z' := by
  have key : ∀ {z z' : α}, ¬ Overlap z x → IsLUB {x, z} y → IsLUB {x, z'} y → z ≤ z' := by
    intro z z' hz hlub hlub'
    obtain ⟨f, hf⟩ := exists_isFusion (fun u ↦ u = x ∨ u = z') ⟨x, .inl rfl⟩
    have hfy : f = y := hf.isLUB.unique
      (by rwa [show {u | u = x ∨ u = z'} = ({x, z'} : Set α) from by ext; simp])
    subst hfy
    refine le_of_forall_overlap fun v hv _ ↦ ?_
    obtain ⟨p, rfl | rfl, hov⟩ := hf.2 v (hv.trans (hlub.1 (by simp)))
    · exact absurd (hov.mono hv le_rfl) hz
    · exact hov
  exact le_antisymm (key hz hlub hlub') (key hz' hlub' hlub)

/-- A proper part of `y` has exactly one remainder in `y`, the unique separation of
[krifka-1998] and [champollion-2017]. -/
theorem existsUnique_remainder (h : x < y) : ∃! z, ¬ Overlap z x ∧ IsLUB {x, z} y :=
  let ⟨z, hz, hlub⟩ := exists_remainder h
  ⟨z, ⟨hz, hlub⟩, fun _ ⟨hz', hlub'⟩ ↦ remainder_unique hz' hlub' hz hlub⟩

theorem exists_isLUB_pair (a b : α) : ∃ s, IsLUB {a, b} s := by
  obtain ⟨t, ht⟩ := exists_isFusion (fun u ↦ u = a ∨ u = b) ⟨a, Or.inl rfl⟩
  refine ⟨t, ?_⟩
  have h := ht.isLUB
  rwa [show {x | x = a ∨ x = b} = ({a, b} : Set α) from by ext x; simp [Set.mem_insert_iff]] at h

/-- The product of two overlapping individuals is the sum of their common parts. -/
instance : HasProducts α where
  exists_isGLB x y := fun ⟨q, _, hqx, hqy⟩ ↦ by
    obtain ⟨p, hp⟩ := exists_isFusion (fun w ↦ w ≤ x ∧ w ≤ y) ⟨q, hqx, hqy⟩
    refine ⟨p, ?_, fun w hw ↦ hp.isLUB.1 ⟨hw (.inl rfl), hw (.inr rfl)⟩⟩
    rintro _ (rfl | rfl)
    exacts [hp.isLUB.2 fun _ h ↦ h.1, hp.isLUB.2 fun _ h ↦ h.2]

/-- The binary sum `a ⊔ b` of a classical mereology is the sum of the pair `{a, b}`. -/
@[reducible] noncomputable def toSemilatticeSup : SemilatticeSup α :=
  { ‹PartialOrder α› with
    sup := fun a b ↦ Classical.choose (exists_isLUB_pair a b)
    le_sup_left := fun a b ↦ (Classical.choose_spec (exists_isLUB_pair a b)).1 (Set.mem_insert _ _)
    le_sup_right := fun a b ↦
      (Classical.choose_spec (exists_isLUB_pair a b)).1 (Set.mem_insert_of_mem _ rfl)
    sup_le := fun a b c ha hb ↦ (Classical.choose_spec (exists_isLUB_pair a b)).2 <| by
      rintro _ (rfl | rfl)
      exacts [ha, hb] }

end IsClassicalMereology

end Classical

instance [SemilatticeSup α] [IsClassicalMereology α] : HasRemainders α where
  exists_remainder _ _ h :=
    let ⟨z, hz, hlub⟩ := IsClassicalMereology.exists_remainder h
    ⟨z, hz, (hlub.unique isLUB_pair).symm⟩

section SetModel

variable {ι : Type*} [Nontrivial ι]

private theorem not_isBot_singleton (p : ι) :
    ¬ IsBot (⟨{p}, Set.singleton_nonempty p⟩ : {s : Set ι // s.Nonempty}) := fun h ↦ by
  obtain ⟨q, hq⟩ := exists_ne p
  exact hq (Set.singleton_subset_singleton.1 (h ⟨{q}, Set.singleton_nonempty q⟩)).symm

private theorem isFusion_iff_eq_iUnion {P : {s : Set ι // s.Nonempty} → Prop}
    {t : {s : Set ι // s.Nonempty}} : IsFusion P t ↔ t.1 = ⋃ (x) (_ : P x), x.1 := by
  constructor
  · rintro ⟨hub, hov⟩
    refine Set.Subset.antisymm (fun p hp ↦ ?_) (Set.iUnion₂_subset fun x hx ↦ hub x hx)
    obtain ⟨x, hx, w, -, hwp, hwx⟩ :=
      hov ⟨{p}, Set.singleton_nonempty p⟩ (Set.singleton_subset_iff.2 hp)
    obtain ⟨q, hq⟩ := w.2
    exact Set.mem_iUnion₂.2 ⟨x, hx, (hwp hq : q = p) ▸ hwx hq⟩
  · intro h
    refine ⟨fun x hx ↦ (Set.subset_iUnion₂ (s := fun x (_ : P x) ↦ x.1) x hx).trans h.ge,
      fun y hy ↦ ?_⟩
    obtain ⟨p, hp⟩ := y.2
    obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.1 (h ▸ hy hp : p ∈ ⋃ (x) (_ : P x), x.1)
    exact ⟨x, hx, ⟨{p}, Set.singleton_nonempty p⟩, not_isBot_singleton p,
      Set.singleton_subset_iff.2 hp, Set.singleton_subset_iff.2 hpx⟩

/-- The nonempty subsets of a set with two elements or more form a classical mereology whose
sums are unions ([champollion-2017]). -/
instance : IsClassicalMereology {s : Set ι // s.Nonempty} where
  existsUnique_isFusion P := by
    rintro ⟨x, hx⟩
    have hne : (⋃ (y) (_ : P y), y.1).Nonempty :=
      x.2.mono (Set.subset_iUnion₂ (s := fun y (_ : P y) ↦ y.1) x hx)
    exact ⟨⟨_, hne⟩, isFusion_iff_eq_iUnion.2 rfl,
      fun t ht ↦ Subtype.ext (isFusion_iff_eq_iUnion.1 ht)⟩

end SetModel

end Mereology
