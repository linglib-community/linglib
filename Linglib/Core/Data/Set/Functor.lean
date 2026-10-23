/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.Control.Functor
public import Mathlib.Data.Set.Functor
public import Mathlib.Logic.Relation
public import Mathlib.Logic.Relator

/-!
# Relation lifting to sets

Mirror of `Mathlib/Data/Set/Functor.lean`: the relation lifting of the powerset functor.
`Set.LiftRel r s t` holds when every member of `s` is `r`-related to some member of `t` and every
member of `t` is `r`-related from some member of `s`. This is the Egli–Milner lifting, the `Set`
counterpart of `Computation.LiftRel`, and at a homogeneous relation the functor-level
`Functor.Liftr`. [UPSTREAM]

## Main definitions

* `Set.LiftRel r s t`: every member of `s` has an `r`-partner in `t`, and conversely.

## Main results

* `Set.liftRel_iff_subset_preimage_image`, `Set.liftRel_iff_exists_dom_cod`,
  `Set.liftRel_iff_biTotal`, `Set.liftRel_iff_liftr`: the lifting as two `SetRel` image
  inclusions, as a subrelation with the given domain and codomain, as bitotality of the
  restriction, and as `Functor.Liftr`.
* `Set.liftRel_eq`, `Set.liftRel_comp`: the lifting sends equality to equality and relational
  composition to composition.
* `Set.LiftRel.union`, `Set.LiftRel.biUnion`: closure under unions, and under the indexed unions
  of related families, the `bind` of `Computation.liftRel_bind`.
* The lifting of a reflexive, symmetric or transitive relation is reflexive, symmetric or
  transitive, and `Set.LiftRel.equiv` for equivalences.

## Implementation notes

By `liftRel_eq` and `liftRel_comp` the lifting is a functor from relations to relations; a lift of
dynamic meanings to plural states is an instance, and inherits identity and sequencing from here.
-/

@[expose] public section

namespace Set

variable {α β γ δ : Type*} {r p : α → β → Prop} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β}

/-- The relation lifting of `r` to sets: every member of `s` is `r`-related to some member of `t`,
and every member of `t` is `r`-related from some member of `s`. -/
def LiftRel (r : α → β → Prop) (s : Set α) (t : Set β) : Prop :=
  (∀ a ∈ s, ∃ b ∈ t, r a b) ∧ ∀ b ∈ t, ∃ a ∈ s, r a b

theorem liftRel_iff_subset_preimage_image :
    LiftRel r s t ↔ s ⊆ SetRel.preimage {q | r q.1 q.2} t ∧ t ⊆ SetRel.image {q | r q.1 q.2} s :=
  Iff.rfl

/-- The lifting holds exactly when some subrelation of `r` has domain `s` and codomain `t`. -/
theorem liftRel_iff_exists_dom_cod :
    LiftRel r s t ↔ ∃ D : SetRel α β, D ⊆ {q | r q.1 q.2} ∧ D.dom = s ∧ D.cod = t := by
  refine ⟨fun ⟨hl, hr⟩ ↦ ⟨{q | q.1 ∈ s ∧ q.2 ∈ t ∧ r q.1 q.2}, fun _ h ↦ h.2.2,
    Set.ext fun a ↦ ⟨fun ⟨_, ha, _⟩ ↦ ha, fun ha ↦ ?_⟩,
    Set.ext fun b ↦ ⟨fun ⟨_, _, hb, _⟩ ↦ hb, fun hb ↦ ?_⟩⟩, ?_⟩
  · obtain ⟨b, hb, hab⟩ := hl a ha
    exact ⟨b, ha, hb, hab⟩
  · obtain ⟨a, ha, hab⟩ := hr b hb
    exact ⟨a, ha, hb, hab⟩
  · rintro ⟨D, hD, rfl, rfl⟩
    exact ⟨fun a ⟨b, hab⟩ ↦ ⟨b, ⟨a, hab⟩, hD hab⟩, fun b ⟨a, hab⟩ ↦ ⟨a, ⟨b, hab⟩, hD hab⟩⟩

theorem liftRel_iff_biTotal : LiftRel r s t ↔ Relator.BiTotal fun (a : s) (b : t) ↦ r a b := by
  simp [LiftRel, Relator.BiTotal, Relator.LeftTotal, Relator.RightTotal]

/-- At a homogeneous relation, the lifting is the functor-level `Functor.Liftr` of `Set`. -/
theorem liftRel_iff_liftr {r : α → α → Prop} {s t : Set α} :
    LiftRel r s t ↔ Functor.Liftr r s t := by
  rw [liftRel_iff_exists_dom_cod]
  constructor
  · rintro ⟨D, hD, rfl, rfl⟩
    refine ⟨{q | q.1 ∈ D}, Set.ext fun a ↦ ?_, Set.ext fun b ↦ ?_⟩ <;>
      simp only [Set.fmap_eq_image, Set.mem_image, Set.mem_ofPred_eq, Subtype.exists,
        SetRel.mem_dom, SetRel.mem_cod]
    · exact ⟨fun ⟨q, _, hq, e⟩ ↦ ⟨q.2, e ▸ hq⟩, fun ⟨b, h⟩ ↦ ⟨(a, b), hD h, h, rfl⟩⟩
    · exact ⟨fun ⟨q, _, hq, e⟩ ↦ ⟨q.1, e ▸ hq⟩, fun ⟨a, h⟩ ↦ ⟨(a, b), hD h, h, rfl⟩⟩
  · rintro ⟨u, rfl, rfl⟩
    refine ⟨Subtype.val '' u, fun _ ⟨q, _, hq⟩ ↦ hq ▸ q.2, Set.ext fun a ↦ ?_, Set.ext fun b ↦ ?_⟩
    · simp [Set.fmap_eq_image]
    · simp [Set.fmap_eq_image]

theorem liftRel_swap : LiftRel (Function.swap r) t s ↔ LiftRel r s t :=
  and_comm

theorem LiftRel.imp (H : ∀ {a b}, r a b → p a b) (h : LiftRel r s t) : LiftRel p s t :=
  ⟨fun a ha ↦ (h.1 a ha).imp fun _ ⟨hb, hab⟩ ↦ ⟨hb, H hab⟩,
    fun b hb ↦ (h.2 b hb).imp fun _ ⟨ha, hab⟩ ↦ ⟨ha, H hab⟩⟩

theorem liftRel_refl_of_refl_on {r : α → α → Prop} (H : ∀ a ∈ s, r a a) : LiftRel r s s :=
  ⟨fun a ha ↦ ⟨a, ha, H a ha⟩, fun a ha ↦ ⟨a, ha, H a ha⟩⟩

@[simp]
theorem liftRel_eq {s t : Set α} : LiftRel (· = ·) s t ↔ s = t := by
  refine ⟨fun ⟨h₁, h₂⟩ ↦ Set.Subset.antisymm (fun a ha ↦ ?_) fun a ha ↦ ?_, ?_⟩
  · obtain ⟨b, hb, rfl⟩ := h₁ a ha
    exact hb
  · obtain ⟨b, hb, rfl⟩ := h₂ a ha
    exact hb
  · rintro rfl
    exact liftRel_refl_of_refl_on fun _ _ ↦ rfl

/-- The lifting of a composite relation is the composite of the liftings. -/
theorem liftRel_comp {p : β → γ → Prop} {u : Set γ} :
    LiftRel (Relation.Comp r p) s u ↔ ∃ t, LiftRel r s t ∧ LiftRel p t u := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨{b | ∃ a ∈ s, ∃ c ∈ u, r a b ∧ p b c}, ⟨fun a ha ↦ ?_, ?_⟩, ?_, fun c hc ↦ ?_⟩
    · obtain ⟨c, hc, b, hab, hbc⟩ := h₁ a ha
      exact ⟨b, ⟨a, ha, c, hc, hab, hbc⟩, hab⟩
    · rintro b ⟨a, ha, -, -, hab, -⟩
      exact ⟨a, ha, hab⟩
    · rintro b ⟨-, -, c, hc, -, hbc⟩
      exact ⟨c, hc, hbc⟩
    · obtain ⟨a, ha, b, hab, hbc⟩ := h₂ c hc
      exact ⟨b, ⟨a, ha, c, hc, hab, hbc⟩, hbc⟩
  · rintro ⟨t, ⟨hst, hts⟩, htu, hut⟩
    refine ⟨fun a ha ↦ ?_, fun c hc ↦ ?_⟩
    · obtain ⟨b, hb, hab⟩ := hst a ha
      obtain ⟨c, hc, hbc⟩ := htu b hb
      exact ⟨c, hc, b, hab, hbc⟩
    · obtain ⟨b, hb, hbc⟩ := hut c hc
      obtain ⟨a, ha, hab⟩ := hts b hb
      exact ⟨a, ha, b, hab, hbc⟩

instance {r : α → α → Prop} [Std.Refl r] : Std.Refl (LiftRel r) :=
  ⟨fun _ ↦ liftRel_refl_of_refl_on fun a _ ↦ refl_of r a⟩

instance {r : α → α → Prop} [Std.Symm r] : Std.Symm (LiftRel r) :=
  ⟨fun _ _ h ↦ (liftRel_swap.2 h).imp fun hab ↦ symm_of r hab⟩

instance {r : α → α → Prop} [IsTrans α r] : IsTrans (Set α) (LiftRel r) :=
  ⟨fun _ _ _ h₁ h₂ ↦ (liftRel_comp.2 ⟨_, h₁, h₂⟩).imp fun ⟨_, hab, hbc⟩ ↦ trans_of r hab hbc⟩

theorem LiftRel.equiv {r : α → α → Prop} (H : Equivalence r) : Equivalence (LiftRel r) :=
  ⟨fun _ ↦ liftRel_refl_of_refl_on fun a _ ↦ H.refl a,
    fun h ↦ (liftRel_swap.2 h).imp H.symm,
    fun h₁ h₂ ↦ (liftRel_comp.2 ⟨_, h₁, h₂⟩).imp fun ⟨_, hab, hbc⟩ ↦ H.trans hab hbc⟩

@[simp]
theorem liftRel_singleton {a : α} {b : β} : LiftRel r {a} {b} ↔ r a b := by
  simp [LiftRel]

theorem liftRel_singleton_right (hs : s.Nonempty) {b : β} :
    LiftRel r s {b} ↔ ∀ a ∈ s, r a b := by
  simp only [LiftRel, Set.mem_singleton_iff, exists_eq_left, forall_eq]
  refine ⟨And.left, fun h ↦ ⟨h, ?_⟩⟩
  obtain ⟨a, ha⟩ := hs
  exact ⟨a, ha, h a ha⟩

theorem LiftRel.nonempty_iff (h : LiftRel r s t) : s.Nonempty ↔ t.Nonempty :=
  ⟨fun ⟨a, ha⟩ ↦ let ⟨b, hb, _⟩ := h.1 a ha; ⟨b, hb⟩,
    fun ⟨b, hb⟩ ↦ let ⟨a, ha, _⟩ := h.2 b hb; ⟨a, ha⟩⟩

theorem LiftRel.eq_empty_iff (h : LiftRel r s t) : s = ∅ ↔ t = ∅ := by
  simp only [← Set.not_nonempty_iff_eq_empty, h.nonempty_iff]

theorem LiftRel.union (h₁ : LiftRel r s₁ t₁) (h₂ : LiftRel r s₂ t₂) :
    LiftRel r (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  ⟨fun a ha ↦ ha.elim (fun ha ↦ (h₁.1 a ha).imp fun _ ⟨hb, hab⟩ ↦ ⟨.inl hb, hab⟩)
      fun ha ↦ (h₂.1 a ha).imp fun _ ⟨hb, hab⟩ ↦ ⟨.inr hb, hab⟩,
    fun b hb ↦ hb.elim (fun hb ↦ (h₁.2 b hb).imp fun _ ⟨ha, hab⟩ ↦ ⟨.inl ha, hab⟩)
      fun hb ↦ (h₂.2 b hb).imp fun _ ⟨ha, hab⟩ ↦ ⟨.inr ha, hab⟩⟩

/-- Lifted families over lifted index sets: if `s` and `t` are related and related indices carry
related sets, the indexed unions are related. -/
theorem LiftRel.biUnion {q : γ → δ → Prop} {f : α → Set γ} {g : β → Set δ}
    (h : LiftRel r s t) (H : ∀ a ∈ s, ∀ b ∈ t, r a b → LiftRel q (f a) (g b)) :
    LiftRel q (⋃ a ∈ s, f a) (⋃ b ∈ t, g b) := by
  refine ⟨fun c hc ↦ ?_, fun d hd ↦ ?_⟩
  · obtain ⟨a, ha, hc⟩ := Set.mem_iUnion₂.1 hc
    obtain ⟨b, hb, hab⟩ := h.1 a ha
    obtain ⟨d, hd, hcd⟩ := (H a ha b hb hab).1 c hc
    exact ⟨d, Set.mem_iUnion₂.2 ⟨b, hb, hd⟩, hcd⟩
  · obtain ⟨b, hb, hd⟩ := Set.mem_iUnion₂.1 hd
    obtain ⟨a, ha, hab⟩ := h.2 b hb
    obtain ⟨c, hc, hcd⟩ := (H a ha b hb hab).2 d hd
    exact ⟨c, Set.mem_iUnion₂.2 ⟨a, ha, hc⟩, hcd⟩

end Set
