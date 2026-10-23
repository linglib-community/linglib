/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Order.Setoid.Partition

/-!
# Kernel monotonicity, meets, and decidable equality for setoids

This file adds to `Mathlib/Data/Setoid/Basic.lean` the monotonicity of `Setoid.ker` under
composition and its equality case for an injective outer map, the relation of an indexed meet
of setoids, the classes of a meet and the order in terms of classes, and decidable equality of
setoids on a finite type. Mathlib has the monotonicity for algebraic kernels
(`LinearMap.ker_le_ker_comp`, `MonoidHom.comap_ker`, `RingHom.ker_comp_of_injective`) but not for
the plain `Setoid.ker` they specialize. [UPSTREAM]
-/

@[expose] public section

theorem Setoid.ker_le_ker_comp {α β γ : Type*} (f : α → β) (h : β → γ) :
    Setoid.ker f ≤ Setoid.ker (h ∘ f) :=
  Setoid.le_def.mpr fun hxy => congrArg h hxy

theorem Setoid.ker_comp_of_injective {α β γ : Type*} (f : α → β) {g : β → γ}
    (hg : Function.Injective g) : Setoid.ker (g ∘ f) = Setoid.ker f :=
  Setoid.ext fun _ _ ↦ hg.eq_iff

theorem Setoid.iInf_iff {α : Type*} {ι : Sort*} {f : ι → Setoid α} {a b : α} :
    (⨅ i, f i) a b ↔ ∀ i, f i a b := by
  rw [iInf, Setoid.sInf_iff]
  simp

theorem Setoid.classes_inf {α : Type*} (r s : Setoid α) :
    (r ⊓ s).classes = {c | ∃ a ∈ r.classes, ∃ b ∈ s.classes, c = a ∩ b ∧ c.Nonempty} := by
  ext c
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, r.mem_classes y, _, s.mem_classes y, Set.ext fun _ ↦ Setoid.inf_iff_and, y,
      r.refl' y, s.refl' y⟩
  · rintro ⟨a, ⟨x, rfl⟩, b, ⟨y, rfl⟩, rfl, z, hzx, hzy⟩
    refine ⟨z, Set.ext fun v ↦ ?_⟩
    change r v x ∧ s v y ↔ (r ⊓ s) v z
    exact ⟨fun ⟨h₁, h₂⟩ ↦
        Setoid.inf_iff_and.2 ⟨r.trans' h₁ (r.symm' hzx), s.trans' h₂ (s.symm' hzy)⟩,
      fun h ↦ let ⟨h₁, h₂⟩ := Setoid.inf_iff_and.1 h; ⟨r.trans' h₁ hzx, s.trans' h₂ hzy⟩⟩

theorem Setoid.le_iff_forall_classes {α : Type*} {r s : Setoid α} :
    r ≤ s ↔ ∀ a ∈ r.classes, ∃ b ∈ s.classes, a ⊆ b := by
  refine ⟨?_, fun h ↦ Setoid.le_def.2 fun {x y} hxy ↦ ?_⟩
  · rintro h a ⟨y, rfl⟩
    exact ⟨_, s.mem_classes y, fun _ hx ↦ h hx⟩
  · obtain ⟨b, hb, hab⟩ := h _ (r.mem_classes y)
    exact s.rel_iff_exists_classes.2 ⟨b, hb, hab hxy, hab (r.refl' y)⟩

/-- The kernel of a map into a type with decidable equality is decidable. [UPSTREAM] -/
instance Setoid.ker.decidableRel {α β : Type*} (f : α → β) [DecidableEq β] :
    DecidableRel (⇑(Setoid.ker f)) :=
  λ a b => inferInstanceAs (Decidable (f a = f b))

/-- Equality of setoids on a finite type is decided pairwise. [UPSTREAM] -/
instance Setoid.decidableEqOfDecidableRel {α : Type*} [Fintype α] (s t : Setoid α)
    [DecidableRel (⇑s)] [DecidableRel (⇑t)] : Decidable (s = t) :=
  decidable_of_iff (∀ a b, s a b ↔ t a b) Setoid.ext_iff.symm
