/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.PFun
public import Linglib.Core.Order.LeftLinear

/-!
# Partial values

Supplements to `Mathlib/Data/Part.lean`. The domain and value of `Part.restrict` and `Part.bind`
are `simp` lemmas, so `simp` rewrites under a restriction. Partial values are left-linear
(`Part.isLeftLinear`): below a defined value lie only itself and `⊥`, so compatible values are
comparable; a partial function `α → Part β` extends another iff the two agree on its domain
(`PFun.le_iff_eqOn_dom`). Equality and order are decidable where domains are
(`Part.decidableEqOfDom`, `Part.decidableLEOfDom`); a type-level `DecidableEq (Part α)` cannot be
computable, since it would decide every `p` through `⟨p, fun _ ↦ ()⟩ = Part.some ()`. [UPSTREAM]
-/

@[expose] public section

namespace Part

variable {α : Type*} {p : Prop} {o : Part α} {H : p → o.Dom}

@[simp] theorem restrict_dom : (restrict p o H).Dom ↔ p := .rfl

@[simp] theorem get_restrict (h : p) : (restrict p o H).get h = o.get (H h) := rfl

@[simp] theorem get_bind {β : Type*} {f : Part α} {g : α → Part β} (h : (f.bind g).Dom) :
    (f.bind g).get h = (g (f.get (bind_dom.1 h).fst)).get (bind_dom.1 h).snd :=
  rfl

/-! ### The order -/

section Order

variable {o o' : Part α} {a b : α}

theorem bot_eq_none : (⊥ : Part α) = none := rfl

@[simp] theorem bot_ne_some : (⊥ : Part α) ≠ some a := none_ne_some a

@[simp] theorem some_ne_bot : some a ≠ (⊥ : Part α) := some_ne_none a

theorem ne_bot_iff_exists : o ≠ ⊥ ↔ ∃ a, o = some a := ne_none_iff

theorem eq_bot_iff_not_dom : o = ⊥ ↔ ¬o.Dom := eq_none_iff'

theorem some_le_iff : some a ≤ o ↔ o = some a :=
  ⟨fun h ↦ eq_some_iff.2 (h _ (mem_some a)), fun h ↦ h ▸ le_rfl⟩

theorem some_le_some : some a ≤ some b ↔ a = b := by
  rw [some_le_iff, some_inj, eq_comm]

theorem Dom.mono (h : o ≤ o') (ho : o.Dom) : o'.Dom :=
  (h _ (get_mem ho)).fst

/-- A partial value below one that is defined only where it is, is equal to it. -/
theorem eq_of_le (h : o ≤ o') (h' : o'.Dom → o.Dom) : o = o' :=
  ext' ⟨Dom.mono h, h'⟩ fun ho _ ↦ mem_unique (h _ (get_mem ho)) (get_mem _)

/-- A partial value is covered exactly by the defined values above it: the order has height one. -/
theorem covBy_iff : o ⋖ o' ↔ ¬o.Dom ∧ o'.Dom := by
  refine ⟨fun h ↦ ⟨fun ho ↦ h.1.ne (eq_of_le h.1.le fun _ ↦ ho), ?_⟩, fun ⟨ho, ho'⟩ ↦ ⟨?_, ?_⟩⟩
  · by_contra ho'
    exact h.1.ne (eq_of_le h.1.le fun h' ↦ absurd h' ho')
  · exact lt_of_le_of_ne (fun a ha ↦ absurd ha.fst ho) fun h ↦ ho (h ▸ ho')
  · exact fun c hc hc' ↦ hc'.ne (eq_of_le hc'.le fun _ ↦ by_contra fun hc₀ ↦
      hc.ne (eq_of_le hc.le fun h ↦ absurd h hc₀))

/-- Two partial values are bounded above iff they agree wherever both are defined. -/
theorem bddAbove_pair_iff : BddAbove ({o, o'} : Set (Part α)) ↔ ∀ a ∈ o, ∀ b ∈ o', a = b := by
  refine ⟨fun ⟨u, hu⟩ a ha b hb ↦ mem_unique (hu (.inl rfl) _ ha) (hu (.inr rfl) _ hb),
    fun h ↦ ?_⟩
  by_cases ho : o.Dom
  · refine ⟨o, ?_⟩
    rintro _ (rfl | rfl)
    exacts [le_rfl, fun b hb ↦ h _ (get_mem ho) b hb ▸ get_mem ho]
  · refine ⟨o', ?_⟩
    rintro _ (rfl | rfl)
    exacts [fun a ha ↦ absurd ha.fst ho, le_rfl]

/-- Partial values are left-linear: below a defined value lie only itself and `⊥`. -/
instance isLeftLinear : IsLeftLinear (Part α) :=
  ⟨fun a _ _ ha hb ↦ (em a.Dom).symm.imp (fun h _ hx ↦ absurd hx.fst h) fun h x hx ↦
    mem_unique (ha _ (get_mem h)) (hb x hx) ▸ get_mem h⟩

end Order

/-! ### Deciding equality and order -/

section Decidable

variable {o o' : Part α}

theorem toOption_inj [Decidable o.Dom] [Decidable o'.Dom] : o.toOption = o'.toOption ↔ o = o' :=
  ⟨fun h ↦ Part.ext fun a ↦ by rw [← mem_toOption, ← mem_toOption, h], fun h ↦ by subst h; congr⟩

theorem ofOption_injective : Function.Injective (ofOption : Option α → Part α) := fun _ _ h ↦
  Option.ext fun _ ↦ by rw [← Option.mem_def, ← Option.mem_def, ← mem_ofOption, h, mem_ofOption]

/-- Partial values with decidable domains are decidably equal. -/
instance decidableEqOfDom [DecidableEq α] (o o' : Part α) [Decidable o.Dom] [Decidable o'.Dom] :
    Decidable (o = o') :=
  decidable_of_iff _ toOption_inj

theorem le_iff_not_dom_or_eq : o ≤ o' ↔ ¬o.Dom ∨ o = o' := by
  refine ⟨fun h ↦ (em o.Dom).symm.imp_right fun ho ↦ Part.ext' ⟨fun _ ↦ dom_iff_mem.2
    ⟨_, h _ (get_mem ho)⟩, fun _ ↦ ho⟩ fun h₁ h₂ ↦ mem_unique (h _ (get_mem h₁)) (get_mem h₂), ?_⟩
  rintro (h | rfl)
  · exact fun a ha ↦ absurd (dom_iff_mem.2 ⟨a, ha⟩) h
  · exact le_rfl

instance decidableLEOfDom [DecidableEq α] (o o' : Part α) [Decidable o.Dom] [Decidable o'.Dom] :
    Decidable (o ≤ o') :=
  decidable_of_iff _ le_iff_not_dom_or_eq.symm

instance botDecidable : Decidable (⊥ : Part α).Dom :=
  noneDecidable

end Decidable

end Part

/-! ### Families of partial values -/

section Pi

variable {ι : Type*} {β : ι → Type*}

instance Pi.botPartDecidable (i : ι) : Decidable ((⊥ : ∀ i, Part (β i)) i).Dom :=
  Part.noneDecidable

/-- One family extends another when it agrees with it wherever the other is defined. -/
theorem Part.pi_le_iff {s t : ∀ i, Part (β i)} : s ≤ t ↔ ∀ i, s i ≠ ⊥ → t i = s i := by
  refine ⟨fun h i hi ↦ ?_, fun h i a ha ↦ ?_⟩
  · obtain ⟨a, ha⟩ := Part.ne_bot_iff_exists.1 hi
    have hle := h i
    rw [ha] at hle ⊢
    exact Part.some_le_iff.1 hle
  · have hi : s i ≠ ⊥ := fun hb ↦ Part.not_none_dom (hb ▸ Part.dom_iff_mem.2 ⟨a, ha⟩)
    exact h i hi ▸ ha

/-- The domain of an updated family is decided from the update and the family at the same index,
so nested updates are decided index by index. -/
instance Function.updatePartDecidable [DecidableEq ι] (f : ∀ i, Part (β i)) (c : ι)
    (x : Part (β c)) (i : ι) [Decidable (f i).Dom] [Decidable x.Dom] :
    Decidable (Function.update f c x i).Dom :=
  if h : i = c then decidable_of_iff x.Dom (by subst h; rw [Function.update_self])
  else decidable_of_iff (f i).Dom (by rw [Function.update_of_ne h])

end Pi

/-! ### Partial functions

A partial function `α →. β` is a family `α → Part β`, ordered pointwise by extension, with domain
`PFun.Dom`. -/

namespace PFun

variable {α β : Type*} {f g : α → Part β}

@[simp] theorem dom_bot : Dom (⊥ : α → Part β) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ↦ Part.not_none_dom (α := β)

theorem dom_mono (h : f ≤ g) : Dom f ⊆ Dom g := fun a ↦ Part.Dom.mono (h a)

/-- One partial function extends another iff they agree on the other's domain. -/
theorem le_iff_eqOn_dom : f ≤ g ↔ Set.EqOn f g (Dom f) :=
  forall_congr' fun _ ↦ Part.le_iff_not_dom_or_eq.trans imp_iff_not_or.symm

theorem eq_of_le_of_dom_subset (h : f ≤ g) (hdom : Dom g ⊆ Dom f) : f = g :=
  funext fun a ↦ Part.eq_of_le (h a) fun ha ↦ hdom ha

@[simp] theorem dom_update_some [DecidableEq α] (f : α → Part β) (a : α) (b : β) :
    Dom (Function.update f a (Part.some b)) = insert a (Dom f) := by
  ext c
  obtain rfl | hc := eq_or_ne c a <;> simp [*]

end PFun
