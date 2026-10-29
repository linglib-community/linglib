module

public import Mathlib.Logic.Relator
public import Linglib.Semantics.Mereology

/-!
# Mereology of relations

Krifka states his conditions on the thematic relation between an object and an event as
part-structure properties of a relation `θ : α → β → Prop` between two mereologies. Uniqueness of
participants and of events are mathlib's `Relator.LeftUnique` and `Relator.RightUnique`,
summativity is cumulativity of the graph of `θ` in the product order, and the mapping and
uniqueness conditions relate the parts of a related object to the parts of its event. Each
condition on the event side is the object-side condition of the converse relation `flip θ`. When
the relation is the graph of a thematic function, as in [champollion-krifka-2016], the
conditions become properties of the function: summativity is preservation of sums, general
uniqueness of events is injectivity, and mapping to subobjects is strict monotonicity.

## Main definitions

* `UP`, `GUE`: uniqueness of participants and general uniqueness of events.
* `SUM`: summativity, the cumulativity of a relation.
* `ME`, `MSE`, `UE`: mapping to events, mapping to subevents, and uniqueness of events.
* `MO`, `MSO`, `UO`: mapping to objects, mapping to subobjects, and uniqueness of objects.

## Main results

* `UP.uo_of_mo`, `UE.mse_of_uo`: uniqueness of participants gives uniqueness of objects, and the
  two uniqueness conditions give the strict mappings.
* `UO.up_of_sum`: conversely, a summative relation with unique objects has unique participants.
* `UE.exists_orderIso_of_uo`: under both uniqueness conditions a related object and event have
  order-isomorphic parts.
* `UO.qua_of_mso`: the events of a fixed object form a quantized predicate.
* `gue_graph_iff`, `mso_graph_iff`, `sum_graph_iff`: the conditions on the graph of a thematic
  function.

## References

* [krifka-1989], [krifka-1998], [champollion-krifka-2016]
-/

@[expose] public section

namespace Mereology

variable {α β : Type*}

/-! ### Uniqueness of participants and events -/

section Unique

variable (θ : α → β → Prop)

/-- A relation has unique participants if an event has at most one `θ`-participant. -/
abbrev UP : Prop := Relator.LeftUnique θ

/-- A relation has general uniqueness of events if an object participates in at most one
`θ`-event. -/
abbrev GUE : Prop := Relator.RightUnique θ

variable {θ}

theorem UP.flip (h : UP θ) : GUE (flip θ) := Relator.LeftUnique.flip h

theorem GUE.flip (h : GUE θ) : UP (flip θ) := fun _ _ _ h₁ h₂ ↦ h h₁ h₂

end Unique

/-! ### Summativity -/

section Sum

variable [SemilatticeSup α] [SemilatticeSup β]

/-- A relation is summative ([krifka-1989]), or cumulative in the sense of [krifka-1998], if
related pairs sum to related pairs. -/
def SUM (θ : α → β → Prop) : Prop := ∀ ⦃x e⦄, θ x e → ∀ ⦃y e'⦄, θ y e' → θ (x ⊔ y) (e ⊔ e')

variable {θ : α → β → Prop}

theorem sum_iff_cum_uncurry : SUM θ ↔ CUM (Function.uncurry θ) :=
  ⟨fun h _ hp _ hq ↦ h hp hq, fun h _ _ hx _ _ hy ↦ h (a := (_, _)) (b := (_, _)) hx hy⟩

theorem SUM.flip (h : SUM θ) : SUM (flip θ) := fun _ _ h₁ _ _ h₂ ↦ h h₁ h₂

end Sum

/-! ### Mapping between parts -/

section Preorder

variable [Preorder α] [Preorder β] (θ : α → β → Prop)

/-- A relation maps to events if a part of a related object is related to a part of the
event. -/
def ME : Prop := ∀ ⦃x e⦄, θ x e → ∀ ⦃y⦄, y ≤ x → ∃ e' ≤ e, θ y e'

/-- A relation maps to subevents if a proper part of a related object is related to a proper
part of the event. -/
def MSE : Prop := ∀ ⦃x e⦄, θ x e → ∀ ⦃y⦄, y < x → ∃ e' < e, θ y e'

/-- A relation has unique events if a part of a related object is related to exactly one
part of the event. -/
def UE : Prop := ∀ ⦃x e⦄, θ x e → ∀ ⦃y⦄, y ≤ x → ∃! e', e' ≤ e ∧ θ y e'

/-- A relation maps to objects if a part of a related event is related to a part of the
object, the converse of `ME`. -/
abbrev MO : Prop := ME (flip θ)

/-- A relation maps to subobjects if a proper part of a related event is related to a proper
part of the object, the converse of `MSE`. -/
abbrev MSO : Prop := MSE (flip θ)

/-- A relation has unique objects if a part of a related event is related to exactly one
part of the object, the converse of `UE`. -/
abbrev UO : Prop := UE (flip θ)

variable {θ}

theorem UE.me (h : UE θ) : ME θ := fun _ _ hxe _ hle ↦ (h hxe hle).exists

theorem UO.mo (h : UO θ) : MO θ := UE.me h

/-- With mapping to objects, uniqueness of participants gives uniqueness of objects. -/
theorem UP.uo_of_mo (hU : UP θ) (hm : MO θ) : UO θ := fun _ _ hxe _ hle ↦
  let ⟨y, hy, hθ⟩ := hm hxe hle
  ⟨y, ⟨hy, hθ⟩, fun _ hz ↦ hU hz.2 hθ⟩

theorem GUE.ue_of_me (hG : GUE θ) (hm : ME θ) : UE θ := UP.uo_of_mo hG.flip hm

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {θ : α → β → Prop}

theorem MSE.me (h : MSE θ) : ME θ := fun _ _ hxe _ hle ↦
  (eq_or_lt_of_le hle).elim (fun heq ↦ ⟨_, le_rfl, heq ▸ hxe⟩)
    (fun hlt ↦ let ⟨e', hlt', hθ⟩ := h hxe hlt; ⟨e', hlt'.le, hθ⟩)

theorem MSO.mo (h : MSO θ) : MO θ := MSE.me h

/-- Uniqueness of events and of objects give mapping to subevents. The part of the event
related to a proper part of the object is proper, since the whole event's unique related part
of the object is the object itself. -/
theorem UE.mse_of_uo (hE : UE θ) (hO : UO θ) : MSE θ := fun _ _ hxe _ hyx ↦
  let ⟨e', ⟨he', hθ⟩, _⟩ := hE hxe hyx.le
  ⟨e', lt_of_le_of_ne he' fun h ↦ hyx.ne ((hO hxe le_rfl).unique ⟨hyx.le, h ▸ hθ⟩ ⟨le_rfl, hxe⟩),
    hθ⟩

theorem UO.mso_of_ue (hO : UO θ) (hE : UE θ) : MSO θ := UE.mse_of_uo hO hE

/-- With unique objects and mapping to subobjects, the events of a fixed object form a quantized
predicate (cf. [krifka-1998] after (50)). -/
theorem UO.qua_of_mso (hO : UO θ) (hm : MSO θ) (x : α) : QUA (θ x) :=
  qua_of_forall fun _ _ he hlt he' ↦
    let ⟨_, hy, hθ⟩ := hm he hlt
    hy.ne ((hO he hlt.le).unique ⟨hy.le, hθ⟩ ⟨le_rfl, he'⟩)

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β] {θ : α → β → Prop}

/-- A summative relation with unique objects has unique participants: two participants of an event
sum to a participant of it, and each is a part of the sum related to the whole event. -/
theorem UO.up_of_sum (hO : UO θ) (hS : SUM θ) : UP θ := fun _ _ _ ha hb ↦
  (hO (hS ha hb) le_sup_left).unique ⟨le_sup_left, ha⟩ ⟨le_sup_right, hb⟩

end SemilatticeSup

/-! ### The correspondence between parts -/

section OrderIso

variable [Preorder α] [Preorder β] {θ : α → β → Prop} {x : α} {e : β}

private theorem monotone_of_ue (hE : UE θ) {f : Set.Iic x → β}
    (hf : ∀ y, (f y ≤ e ∧ θ y (f y)) ∧ ∀ e', e' ≤ e ∧ θ y e' → e' = f y) : Monotone f :=
  fun y₁ y₂ hle ↦
    let ⟨e₀, ⟨he₀, hθ⟩, _⟩ := hE (hf y₂).1.2 hle
    (hf y₁).2 e₀ ⟨he₀.trans (hf y₂).1.1, hθ⟩ ▸ he₀

/-- Under uniqueness of events and of objects, `θ` restricts, between the parts of a related
object and event, to the graph of an order isomorphism. -/
theorem UE.exists_orderIso_of_uo (hE : UE θ) (hO : UO θ) (hxe : θ x e) :
    ∃ f : Set.Iic x ≃o Set.Iic e, ∀ (y : Set.Iic x) (e' : Set.Iic e), θ y e' ↔ f y = e' := by
  choose f hf using fun y : Set.Iic x ↦ hE hxe y.2
  choose g hg using fun e' : Set.Iic e ↦ hO hxe e'.2
  let F : Set.Iic x ≃ Set.Iic e :=
    { toFun := fun y ↦ ⟨f y, (hf y).1.1⟩
      invFun := fun e' ↦ ⟨g e', (hg e').1.1⟩
      left_inv := fun y ↦ Subtype.ext ((hg ⟨f y, (hf y).1.1⟩).2 y ⟨y.2, (hf y).1.2⟩).symm
      right_inv := fun e' ↦ Subtype.ext ((hf ⟨g e', (hg e').1.1⟩).2 e' ⟨e'.2, (hg e').1.2⟩).symm }
  refine ⟨F.toOrderIso (fun _ _ h ↦ monotone_of_ue hE hf h) (fun _ _ h ↦ monotone_of_ue hO hg h),
    fun y e' ↦ ⟨fun h ↦ Subtype.ext ((hf y).2 e' ⟨e'.2, h⟩).symm, fun h ↦ h ▸ (hf y).1.2⟩⟩

end OrderIso

/-! ### Thematic functions

A thematic function `f : β → α` sends an event to its participant, and its graph `(· = f ·)` is
the corresponding thematic relation. [champollion-krifka-2016] require of such a function
cumulativity (13.23), that it preserve sums, and distinctiveness (13.24), that distinct events
have distinct participants. -/

section Graph

variable (f : β → α)

theorem up_graph : UP (· = f ·) := fun _ _ _ hx hy ↦ hx.trans hy.symm

/-- The graph of a function has general uniqueness of events iff the function is injective, the
distinctiveness (13.24) of [champollion-krifka-2016]. -/
theorem gue_graph_iff : GUE (· = f ·) ↔ Function.Injective f :=
  ⟨fun h _ _ heq ↦ h rfl heq, fun h _ _ _ h₁ h₂ ↦ h (h₁.symm.trans h₂)⟩

variable [Preorder α] [Preorder β]

theorem mo_graph_iff : MO (· = f ·) ↔ Monotone f :=
  ⟨fun h _ _ hle ↦ let ⟨_, hy, hy'⟩ := h rfl hle; hy' ▸ hy,
    fun h _ _ hxe _ hle ↦ ⟨_, hxe ▸ h hle, rfl⟩⟩

theorem uo_graph_iff : UO (· = f ·) ↔ Monotone f :=
  ⟨fun h _ _ hle ↦ let ⟨_, ⟨hy, hy'⟩, _⟩ := h rfl hle; hy' ▸ hy,
    fun h _ _ hxe _ hle ↦ ⟨_, ⟨hxe ▸ h hle, rfl⟩, fun _ hz ↦ hz.2⟩⟩

/-- The graph of a function maps to subobjects iff the function is strictly monotone. -/
theorem mso_graph_iff : MSO (· = f ·) ↔ StrictMono f :=
  ⟨fun h _ _ hlt ↦ let ⟨_, hy, hy'⟩ := h rfl hlt; hy' ▸ hy,
    fun h _ _ hxe _ hlt ↦ ⟨_, hxe ▸ h hlt, rfl⟩⟩

end Graph

section GraphSum

variable [SemilatticeSup α] [SemilatticeSup β]

/-- The graph of a function is summative iff the function preserves sums, the cumulativity
(13.23) of [champollion-krifka-2016]. -/
theorem sum_graph_iff (f : β → α) : SUM (· = f ·) ↔ ∀ e e', f (e ⊔ e') = f e ⊔ f e' :=
  ⟨fun h e e' ↦ (h (x := f e) rfl (y := f e') rfl).symm,
    fun h _ _ hx _ _ hy ↦ (congr_arg₂ (· ⊔ ·) hx hy).trans (h _ _).symm⟩

theorem sum_graph {F : Type*} [FunLike F β α] [SupHomClass F β α] (f : F) : SUM (· = f ·) :=
  (sum_graph_iff f).2 (map_sup f)

end GraphSum

end Mereology
