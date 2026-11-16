module

public import Linglib.Core.Order.SetRel
public import Linglib.Semantics.Mereology
public import Mathlib.Order.UpperLower.Fibration

/-!
# Mereology of relations

A thematic relation between objects and events is a relation `θ : SetRel α β` between two
mereologies, a set of pairs in the product part structure. Krifka's conditions on it are
part-structure properties of that set. Summativity is closure of `θ` under sums, uniqueness of
participants and of events are injectivity of the two projections on `θ`, and the mapping and
uniqueness conditions relate the parts of a related object to the parts of its event. Each
condition on the object side is the event-side condition of the converse relation `θ.inv`. A
relation maps to events exactly when
[the objects of a divisive set of events are divisive](##Mereology.me_iff_forall_isLowerSet), and
under both uniqueness conditions the parts of a related object and event
[correspond by an order isomorphism](##Mereology.UE.partOrderIso) whose graph is `θ`. Uniqueness
of objects makes mapping to subobjects the same as
[quantization of the events of each object](##Mereology.UO.mso_iff_forall_qua), and a summative
relation with unique events [gives each object one event](##Mereology.UE.gue_of_sum).

When the relation is the converse graph of a thematic function, as in [champollion-krifka-2016],
the conditions become properties of the function: summativity is preservation of sums, general
uniqueness of events is injectivity, mapping to subobjects is strict monotonicity, and mapping to
events is mathlib's `Relation.Fibration` for the part orders.

## References

* [krifka-1989], [krifka-1998], [champollion-krifka-2016]
-/

@[expose] public section

namespace Mereology

open Function
open scoped SetRel

variable {α β : Type*}

/-! ### Uniqueness of participants and events -/

section Unique

variable (θ : SetRel α β)

/-- A relation has unique participants if an event has at most one `θ`-participant. -/
abbrev UP : Prop := Set.InjOn Prod.snd θ

/-- A relation has general uniqueness of events if an object participates in at most one
`θ`-event. -/
abbrev GUE : Prop := Set.InjOn Prod.fst θ

variable {θ}

theorem up_iff : UP θ ↔ ∀ ⦃x y e⦄, x ~[θ] e → y ~[θ] e → x = y :=
  ⟨fun h _ _ _ h₁ h₂ ↦ congrArg Prod.fst (h h₁ h₂ rfl),
    fun h ⟨_, e⟩ h₁ ⟨_, e'⟩ h₂ he ↦ by
      obtain rfl : e = e' := he
      exact Prod.ext (h h₁ h₂) rfl⟩

theorem gue_iff : GUE θ ↔ ∀ ⦃x e e'⦄, x ~[θ] e → x ~[θ] e' → e = e' :=
  ⟨fun h _ _ _ h₁ h₂ ↦ congrArg Prod.snd (h h₁ h₂ rfl),
    fun h ⟨x, _⟩ h₁ ⟨y, _⟩ h₂ hx ↦ by
      obtain rfl : x = y := hx
      exact Prod.ext rfl (h h₁ h₂)⟩

alias ⟨UP.eq, _⟩ := up_iff

alias ⟨GUE.eq, _⟩ := gue_iff

theorem UP.inv (h : UP θ) : GUE θ.inv := gue_iff.2 fun _ _ _ h₁ h₂ ↦ h.eq h₁ h₂

theorem GUE.inv (h : GUE θ) : UP θ.inv := up_iff.2 fun _ _ _ h₁ h₂ ↦ h.eq h₁ h₂

end Unique

/-! ### Summativity -/

section Sum

variable [SemilatticeSup α] [SemilatticeSup β]

/-- A relation is summative ([krifka-1989]), or cumulative in the sense of [krifka-1998], if
related pairs sum to related pairs. -/
abbrev SUM (θ : SetRel α β) : Prop := SupClosed θ

variable {θ : SetRel α β}

theorem SUM.sup (h : SUM θ) {x y : α} {e e' : β} (h₁ : x ~[θ] e) (h₂ : y ~[θ] e') :
    (x ⊔ y) ~[θ] (e ⊔ e') :=
  h h₁ h₂

theorem SUM.inv (h : SUM θ) : SUM θ.inv := SupClosed.relInv h

end Sum

/-! ### Mapping between parts -/

section Preorder

variable [Preorder α] [Preorder β] (θ : SetRel α β)

/-- A relation maps to events if a part of a related object is related to a part of the
event. -/
def ME : Prop := ∀ ⦃x e⦄, x ~[θ] e → ∀ ⦃y⦄, y ≤ x → ∃ e' ≤ e, y ~[θ] e'

/-- A relation maps to subevents if a proper part of a related object is related to a proper
part of the event. -/
def MSE : Prop := ∀ ⦃x e⦄, x ~[θ] e → ∀ ⦃y⦄, y < x → ∃ e' < e, y ~[θ] e'

/-- A relation has unique events if a part of a related object is related to exactly one
part of the event. -/
def UE : Prop := ∀ ⦃x e⦄, x ~[θ] e → ∀ ⦃y⦄, y ≤ x → ∃! e', e' ≤ e ∧ y ~[θ] e'

/-- A relation maps to objects if a part of a related event is related to a part of the
object, the converse of `ME`. -/
abbrev MO : Prop := ME θ.inv

/-- A relation maps to subobjects if a proper part of a related event is related to a proper
part of the object, the converse of `MSE`. -/
abbrev MSO : Prop := MSE θ.inv

/-- A relation has unique objects if a part of a related event is related to exactly one
part of the object, the converse of `UE`. -/
abbrev UO : Prop := UE θ.inv

variable {θ}

theorem UE.me (h : UE θ) : ME θ := fun _ _ hxe _ hle ↦ (h hxe hle).exists

theorem UO.mo (h : UO θ) : MO θ := UE.me h

/-- With mapping to objects, uniqueness of participants gives uniqueness of objects. -/
theorem UP.uo_of_mo (hU : UP θ) (hm : MO θ) : UO θ := fun _ _ hxe _ hle ↦
  let ⟨y, hy, hθ⟩ := hm hxe hle
  ⟨y, ⟨hy, hθ⟩, fun _ ⟨_, hz⟩ ↦ hU.eq hz hθ⟩

theorem GUE.ue_of_me (hG : GUE θ) (hm : ME θ) : UE θ := UP.uo_of_mo hG.inv hm

/-- A relation maps to events iff the objects related to a lower set of events form a lower set,
as `Relation.fibration_iff_isLowerSet_image` characterizes a fibration. -/
theorem me_iff_forall_isLowerSet :
    ME θ ↔ ∀ s : Set β, IsLowerSet s → IsLowerSet (θ.preimage s) :=
  ⟨fun h _ hs _ _ hle ⟨_, he, hθ⟩ ↦ let ⟨e', he', hθ'⟩ := h hθ hle; ⟨e', hs he' he, hθ'⟩,
    fun h _ e hθ _ hle ↦ h _ (isLowerSet_Iic e) hle ⟨e, le_rfl, hθ⟩⟩

/-- A relation maps to objects iff the events related to a lower set of objects form a lower
set. -/
theorem mo_iff_forall_isLowerSet :
    MO θ ↔ ∀ s : Set α, IsLowerSet s → IsLowerSet (θ.image s) :=
  me_iff_forall_isLowerSet

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {θ : SetRel α β}

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

/-- Under uniqueness of objects, a relation maps to subobjects iff the events of each object form
a quantized predicate: it takes the whole event to relate the object, not a part of it
([krifka-1998], after (50)). -/
theorem UO.mso_iff_forall_qua (hO : UO θ) : MSO θ ↔ ∀ x, QUA (x ~[θ] ·) :=
  ⟨fun hm _ ↦ qua_of_forall fun _ _ he hlt he' ↦
      let ⟨_, hy, hθ⟩ := hm he hlt
      hy.ne ((hO he hlt.le).unique ⟨hy.le, hθ⟩ ⟨le_rfl, he'⟩),
    fun hq _ x hxe e' hlt ↦
      let ⟨y, hy, hθ⟩ := (hO hxe hlt.le).exists
      ⟨y, lt_of_le_of_ne hy fun h ↦ hq x (h ▸ hθ : x ~[θ] e') hxe hlt.ne hlt.le, hθ⟩⟩

theorem UO.qua_of_mso (hO : UO θ) (hm : MSO θ) (x : α) : QUA (x ~[θ] ·) :=
  hO.mso_iff_forall_qua.mp hm x

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β] {θ : SetRel α β}

/-- A summative relation with unique objects has unique participants: two participants of an event
sum to a participant of it, and each is a part of the sum related to the whole event. -/
theorem UO.up_of_sum (hO : UO θ) (hS : SUM θ) : UP θ := up_iff.2 fun _ _ _ ha hb ↦
  (hO (hS.sup ha hb) le_sup_left).unique ⟨le_sup_left, ha⟩ ⟨le_sup_right, hb⟩

/-- A summative relation with unique events has general uniqueness of events: two events of an
object sum to an event of it, as two readings of a novel do, and each is a part of the sum related
to the whole object ([krifka-1998], after (51)). -/
theorem UE.gue_of_sum (hE : UE θ) (hS : SUM θ) : GUE θ :=
  (UO.up_of_sum (θ := θ.inv) hE hS.inv).inv

end SemilatticeSup

/-! ### The correspondence between parts

Uniqueness of events and of objects make `θ`, between the parts of a related object and event, a
one-to-one mapping ([krifka-1998], after (50)). -/

section Part

variable [Preorder α] [Preorder β] {θ : SetRel α β} {x : α} {e : β}

/-- Under uniqueness of events, the part of a related event that a part of the object is related
to. -/
noncomputable def UE.part (hE : UE θ) (hxe : x ~[θ] e) (y : Set.Iic x) : Set.Iic e :=
  ⟨(hE hxe y.prop).exists.choose, (hE hxe y.prop).exists.choose_spec.left⟩

theorem UE.rel_part (hE : UE θ) (hxe : x ~[θ] e) (y : Set.Iic x) :
    (y : α) ~[θ] (hE.part hxe y : β) :=
  (hE hxe y.prop).exists.choose_spec.right

/-- Between the parts of a related object and event, `θ` is the graph of `UE.part`. -/
theorem UE.rel_iff_part_eq (hE : UE θ) (hxe : x ~[θ] e) {y : Set.Iic x} {e' : Set.Iic e} :
    (y : α) ~[θ] (e' : β) ↔ hE.part hxe y = e' :=
  ⟨fun h ↦ Subtype.ext
      ((hE hxe y.prop).unique ⟨(hE.part hxe y).prop, hE.rel_part hxe y⟩ ⟨e'.prop, h⟩),
    fun h ↦ h ▸ hE.rel_part hxe y⟩

theorem UE.part_mono (hE : UE θ) (hxe : x ~[θ] e) : Monotone (hE.part hxe) := fun _ y₂ hle ↦
  let ⟨e₀, ⟨he₀, hθ⟩, _⟩ := hE (hE.rel_part hxe y₂) hle
  ((hE.rel_iff_part_eq hxe (e' := ⟨e₀, he₀.trans (hE.part hxe y₂).prop⟩)).mp hθ).le.trans he₀

/-- Under uniqueness of events and of objects, the parts of a related object and event are
order-isomorphic along `θ`. -/
noncomputable def UE.partOrderIso (hE : UE θ) (hO : UO θ) (hxe : x ~[θ] e) :
    Set.Iic x ≃o Set.Iic e :=
  Equiv.toOrderIso
    ⟨hE.part hxe, hO.part hxe, fun y ↦ (hO.rel_iff_part_eq hxe).mp (hE.rel_part hxe y),
      fun e' ↦ (hE.rel_iff_part_eq hxe).mp (hO.rel_part hxe e')⟩
    (hE.part_mono hxe) (hO.part_mono hxe)

@[simp]
theorem UE.partOrderIso_apply (hE : UE θ) (hO : UO θ) (hxe : x ~[θ] e) (y : Set.Iic x) :
    hE.partOrderIso hO hxe y = hE.part hxe y := rfl

@[simp]
theorem UE.partOrderIso_symm (hE : UE θ) (hO : UO θ) (hxe : x ~[θ] e) :
    (hE.partOrderIso hO hxe).symm = UE.partOrderIso (θ := θ.inv) hO hE hxe := rfl

end Part

/-! ### Thematic functions

A thematic function `f : β → α` sends an event to its participant, and the converse of its graph
is the corresponding thematic relation. [champollion-krifka-2016] require of such a function
cumulativity (13.23), that it preserve sums, and distinctiveness (13.24), that distinct events
have distinct participants. -/

section Graph

variable (f : β → α)

theorem up_graph : UP (graph f).inv := GUE.inv (θ := graph f) (SetRel.injOn_fst_graph f)

/-- The converse graph of a function has general uniqueness of events iff the function is
injective, the distinctiveness (13.24) of [champollion-krifka-2016]. -/
theorem gue_graph_iff : GUE (graph f).inv ↔ Injective f :=
  ⟨fun h ↦ SetRel.injOn_snd_graph_iff.1 (GUE.inv h),
    fun h ↦ UP.inv (θ := graph f) (SetRel.injOn_snd_graph_iff.2 h)⟩

variable [Preorder α] [Preorder β]

/-- The converse graph of a function maps to events iff the function is a fibration of the part
orders. -/
theorem me_graph_iff : ME (graph f).inv ↔ Relation.Fibration (· ≤ ·) (· ≤ ·) f :=
  ⟨fun h a _ hle ↦ h (show (f a, a) ∈ (graph f).inv from rfl) hle,
    fun h _ _ hxe _ hle ↦ h (hle.trans_eq hxe.symm)⟩

theorem mse_graph_iff : MSE (graph f).inv ↔ Relation.Fibration (· < ·) (· < ·) f :=
  ⟨fun h a _ hlt ↦ h (show (f a, a) ∈ (graph f).inv from rfl) hlt,
    fun h _ _ hxe _ hlt ↦ h (hlt.trans_eq hxe.symm)⟩

theorem mo_graph_iff : MO (graph f).inv ↔ Monotone f :=
  ⟨fun h _ b hle ↦
      let ⟨_, hy, hy'⟩ := h (show (b, f b) ∈ graph f from rfl) hle
      hy'.trans_le hy,
    fun h _ _ hxe _ hle ↦ ⟨_, (h hle).trans_eq hxe, rfl⟩⟩

theorem uo_graph_iff : UO (graph f).inv ↔ Monotone f :=
  ⟨fun h _ b hle ↦
      let ⟨_, ⟨hy, hy'⟩, _⟩ := h (show (b, f b) ∈ graph f from rfl) hle
      hy'.trans_le hy,
    fun h _ _ hxe _ hle ↦ ⟨_, ⟨(h hle).trans_eq hxe, rfl⟩, fun _ ⟨_, hz⟩ ↦ hz.symm⟩⟩

/-- The converse graph of a function maps to subobjects iff the function is strictly monotone. -/
theorem mso_graph_iff : MSO (graph f).inv ↔ StrictMono f :=
  ⟨fun h _ b hlt ↦
      let ⟨_, hy, hy'⟩ := h (show (b, f b) ∈ graph f from rfl) hlt
      hy'.trans_lt hy,
    fun h _ _ hxe _ hlt ↦ ⟨_, (h hlt).trans_eq hxe, rfl⟩⟩

end Graph

section GraphSum

variable [SemilatticeSup α] [SemilatticeSup β]

/-- The converse graph of a function is summative iff the function preserves sums, the
cumulativity (13.23) of [champollion-krifka-2016]. -/
theorem sum_graph_iff (f : β → α) : SUM (graph f).inv ↔ ∀ e e', f (e ⊔ e') = f e ⊔ f e' :=
  SetRel.supClosed_inv.trans SetRel.supClosed_graph_iff

theorem sum_graph {F : Type*} [FunLike F β α] [SupHomClass F β α] (f : F) : SUM (graph f).inv :=
  (SetRel.supClosed_graph f).relInv

end GraphSum

end Mereology
