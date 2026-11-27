module

public import Linglib.Semantics.Aspect.AspectualClass
public import Linglib.Semantics.Mereology.Relation

/-!
# Incremental relations

Telicity originates in the thematic relation. A relation is strictly incremental when the parts of
the object and of the event correspond one to one, as for the object of *eat*, and incremental when
it is the closure of such a relation under sums, which admits the backups of *read the article*; a
strictly incremental relation that is summative [relates each object to one
event](##Aspect.SINC.gue_of_sum). The reference properties of the object carry over to the verb
phrase: [cumulativity](##Aspect.vp_cum) along a summative relation, [quantization](##Aspect.vp_qua)
along a relation with unique participants that maps to subobjects, and
[divisiveness](##Aspect.mo_iff_forall_div_vp) along exactly the relations that map to objects. For a
relation with unique participants that maps to objects the first two conditions are exact as well:
it is [summative](##Aspect.sum_iff_forall_cum_vp) iff cumulativity carries over from every object
predicate, and it [maps to subobjects](##Aspect.mso_iff_forall_qua_vp) iff quantization does. A
thematic function that preserves sums is such a relation, so *drink milk* [is
cumulative](##Aspect.vp_cum_graph), and an injective one maps to subobjects, so *drink two liters of
milk* [is quantized](##Aspect.vp_qua_graph).

## References

* [krifka-1989], [krifka-1998], [champollion-krifka-2016]
-/

@[expose] public section

namespace Aspect

open Mereology
open scoped SetRel

variable {α β : Type*}

/-! ### Incremental relations -/

section Incremental

/-- A relation is strictly incremental when a part of a related object is related to exactly one
part of the event and conversely, and some related pair has related proper parts, so the
relation is not confined to atoms. -/
structure SINC [PartialOrder α] [PartialOrder β] (θ : SetRel α β) : Prop where
  ue : UE θ
  uo : UO θ
  /-- Some related pair has related proper parts. -/
  extended : ∃ (x y : α) (e e' : β), y < x ∧ e' < e ∧ x ~[θ] e ∧ y ~[θ] e'

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {θ : SetRel α β}

theorem SINC.mse (h : SINC θ) : MSE θ := h.ue.mse_of_uo h.uo

theorem SINC.mso (h : SINC θ) : MSO θ := h.uo.mso_of_ue h.ue

theorem SINC.me (h : SINC θ) : ME θ := h.ue.me

theorem SINC.mo (h : SINC θ) : MO θ := h.uo.mo

end PartialOrder

variable [SemilatticeSup α] [SemilatticeSup β] {θ : SetRel α β}

theorem SINC.up_of_sum (h : SINC θ) (hs : SUM θ) : UP θ := h.uo.up_of_sum hs

/-- A summative strictly incremental relation relates each object to one event, so strict
incrementality and summativity are compatible only for relations like that of *eat*, not that of
*read* ([krifka-1998], after (51)). -/
theorem SINC.gue_of_sum (h : SINC θ) (hs : SUM θ) : GUE θ := h.ue.gue_of_sum hs

/-- A relation is incremental when it is the closure of some strictly incremental relation under
sums. -/
def INC (θ : SetRel α β) : Prop := ∃ θ', SINC θ' ∧ θ = supClosure θ'

/-- A summative strictly incremental relation is incremental, being its own closure. -/
theorem SINC.inc_of_sum (h : SINC θ) (hs : SUM θ) : INC θ :=
  ⟨θ, h, hs.supClosure_eq.symm⟩

/-- An incremental relation is summative, being a closure under sums. -/
theorem INC.sum (h : INC θ) : SUM θ :=
  let ⟨_, _, hθ⟩ := h
  hθ ▸ supClosed_supClosure

/-- The property of a thematic relation that an incrementality class names. A verb is classed
by the strongest that its theme relation has. -/
def Incrementality.Holds : Incrementality → SetRel α β → Prop
  | .strict, θ => SINC θ
  | .incremental, θ => INC θ
  | .cumulative, θ => SUM θ

theorem Incrementality.Holds.cumulative (h : Incrementality.incremental.Holds θ) :
    Incrementality.cumulative.Holds θ :=
  INC.sum h

/-- A summative relation of the strict class is of the incremental class. -/
theorem Incrementality.Holds.incremental (h : Incrementality.strict.Holds θ) (hs : SUM θ) :
    Incrementality.incremental.Holds θ :=
  SINC.inc_of_sum h hs

end Incremental

/-! ### The verb phrase -/

section VP

/-- The verb phrase of a relation and a region of objects is the region of events with some object
in it, the image of the region under the relation. -/
abbrev VP (θ : SetRel α β) (OBJ : Set α) : Set β := θ.image OBJ

theorem vp_eq (θ : SetRel α β) (y : α) : VP θ {y} = {e | y ~[θ] e} :=
  Set.ext fun _ ↦ ⟨fun ⟨_, h, hθ⟩ ↦ h ▸ hθ, fun h ↦ ⟨y, rfl, h⟩⟩

theorem vp_graph (f : β → α) (OBJ : Set α) : VP (Function.graph f).inv OBJ = f ⁻¹' OBJ :=
  Set.ext fun e ↦
    ⟨fun ⟨_, h, he⟩ ↦ show f e ∈ OBJ from (he : f e = _) ▸ h, fun h ↦ ⟨_, h, rfl⟩⟩

variable {θ : SetRel α β} {OBJ : Set α}

section Preorder

variable [Preorder α] [Preorder β]

/-- A relation maps to objects iff it carries divisive reference from the object to the verb
phrase. -/
theorem mo_iff_forall_div_vp : MO θ ↔ ∀ OBJ : Set α, DIV OBJ → DIV (VP θ OBJ) :=
  mo_iff_forall_isLowerSet

theorem vp_div (hm : MO θ) (hObj : DIV OBJ) : DIV (VP θ OBJ) := mo_iff_forall_div_vp.1 hm OBJ hObj

end Preorder

/-- Uniqueness of participants and mapping to subobjects carry quantization from the object
to the verb phrase, since the object of a proper subevent is a proper part of the object. -/
theorem vp_qua [PartialOrder α] [PartialOrder β] (hU : UP θ) (hm : MSO θ) (hObj : QUA OBJ) :
    QUA (VP θ OBJ) :=
  qua_of_forall fun _ _ ⟨_, hy, hθ⟩ hlt ⟨_, hz, hθz⟩ ↦
    let ⟨_, hlt', hθ'⟩ := hm hθ hlt
    hObj (hU.eq hθz (SetRel.mem_inv.1 hθ') ▸ hz) hy hlt'.ne hlt'.le

/-- Quantization carries over to the verb phrase from every object predicate iff the objects of
properly nested events are properly nested, in either direction. -/
theorem forall_qua_vp_iff [PartialOrder α] [PartialOrder β] :
    (∀ OBJ : Set α, QUA OBJ → QUA (VP θ OBJ)) ↔
      ∀ ⦃x y e e'⦄, x ~[θ] e → y ~[θ] e' → e' < e → x < y ∨ y < x := by
  refine ⟨fun h x y _ _ hx hy hlt ↦ by_contra fun hn ↦ ?_, fun h OBJ hO e' ⟨y, hy, hθy⟩ e
    ⟨x, hx, hθx⟩ hne hle ↦ ?_⟩
  · have hO : QUA ({x, y} : Set α) := by
      rintro a (rfl | rfl) b (rfl | rfl) hab hle
      · exact hab rfl
      · exact hn (.inl (lt_of_le_of_ne hle hab))
      · exact hn (.inr (lt_of_le_of_ne hle hab))
      · exact hab rfl
    exact h _ hO ⟨y, .inr rfl, hy⟩ ⟨x, .inl rfl, hx⟩ hlt.ne hlt.le
  · rcases h hθx hθy (lt_of_le_of_ne hle hne) with hxy | hyx
    · exact hO hx hy hxy.ne hxy.le
    · exact hO hy hx hyx.ne hyx.le

/-- For a relation with unique participants that maps to objects, mapping to subobjects is
exactly what carries quantization from every object predicate to the verb phrase. -/
theorem mso_iff_forall_qua_vp [PartialOrder α] [PartialOrder β] (hU : UP θ) (hm : MO θ) :
    MSO θ ↔ ∀ OBJ : Set α, QUA OBJ → QUA (VP θ OBJ) :=
  ⟨fun h _ hO ↦ vp_qua hU h hO, fun h _ _ hxe _ hlt ↦
    let ⟨y, hy, hθy⟩ := hm hxe hlt.le
    ⟨y, (forall_qua_vp_iff.1 h hxe (SetRel.mem_inv.1 hθy) hlt).resolve_left hy.not_gt, hθy⟩⟩

variable [SemilatticeSup α] [SemilatticeSup β]

/-- A summative relation carries cumulativity from the object to the verb phrase. -/
theorem vp_cum (hθ : SUM θ) (hObj : CUM OBJ) : CUM (VP θ OBJ) := SupClosed.relImage hθ hObj

/-- For a relation with unique participants that maps to objects, summativity is exactly what
carries cumulativity from every object predicate to the verb phrase. -/
theorem sum_iff_forall_cum_vp (hU : UP θ) (hm : MO θ) :
    SUM θ ↔ ∀ OBJ : Set α, CUM OBJ → CUM (VP θ OBJ) := by
  refine ⟨fun h _ hO ↦ vp_cum h hO, fun h ⟨x, e⟩ hx ⟨y, e'⟩ hy ↦ ?_⟩
  obtain ⟨z, hz, hθz⟩ := h (supClosure {x, y}) supClosed_supClosure
    ⟨x, subset_supClosure (.inl rfl), hx⟩ ⟨y, subset_supClosure (.inr rfl), hy⟩
  have hle : z ≤ x ⊔ y := by
    have : x ⊔ y ∈ upperBounds (supClosure {x, y}) := by
      rw [upperBounds_supClosure]; rintro _ (rfl | rfl) <;> simp
    exact this hz
  obtain ⟨x', hx', hθx'⟩ := hm hθz (le_sup_left : e ≤ e ⊔ e')
  obtain ⟨y', hy', hθy'⟩ := hm hθz (le_sup_right : e' ≤ e ⊔ e')
  obtain rfl : x' = x := hU.eq (SetRel.mem_inv.1 hθx') hx
  obtain rfl : y' = y := hU.eq (SetRel.mem_inv.1 hθy') hy
  obtain rfl : z = x' ⊔ y' := le_antisymm hle (sup_le hx' hy')
  exact hθz

/-- Along a summative relation with unique participants, a verb phrase is cumulative only if the
object predicate holds of the sum of any two of its objects that the relation relates to
events. -/
theorem not_cum_vp (hs : SUM θ) (hU : UP θ) {x y : α} {e₁ e₂ : β} (hx : x ∈ OBJ) (hy : y ∈ OBJ)
    (hθ₁ : x ~[θ] e₁) (hθ₂ : y ~[θ] e₂) (hSum : x ⊔ y ∉ OBJ) : ¬ CUM (VP θ OBJ) := fun hCum ↦
  let ⟨_, hz, hθ⟩ := hCum ⟨x, hx, hθ₁⟩ ⟨y, hy, hθ₂⟩
  hSum (hU.eq hθ (hs.sup hθ₁ hθ₂) ▸ hz)

/-- A summative strictly incremental relation, as *eat* is ([krifka-1998]), carries quantization
from the object to the verb phrase, since summativity and unique objects give unique
participants. -/
theorem SINC.vp_qua (h : SINC θ) (hs : SUM θ) (hObj : QUA OBJ) : QUA (VP θ OBJ) :=
  Aspect.vp_qua (h.up_of_sum hs) h.mso hObj

/-- A cumulative object predicate along a sum homomorphism gives a cumulative verb phrase, so
*drink milk* is cumulative ([champollion-krifka-2016]). -/
theorem vp_cum_graph {F : Type*} [FunLike F β α] [SupHomClass F β α] (f : F) (hObj : CUM OBJ) :
    CUM (VP (Function.graph f).inv OBJ) :=
  vp_cum (sum_graph f) hObj

/-- A quantized object predicate along an injective sum homomorphism gives a quantized verb
phrase, so *drink two liters of milk* is quantized ([champollion-krifka-2016]). The
homomorphism places the participant of a proper subevent below the whole participant, and
injectivity makes it a proper part. -/
theorem vp_qua_graph {F : Type*} [FunLike F β α] [SupHomClass F β α] (f : F)
    (hf : Function.Injective f) (hObj : QUA OBJ) : QUA (VP (Function.graph f).inv OBJ) :=
  vp_qua (up_graph f) ((mso_graph_iff f).2 ((OrderHomClass.mono f).strictMono_of_injective hf))
    hObj

end VP

end Aspect
