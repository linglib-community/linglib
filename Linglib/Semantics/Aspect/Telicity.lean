module

public import Linglib.Core.Order.Minimals
public import Linglib.Semantics.Aspect.Defs
public import Linglib.Semantics.Events.Precedence
public import Linglib.Semantics.Mereology.Relation
public import Mathlib.Order.Comparable

/-!
# Telicity

Krifka treats telicity as a property of event predicates: a predicate is telic when every part
of one of its events that it also applies to is both an initial and a final part of that event.
[Quantized predicates are telic](##Aspect.isTelic_of_qua) though not conversely, since a
predicate that fixes the run time, *from three to four*,
[is telic](##Aspect.isTelic_runTime_eq) without being quantized, and
[cumulative](##Aspect.not_isTelic_of_cum) or [divisive](##Aspect.not_isTelic_of_div) predicates
that apply to events with successive parts are not. Telicity originates in the thematic relation. A
relation is strictly incremental when the parts of the object and of the event correspond one to
one, as for the object of *eat*, and incremental when it is the closure of such a relation under
sums, which admits the backups of *read the article*; a strictly incremental relation that is
summative [relates each object to one event](##Aspect.SINC.gue_of_sum). The reference properties
of the object carry over to the verb phrase: [cumulativity](##Aspect.vp_cum) along a summative
relation, [quantization](##Aspect.vp_qua) along a relation with unique participants that maps to
subobjects, and [divisiveness](##Aspect.mo_iff_forall_div_vp) along exactly the relations that
map to objects. For a thematic function these are a sum homomorphism and an injective one, so
*drink milk* [is cumulative](##Aspect.vp_cum_graph) and *drink two liters of milk*
[quantized](##Aspect.vp_qua_graph).

## Implementation notes

Temporal precedence is a parameter of the telicity notions. The proofs use only that parts of an
event neither precede nor follow it, `NoPartPrecedes`, which follows from Krifka's axiom that
overlapping events do not precede each other (`noPartPrecedes_of_overlap`) and holds of any
temporal precedence on a part structure of events
(`IsTemporalPrecedence.noPartPrecedes`). A final part is an
initial part under the converse precedence, so results about final parts are transported, and
an initial part is a minimal part in the order of precedence, which is why precedence is a strict
order.

## References

* [krifka-1989], [krifka-1998], [champollion-krifka-2016]
-/

@[expose] public section

namespace Aspect

open Mereology

/-! ### Telicity by initial and final parts -/

section InitialFinal

variable {β : Type*}

section Telicity

variable [PartialOrder β] (precedes : β → β → Prop)

/-- Parts of an event neither precede nor follow it: events ordered by precedence are
incomparable by parthood. -/
def NoPartPrecedes : Prop := ∀ ⦃a b : β⦄, precedes a b → IncompRel (· ≤ ·) a b

variable {precedes}

theorem NoPartPrecedes.swap (h : NoPartPrecedes precedes) :
    NoPartPrecedes (Function.swap precedes) :=
  fun _ _ hp ↦ (h hp).symm

/-- Parts of an event neither precede nor follow it if overlapping events do not precede each
other ([krifka-1998] (35)) and no event is null. -/
theorem noPartPrecedes_of_overlap [NoBotOrder β] (h : ∀ a b, Overlap a b → ¬ precedes a b) :
    NoPartPrecedes precedes := fun a b hp ↦
  ⟨fun hle ↦ h a b (.of_le (not_isBot a) hle) hp,
    fun hle ↦ h a b (Overlap.of_le (not_isBot b) hle).symm hp⟩

variable (precedes) [IsStrictOrder β precedes]

/-- An initial part of an event is a part that no part of the event precedes: a minimal element
of the parts of the event in the order of precedence. -/
def IsInitialPart (e' e : β) : Prop :=
  e' ∈ (partialOrderOfSO precedes).toPreorder.minimals (Set.Iic e)

/-- A final part of an event is a part that no part of the event follows, an initial part under
the converse precedence. -/
abbrev IsFinalPart (e' e : β) : Prop := IsInitialPart (Function.swap precedes) e' e

/-- A predicate is telic when every `P`-part of a `P`-event is an initial and a final part of
it. -/
def IsTelic (P : β → Prop) : Prop :=
  ∀ ⦃e e'⦄, P e → P e' → e' ≤ e → IsInitialPart precedes e' e ∧ IsFinalPart precedes e' e

variable {precedes} {P : β → Prop} {e e' e'' : β}

theorem isInitialPart_iff :
    IsInitialPart precedes e' e ↔ e' ≤ e ∧ ∀ ⦃e''⦄, e'' ≤ e → ¬ precedes e'' e' :=
  Preorder.mem_minimals_iff.trans <| and_congr_right fun _ ↦
    ⟨fun h _ h'' hp ↦ (h h'' (.inr hp)).elim (fun heq ↦ irrefl_of precedes _ (heq ▸ hp))
        fun hp' ↦ irrefl_of precedes _ (_root_.trans hp hp'),
      fun h _ h'' hle ↦ hle.elim (fun heq ↦ .inl heq.symm) fun hp ↦ (h h'' hp).elim⟩

theorem IsInitialPart.le (h : IsInitialPart precedes e' e) : e' ≤ e := (isInitialPart_iff.mp h).left

theorem IsInitialPart.not_precedes (h : IsInitialPart precedes e' e) (h'' : e'' ≤ e) :
    ¬ precedes e'' e' := (isInitialPart_iff.mp h).right h''

theorem IsTelic.isInitialPart (h : IsTelic precedes P) (he : P e) (he' : P e') (hle : e' ≤ e) :
    IsInitialPart precedes e' e := (h he he' hle).left

theorem IsTelic.isFinalPart (h : IsTelic precedes P) (he : P e) (he' : P e') (hle : e' ≤ e) :
    IsFinalPart precedes e' e := (h he he' hle).right

/-- A predicate is telic iff a `P`-part of a `P`-event neither precedes nor follows any part of
that event. -/
theorem isTelic_iff :
    IsTelic precedes P ↔
      ∀ ⦃e e'⦄, P e → P e' → e' ≤ e → ∀ ⦃e''⦄, e'' ≤ e → IncompRel precedes e'' e' :=
  ⟨fun h _ _ he he' hle _ h'' ↦
      ⟨(h.isInitialPart he he' hle).not_precedes h'', (h.isFinalPart he he' hle).not_precedes h''⟩,
    fun h _ _ he he' hle ↦
      ⟨isInitialPart_iff.mpr ⟨hle, fun _ h'' ↦ (h he he' hle h'').left⟩,
        isInitialPart_iff.mpr ⟨hle, fun _ h'' ↦ (h he he' hle h'').right⟩⟩⟩

theorem isInitialPart_self (h : NoPartPrecedes precedes) (e : β) :
    IsInitialPart precedes e e :=
  isInitialPart_iff.mpr ⟨le_rfl, fun _ h' hp ↦ (h hp).not_le h'⟩

theorem isFinalPart_self (h : NoPartPrecedes precedes) (e : β) : IsFinalPart precedes e e :=
  isInitialPart_self h.swap e

theorem IsTelic.swap (h : IsTelic precedes P) : IsTelic (Function.swap precedes) P :=
  fun _ _ he he' hle ↦ ⟨h.isFinalPart he he' hle, h.isInitialPart he he' hle⟩

/-- Quantized predicates are telic. -/
theorem isTelic_of_qua (h : NoPartPrecedes precedes) (hP : QUA P) :
    IsTelic precedes P := fun e e' he he' hle ↦ by
  obtain rfl : e' = e := by_contra fun hne ↦ hP he' he hne hle
  exact ⟨isInitialPart_self h _, isFinalPart_self h _⟩

end Telicity

/-! ### Precedence by run times -/

section Precedence

open Event

/-- Parts of an event neither precede nor follow it. -/
theorem _root_.IsTemporalPrecedence.noPartPrecedes [SemilatticeSup β] (r : β → β → Prop)
    [IsTemporalPrecedence β r] : NoPartPrecedes r := fun a b hr ↦
  ⟨fun hab ↦ irrefl_of r a (IsTemporalPrecedence.mono_right hab hr),
    fun hba ↦ irrefl_of r b (IsTemporalPrecedence.mono_left hba hr)⟩

/-- Quantized predicates are telic under a temporal precedence on the part structure of
events. -/
theorem _root_.IsTemporalPrecedence.isTelic_of_qua [SemilatticeSup β] (r : β → β → Prop)
    [IsTemporalPrecedence β r] {P : β → Prop} (hP : QUA P) : IsTelic r P :=
  Aspect.isTelic_of_qua (IsTemporalPrecedence.noPartPrecedes r) hP

/-- A predicate that fixes the run time is telic: a part of an event runs within it, so it neither
precedes nor follows a part with the event's run time. -/
theorem isTelic_runTime_eq [PartialOrder β] {T : Type*} [LinearOrder T]
    [TemporalTrace β T] (hτ : Monotone (τ : β → NonemptyInterval T))
    (I : NonemptyInterval T) : IsTelic (Precedes : β → β → Prop) (τ · = I) := by
  refine isTelic_iff.mpr fun e e' he he' _ e'' h'' ↦ ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩ <;>
    have hτe : τ e' = τ e := he'.trans he.symm
  · change (τ e'').snd < (τ e').fst at hp
    rw [hτe] at hp
    exact hp.not_ge ((NonemptyInterval.le_def.1 (hτ h'')).1.trans (τ e'').fst_le_snd)
  · change (τ e').snd < (τ e'').fst at hp
    rw [hτe] at hp
    exact hp.not_ge ((τ e'').fst_le_snd.trans (NonemptyInterval.le_def.1 (hτ h'')).2)

end Precedence

/-- A cumulative predicate true of two events, a part of one following the other, is not
telic. -/
theorem not_isTelic_of_cum [SemilatticeSup β] {precedes : β → β → Prop}
    [IsStrictOrder β precedes] {P : β → Prop}
    (hP : CUM P) {e e' e'' : β} (he : P e) (he' : P e') (h'' : e'' ≤ e)
    (hp : precedes e' e'') : ¬ IsTelic precedes P :=
  fun hT ↦ (isTelic_iff.mp hT (hP he he') he' le_sup_right (h''.trans le_sup_left)).right hp

/-- A divisive predicate true of an event with a part preceding another part is not telic, as
the divisive reference of activities makes them atelic ([champollion-krifka-2016]). -/
theorem not_isTelic_of_div [PartialOrder β] {precedes : β → β → Prop}
    [IsStrictOrder β precedes] {P : β → Prop}
    (hP : DIV P) {e e' e'' : β} (he : P e) (h' : e' ≤ e) (h'' : e'' ≤ e)
    (hp : precedes e' e'') : ¬ IsTelic precedes P :=
  fun hT ↦ (isTelic_iff.mp hT he (hP h' he) h' h'').right hp

end InitialFinal

variable {α β : Type*}

/-! ### Incremental relations -/

section Incremental

/-- A relation is strictly incremental when a part of a related object is related to exactly one
part of the event and conversely, and some related pair has related proper parts, so the
relation is not confined to atoms. -/
structure SINC [PartialOrder α] [PartialOrder β] (θ : α → β → Prop) : Prop where
  ue : UE θ
  uo : UO θ
  /-- Some related pair has related proper parts. -/
  extended : ∃ (x y : α) (e e' : β), y < x ∧ e' < e ∧ θ x e ∧ θ y e'

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {θ : α → β → Prop}

theorem SINC.mse (h : SINC θ) : MSE θ := h.ue.mse_of_uo h.uo

theorem SINC.mso (h : SINC θ) : MSO θ := h.uo.mso_of_ue h.ue

theorem SINC.me (h : SINC θ) : ME θ := h.ue.me

theorem SINC.mo (h : SINC θ) : MO θ := h.uo.mo

end PartialOrder

variable [SemilatticeSup α] [SemilatticeSup β] {θ : α → β → Prop}

theorem SINC.up_of_sum (h : SINC θ) (hs : SUM θ) : UP θ := h.uo.up_of_sum hs

/-- A summative strictly incremental relation relates each object to one event, so strict
incrementality and summativity are compatible only for relations like that of *eat*, not that of
*read* ([krifka-1998], after (51)). -/
theorem SINC.gue_of_sum (h : SINC θ) (hs : SUM θ) : GUE θ := h.ue.gue_of_sum hs

/-- A relation is incremental when it is the closure of some strictly incremental relation under
sums. -/
def INC (θ : α → β → Prop) : Prop :=
  ∃ θ', SINC θ' ∧ ∀ x e, θ x e ↔ AlgClosure (Function.uncurry θ') (x, e)

/-- A summative strictly incremental relation is incremental, being its own closure. -/
theorem SINC.inc_of_sum (h : SINC θ) (hs : SUM θ) : INC θ :=
  ⟨θ, h, fun x e ↦ (algClosure_of_cum (x := (x, e)) (sum_iff_cum_uncurry.1 hs)).symm⟩

/-- An incremental relation is summative, being a closure under sums. -/
theorem INC.sum (h : INC θ) : SUM θ :=
  let ⟨_, _, hθ⟩ := h
  fun _ _ h₁ _ _ h₂ ↦ (hθ _ _).mpr (((hθ _ _).mp h₁).sum ((hθ _ _).mp h₂))

/-- The property of a thematic relation that an incrementality class names. A verb is classed
by the strongest that its theme relation has. -/
def Incrementality.Holds : Incrementality → (α → β → Prop) → Prop
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

/-- The verb phrase of a relation and an object predicate holds of the events with some object
of the predicate. -/
def VP (θ : α → β → Prop) (OBJ : α → Prop) : β → Prop := fun e ↦ ∃ y, OBJ y ∧ θ y e

theorem vp_eq (θ : α → β → Prop) (y : α) : VP θ (· = y) = θ y :=
  funext fun _ ↦ propext ⟨fun ⟨_, h, hθ⟩ ↦ h ▸ hθ, fun h ↦ ⟨y, rfl, h⟩⟩

theorem vp_graph (f : β → α) (OBJ : α → Prop) : VP (· = f ·) OBJ = OBJ ∘ f :=
  funext fun _ ↦ propext ⟨by rintro ⟨_, h, rfl⟩; exact h, fun h ↦ ⟨_, h, rfl⟩⟩

variable {θ : α → β → Prop} {OBJ : α → Prop}

section Preorder

variable [Preorder α] [Preorder β]

/-- A relation maps to objects iff it carries divisive reference from the object to the verb
phrase. -/
theorem mo_iff_forall_div_vp : MO θ ↔ ∀ OBJ : α → Prop, DIV OBJ → DIV (VP θ OBJ) :=
  mo_iff_forall_isLowerSet.trans ⟨fun h OBJ ↦ h {x | OBJ x}, fun h s ↦ h (· ∈ s)⟩

theorem vp_div (hm : MO θ) (hObj : DIV OBJ) : DIV (VP θ OBJ) := mo_iff_forall_div_vp.1 hm OBJ hObj

end Preorder

/-- Uniqueness of participants and mapping to subobjects carry quantization from the object
to the verb phrase, since the object of a proper subevent is a proper part of the object. -/
theorem vp_qua [PartialOrder α] [PartialOrder β] (hU : UP θ) (hm : MSO θ) (hObj : QUA OBJ) :
    QUA (VP θ OBJ) :=
  qua_of_forall fun _ _ ⟨_, hy, hθ⟩ hlt ⟨_, hz, hθz⟩ ↦
    let ⟨_, hlt', hθ'⟩ := hm hθ hlt
    hObj (hU hθz hθ' ▸ hz) hy hlt'.ne hlt'.le

variable [SemilatticeSup α] [SemilatticeSup β]

/-- A summative relation carries cumulativity from the object to the verb phrase. -/
theorem vp_cum (hθ : SUM θ) (hObj : CUM OBJ) : CUM (VP θ OBJ) :=
  fun _ ⟨_, h₁, hθ₁⟩ _ ⟨_, h₂, hθ₂⟩ ↦ ⟨_, hObj h₁ h₂, hθ hθ₁ hθ₂⟩

/-- Along a summative relation with unique participants, a verb phrase is cumulative only if the
object predicate holds of the sum of any two of its objects that the relation relates to
events. -/
theorem not_cum_vp (hs : SUM θ) (hU : UP θ) {x y : α} {e₁ e₂ : β} (hx : OBJ x) (hy : OBJ y)
    (hθ₁ : θ x e₁) (hθ₂ : θ y e₂) (hSum : ¬ OBJ (x ⊔ y)) : ¬ CUM (VP θ OBJ) := fun hCum ↦
  let ⟨_, hz, hθ⟩ := hCum ⟨x, hx, hθ₁⟩ ⟨y, hy, hθ₂⟩
  hSum (hU hθ (hs hθ₁ hθ₂) ▸ hz)

/-- A summative strictly incremental relation, as *eat* is ([krifka-1998]), carries quantization
from the object to the verb phrase, since summativity and unique objects give unique
participants. -/
theorem SINC.vp_qua (h : SINC θ) (hs : SUM θ) (hObj : QUA OBJ) : QUA (VP θ OBJ) :=
  Aspect.vp_qua (h.up_of_sum hs) h.mso hObj

/-- A cumulative object predicate along a sum homomorphism gives a cumulative verb phrase, so
*drink milk* is cumulative ([champollion-krifka-2016]). -/
theorem vp_cum_graph {F : Type*} [FunLike F β α] [SupHomClass F β α] (f : F) (hObj : CUM OBJ) :
    CUM (VP (· = f ·) OBJ) :=
  vp_cum (sum_graph f) hObj

/-- A quantized object predicate along an injective sum homomorphism gives a quantized verb
phrase, so *drink two liters of milk* is quantized ([champollion-krifka-2016]). The
homomorphism places the participant of a proper subevent below the whole participant, and
injectivity makes it a proper part. -/
theorem vp_qua_graph {F : Type*} [FunLike F β α] [SupHomClass F β α] (f : F)
    (hf : Function.Injective f) (hObj : QUA OBJ) : QUA (VP (· = f ·) OBJ) :=
  vp_qua (up_graph f) ((mso_graph_iff f).2 ((OrderHomClass.mono f).strictMono_of_injective hf))
    hObj

end VP

end Aspect
