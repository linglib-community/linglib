module

public import Mathlib.Order.Interval.Basic
public import Linglib.Semantics.Aspect.Defs
public import Linglib.Semantics.Mereology.Relation

/-!
# Telicity

Krifka treats telicity as a property of event predicates: a predicate is telic when every part
of one of its events that it also applies to is both an initial and a final part of that event.
Quantized predicates are telic though not conversely, since a predicate that fixes the run time,
*from three to four*, is telic without being quantized, and cumulative or divisive predicates that
apply to events with successive parts are not. Telicity originates in the thematic relation. A
relation is strictly incremental when the parts of the object and of the event correspond one to
one, as for the object of *eat*, and incremental when it is the closure of such a relation under
sums, which admits the backups of *read the article*. The reference properties of the object
carry over to the verb phrase: cumulativity along a summative relation, and quantization along a
relation with unique participants that maps to subobjects. For a thematic function these are a
sum homomorphism and an injective one, so *drink milk* is cumulative and *drink two liters of
milk* quantized.

## Main definitions

* `IsTelic`: every part of an event of the predicate that the predicate applies to is an initial
  and a final part of it.
* `SINC`, `INC`: strict incrementality and incrementality of a thematic relation.
* `Incrementality.Holds`: the property an incrementality class of `Aspect/Defs.lean` names.
* `VP`: the verb phrase of a relation and an object predicate.

## Main results

* `isTelic_of_qua`, `exists_isTelic_not_qua`: quantized predicates are telic, not conversely.
* `isTelic_runTime_eq`: under temporal precedence a predicate that fixes the run time is telic.
* `not_isTelic_of_cum`, `not_isTelic_of_div`: cumulative and divisive predicates with successive
  events or parts are not telic.
* `SINC.inc_of_sum`, `INC.sum`: a summative strictly incremental relation is incremental, and an
  incremental relation is summative.
* `vp_cum`, `vp_qua`: cumulativity and quantization carry over from the object to the verb
  phrase; `SINC.vp_qua` is the case of a summative strictly incremental relation, and
  `vp_cum_graph` and `vp_qua_graph` are the cases of a thematic function.

## Implementation notes

Temporal precedence is a parameter of the telicity notions. The proofs use only that parts of an
event neither precede nor follow it, `NoPartPrecedes`, which follows from Krifka's axiom that
overlapping events do not precede each other (`noPartPrecedes_of_overlap`). A final part is an
initial part under the converse precedence, so results about final parts are transported.

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

/-- An initial part of an event is a part that no part of the event precedes. -/
def IsInitialPart (e' e : β) : Prop := e' ≤ e ∧ ¬ ∃ e'', e'' ≤ e ∧ precedes e'' e'

/-- A final part of an event is a part that no part of the event follows, an initial part under
the converse precedence. -/
abbrev IsFinalPart (e' e : β) : Prop := IsInitialPart (flip precedes) e' e

/-- A predicate is telic when every `P`-part of a `P`-event is an initial and a final part of
it. -/
def IsTelic (P : β → Prop) : Prop :=
  ∀ e e', P e → P e' → e' ≤ e → IsInitialPart precedes e' e ∧ IsFinalPart precedes e' e

/-- Parts of an event neither precede nor follow it. -/
def NoPartPrecedes : Prop := ∀ a b : β, a ≤ b → ¬ precedes a b ∧ ¬ precedes b a

variable {precedes}

theorem NoPartPrecedes.flip (h : NoPartPrecedes precedes) : NoPartPrecedes (flip precedes) :=
  fun a b hle ↦ ⟨(h a b hle).2, (h a b hle).1⟩

/-- Parts of an event neither precede nor follow it if overlapping events do not precede each
other ([krifka-1998] (35)) and no event is null. -/
theorem noPartPrecedes_of_overlap [NoBotOrder β] (h : ∀ a b, Overlap a b → ¬ precedes a b) :
    NoPartPrecedes precedes := fun a b hle ↦
  ⟨h a b (.of_le (not_isBot a) hle), h b a (Overlap.of_le (not_isBot a) hle).symm⟩

theorem isInitialPart_self (h : NoPartPrecedes precedes) (e : β) :
    IsInitialPart precedes e e :=
  ⟨le_rfl, fun ⟨_, h', hp⟩ ↦ (h _ _ h').1 hp⟩

theorem isFinalPart_self (h : NoPartPrecedes precedes) (e : β) : IsFinalPart precedes e e :=
  isInitialPart_self h.flip e

theorem IsTelic.flip {P : β → Prop} (h : IsTelic precedes P) : IsTelic (flip precedes) P :=
  fun e e' he he' hle ↦ ⟨(h e e' he he' hle).2, (h e e' he he' hle).1⟩

/-- Quantized predicates are telic. -/
theorem isTelic_of_qua (h : NoPartPrecedes precedes) {P : β → Prop} (hP : QUA P) :
    IsTelic precedes P := fun e e' he he' hle ↦ by
  obtain rfl : e' = e := by_contra fun hne ↦ hP he' he hne hle
  exact ⟨isInitialPart_self h _, isFinalPart_self h _⟩

end Telicity

/-- Under temporal precedence a predicate that fixes the run time is telic: a part of an event runs
within it, so it neither precedes nor follows a part with the event's run time. -/
theorem isTelic_runTime_eq [PartialOrder β] {T : Type*} [LinearOrder T]
    {τ : β → NonemptyInterval T} (hτ : Monotone τ) (I : NonemptyInterval T) :
    IsTelic (fun a b ↦ (τ a).snd < (τ b).fst) (τ · = I) := by
  intro e e' he he' hle
  have hτe : τ e' = τ e := he'.trans he.symm
  refine ⟨⟨hle, ?_⟩, ⟨hle, ?_⟩⟩ <;> rintro ⟨e'', h'', hp⟩
  · change (τ e'').snd < (τ e').fst at hp
    rw [hτe] at hp
    exact hp.not_ge ((NonemptyInterval.le_def.1 (hτ h'')).1.trans (τ e'').fst_le_snd)
  · change (τ e').snd < (τ e'').fst at hp
    rw [hτe] at hp
    exact hp.not_ge ((τ e'').fst_le_snd.trans (NonemptyInterval.le_def.1 (hτ h'')).2)

/-- A telic predicate need not be quantized. With events ordered by their participants and run
times, the predicate true of the events that run from three to four is telic under temporal
precedence, though it holds of an event and of a proper part with the same run time; under the same
precedence the predicate true of every event is not telic. -/
theorem exists_isTelic_not_qua :
    ∃ P : Finset (Fin 2) × NonemptyInterval ℕ → Prop,
      IsTelic (fun a b : Finset (Fin 2) × NonemptyInterval ℕ ↦ a.2.snd < b.2.fst) P ∧ ¬ QUA P ∧
        ¬ IsTelic (fun a b : Finset (Fin 2) × NonemptyInterval ℕ ↦ a.2.snd < b.2.fst)
          fun _ ↦ True := by
  refine ⟨(·.2 = ⟨(3, 4), by decide⟩), isTelic_runTime_eq monotone_snd _, fun h ↦ ?_, fun h ↦ ?_⟩
  · exact h (x := ({0}, ⟨(3, 4), by decide⟩)) rfl (y := ({0, 1}, ⟨(3, 4), by decide⟩)) rfl
      (fun hxy ↦ absurd (congrArg Prod.fst hxy) (by decide))
      (Prod.mk_le_mk.2 ⟨(by decide : ({0} : Finset (Fin 2)) ⊆ {0, 1}), le_rfl⟩)
  · exact (h ({0}, ⟨(0, 1), by decide⟩) ({0}, ⟨(1, 1), by decide⟩) trivial trivial
      (Prod.mk_le_mk.2 ⟨le_rfl, NonemptyInterval.le_def.2 ⟨by decide, by decide⟩⟩)).1.2
      ⟨({0}, ⟨(0, 0), by decide⟩),
        Prod.mk_le_mk.2 ⟨le_rfl, NonemptyInterval.le_def.2 ⟨by decide, by decide⟩⟩,
        (by decide : (0 : ℕ) < 1)⟩

/-- A cumulative predicate true of two events, a part of one following the other, is not
telic. -/
theorem not_isTelic_of_cum [SemilatticeSup β] {precedes : β → β → Prop} {P : β → Prop}
    (hP : CUM P) {e e' e'' : β} (he : P e) (he' : P e') (h'' : e'' ≤ e)
    (hp : precedes e' e'') : ¬ IsTelic precedes P :=
  fun hT ↦ (hT (e ⊔ e') e' (hP he he') he' le_sup_right).2.2 ⟨e'', h''.trans le_sup_left, hp⟩

/-- A divisive predicate true of an event with a part preceding another part is not telic, as
the divisive reference of activities makes them atelic ([champollion-krifka-2016]). -/
theorem not_isTelic_of_div [PartialOrder β] {precedes : β → β → Prop} {P : β → Prop}
    (hP : DIV P) {e e' e'' : β} (he : P e) (h' : e' ≤ e) (h'' : e'' ≤ e)
    (hp : precedes e' e'') : ¬ IsTelic precedes P :=
  fun hT ↦ (hT e e' he (hP h' he) h').2.2 ⟨e'', h'', hp⟩

end InitialFinal

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-! ### Incremental relations -/

/-- A relation is strictly incremental when a part of a related object is related to exactly one
part of the event and conversely, and some related pair has related proper parts, so the
relation is not confined to atoms. -/
structure SINC (θ : α → β → Prop) : Prop where
  ue : UE θ
  uo : UO θ
  /-- Some related pair has related proper parts. -/
  extended : ∃ (x y : α) (e e' : β), y < x ∧ e' < e ∧ θ x e ∧ θ y e'

variable {θ : α → β → Prop}

theorem SINC.mse (h : SINC θ) : MSE θ := h.ue.mse_of_uo h.uo

theorem SINC.mso (h : SINC θ) : MSO θ := h.uo.mso_of_ue h.ue

theorem SINC.me (h : SINC θ) : ME θ := h.ue.me

theorem SINC.mo (h : SINC θ) : MO θ := h.uo.mo

/-- A relation is incremental when it is the closure of some strictly incremental relation under
sums. -/
def INC (θ : α → β → Prop) : Prop :=
  ∃ θ', SINC θ' ∧ ∀ x e, θ x e ↔ AlgClosure (Function.uncurry θ') (x, e)

/-- A summative strictly incremental relation is incremental, being its own closure. -/
theorem SINC.inc_of_sum (h : SINC θ) (hs : SUM θ) : INC θ :=
  ⟨θ, h, fun x e ↦ (algClosure_of_cum (x := (x, e)) (sum_iff_cum_uncurry.1 hs)).symm⟩

/-- An incremental relation is summative, being a closure under sums. -/
theorem INC.sum (h : INC θ) : SUM θ := by
  obtain ⟨θ', -, hθ⟩ := h
  have : Function.uncurry θ = AlgClosure (Function.uncurry θ') :=
    funext fun ⟨x, e⟩ ↦ propext (hθ x e)
  exact sum_iff_cum_uncurry.2 (this ▸ algClosure_cum)

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

/-! ### The verb phrase -/

/-- The verb phrase of a relation and an object predicate holds of the events with some object
of the predicate. -/
def VP (θ : α → β → Prop) (OBJ : α → Prop) : β → Prop := fun e ↦ ∃ y, OBJ y ∧ θ y e

variable {θ : α → β → Prop} {OBJ : α → Prop}

/-- A summative relation carries cumulativity from the object to the verb phrase. -/
theorem vp_cum (hθ : SUM θ) (hObj : CUM OBJ) : CUM (VP θ OBJ) :=
  fun _ ⟨_, h₁, hθ₁⟩ _ ⟨_, h₂, hθ₂⟩ ↦ ⟨_, hObj h₁ h₂, hθ hθ₁ hθ₂⟩

/-- Uniqueness of participants and mapping to subobjects carry quantization from the object
to the verb phrase, since the object of a proper subevent is a proper part of the object. -/
theorem vp_qua (hU : UP θ) (hm : MSO θ) (hObj : QUA OBJ) : QUA (VP θ OBJ) :=
  qua_of_forall fun _ _ ⟨_, hy, hθ⟩ hlt ⟨_, hz, hθz⟩ ↦
    let ⟨_, hlt', hθ'⟩ := hm hθ hlt
    hObj (hU hθz hθ' ▸ hz) hy hlt'.ne hlt'.le

/-- A summative strictly incremental relation, as *eat* is ([krifka-1998]), carries quantization
from the object to the verb phrase, since summativity and unique objects give unique
participants. -/
theorem SINC.vp_qua (h : SINC θ) (hs : SUM θ) (hObj : QUA OBJ) : QUA (VP θ OBJ) :=
  Aspect.vp_qua (h.uo.up_of_sum hs) h.mso hObj

omit [SemilatticeSup α] [SemilatticeSup β] in
theorem vp_eq (θ : α → β → Prop) (y : α) : VP θ (· = y) = θ y :=
  funext fun _ ↦ propext ⟨fun ⟨_, h, hθ⟩ ↦ h ▸ hθ, fun h ↦ ⟨y, rfl, h⟩⟩

omit [SemilatticeSup α] [SemilatticeSup β] in
theorem vp_graph (f : β → α) (OBJ : α → Prop) : VP (· = f ·) OBJ = OBJ ∘ f :=
  funext fun _ ↦ propext ⟨by rintro ⟨_, h, rfl⟩; exact h, fun h ↦ ⟨_, h, rfl⟩⟩

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

end Aspect
