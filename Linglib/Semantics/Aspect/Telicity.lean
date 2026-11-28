module

public import Linglib.Core.Order.Minimals
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
that apply to events with successive parts are not. The thematic relations from which telicity
originates are in `Semantics/Aspect/Incremental.lean`.

## Implementation notes

Temporal precedence is a parameter of the telicity notions. The proofs use only that parts of an
event neither precede nor follow it, `NoPartPrecedes`, which follows from Krifka's axiom that
overlapping events do not precede each other (`noPartPrecedes_of_forall_le`) and holds of any
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
open scoped SetRel

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

/-- Parts of an event neither precede nor follow it if events with a common part do not precede
each other ([krifka-1998] (35)). -/
theorem noPartPrecedes_of_forall_le (h : ∀ a b c, c ≤ a → c ≤ b → ¬ precedes a b) :
    NoPartPrecedes precedes := fun a b hp ↦
  ⟨fun hle ↦ h a b a le_rfl hle hp, fun hle ↦ h a b b hle le_rfl hp⟩

variable (precedes) [IsStrictOrder β precedes]

/-- An initial part of an event is a part that no part of the event precedes: a minimal element
of the parts of the event in the order of precedence. -/
def IsInitialPart (e' e : β) : Prop :=
  e' ∈ (partialOrderOfSO precedes).toPreorder.minimals (Set.Iic e)

/-- A final part of an event is a part that no part of the event follows, an initial part under
the converse precedence. -/
abbrev IsFinalPart (e' e : β) : Prop := IsInitialPart (Function.swap precedes) e' e

/-- A set of events is telic when every part in it of one of its events is an initial and a final
part of that event. -/
def IsTelic (s : Set β) : Prop :=
  ∀ ⦃e e'⦄, e ∈ s → e' ∈ s → e' ≤ e → IsInitialPart precedes e' e ∧ IsFinalPart precedes e' e

variable {precedes} {s : Set β} {e e' e'' : β}

theorem isInitialPart_iff :
    IsInitialPart precedes e' e ↔ e' ≤ e ∧ ∀ ⦃e''⦄, e'' ≤ e → ¬ precedes e'' e' :=
  Preorder.mem_minimals_iff.trans <| and_congr_right fun _ ↦
    ⟨fun h _ h'' hp ↦ (h h'' (.inr hp)).elim (fun heq ↦ irrefl_of precedes _ (heq ▸ hp))
        fun hp' ↦ irrefl_of precedes _ (_root_.trans hp hp'),
      fun h _ h'' hle ↦ hle.elim (fun heq ↦ .inl heq.symm) fun hp ↦ (h h'' hp).elim⟩

theorem IsInitialPart.le (h : IsInitialPart precedes e' e) : e' ≤ e := (isInitialPart_iff.mp h).left

theorem IsInitialPart.not_precedes (h : IsInitialPart precedes e' e) (h'' : e'' ≤ e) :
    ¬ precedes e'' e' := (isInitialPart_iff.mp h).right h''

theorem IsTelic.isInitialPart (h : IsTelic precedes s) (he : e ∈ s) (he' : e' ∈ s) (hle : e' ≤ e) :
    IsInitialPart precedes e' e := (h he he' hle).left

theorem IsTelic.isFinalPart (h : IsTelic precedes s) (he : e ∈ s) (he' : e' ∈ s) (hle : e' ≤ e) :
    IsFinalPart precedes e' e := (h he he' hle).right

/-- A set of events is telic iff a part in it of one of its events neither precedes nor follows
any part of that event. -/
theorem isTelic_iff :
    IsTelic precedes s ↔
      ∀ ⦃e e'⦄, e ∈ s → e' ∈ s → e' ≤ e → ∀ ⦃e''⦄, e'' ≤ e → IncompRel precedes e'' e' :=
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

theorem IsTelic.swap (h : IsTelic precedes s) : IsTelic (Function.swap precedes) s :=
  fun _ _ he he' hle ↦ ⟨h.isFinalPart he he' hle, h.isInitialPart he he' hle⟩

/-- Quantized predicates are telic. -/
theorem isTelic_of_qua (h : NoPartPrecedes precedes) (hP : QUA s) :
    IsTelic precedes s := fun e e' he he' hle ↦ by
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
    [IsTemporalPrecedence β r] {s : Set β} (hP : QUA s) : IsTelic r s :=
  Aspect.isTelic_of_qua (IsTemporalPrecedence.noPartPrecedes r) hP

/-- A predicate that fixes the run time is telic: a part of an event runs within it, so it neither
precedes nor follows a part with the event's run time. -/
theorem isTelic_runTime_eq [PartialOrder β] {T : Type*} [LinearOrder T]
    {τ : β → NonemptyInterval T} (hτ : Monotone τ) (I : NonemptyInterval T) :
    IsTelic (Precedes τ) {e | τ e = I} := by
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
    [IsStrictOrder β precedes] {s : Set β}
    (hP : CUM s) {e e' e'' : β} (he : e ∈ s) (he' : e' ∈ s) (h'' : e'' ≤ e)
    (hp : precedes e' e'') : ¬ IsTelic precedes s :=
  fun hT ↦ (isTelic_iff.mp hT (hP he he') he' le_sup_right (h''.trans le_sup_left)).right hp

/-- A divisive predicate true of an event with a part preceding another part is not telic, as
the divisive reference of activities makes them atelic ([champollion-krifka-2016]). -/
theorem not_isTelic_of_div [PartialOrder β] {precedes : β → β → Prop}
    [IsStrictOrder β precedes] {s : Set β}
    (hP : DIV s) {e e' e'' : β} (he : e ∈ s) (h' : e' ≤ e) (h'' : e'' ≤ e)
    (hp : precedes e' e'') : ¬ IsTelic precedes s :=
  fun hT ↦ (isTelic_iff.mp hT he (hP h' he) h' h'').right hp

end InitialFinal

end Aspect
