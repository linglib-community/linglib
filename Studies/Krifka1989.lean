module

public import Linglib.Semantics.Aspect.Telicity
public import Mathlib.Order.WellFounded

/-!
# Krifka (1989): Nominal Reference, Temporal Constitution and Quantification in Event Semantics

Krifka relates the reference of nominal predicates to the temporal constitution of verbal
predicates. Objects, events and times form join semilattices, and a predicate is cumulative when
it is closed under join and quantized when no instance is a proper part of another. Measure
phrases and count nouns are quantized because their measure functions are extensive. A thematic
relation transfers the reference type of its nominal argument to the verbal predicate:
summativity carries cumulativity across, and uniqueness and mapping properties carry quantization
across when the relation is not iterative.

## Implementation notes

The paper's relations are stated with the library's object-first thematic relations, so its
uniqueness of objects is `UP`, uniqueness of events `GUE`, mapping to objects `MO`, mapping to
events `ME`, and summativity `SUM`. Its part structures satisfy relative complementarity (D 9),
which the measure theorems assume as `Mereology.HasRemainders`. Theorem (T 3) needs a nonempty
predicate, since the empty predicate is both quantized and strictly cumulative. The proof of
(T 13) shows that every verbal event has a part outside the predicate; its conclusion that the
event contains an atom holds when the part order on events is well founded
(`atm_of_wellFoundedLT`). The sections on negation (§6) and quantification (§7) are prose.

## References

* [krifka-1989]
* [link-1983], [krifka-1998]
-/

@[expose] public section

namespace Krifka1989

open Mereology Aspect

/-! ### Reference types (§2) -/

section Reference

variable {α : Type*} [SemilatticeSup α]

/-- A predicate has singular reference (D 11) if it holds of exactly one element. -/
def SNG (P : α → Prop) : Prop := ∃ x, P x ∧ ∀ y, P y → x = y

/-- A predicate has strictly cumulative reference (D 13) if it is cumulative and not
singular. -/
def SCUM (P : α → Prop) : Prop := CUM P ∧ ¬ SNG P

/-- A predicate has strictly quantized reference (D 15) if it is quantized and every instance
has a proper part. -/
def SQUA (P : α → Prop) : Prop := QUA P ∧ ∀ x, P x → ∃ y, y < x

/-- A predicate has atomic reference (D 18) if every instance has a part that is a `P`-atom
(D 17). -/
def ATM (P : α → Prop) : Prop := ∀ x, P x → ∃ y ≤ x, atomize P y

theorem qua_of_sng {P : α → Prop} (h : SNG P) : QUA P :=
  let ⟨_, _, hx⟩ := h
  qua_of_forall fun a b ha hlt hb ↦ hlt.ne ((hx b hb).symm.trans (hx a ha))

theorem cum_of_sng {P : α → Prop} (h : SNG P) : CUM P := by
  obtain ⟨x, hx, huniq⟩ := h
  intro a ha b hb
  rw [← huniq a ha, ← huniq b hb, sup_idem]
  exact hx

theorem not_scum_of_qua {P : α → Prop} (hne : ∃ x, P x) (h : QUA P) : ¬ SCUM P := by
  rintro ⟨hcum, hsng⟩
  obtain ⟨x, hx⟩ := hne
  refine hsng ⟨x, hx, fun y hy ↦ ?_⟩
  by_contra hxy
  have hsup := hcum hx hy
  rcases eq_or_ne (x ⊔ y) x with hxs | hxs
  · exact h hy hx (Ne.symm hxy) (hxs ▸ le_sup_right)
  · exact h hx hsup hxs.symm le_sup_left

theorem atm_of_qua {P : α → Prop} (h : QUA P) : ATM P := fun x hx ↦
  ⟨x, le_rfl, hx, fun z hz hzx ↦ by
    rcases eq_or_lt_of_le hzx with rfl | hlt
    · exact le_rfl
    · exact (h hz hx hlt.ne hlt.le).elim⟩

theorem qua_of_isExtensiveMeasure [HasRemainders α] {M : Type*} [AddCommMonoid M]
    [PartialOrder M] [AddLeftStrictMono M] (μ : α → M) [IsExtensiveMeasure μ] (n : M) :
    QUA (μ · = n) :=
  qua_pullback (IsExtensiveMeasure.strictMono μ) (singleton_qua n)

theorem atm_of_wellFoundedLT [WellFoundedLT α] (P : α → Prop) : ATM P := fun x hx ↦ by
  obtain ⟨y, ⟨hy, hyx⟩, hmin⟩ :=
    WellFounded.has_min wellFounded_lt {y | P y ∧ y ≤ x} ⟨x, hx, le_rfl⟩
  exact ⟨y, hyx, hy, fun z hz hzy ↦ (eq_of_le_of_not_lt hzy (hmin z ⟨hz, hzy.trans hyx⟩)).symm.le⟩

end Reference

/-! ### Nominal predicates (§3) -/

section Nominal

variable {α M : Type*} [SemilatticeSup α] [HasRemainders α] [AddCommMonoid M] [PartialOrder M]
  [AddLeftStrictMono M]

omit [HasRemainders α] in
theorem barePlural_cum (P : α → Prop) : CUM (AlgClosure P) := algClosure_cum

/-- The measure construction (4) quantizes a cumulative noun with two distinct instances (D 28), so
measure phrases cannot stack (3c). -/
theorem measure_qmod {P : α → Prop} (hP : CUM P) {x y : α} (hx : P x) (hy : P y) (hxy : x ≠ y)
    (μ : α → M) [IsExtensiveMeasure μ] (n : M) : ¬ QUA P ∧ QUA (QMOD P μ n) :=
  ⟨fun hQ ↦ qua_cum_incompatible hQ hx hy hxy hP,
    qmod_qua ((IsExtensiveMeasure.strictMono μ).strictMonoOn _) n⟩

/-- A count noun (6), a classifier construction with a built-in natural unit, is quantized. -/
theorem countNoun_qua (P : α → Prop) (NU : α → M) [IsExtensiveMeasure NU] (n : M) :
    QUA (QMOD P NU n) :=
  qmod_qua ((IsExtensiveMeasure.strictMono NU).strictMonoOn _) n

end Nominal

/-! ### Transfer of reference from objects to events (§4) -/

section Transfer

variable {O E : Type*} [SemilatticeSup O] [SemilatticeSup E]

/-- The verbal predicate (12) conjoins a verb with the verb phrase of a thematic relation and a
nominal predicate. -/
def ofTheta (α : E → Prop) (δ : O → Prop) (θ : O → E → Prop) : E → Prop :=
  fun e ↦ α e ∧ VP θ δ e

/-- An event is iterative on an object (D 34) if some part of the object is subjected to two
parts of the event. -/
def ITER (θ : O → E → Prop) (e : E) (x : O) : Prop :=
  θ x e ∧ ∃ e' e'' x', e' ≤ e ∧ e'' ≤ e ∧ e' ≠ e'' ∧ x' ≤ x ∧ θ x' e' ∧ θ x' e''

/-- A relation is gradual (D 35) if it has uniqueness of objects and both mappings. -/
def GRAD (θ : O → E → Prop) : Prop := UP θ ∧ MO θ ∧ ME θ

variable {α : E → Prop} {δ : O → Prop} {θ : O → E → Prop}

theorem cum_ofTheta (hα : CUM α) (hδ : CUM δ) (hθ : SUM θ) : CUM (ofTheta α δ θ) :=
  hα.inter (vp_cum hθ hδ)

theorem exists_iter (hδ : SNG δ) (hθ : SUM θ) (hne : ∃ e, ofTheta α δ θ e)
    (hs : SCUM (ofTheta α δ θ)) : ∃ e x, ITER θ e x := by
  obtain ⟨e₁, hα₁, x₁, hx₁, hθ₁⟩ := hne
  obtain ⟨hcum, hsng⟩ := hs
  have : ∃ e₂, ofTheta α δ θ e₂ ∧ e₁ ≠ e₂ := by
    by_contra h
    exact hsng ⟨e₁, ⟨hα₁, x₁, hx₁, hθ₁⟩, fun e₂ he₂ ↦ by
      by_contra hne
      exact h ⟨e₂, he₂, hne⟩⟩
  obtain ⟨e₂, ⟨_, x₂, hx₂, hθ₂⟩, hne⟩ := this
  obtain ⟨x, _, huniq⟩ := hδ
  rw [← huniq x₁ hx₁] at hθ₁
  rw [← huniq x₂ hx₂] at hθ₂
  exact ⟨e₁ ⊔ e₂, x, by simpa using hθ hθ₁ hθ₂, e₁, e₂, x, le_sup_left,
    le_sup_right, hne, le_rfl, hθ₁, hθ₂⟩

theorem not_scum_of_not_iter (hδ : SNG δ) (hθ : SUM θ) (hne : ∃ e, ofTheta α δ θ e)
    (hi : ∀ e x, ¬ ITER θ e x) : ¬ SCUM (ofTheta α δ θ) := fun hs ↦
  let ⟨e, x, h⟩ := exists_iter hδ hθ hne hs; hi e x h

theorem not_iter_of_gue (h : GUE θ) (e : E) (x : O) : ¬ ITER θ e x :=
  fun ⟨_, _, _, _, _, _, hne, _, h', h''⟩ ↦ hne (h h' h'')

theorem mso_of_not_iter (hm : MO θ) (hi : ∀ e x, ¬ ITER θ e x) : MSO θ := fun _ _ hxe _ hlt ↦
  let ⟨y, hy, hθ⟩ := hm hxe hlt.le
  ⟨y, lt_of_le_of_ne hy fun h ↦ hi _ _ ⟨hxe, _, _, y, hlt.le, le_rfl, hlt.ne, hy, hθ, h ▸ hxe⟩, hθ⟩

theorem qua_ofTheta (hδ : QUA δ) (hu : UP θ) (hm : MO θ) (hi : ∀ e x, ¬ ITER θ e x) :
    QUA (ofTheta α δ θ) :=
  (vp_qua hu (mso_of_not_iter hm hi) hδ).subset fun _ h ↦ h.2

theorem qua_ofTheta_of_gue (hδ : QUA δ) (hu : UP θ) (hm : MO θ) (hg : GUE θ) :
    QUA (ofTheta α δ θ) :=
  qua_ofTheta hδ hu hm (not_iter_of_gue hg)

theorem exists_le_not_ofTheta (hδ : SQUA δ) (hm : ME θ) (hu : UP θ) (e : E)
    (he : ofTheta α δ θ e) : ∃ e' ≤ e, ¬ ofTheta α δ θ e' := by
  obtain ⟨_, x, hx, hθx⟩ := he
  obtain ⟨y, hyx⟩ := hδ.2 x hx
  obtain ⟨e', he', hθy⟩ := hm hθx hyx.le
  refine ⟨e', he', fun ⟨_, z, hz, hθz⟩ ↦ ?_⟩
  have hzy : z = y := hu hθz hθy
  subst hzy
  exact hδ.1 hz hx hyx.ne hyx.le

/-! ### The classification of thematic relations (14) -/

/-- The five classes of (14) are gradual effected patient (*write a letter*), gradual consumed
patient (*eat an apple*), gradual patient (*read a letter*), affected patient (*touch a
cat*), and stimulus (*see a horse*). -/
inductive ThematicClass
  | gradualEffectedPatient
  | gradualConsumedPatient
  | gradualPatient
  | affectedPatient
  | stimulus
  deriving DecidableEq, Repr

/-- The gradual classes. -/
def ThematicClass.Gradual : ThematicClass → Prop
  | .gradualEffectedPatient | .gradualConsumedPatient | .gradualPatient => True
  | .affectedPatient | .stimulus => False

/-- The classes with uniqueness of events. -/
def ThematicClass.UniqueEvents : ThematicClass → Prop
  | .gradualEffectedPatient | .gradualConsumedPatient => True
  | .gradualPatient | .affectedPatient | .stimulus => False

/-- `c.Requires θ` holds when `θ` meets what (14) requires of the class `c`, namely
summativity throughout, graduality for the gradual classes, and uniqueness of events for
effected and consumed patients. -/
def ThematicClass.Requires (c : ThematicClass) (θ : O → E → Prop) : Prop :=
  SUM θ ∧ (c.Gradual → GRAD θ) ∧ (c.UniqueEvents → GUE θ)

theorem qua_of_uniqueEvents {c : ThematicClass} (hc : c.UniqueEvents) (h : c.Requires θ)
    (hδ : QUA δ) : QUA (ofTheta α δ θ) := by
  have hg : GRAD θ := h.2.1 (by cases c <;> trivial)
  exact qua_ofTheta_of_gue hδ hg.1 hg.2.1 (h.2.2 hc)

theorem gradualPatient_transfer (h : ThematicClass.gradualPatient.Requires θ) :
    (CUM α → CUM δ → CUM (ofTheta α δ θ)) ∧
      (SQUA δ → ∀ e, ofTheta α δ θ e → ∃ e' ≤ e, ¬ ofTheta α δ θ e') :=
  ⟨fun hα hδ ↦ cum_ofTheta hα hδ h.1,
    fun hδ ↦ exists_le_not_ofTheta hδ (h.2.1 trivial).2.2 (h.2.1 trivial).1⟩

end Transfer

/-! ### Temporal adverbials (§5) -/

section Adverbials

variable {E T M : Type*} [SemilatticeSup T]

/-- A durative adverbial (15) quantizes events through an extensive measure of the temporal trace (D
41). -/
theorem durative_qua [SemilatticeSup E] [HasRemainders E] [AddCommMonoid M] [PartialOrder M]
    [AddLeftStrictMono M] (P : E → Prop) (μ' : E → M) [IsExtensiveMeasure μ'] (n : M) :
    QUA (QMOD P μ' n) :=
  qmod_qua ((IsExtensiveMeasure.strictMono μ').strictMonoOn _) n

/-- A time-span adverbial (16) holds of an event that lies within a convex time of the given
measure. -/
def inSpan (P : E → Prop) (τ : E → T) (Conv : T → Prop) (μ : T → M) (n : M) : E → Prop :=
  fun e ↦ P e ∧ ∃ t, Conv t ∧ μ t = n ∧ τ e ≤ t

/-- Time-span adverbials are upward entailing in their number (17). -/
theorem inSpan_mono (P : E → Prop) (τ : E → T) (Conv : T → Prop) (μ : T → M) {n n' : M}
    (h : ∀ t, Conv t → μ t = n → ∃ t', Conv t' ∧ μ t' = n' ∧ t ≤ t') :
    ∀ e, inSpan P τ Conv μ n e → inSpan P τ Conv μ n' e := by
  rintro e ⟨hp, t, hc, hμ, hle⟩
  obtain ⟨t', hc', hμ', htt'⟩ := h t hc hμ
  exact ⟨hp, t', hc', hμ', hle.trans htt'⟩

end Adverbials

end Krifka1989
