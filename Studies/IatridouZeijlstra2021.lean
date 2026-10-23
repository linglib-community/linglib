module

public import Linglib.Semantics.Aspect.SubintervalProperty
public import Linglib.Semantics.Exhaustification.Excluder
public import Linglib.Semantics.Quantification.Exceptive
public import Studies.Giannakidou2002
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Iatridou and Zeijlstra (2021): The Complex Beauty of Boundary Adverbials

Iatridou and Zeijlstra analyze *in years* and *until* as boundary adverbials that are domain
wideners. *In years* introduces the subintervals of the perfect time span as domain alternatives,
which exhaustification turns into a contradiction for the positive perfective claim and leaves
vacuous under negation, so it is a negative polarity item. As a domain widener it stretches its
left boundary as far as is logically possible, to the greatest event-free span, which forces an
event just beyond that boundary, the noncancelable actuality inference, and makes the span
contain every event-free alternative, the beyond expectation inference. *Until* is the mirror
image with the left boundary fixed: with an imperfective predicate exhaustification is vacuous,
and with a perfective one only the construal exhaustifying the negated claim survives, so the
punctual and durative *until*s of Karttunen and Giannakidou are one word. Against their ambiguity
account, negation yields the subinterval property, so its durative *until* would accept a negated
perfective with no event at all, and Greek *para mono* is an exceptive whose meaning already
gives the punctual one.

## Main statements

* `in_years_contradictory`: exhaustified, the positive perfective claim is contradictory when
  the events are shorter than the span.
* `negated_perfective_exh_vacuous`, `throughout_exh_vacuous`: exhaustification is vacuous for a
  negated perfective and for a predicate holding throughout the span.
* `not_throughout_exh_contradictory`: exhaustifying the claim that an imperfective predicate does
  not hold throughout the span is contradictory.
* `actuality_inference`, `event_near_lb`, `event_near_rb`: a widened span forces a relevant event
  just beyond its widened boundary.
* `beyond_expectation_inference`: the widened span contains every event-free alternative.
* `widened_iff_maximal`: the widened span is the event-free span stretched until the sentence
  would become false.
* `not_widened_rb_of_finite`: in dense time no span is widened past finitely many events.
* `two_until_overgenerates`: the durative *until* of the ambiguity account accepts a negated
  perfective with no event at all.
* `eventiveUntil_of_exceptive`: *para mono* with a temporal argument under negation, read as an
  exceptive, entails the punctual *until* meaning, the event included.
* `isLeast_rightBoundaries_prfv`, `isLeast_rightBoundaries_unbounded`: a perfective argument of
  *until* sets the right boundary at the completion of its event, an imperfective one at the
  onset.

## Implementation notes

* Exhaustification is the shared `Exhaustification.exh` over the domain alternatives, the claim
  at every subinterval. Entailment between the alternatives is logical, inclusion between sets of
  interpretations of the event predicate: a claim is stated for `P : V → E → Prop` reaching every
  extension (`Function.Surjective P`), the extensions themselves (`P = id`, `V = E → Prop`) or
  their negations (`surjective_not`). A predicate at a world is its extension, `τ ∈ PRFV P w` being
  `PRFV id (P w) τ` by definition. Refuting an entailment assumes the event domain rich, every
  interval the run time of some event (`Function.Surjective Event.τ`).
* The paper calls the exhaustified positive claim a logical contradiction. It needs the events to
  be shorter than the span, as Chierchia's culminated event inside a period of weeks is; an event
  filling the span exactly survives exhaustification (`mem_exh_prfv_iff`). The contradiction for
  the not-throughout claim, (142), needs overlapping events to sum and an interior point of the
  span.
* The widened span is `IsGreatest` among the event-free spans with the fixed boundary, its other
  boundary the right one set by tense for *in years* and the contextual left one for *until*.
  With closed spans and inclusion the forced event lies strictly beyond the widened boundary, and
  in dense time such a span exists only past infinitely many events; the paper puts "issues of
  density aside".
* The paper's meaning for *para mono*, after von Fintel and Iatridou, is an existential that does
  not itself entail the exception; for the entailment it appeals to "one's favorite semantics" of
  exceptives. Von Fintel's least-exception semantics, `Quantifier.Exceptive`, supplies it.
* The paper's summary of the three scopal construals in Section 7.2 has the labels of the first
  two interchanged relative to (146) and (148), and Section 8 once attaches throughout-not and
  not-throughout to (148c2) and (148c1), the reverse of (148); the theorems follow (146) and
  (148).

## TODO

* Section 8's fact that *in*-adverbials lack the universal perfect, (153), on which the
  exclusion of (154c1–2) rests, is taken as given by the paper and not derived.
* The satisfaction of the actuality inference on a future branch, (155)–(162), and the hypothesis
  that a presupposed span makes a domain widener a strong polarity item, after Gajewski's account
  of strong items by enriched meanings, are not formalized.

## References

* [iatridou-zeijlstra-2021]
* [iatridou-anagnostopoulou-izvorski-2001]
* [chierchia-2013]
* [kadmon-landman-1993]
* [karttunen-1974]
* [giannakidou-2002]
* [von-fintel-1993]
* [von-fintel-fox-iatridou-2014]
* [gajewski-2011]
-/

@[expose] public section

namespace IatridouZeijlstra2021

open Aspect NonemptyInterval Exhaustification

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]

/-! ### Domain alternatives and exhaustification -/

section Exhaustification

variable {V : Type*} {p : V → Set (NonemptyInterval T)} {τ : NonemptyInterval T}

/-- The domain alternatives of the claim `p` at the span `τ` are the claim at each of its
subintervals, (45b), (49b) and (127). -/
def domainAlternatives (p : V → Set (NonemptyInterval T)) (τ : NonemptyInterval T) :
    Set (Set V) :=
  (fun τ' ↦ {v | τ' ∈ p v}) '' Set.Iic τ

theorem exh_domainAlternatives_eq_self (hp : ∀ v, IsLowerSet (p v)) :
    exh (domainAlternatives p τ) {v | τ ∈ p v} = {v | τ ∈ p v} :=
  exh_eq_self <| by rintro _ ⟨τ', hτ', rfl⟩ v hv; exact hp v hτ' hv

theorem mem_exh_domainAlternatives_iff
    (hp : ∀ τ₁ τ₂, {v | τ₁ ∈ p v} ⊆ {v | τ₂ ∈ p v} ↔ τ₁ ≤ τ₂) {v : V} :
    v ∈ exh (domainAlternatives p τ) {v | τ ∈ p v} ↔ τ ∈ p v ∧ ∀ τ' < τ, τ' ∉ p v := by
  simp only [mem_exh, domainAlternatives, Set.forall_mem_image, Set.mem_Iic, Set.mem_ofPred_eq,
    hp]
  refine and_congr_right fun _ ↦ ⟨fun h τ' hlt hv ↦ hlt.not_ge (h hlt.le hv), fun h τ' hle hv ↦ ?_⟩
  obtain rfl | hlt := hle.eq_or_lt
  · exact le_rfl
  · exact absurd hv (h τ' hlt)

end Exhaustification

/-! ### *In years*: the perfective claim and its negation

The assertion of a perfect of the perfective, (14e) and (49a), is `Aspect.PRFV`: some event's
run time lies inside the span. Its domain alternatives are stronger and not entailed, so
exhaustification negates them all and the event would have to fill the span, which a culminated
event shorter than weeks cannot, (44) and (49). The negated perfective has the subinterval
property (`Aspect.isLowerSet_compl_prfv`), so under negation every alternative is
entailed and exhaustification is vacuous, (50). With *until* the same holds of the until time
span: the positive perfective (128)–(132) is contradictory, and so is (146a), exhaustifying the
perfective of the negated predicate, while the construal exhaustifying the negated claim, (148b),
is vacuous. -/

section Perfective

variable {V : Type*} {P : V → E → Prop} {τ : NonemptyInterval T}

theorem prfv_subset_prfv_iff (hP : Function.Surjective P)
    (hrich : Function.Surjective (Event.τ : E → NonemptyInterval T)) {τ₁ τ₂ : NonemptyInterval T} :
    {v | τ₁ ∈ PRFV P v} ⊆ {v | τ₂ ∈ PRFV P v} ↔ τ₁ ≤ τ₂ := by
  refine ⟨fun h ↦ ?_, fun h _ ⟨e, he, hv⟩ ↦ ⟨e, he.trans h, hv⟩⟩
  obtain ⟨v, hv⟩ := hP (Event.τ · = τ₁)
  obtain ⟨e₀, he₀⟩ := hrich τ₁
  obtain ⟨e, he, heq⟩ := h (a := v) ⟨e₀, he₀.le, (congrFun hv e₀).mpr he₀⟩
  exact (congrFun hv e).mp heq ▸ he

theorem mem_exh_prfv_iff (hP : Function.Surjective P)
    (hrich : Function.Surjective (Event.τ : E → NonemptyInterval T)) {v : V} :
    v ∈ exh (domainAlternatives (PRFV P) τ) {v | τ ∈ PRFV P v} ↔
      (∃ e, Event.τ e = τ ∧ P v e) ∧ ∀ τ' < τ, τ' ∉ PRFV P v := by
  rw [mem_exh_domainAlternatives_iff fun _ _ ↦ prfv_subset_prfv_iff hP hrich]
  exact ⟨fun ⟨⟨e, he, hv⟩, h⟩ ↦ ⟨⟨e, he.eq_of_not_lt fun hlt ↦ h _ hlt ⟨e, le_rfl, hv⟩, hv⟩, h⟩,
    fun ⟨⟨e, he, hv⟩, h⟩ ↦ ⟨⟨e, he.le, hv⟩, h⟩⟩

/-- Where every relevant event is shorter than the span, the exhaustified positive claim is
contradictory, so *in years* is a negative polarity item, (44) and (49). The positive *until*
sentence (128), the perfect of (152b), the perfective of the negated predicate in (146a) and the
presupposition of (180) are instances. -/
theorem in_years_contradictory (hP : Function.Surjective P)
    (hrich : Function.Surjective (Event.τ : E → NonemptyInterval T)) {v : V}
    (hshort : ∀ e, P v e → Event.τ e ≠ τ) :
    v ∉ exh (domainAlternatives (PRFV P) τ) {v | τ ∈ PRFV P v} := fun h ↦
  let ⟨⟨e, he, hv⟩, _⟩ := (mem_exh_prfv_iff hP hrich).1 h
  hshort e hv he

/-- Under negation exhaustification is vacuous, (50) and (126)–(127), and so is the construal of
*until* that exhaustifies the negated perfective, (148b). -/
theorem negated_perfective_exh_vacuous :
    exh (domainAlternatives (fun v ↦ (PRFV P v)ᶜ) τ) {v | τ ∉ PRFV P v} = {v | τ ∉ PRFV P v} :=
  exh_domainAlternatives_eq_self fun v ↦ isLowerSet_compl_prfv P v

end Perfective

theorem surjective_not : Function.Surjective fun (v : E → Prop) e ↦ ¬ v e :=
  fun u ↦ ⟨fun e ↦ ¬ u e, funext fun _ ↦ propext not_not⟩

/-! ### Domain widening: the actuality and beyond expectation inferences

A boundary adverbial sets one boundary of its span, while tense or the argument of *until* fixes
the other (`F`, the spans ending at `t` for *in years* and those starting at `t` for *until*). A
domain widener stretches its boundary as far as is logically possible: its span is the greatest
event-free span with the fixed boundary, Section 4. The event that stops the widening is the
actuality inference, Constant's observation, and the span's containing every event-free
alternative is the beyond expectation inference. A boundary adverbial that names its own
boundary, *in (the last) 5 years* or *since 2015*, leaves the actuality inference cancelable and
has no beyond expectation inference. -/

section Widening

/-- The span of a domain widener whose other boundary is fixed by `F` is the greatest event-free
span that `F` admits. -/
def Widened (F : Set (NonemptyInterval T)) (P : W → E → Prop) (w : W)
    (τ : NonemptyInterval T) : Prop :=
  IsGreatest (F \ PRFV P w) τ

variable {F : Set (NonemptyInterval T)} {P : W → E → Prop} {w : W} {τ τ' : NonemptyInterval T}

theorem isChain_rb (t : T) : IsChain (· ≤ ·) {τ : NonemptyInterval T | τ.snd = t} := by
  intro τ₁ h₁ τ₂ h₂ _
  rcases le_total τ₂.fst τ₁.fst with h | h
  · exact .inl (le_def.2 ⟨h, (h₁.trans h₂.symm).le⟩)
  · exact .inr (le_def.2 ⟨h, (h₂.trans h₁.symm).le⟩)

theorem isChain_lb (t : T) : IsChain (· ≤ ·) {τ : NonemptyInterval T | τ.fst = t} := by
  intro τ₁ h₁ τ₂ h₂ _
  rcases le_total τ₁.snd τ₂.snd with h | h
  · exact .inl (le_def.2 ⟨(h₂.trans h₁.symm).le, h⟩)
  · exact .inr (le_def.2 ⟨(h₁.trans h₂.symm).le, h⟩)

/-- On a chain of spans sharing the fixed boundary, the widened span is the maximal event-free
one, the boundary stretched until the sentence would become false. -/
theorem widened_iff_maximal (hF : IsChain (· ≤ ·) F) :
    Widened F P w τ ↔ Maximal (· ∈ F \ PRFV P w) τ := by
  refine ⟨fun h ↦ ⟨h.1, fun _ hτ' _ ↦ h.2 hτ'⟩, fun h ↦ ⟨h.1, fun τ' hτ' ↦ ?_⟩⟩
  obtain rfl | hne := eq_or_ne τ' τ
  · exact le_rfl
  · exact (hF hτ'.1 h.1.1 hne).elim id (h.2 hτ')

theorem Widened.prfv (h : Widened F P w τ) (hτ' : τ' ∈ F) (hlt : τ < τ') : τ' ∈ PRFV P w :=
  by_contra fun hfree ↦ hlt.not_ge (h.2 ⟨hτ', hfree⟩)

/-- The actuality inference is not cancelable, Constant's observation (22) and (26), since a
relevant event exists whenever the span could be widened at all. -/
theorem actuality_inference (h : Widened F P w τ) (hw : ∃ τ' ∈ F, τ < τ') : ∃ e, P w e :=
  let ⟨_, hτ', hlt⟩ := hw
  let ⟨e, _, hP⟩ := h.prfv hτ' hlt
  ⟨e, hP⟩

/-- The beyond expectation inference, (31)–(33) and (119)–(122), is that the widened span contains
every event-free span with the same fixed boundary. -/
theorem beyond_expectation_inference (h : Widened F P w τ) (hτ' : τ' ∈ F)
    (hfree : τ' ∉ PRFV P w) : τ' ≤ τ :=
  h.2 ⟨hτ', hfree⟩

/-- With *in years* the last event starts just before the left boundary of the widened perfect
time span, (51), since however close to the boundary one looks an event starts there,
(23)–(24). -/
theorem event_near_lb {t : T} (h : Widened {τ | τ.snd = t} P w τ) {s : T} (hs : s < τ.fst) :
    ∃ e, P w e ∧ s ≤ (Event.τ e).fst ∧ (Event.τ e).fst < τ.fst := by
  obtain ⟨e, he, hP⟩ := h.prfv (τ' := ⟨(s, τ.snd), hs.le.trans τ.fst_le_snd⟩) h.1.1
    (lt_of_le_of_ne (le_def.2 ⟨hs.le, le_rfl⟩) fun heq ↦ hs.ne' (congrArg (·.fst) heq))
  exact ⟨e, hP, (le_def.1 he).1,
    lt_of_not_ge fun hge ↦ h.1.2 ⟨e, le_def.2 ⟨hge, (le_def.1 he).2⟩, hP⟩⟩

/-- With *until* the event ends just after the right boundary of the widened until time span,
(123). -/
theorem event_near_rb {t : T} (h : Widened {τ | τ.fst = t} P w τ) {s : T} (hs : τ.snd < s) :
    ∃ e, P w e ∧ (Event.τ e).snd ≤ s ∧ τ.snd < (Event.τ e).snd := by
  obtain ⟨e, he, hP⟩ := h.prfv (τ' := ⟨(τ.fst, s), τ.fst_le_snd.trans hs.le⟩) h.1.1
    (lt_of_le_of_ne (le_def.2 ⟨le_rfl, hs.le⟩) fun heq ↦ hs.ne (congrArg (·.snd) heq))
  exact ⟨e, hP, (le_def.1 he).2,
    lt_of_not_ge fun hge ↦ h.1.2 ⟨e, le_def.2 ⟨(le_def.1 he).1, hge⟩, hP⟩⟩

/-- Over the integers, with one seizure at time `0` and the right boundary at `10`, the perfect time
span of *in years* runs from `1` to `10`. -/
example : Widened (W := Unit) (E := NonemptyInterval ℤ) {τ | τ.snd = 10}
    (fun _ e ↦ e = NonemptyInterval.pure 0) () ⟨(1, 10), by decide⟩ := by
  refine ⟨⟨rfl, fun ⟨e, he, hP⟩ ↦ by
    subst hP; simp [ViewpointType.ttTSitRelation, le_def] at he⟩, fun τ' ⟨hrb, hfree⟩ ↦ ?_⟩
  refine le_def.2 ⟨not_lt.1 fun hlt ↦ hfree ⟨.pure 0, le_def.2 ⟨?_, ?_⟩, rfl⟩, hrb.le⟩
  · simp at hlt ⊢; omega
  · simp at hrb ⊢; omega

/-- In dense time a perfect time span is widened only past infinitely many events, since with
finitely many an event-free span can always be stretched a little further. -/
theorem not_widened_rb_of_finite [DenselyOrdered T] [NoMinOrder T] {t : T}
    (hfin : {e | P w e}.Finite) : ¬ Widened {τ | τ.snd = t} P w τ := fun h ↦ by
  obtain ⟨s, hs, hsF⟩ :
      ∃ s < τ.fst, ∀ e, P w e → (Event.τ e).fst < τ.fst → (Event.τ e).fst < s := by
    rcases ({e | P w e ∧ (Event.τ e).fst < τ.fst} : Set E).eq_empty_or_nonempty with hE | hne
    · obtain ⟨s, hs⟩ := exists_lt τ.fst
      exact ⟨s, hs, fun e hP hlt ↦ (hE.subset ⟨hP, hlt⟩).elim⟩
    · obtain ⟨m, ⟨_, hm⟩, hmax⟩ :=
        Set.exists_max_image _ (fun e ↦ (Event.τ e).fst) (hfin.subset fun _ he ↦ he.1) hne
      obtain ⟨s, hms, hs⟩ := exists_between hm
      exact ⟨s, hs, fun e hP hlt ↦ (hmax e ⟨hP, hlt⟩).trans_lt hms⟩
  obtain ⟨e, hP, hse, hlt⟩ := event_near_lb h hs
  exact (hsF e hP hlt).not_ge hse

/-- A boundary adverbial that names its left boundary `s`, *in (the last) 5 years* or *since 2015*,
leaves the actuality inference cancelable, since the negated perfect holds with no relevant event
at all, (11)–(12), and with the last event before the left boundary, (23). -/
theorem cancelable_of_lb {t : T} (s : T) (hs : s ≤ t) :
    (∃ P : W → E → Prop, ∃ τ : NonemptyInterval T, τ.fst = s ∧ τ.snd = t ∧ τ ∉ PRFV P w ∧
        ∀ e, ¬ P w e) ∧
      ∀ e₀ : E, (Event.τ e₀).snd < s →
        ∃ P : W → E → Prop, ∃ τ : NonemptyInterval T, τ.fst = s ∧ τ.snd = t ∧ τ ∉ PRFV P w ∧
          P w e₀ :=
  ⟨⟨fun _ _ ↦ False, ⟨(s, t), hs⟩, rfl, rfl, fun ⟨_, _, h⟩ ↦ h, fun _ ↦ id⟩,
    fun e₀ he₀ ↦ ⟨fun _ e ↦ e = e₀, ⟨(s, t), hs⟩, rfl, rfl,
      fun ⟨_, hle, heq⟩ ↦ (heq ▸ (le_def.1 hle).1 : s ≤ (Event.τ e₀).fst).not_gt
        ((Event.τ e₀).fst_le_snd.trans_lt he₀), rfl⟩⟩

end Widening

/-! ### *Until* with an imperfective predicate

The predicate holds throughout the until time span, (137): `Aspect.UNBOUNDED`, the span inside
the event's run time. Every domain alternative is then entailed and exhaustification is vacuous,
for the affirmative (148a) as for the throughout-not reading with the negated event predicate,
(139) and (148c1), and the not-throughout reading with negation above the exhaustifier, (148c2).
The remaining construal, exhaustifying the not-throughout claim (148b), makes the predicate hold
throughout every proper subinterval, (142), which is contradictory once overlapping events
sum. -/

section Imperfective

variable {V : Type*} {P : V → E → Prop} {τ : NonemptyInterval T}

/-- Exhaustifying the throughout claim is vacuous, (137) with (144), and (139) with (141) for the
negated event predicate. -/
theorem throughout_exh_vacuous :
    exh (domainAlternatives (UNBOUNDED P) τ) {v | τ ∈ UNBOUNDED P v} = {v | τ ∈ UNBOUNDED P v} :=
  exh_domainAlternatives_eq_self fun v ↦ isLowerSet_unbounded P v

/-- Where every extension is available and the event domain is rich, the not-throughout claim at
one span entails it at another exactly when the second contains the first, (142). -/
theorem not_unbounded_subset_iff (hP : Function.Surjective P)
    (hrich : Function.Surjective (Event.τ : E → NonemptyInterval T)) {τ₁ τ₂ : NonemptyInterval T} :
    {v | τ₁ ∉ UNBOUNDED P v} ⊆ {v | τ₂ ∉ UNBOUNDED P v} ↔ τ₁ ≤ τ₂ := by
  refine ⟨fun h ↦ ?_, fun h _ hn ⟨e, he, hv⟩ ↦ hn ⟨e, h.trans he, hv⟩⟩
  obtain ⟨v, hv⟩ := hP (Event.τ · = τ₂)
  obtain ⟨e₀, he₀⟩ := hrich τ₂
  by_contra hle
  exact h (a := v) (fun ⟨e, he, heq⟩ ↦ hle ((congrFun hv e).mp heq ▸ he))
    ⟨e₀, he₀.ge, (congrFun hv e₀).mpr he₀⟩

theorem mem_exh_not_unbounded_iff (hP : Function.Surjective P)
    (hrich : Function.Surjective (Event.τ : E → NonemptyInterval T)) {v : V} :
    v ∈ exh (domainAlternatives (fun v ↦ (UNBOUNDED P v)ᶜ) τ) {v | τ ∉ UNBOUNDED P v} ↔
      τ ∉ UNBOUNDED P v ∧ ∀ τ' < τ, τ' ∈ UNBOUNDED P v :=
  (mem_exh_domainAlternatives_iff (p := fun v ↦ (UNBOUNDED P v)ᶜ)
    fun _ _ ↦ not_unbounded_subset_iff hP hrich).trans <| by simp

theorem unbounded_of_forall_lt {v : V}
    (hsum : ∀ e₁ e₂, P v e₁ → P v e₂ → (Event.τ e₁).Overlaps (Event.τ e₂) →
      ∃ e, P v e ∧ Event.τ e₁ ≤ Event.τ e ∧ Event.τ e₂ ≤ Event.τ e)
    {m : T} (hm₁ : τ.fst < m) (hm₂ : m < τ.snd) (h : ∀ τ' < τ, τ' ∈ UNBOUNDED P v) :
    τ ∈ UNBOUNDED P v := by
  obtain ⟨e₁, he₁, hP₁⟩ := h ⟨(τ.fst, m), hm₁.le⟩
    (lt_of_le_of_ne (le_def.2 ⟨le_rfl, hm₂.le⟩) fun heq ↦ hm₂.ne (congrArg (·.snd) heq))
  obtain ⟨e₂, he₂, hP₂⟩ := h ⟨(m, τ.snd), hm₂.le⟩
    (lt_of_le_of_ne (le_def.2 ⟨hm₁.le, le_rfl⟩) fun heq ↦ hm₁.ne' (congrArg (·.fst) heq))
  obtain ⟨he₁f, he₁s⟩ := le_def.1 he₁
  obtain ⟨he₂f, he₂s⟩ := le_def.1 he₂
  obtain ⟨e, hP, h₁, h₂⟩ := hsum e₁ e₂ hP₁ hP₂
    ⟨(he₁f.trans hm₁.le).trans (hm₂.le.trans he₂s), he₂f.trans he₁s⟩
  exact ⟨e, le_def.2 ⟨(le_def.1 h₁).1.trans he₁f, he₂s.trans (le_def.1 h₂).2⟩, hP⟩

/-- With an imperfective predicate the construal exhaustifying the not-throughout claim, (148b), is
contradictory, (142). -/
theorem not_throughout_exh_contradictory (hP : Function.Surjective P)
    (hrich : Function.Surjective (Event.τ : E → NonemptyInterval T)) {v : V}
    (hsum : ∀ e₁ e₂, P v e₁ → P v e₂ → (Event.τ e₁).Overlaps (Event.τ e₂) →
      ∃ e, P v e ∧ Event.τ e₁ ≤ Event.τ e ∧ Event.τ e₂ ≤ Event.τ e)
    {m : T} (hm₁ : τ.fst < m) (hm₂ : m < τ.snd) :
    v ∉ exh (domainAlternatives (fun v ↦ (UNBOUNDED P v)ᶜ) τ) {v | τ ∉ UNBOUNDED P v} :=
  fun h ↦
    let ⟨hn, hall⟩ := (mem_exh_not_unbounded_iff hP hrich).1 h
    hn (unbounded_of_forall_lt hsum hm₁ hm₂ hall)

end Imperfective

/-! ### Against the lexical ambiguity of *until*

The ambiguity account must deny that negation yields the subinterval property, Section 5.2.2:
otherwise its durative *until* takes a negated perfective on the throughout-not reading, which has
no actuality inference, and *She did not leave until 5 p.m. and maybe she didn't leave at all*,
(83), would not be a contradiction. Greek, Section 5.2.1.1, offers no separate punctual *until*:
*para mono* is the exceptive 'but only', and *Dhen thimose para mono htes* 'he didn't get angry
except yesterday', (69), means what the punctual *until* is said to mean. -/

section Ambiguity

variable {P : W → E → Prop} {w : W}

/-- The durative *until* of [giannakidou-2002] accepts a negated perfective, which has the
subinterval property, in a model with no relevant event at all. -/
theorem two_until_overgenerates (hP : ∀ e, ¬ P w e) {s t : T} (h : s < t) :
    Giannakidou2002.durativeUntil (fun w ↦ (PRFV P w)ᶜ) w t :=
  (Giannakidou2002.durativeUntil_iff_of_isLowerSet (isLowerSet_compl_prfv P w) t).2
    ⟨⟨(s, t), h.le⟩, fun ⟨e, _, he⟩ ↦ hP e he, h, rfl⟩

/-- *No time but `t₀` is a time of a `P`-event*, the exceptive of *dhen … para mono* with a
temporal argument on the least-exception semantics, says that `t₀` is the only such time, which
entails the punctual *until* of [giannakidou-2002], the event at `t₀` included. -/
theorem eventiveUntil_of_exceptive {t₀ : T}
    (h : Quantifier.Exceptive.IsExceptionSet .no ⊤ (· = t₀) fun t ↦ ∃ e, P w e ∧ t ∈ Event.τ e) :
    Giannakidou2002.eventiveUntil P w t₀ := by
  have key : ∀ t, (∃ e, P w e ∧ t ∈ Event.τ e) ↔ t = t₀ := fun t ↦ by
    simpa using congrFun (Quantifier.Exceptive.isExceptionSet_no_iff.1 h) t
  exact ⟨(key t₀).2 rfl,
    fun e hP ↦ ((key _).1 ⟨e, hP, mem_def.2 ⟨le_rfl, (Event.τ e).fst_le_snd⟩⟩).ge⟩

end Ambiguity

/-! ### Setting the right boundary

The argument of *until* contains a definite description over intervals, which picks the
maximally informative interval as von Fintel, Fox and Iatridou have definites do, so the right
boundary is the first moment at which the argument clause holds of a span ending there. A
perfective argument, *until she read Anna Karenina*, (170)–(171), sets it at the completion of
the reading, an imperfective one, *until she was working at the grocery store*, (172)–(175), at
the onset. -/

section RightBoundary

variable {Q : W → E → Prop} {w : W} {e : E}

/-- A perfective argument clause sets the right boundary at the completion of its first event. -/
theorem isLeast_rightBoundaries_prfv (he : Q w e)
    (hfirst : ∀ e', Q w e' → (Event.τ e).snd ≤ (Event.τ e').snd) :
    IsLeast ((·.snd) '' PRFV Q w) (Event.τ e).snd :=
  ⟨⟨Event.τ e, ⟨e, le_rfl, he⟩, rfl⟩,
    fun _ ⟨_, ⟨e', hle, he'⟩, hτ⟩ ↦ hτ ▸ (hfirst e' he').trans (le_def.1 hle).2⟩

/-- An imperfective argument clause sets the right boundary at the onset of its first event. -/
theorem isLeast_rightBoundaries_unbounded (he : Q w e)
    (hfirst : ∀ e', Q w e' → (Event.τ e).fst ≤ (Event.τ e').fst) :
    IsLeast ((·.snd) '' UNBOUNDED Q w) (Event.τ e).fst :=
  ⟨⟨.pure (Event.τ e).fst, ⟨e, le_def.2 ⟨le_rfl, (Event.τ e).fst_le_snd⟩, he⟩, rfl⟩,
    fun _ ⟨τ, ⟨e', hle, he'⟩, hτ⟩ ↦
      hτ ▸ ((hfirst e' he').trans (le_def.1 hle).1).trans τ.fst_le_snd⟩

end RightBoundary

end IatridouZeijlstra2021
