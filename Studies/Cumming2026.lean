module

public import Linglib.Fragments.Korean.Evidentiality
public import Linglib.Semantics.Tense.Evidential
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Data.Examples.Cumming2026

/-!
# Cumming (2026): Tense and evidence

This file formalizes Cumming's answer to Ninan's puzzle, that a future-tense sentence
can be asserted on prior inferential grounds while the past-tense sentence about the same
event cannot. Cumming, amending Cariani, assigns the nonfuture tenses the non-truth-conditional
constraint that the speaker's evidence be downstream of the event, and the future forms no
such constraint. A cell of a tense-evidential paradigm constrains three relations of the
frame, the evidential perspective, of the event to the acquisition of the evidence, the
relation of the acquisition to speech, and the utterance perspective, of the event to speech,
each a cell of the tense partition. Under the Korean evidentials *-te* and *-ney* of Lee and
the Bulgarian *-l* of Koev, the evidential fixes the relation of the acquisition to speech and
the tense the evidential perspective, and the utterance perspective is the composition of the
two; the English nonfuture tenses fix the utterance perspective and carry the downstream
constraint, and the past- and present-directed *will* forms of Winans restrict the evidence
to the prospective.

We derive the utterance-perspective columns of the paper's tables by composing cells, show
that the nonfuture cells of all three languages require downstream evidence, that no true
future can, and that the prospective cells lie beyond Cariani's obviation, and check the
paper's felicity judgments against the cells on the frames its scenarios fix, with planned
events exempt.

## Implementation notes

* The constraints are read temporally, as in the paper's tables; Cumming's own constraint is
  causal, and cases turning on the difference, as the rewatched film of footnote 9, are not
  represented.
* Koev distinguishes a null past and a null present tense under *-l*; Cumming's nonfuture cell
  is their join, and a frame satisfies it exactly when it satisfies one of Koev's two.
* The printed table (22) gives *will have* the utterance perspective T > S; the text and the
  example of the Fed's meeting require a past event, recorded here.

## References

* [S. Cumming, *Tense and evidence* (2026)][cumming-2026]
* [D. Ninan, *Assertion, evidence, and the future* (2022)][ninan-2022]
* [F. Cariani, *The modal future* (2021)][cariani-2021]
* [F. Cariani, *Future-past asymmetries, evidential grounding, and projection*
  (2022)][cariani-2022]
* [J. Lee, *Evidentiality and its interaction with tense: evidence from Korean*
  (2011)][lee-2011]
* [J. Lee, *Temporal constraints on the meaning of evidentiality* (2013)][lee-2013]
* [T. Koev, *Evidentiality, learning events and spatiotemporal distance* (2017)][koev-2017]
* [L. Winans, *Inferences of will* (2016)][winans-2016]
* [S. Cumming, L. Winans, *Counterfactuals and abduction* (2021)][cumming-winans-2021]
* [L. Matthewson, *Evidence type, evidence location, evidence strength*
  (2020)][matthewson-2020]
-/

@[expose] public section

namespace Cumming2026

open scoped Denotes

open Tense Tense.EvidentialFrame

variable {T : Type*} [LinearOrder T]

/-! ### Paradigm cells

A cell of a tense-evidential paradigm is a constraint on the evidential frame
(`Tense.EvidentialFrame.Constraint`): it restricts the evidential perspective, the relation of
the event to the acquisition of the evidence, the relation of the acquisition to speech, and
the utterance perspective, the relation of the event to speech, `⊤` where the paradigm leaves a
relation open. -/

open Classical in
/-- The meaning of a cell at a frame presupposes the constraints and asserts the content, so the
constraint is not part of what is asserted. -/
noncomputable def meaning {W : Type*} (c : Constraint) (f : EvidentialFrame T) (φ : W → Prop) :
    W → SignType :=
  {_w | c.Holds f}.indicator fun w ↦ SignType.ofProp (φ w)

/-- An evidential fixes the relation of the acquisition of the evidence to speech and turns
the tense it combines with into a constraint on the evidential perspective (§3). -/
def evidential (acquisition tense : Finset Ordering) : Constraint :=
  { eventToAcquisition := tense, acquisitionToSpeech := acquisition }

theorem holds_evidential_sup {a t t' : Finset Ordering} {f : EvidentialFrame T} :
    (evidential a (t ⊔ t')).Holds f ↔ (evidential a t).Holds f ∨ (evidential a t').Holds f :=
  Constraint.holds_eventToAcquisition_sup (c := evidential a t)

/-! ### The paradigms (§2 to §4) -/

/-- Korean *-te*, sensory evidence acquired in the past of speech ((13), (18)), the acquisition
cell of the lexical *-te*. -/
def te : Finset Ordering → Constraint := evidential Korean.Evidentiality.te.acquisitionToSpeech

/-- Korean *-ney*, sensory evidence acquired at speech ((14), (19)), the acquisition cell of the
lexical *-ney*. -/
def ney : Finset Ordering → Constraint := evidential Korean.Evidentiality.ney.acquisitionToSpeech

/-- Bulgarian *-l*, indirect evidence acquired by the time of speech ((15) to (17)). -/
def l : Finset Ordering → Constraint := evidential ⟦future⟧ᶜ

/-- The English simple past requires downstream evidence for a past event ((20)). -/
def simplePast : Constraint := { eventToAcquisition := ⟦future⟧ᶜ, eventToSpeech := ⟦past⟧ }

/-- The English present progressive requires downstream evidence for a present event ((20)). -/
def presentProgressive : Constraint :=
  { eventToAcquisition := ⟦future⟧ᶜ, eventToSpeech := ⟦present⟧ }

/-- The English future *will* places no evidential constraint on a future event ((20)). -/
def will : Constraint := { eventToSpeech := ⟦future⟧ }

/-- The past-directed *will have* requires prospective evidence for a past event ((22)). -/
def willHave : Constraint := { eventToAcquisition := ⟦future⟧, eventToSpeech := ⟦past⟧ }

/-- The present-directed *will now* requires prospective evidence for a present event ((22)). -/
def willNow : Constraint := { eventToAcquisition := ⟦future⟧, eventToSpeech := ⟦present⟧ }

/-! ### The utterance perspective derived (§3)

Under *-te* and *-ney* the tense fixes the evidential perspective and the evidential the
relation of the acquisition to speech, and the utterance-perspective columns of tables (18)
and (19) are compositions; under *-l* the same holds of table (17), whose nonfuture cell is
the join of Koev's null past and null present. -/

theorem te_past_derived : (te ⟦past⟧).derived = ⟦past⟧ := comp_past_past

theorem te_present_derived : (te ⟦present⟧).derived = ⟦past⟧ := comp_present_left _

theorem te_future_derived : (te ⟦future⟧).derived = ⊤ := comp_future_past

theorem ney_past_derived : (ney ⟦past⟧).derived = ⟦past⟧ := comp_present_right _

theorem ney_present_derived : (ney ⟦present⟧).derived = ⟦present⟧ := comp_present_right _

theorem ney_future_derived : (ney ⟦future⟧).derived = ⟦future⟧ := comp_present_right _

-- (17)
theorem l_nonfuture_derived : (l ⟦future⟧ᶜ).derived = ⟦future⟧ᶜ :=
  comp_compl_future_compl_future

-- (16)
theorem l_future_derived : (l ⟦future⟧).derived = ⊤ := by
  show comp ⟦future⟧ ⟦future⟧ᶜ = ⊤
  rw [← past_sup_present, comp_sup_right]
  simp

-- footnote 7
theorem holds_l_nonfuture_iff {f : EvidentialFrame T} :
    (l ⟦future⟧ᶜ).Holds f ↔ (l ⟦past⟧).Holds f ∨ (l ⟦present⟧).Holds f := by
  rw [← past_sup_present]
  exact holds_evidential_sup

/-! ### Downstream evidence, obviation and the true future (§5, §7) -/

-- (10)
theorem nonfuture_downstream {f : EvidentialFrame T} :
    ∀ c ∈ [simplePast, presentProgressive, te ⟦past⟧, te ⟦present⟧, ney ⟦past⟧, ney ⟦present⟧,
      l ⟦future⟧ᶜ], c.Holds f → f.Downstream := fun c hc ↦
  Constraint.downstream_of_holds (by revert c; decide)

-- §5
theorem prospective_beyond_obviation :
    ∀ c ∈ [te ⟦future⟧, ney ⟦future⟧, l ⟦future⟧, willHave, willNow],
      c.eventToAcquisition ≠ ⟦future⟧ᶜ ∧ c.eventToAcquisition ≠ ⊤ := by
  decide

-- §7
theorem speechTime_lt_acquisitionTime {f : EvidentialFrame T}
    (h : (⟨⟦future⟧ᶜ, ⊤, ⟦future⟧⟩ : Constraint).Holds f) : f.speechTime < f.acquisitionTime :=
  lt_of_lt_of_le ((compare_mem_future _ _).1 h.2.2) ((compare_mem_compl_future _ _).1 h.1)

-- (23)
theorem willHave_meaning_eq_simplePast_meaning {W : Type*} {f f' : EvidentialFrame T}
    (φ : W → Prop) (h : willHave.Holds f) (h' : simplePast.Holds f') :
    meaning willHave f φ = meaning simplePast f' φ := by
  funext w
  simp [meaning, h, h']

/-! ### The felicity judgments -/

/-- The cell a row's `form` feature names. -/
def cell? (e : Datum) : Option Constraint :=
  e.parse? "form"
    [("simple past", simplePast), ("present progressive", presentProgressive),
      ("future (will)", will), ("will have V-ed", willHave), ("will now be V-ing", willNow),
      ("-te PAST", te ⟦past⟧), ("-te PRES", te ⟦present⟧), ("-te FUT", te ⟦future⟧),
      ("-ney PAST", ney ⟦past⟧), ("-ney PRES", ney ⟦present⟧), ("-ney FUT", ney ⟦future⟧),
      ("NFUT + -l", l ⟦future⟧ᶜ), ("FUT + -l", l ⟦future⟧)]

/-- The frame a row's scenario fixes. -/
def frame? (e : Datum) : Option (EvidentialFrame ℤ) := do
  let s ← e.nat? "speechTime"
  let a ← e.nat? "acquisitionTime"
  let t ← e.nat? "eventTime"
  pure { speechTime := s, eventTime := t, acquisitionTime := a }

/-- The row describes a planned or scheduled event (§6). -/
def Scheduled (e : Datum) : Prop := e.feature? "scheduled" = some "true"

instance : DecidablePred Scheduled := fun _ ↦ inferInstanceAs (Decidable (_ = _))

theorem cell?_frame?_isSome : ∀ e ∈ Examples.all, (cell? e).isSome ∧ (frame? e).isSome := by
  decide

-- §6
theorem judgment_iff : ∀ e ∈ Examples.all, ∀ c ∈ cell? e, ∀ f ∈ frame? e,
    (e.JudgedFelicitous ↔ Scheduled e ∨ c.Holds f) := by
  decide

end Cumming2026
