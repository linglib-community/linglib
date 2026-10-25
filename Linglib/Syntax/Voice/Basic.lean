module

public import Linglib.Syntax.Voice.Construction
public import Linglib.Morphology.Morph

/-!
# Voice

A *voice* relates an initial and a derived diathesis of a verb's participants, and so an initial
and a derived construction (`Syntax/Voice/Construction.lean`). It also records its *pivot*, the
syntactically privileged derived term, and its *marker*, the morphs coding it on the verb. A
voice realizes a type of voice alternation when its two constructions do, and the voices defined
here realize the types they are named for.

## Main definitions

* `Voice`, `Voice.of`: an initial and a derived diathesis, with a pivot and a marker.
* `Voice.IsPassivization`, `IsAntipassivization`, `IsDecausativization`, …: a voice realizing a
  type of voice alternation.
* `Voice.Relates`, `Verb.Alternates`: a voice relating two diatheses of a verb.
* `Verb.formIn`, `Verb.Marks`: the verb's form in a diathesis, and a voice the verb's form marks.
* `Voice.passive`, `antipassive`, `anticausative`, `causative`, `reflexive`, `applicative`,
  `patientVoice`, `obliqueVoice`, `leaveImplicit`: the voices.

## Main statements

* `Voice.isAntipassivization_antipassive_iff`: the antipassive is an antipassivization exactly
  when it keeps the initial P in participant structure without making it a core term.
* `Voice.passive_isPassivization`, `Voice.anticausative_isDecausativization`: the voices realize
  their types.
* `Voice.isSymmetrical_refl`: the trivial voice neither nucleativizes nor denucleativizes.

## Implementation notes

* Participants are numbered as a verb's are: those of the initial frame's slots in order, then
  those the voice adds. A participant the derived diathesis leaves out is suppressed.

## References

* [comrie-1989]
* [creissels-2024]
* [dixon-1994]
* [dixon-aikhenvald-2000]
* [fillmore-1986]
* [levin-1993]
* [song-1996]
-/

@[expose] public section

namespace Voice

/-! ### Coding -/

/-- A voice is coded on the verb by verbal morphology, by an analytic construction, or not at
all, like the unmarked voice of a system or a flexivalent alternation ([creissels-2024]
§1.1.3). Equipollence is a property of a system, `Voice.System.IsEquipollent`. -/
inductive Coding where
  | synthetic
  | analytic
  | uncoded
  deriving DecidableEq, Repr

/-- A marker is uncoded when empty, synthetic when every morph is bound, and analytic
otherwise. -/
def Coding.ofMarker (ms : List Morphology.Morph) : Coding :=
  if ms = [] then .uncoded
  else if ms.all fun m ↦ m.kind.position?.isSome then .synthetic
  else .analytic

end Voice

/-- A voice relates an initial and a derived diathesis of its participants, privileges a slot of
the derived diathesis as its pivot, and is coded by a marker on the verb; its classification is
computed from the two diatheses. -/
structure Voice where
  /-- The number of participants. -/
  arity : ℕ
  /-- The initial diathesis. -/
  initial : Diathesis arity
  /-- The derived diathesis, which leaves out the participants the voice suppresses. -/
  derived : Diathesis arity
  /-- The syntactically privileged term of the derived construction is by default its first core
  slot (S or A), unless a symmetrical voice selects another, and is `none` for an impersonal
  construction ([creissels-2024] §8.1.7). -/
  pivot : Option ArgumentFrame.Slot := derived.coreSlots.head?
  /-- The morphs (affixes or an auxiliary) coding the voice on the verb, in surface order; empty
      for a zero-marked or an unmarked voice. -/
  marker : List Morphology.Morph := []
  deriving DecidableEq, Repr

namespace Voice

open ArgumentFrame (Slot)

/-- The voice from frame `fr` to frame `gr`. Its participants are those of the slots of `fr`, in
order, followed by those the voice adds; `links` gives each participant's slot in `gr`, or `none`
if `gr` leaves it out. -/
def of (fr gr : ArgumentFrame) (links : List (Option Slot)) : Voice where
  arity := links.length
  initial := { fr with links := .ofFn fun i ↦ fr.slots[i.val]? }
  derived := { gr with links := ⟨links.toArray, List.size_toArray⟩ }

variable (v : Voice)

/-! ### The participants of a voice -/

/-- The derived slot of the participant of an initial slot. -/
def image (s : Slot) : Option Slot := (v.initial.participantAt s).bind v.derived.links.get

/-- The initial slots whose participant occupies a derived slot. -/
def preimages (t : Slot) : List Slot := v.initial.slots.filter fun s ↦ v.image s == some t

/-- The derived slots of the participants the voice adds. -/
def newSlots : List Slot :=
  (List.finRange v.arity).filterMap fun i ↦
    if v.initial.links.get i = none then v.derived.links.get i else none

/-- The fate of the participant of an initial slot. -/
def fate (s : Slot) : ParticipantFate :=
  (v.initial.participantAt s).elim .na (v.initial.construction.fate v.derived.construction)

/-- The fate of the initial core term with a transitivity-related role. -/
def fateOfRole (r : TermRole) : ParticipantFate :=
  (v.initial.coreSlots.find? fun s ↦
    (v.initial.argumentRole s).map TermRole.ofArgumentRole == some r).elim .na v.fate

/-- The role of the first participant the voice introduces, if one. -/
def newParticipant : Option TermRole :=
  ((List.finRange v.arity).find? fun i ↦
      v.initial.construction.Introduced v.derived.construction i).bind
    fun i ↦ (v.derived.construction i).role

/-- The transitivity-related role of the pivot is S, A or P for a core term and X for an
oblique. -/
def pivotRole : Option TermRole := v.pivot.bind fun t ↦ (v.derived.status t).role

/-! ### Classification -/

/-- Some participant becomes a core term. -/
abbrev Nucleativizes : Prop := v.initial.construction.Nucleativizes v.derived.construction

/-- Some initial core term ceases to be one. -/
abbrev Denucleativizes : Prop := v.initial.construction.Denucleativizes v.derived.construction

/-- Two initial core terms are cumulated. -/
abbrev Cumulates : Prop := v.initial.construction.Cumulates v.derived.construction

/-- A voice is valency-increasing when it nucleativizes without denucleativizing. -/
abbrev IsValencyIncreasing : Prop :=
  v.initial.construction.IsValencyIncreasing v.derived.construction

/-- A voice is valency-decreasing when it denucleativizes without nucleativizing. -/
abbrev IsValencyDecreasing : Prop :=
  v.initial.construction.IsValencyDecreasing v.derived.construction

/-- A voice is symmetrical when it neither nucleativizes nor denucleativizes and keeps the
transitivity of the construction. -/
abbrev IsSymmetrical : Prop := v.initial.construction.IsSymmetrical v.derived.construction

/-- A voice is a passivization when its two constructions are. -/
abbrev IsPassivization : Prop := v.initial.construction.IsPassivization v.derived.construction

/-- A voice is an I-passivization when its two constructions are. -/
abbrev IsImpersonalPassivization : Prop :=
  v.initial.construction.IsImpersonalPassivization v.derived.construction

/-- A voice is an antipassivization when its two constructions are. -/
abbrev IsAntipassivization : Prop :=
  v.initial.construction.IsAntipassivization v.derived.construction

/-- A voice is an S-denucleativization when its two constructions are. -/
abbrev IsSDenucleativization : Prop :=
  v.initial.construction.IsSDenucleativization v.derived.construction

/-- A voice is a decausativization when its two constructions are. -/
abbrev IsDecausativization : Prop :=
  v.initial.construction.IsDecausativization v.derived.construction

/-- A voice is a reflexivization or reciprocalization when its two constructions cumulate two
roles in one S. -/
abbrev IsCumulation : Prop := v.initial.construction.IsCumulation v.derived.construction

/-- A voice is an A/S-nucleativization when its two constructions are, of some participant. -/
abbrev IsASNucleativization : Prop :=
  ∃ i, v.initial.construction.IsASNucleativization v.derived.construction i

/-- A voice is a P-applicativization when its two constructions are, of some participant. -/
abbrev IsPApplicativization : Prop :=
  ∃ i, v.initial.construction.IsPApplicativization v.derived.construction i

/-- The pivot is an oblique, which a binary system does not allow ([creissels-2024] §8.5.2). -/
def SelectsOblique : Prop := v.pivotRole = some .X

/-- A voice is impersonal when its derived construction privileges no term, so it has no pivot
([creissels-2024] §8.3.2.2). A frame without a subject still codes its objects as core terms, so
an impersonal construction keeps its P. -/
def IsImpersonal : Prop := v.pivot = none

/-- The coding type of the voice is synthetic if every morph of its marker is bound, analytic if a
free morph (an auxiliary) is among them, and uncoded if the marker is empty ([creissels-2024]
§1.1.3). -/
def coding : Coding := .ofMarker v.marker

/-- A voice is coded when it is marked on the verb, as against a flexivalent alternation
([creissels-2024] §1.1.3). -/
def IsCoded : Prop := v.marker ≠ []

instance : Decidable v.SelectsOblique := inferInstanceAs (Decidable (_ = _))
instance : Decidable v.IsImpersonal := inferInstanceAs (Decidable (_ = _))
instance : Decidable v.IsCoded := inferInstanceAs (Decidable (_ ≠ _))

/-! ### Marking -/

/-- The voice with the given marker. A fragment states a voice with its marker, as in
`Voice.passive.marked [.suff "x"]`; the bare constants are unmarked. -/
def marked (ms : List Morphology.Morph) : Voice := { v with marker := ms }

@[simp] theorem marker_marked (ms : List Morphology.Morph) : (v.marked ms).marker = ms := rfl

@[simp] theorem coding_marked (ms : List Morphology.Morph) :
    (v.marked ms).coding = .ofMarker ms := rfl

@[simp] theorem fateOfRole_marked (ms : List Morphology.Morph) (r : TermRole) :
    (v.marked ms).fateOfRole r = v.fateOfRole r := rfl

@[simp] theorem newParticipant_marked (ms : List Morphology.Morph) :
    (v.marked ms).newParticipant = v.newParticipant := rfl

theorem coding_eq_uncoded_iff : v.coding = .uncoded ↔ v.marker = [] := by
  unfold coding Coding.ofMarker
  split_ifs <;> simp_all

theorem isCoded_iff : v.IsCoded ↔ v.coding ≠ .uncoded := by
  rw [IsCoded, Ne, Ne, coding_eq_uncoded_iff]

variable {v}

/-! ### The trivial voice -/

/-- The trivial voice of a frame with itself is the initial construction of a system. -/
def refl (fr : ArgumentFrame) : Voice := of fr fr (fr.slots.map some)

theorem derived_refl (fr : ArgumentFrame) : (refl fr).derived = (refl fr).initial := by
  simp only [refl, of, Diathesis.mk.injEq, true_and, and_true]
  ext m hm
  simp only [List.length_map] at hm
  simp [List.getElem?_eq_getElem hm]

theorem isSymmetrical_refl (fr : ArgumentFrame) : (refl fr).IsSymmetrical := by
  show Construction.IsSymmetrical _ _
  rw [derived_refl]
  exact Construction.isSymmetrical_self _

/-! ### The voices -/

open ArgumentFrame.Slot

/-- The active is the initial transitive construction. -/
def active : Voice := refl .np

/-- The agent voice of a symmetrical system, with the agent the pivot, is the active. -/
abbrev agentVoice : Voice := active

/-- The passive of a frame with a complement (by default the transitive frame). It makes the first
complement the subject and pivot, and denucleativizes the external argument while keeping it in
participant structure, implied here and expressed as an oblique in a long passive ([creissels-2024]
§8.3.2.1). -/
def passive (fr : ArgumentFrame := .np) : Voice :=
  of fr ⟨some .nominal, fr.complements.tail ++ [.implicit]⟩ <|
    some (complement (fr.complements.length - 1)) :: some external ::
      (List.range (fr.complements.length - 1)).map (some ∘ complement)

/-- The impersonal passive denucleativizes the external argument as the passive does but leaves
the complements in place, with no subject. The initial P keeps its coding and the derived
construction has no pivot ([creissels-2024] §8.3.2.2). Applied to an intransitive frame, it
denucleativizes the S (§8.3.2.4). -/
def impersonalPassive (fr : ArgumentFrame := .np) : Voice :=
  { of fr ⟨none, fr.complements ++ [.implicit]⟩ <|
      some (complement fr.complements.length) ::
        (List.range fr.complements.length).map (some ∘ complement) with pivot := none }

/-- The antipassive denucleativizes the initial P and makes the initial A the S of an
intransitive construction ([creissels-2024] §8.3.2.3). The derived construction has the initial
P at position `p`: an oblique by default, an implicit argument, or an incorporated noun
(§10.2). -/
def antipassive (p : ArgumentFrame.Position := .adpositional) : Voice :=
  of .np ⟨some .nominal, [p]⟩ [some external, some (complement 0)]

/-- The voice that leaves the `i`-th complement of `fr` unexpressed but implied, with
interpretation `a`; every participant keeps its slot. Examples are Fillmore's null complements and
Levin's unexpressed object alternations. -/
def leaveImplicit (fr : ArgumentFrame) (i : ℕ) (a : Option ImplicitInterp := none) : Voice :=
  of fr (fr.leaveImplicit i a) (fr.slots.map some)

/-- The anticausative suppresses the initial A from participant structure and makes the
initial P the S of an intransitive construction, [creissels-2024]'s decausativization
(§8.3.1.2). -/
def anticausative : Voice := of .np .intransitive [none, some external]

/-- The causative nucleativizes a causer as the A of a transitive construction whose P is the
initial S ([creissels-2024] §8.3.1.1). -/
def causative : Voice := of .intransitive .np [some (complement 0), some external]

/-- The reflexive cumulates the initial A and P in one S, an individual bearing both roles
([creissels-2024] §8.3.3). The object is left implicit, understood as the subject itself. -/
def reflexive : Voice := leaveImplicit .np 0 (some .reflexive)

/-- The reciprocal cumulates the initial A and P in one S, a group whose members bear both roles
toward one another ([creissels-2024] §8.3.3). The object is left implicit, understood as the
subject's members. -/
def reciprocal : Voice := leaveImplicit .np 0 (some .reciprocal)

/-- The applicative nucleativizes an applied participant as a second P beside the initial A
and P ([creissels-2024] §8.3.5). -/
def applicative : Voice :=
  of .np .np_np [some external, some (complement 0), some (complement 1)]

/-- The patient voice of a symmetrical system leaves the transitive construction unchanged and
makes the patient the pivot ([creissels-2024] §8.5.1). -/
def patientVoice : Voice := { refl .np with pivot := some (complement 0) }

/-- An oblique voice of a multiple symmetrical system leaves the transitive construction with
an oblique marking a case of type `r` unchanged and makes the oblique the pivot
([creissels-2024] §8.5.2). -/
def obliqueVoice (r : Case.Kind) : Voice :=
  { refl ⟨some .nominal, [.nominal, .adpositional (some r)]⟩ with pivot := some (complement 1) }

/-- The locative voice is the oblique voice of a spatial oblique. -/
abbrev locativeVoice : Voice := obliqueVoice .spatial

/-! ### Properties of the voices -/

theorem causative_isValencyIncreasing : causative.IsValencyIncreasing := by decide

theorem anticausative_isValencyDecreasing : anticausative.IsValencyDecreasing := by decide

theorem passive_isValencyDecreasing : passive.IsValencyDecreasing := by decide

/-- The passive maintains the initial A in participant structure; the anticausative
suppresses it ([creissels-2024] §8.3.2.1). -/
theorem passive_anticausative_fate :
    passive.fateOfRole .A = .denucleativized ∧ anticausative.fateOfRole .A = .suppressed := by
  decide

theorem impersonalPassive_isImpersonal (fr : ArgumentFrame) :
    (impersonalPassive fr).IsImpersonal := rfl

theorem passive_not_isImpersonal : ¬ passive.IsImpersonal := by decide

theorem antipassive_isValencyDecreasing : antipassive.IsValencyDecreasing := by decide

theorem passive_isPassivization : passive.IsPassivization := by decide

theorem impersonalPassive_isImpersonalPassivization :
    impersonalPassive.IsImpersonalPassivization := by
  decide

theorem impersonalPassive_intransitive_isSDenucleativization :
    (impersonalPassive .intransitive).IsSDenucleativization := by
  decide

theorem anticausative_isDecausativization : anticausative.IsDecausativization := by decide

theorem causative_isASNucleativization : causative.IsASNucleativization := by decide

theorem reflexive_isCumulation : reflexive.IsCumulation := by decide

theorem reciprocal_isCumulation : reciprocal.IsCumulation := by decide

theorem applicative_isPApplicativization : applicative.IsPApplicativization := by decide

/-- The antipassive is an antipassivization exactly when the derived construction keeps the
initial P in participant structure without making it a core term. -/
theorem isAntipassivization_antipassive_iff (p : ArgumentFrame.Position) :
    (antipassive p).IsAntipassivization ↔ (antipassive p).fateOfRole .P = .denucleativized := by
  cases p <;> first
    | exact of_decide_eq_true rfl
    | rename_i a; rcases a with _ | (_ | _ | _ | _ | _) <;> decide

/-- The antipassive is an antipassivization whether the derived construction encodes the initial
P as an oblique, leaves it implicit or incorporates it ([creissels-2024] §10.2); when the implicit
P is understood as the subject itself it is a reflexivization instead. -/
theorem antipassive_isAntipassivization :
    antipassive.IsAntipassivization ∧ (antipassive (.implicit none)).IsAntipassivization ∧
      (antipassive .incorporated).IsAntipassivization ∧
      ¬ (antipassive (.implicit (some .reflexive))).IsAntipassivization ∧
      (antipassive (.implicit (some .reflexive))).IsCumulation := by
  decide

theorem reflexive_cumulates : reflexive.Cumulates := by decide

theorem reciprocal_cumulates : reciprocal.Cumulates := by decide

theorem reflexive_not_isSymmetrical : ¬ reflexive.IsSymmetrical := by decide

theorem applicative_isValencyIncreasing : applicative.IsValencyIncreasing := by decide

theorem patientVoice_isSymmetrical : patientVoice.IsSymmetrical := isSymmetrical_refl _

theorem obliqueVoice_isSymmetrical (r : Case.Kind) :
    (obliqueVoice r).IsSymmetrical := isSymmetrical_refl _

theorem obliqueVoice_selectsOblique (r : Case.Kind) :
    (obliqueVoice r).SelectsOblique := by cases r <;> decide

/-! ### Alternating verbs -/

section Relates

variable {n : ℕ} (c d : Diathesis n)

/-- A voice relates two diatheses `c` and `d` of a verb when their frames refine its initial and
derived frames and each participant is placed as the voice says. A participant of an initial slot
goes to the voice's image of that slot, or out of the construction if there is none; a participant
that `c` leaves out goes, if anywhere, to a derived slot that is the image of no initial slot. -/
def Relates : Prop :=
  v.initial.toArgumentFrame ≤ c.toArgumentFrame ∧ v.derived.toArgumentFrame ≤ d.toArgumentFrame ∧
    ∀ i, (∀ s ∈ c.links.get i, d.links.get i = v.image s) ∧
      (c.links.get i = none → ∀ t ∈ d.links.get i, v.preimages t = [])

instance : Decidable (v.Relates c d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ _, _ ∧ _))

end Relates

/-- The verb alternates by `v` when the voice relates two of its diatheses. -/
def _root_.Verb.Alternates (w : Verb) (v : Voice) : Prop :=
  ∃ c ∈ w.valency.diatheses, ∃ d ∈ w.valency.diatheses, v.Relates c d

/-- Deciding the alternation skips a diathesis whose frame does not refine the initial one before
looking for a derived one. -/
instance (w : Verb) (v : Voice) : Decidable (w.Alternates v) :=
  decidable_of_iff (∃ c ∈ w.valency.diatheses, v.initial.toArgumentFrame ≤ c.toArgumentFrame ∧
      ∃ d ∈ w.valency.diatheses, v.Relates c d)
    ⟨fun ⟨c, hc, _, d, hd, h⟩ ↦ ⟨c, hc, d, hd, h⟩, fun ⟨c, hc, d, hd, h⟩ ↦ ⟨c, hc, h.1, d, hd, h⟩⟩

/-- The verb's form in a diathesis, the citation form unless the diathesis has its own. -/
def _root_.Verb.formIn (w : Verb) {n : ℕ} (d : Diathesis n) : List Morphology.Morph :=
  d.form.getD w.morphs

/-- The verb's form marks `v`: the voice relates two of its diatheses, and the derived one's form
is the initial one's with the voice's marker added. -/
def _root_.Verb.Marks (w : Verb) (v : Voice) : Prop :=
  ∃ c ∈ w.valency.diatheses, ∃ d ∈ w.valency.diatheses, v.Relates c d ∧
    (w.formIn c).Sublist (w.formIn d) ∧ (w.formIn d).Perm (w.formIn c ++ v.marker)

instance (w : Verb) (v : Voice) : Decidable (w.Marks v) :=
  inferInstanceAs (Decidable (∃ c ∈ w.valency.diatheses, ∃ d ∈ w.valency.diatheses, _ ∧ _ ∧ _))

theorem _root_.Verb.Marks.alternates {w : Verb} {v : Voice} (h : w.Marks v) : w.Alternates v :=
  let ⟨c, hc, d, hd, hr, _⟩ := h
  ⟨c, hc, d, hd, hr⟩

/-! ### Alignment -/

/-- The alignment of the core terms of transitive and intransitive clauses codes S like A or
like P ([creissels-2024] §1.3.4). -/
inductive Alignment where
  /-- S is coded like A, traditionally accusative. -/
  | A_alignment
  /-- S is coded like P, traditionally ergative. -/
  | P_alignment
  deriving DecidableEq, Repr

end Voice
