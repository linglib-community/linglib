module

public import Linglib.Semantics.Aspect.Telicity
public import Linglib.Semantics.ArgumentStructure.LevinClass.Properties
public import Linglib.Syntax.Cartography
public import Studies.TonhauserEtAl2013
public import Linglib.Data.Examples.HoleFraser2026
public import Mathlib.Data.Set.Card

/-!
# Hole and Fraser (2026): Syntax and semantics of the *swarm* alternation

In the non-base alternant of the *swarm* alternation, *the garden is swarming with bees*, a
pluractional swarming causes a state of the garden's inside being with bees, the garden being the
landmark of the swarming and binding the variable of the inside (69). The pluractional head (66)
asks for more atomic subevents than a contextual threshold, so the alternant is quasi-homogeneous,
true of every part of its events with enough atomic subevents and of no atom, and atelic, as the
*in* and *for* adverbials of (14) show. Locatum abundance is asserted and denied by a plain *no*,
while the alternant's scalarity and mirativity (71) are not at issue. Granting that they project,
their judgments in neutral contexts and in belief reports put them in the class of projective
content with obligatory local effect and no strong contextual felicity constraint. Scalarity
clashes with *even* under negation, which presupposes a low value, (38)–(40). The two contents
need heads above tense, so a non-base gerund projects to mirativity where a base one stops at
tense, and the adverbs only the former admits are those of the heads in between (§4). Levin's
class pages attest the alternation for six of the seven verb classes of (11).

## Main statements

* `not_isTelic_nonBase`: the non-base alternant is atelic.
* `denial_rows`: a plain *no* denies locatum abundance but not scalarity or mirativity.
* `nonBase_class_eq_C`: granting projection, the two contents have obligatory local effect and no
  strong contextual felicity constraint.
* `even_rows`: *not even* is good exactly with the base alternant, (38)–(40).
* `gerund_rows`: an adverb is good in a gerund exactly when its head is no higher than the gerund
  projects, (51)–(60).

## Implementation notes

* (66) counts the atomic proper parts of an event, here its atomic parts, the same above a
  threshold of one. Quasi-homogeneity takes the swarming to be quasi-homogeneous, the states of
  central coincidence (64) and the landmark relation to be divisive, and the parts of a causing
  event to cause parts of its state, as hypotheses; *with* is where the paper places homogeneity.
* Tonhauser, Beaver, Roberts and Simons classify projective contents, and the paper does not test
  projection, so the class is this file's inference. The contexts of (30)–(32), a normal count,
  are neutral about an unusually high one, and the sentences are read without *nur so*; (50a)'s
  "isn't a big deal" bears on remarkableness as much as on amount.
* Mirativity is just below Cinque's evaluative mood, the paper's "probably right below", and
  scalarity just above his past tense (§4.1); "continuative aspect I" is his continuative. Cinque
  pairs *surprisingly* with the evaluative mood, so (52)–(53) split his class. Future tense,
  irrealis mood and the alethic modals are below past tense, so *then*, *perhaps*, *possibly* and
  *necessarily* are predicted good in both gerunds.

## Errata

* In (67)–(69) the abundance condition counts the parts of `e′`, free once `e′` is reduced away;
  it is read as counting the parts of `e`. (67a) applies the one-place `v` to the PP and to the
  VP, which enters by event identification.
* The locatum enters (69) only through the result state, so theme abundance does not follow from
  event abundance as p. 24 says (`exists_nonBase_atom`); the route through (64) on p. 23 is open.
* (71) relativizes scalarity and mirativity to a parameter `S` read as the speaker, and leaves
  `w` free. (25) and (50) need the attitude holder's evaluation, and no denotation shifts `S`:
  with the holder's, (50b) is inconsistent (`not_subset_compl_of_image_subset`), with the
  speaker's it is not (`exists_speaker_consistent`).
* §4.2 has habitual aspect "immediately dominated by T", where Cinque puts future tense, irrealis
  mood and the alethic modals between. P. 24 dates Dowty's dynamic texture 2000, §3.2 2001, and
  (55) refers to §3.2.2 for §3.3.2. The bibliography dates Henderson's dissertation 2014 for
  2012, and "Dowty (2000: 2)" and "(2001: 6)" fall outside the page ranges it gives.

## TODO

* The *consider* test (25) as the discretionariness that `Studies/Coppock2018.lean` asks of
  *consider*, and the non-atomic locatum of (12) from central coincidence in a spatial model.

## References

* [hole-fraser-2026]
* [cinque-1999]
* [tonhauser-beaver-roberts-simons-2013]
* [krifka-1998]
* [levin-1993]
-/

@[expose] public section

namespace HoleFraser2026

open Mereology Aspect

/-! ### The non-base alternant, §5.2 -/

section Events

variable {E S L Y : Type*} [PartialOrder E]

/-- The pluractional head (66): the events of `f` with more than `θ` atomic parts. -/
def pluract (θ : ℕ∞) (f : E → Prop) (e : E) : Prop := f e ∧ θ < (atomsBelow e).encard

/-- The non-base alternant (69): a pluractional swarming that causes a state of the landmark's
inside and the locatum `y` being centrally coincident (64), the landmark `g`. -/
def nonBase (θ : ℕ∞) (swarm : E → Prop) (cause : S → E → Prop) (coincident : L → Y → S → Prop)
    (landmark : L → E → Prop) (g : L) (y : Y) (e : E) : Prop :=
  pluract θ swarm e ∧ (∃ s, coincident g y s ∧ cause s e) ∧ landmark g e

/-- A predicate is quasi-homogeneous (§3.2.2) when it is true of every part of its events with
more than `θ` atomic parts. -/
def IsQuasiHomogeneous (θ : ℕ∞) (P : E → Prop) : Prop :=
  ∀ ⦃e e'⦄, P e → e' ≤ e → θ < (atomsBelow e').encard → P e'

variable {θ : ℕ∞} {swarm : E → Prop} {cause : S → E → Prop} {coincident : L → Y → S → Prop}
  {landmark : L → E → Prop} {g : L} {y : Y}

theorem not_nonBase_of_atom (hθ : 1 ≤ θ) {e : E} (he : Atom e) :
    ¬ nonBase θ swarm cause coincident landmark g y e := by
  rintro ⟨⟨-, h⟩, -⟩
  rw [atomsBelow_of_atom he, Set.encard_singleton] at h
  exact (hθ.trans_lt h).false

theorem isQuasiHomogeneous_nonBase [Preorder S] (hs : IsQuasiHomogeneous θ swarm)
    (hw : DIV (coincident g y)) (hc : ∀ ⦃s e e'⦄, cause s e → e' ≤ e → ∃ s' ≤ s, cause s' e')
    (hl : DIV (landmark g)) :
    IsQuasiHomogeneous θ (nonBase θ swarm cause coincident landmark g y) := by
  rintro e e' ⟨⟨hse, -⟩, ⟨s, hws, hcs⟩, hle⟩ h h'
  obtain ⟨s', hs', hcs'⟩ := hc hcs h
  exact ⟨⟨hs hse h h', h'⟩, ⟨s', hw hs' hws, hcs'⟩, hl h hle⟩

theorem IsQuasiHomogeneous.not_isTelic {precedes : E → E → Prop} {P : E → Prop}
    (hP : IsQuasiHomogeneous θ P) {e e' e'' : E} (he : P e) (h' : e' ≤ e)
    (hθ : θ < (atomsBelow e').encard) (h'' : e'' ≤ e) (hp : precedes e' e'') :
    ¬ IsTelic precedes P :=
  fun hT ↦ (hT e e' he (hP he h' hθ) h').2.2 ⟨e'', h'', hp⟩

/-- (14), (21): the non-base alternant is atelic, by its quasi-homogeneity (§3.2.2). -/
theorem not_isTelic_nonBase [Preorder S] {precedes : E → E → Prop}
    (hs : IsQuasiHomogeneous θ swarm) (hw : DIV (coincident g y))
    (hc : ∀ ⦃s e e'⦄, cause s e → e' ≤ e → ∃ s' ≤ s, cause s' e') (hl : DIV (landmark g))
    {e e' e'' : E} (he : nonBase θ swarm cause coincident landmark g y e) (h' : e' ≤ e)
    (hθ : θ < (atomsBelow e').encard) (h'' : e'' ≤ e) (hp : precedes e' e'') :
    ¬ IsTelic precedes (nonBase θ swarm cause coincident landmark g y) :=
  (isQuasiHomogeneous_nonBase hs hw hc hl).not_isTelic he h' hθ h'' hp

end Events

theorem exists_nonBase_atom :
    ∃ y e : Finset ℕ, Atom y ∧ nonBase 1 (fun _ ↦ True) (fun (_ : Unit) _ ↦ True)
      (fun (_ : Unit) _ _ ↦ True) (fun _ _ ↦ True) () y e := by
  refine ⟨{0}, {0, 1}, atom_iff_isAtom.2 (Finset.isAtom_singleton 0), ⟨trivial, ?_⟩,
    ⟨(), trivial, trivial⟩, trivial⟩
  rw [atomsBelow_finset, (Finset.singleton_injective.injOn).encard_image]
  simp [Set.encard_pair]

/-! ### At-issue and projective content, §3.1 and §3.3 -/

open TonhauserEtAl2013

/-- The two alternants. -/
inductive Alternant
  | base
  | nonBase
  deriving DecidableEq, Repr

/-- The alternant of a row. -/
def alternantOf (d : Datum) : Option Alternant :=
  d.parse? "alternant" [("base", .base), ("nonBase", .nonBase)]

/-- The contents of the non-base alternant that the diagnostics target. -/
inductive Content
  | abundance
  | scalarity
  | mirativity
  deriving DecidableEq, Repr

/-- A content is at issue when (69) asserts it, as it does locatum abundance through the threshold
of (66); scalarity and mirativity are the definedness conditions of (71). -/
def Content.IsAtIssue (c : Content) : Prop := c = .abundance

instance : DecidablePred Content.IsAtIssue := fun c ↦ inferInstanceAs (Decidable (c = _))

/-- A reply to the alternant, a plain denial or *Hey, wait a minute*. -/
inductive Response
  | denial
  | waitAMinute
  deriving DecidableEq, Repr

/-- The content a row targets. -/
def contentOf (d : Datum) : Option Content :=
  d.parse? "content"
    [("abundance", .abundance), ("scalarity", .scalarity), ("mirativity", .mirativity)]

/-- The reply of a row. -/
def responseOf (d : Datum) : Option Response :=
  d.parse? "response" [("denial", .denial), ("wait a minute", .waitAMinute)]

theorem denial_rows : ∀ d ∈ Examples.all, ∀ r ∈ responseOf d, ∀ c ∈ contentOf d,
    (d.judgment = .acceptable ↔ (r = .denial ↔ c.IsAtIssue)) := by
  decide +kernel

/-- The diagnostic a row answers: an unembedded sentence in a context neutral about the content,
or a belief report whose holder's state denies it. -/
def testOf (d : Datum) : Option Test :=
  (d.parse? "diagnostic" [("nur so", .matrix .unembedded .neutral)]).orElse
    fun _ ↦ d.parse? "holder" [("negative", .belief .negative)]

/-- Of the classes of projective content, the judgments of the non-base rows fit exactly the one
with obligatory local effect and no strong contextual felicity constraint. -/
theorem nonBase_class_eq_C (k : ProjectiveClass) :
    (∀ d ∈ Examples.all, alternantOf d = some .nonBase → ∀ t ∈ testOf d,
      (d.judgment = .acceptable ↔ ¬ Excludes k t)) ↔ k = .C := by
  revert k
  decide +kernel

section Evaluator

variable {W : Type*}

theorem not_subset_compl_of_image_subset {R : SetRel W W} {m c : Set W}
    (hR : ∀ w, (R.image {w}).Nonempty) (hm : ∀ w ∉ m, R.image {w} ⊆ mᶜ) (hc : c.Nonempty)
    (hloc : R.image c ⊆ m) : ¬ c ⊆ mᶜ := by
  intro hcm
  obtain ⟨w, hw⟩ := hc
  obtain ⟨v, hv⟩ := hR w
  exact hm w (hcm hw) hv (hloc (SetRel.image_mono (Set.singleton_subset_iff.2 hw) hv))

theorem exists_speaker_consistent :
    ∃ (R : SetRel Bool Bool) (speaker holder c : Set Bool), (∀ w, (R.image {w}).Nonempty) ∧
      (∀ w ∉ holder, R.image {w} ⊆ holderᶜ) ∧ c.Nonempty ∧ R.image c ⊆ speaker ∧ c ⊆ holderᶜ :=
  ⟨SetRel.id, .univ, ∅, .univ, fun w ↦ ⟨w, by simp⟩, fun _ _ _ _ h ↦ h, ⟨true, trivial⟩,
    Set.subset_univ _, fun _ _ h ↦ h⟩

end Evaluator

/-! ### *Not even*, §3.3.4 -/

/-- The presuppositions of *even* under negation, a value below the low threshold `lo` (36), and
of the non-base alternant's scalarity, a value above the upper threshold of normalcy `hi` (71a),
can be met together. -/
def BeneathSatisfiable {α : Type*} [Preorder α] (lo hi : α) (a : Alternant) : Prop :=
  ∃ v, v < lo ∧ (a = .nonBase → hi < v)

theorem beneathSatisfiable_iff {α : Type*} [Preorder α] {lo hi : α} (h : lo ≤ hi)
    (hv : ∃ v, v < lo) (a : Alternant) : BeneathSatisfiable lo hi a ↔ a = .base := by
  cases a
  · simpa [BeneathSatisfiable] using hv
  · simp only [BeneathSatisfiable, forall_const, reduceCtorEq, iff_false, not_exists, not_and]
    exact fun v hlo hhi ↦ lt_irrefl v ((hlo.trans_le h).trans hhi)

theorem even_rows {α : Type*} [Preorder α] {lo hi : α} (h : lo ≤ hi) (hv : ∃ v, v < lo) :
    ∀ d ∈ Examples.all, d.feature? "diagnostic" = some "not even" → ∀ a ∈ alternantOf d,
      (d.judgment = .acceptable ↔ BeneathSatisfiable lo hi a) := by
  have key : ∀ d ∈ Examples.all, d.feature? "diagnostic" = some "not even" →
      ∀ a ∈ alternantOf d, (d.judgment = .acceptable ↔ a = .base) := by
    decide +kernel
  simpa only [beneathSatisfiable_iff h hv] using key

/-! ### The size of a gerund, §4 -/

/-- The heads of the paper's hierarchy: Cinque's, a mirative head and a scalarity head. -/
inductive Head
  | cinque (h : Cartography.Head)
  | mirative
  | scalarity
  deriving DecidableEq, Fintype

namespace Head

/-- The place of a head, three to each of Cinque's: mirativity just below his evaluative mood,
scalarity just above his past tense. -/
def rank : Head → ℕ
  | cinque h => 3 * h.ctorIdx + 1
  | mirative => 3 * Cartography.Head.moodEvaluative.ctorIdx
  | scalarity => 3 * Cartography.Head.tPast.ctorIdx + 2

instance : LinearOrder Head := LinearOrder.lift' rank (by decide)

/-- Cinque's hierarchy embeds in the paper's. -/
def ofCinque : Cartography.Head ↪o Head := OrderEmbedding.ofStrictMono cinque (by decide)

theorem covBy_mirative_scalarity :
    cinque .moodEvidential ⋖ mirative ∧ mirative ⋖ cinque .moodEvaluative ∧
      cinque .tPast ⋖ scalarity ∧ scalarity ⋖ cinque .modEpistemic := by
  simp only [CovBy]
  decide

end Head

open Head

/-- The heads a gerund of an alternant requires: tense, and the scalarity and mirativity of the
non-base alternant (§4.1). -/
def required : Alternant → Finset Head
  | .base => {cinque .tPast}
  | .nonBase => {cinque .tPast, scalarity, mirative}

/-- A gerund projects as high as its highest required head (§4.1). -/
def size (a : Alternant) : Head := (required a).max' (by cases a <;> simp [required])

theorem size_base : size .base = cinque .tPast := by decide

theorem size_nonBase : size .nonBase = mirative := by decide

/-- The head of the adverb class a row tests, by the projection the paper names. -/
def projectionOf (d : Datum) : Option Head :=
  d.parse? "projection"
    [("speech-act", cinque .moodSpeechAct), ("evaluation", cinque .moodEvaluative),
      ("mirativity", mirative), ("epistemic modality", cinque .modEpistemic),
      ("scalar evaluation", scalarity), ("deictic tense", cinque .tPast),
      ("habitual aspect", cinque .aspHabitual), ("continuative aspect I", cinque .aspContinuative),
      ("durative aspect", cinque .aspDurative), ("prospective aspect", cinque .aspProspective)]

theorem gerund_rows : ∀ d ∈ Examples.all, ∀ a ∈ alternantOf d, ∀ h ∈ projectionOf d,
    (d.judgment = .acceptable ↔ h ≤ size a) := by
  decide +kernel

theorem mem_Ioc_size_iff (h : Head) : h ∈ Set.Ioc (size .base) (size .nonBase) ↔
    h ∈ ({scalarity, cinque .modEpistemic, cinque .moodEvidential, mirative} : Finset Head) := by
  rw [size_base, size_nonBase, Set.mem_Ioc]
  revert h
  decide

/-! ### The participating verb classes, §2 -/

open ArgumentStructure

/-- The verb classes of (11). -/
def participatingClasses : List LevinClass :=
  [.lightEmission, .soundEmission, .substanceEmission, .soundExistence, .entitySpecificModeOfBeing,
    .modeOfBeingInvolvingMotion, .swarm]

theorem participates_swarm_iff :
    ∀ c ∈ participatingClasses, c.Participates .swarm ↔ c ≠ .modeOfBeingInvolvingMotion := by
  decide +kernel

theorem modeOfBeingInvolvingMotion_stars_swarm :
    LevinClass.modeOfBeingInvolvingMotion.Stars .swarm := by
  decide

end HoleFraser2026
