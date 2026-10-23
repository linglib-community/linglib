module

public import Linglib.Fragments.Tarifit.ConsonantalRoots
public import Linglib.Morphology.Morphotactics.Association
public import Linglib.Data.Examples.AfkirZellou2025
import all Init.Data.String.Defs  -- for unfolding `String.join`

/-!
# Schwa variation in Tarifit CCəC words

Tarifit triconsonantal verbs in the simple imperative carry a template schwa between the second
and third radicals, and Afkir and Zellou find two further variants: a short intrusive schwa in
the initial cluster ([Cə̆CəC]) and vowelless forms ([CCC]). This file builds the thirty-eight
target words from the fragment's roots by McCarthy's association conventions, classifies their
initial clusters on the book's sonority scale, and states the generalizations of Tables 7 and 9
over the pooled rows.

On the repair hypothesis, intrusion should be most frequent in the dispreferred falling clusters;
on the syllable-planning account of Georgian, a vocoid is tolerated only in rising ones. The data
side with the second (`intrusion_of_rising`, `nonRising_or_voiceless_of_never_rarely`), up to the
book's flagged exceptions (`variably_exceptions`). The near-categorical class is exactly the words
with medial /r/ (`almostExclusively_iff_c2_r`), not the rising class: the book's count of onset
profiles (`countP_rising_plateau_falling`) needs /ʕ/ above the tap, so /ʕrəm/ falls although
Table 9 files it under rising sonority. Vowellessness tracks voiceless second and third radicals
(`voiceless_of_often_vowelless`, `voiced_of_never_vowelless`).

## Main definitions

* `AfkirZellou2025.imperative`: a root's simple imperative, by the association conventions.
* `AfkirZellou2025.sonority`: the sonority of a phone on the scale of Figure 9.
* `AfkirZellou2025.Rising`, `Plateau`, `Falling`: the sonority profile of the initial cluster.
* `AfkirZellou2025.targets`: the thirty-eight CCəC target words, by root.

## Implementation notes

Figure 9 ranks voiced stops below voiceless fricatives, against the default of [parker-2002]
that it cites (`Sonority.Class.parkerRank`). No target cluster pairs the two classes, so the
profiles are the same on either scale. The regression estimates, the acoustic measurements and
the perception study have no formal counterpart here.

## References

* [afkir-zellou-2025]
* [mccarthy-1981]
* [parker-2002]
* [hall-2006]
-/

@[expose] public section

namespace AfkirZellou2025

open Tarifit Morphology Phonology

/-! ### The simple imperative -/

/-- The prosodic template CCəC of the simple imperative. -/
def imperativeTemplate : Autosegmental.Skeleton := [.C, .C, .V, .C]

/-- The simple imperative of a root: the root and the schwa associated with the template CCəC by
the universal association conventions. -/
def imperative (r : ConsonantalRoot Segment) : TemplateMatch Segment :=
  ((({ root := r, vocalism := [«ə»], template := imperativeTemplate, associations := [] } :
    TemplateMatch Segment).associate .root).associate .vocalism)

theorem spellout_imperative (a b c : Segment) :
    (imperative ⟨[a, b, c]⟩).spellout = [a, b, «ə», c] := by
  simp [imperative, imperativeTemplate, TemplateMatch.associate, TemplateMatch.associateOneToOne,
    TemplateMatch.associateRemaining, TemplateMatch.spread, TemplateMatch.unassociated,
    TemplateMatch.freeBearers, TemplateMatch.bearers, TemplateMatch.link, TemplateMatch.spellout,
    TemplateMatch.melody, TemplateMatch.segmentAt, TemplateMatch.IsAssociated,
    TemplateMatch.IsFilled, Autosegmental.Skeleton.cSlots, Autosegmental.Skeleton.vSlots,
    List.range_succ]

/-- The transcription of a root's imperative. -/
def surface (r : ConsonantalRoot Segment) : String :=
  String.join ((imperative r).spellout.filterMap ipa?)

/-- The thirty-eight CCəC target words, by root, in the order of Table 7. -/
def targets : List (ConsonantalRoot Segment) :=
  [«ðfʕ», ðqr, «ʁdˤr», «ʁfr», «ʁrβ», ħmð, nqr, qβr, qðf, qfr, qrβ, «qrʕ», «qtˤʕ», rmð, srm,
    «stˤr», χrf, «ʒβð», «ʒmð», «ʕβð», «ʕrm», ħsβ, ħzn, «ʃmθ», χzn, βkm, ħlm, ħsn, nqβ, «qmʕ»,
    «sʃn», χns, «ʒmʕ», sχf, ħkm, ntf, skf, rsq]

/-! ### Sonority profiles -/

/-- The sonority scale of Figure 9, which ranks the obstruents by manner before voicing. -/
def scale : Sonority.Class → ℕ
  | .vls => 1 | .vds => 2 | .vlf => 3 | .vdf => 4
  | .nasal => 5 | .liquid => 6 | .glide => 7 | .vowel => 8

/-- The sonority of a phone on the scale of Figure 9. -/
def sonority (x : Segment) : ℕ := scale (Sonority.Class.ofSegment x)

/-- The phone at root position `i` is a voiceless obstruent. -/
def VoicelessAt (r : ConsonantalRoot Segment) (i : ℕ) : Prop :=
  ∃ p ∈ r.segments[i]?, (Sonority.Class.ofSegment p).Voiceless

/-- The initial cluster rises in sonority. -/
def Rising (r : ConsonantalRoot Segment) : Prop :=
  ∃ a ∈ r.segments[0]?, ∃ b ∈ r.segments[1]?, sonority a < sonority b

/-- The initial cluster is level in sonority. -/
def Plateau (r : ConsonantalRoot Segment) : Prop :=
  ∃ a ∈ r.segments[0]?, ∃ b ∈ r.segments[1]?, sonority a = sonority b

/-- The initial cluster falls in sonority. -/
def Falling (r : ConsonantalRoot Segment) : Prop :=
  ∃ a ∈ r.segments[0]?, ∃ b ∈ r.segments[1]?, sonority b < sonority a

instance (r : ConsonantalRoot Segment) (i : ℕ) : Decidable (VoicelessAt r i) := by
  unfold VoicelessAt; infer_instance
instance (r : ConsonantalRoot Segment) : Decidable (Rising r) := by unfold Rising; infer_instance
instance (r : ConsonantalRoot Segment) : Decidable (Plateau r) := by
  unfold Plateau; infer_instance
instance (r : ConsonantalRoot Segment) : Decidable (Falling r) := by unfold Falling; infer_instance

/-- Seventeen of the target words begin with a rising cluster, six with a plateau and fifteen
with a fall (§3.2.1). -/
theorem countP_rising_plateau_falling :
    targets.countP (Rising ·) = 17 ∧ targets.countP (Plateau ·) = 6 ∧
      targets.countP (Falling ·) = 15 := by
  decide

example : ∀ r ∈ targets, ∀ a ∈ r.segments[0]?, ∀ b ∈ r.segments[1]?,
    compare (sonority a) (sonority b) =
      compare (Sonority.Class.ofSegment a).parkerRank (Sonority.Class.ofSegment b).parkerRank := by
  decide

/-! ### The tables -/

/-- Rate of the intrusive C1ə̆C2 schwa across a word's productions. -/
inductive Intrusion
  | never
  | rarely
  | variably
  | almostExclusively
  deriving DecidableEq, Repr

/-- Rate of vowelless production of a word. -/
inductive Vowelless
  | never
  | rarely
  | often
  deriving DecidableEq, Repr

/-- The root a row reports, by the transcription of its imperative. -/
def root? (e : Datum) : Option (ConsonantalRoot Segment) :=
  targets.find? (surface · == e.primaryText)

/-- The row's intrusion category. -/
def intrusion? (e : Datum) : Option Intrusion :=
  match e.feature? "intrusion" with
  | some "never" => some .never
  | some "rarely" => some .rarely
  | some "variably" => some .variably
  | some "almost exclusively" => some .almostExclusively
  | _ => none

/-- The row's vowelless category. -/
def vowelless? (e : Datum) : Option Vowelless :=
  match e.feature? "vowelless" with
  | some "never" => some .never
  | some "rarely" => some .rarely
  | some "often" => some .often
  | _ => none

theorem rows_complete :
    ∀ e ∈ Examples.all, (root? e).isSome ∧ (intrusion? e).isSome ∧ (vowelless? e).isSome := by
  decide

/-! ### The intrusive schwa -/

theorem almostExclusively_iff_c2_r :
    ∀ e ∈ Examples.all, ∀ r ∈ root? e,
      intrusion? e = some .almostExclusively ↔ r.segments[1]? = some Tarifit.r := by
  decide

theorem intrusion_of_rising :
    ∀ e ∈ Examples.all, ∀ r ∈ root? e, Rising r →
      intrusion? e = some .variably ∨ intrusion? e = some .almostExclusively ∨
        VoicelessAt r 1 := by
  decide

theorem nonRising_or_voiceless_of_never_rarely :
    ∀ e ∈ Examples.all, (intrusion? e = some .never ∨ intrusion? e = some .rarely) →
      ∀ r ∈ root? e, ¬ Rising r ∨ VoicelessAt r 1 := by
  decide

theorem variably_exceptions :
    ∀ e ∈ Examples.all, intrusion? e = some .variably →
      ∀ r ∈ root? e, Rising r ∨ ¬ VoicelessAt r 1 ∨ r ∈ [nqβ, nqr, «qtˤʕ»] := by
  decide

/-! ### Vowelless production -/

theorem voiceless_of_often_vowelless :
    ∀ e ∈ Examples.all, vowelless? e = some .often →
      ∀ r ∈ root? e, (VoicelessAt r 1 ∧ VoicelessAt r 2) ∨ r = ħkm := by
  decide

theorem voiced_of_never_vowelless :
    ∀ e ∈ Examples.all, vowelless? e = some .never →
      ∀ r ∈ root? e, ¬ VoicelessAt r 1 ∨ ¬ VoicelessAt r 2 := by
  decide

end AfkirZellou2025
