module

public import Linglib.Fragments.Tarifit.ConsonantalRoots
public import Linglib.Morphology.Morphotactics.TemplateMatch
public import Linglib.Data.Examples.AfkirZellou2025
import all Init.Data.String.Defs  -- for unfolding `String.join`

/-!
# Schwa variation in Tarifit CCəC words

Tarifit triconsonantal verbs in the simple imperative carry a prosodic-template schwa between
the second and third root consonants, and Afkir and Zellou find two further phonetic variants:
a shorter, coarticulating intrusive schwa inside the initial cluster ([Cə̆CəC], about a quarter of
productions), and vowelless forms ([CCC], about five percent), neither of them sensitive to
speaking style. The two schwas are independent processes, the template schwa a targeted segment
whose deletion shortens the word and the intrusive schwa a targetless vocoid. Their distribution
over the thirty-eight target words is tabulated by word. The words are the fragment's roots
vocalized by the simple-imperative template CCəC (`imperative`, `surface`), and this file states
the tables' generalizations over the pooled rows (`root?`, `intrusion?`, `vowelless?`), with each
root's initial-cluster sonority profile read off its phones (`Rising`, `Falling`).

Two hypotheses about the intrusive schwa are set against each other: repair, on which
insertion should be most frequent in the dispreferred falling-sonority clusters, and the
syllable-planning account of Georgian, on which a vocoid is tolerated only where it boosts the
planned sonority peak, hence in rising clusters. The data side with the second: every rising
cluster shows intrusion at least variably unless its second consonant is voiceless
(`intrusion_of_rising`), the words that never or rarely show intrusion are non-rising or have a
voiceless second consonant (`nonRising_or_voiceless_of_never_rarely`), and the paper's three
flagged exceptions are the only non-rising words with a voiceless second consonant that vary
(`variably_exceptions`). The near-categorical class is exactly the words with medial /r/
(`almostExclusively_iff_c2_r`); it is not the rising class, since on the paper's scale the
pharyngeal outranks the tap and /ʕrəm/ falls.
Vowellessness tracks low sonority: the often-vowelless words have voiceless second and third
consonants, except the flagged /ħkəm/ (`voiceless_of_often_vowelless`), and the never-vowelless
words all carry a voiced consonant there (`voiced_of_never_vowelless`). The regression
estimates, the acoustic measurements, and the perception result that an intrusive vowel aids
discrimination only in falling clusters are reported in the paper without a formal counterpart
here.

## References

* [afkir-zellou-2025]
* [parker-2002]
* [hall-2006]
-/

@[expose] public section

namespace AfkirZellou2025

open Tarifit Morphology Phonology

/-! ### The simple imperative -/

/-- The prosodic template CCəC of the simple imperative. -/
def imperativeTemplate : Autosegmental.Skeleton := [.C, .C, .V, .C]

/-- In the simple imperative the consonants of a root fill the C-slots in order and the schwa
the V-slot. -/
def imperative (r : ConsonantalRoot Segment) : TemplateMatch Segment where
  root := r
  vocalism := [schwa]
  template := imperativeTemplate
  associations := [⟨.root, 0, 0⟩, ⟨.root, 1, 1⟩, ⟨.vocalism, 0, 2⟩, ⟨.root, 2, 3⟩]

theorem spellout_imperative (a b c : Segment) :
    (imperative ⟨[a, b, c]⟩).spellout = [a, b, schwa, c] := rfl

/-- The transcription of a root's imperative. -/
def surface (r : ConsonantalRoot Segment) : String :=
  String.join ((imperative r).spellout.filterMap ipa?)

/-- The Parker sonority rank of a phone. -/
def rank (x : Segment) : ℕ := (Sonority.Class.ofSegment x).parkerRank

/-- The phone at root position `i` is a voiceless obstruent. -/
def VoicelessAt (r : ConsonantalRoot Segment) (i : ℕ) : Prop :=
  ∃ p ∈ r.segmentAt i, (Sonority.Class.ofSegment p).Voiceless

/-- The initial cluster rises in sonority. -/
def Rising (r : ConsonantalRoot Segment) : Prop :=
  ∃ a ∈ r.segmentAt 0, ∃ b ∈ r.segmentAt 1, rank a < rank b

/-- The initial cluster falls in sonority. -/
def Falling (r : ConsonantalRoot Segment) : Prop :=
  ∃ a ∈ r.segmentAt 0, ∃ b ∈ r.segmentAt 1, rank b < rank a

instance (r : ConsonantalRoot Segment) (i : ℕ) : Decidable (VoicelessAt r i) := by
  unfold VoicelessAt; infer_instance
instance (r : ConsonantalRoot Segment) : Decidable (Rising r) := by unfold Rising; infer_instance
instance (r : ConsonantalRoot Segment) : Decidable (Falling r) := by unfold Falling; infer_instance

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
  roots.find? (surface · == e.primaryText)

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

/-- Every row names a root and carries both categories. -/
theorem rows_complete :
    ∀ e ∈ Examples.all, (root? e).isSome ∧ (intrusion? e).isSome ∧ (vowelless? e).isSome := by
  decide

/-! ### The intrusive schwa -/

/-- Intrusion is near-categorical exactly in the words whose second consonant is /r/. -/
theorem almostExclusively_iff_c2_r :
    ∀ e ∈ Examples.all, ∀ r ∈ root? e,
      intrusion? e = some .almostExclusively ↔ r.segmentAt 1 = some Tarifit.r := by
  decide

/-- A rising cluster shows intrusion at least variably unless its second consonant is
voiceless. -/
theorem intrusion_of_rising :
    ∀ e ∈ Examples.all, ∀ r ∈ root? e, Rising r →
      intrusion? e = some .variably ∨ intrusion? e = some .almostExclusively ∨
        VoicelessAt r 1 := by
  decide

/-- Words that never or rarely show intrusion have a non-rising cluster or a voiceless second
consonant. -/
theorem nonRising_or_voiceless_of_never_rarely :
    ∀ e ∈ Examples.all, (intrusion? e = some .never ∨ intrusion? e = some .rarely) →
      ∀ r ∈ root? e, ¬ Rising r ∨ VoicelessAt r 1 := by
  decide

/-- Variable intrusion goes with a rising cluster or a voiced second consonant, except for the
three words the paper flags. -/
theorem variably_exceptions :
    ∀ e ∈ Examples.all, intrusion? e = some .variably →
      ∀ r ∈ root? e, Rising r ∨ ¬ VoicelessAt r 1 ∨ r ∈ [nqeb, nqer, qtes] := by
  decide

/-! ### Vowelless production -/

/-- Often-vowelless words have voiceless second and third consonants, except /ħkəm/. -/
theorem voiceless_of_often_vowelless :
    ∀ e ∈ Examples.all, vowelless? e = some .often →
      ∀ r ∈ root? e, (VoicelessAt r 1 ∧ VoicelessAt r 2) ∨ r = hkem := by
  decide

/-- Never-vowelless words have a voiced second or third consonant. -/
theorem voiced_of_never_vowelless :
    ∀ e ∈ Examples.all, vowelless? e = some .never →
      ∀ r ∈ root? e, ¬ VoicelessAt r 1 ∨ ¬ VoicelessAt r 2 := by
  decide

end AfkirZellou2025
