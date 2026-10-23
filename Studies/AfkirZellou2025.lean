module

public import Linglib.Fragments.Tarifit.ConsonantalRoots
public import Linglib.Morphology.Morphotactics.Association
public import Linglib.Data.Examples.AfkirZellou2025
public import Linglib.Data.Wordlist.AfkirZellou2025
import Mathlib.Data.Fin.VecNotation
import all Init.Data.String.Defs  -- for unfolding `String.join`

/-!
# Schwa variation and the intensive imperative in Tarifit

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

The intensive imperative geminates the medial radical in the template CəCCəC, and a geminate
bilabial or dental fricative is a stop (p. 9): /ʒβð/ has [ʒβəð] and [ʒəb:əð]. One fragment root
derives both imperatives of each verb of §2 (`imperatives_derived`), except that Table 1 prints
the intensive of /χns/ without the schwa after the geminate (`bend_down_imp_intens`).

## Main definitions

* `AfkirZellou2025.imperative`: a root's simple imperative, by the association conventions.
* `AfkirZellou2025.intensive`: a root's intensive imperative, by the conventions, Erasure and
  fortition.
* `AfkirZellou2025.sonority`: the sonority of a phone on the scale of Figure 9.
* `AfkirZellou2025.Rising`, `Plateau`, `Falling`: the sonority profile of the initial cluster.
* `AfkirZellou2025.targets`: the thirty-eight CCəC target words, by root.

## Implementation notes

Figure 9 ranks voiced stops below voiceless fricatives, the majority view in the literature,
against the default of Parker, whom it cites (`Sonority.Class.parkerRank`). No target cluster
pairs the two classes, so the profiles are the same on either scale. The book gives the
intensive forms, not their derivation: the derivation here is McCarthy's for the Arabic second
binyan, whose template CVCCVC the intensive shares (`intensiveStem_eq`). The regression
estimates, the acoustic measurements and the perception study have no formal counterpart here.

## References

* [afkir-zellou-2025]
* [mccarthy-1981]
* [parker-2002]: the orders of voiced stops and voiceless fricatives (pp. 68–70)
* [hall-2006]
-/

@[expose] public section

namespace AfkirZellou2025

open Tarifit Morphology Phonology

/-! ### Stems -/

section Stem

variable {α β : Type*}

/-- The prosodic template CCəC of the simple imperative. -/
def imperativeTemplate : Autosegmental.Skeleton := [.C, .C, .V, .C]

/-- The prosodic template CəCCəC of the intensive imperative. -/
def intensiveTemplate : Autosegmental.Skeleton := [.C, .V, .C, .C, .V, .C]

/-- A root and the vowel `v` on a template, with no association lines yet. -/
def unassociated (t : Autosegmental.Skeleton) (v : α) (r : ConsonantalRoot α) : TemplateMatch α :=
  { root := r, vocalism := [v], template := t, associations := [] }

/-- The simple stem: the root and the vowel associated with CCəC by the universal conventions. -/
def simpleStem (v : α) (r : ConsonantalRoot α) : TemplateMatch α :=
  ((unassociated imperativeTemplate v r).associate .root).associate .vocalism

/-- The intensive stem: the root associated with CəCCəC by the conventions, the root line on the
C-slot of the final CVC erased, and the conventions again, which respread the medial radical to
it, as McCarthy's Erasure does in the Arabic second binyan; then the vowel. -/
def intensiveStem (v : α) (r : ConsonantalRoot α) : TemplateMatch α :=
  let m := (unassociated intensiveTemplate v r).associate .root
  ((m.delink .root 3).associate .root).associate .vocalism

theorem simpleStem_map (f : α → β) (v : α) (r : ConsonantalRoot α) :
    simpleStem (f v) (r.map f) = (simpleStem v r).map f := by
  simp only [simpleStem, ← TemplateMatch.associate_map]; rfl

theorem intensiveStem_map (f : α → β) (v : α) (r : ConsonantalRoot α) :
    intensiveStem (f v) (r.map f) = (intensiveStem v r).map f := by
  simp only [intensiveStem, ← TemplateMatch.associate_map, ← TemplateMatch.delink_map]; rfl

theorem simpleStem_eq (a b c v : α) :
    simpleStem v ⟨[a, b, c]⟩ =
      { root := ⟨[a, b, c]⟩, vocalism := [v], template := imperativeTemplate,
        associations := [⟨.root, 0, 0⟩, ⟨.root, 1, 1⟩, ⟨.root, 2, 3⟩, ⟨.vocalism, 0, 2⟩] } :=
  (simpleStem_map ![a, b, c, v] 3 ⟨[0, 1, 2]⟩).trans <| congrArg (·.map ![a, b, c, v])
    (show simpleStem (3 : Fin 4) ⟨[0, 1, 2]⟩ =
        { root := ⟨[0, 1, 2]⟩, vocalism := [3], template := imperativeTemplate,
          associations := [⟨.root, 0, 0⟩, ⟨.root, 1, 1⟩, ⟨.root, 2, 3⟩, ⟨.vocalism, 0, 2⟩] } by
      decide +kernel)

theorem intensiveStem_eq (a b c v : α) :
    intensiveStem v ⟨[a, b, c]⟩ =
      { root := ⟨[a, b, c]⟩, vocalism := [v], template := intensiveTemplate,
        associations := [⟨.root, 0, 0⟩, ⟨.root, 1, 2⟩, ⟨.root, 2, 5⟩, ⟨.root, 1, 3⟩,
          ⟨.vocalism, 0, 1⟩, ⟨.vocalism, 0, 4⟩] } :=
  (intensiveStem_map ![a, b, c, v] 3 ⟨[0, 1, 2]⟩).trans <| congrArg (·.map ![a, b, c, v])
    (show intensiveStem (3 : Fin 4) ⟨[0, 1, 2]⟩ =
        { root := ⟨[0, 1, 2]⟩, vocalism := [3], template := intensiveTemplate,
          associations := [⟨.root, 0, 0⟩, ⟨.root, 1, 2⟩, ⟨.root, 2, 5⟩, ⟨.root, 1, 3⟩,
            ⟨.vocalism, 0, 1⟩, ⟨.vocalism, 0, 4⟩] } by
      decide +kernel)

theorem spellout_simpleStem (a b c v : α) :
    (simpleStem v ⟨[a, b, c]⟩).spellout = [a, b, v, c] := by
  rw [simpleStem_eq]; rfl

theorem spellout_intensiveStem (a b c v : α) :
    (intensiveStem v ⟨[a, b, c]⟩).spellout = [a, v, b, b, v, c] := by
  rw [intensiveStem_eq]; rfl

end Stem

/-- The simple imperative of a root. -/
def imperative (r : ConsonantalRoot Segment) : TemplateMatch Segment := simpleStem «ə» r

theorem spellout_imperative (a b c : Segment) :
    (imperative ⟨[a, b, c]⟩).spellout = [a, b, «ə», c] :=
  spellout_simpleStem a b c «ə»

/-- The transcription of a root's imperative. -/
def surface (r : ConsonantalRoot Segment) : String :=
  String.join ((imperative r).spellout.filterMap ipa?)

/-- The thirty-eight CCəC target words, by root, in the order of Table 7. -/
def targets : List (ConsonantalRoot Segment) :=
  [«ðfʕ», ðqr, «ʁdˤr», «ʁfr», «ʁrβ», ħmð, nqr, qβr, qðf, qfr, qrβ, «qrʕ», «qtˤʕ», rmð, srm,
    «stˤr», χrf, «ʒβð», «ʒmð», «ʕβð», «ʕrm», ħsβ, ħzn, «ʃmθ», χzn, βkm, ħlm, ħsn, nqβ, «qmʕ»,
    «sʃn», χns, «ʒmʕ», sχf, ħkm, ntf, skf, rsq]

example : ∀ r ∈ targets, ∀ x ∈ r.segments, x ∈ consonants ∨ x = l := by decide +kernel

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
  decide +kernel

example : ∀ r ∈ targets, ∀ a ∈ r.segments[0]?, ∀ b ∈ r.segments[1]?,
    compare (sonority a) (sonority b) =
      compare (Sonority.Class.ofSegment a).parkerRank (Sonority.Class.ofSegment b).parkerRank := by
  decide +kernel

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

/-- The rows of Tables 7 and 9, each with its root, both in the order of Table 7. -/
def rows : List (Datum × ConsonantalRoot Segment) := Examples.all.zip targets

theorem rows_complete :
    Examples.all.length = targets.length ∧ ∀ x ∈ rows,
      surface x.2 = x.1.primaryText ∧ (intrusion? x.1).isSome ∧ (vowelless? x.1).isSome := by
  decide +kernel

/-! ### The intrusive schwa -/

theorem almostExclusively_iff_c2_r :
    ∀ x ∈ rows, intrusion? x.1 = some .almostExclusively ↔ x.2.segments[1]? = some Tarifit.r := by
  decide +kernel

theorem intrusion_of_rising :
    ∀ x ∈ rows, Rising x.2 →
      intrusion? x.1 = some .variably ∨ intrusion? x.1 = some .almostExclusively ∨
        VoicelessAt x.2 1 := by
  decide +kernel

theorem nonRising_or_voiceless_of_never_rarely :
    ∀ x ∈ rows, intrusion? x.1 = some .never ∨ intrusion? x.1 = some .rarely →
      ¬ Rising x.2 ∨ VoicelessAt x.2 1 := by
  decide +kernel

theorem variably_exceptions :
    ∀ x ∈ rows, intrusion? x.1 = some .variably →
      Rising x.2 ∨ ¬ VoicelessAt x.2 1 ∨ x.2 ∈ [nqβ, nqr, «qtˤʕ»] := by
  decide +kernel

/-! ### Vowelless production -/

theorem voiceless_of_often_vowelless :
    ∀ x ∈ rows, vowelless? x.1 = some .often →
      (VoicelessAt x.2 1 ∧ VoicelessAt x.2 2) ∨ x.2 = ħkm := by
  decide +kernel

theorem voiced_of_never_vowelless :
    ∀ x ∈ rows, vowelless? x.1 = some .never → ¬ VoicelessAt x.2 1 ∨ ¬ VoicelessAt x.2 2 := by
  decide +kernel

/-! ### The intensive imperative -/

/-- The bilabial and dental fricatives, which continue the historical stops at their places. -/
def spirants : Finset Segment := ⟨↑[β, θ, ð, «ðˤ»], by decide +kernel⟩

/-- The stop at a fricative's place: [−continuant], without delayed release. -/
def harden (x : Segment) : Segment :=
  (x.setFeature .continuant false).setFeature .delayedRelease false

/-- The labial and dental stops are fricatives except when geminated (p. 9). -/
theorem spirantization : ∀ x ∈ spirants, harden x ∈ geminates ∧ x ∉ geminates := by
  decide +kernel

example : [β, θ, ð, «ðˤ»].map harden = [b, t, d, «dˤ»] := by decide +kernel

/-- The fortis counterpart of a phoneme: the stop of a spirant, any other phoneme itself. -/
def fortis (x : Segment) : Segment := if x ∈ spirants then harden x else x

/-- Fortition: a root element linked to two slots is fortis. -/
def fortition (m : TemplateMatch Segment) : TemplateMatch Segment :=
  { m with root := ⟨m.root.segments.mapIdx fun k x ↦
      if 2 ≤ m.linkCount .root k then fortis x else x⟩ }

/-- The intensive imperative of a root: the intensive stem with schwa, after fortition. -/
def intensive (r : ConsonantalRoot Segment) : TemplateMatch Segment :=
  fortition (intensiveStem «ə» r)

theorem spellout_intensive (a b c : Segment) :
    (intensive ⟨[a, b, c]⟩).spellout = [a, «ə», fortis b, fortis b, «ə», c] := by
  rw [intensive, intensiveStem_eq]; rfl

/-- The written segments of a phoneme string, with a geminate, two adjacent identical phonemes,
written once with a length mark. -/
def written : List Segment → Option (List String)
  | [] => some []
  | x :: xs => do
    let s ← ipa? x
    match xs.head?, ← written xs with
    | some y, w :: ws => pure (if x = y ∧ w = s then (s ++ ":") :: ws else s :: w :: ws)
    | _, ws => pure (s :: ws)

/-- The stem of a cell of the data. -/
def stem (c : Wordlist.Cell) (r : ConsonantalRoot Segment) : TemplateMatch Segment :=
  if c.stem = ↑Wordlist.Stem.intensive then intensive r else imperative r

/-- The roots of the imperatives of §2. -/
def sketchRoots : List (ConsonantalRoot Segment) := [«ʒβð», χðm, skf, nqβ, fhm, rħm, χns]

/-- One root derives each verb's simple and intensive imperatives, except the intensive of
Table 1. -/
theorem imperatives_derived :
    ∀ ℓ ∈ Wordlist.lexemes, ∃ r ∈ sketchRoots, ∀ f ∈ Wordlist.all, f.lexeme = ℓ →
      f ≠ Wordlist.bend_down_imp_intens → written (stem f.cell r).spellout = some f.segments := by
  decide +kernel

/-- Table 1 writes the intensive of χns without the schwa after the geminate. -/
theorem bend_down_imp_intens :
    written (intensive χns).spellout ≠ some Wordlist.bend_down_imp_intens.segments ∧
      written ((intensive χns).spellout.eraseIdx 4) =
        some Wordlist.bend_down_imp_intens.segments := by
  decide +kernel

end AfkirZellou2025
