module

public import Linglib.Phonology.Prosody.Intonation
public import Linglib.Phonology.Tone.Register
public import Linglib.Fragments.Japanese.Prosody
public import Linglib.Data.Examples.BeckmanPierrehumbert1986

/-!
# Beckman and Pierrehumbert (1986): Intonational structure in Japanese and English

Japanese and English share one sparse-tone prosodic hierarchy: pitch accents group into
accentual phrases with at most one accent each, accentual phrases into intermediate phrases, and
those into intonation phrases. A bitonal accent triggers catathesis, a step down of the pitch
range for the rest of its intermediate phrase, so chained accents [descend a
staircase](##BeckmanPierrehumbert1986.terrace_registerShifts) and a phrase boundary [resets the
register above the continued chain](##BeckmanPierrehumbert1986.boundary_raises). Japanese has
the one bitonal accent shape, while English [has shapes that do not trigger
catathesis](##BeckmanPierrehumbert1986.triggers_differ).

## Implementation notes

Catathesis is a phonetic-implementation rule triggered by bitonal accents; it is modelled as a
unit step down of the register, each accentual phrase contributing its shift and `Tone.terrace`
realizing the shifts as running sums, so the staircase, the boundary reset, and the comparison
with an unbroken chain are theorems rather than numbers read off figures. The Japanese
accentual phrase is built from the prosodic fragment's word entries.

## References

* [beckman-pierrehumbert-1986]
* [pierrehumbert-1980]
-/

@[expose] public section

namespace BeckmanPierrehumbert1986

open Prosody Tone

/-! ### Accentual phrases and catathesis -/

/-- An accentual phrase: the lowest level of the hierarchy, carrying at most one pitch accent
(`none` when unaccented). -/
structure AccentualPhrase where
  accent : Option PitchAccent
  /-- The words grouped into the phrase. -/
  nWords : ℕ
  deriving Repr, DecidableEq

/-- The phrase triggers catathesis: its accent is bitonal. -/
def AccentualPhrase.TriggersCatathesis (ap : AccentualPhrase) : Prop :=
  ∃ a ∈ ap.accent, a.IsBitonal

instance : DecidablePred AccentualPhrase.TriggersCatathesis := fun ap ↦
  inferInstanceAs (Decidable (∃ a ∈ ap.accent, a.IsBitonal))

/-- The register shift of an accentual phrase: a step down if its accent is bitonal, and none
otherwise. -/
def AccentualPhrase.shift (ap : AccentualPhrase) : ℤ :=
  if ap.TriggersCatathesis then -1 else 0

/-- The register shifts of a sequence of accentual phrases. -/
def registerShifts (aps : List AccentualPhrase) : List ℤ :=
  aps.map AccentualPhrase.shift

/-- The number of catathesis triggers in a sequence. -/
def catathesisCount (aps : List AccentualPhrase) : ℕ :=
  (aps.filter (·.TriggersCatathesis)).length

variable (b : ℤ) (aps aps₁ aps₂ : List AccentualPhrase) (ap : AccentualPhrase)

@[simp] theorem catathesisCount_nil : catathesisCount [] = 0 := rfl

theorem catathesisCount_cons :
    catathesisCount (ap :: aps) =
      (if ap.TriggersCatathesis then 1 else 0) + catathesisCount aps := by
  by_cases h : ap.TriggersCatathesis <;> simp [catathesisCount, h, Nat.add_comm]

theorem catathesisCount_eq_zero_iff :
    catathesisCount aps = 0 ↔ ∀ ap ∈ aps, ¬ap.TriggersCatathesis := by
  simp [catathesisCount, List.filter_eq_nil_iff]

theorem sum_registerShifts : (registerShifts aps).sum = -(catathesisCount aps : ℤ) := by
  induction aps with
  | nil => rfl
  | cons ap aps ih =>
    simp only [registerShifts, List.map_cons, List.sum_cons, catathesisCount_cons] at ih ⊢
    rw [ih, AccentualPhrase.shift]
    split <;> omega

/-- The staircase: each phrase is realized below the baseline by the number of catathesis
triggers up to and including it. -/
theorem terrace_registerShifts {i : ℕ} (hi : i < aps.length) :
    (terrace b (registerShifts aps))[i]? = some (b - catathesisCount (aps.take (i + 1))) := by
  induction aps generalizing b i with
  | nil => simp at hi
  | cons ap aps ih =>
    cases i with
    | zero =>
      simp only [registerShifts, List.map_cons, terrace_cons, List.getElem?_cons_zero,
        List.take_succ_cons, List.take_zero, catathesisCount_cons, catathesisCount_nil,
        Option.some.injEq, AccentualPhrase.shift]
      split <;> omega
    | succ i =>
      simp only [registerShifts, List.map_cons, terrace_cons, List.getElem?_cons_succ]
      rw [show (aps.map AccentualPhrase.shift) = registerShifts aps from rfl,
        ih _ (by simpa using hi)]
      simp only [List.take_succ_cons, catathesisCount_cons, Option.some.injEq,
        AccentualPhrase.shift]
      split <;> omega

theorem terrace_registerShifts_append :
    terrace b (registerShifts (aps₁ ++ aps₂)) =
      terrace b (registerShifts aps₁) ++
        terrace (b - catathesisCount aps₁) (registerShifts aps₂) := by
  rw [registerShifts, List.map_append, terrace_append, ← registerShifts, ← registerShifts,
    sum_registerShifts, Int.sub_eq_add_neg]

/-- The boundary reset: a chain started again from the baseline lies pointwise above the same
chain continued after the triggers of an earlier one. -/
theorem boundary_raises :
    List.Forall₂ (· ≤ ·) (terrace (b - catathesisCount aps₁) (registerShifts aps₂))
      (terrace b (registerShifts aps₂)) :=
  terrace_mono (List.forall₂_refl _) (by omega)

/-! ### Intermediate and intonation phrases -/

/-- An intermediate phrase: accentual phrases closed by a phrase accent, the domain of
catathesis. -/
structure IntermediatePhrase where
  aps : List AccentualPhrase
  phraseAccent : LevelTone
  aps_nonempty : aps ≠ [] := by decide
  deriving Repr

/-- An intonation phrase: intermediate phrases closed by a boundary tone. -/
structure IntonationPhrase where
  ips : List IntermediatePhrase
  boundaryTone : LevelTone
  ips_nonempty : ips ≠ [] := by decide
  deriving Repr

/-- The terminal contour of an intonation phrase: the last intermediate phrase's phrase
accent and the boundary tone, [pierrehumbert-1980]'s terminal sequence decomposed. -/
def IntonationPhrase.terminalContour (ip : IntonationPhrase) : TerminalContour :=
  ⟨(ip.ips.getLast ip.ips_nonempty).phraseAccent, ip.boundaryTone⟩

/-! ### The two systems -/

-- §3.2
theorem card_pitchAccent : Fintype.card PitchAccent = 10 := rfl

/-- Where a language's pitch-accent shapes come from (§2.1). With `lexical` a shape can be
part of a word's phonological specification, as in the two accents of Stockholm Swedish; with
`intonational` the shape never contrasts lexical items and instead contrasts intonational
meanings, as in English. The accent *locus* is lexically specified in both English and
Japanese (§2.5). Japanese has a single shape, so it allows neither contrast; B&P treat its
accent as a lexically linked H. -/
inductive AccentSpecification where
  | lexical
  | intonational
  deriving Repr, DecidableEq

/-- Where the compression takes effect relative to its trigger: within the accent itself
(Japanese, whose trailing L is already compressed) or only after it (English). -/
inductive CatathesisTiming where
  | withinAccent
  | afterAccent
  deriving Repr, DecidableEq

/-- A language's intonation system: how accents are specified, the contrastive accent
shapes, whether lexically unaccented words exist, whether the accentual-phrase boundary L is
always present, and when catathesis takes effect. -/
structure IntonationSystem where
  accentSpec : AccentSpecification
  accentShapes : List PitchAccent
  hasUnaccented : Bool
  apBoundaryLAlwaysPresent : Bool
  catathesisTiming : CatathesisTiming
  deriving Repr

/-- Japanese: a lexically linked accent, the one shape H*+L, unaccented words, a boundary L in
every accentual phrase, compression within the accent. -/
def japanese : IntonationSystem :=
  { accentSpec := .lexical
    accentShapes := [.trailing .H .L]
    hasUnaccented := true
    apBoundaryLAlwaysPresent := true
    catathesisTiming := .withinAccent }

/-- English: intonational accent shapes, the six H*, L*, H*+L, H+L*, L*+H and L+H* (§2.1),
every content word accentable, no accentual-phrase boundary tone, compression after the
accent. -/
def english : IntonationSystem :=
  { accentSpec := .intonational
    accentShapes := [.mono .H, .mono .L, .trailing .H .L,
                     .leading .H .L, .trailing .L .H, .leading .L .H]
    hasUnaccented := false
    apBoundaryLAlwaysPresent := false
    catathesisTiming := .afterAccent }

-- §3.2
theorem mem_english_accentShapes_iff (a : PitchAccent) :
    a ∈ english.accentShapes ↔ a.tones.Nodup := by
  revert a; decide

/-- Every Japanese accent shape steps the register down, and some English shape does not. -/
theorem triggers_differ :
    (∀ a ∈ japanese.accentShapes, registerShifts [⟨some a, 1⟩] = [-1]) ∧
      ∃ a ∈ english.accentShapes, registerShifts [⟨some a, 1⟩] = [0] := by
  decide

/-- An accented accentual phrase (*uma'i*, *mo'riya-no*). -/
def accentedAP : AccentualPhrase := ⟨some (.trailing .H .L), 1⟩

/-- An unaccented accentual phrase (*amai*, *toriya-no mawari-no*). -/
def unaccentedAP : AccentualPhrase := ⟨none, 1⟩

-- Chained accents descend, an unaccented phrase does not step down, and a reset chain lies above.
example : terrace 0 (registerShifts [accentedAP, accentedAP, accentedAP]) = [-1, -2, -3] := by
  simp only [registerShifts, List.map_cons, List.map_nil, terrace_cons, terrace_nil]; decide
example : terrace 0 (registerShifts [accentedAP, unaccentedAP, accentedAP]) = [-1, -1, -2] := by
  simp only [registerShifts, List.map_cons, List.map_nil, terrace_cons, terrace_nil]; decide
example : terrace (0 - catathesisCount [accentedAP]) (registerShifts [accentedAP]) = [-2] ∧
    terrace 0 (registerShifts [accentedAP]) = [-1] := by
  simp only [registerShifts, List.map_cons, List.map_nil, terrace_cons, terrace_nil]; decide

/-! ### Japanese accentual phrases from the lexicon -/

section JapaneseAP
open Japanese.Prosody

/-- The accentual phrase over grouped word entries: accented, always H*+L, iff some word is
lexically accented, grouping deleting all but one accent. -/
def AccentualPhrase.ofWords (ws : List ProsodicEntry) : AccentualPhrase :=
  { accent := if ∃ w ∈ ws, w.Accented then some (.trailing .H .L) else none
    nWords := ws.length }

theorem ofWords_triggersCatathesis_iff (ws : List ProsodicEntry) :
    (AccentualPhrase.ofWords ws).TriggersCatathesis ↔ ∃ w ∈ ws, w.Accented := by
  unfold AccentualPhrase.ofWords AccentualPhrase.TriggersCatathesis
  split <;> simp_all

end JapaneseAP

end BeckmanPierrehumbert1986
