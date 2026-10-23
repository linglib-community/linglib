module

public import Linglib.Phonology.Prosody.Intonation
public import Linglib.Phonology.Tone.Register
public import Linglib.Fragments.Japanese.Prosody
public import Linglib.Data.Examples.BeckmanPierrehumbert1986

/-!
# Beckman and Pierrehumbert (1986): Intonational structure in Japanese and English

[beckman-pierrehumbert-1986] give Japanese and English one sparse-tone prosodic hierarchy:
pitch accents group into accentual phrases with at most one accent each, accentual phrases
into intermediate phrases, and those into intonation phrases, the phrase accent of
[pierrehumbert-1980] becoming the terminal tone of the intermediate phrase and the boundary
tone that of the intonation phrase. In both languages a bitonal accent triggers catathesis,
the compression of the pitch range for everything that follows within the intermediate
phrase, so chained accents descend a staircase and a phrase boundary resets the register; an
unaccented phrase's phrasal H and boundary L do not trigger it, which separates catathesis
from African downdrift. Both languages fix the accent's location in the lexicon; they differ
in where its shape comes from, a lexically linked H*+L in Japanese against a choice made by
the intonation system in English, in the inventory of shapes, one against six, and in whether
the compression takes effect within the accent or after it. Final lowering
and declination act above the intermediate phrase and are not catathesis.

## Implementation notes

Catathesis is register downstep on the tonal register tier: each bitonal accent contributes
a downstep node and `Tone.realizePitch` realizes the sequence as the running sum, so the
staircase, the boundary reset, and the comparison with an unbroken chain are theorems of the
register substrate rather than numbers read off figures. The Japanese accentual phrase is
built from the prosodic fragment's word entries.

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

/-- The register nodes of a sequence of accentual phrases: a downstep for each bitonal
accent and nothing otherwise. -/
def registerSpecs (aps : List AccentualPhrase) : List TRN :=
  aps.map fun ap ↦ if ap.TriggersCatathesis then TRN.downstep else TRN.empty

/-- The number of catathesis triggers in a sequence. -/
def catathesisCount (aps : List AccentualPhrase) : ℕ :=
  (aps.filter (·.TriggersCatathesis)).length

variable (b : Int) (aps aps₁ aps₂ : List AccentualPhrase) (ap : AccentualPhrase)

@[simp] private theorem pitchEffect_downstep : TRN.downstep.pitchEffect = -1 := rfl
@[simp] private theorem pitchEffect_empty : TRN.empty.pitchEffect = 0 := rfl
@[simp] theorem catathesisCount_nil : catathesisCount [] = 0 := rfl

theorem catathesisCount_cons :
    catathesisCount (ap :: aps) =
      (if ap.TriggersCatathesis then 1 else 0) + catathesisCount aps := by
  by_cases h : ap.TriggersCatathesis <;> simp [catathesisCount, h, Nat.add_comm]

theorem catathesisCount_eq_zero_iff :
    catathesisCount aps = 0 ↔ ∀ ap ∈ aps, ¬ap.TriggersCatathesis := by
  simp [catathesisCount, List.filter_eq_nil_iff]

theorem pitchEffect_registerSpecs_nonpos {t : TRN} (h : t ∈ registerSpecs aps) :
    t.pitchEffect ≤ 0 := by
  simp only [registerSpecs, List.mem_map] at h
  obtain ⟨ap, _, rfl⟩ := h
  split <;> decide

theorem sum_pitchEffect_registerSpecs :
    ((registerSpecs aps).map TRN.pitchEffect).sum = -(catathesisCount aps : Int) := by
  induction aps with
  | nil => rfl
  | cons ap aps ih =>
    simp only [registerSpecs, List.map_cons, List.sum_cons, catathesisCount_cons] at ih ⊢
    rw [ih]
    split <;> (simp only [pitchEffect_downstep, pitchEffect_empty]; omega)

theorem realizePitch_registerSpecs {i : ℕ} (hi : i < aps.length) :
    (realizePitch b (registerSpecs aps))[i]? = some (b - catathesisCount (aps.take (i + 1))) := by
  induction aps generalizing b i with
  | nil => simp at hi
  | cons ap aps ih =>
    cases i with
    | zero =>
      simp only [registerSpecs, List.map_cons, realizePitch_cons, List.getElem?_cons_zero,
        List.take_succ_cons, List.take_zero, catathesisCount_cons, catathesisCount_nil,
        Option.some.injEq]
      split <;> (simp only [pitchEffect_downstep, pitchEffect_empty]; omega)
    | succ i =>
      simp only [registerSpecs, List.map_cons, realizePitch_cons, List.getElem?_cons_succ,
        List.take_succ_cons, catathesisCount_cons]
      rw [show List.map _ aps = registerSpecs aps from rfl, ih _ (by simpa using hi)]
      split <;> (simp only [pitchEffect_downstep, pitchEffect_empty, Option.some.injEq]; omega)

theorem realizePitch_registerSpecs_append :
    realizePitch b (registerSpecs (aps₁ ++ aps₂)) =
      realizePitch b (registerSpecs aps₁) ++
        realizePitch (b - catathesisCount aps₁) (registerSpecs aps₂) := by
  have h : registerSpecs (aps₁ ++ aps₂) = registerSpecs aps₁ ++ registerSpecs aps₂ :=
    List.map_append ..
  rw [h, realizePitch_append, sum_pitchEffect_registerSpecs, Int.sub_eq_add_neg]

theorem boundary_raises :
    List.Forall₂ (· ≤ ·) (realizePitch (b - catathesisCount aps₁) (registerSpecs aps₂))
      (realizePitch b (registerSpecs aps₂)) :=
  realizePitch_baseline_mono _ (by omega)

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

/-- The register nodes of one intermediate phrase: a single chain. -/
def ipRegisterSpecs (ip : IntermediatePhrase) : List TRN := registerSpecs ip.aps

/-- The register nodes of an intonation phrase, one chain per intermediate phrase: each
starts again from the baseline. -/
def ipRegisterSpecsAcrossIps (ips : List IntermediatePhrase) : List (List TRN) :=
  ips.map ipRegisterSpecs

/-! ### The two systems -/

/-- The ten accents that the system permits in principle: two single-tone accents and eight
two-tone ones (§3.2). -/
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

/-- English uses exactly the accents whose tones differ: of the ten, the four two-tone accents
L*+L, L+L*, H*+H and H+H* are missing, since the realisation rules would neutralise them with
single-tone accents (§3.2). -/
theorem mem_english_accentShapes_iff (a : PitchAccent) :
    a ∈ english.accentShapes ↔ a.tones.Nodup := by
  revert a; decide

theorem triggers_differ :
    (∀ a ∈ japanese.accentShapes, registerSpecs [⟨some a, 1⟩] = [TRN.downstep]) ∧
      ∃ a ∈ english.accentShapes, registerSpecs [⟨some a, 1⟩] = [TRN.empty] := by
  decide

/-- An accented accentual phrase (*uma'i*, *mo'riya-no*). -/
def accentedAP : AccentualPhrase := ⟨some (.trailing .H .L), 1⟩

/-- An unaccented accentual phrase (*amai*, *toriya-no mawari-no*). -/
def unaccentedAP : AccentualPhrase := ⟨none, 1⟩

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
