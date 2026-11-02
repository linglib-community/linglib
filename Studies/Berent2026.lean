module

public import Linglib.Data.Examples.Berent2026
public import Linglib.Fragments.English.Phonology
public import Linglib.Fragments.Hebrew.ConsonantalRoots
public import Linglib.Morphology.Root.Consonantal
public import Linglib.Phonology.Segmental.Sonority
public import Studies.BerentEtAl2016

/-!
# Berent (2026): Three arguments for abstraction in phonology

Three sets of experiments argue that phonological grammar is substance-free. Onsets with larger
sonority rises are preferred, *blif* to *bnif* to *bdif* to *lbif*, in print and with the lips or
the tongue suppressed, as [the rise reads only the features defining sonority](##onsetRise_congr).
Hebrew speakers extend their ban on roots that begin with two identical consonants to /θ/, and ASL
signers their preference for reduplication to handshapes ASL lacks: [the ban survives any injective
relabelling](##initialIdentity_map), and a model of token co-occurrence [cannot tell the forms
apart](##kathath_thathak). English speakers carry doubling over to novel ASL signs, [preferring
doubled plurals where speakers without plural morphology do not](##plural_transfer).

## Implementation notes

* The paper defers its analysis of the syllable hierarchy to earlier work, so the hierarchy is
  the order on sonority rises and no tableau is built. The acoustic, articulatory and neural
  measures of Figures 1 and 3 are not modelled.
* The ban is the paper's generalization over the first two consonants of a root. In
  [mccarthy-1981]'s analysis it follows from the OCP on the root tier, which makes *smm* a
  biliteral root, and rightward spreading (`McCarthy1981.consonantism_biliteral`).
* The model of token co-occurrence counts adjacent pairs of segments in a lexicon. The paper adds
  that the place feature of /θ/, a wide tongue-tip constriction, is unattested in Hebrew too. The
  PHOIBLE features lack it, but `pairCount_eq_zero` holds for tokens of any type, its values
  included.
* The paper credits the signers' preference to the productive reduplication of ASL, so signers
  analyse a doubled sign at the morphological level and nonsigners at the phonological one. The
  level is assumed, not computed by `SpokenLanguage.level`, which reads a taught meaning.
* Mandarin enters as any spoken language without plural morphology, the property the paper
  credits for the result.

## Errata

* The cross-modal experiments are said to present novel signs to "speakers who are sign-native"
  (p. 13); the participants were sign-naïve English speakers, as the abstract and the surrounding
  argument have it.
* The preference for doubled signs in the morphological context is referred to Figure 1B
  (p. 15); it is plotted in Figure 2B.

## References

* [berent-2026]
* [berent-steriade-lennertz-vaknin-2007]
* [berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016]
* [berent-bat-el-brentari-platt-2020]
* [mccarthy-1981]
-/

@[expose] public section

namespace Berent2026

open Phonology Morphology OptimalityTheory BerentEtAl2016

/-! ### Abstract: the syllable hierarchy -/

section Abstract

variable {c₁ c₂ d₁ d₂ : Segment}

/-- The sonority rise across a two-consonant onset. Larger rises are better formed. -/
def onsetRise (c₁ c₂ : Segment) : ℤ := Sonority.rise (.ofSegment c₁) (.ofSegment c₂)

/-- The rise of an onset depends on its consonants only through the features that define
sonority, so it is blind to the place of articulation that the suppression experiments
disrupt. -/
theorem onsetRise_congr (h₁ : ∀ f ∈ Sonority.features, c₁ f = d₁ f)
    (h₂ : ∀ f ∈ Sonority.features, c₂ f = d₂ f) : onsetRise c₁ c₂ = onsetRise d₁ d₂ := by
  rw [onsetRise, onsetRise, Sonority.ofSegment_congr h₁, Sonority.ofSegment_congr h₂]

open English.Phonology

-- The onsets of *lbif*, *bdif*, *bnif* and *blif* ([berent-steriade-lennertz-vaknin-2007]), p. 7.
theorem sonority_cline :
    onsetRise l b < 0 ∧ onsetRise b d = 0 ∧ 0 < onsetRise b n ∧ onsetRise b n < onsetRise b l := by
  decide

-- The labial onsets of *ptik*, *pnik* and *plik* in the suppression experiment of Figure 1D, p. 10.
theorem labial_cline : onsetRise p t = 0 ∧ 0 < onsetRise p n ∧ onsetRise p n < onsetRise p l := by
  decide

end Abstract

/-! ### Algebraic: identity restrictions -/

section Algebraic

variable {α β : Type*} {f : α → β} {x y z : α} {q : α × α} {L : List (List α)}

/-- A consonantal root begins with two identical consonants, which Hebrew bans while allowing
identical consonants at the end of a root. -/
def InitialIdentity (r : ConsonantalRoot α) : Prop := ¬ OCP.IsClean (r.segments.take 2)

instance [DecidableEq α] : DecidablePred (InitialIdentity (α := α)) :=
  fun _ ↦ inferInstanceAs (Decidable (¬ _))

/-- The ban gives the same verdict on a root and on its image under an injective relabelling of
its consonants, so it extends to consonants that the language lacks. -/
theorem initialIdentity_map (hf : Function.Injective f) (r : ConsonantalRoot α) :
    InitialIdentity (r.map f) ↔ InitialIdentity r := by
  simp only [InitialIdentity, ConsonantalRoot.segments_map, ← List.map_take, OCP.IsClean,
    List.isChain_map, hf.ne_iff]

open Hebrew.Phonology in
-- *dideb* and *bided* 'he isolated', p. 11.
theorem initialIdentity_iff_judgment :
    (InitialIdentity ⟨[d, d, b]⟩ ↔ Examples.dideb.judgment = .ungrammatical) ∧
      (InitialIdentity ⟨[b, d, d]⟩ ↔ Examples.bided.judgment = .ungrammatical) := by
  decide +kernel

variable [DecidableEq α]

/-- The number of times the tokens of `q` occur next to each other in the forms of a lexicon, the
statistic of a model that tracks the co-occurrence of specific tokens. -/
def pairCount (L : List (List α)) (q : α × α) : ℕ := (L.flatMap fun w ↦ w.zip w.tail).count q

/-- The counts in a lexicon of the adjacent pairs of a form, all that a model of token
co-occurrence knows of it. -/
def pairCounts (L : List (List α)) (w : List α) : List ℕ := (w.zip w.tail).map (pairCount L)

theorem pairCount_eq_zero (hz : ∀ w ∈ L, z ∉ w) (hq : q.1 = z ∨ q.2 = z) : pairCount L q = 0 := by
  rw [pairCount, List.count_eq_zero]
  simp only [List.mem_flatMap, not_exists, not_and]
  intro w hw hmem
  obtain ⟨h₁, h₂⟩ := List.of_mem_zip hmem
  rcases hq with rfl | rfl
  exacts [hz w hw h₁, hz w hw (List.mem_of_mem_tail h₂)]

open Hebrew.Phonology in
open English.Phonology (θ) in
/-- Hebrew speakers favoured *kathath* over *thathak* (p. 11). Since /θ/ is neither a Hebrew
consonant nor one of the archisegments of the alternating stops, every adjacent pair of either
root has count zero in any lexicon of Hebrew roots, so a model of token co-occurrence cannot tell
them apart, while the ban rules out *thathak* alone. -/
theorem kathath_thathak (L : List (ConsonantalRoot Segment))
    (hL : ∀ r ∈ L, ∀ c ∈ r.segments, c ∈ consonants ∪ {B, K, P}) :
    pairCounts (L.map (·.segments)) [k, θ, θ] = pairCounts (L.map (·.segments)) [θ, θ, k] ∧
      ¬ InitialIdentity ⟨[k, θ, θ]⟩ ∧ InitialIdentity ⟨[θ, θ, k]⟩ := by
  have hθ : ∀ w ∈ L.map (·.segments), θ ∉ w := by
    simp only [List.mem_map]
    rintro _ ⟨r, hr, rfl⟩ h
    exact absurd (hL r hr θ h) (by decide +kernel)
  exact ⟨by simp [pairCounts, pairCount_eq_zero hθ], by decide +kernel, by decide +kernel⟩

-- The fragment's roots, archisegments included, form such a lexicon.
open Hebrew Hebrew.Phonology in
example : ∀ r ∈ [ktv, pll, rkk, mss, xmm], ∀ c ∈ r.segments, c ∈ consonants ∪ {B, K, P} := by
  decide +kernel

/-- Native ASL signers preferred novel doubled signs whose handshape ASL lacks to their controls,
and nonsigners dispreferred them (p. 12). Both forms have only pairs of count zero in any lexicon
of ASL signs, while the grammar of doubling prefers the doubled sign at the signers' morphological
level and the control at the nonsigners' phonological one. -/
theorem unattested_handshapes (hx : ∀ w ∈ L, x ∉ w) (h : x ≠ y) (r : Ranking (Fin 2) 2) :
    pairCounts L [x, x] = pairCounts L [x, y] ∧
      (tableau x y .morphology r).optimal = {.reduplicated [x]} ∧
      (tableau x y .phonology r).optimal = {.simplex [x, y]} :=
  ⟨by simp [pairCounts, pairCount_eq_zero hx], optimal_morphology h r, optimal_phonology h r⟩

end Algebraic

/-! ### Amodal: transfer from speech to sign -/

section Amodal

variable {α : Type*} [DecidableEq α] {x y : α}

/-- English speakers preferred a doubled sign for a set of objects and Mandarin speakers did not,
in line with the absence of plural morphology from Mandarin ([berent-bat-el-brentari-platt-2020],
reported p. 15). The licensing of [berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016] predicts
the contrast for every spoken language without plural morphology, over constituents of any
type, signed or spoken. -/
theorem plural_transfer (l : SpokenLanguage Meaning) (hl : .plural ∉ l.marked) (h : x ≠ y)
    (r : Ranking (Fin 2) 2) :
    (∃ p ∈ (tableau x y (english.level .plural) r).optimal, p.surface = [x, x]) ∧
      ¬ ∃ p ∈ (tableau x y (l.level .plural) r).optimal, p.surface = [x, x] := by
  rw [exists_optimal_surface_iff _ _ h, exists_optimal_surface_iff _ _ h, english_licenses_iff]
  exact ⟨rfl, fun hp ↦ hl hp.1⟩

end Amodal

end Berent2026
