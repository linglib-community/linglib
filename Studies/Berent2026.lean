module

public import Linglib.Data.Examples.Berent2026
public import Linglib.Fragments.English.Phonology
public import Linglib.Fragments.Hebrew.ConsonantalRoots
public import Linglib.Morphology.Root.Consonantal
public import Linglib.Phonology.Segmental.Sonority
public import Linglib.Phonology.Subregular.StrictlyLocal
public import Studies.BerentEtAl2016

/-!
# Berent (2026): Three arguments for abstraction in phonology

Three sets of experiments argue that phonology is substance-free. Onsets with larger sonority rises
are preferred, *blif* to *bnif* to *bdif* to *lbif*, in print and under articulatory suppression, as
[the rise reads only the features defining sonority](##onsetRise_congr). Hebrew speakers extend
their ban on initial identical consonants to /θ/, and ASL signers their preference for reduplication
to novel handshapes. The ban is strictly local, forbidding ⋊XX for every X, so [it survives any
injective relabelling](##initialIdentity_map), while [no function of token co-occurrence counts
decides it](##initialIdentity_not_factorsThrough). English speakers carry doubling over to signs,
[preferring doubled plurals where speakers without plural morphology do not](##plural_transfer).

## Implementation notes

* The paper defers its analysis of the syllable hierarchy to earlier work, so the hierarchy is
  the order on sonority rises and no tableau is built. The acoustic, articulatory and neural
  measures of Figures 1 and 3 are not modelled.
* The ban is the paper's generalization over the first two consonants of a root. In
  [mccarthy-1981]'s analysis it follows from the OCP on the root tier, which makes *smm* a
  biliteral root, and rightward spreading (`McCarthy1981.consonantism_biliteral`).
* The model of token co-occurrence counts the adjacent pairs of a form among those of a lexicon,
  without word boundaries, so that every pair of *kathath* and *thathak* contains /θ/; with
  boundaries it could still separate them by the position of the attested /k/. The paper adds that
  the place feature of /θ/, a wide tongue-tip constriction, is unattested in Hebrew too. The
  PHOIBLE features lack it, but `pairCount_eq_zero` holds for tokens of any type.
* The paper credits the signers' preference to the productive reduplication of ASL, so signers
  analyse a doubled sign at the morphological level and nonsigners at the phonological one. The
  level is assumed, not computed by `SpokenLanguage.level`, which reads a taught meaning.
* Mandarin enters as any spoken language without plural morphology, the property the paper
  credits for the result.

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

variable {α β : Type*} {f : α → β} {x y z : α} {u : α × α} {L : List (List α)}

/-- The 3-factors that begin a word with two identical elements, ⋊XX with X a variable over the
alphabet. -/
def initialDoubles : Set (Augmented α) := {u | ∃ x, u = [none, some x, some x]}

/-- A consonantal root begins with two identical consonants, which Hebrew bans while allowing
identical consonants at the end of a root: the strictly 3-local grammar that forbids
`initialDoubles` rejects it. -/
def InitialIdentity (r : ConsonantalRoot α) : Prop :=
  r.segments ∉ (StrictlyLocalGrammar.ofForbidden initialDoubles).language 3

theorem initialIdentity_iff {r : ConsonantalRoot α} :
    InitialIdentity r ↔ ∃ x t, r.segments = x :: x :: t := by
  obtain ⟨w⟩ := r
  simp only [InitialIdentity, StrictlyLocalGrammar.mem_ofForbidden_language, initialDoubles,
    Set.mem_ofPred_eq, not_forall, not_not, exists_prop]
  constructor
  · rintro ⟨_, hl, hu, x, rfl⟩
    obtain ⟨i, -, hi, he⟩ := (infix_boundary_and_length_eq_iff (by norm_num)).1 ⟨hu, hl⟩
    simp only [window, List.ofFn_succ, List.ofFn_zero, List.cons.injEq, Fin.val_zero,
      Fin.val_succ, and_true] at he
    obtain ⟨h₀, h₁, h₂⟩ := he
    have := List.getElem?_int_eq_none_iff.1 (by simpa using h₀.symm)
    have := List.getElem?_int_eq_none_iff.not.1 (h₁ ▸ Option.some_ne_none x)
    obtain rfl : i = -1 := by push_cast at *; omega
    rw [List.getElem?_int_of_nonneg (by omega)] at h₁ h₂
    norm_num at h₁ h₂
    rcases w with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp only [List.getElem?_nil, List.getElem?_cons_zero,
      List.getElem?_cons_succ, reduceCtorEq, Option.some.injEq] at h₁ h₂
    subst h₁ h₂
    exact ⟨x, t, rfl⟩
  · rintro ⟨x, t, h⟩
    exact ⟨_, rfl, ⟨[none], t.map some ++ [none, none], by simp [boundary, h]⟩, x, rfl⟩

instance [DecidableEq α] : DecidablePred (InitialIdentity (α := α)) := fun r ↦
  decidable_of_iff (r.segments ≠ [] ∧ r.segments[0]? = r.segments[1]?) <| by
    rw [initialIdentity_iff]
    rcases r with ⟨_ | ⟨a, _ | ⟨b, t⟩⟩⟩ <;> simp [eq_comm]

/-- The ban gives the same verdict on a root and on its image under an injective relabelling of
its consonants, so it extends to consonants that the language lacks. -/
theorem initialIdentity_map (hf : Function.Injective f) (r : ConsonantalRoot α) :
    InitialIdentity (r.map f) ↔ InitialIdentity r := by
  rcases r with ⟨_ | ⟨a, _ | ⟨b, t⟩⟩⟩ <;> simp [initialIdentity_iff, hf.eq_iff]

open Hebrew.Phonology in
-- *dideb* and *bided* 'he isolated', p. 11.
theorem initialIdentity_iff_judgment :
    (InitialIdentity ⟨[d, d, b]⟩ ↔ Examples.dideb.judgment = .ungrammatical) ∧
      (InitialIdentity ⟨[b, d, d]⟩ ↔ Examples.bided.judgment = .ungrammatical) := by
  decide +kernel

variable [DecidableEq α]

/-- The number of occurrences of `u` among the adjacent pairs of the forms of a lexicon, the
statistic of a model that tracks the co-occurrence of specific tokens. -/
def pairCount (L : List (List α)) (u : α × α) : ℕ := (L.flatMap List.consecutivePairs).count u

/-- The counts in a lexicon of the adjacent pairs of a form, all that a model of token co-occurrence
knows of it. -/
def pairCounts (L : List (List α)) (w : List α) : List ℕ :=
  w.consecutivePairs.map (pairCount L)

theorem pairCount_eq_zero (hz : ∀ w ∈ L, z ∉ w) (hu : u.1 = z ∨ u.2 = z) : pairCount L u = 0 := by
  rw [pairCount, List.count_eq_zero]
  simp only [List.mem_flatMap, not_exists, not_and]
  rintro w hw h
  have := List.of_mem_zip (a := u.1) (b := u.2) h
  rcases hu with rfl | rfl
  · exact hz w hw this.1
  · exact hz w hw (List.mem_of_mem_tail this.2)

open Hebrew.Phonology in
open English.Phonology (θ) in
/-- Hebrew speakers favoured *kathath* over *thathak* (p. 11). Since /θ/ is neither a Hebrew
consonant nor one of the archisegments of the alternating stops, the two roots have the same pair
counts in any lexicon of Hebrew roots, so the ban, which separates them, is no function of the
pair counts. -/
theorem initialIdentity_not_factorsThrough (L : List (ConsonantalRoot Segment))
    (hL : ∀ r ∈ L, ∀ c ∈ r.segments, c ∈ consonants ∪ {B, K, P}) :
    ¬ Function.FactorsThrough InitialIdentity
        fun r : ConsonantalRoot Segment ↦ pairCounts (L.map (·.segments)) r.segments := by
  have hθ : ∀ w ∈ L.map (·.segments), θ ∉ w := by
    simp only [List.mem_map]
    rintro _ ⟨r, hr, rfl⟩ h
    exact absurd (hL r hr θ h) (by decide +kernel)
  intro h
  have := @h ⟨[k, θ, θ]⟩ ⟨[θ, θ, k]⟩
    (by simp [pairCounts, List.consecutivePairs, pairCount_eq_zero hθ])
  exact (by decide +kernel : ¬ InitialIdentity ⟨[k, θ, θ]⟩) (this ▸ by decide +kernel)

-- The fragment's roots, archisegments included, form such a lexicon.
open Hebrew Hebrew.Phonology in
example : ∀ r ∈ [ktv, pll, rkk, mss, xmm], ∀ c ∈ r.segments, c ∈ consonants ∪ {B, K, P} := by
  decide +kernel

/-- Native ASL signers preferred novel doubled signs whose handshape ASL lacks to their controls,
and nonsigners dispreferred them (p. 12). A doubled sign and its control have the same pair counts
in any lexicon of ASL signs, so the winner of the doubling grammar, at the signers' morphological
level or the nonsigners' phonological one, is no function of the pair counts. -/
theorem doubling_not_factorsThrough (hx : ∀ w ∈ L, x ∉ w) (h : x ≠ y) (l : Level)
    (r : Ranking (Fin 2) 2) :
    ¬ Function.FactorsThrough (fun w ↦ ∃ p ∈ (tableau x y l r).optimal, p.surface = w)
        (pairCounts L) := by
  intro hf
  have := @hf [x, x] [x, y] (by simp [pairCounts, List.consecutivePairs, pairCount_eq_zero hx])
  cases l
  · simp [optimal_phonology h r, Parse.surface, Parse.morphemes, h.symm] at this
  · simp [optimal_morphology h r, Parse.surface, Parse.morphemes, h] at this

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
