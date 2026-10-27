module

public import Linglib.Core.InformationTheory.EntropyRate
public import Linglib.Syntax.DependencyGrammar.Reordering
public import Linglib.Fragments.Japanese.Morph
public import Linglib.Fragments.Sesotho.Morph
public import Studies.Bybee1985
public import Linglib.Data.Examples.HahnDegenFutrell2021

/-!
# Hahn, Degen, and Futrell (2021): Modeling Word and Morpheme Order in Natural Language as an Efficient Trade-Off of Memory and Surprisal

Hahn, Degen and Futrell explain word and morpheme order by the tradeoff of memory and surprisal.
A listener predicts each word from a memory state updated word by word, and the paper's
information locality bound says that a listener whose memory cannot hold the dependencies up to
some distance pays at least the entropy rate plus the information carried at longer distances,
the quantities of `Core/InformationTheory/EntropyRate.lean`. We prove the bound, compare two
orders of a sentence by dependency length, and check the paper's morpheme templates against
Bybee's relevance hierarchy.

## Implementation notes

* The Japanese suffix order is `Japanese.Verb.template`'s, the order of the paper's text, its
  supplement and its code, with the polite suffix before the desiderative; the paper's Table 2
  lists the two the other way round. The supplement's forms attest neither order, the two
  suffixes never sharing a form there.
* `japaneseCategory?` and `sesothoCategory?` map the slots the paper labels with a category of
  Bybee's hierarchy to it. The paper's Japanese "Voice and Mood" slot of the passive and
  the potential is read as voice, and its final "Tense, Aspect, Mood, and Finiteness" slot and
  the Sesotho "Tense/aspect" prefix as tense. The slots it labels otherwise, *suru*, politeness,
  negation, the reversive and the interrogative and relative markers, have no rank and are left
  out of the comparison.
* The paper orders the Sesotho passive before the perfect, in its text, its Table 4 and its
  supplement; Demuth's schema (14) and examples (28) and (44) order the perfect before
  the passive, and the Fragment follows Demuth. The paper's order is `paperSesothoTemplate`.
* The Sesotho rows are the verbs of Demuth's examples, their glosses without the noun classes,
  and two corpus forms from the supplement in which a tense prefix is fused with the
  neighbouring marker and glossed as that marker.
* Time runs over `ℕ` from the initial memory state. Every quantity in the bound is an entropy of
  a finite block, so the paper's two-sided process enters through its one-sided restriction.
* The initial memory state is an arbitrary random variable, so the bound holds without the
  paper's No Mindreading assumption, as the paper remarks.
* Entropies are in nats rather than bits; the bound is homogeneous in them.
* The dependency graphs of (2) follow Universal Dependencies conventions, with the comma
  dropped.

## References

* [M. Hahn, J. Degen, R. Futrell, *Modeling Word and Morpheme Order in Natural Language as an
  Efficient Trade-Off of Memory and Surprisal* (2021)][hahn-degen-futrell-2021]
* [J. Bybee, *Morphology: A Study of the Relation between Meaning and Form* (1985)][bybee-1985]
* [K. Demuth, *Acquisition of Sesotho* (1992)][demuth-1992]
* [O. Behaghel, *Beziehungen zwischen Umfang und Reihenfolge von Satzgliedern*
  (1909)][behaghel-1909]
-/

@[expose] public section

namespace HahnDegenFutrell2021

open DependencyGrammar Morphology
open Morphology (Word)

/-! ### Dependency locality -/

/-- The unshifted order of example (2), in which the object precedes the prepositional phrase. -/
def longObjectFirst : Graph 11 :=
  .ofArcs
    [Word.mk' "Lucy" .PROPN, Word.mk' "ate" .VERB, Word.mk' "the" .DET,
      Word.mk' "extremely" .ADV, Word.mk' "delicious" .ADJ, Word.mk' "bright" .ADV,
      Word.mk' "green" .ADJ, Word.mk' "broccoli" .NOUN, Word.mk' "with" .ADP,
      Word.mk' "a" .DET, Word.mk' "fork" .NOUN]
    1 [(1, 0, .nsubj), (1, 7, .obj), (7, 2, .det), (4, 3, .advmod), (7, 4, .amod),
      (6, 5, .advmod), (7, 6, .amod), (10, 8, .case), (10, 9, .det), (1, 10, .obl)]

/-- The shifted order of example (2), in which the prepositional phrase precedes the long
object. -/
def shifted : Graph 11 :=
  .ofArcs
    [Word.mk' "Lucy" .PROPN, Word.mk' "ate" .VERB, Word.mk' "with" .ADP, Word.mk' "a" .DET,
      Word.mk' "fork" .NOUN, Word.mk' "the" .DET, Word.mk' "extremely" .ADV,
      Word.mk' "delicious" .ADJ, Word.mk' "bright" .ADV, Word.mk' "green" .ADJ,
      Word.mk' "broccoli" .NOUN]
    1 [(1, 0, .nsubj), (1, 10, .obj), (10, 5, .det), (7, 6, .advmod), (10, 7, .amod),
      (9, 8, .advmod), (10, 9, .amod), (4, 2, .case), (4, 3, .det), (1, 4, .obl)]

theorem longObjectFirst_eq_reorderDependents :
    longObjectFirst = shifted.reorderDependents 1 (.swap ⟨4, by decide⟩ ⟨10, by decide⟩) :=
  Graph.ext (funext (by decide +kernel : ∀ x, _)) (funext₂ (by decide +kernel : ∀ x y, _))
    (by decide +kernel)

/-- Heavy NP shift cuts the verb's distance to the prepositional phrase from nine to three and
raises its distance to the object from six to nine, so the total dependency length falls: by
Behaghel's law at the verb, the phrases after it grow outward in the shifted order and not in the
unshifted one ((2)). -/
theorem heavyNPShift_shorter : shifted.totalLength < longObjectFirst.totalLength := by
  rw [longObjectFirst_eq_reorderDependents]
  exact (Graph.totalLength_lt_reorderDependents_iff (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2 (by decide +kernel)

/-! ### The information locality bound -/

section InformationLocality

open MeasureTheory ProbabilityTheory InformationTheory Finset

variable {Ω W Mem : Type*}

/-- `memoryState M m₀ w t` is the listener's memory state when the word at time `t` arrives. It
is reached from the initial state `m₀` by the memory encoding function `M`, which updates a state
with the word just heard. -/
def memoryState (M : Mem → W → Mem) (m₀ : Ω → Mem) (w : ℕ → Ω → W) : ℕ → Ω → Mem
  | 0 => m₀
  | t + 1 => fun ω ↦ M (memoryState M m₀ w t ω) (w t ω)

variable {w : ℕ → Ω → W} {M : Mem → W → Mem} {m₀ : Ω → Mem}

theorem exists_memoryState_eq_comp (t : ℕ) : ∃ g : (Fin t → W) × Mem → Mem,
    memoryState M m₀ w t = g ∘ fun ω ↦ (block w 0 t ω, m₀ ω) := by
  induction t with
  | zero => exact ⟨Prod.snd, rfl⟩
  | succ t ih =>
    obtain ⟨g, hg⟩ := ih
    exact ⟨fun p ↦ M (g (Fin.init p.1, p.2)) (p.1 (Fin.last t)), by
      funext ω; simp only [memoryState, hg]; rfl⟩

variable [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSingletonClass W] [Fintype W]
  [MeasurableSpace Mem] [MeasurableSingletonClass Mem] [Fintype Mem] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

theorem measurable_memoryState (hw : ∀ t, Measurable (w t)) (hm₀ : Measurable m₀) :
    ∀ t, Measurable (memoryState M m₀ w t)
  | 0 => hm₀
  | t + 1 => (measurable_of_finite (Function.uncurry M)).comp
      ((measurable_memoryState hw hm₀ t).prodMk (hw t))

theorem condEntropy_block_le_sum (hw : ∀ t, Measurable (w t)) (hm₀ : Measurable m₀) (T : ℕ) :
    H[block w 0 T | m₀ ; μ] ≤ ∑ t ∈ range T, H[w t | memoryState M m₀ w t ; μ] := by
  suffices h : H[fun ω ↦ (block w 0 T ω, m₀ ω) ; μ]
      ≤ H[m₀ ; μ] + ∑ t ∈ range T, H[w t | memoryState M m₀ w t ; μ] by
    linarith [chain_rule μ (measurable_block hw 0 T) hm₀]
  induction T with
  | zero =>
    have : (fun ω ↦ (block w 0 0 ω, m₀ ω)) = (fun m ↦ (Fin.elim0, m)) ∘ m₀ :=
      funext fun ω ↦ Prod.ext (Subsingleton.elim _ _) rfl
    rw [this, entropy_comp_of_injective μ hm₀ (measurable_of_finite _) (Prod.mk_right_injective _)]
    simp
  | succ T ih =>
    have hZ := (measurable_block hw 0 T).prodMk hm₀
    obtain ⟨g, hg⟩ := exists_memoryState_eq_comp (M := M) (m₀ := m₀) (w := w) T
    let e := (Equiv.prodAssoc W (Fin T → W) Mem).symm.trans
      ((Fin.snocEquiv fun _ ↦ W).prodCongr (Equiv.refl Mem))
    have hrec : (fun ω ↦ (block w 0 (T + 1) ω, m₀ ω)) = e ∘ fun ω ↦ (w T ω, block w 0 T ω, m₀ ω) :=
      funext fun ω ↦ Prod.ext (congrFun (block_zero_succ T) ω) rfl
    rw [hrec, entropy_comp_of_injective μ ((hw T).prodMk hZ) (measurable_of_finite _) e.injective,
      chain_rule μ (hw T) hZ, sum_range_succ, hg]
    linarith [condEntropy_le_condEntropy_comp μ (hw T) hZ g]

theorem condEntropy_memoryState_eq (hw : ∀ t, Measurable (w t)) (hm₀ : Measurable m₀)
    (hs : IsStationary (fun t ω ↦ (w t ω, memoryState M m₀ w t ω)) μ) (t : ℕ) :
    H[w t | memoryState M m₀ w t ; μ] = H[w 0 | m₀ ; μ] := by
  have h := (hs t 1).comp (u := fun v ↦ v 0) (measurable_pi_apply 0)
  simp only [block, Function.comp_def, Fin.val_zero, zero_add] at h
  exact h.condEntropy_eq (hw t) (measurable_memoryState hw hm₀ t) (hw 0) hm₀

variable (hw : ∀ t, Measurable (w t)) (hm₀ : Measurable m₀)
  (hs : IsStationary (fun t ω ↦ (w t ω, memoryState M m₀ w t ω)) μ) {T : ℕ} (hT : 0 < T)
  (hmem : H[m₀ ; μ] ≤ ∑ t ∈ Icc 1 T, t * distanceInfo w μ t)
include hw hm₀ hs hT hmem

theorem pastCondEntropy_le_condEntropy : pastCondEntropy w μ T ≤ H[w 0 | m₀ ; μ] := by
  have hblock := condEntropy_block_le_sum (μ := μ) (M := M) hw hm₀ T
  simp_rw [condEntropy_memoryState_eq hw hm₀ hs, sum_const, card_range, nsmul_eq_mul] at hblock
  have hb := measurable_block hw 0 T
  rw [sum_Icc_mul_distanceInfo hw (hs.comp measurable_fst), ← entropy_block hw] at hmem
  refine le_of_mul_le_mul_left ?_ (by exact_mod_cast hT : (0 : ℝ) < T)
  linarith [chain_rule μ hb hm₀, chain_rule μ hm₀ hb, entropy_comm μ hb hm₀,
    condEntropy_nonneg m₀ (block w 0 T) μ]

/-- A listener whose memory entropy is at most `∑ t ∈ Icc 1 T, t * I t` has average surprisal at
least the entropy rate plus the information beyond distance `T` (Theorem 1). -/
theorem information_locality_bound :
    entropyRate w μ + ∑' t, distanceInfo w μ (T + t + 1) ≤ H[w 0 | m₀ ; μ] :=
  entropyRate_add_tsum hw (hs.comp measurable_fst) T ▸
    pastCondEntropy_le_condEntropy hw hm₀ hs hT hmem

end InformationLocality

/-! ### The Japanese suffix template

The supplement tabulates the relative orders of the Japanese verb suffixes in attested forms,
each segmented into a stem and its suffixes. Every suffix gloss names a suffix of the Fragment,
and the suffixes of every form are licensed by its template. -/

/-- The paper's glosses of the Japanese suffixes, as suffixes of the Fragment. -/
def japaneseSuffix? : String → Option (Σ σ, Japanese.Verb.Exponent σ)
  | "CAUS" => some ⟨_, .sase⟩
  | "PASS" => some ⟨_, .rare⟩
  | "POT" => some ⟨_, .potential⟩
  | "POL" => some ⟨_, .mas⟩
  | "DESID" => some ⟨_, .tai⟩
  | "NEG" => some ⟨_, .na⟩
  | "PST" => some ⟨_, .ta⟩
  | "HORT" => some ⟨_, .yoo⟩
  | _ => none

/-- The suffixes a row's gloss line names after the stem. -/
def japaneseSuffixes (r : Datum) : List (Σ σ, Japanese.Verb.Exponent σ) :=
  r.glossLine.tail.filterMap japaneseSuffix?

/-- The supplement's Japanese forms. -/
def japaneseForms : List Datum :=
  Examples.all.filter (·.language = "nucl1643")

theorem japanese_forms_licensed :
    ∀ r ∈ japaneseForms, (japaneseSuffixes r).length + 1 = r.glossLine.length ∧
      Japanese.Verb.template.Licensed (japaneseSuffixes r) := by
  decide

/-! ### The Sesotho affix template

The paper's examples (2), the forms of [demuth-1992] its supplement tabulates, and two forms
from the corpus are segmented into a stem and its affixes; every gloss but the stem's names an
affix of the Fragment, and the affixes of every form are licensed by its template. -/

/-- The affixes a gloss names, the glosses being Demuth's labels, the corpus labels of the
supplement and the fused applicative perfect *-ets-*. Demuth's mood vowel is read as the
indicative ending. -/
def sesothoAffix : String → List (Σ σ, Sesotho.Verb.Exponent σ)
  | "SM" => [⟨_, .subject⟩]
  | "OBJ" => [⟨_, .object⟩]
  | "REFL" => [⟨_, .reflexive⟩]
  | "NEG" => [⟨_, .negative⟩]
  | "FUT" => [⟨_, .future⟩]
  | "POT" => [⟨_, .potential⟩]
  | "CAUS" => [⟨_, .causative⟩]
  | "NT" => [⟨_, .neuter⟩]
  | "APL" => [⟨_, .applicative⟩]
  | "CL" => [⟨_, .completive⟩]
  | "RC" => [⟨_, .reciprocal⟩]
  | "APL:PERF" => [⟨_, .applicative⟩, ⟨_, .perfect⟩]
  | "PASS" => [⟨_, .passive⟩]
  | "PERF" => [⟨_, .perfect⟩]
  | "M" => [⟨_, .indicative⟩]
  | "RL" => [⟨_, .relative⟩]
  | "WH" => [⟨_, .interrogative⟩]
  | _ => []

/-- The affixes a row's gloss line names, in linear order. -/
def sesothoAffixes (r : Datum) : List (Σ σ, Sesotho.Verb.Exponent σ) :=
  r.glossLine.flatMap sesothoAffix

/-- The paper's Sesotho forms. -/
def sesothoForms : List Datum :=
  Examples.all.filter (·.language = "sout2807")

theorem sesotho_forms_licensed :
    ∀ r ∈ sesothoForms, (r.glossLine.filter fun g ↦ (sesothoAffix g).isEmpty).length = 1 ∧
      Sesotho.Verb.template.Licensed (sesothoAffixes r) := by
  decide

/-- The Fragment's template with the paper's own suffix order, which places the passive before
the perfect. -/
def paperSesothoTemplate : AffixTemplate Sesotho.Verb.Slot :=
  { Sesotho.Verb.template with
    suffixSlots := [.reversive, .extension, .voice, .tense, .mood, .interrogativeRelative] }

-- (44)
theorem demuth_perfect_passive :
    Sesotho.Verb.template.Licensed (sesothoAffixes Examples.so6) ∧
      ¬ paperSesothoTemplate.Licensed (sesothoAffixes Examples.so6) := by
  decide

/-! ### Morpheme order and the relevance hierarchy

The paper compares its slots with [bybee-1985]'s hierarchy of valence, voice, aspect, tense,
mood and subject agreement, and claims that the valence and voice suffixes lie closer to the stem
than the tense, aspect and mood markers, and that Sesotho subject agreement lies farther out
than the tense and aspect prefixes. The slots are compared through the categories the paper
labels them with. -/

/-- The hierarchy category of a Sesotho affix position, when the paper's label is one. -/
def sesothoCategory? : Sesotho.Verb.Slot → Option RelevanceHierarchy
  | .subject => some .agreement
  | .negation => none
  | .tam => some .tense
  | .object => some .agreement
  | .reversive => none
  | .extension => some .valence
  | .voice => some .voice
  | .tense => some .tense
  | .mood => some .mood
  | .interrogativeRelative => none

/-- The Sesotho suffix order in Bybee's vocabulary, stem-outward. -/
def sesothoSuffixCategories : List RelevanceHierarchy :=
  Sesotho.Verb.template.suffixSlots.filterMap sesothoCategory?

/-- The Sesotho prefix order in Bybee's vocabulary, stem-outward. -/
def sesothoPrefixCategories : List RelevanceHierarchy :=
  Sesotho.Verb.template.prefixSlots.reverse.filterMap sesothoCategory?

/-- The hierarchy category of a Japanese suffix position, when the paper's label is one. -/
def japaneseCategory? : Japanese.Verb.Slot → Option RelevanceHierarchy
  | .derivation => none
  | .valence => some .valence
  | .voice => some .voice
  | .politeness => none
  | .desiderative => some .mood
  | .negation => none
  | .inflection => some .tense

/-- The Japanese suffix order in Bybee's vocabulary. -/
def japaneseCategories : List RelevanceHierarchy :=
  Japanese.Verb.template.suffixSlots.filterMap japaneseCategory?

theorem paper_sesotho_suffixes_respect_relevance :
    (paperSesothoTemplate.suffixSlots.filterMap sesothoCategory?).SortedLE := by decide

/-- The Fragment's suffix order, [demuth-1992]'s, has the perfect before the passive, tense
before voice, and is not sorted by the hierarchy: the paper's agreement rests on its order. -/
theorem sesotho_suffixes_violate_relevance : ¬ sesothoSuffixCategories.SortedLE := by decide

theorem sesotho_prefixes_violate_relevance :
    (∀ a ∈ sesothoCategory? .tam, ∀ b ∈ sesothoCategory? .subject, a < b) ∧
      ¬ sesothoPrefixCategories.SortedLE := by
  decide

theorem japanese_valence_voice_inside :
    japaneseCategories.Pairwise fun a b ↦ b ≤ .voice → a ≤ .voice := by
  decide

/-- The Japanese suffix order is nonetheless not sorted by the hierarchy: [bybee-1985]'s survey
ranks tense closer to the stem than mood, `Bybee1985.SurveyedCloser`, and the desiderative, a
mood suffix, precedes the final inflection, read as tense. The paper claims no order of mood
and tense. -/
theorem japanese_violates_surveyed_relevance :
    Bybee1985.SurveyedCloser .tense .mood ∧ ¬ japaneseCategories.SortedLE := by
  decide

end HahnDegenFutrell2021
