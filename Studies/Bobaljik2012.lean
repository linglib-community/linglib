module

public import Linglib.Morphology.Exponence.Containment.Contiguity
public import Mathlib.Logic.Relation
public import Linglib.Fragments.English.Adjectives
public import Linglib.Fragments.Latin.Adjectives
public import Linglib.Fragments.Slavic.Russian.Adjectives
public import Linglib.Data.Wordlist.Bobaljik2012
public import Linglib.Data.StructureDataset.Bobaljik2012

/-!
# Universals in comparative morphology

Bobaljik surveys comparative and superlative suppletion in some 300
languages and finds three root patterns — AAA, ABB, ABC — with *AAB
unattested and *ABA attested only in a Basque doublet that the book leaves
open (section 4.1.2): the Comparative-Superlative Generalization (1)–(2), beside
the Synthetic Superlative Generalization (3), the Root Suppletion
Generalization (4), and Lesslessness (5). All but the last follow from the
Containment Hypothesis (6) — the superlative contains the comparative —
under Late Insertion, Elsewhere ordering, and locality (8). A comparative
root allomorph is chosen in the superlative too, so ABA needs an accidental
homophony that Antihomophony (44) excludes; AAB needs a
superlative-conditioned allomorph with no comparative counterpart, which
adjacency (190) or the markedness condition (202) excludes; and a root sees
CMPR only when Merger has made the comparative synthetic (90), which is the
RSG, with the SSG as Merger's downward closure. The same locality condition
limits CSG1 to periphrastic superlatives that embed the comparative (§3.3.3),
so Russian *plox-oj – xuž-e – samyj plox-oj*, whose superlative embeds the
positive, is ABA without any homophony.

## Main definitions

* `czechBad`, `englishGood`, `englishBad`, `welshGood`, `latinBonus`: the
  book's vocabularies (39), (203), (194), (198), (204) as `SpanRule`s.
* `aabContextual`, `welshAAB`, `fakeAba`: the vocabularies behind the
  unattested shapes — (190), (201), and the homophony loophole of (44).
* `greekBad`, `russianBad`: the Modern Greek vocabulary (93) and its Russian
  counterpart.
* `positiveEmbedding`: the word extents of a superlative embedding the positive.
* `latinBonusNS`: the Latin entries in nanosyntax form.
* `Synthetic`, `Periphrastic`: a grade form of one word, and one of several.
* `rootPattern`, `Quantifier`: the root classes of a triple over the grades,
  and the triples of quantifiers.
* `BearsOnCSG`: a language of the broad sample with suppletion and a
  morphological superlative.
* `MorphComparative`, `MorphSuperlative`, `Records`: a table row's `M`
  columns, and the synthetic extents of a language's adjectives they record.

## Main results

* `isContiguous_iff_ne_basque`, `ne_aab`, `abc_iff`: of the 73 adjectival
  cognate triples of Table 4.1, read from `Data/Wordlist/Bobaljik2012`,
  every one is contiguous but the Basque doublet (143b), no triple is AAB,
  and the ABC ones are the triples (31) and p. 112 name.
* `quantifier_isContiguous_iff`, `bulgarian_armenian_eq_abb_comp`,
  `karelian_sources`, `exists_ungrammatical_of_not_isContiguous`: of the
  quantifier triples of Table 4.2, all but the three of (165) are
  contiguous; the Bulgarian and Armenian ones are ABB through a superlative
  embedding the positive, and the Karelian one is contradicted by the
  triple (170), its superlative rejected by the questionnaire.
* `csg1_of_ne_basque`, `basque_not_realized`: CSG1 holds of every other
  triple, and no antihomophonous vocabulary realizes the Basque one.
* `bearsOnCSG_names`, `eurasia_of_suppletion`,
  `exists_rootClasses_of_bearsOnCSG`: of the 148 languages of the broad
  sample, read from `Data/StructureDataset/Bobaljik2012`, four have suppletion and
  a morphological superlative, every language with suppletion is in Eurasia,
  and each of the four has a triple in Table 4.1.
* `exists_records_iff`, `ssg_exceptions`: a row records synthetic extents
  exactly when it satisfies the SSG, and of the rows of Tables A.1 and B.1
  only the four counterexamples §3.4.2 and §3.4.3 discuss fail it.
* `english_ssg`, `english_rsg`: (3) and (4) on the English Fragment.
* `czech_bad_abb`, `latin_realize_abc`, `welsh_good_abc`: the engine derives
  the book's paradigms.
* `aabContextual_not_adjacent`, `welshAAB_not_grounded`,
  `fakeAba_not_antihomophonous`: each unattested shape violates exactly one
  condition.
* `latin_sprl_needs_portmanteau`: ABC needs a portmanteau ((199)).
* `greek_comparative`: *pjo kak-ós*, not *pjo cheir-ós* ((94)).
* `csg1_iff_one_le`: with a suppletive comparative, CSG1 holds of the
  superlative exactly when its adjective word contains CMPR (§3.3.3).
* `greek_superlative`, `russian_bad_eq_ploxoj`: the Greek superlative inherits
  the suppletive root ((106a)) and the Russian one does not ((106d)), as the
  Fragment's *samyj plox-oj* shows.
* `periphrastic_of_aba`: on the Fragments a superlative on the positive's root
  after a comparative on another is periphrastic.
* `latin_ns_eq_dm`: nanosyntax and DM realize Latin alike.

## Implementation notes

Lesslessness (5) — no language has a synthetic comparative of inferiority
((278)–(279)) — is the book's most robust generalization but is not
derived here: its account, a polarity-reversing head under the Complexity
Condition, is a sketch in the book as well. The generalizations concern
relative superlatives only; absolute superlatives lack the comparative
component and its structure.

The book gives no Russian vocabulary. `russianBad` is built in the format of
the Greek (93), with the comparative root *xud-* that §6.4.4 identifies in
*xuž-e*.

## References

* [bobaljik-2012]
* [caha-2009]
-/

@[expose] public section

namespace Bobaljik2012

open Morphology Morphology.Exponence Morphology.Containment
open English.Adjectives

/-! ### Merger -/

section Merger

variable {n : ℕ} {F : Type*}

/-! ### Merger as successive-cyclic head bundling -/

/-- One application of Merger adjoins head `h` to the merged region `R`. Every head strictly
between the root and `h` must already be merged, since Merger cannot skip intervening heads, which
[bobaljik-2012] takes from the definition of Morphological Merger. For head movement the condition
is successive cyclicity. -/
def MergerStep [NeZero n] (R S : Finset (Fin n)) : Prop :=
  ∃ h : Fin n, 0 < h ∧ h ∉ R ∧ (∀ k : Fin n, 0 < k → k < h → k ∈ R) ∧ S = insert h R

/-- The merged regions reachable from the bare root (empty region) by
successive applications of Merger. -/
def MergerReachable [NeZero n] (R : Finset (Fin n)) : Prop :=
  Relation.ReflTransGen MergerStep ∅ R

theorem mergerReachable_Ioc [NeZero n] (t : Fin n) :
    MergerReachable (Finset.Ioc 0 t) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
  induction t using Fin.induction with
  | zero => rw [Finset.Ioc_self]; exact .refl
  | succ i ih =>
    refine ih.tail ⟨i.succ, i.succ_pos, ?_, ?_, ?_⟩
    · simp only [Finset.mem_Ioc, not_and, not_le]
      exact fun _ ↦ Fin.castSucc_lt_succ
    · exact fun k hk0 hkh ↦ Finset.mem_Ioc.mpr ⟨hk0, Fin.le_castSucc_iff.mpr hkh⟩
    · ext k
      simp only [Finset.mem_insert, Finset.mem_Ioc, Fin.ext_iff, Fin.lt_def,
        Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.val_zero]
      omega

/-- The regions reachable by successive Merger are exactly the initial
segments of the hierarchy, since the no-skipping condition forces every head
below a merged head to be merged. -/
theorem mergerReachable_iff [NeZero n] {R : Finset (Fin n)} :
    MergerReachable R ↔ ∃ t : Fin n, R = Finset.Ioc 0 t := by
  refine ⟨fun h ↦ ?_, fun ⟨t, ht⟩ ↦ ht ▸ mergerReachable_Ioc t⟩
  induction h with
  | refl => exact ⟨0, (Finset.Ioc_self 0).symm⟩
  | tail _ hstep ih =>
    obtain ⟨t, rfl⟩ := ih
    obtain ⟨h, hpos, hnot, hskip, rfl⟩ := hstep
    have hth : t < h := by
      rcases lt_or_ge t h with h' | h'
      · exact h'
      · exact absurd (Finset.mem_Ioc.mpr ⟨hpos, h'⟩) hnot
    refine ⟨h, ?_⟩
    ext k
    simp only [Finset.mem_insert, Finset.mem_Ioc]
    constructor
    · rintro (rfl | ⟨hk0, hkt⟩)
      · exact ⟨hpos, le_rfl⟩
      · exact ⟨hk0, le_trans hkt hth.le⟩
    · rintro ⟨hk0, hkh⟩
      rcases eq_or_lt_of_le hkh with rfl | hkh'
      · exact Or.inl rfl
      · exact Or.inr ⟨hk0, (Finset.mem_Ioc.mp (hskip k hk0 hkh')).2⟩

/-- Merged regions are downward closed in heads, so if the superlative head has merged, so has the
comparative head below it. This is the core of the Synthetic Superlative Generalization of
[bobaljik-2012] ch. 3. -/
theorem MergerReachable.mem_of_le [NeZero n] {R : Finset (Fin n)}
    (hR : MergerReachable R) {h k : Fin n} (hk0 : 0 < k) (hkh : k ≤ h)
    (hh : h ∈ R) : k ∈ R := by
  obtain ⟨t, rfl⟩ := mergerReachable_iff.mp hR
  exact Finset.mem_Ioc.mpr ⟨hk0, le_trans hkh (Finset.mem_Ioc.mp hh).2⟩

/-! ### The synthetic extent -/

/-- The synthetic extent of a lexeme's paradigm. Heads `1..wordTop` are realized word-internally
with the root, and grades above `wordTop` are periphrastic. By `mergerReachable_iff_exists_region`
the regions successive-cyclic Merger builds are exactly those of this form. -/
structure Synthesis (n : ℕ) where
  /-- The highest head merged into the root's word. -/
  wordTop : Fin n
  deriving DecidableEq, Repr

/-- The merged region of the lexeme's word, heads `1..wordTop`. -/
def Synthesis.region [NeZero n] (s : Synthesis n) : Finset (Fin n) :=
  Finset.Ioc 0 s.wordTop

/-- A region is Merger-reachable iff it is the region of some synthetic extent. -/
theorem mergerReachable_iff_exists_region [NeZero n] {R : Finset (Fin n)} :
    MergerReachable R ↔ ∃ s : Synthesis n, R = s.region :=
  mergerReachable_iff.trans
    ⟨fun ⟨t, ht⟩ ↦ ⟨⟨t⟩, ht⟩, fun ⟨s, hs⟩ ↦ ⟨s.wordTop, hs⟩⟩

theorem Synthesis.mergerReachable_region [NeZero n] (s : Synthesis n) :
    MergerReachable s.region :=
  mergerReachable_Ioc s.wordTop

/-- Grade `g` is realized synthetically when all its heads are word-internal. -/
def Synthesis.SyntheticAt (s : Synthesis n) (g : Fin n) : Prop :=
  g ≤ s.wordTop

instance (s : Synthesis n) (g : Fin n) : Decidable (s.SyntheticAt g) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Syntheticity is containment of the grade's heads in the merged
region. -/
theorem Synthesis.syntheticAt_iff_region [NeZero n] {s : Synthesis n} {g : Fin n} :
    s.SyntheticAt g ↔ Finset.Ioc 0 g ⊆ s.region := by
  refine ⟨fun h ↦ Finset.Ioc_subset_Ioc le_rfl h, fun hsub ↦ ?_⟩
  rcases eq_or_ne g 0 with rfl | hg
  · exact Fin.zero_le _
  · exact (Finset.mem_Ioc.mp
      (hsub (Finset.mem_Ioc.mpr ⟨(Fin.pos_iff_ne_zero' g).mpr hg, le_rfl⟩))).2

/-- Synthesis is downward closed, so a synthetic superlative entails a synthetic comparative. This
is the Synthetic Superlative Generalization of [bobaljik-2012] ch. 3, the grade-level shadow of
`MergerReachable.mem_of_le`. -/
theorem Synthesis.syntheticAt_of_le {s : Synthesis n} {g g' : Fin n}
    (h : s.SyntheticAt g) (h' : g' ≤ g) : s.SyntheticAt g' :=
  le_trans h' h

/-! ### Word-internal realization -/

/-- Realization within the lexeme's synthetic extent. At grade `g` rules see only the root's word,
which reaches head `min g wordTop`, so suppletion cannot be conditioned by material outside the
word ([bobaljik-2012]'s locality condition (90)). A periphrastic grade thus embeds the highest
synthetic form, as the Greek superlative *o cheiró-ter-os* embeds the comparative. A superlative
that embeds the positive instead, as Russian *samyj plox-oj* does (§3.3.3), is `realize`
precomposed with a choice of word extent for each grade. -/
def realizeIn (s : Synthesis n) (v : RuleSet (SpanRule n F)) : Paradigm n (Option F) :=
  fun g ↦ realize v (min g s.wordTop)

/-- At a synthetic grade, word-internal realization is realization. -/
theorem realizeIn_eq_realize_of_le {s : Synthesis n} {v : RuleSet (SpanRule n F)}
    {g : Fin n} (h : g ≤ s.wordTop) : realizeIn s v g = realize v g :=
  congrArg (realize v) (min_eq_left h)

/-- At a periphrastic grade, the root's word realizes as at `wordTop`, the highest grade whose
structure is word-internal. -/
theorem realizeIn_eq_realize_wordTop_of_le {s : Synthesis n}
    {v : RuleSet (SpanRule n F)} {g : Fin n} (h : s.wordTop ≤ g) :
    realizeIn s v g = realize v s.wordTop :=
  congrArg (realize v) (min_eq_right h)

/-- Word-internal realization is contiguous, since it is `realize` precomposed with the monotone
regrading `min · wordTop`. -/
theorem isContiguous_realizeIn {s : Synthesis n} {v : RuleSet (SpanRule n F)}
    (hAH : v.Antihomophonous) :
    IsContiguous (realizeIn s v) :=
  (isContiguous_realize hAH).comp_monotone fun _ _ h ↦ min_le_min_right _ h

/-- A lexeme with no Merger at all (`wordTop = 0`, fully periphrastic
paradigm) realizes the same root form at every grade. -/
theorem realizeIn_const_of_wordTop_eq_zero {s : Synthesis n}
    {v : RuleSet (SpanRule n F)} (h : (s.wordTop : ℕ) = 0) (g g' : Fin n) :
    realizeIn s v g = realizeIn s v g' := by
  have hle : ∀ x : Fin n, s.wordTop ≤ x := fun x ↦ by
    rw [Fin.le_def, h]; exact Nat.zero_le _
  rw [realizeIn_eq_realize_wordTop_of_le (hle g),
    realizeIn_eq_realize_wordTop_of_le (hle g')]

/-- Distinct root forms at two grades force Merger past their lower grade, so root suppletion at a
grade requires that grade's word to be synthetic. This is the general form of the Root Suppletion
Generalization of [bobaljik-2012] ch. 3; above `wordTop` the word realizes constantly
(`realizeIn_eq_realize_wordTop_of_le`). -/
theorem min_lt_wordTop_of_realizeIn_ne {s : Synthesis n}
    {v : RuleSet (SpanRule n F)} {g g' : Fin n}
    (h : realizeIn s v g ≠ realizeIn s v g') : min g g' < s.wordTop := by
  by_contra hle
  push Not at hle
  rw [realizeIn_eq_realize_wordTop_of_le (hle.trans (min_le_left g g')),
    realizeIn_eq_realize_wordTop_of_le (hle.trans (min_le_right g g'))] at h
  exact h rfl

/-- Root suppletion is limited to synthetic comparatives, the Root Suppletion Generalization of
[bobaljik-2012] ch. 3. A lexeme showing distinct root forms at two grades has undergone Merger at
least once, so its comparative is synthetic, which excludes *good – more bett*. -/
theorem rsg {s : Synthesis 3} {v : RuleSet (SpanRule 3 F)} {g g' : Fin 3}
    (h : realizeIn s v g ≠ realizeIn s v g') : s.SyntheticAt 1 := by
  have hlt := min_lt_wordTop_of_realizeIn_ne h
  rw [Fin.lt_def] at hlt
  rw [Synthesis.SyntheticAt, Fin.le_def, Fin.val_one]
  omega

end Merger

/-! ### CSG1 -/

/-- In a contiguous pattern a suppletive comparative, whose root differs from the positive's,
forces a suppletive superlative. This is CSG1 (1). -/
theorem csg1 {F : Type*} {p : Paradigm 3 F} (hc : IsContiguous p) (h : p 1 ≠ p 0) :
    p 2 ≠ p 0 :=
  fun h2 ↦ h (hc (i := 0) (j := 1) (k := 2) (by decide) (by decide) h2.symm).symm

/-! ### The suppletive triples (Tables 4.1 and 4.2)

The 73 adjectival cognate triples of Table 4.1, each with the root classes the book assigns its
grades: ABC for the triples (31) names and the Greek pair counted on p. 112, ABA for the Basque
doublet (143), and ABB for the rest, by the summary on p. 109. The quantifier triples of Table 4.2
follow in their own section. A triple counts once however many languages share it (section 1.3). -/

/-- The root pattern of a triple over the positive, the comparative and the superlative. -/
def rootPattern (r : Data.Wordlist.RootClasses Wordlist.Cell) : Paradigm 3 ℕ := fun g ↦
  (r.classOf (![Wordlist.positive, Wordlist.comparative, Wordlist.superlative] g)).getD 0

/-- A triple of quantifiers, which the book treats apart from adjectives since they may not be
adjectives in every language (p. 105). -/
def Quantifier (r : Data.Wordlist.RootClasses Wordlist.Cell) : Prop :=
  r.lexeme.parameterId ∈ ["many_much", "few"]

instance : DecidablePred Quantifier := fun r ↦
  inferInstanceAs (Decidable (r.lexeme.parameterId ∈ _))

/-- Of the more than 300 languages considered, 73 adjectival cognate triples (p. 105). -/
theorem adjectival_length : (Wordlist.rootClasses.filter (¬ Quantifier ·)).length = 73 := by
  decide

/-- Every triple has a suppletive comparative. -/
theorem suppletive_comparative :
    ∀ r ∈ Wordlist.rootClasses, rootPattern r 1 ≠ rootPattern r 0 := by
  decide +kernel

/-- Every adjectival triple but the Basque doublet (143b) is contiguous. -/
theorem isContiguous_iff_ne_basque :
    ∀ r ∈ Wordlist.rootClasses, ¬ Quantifier r →
      (IsContiguous (rootPattern r) ↔ r.id ≠ Wordlist.eus_good_on.roots.id) := by
  simp only [isContiguous_fin_three_iff]
  decide +kernel

/-- No triple, adjectival or quantifier, is AAB. -/
theorem ne_aab : ∀ r ∈ Wordlist.rootClasses,
    Setoid.ker (rootPattern r) ≠ Setoid.ker Paradigm.aab := by
  simp only [ne_eq, ker_eq_ker_aab_iff]
  decide +kernel

/-- The ABC triples are the four of (31) and the Greek pair counted on p. 112; no quantifier triple
is ABC. -/
theorem abc_iff : ∀ r ∈ Wordlist.rootClasses,
    Setoid.ker (rootPattern r) = Setoid.ker Paradigm.abc ↔
      r.id ∈ [Wordlist.lat_good.roots.id, Wordlist.cym_good.roots.id, Wordlist.sga_good.roots.id,
        Wordlist.pal_good.roots.id, Wordlist.grc_good_amein.roots.id] := by
  simp only [ker_eq_ker_abc_iff]
  decide +kernel

/-- CSG1 holds of every adjectival triple but the Basque doublet. -/
theorem csg1_of_ne_basque {r : Data.Wordlist.RootClasses Wordlist.Cell}
    (hr : r ∈ Wordlist.rootClasses) (hq : ¬ Quantifier r)
    (h : r.id ≠ Wordlist.eus_good_on.roots.id) : rootPattern r 2 ≠ rootPattern r 0 :=
  csg1 ((isContiguous_iff_ne_basque r hr hq).2 h) (suppletive_comparative r hr)

/-- No antihomophonous vocabulary realizes the Basque triple *on – hobe – on-en* (143b), which
needs the accidental homophony that Antihomophony (44) excludes: the problem section 4.1.2 leaves
open. -/
theorem basque_not_realized {v : RuleSet (SpanRule 3 ℕ)} (hv : v.Antihomophonous) :
    realize v ≠ some ∘ rootPattern Wordlist.eus_good_on.roots := fun h ↦ by
  have hc := isContiguous_realize hv
  rw [h, isContiguous_comp_iff (Option.some_injective ℕ)] at hc
  exact absurd hc (by decide)

/-! ### The broad sample (Appendix A)

The 148 languages of Table A.1, chosen on a quasi-random basis (section 1.3). Most languages
satisfy the generalizations for trivial reasons, lacking suppletion, superlatives or adjectives
(p. 16): a language bears on the CSG only with suppletion and a morphological superlative. -/

/-- A language of the sample bears on the CSG when the table gives it suppletion and a
morphological superlative not marked questionable. -/
def BearsOnCSG (r : StructureDataset.Row) : Prop :=
  (∃ v ∈ r.suppl, v.code = .yes) ∧ ∃ v ∈ r.sprl, v.code = .morphological ∧ v.questionable = false

instance (r : StructureDataset.Row) : Decidable (BearsOnCSG r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Four of the 148 languages bear on the CSG. -/
theorem bearsOnCSG_names :
    (StructureDataset.broadSample.filter (BearsOnCSG ·)).map (·.language.name) =
      ["Persian (Farsi)", "Czech", "Finnish", "Basque"] := by
  decide

/-- Every language of the sample with suppletion is in Eurasia: comparative suppletion with
morphological superlatives is confined to a Greater European area (p. 17). -/
theorem eurasia_of_suppletion : ∀ r ∈ StructureDataset.broadSample, (∃ v ∈ r.suppl, v.code = .yes) →
    ∃ v ∈ r.region, v.code = .eurasia := by
  decide +kernel

/-- Each language of the sample that bears on the CSG has a cognate triple in Table 4.1. -/
theorem exists_rootClasses_of_bearsOnCSG : ∀ r ∈ StructureDataset.broadSample, BearsOnCSG r →
    ∃ t ∈ Wordlist.rootClasses,
      ¬ Quantifier t ∧ some t.lexeme.languageId = r.language.glottocode := by
  decide +kernel

/-! ### The English Fragment -/

/-- A grade form of one word is synthetic, as *taller* is. -/
def Synthetic (f : List Morph) : Prop := (Morph.wordsAt .clitic f).length = 1

/-- A grade form of several words is periphrastic, as *more careful* is. -/
def Periphrastic (f : List Morph) : Prop := 1 < (Morph.wordsAt .clitic f).length

instance (f : List Morph) : Decidable (Synthetic f) := inferInstanceAs (Decidable (_ = _))

instance (f : List Morph) : Decidable (Periphrastic f) := inferInstanceAs (Decidable (_ < _))

/-- On the English Fragment a synthetic superlative comes with a synthetic comparative. This is
the SSG (3), which `Synthesis.syntheticAt_of_le` derives structurally. -/
theorem english_ssg :
    ∀ e ∈ allEntries, Synthetic e.comparison.superlative → Synthetic e.comparison.comparative := by
  decide

/-- On the English Fragment a comparative not on the positive's root is synthetic (*better*,
*worse*, never *more bett*). This is the RSG (4). -/
theorem english_rsg :
    ∀ e ∈ allEntries, e.comparison.comparative ≠ [] → .root e.form ∉ e.comparison.comparative →
      Synthetic e.comparison.comparative := by
  decide

/-! ### The Synthetic Superlative Generalization over both samples (§3.4)

The focused survey of Table B.1 adds 174 languages with morphological comparison or comparative
suppletion and their relatives (section 1.3). A table row records the synthetic extents of the
language's adjectives, so Merger's downward closure predicts the SSG (89) of every row. Over both
tables four rows fail it, the apparent counterexamples of §3.4.2 and §3.4.3: Western and Eastern
Armenian, whose superlative *amen-a-* may be a compound or sit on a null comparative affix; Zulu,
whose questionable *-kazi* may form absolute superlatives; and Alutor, whose brief description
omits the comparative suffix that the longer description of its sister Koryak records. -/

/-- The row has `M` in its CMPR column, optional or questionable included. -/
def MorphComparative (r : StructureDataset.Row) : Prop := ∃ v ∈ r.cmpr, v.code = .morphological

/-- The row has `M` in its SPRL column, optional or questionable included. -/
def MorphSuperlative (r : StructureDataset.Row) : Prop := ∃ v ∈ r.sprl, v.code = .morphological

instance : DecidablePred MorphComparative := fun r ↦
  inferInstanceAs (Decidable (∃ v ∈ r.cmpr, _))

instance : DecidablePred MorphSuperlative := fun r ↦
  inferInstanceAs (Decidable (∃ v ∈ r.sprl, _))

/-- A row records the synthetic extents `S` of a language's adjectives when its CMPR and SPRL
columns have `M` exactly when some adjective's comparative, respectively superlative, is
synthetic. -/
def Records (r : StructureDataset.Row) (S : Set (Synthesis 3)) : Prop :=
  (MorphComparative r ↔ ∃ s ∈ S, s.SyntheticAt 1) ∧ (MorphSuperlative r ↔ ∃ s ∈ S, s.SyntheticAt 2)

/-- A recorded row obeys the SSG (89), since Merger reaches the comparative head before the
superlative head (`Synthesis.syntheticAt_of_le`). -/
theorem Records.morphComparative {r : StructureDataset.Row} {S : Set (Synthesis 3)}
    (h : Records r S) (hs : MorphSuperlative r) : MorphComparative r :=
  let ⟨s, hS, h2⟩ := h.2.1 hs
  h.1.2 ⟨s, hS, Synthesis.syntheticAt_of_le h2 (by decide)⟩

/-- A row records some synthetic extents exactly when it satisfies the SSG. -/
theorem exists_records_iff {r : StructureDataset.Row} :
    (∃ S, Records r S) ↔ (MorphSuperlative r → MorphComparative r) := by
  refine ⟨fun ⟨S, h⟩ ↦ h.morphComparative, fun h ↦ ⟨{s | (MorphComparative r ∧ s.wordTop = 1) ∨
    (MorphSuperlative r ∧ s.wordTop = 2)}, ⟨fun hc ↦ ⟨⟨1⟩, .inl ⟨hc, rfl⟩, le_rfl⟩, ?_⟩,
    fun hs ↦ ⟨⟨2⟩, .inr ⟨hs, rfl⟩, le_rfl⟩, ?_⟩⟩
  · rintro ⟨s, (⟨hc, -⟩ | ⟨hs, -⟩), -⟩
    exacts [hc, h hs]
  · rintro ⟨⟨t⟩, (⟨-, rfl⟩ | ⟨hs, -⟩), ht⟩
    exacts [absurd ht (by decide), hs]

instance (r : StructureDataset.Row) : Decidable (∃ S, Records r S) :=
  decidable_of_iff _ exists_records_iff.symm

/-- The rows of the two samples that record no synthetic extents are the four of §3.4.2 and
§3.4.3. -/
theorem ssg_exceptions :
    ((StructureDataset.broadSample ++ StructureDataset.focusedSurvey).filter
      (fun r ↦ ¬ ∃ S, Records r S)).map (·.language.name) =
    ["Zulu", "Armenian (Western)", "Armenian (Eastern)", "Alutor"] := by
  decide

/-- Koryak, whose longer description §3.4.3 sets beside Alutor's, has `M` in both columns. -/
theorem koryak_morph : ∃ r ∈ StructureDataset.focusedSurvey, r.language.name = "Koryak" ∧
    MorphComparative r ∧ MorphSuperlative r := by
  decide +kernel

/-! ### The book's vocabularies (ch. 2, ch. 5)

Each vocabulary is run through the Elsewhere engine of
`Morphology/Exponence/Containment/Contiguity.lean`; the syncretism of the
realized cells is the root pattern. -/

/-- Czech BAD (39), with *hor-* under CMPR and *špatn-* elsewhere. -/
def czechBad : RuleSet (SpanRule 3 String) := [⟨"špatn", 0, none⟩, ⟨"hor", 0, some 1⟩]

/-- The comparative allomorph is chosen in the superlative, *špatn-ý, hor-ší, nej-hor-ší*, since
the superlative contains its context. -/
theorem czech_bad_realize : realize czechBad = ![some "špatn", some "hor", some "hor"] := by
  decide

theorem czech_bad_abb : Setoid.ker (realize czechBad) = Setoid.ker Paradigm.abb := by decide

/-- English GOOD (203), with *bett-* under CMPR and *good* elsewhere. -/
def englishGood : RuleSet (SpanRule 3 String) := [⟨"good", 0, none⟩, ⟨"bett", 0, some 1⟩]

theorem english_good_abb : Setoid.ker (realize englishGood) = Setoid.ker Paradigm.abb := by decide

/-- English BAD (194), with the √ROOT+CMPR portmanteau *worse* and *bad* elsewhere. -/
def englishBad : RuleSet (SpanRule 3 String) := [⟨"bad", 0, none⟩, ⟨"worse", 1, none⟩]

theorem english_bad_abb : Setoid.ker (realize englishBad) = Setoid.ker Paradigm.abb := by decide

/-- Welsh GOOD (198), with the √ROOT+CMPR portmanteaus *gor-* under SPRL and *gwell*, and *da*
elsewhere. -/
def welshGood : RuleSet (SpanRule 3 String) :=
  [⟨"da", 0, none⟩, ⟨"gwell", 1, none⟩, ⟨"gor", 1, some 2⟩]

/-- Welsh *da, gwell, gor-au* is ABC, since the superlative exponent is a portmanteau. -/
theorem welsh_good_abc : Setoid.ker (realize welshGood) = Setoid.ker Paradigm.abc := by decide

/-- Latin GOOD (204), with the √ROOT+CMPR portmanteau *opt-* under SPRL, the root allomorph
*mel-* under CMPR, and *bon* elsewhere. Since *opt-* expones the CMPR cell, *-ior* has nothing to
realize, which gives *opt-imus* and not *\*opt-ior-imus*. -/
def latinBonus : RuleSet (SpanRule 3 String) :=
  [⟨"bon", 0, none⟩, ⟨"mel", 0, some 1⟩, ⟨"opt", 1, some 2⟩]

theorem latin_bonus_realize : realize latinBonus = ![some "bon", some "mel", some "opt"] := by
  decide

theorem latin_realize_abc : Setoid.ker (realize latinBonus) = Setoid.ker Paradigm.abc := by decide

/-- Latin satisfies every condition the CSG2 derivation uses. -/
theorem latin_wellformed :
    Adjacent latinBonus ∧ Grounded latinBonus ∧ latinBonus.Antihomophonous := by decide

/-- Latin is not terminal, and must not be, since terminal adjacent rules plateau at the
comparative (`realize_const_of_terminal_adjacent`), which would exclude ABC. -/
theorem latin_not_terminal : ¬ Terminal latinBonus := by decide

/-- The superlative winner is the portmanteau *opt-*. -/
theorem latin_superlative_portmanteau :
    latinBonus.selectBy SpanRule.threshold 2 = some ⟨"opt", 1, some 2⟩ := by
  decide

/-- ABC needs a portmanteau ((199), §5.3.1). Under adjacency, distinct comparative and
superlative cells force a winner exponing more than the root. -/
theorem latin_sprl_needs_portmanteau :
    ∃ it ∈ latinBonus, latinBonus.selectBy SpanRule.threshold 2 = some it ∧
      0 < (it.spans : ℕ) :=
  exists_portmanteau_of_ne (by decide) (by decide)

/-! ### The unattested shapes

AAB has two routes, each closed by one condition: a root allomorph
conditioned by a nonadjacent SPRL ((190), (45)), and a portmanteau
conditioned by SPRL with no comparative-level counterpart ((201)). Surface
ABA has one, accidental homophony, closed by Antihomophony ((44)). -/

/-- The vocabulary (190), with *be(tt)-* conditioned by SPRL across the comparative. -/
def aabContextual : RuleSet (SpanRule 3 String) := [⟨"good", 0, none⟩, ⟨"bett", 0, some 2⟩]

theorem aabContextual_realizes_aab :
    Setoid.ker (realize aabContextual) = Setoid.ker Paradigm.aab := by decide

/-- Its context skips the comparative, so adjacency excludes it. -/
theorem aabContextual_not_adjacent : ¬ Adjacent aabContextual := by decide

/-- The vocabulary (201), with *gor-* restricted to the superlative and no comparative-level
counterpart, which gives *\*da – da-ch – gor-au*. -/
def welshAAB : RuleSet (SpanRule 3 String) := [⟨"da", 0, none⟩, ⟨"gor", 1, some 2⟩]

theorem welshAAB_realizes_aab : Setoid.ker (realize welshAAB) = Setoid.ker Paradigm.aab := by decide

/-- The node [GOOD, CMPR] has a context-sensitive rule and no context-free one, which (202)
excludes. -/
theorem welshAAB_not_grounded : ¬ Grounded welshAAB := by decide

/-- By `realize_const_of_grounded`, the AAB cells refute Antihomophony and (202) together. -/
theorem welshAAB_blocked : ¬ (welshAAB.Antihomophonous ∧ Grounded welshAAB) :=
  fun ⟨hAH, hG⟩ ↦
    absurd (realize_const_of_grounded hAH hG (by decide) (by decide)) (by decide)

/-- A superlative allomorph accidentally homophonous with the positive yields surface ABA, the
loophole that Antihomophony (44) closes. -/
def fakeAba : RuleSet (SpanRule 3 String) :=
  [⟨"A", 0, none⟩, ⟨"B", 0, some 1⟩, ⟨"A", 0, some 2⟩]

theorem fakeAba_realizes_aba : Setoid.ker (realize fakeAba) = Setoid.ker Paradigm.aba := by decide

theorem fakeAba_not_antihomophonous : ¬ fakeAba.Antihomophonous := by decide

/-! ### Periphrasis and locality (§3.3) -/

/-- Modern Greek BAD (93), with *cheiró-* under CMPR and *kak-* elsewhere. -/
def greekBad : RuleSet (SpanRule 3 String) := [⟨"kak", 0, none⟩, ⟨"cheiró", 0, some 1⟩]

/-- With Merger the comparative is *cheiró-ter-os*. Without it the root cannot see CMPR, and the
periphrastic comparative is *pjo kak-ós*, not *\*pjo cheir-ós* (94), which is the RSG from
locality (90). -/
theorem greek_comparative :
    realizeIn (⟨1⟩ : Synthesis 3) greekBad 1 = some "cheiró" ∧
      realizeIn (⟨0⟩ : Synthesis 3) greekBad 1 = some "kak" := by
  decide

/-- Greek's distinct root forms certify its comparative as synthetic, by the engine's RSG. -/
theorem greek_rsg : (Synthesis.mk 1 : Synthesis 3).SyntheticAt 1 :=
  rsg (s := ⟨1⟩) (v := greekBad) (g := 1) (g' := 0) (by decide)

/-! ### Periphrastic superlatives (§3.3.3)

A periphrastic superlative may embed the comparative word, as Greek
*o cheiró-ter-os* does, or the positive, as Russian *samyj plox-oj* does. By
locality (90) only the first inherits a suppletive comparative root, so CSG1
holds of the first type and fails for the second. -/

/-- With a suppletive comparative, CSG1 holds of the superlative exactly when the superlative's
adjective word contains the comparative head. -/
theorem csg1_iff_one_le {F : Type*} {e : Fin 3 → Fin 3} (he : ∀ g, e g ≤ g)
    {v : RuleSet (SpanRule 3 F)} (hAH : v.Antihomophonous)
    (h : realize v (e 1) ≠ realize v (e 0)) :
    realize v (e 2) ≠ realize v (e 0) ↔ 1 ≤ e 2 := by
  have h0 : e 0 = 0 := Fin.le_zero_iff.mp (he 0)
  have h1 : e 1 = 1 := by
    have := he 1
    by_contra hne
    exact h (by rw [h0, show e 1 = 0 by omega])
  refine ⟨fun h2 ↦ ?_, fun h2 h20 ↦ h ?_⟩
  · by_contra hlt
    exact h2 (by rw [h0, show e 2 = 0 by omega])
  · rw [h0] at h20 ⊢
    rw [h1]
    exact (isContiguous_realize hAH (Fin.zero_le _) h2 h20.symm).symm

/-- The periphrastic superlative *o cheiró-ter-os* (106a) embeds the comparative word, so it
inherits the suppletive root. -/
theorem greek_superlative : realizeIn (⟨1⟩ : Synthesis 3) greekBad 2 = some "cheiró" := by
  decide

/-- Russian BAD, with *xud-* under CMPR and *plox-* elsewhere. -/
def russianBad : RuleSet (SpanRule 3 String) := [⟨"plox", 0, none⟩, ⟨"xud", 0, some 1⟩]

theorem russianBad_antihomophonous : russianBad.Antihomophonous := by decide

/-- The word extents of a synthetic comparative and a superlative embedding the positive, as in
*samyj sux-oj* (107d). -/
def positiveEmbedding : Fin 3 → Fin 3 := ![0, 1, 0]

/-- *Plox-oj, xuž-e, samyj plox-oj* (106d) is ABA although the vocabulary is antihomophonous,
since the superlative's adjective word lacks CMPR. The Russian Fragment's superlative is that one:
periphrastic and on the positive's root, after a comparative on another. -/
theorem russian_bad_eq_ploxoj :
    Setoid.ker (realize russianBad ∘ positiveEmbedding) = Setoid.ker Paradigm.aba ∧
      Periphrastic Russian.Adjectives.ploxoj.comparison.superlative ∧
      .root Russian.Adjectives.ploxoj.form ∈ Russian.Adjectives.ploxoj.comparison.superlative ∧
      .root Russian.Adjectives.ploxoj.form ∉ Russian.Adjectives.ploxoj.comparison.comparative := by
  decide

/-- With a superlative embedding the comparative, as in Greek, the same vocabulary is ABB. -/
theorem russian_bad_comparative_embedding :
    Setoid.ker (realizeIn ⟨1⟩ russianBad) = Setoid.ker Paradigm.abb := by
  decide

/-- The literary synthetic superlative *nai-xud-š-ij* is built on the suppletive root, so the
fully synthetic paradigm is ABB, as the locality condition predicts. -/
theorem russian_bad_synthetic_abb : Setoid.ker (realize russianBad) = Setoid.ker Paradigm.abb := by
  decide

/-- In the English, Latin and Russian Fragments a superlative on the positive's root after a
comparative on another is periphrastic, embedding the positive, so every morphological superlative
satisfies CSG1. -/
theorem periphrastic_of_aba :
    ∀ e ∈ allEntries.map (·.toAdjective) ++ Latin.Adjectives.allEntries ++
        Russian.Adjectives.allEntries,
      e.comparison.comparative ≠ [] → .root e.form ∉ e.comparison.comparative →
        .root e.form ∈ e.comparison.superlative → Periphrastic e.comparison.superlative := by
  simp only [List.mem_append, or_imp, forall_and, List.forall_mem_map]
  exact ⟨⟨by decide, by decide⟩, by decide⟩

/-! ### The quantifier triples (Table 4.2)

Of the quantifier triples, all but three are ABB; the three apparent ABA triples are Karelian,
Armenian and Bulgarian (165). Bulgarian *naj* is a freestanding particle (pp. 127-128) and Armenian
*amena-* a compound with *amen* 'all' (pp. 128-129), so their superlatives embed the positive, as
Russian *samyj plox-oj* does. The Karelian ABA comes from Zajkov's dictionary; the online
dictionary gives the ABB triple (170), which a questionnaire of seven speakers bears out
(pp. 129-131), none of whom gave or recognized Zajkov's superlative. -/

/-- Every quantifier triple but the three of (165) is contiguous. -/
theorem quantifier_isContiguous_iff : ∀ r ∈ Wordlist.rootClasses, Quantifier r →
    (IsContiguous (rootPattern r) ↔
      r.id ∉ [Wordlist.krl_many.roots.id, Wordlist.hye_many.roots.id,
        Wordlist.bul_many.roots.id]) := by
  simp only [isContiguous_fin_three_iff]
  decide +kernel

/-- The Bulgarian and Armenian triples are ABB seen through a superlative that embeds the
positive, as (168) and (169) analyse them. -/
theorem bulgarian_armenian_eq_abb_comp :
    ∀ r ∈ [Wordlist.bul_many.roots, Wordlist.hye_many.roots],
      Setoid.ker (rootPattern r) = Setoid.ker (Paradigm.abb ∘ positiveEmbedding) := by
  decide

/-- The two Karelian sources disagree: Zajkov's triple (165a) is ABA, the triple (170) ABB. -/
theorem karelian_sources :
    Setoid.ker (rootPattern Wordlist.krl_many.roots) = Setoid.ker Paradigm.aba ∧
      Setoid.ker (rootPattern Wordlist.krl_many_onego.roots) = Setoid.ker Paradigm.abb := by
  decide

/-- The one quantifier triple that is not contiguous and that no parse makes ABB, Zajkov's
Karelian (165a), has a form another source rejects in its cell: no respondent of the
questionnaire gave or recognized *äij-in* (p. 130). -/
theorem exists_ungrammatical_of_not_isContiguous : ∀ r ∈ Wordlist.rootClasses, Quantifier r →
    ¬ IsContiguous (rootPattern r) →
    r.id ∉ [Wordlist.hye_many.roots.id, Wordlist.bul_many.roots.id] →
    ∃ f ∈ r.forms, ∃ g ∈ Wordlist.marked, g.judgment = .ungrammatical ∧ g.cell = f.cell ∧
      g.form = f.form ∧ g.lexeme.id = r.lexeme.id := by
  simp only [isContiguous_fin_three_iff]
  decide +kernel

/-! ### The nanosyntax reading

The book treats *opt-* and *gor-* as portmanteaus by Fusion or insertion at
a nonterminal node, citing [caha-2009] among others (§5.3.1). Caha's
lexicon does it with context-free entries storing successively larger
constituents, competing under the Superset Principle. -/

/-- The Latin entries as a nanosyntax lexicon. -/
def latinBonusNS : RuleSet (SupersetRule 3 String) := [⟨"bon", 0⟩, ⟨"mel", 1⟩, ⟨"opt", 2⟩]

/-- Superset spellout derives the same paradigm with no contextual
apparatus. -/
theorem latin_ns_spellout : spellout latinBonusNS = ![some "bon", some "mel", some "opt"] := by
  decide

/-- The two frameworks realize Latin cell for cell — the concrete face of
`spelloutGenerable_iff_generable`. -/
theorem latin_ns_eq_dm : spellout latinBonusNS = realize latinBonus :=
  latin_ns_spellout.trans latin_bonus_realize.symm

end Bobaljik2012
