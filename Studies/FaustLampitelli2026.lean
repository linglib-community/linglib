module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Phonology.GovernmentPhonology.ElementTheory
public import Linglib.Phonology.GovernmentPhonology.EmptyCategoryPrinciple
public import Linglib.Phonology.RuleInteraction
public import Linglib.Phonology.Segmental.NaturalClass
public import Linglib.Fragments.Tigrinya.Phonology
public import Linglib.Fragments.Tigre.Phonology
public import Linglib.Data.Examples.FaustLampitelli2026
public import Linglib.Data.Examples.Languages

/-!
# Faust and Lampitelli (2026): Guttural syneresis in Tigrinya and Tigre

In Tigrinya and Tigre a low vowel in an open syllable before a guttural is syncopated, as in
[sɨmʕ-i] from /s_mʌʕ-i/, the way /i/ is before /j/, as in [sʌtj-u] from /sʌtij-u/. In Element
Theory the gutturals and the low vowels share the element |A| as the glide and the high vowel
share |I|, and the analysis runs in Strict CV with the lateral relations of Government Phonology.

We define a form as a sequence of CV units and three operations on forms. `fusion` joins the
element that is the whole melody of a vowel with the same element of an adjacent consonant: the
vowel then shares the element with what follows, or is licensed by its own onset. `dissociation`
empties a nucleus that shares its element with what follows when the next nucleus governs.
`epenthesis` marks the empty nuclei that must be realized, and `realizations` realizes each as
the weak vowel or as a copy of the vowel across a guttural. `derive` applies the three in this
order.

For every element, a nucleus is emptied exactly when its onset lacks the element, what follows has
it, and the next nucleus governs (`dissociation_empty_iff`); otherwise the fused vowel stays,
lowered when the element is |A| and before its glide when it is |I|. The attested forms are
realizations of the derived forms (`mem_realizations_of_not_retains`), except the Tigrinya forms
that keep a stem-initial nucleus the derivation empties (`notMem_realizations_of_retains`), which
requiring that nucleus to be realized derives (`mem_realizations_stemStart_of_retains`). Each
operation applies to the output of the one before it and not to the input (`feeds_fusion`,
`feeds_dissociation`), and no operation applies to a derived form of the rows
(`derive_isFixedPt`). Trans-guttural harmony restores the environment of fusion and dissociation
(`feeds_harmonized`): a derivation that read the harmonized form again would not end on /s_ħʌb/
(`derive_harmonized_pull`) and would syncopate [sʌmaʕaku] (`realizations_harmonized_37d`).

## Implementation notes

* The consonants and roots are those of the Tigrinya and Tigre fragments, and the surface forms
  are lists of their segments. `read` reads an attested form's transcription through the PHOIBLE
  inventory of its language; `image_segment_eq_vowels` shows that the vowels are the Tigrinya
  fragment's.
* A pattern is a prefix and a stem of positions (radical, geminable radical, fixed segment)
  with nuclei, instantiated by a root. Gutturals do not geminate, so a geminable position
  holding a guttural is a single unit. The prefixes tɨ- and mɨ- carry empty nuclei; the
  causative ʔʌ- is lexical.
* Government is that of `GovernmentPhonology`, of which the paper states a simplified version.
  The final nucleus may be empty, does not govern, and licenses, which leaves a final guttural
  licensed; [scheer-zikova-2010] take a final nucleus to govern and license together or to do
  neither.
* The paper gives the mid vowels as |A| with |I| or |U|; here |I| and |U| are their heads. It
  derives the lowering of a fused vowel from the span of its |A| and writes [a] as headed |A|;
  `headed` makes the fused element the head of the vowel.
* A consonant has a melody when it is a guttural or a glide, |I| for [j] and |U| for [w]; the
  palatals and the ejectives, which contain |I| and |A| and never trigger syneresis, have none.
  A long [iː] is read as [i] before [j], one |I| on a nucleus and the next onset.
* The 3FPL forms of the perfective paradigms, whose suffix vowel is not among the vowels the
  paper lists, are not recorded.
* `fusion` also joins two /a/s in successive nuclei, as in the derivation of [mɨ-bɨrak] from
  /m_-barak/.
* `epenthesis` marks the nuclei that `GovernmentPhonology.leftward` expresses, the realization
  from the left, so that the derived forms satisfy the Empty Category Principle
  (`emptyCategoryPrinciple_surface`). `pronounced_eq_obligatory_iff` compares it with the
  obligatory realization, which is decided from the right: they differ where the dissociated
  nucleus is the third of three empty nuclei, where the realization from the left gives C▪C_C▪C.
* Trans-guttural harmony is optional, so `realizations` lists every option. `harmonized` reads
  one harmonized surface form back as an underlying form.
* The postvocalic spirantization of b ([nɨβaħ]) is outside the analysis; `read` takes β as b.

## TODO

* The ejectives, which lower a vowel and never syncopate it, are not derived.
* `derive_isFixedPt` is stated of the rows. Of every form, `epenthesis_epenthesis` shows that
  epenthesis marks nothing further; that fusion and dissociation do not apply to a derived form
  is not proved.

## References

* [faust-lampitelli-2026]
* [kaye-lowenstamm-vergnaud-1985]
* [backley-2011]
* [angoujard-1995]
* [lowenstamm-1996]
* [scheer-2004]
* [kaye-lowenstamm-vergnaud-1990]
* [charette-1991]
* [segeral-scheer-2001]
* [scheer-zikova-2010]
* [kaye-1992]
* [bye-2011]
* [buckley-2000]
-/

@[expose] public section

namespace FaustLampitelli2026

open Morphology ElementTheory GovernmentPhonology Phonology
open Examples (Example)

/-! ### Vowels and gutturals -/

/-- The vowels of Tigrinya and Tigre, six full qualities and the weak [ɨ] (p. 5). -/
inductive Vowel where
  | a
  | aBare
  | i
  | u
  | e
  | o
  | weak
  deriving DecidableEq, Repr, Fintype

/-- The vowel a letter of the paper's transcription writes. -/
def Vowel.ofLetter? : String → Option Vowel
  | "a" => some .a
  | "ʌ" => some .aBare
  | "i" => some .i
  | "u" => some .u
  | "e" => some .e
  | "o" => some .o
  | "ɨ" => some .weak
  | _ => none

/-- `v.segment` is the vowel `v` in the Tigrinya fragment, whose vowels are those of Tigre. -/
def Vowel.segment : Vowel → Phonology.Segment
  | .a => Tigrinya.Phonology.a
  | .aBare => Tigrinya.Phonology.«ʌ»
  | .i => Tigrinya.Phonology.i
  | .u => Tigrinya.Phonology.u
  | .e => Tigrinya.Phonology.e
  | .o => Tigrinya.Phonology.o
  | .weak => Tigrinya.Phonology.«ɨ»

theorem Vowel.segment_injective : Function.Injective Vowel.segment := by decide +kernel

/-- `Vowel.segment` as an embedding of the vowels into the segments. -/
def Vowel.segmentEmbedding : Vowel ↪ Phonology.Segment := ⟨segment, segment_injective⟩

@[simp] theorem Vowel.coe_segmentEmbedding : ⇑Vowel.segmentEmbedding = Vowel.segment := rfl

theorem image_segment_eq_vowels :
    Finset.univ.map Vowel.segmentEmbedding = Tigrinya.Phonology.vowels := by
  decide +kernel

/-- The low vowels are [a] and [ʌ]. -/
def Vowel.IsLow : Vowel → Prop
  | .a | .aBare => True
  | _ => False

instance : DecidablePred Vowel.IsLow := fun v ↦ by cases v <;> unfold Vowel.IsLow <;> infer_instance

/-- The four gutturals are the glottals [ʔ, h] and the pharyngeals [ʕ, ħ]. -/
inductive Guttural where
  | glottalStop
  | h
  | pharyngealVoiced
  | pharyngealVoiceless
  deriving DecidableEq, Repr, Fintype

/-- `g.segment` is the guttural `g` in the Tigrinya fragment, whose gutturals are those of
Tigre. -/
def Guttural.segment : Guttural → Phonology.Segment
  | .glottalStop => Tigrinya.Phonology.«ʔ»
  | .h => Tigrinya.Phonology.h
  | .pharyngealVoiced => Tigrinya.Phonology.«ʕ»
  | .pharyngealVoiceless => Tigrinya.Phonology.ħ

theorem Guttural.segment_injective : Function.Injective Guttural.segment := by decide +kernel

/-- `Guttural.segment` as an embedding of the gutturals into the segments. -/
def Guttural.segmentEmbedding : Guttural ↪ Phonology.Segment := ⟨segment, segment_injective⟩

@[simp] theorem Guttural.coe_segmentEmbedding : ⇑Guttural.segmentEmbedding = Guttural.segment :=
  rfl

/-- The pharyngeals are [ʕ] and [ħ]. -/
def Guttural.IsPharyngeal : Guttural → Prop
  | .pharyngealVoiced | .pharyngealVoiceless => True
  | _ => False

instance : DecidablePred Guttural.IsPharyngeal :=
  fun g ↦ by cases g <;> unfold Guttural.IsPharyngeal <;> infer_instance

-- fn. 15: whether the gutturals are a natural class
theorem not_isNaturalClass_gutturals :
    ¬ Phonology.IsNaturalClass Tigrinya.Phonology.consonants
      (Finset.univ.map Guttural.segmentEmbedding) := by
  decide +kernel

/-! ### Element-theoretic representations (20)–(22) -/

/-- `vowelET v` is the melody of the vowel `v` (21)–(22). [ʌ] is |A| and [a] headed |A|, the mid
vowels combine |A| with |I| or |U|, and the weak vowel is the realization of an empty nucleus. -/
def vowelET : Vowel → MR
  | .a => .headedSimplex .A
  | .aBare => .simplex .A
  | .i => .headedSimplex .I
  | .u => .headedSimplex .U
  | .e => .headedSimplex .I ⊔ .simplex .A
  | .o => .headedSimplex .U ⊔ .simplex .A
  | .weak => ⊥

/-- `gutturalET g` is the melody of the guttural `g`. Every guttural contains |A|, and the
pharyngeals are headed by it (20). -/
def gutturalET : Guttural → MR
  | .glottalStop => .headedSimplex .glottal ⊔ .simplex .A
  | .h => .headedSimplex .H ⊔ .simplex .A
  | .pharyngealVoiceless => .headedSimplex .A ⊔ .simplex .glottal ⊔ .simplex .H
  | .pharyngealVoiced => .headedSimplex .A ⊔ .simplex .glottal ⊔ .simplex .H ⊔ .simplex .L

theorem mem_elements_gutturalET : ∀ g : Guttural, .A ∈ (gutturalET g).elements := by decide

theorem mem_heads_gutturalET_iff : ∀ g : Guttural, .A ∈ (gutturalET g).heads ↔ g.IsPharyngeal := by
  decide

/-- The element that is the whole melody of a vowel, if one is: |A| for the low vowels of (21),
|I| and |U| for the high vowels. The mid vowels carry |A| in a complex expression, which blocks
fusion (§3.2.2). -/
def Vowel.element? (v : Vowel) : Option Element :=
  [Element.A, .I, .U].find? fun e ↦ (vowelET v).elements = {e}

theorem element?_eq_some_A_iff_isLow : ∀ v : Vowel, v.element? = some .A ↔ v.IsLow := by decide

/-- The vowel with a given melody, if any. -/
def Vowel.ofMR? (m : MR) : Option Vowel :=
  [Vowel.a, .aBare, .i, .u, .e, .o, .weak].find? (vowelET · = m)

/-- A fused vowel is realized with the fused element as its head, so that [ʌ] lowers to [a]
((21), (27)). -/
def headed (e : Element) (v : Vowel) : Vowel :=
  (Vowel.ofMR? (vowelET v ⊔ .headedSimplex e)).getD v

theorem headed_aBare : headed .A .aBare = .a := by decide

theorem headed_headed : ∀ (e : Element) (v : Vowel), headed e (headed e v) = headed e v := by
  intro e v; cases e <;> cases v <;> decide

/-! ### Strict CV forms -/

/-- The melody of a consonant: that of a guttural (20), and |I| or |U| for a glide, the element of
a high vowel in a consonantal position (3). Other consonants carry no representation here, since
the palatals and the ejectives contain |I| and |A| but never trigger syneresis (fn. 8). -/
def consET (c : Phonology.Segment) : MR :=
  if c = Tigrinya.Phonology.j then .simplex .I
  else if c = Tigrinya.Phonology.w then .simplex .U
  else (([.glottalStop, .h, .pharyngealVoiced, .pharyngealVoiceless] : List Guttural).find?
    (·.segment = c)).elim ⊥ gutturalET

/-- `Has e c` says that the melody of the consonant `c` contains the element `e`. -/
def Has (e : Element) (c : Phonology.Segment) : Prop := e ∈ (consET c).elements

instance (e : Element) : DecidablePred (Has e) := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

theorem has_A_segment : ∀ g : Guttural, Has .A g.segment := by decide +kernel

/-- A nucleus in the course of a derivation (29) is empty, empty but to be realized (▪), or a
vowel. A vowel fused with an adjacent |A| either shares that |A| with what follows ((26), (27))
or is licensed by its own onset, with which it forms a self-licensing domain (28). -/
inductive Nuc where
  | empty
  | mark
  | vowel (v : Vowel)
  | shared (v : Vowel)
  | licensed (v : Vowel)
  deriving DecidableEq, Repr

/-- The vowel a nucleus holds, fused or not. -/
def Nuc.vowel? : Nuc → Option Vowel
  | .vowel v | .shared v | .licensed v => some v
  | .empty | .mark => none

/-- A CV unit ([lowenstamm-1996]). -/
structure CV where
  c : Phonology.Segment
  v : Nuc
  deriving DecidableEq

/-- A form is a strict iteration of CV units. -/
abbrev Form := List CV

/-- The consonant at `i` contains the element `e`. -/
def HasAt (e : Element) (f : Form) (i : ℕ) : Prop :=
  match f[i]? with
  | some u => Has e u.c
  | none => False

instance (e : Element) (f : Form) (i : ℕ) : Decidable (HasAt e f i) := by
  unfold HasAt; split <;> infer_instance

/-- The nucleus at `i` holds an unfused vowel headed by |A|, which is /a/. -/
def HeadedAAt (f : Form) (i : ℕ) : Prop :=
  match f[i]? with
  | some ⟨_, .vowel v⟩ => .A ∈ (vowelET v).heads
  | _ => False

instance (f : Form) (i : ℕ) : Decidable (HeadedAAt f i) := by
  unfold HeadedAAt; split <;> infer_instance

/-- The nucleus at `i` sits inside a geminate. -/
def GeminateInternal (f : Form) (i : ℕ) : Prop :=
  match f[i]?, f[i + 1]? with
  | some u, some u' => u.c = u'.c
  | _, _ => False

instance (f : Form) (i : ℕ) : Decidable (GeminateInternal f i) := by
  unfold GeminateInternal; split <;> infer_instance

/-! ### Lateral relations -/

/-- The lateral actorship of Tigrinya and Tigre. A contentful nucleus governs and licenses (23a),
(24), an epenthetic one included. The final nucleus may be empty; it does not govern (§3.3.1) and
it licenses, so that a final guttural has its licensor ((32a)). -/
def actorship : Actorship := .ltp ↑Melody.floating ⊥ true true false

/-- The melody of a nucleus is associated for a vowel and empty otherwise, even when the nucleus
is marked for epenthesis. -/
def Nuc.melody : Nuc → Melody
  | .vowel _ | .shared _ | .licensed _ => .associated
  | .empty | .mark => .empty

/-- The nuclei of a form as the lateral computation reads them, none yet expressed. -/
def nuclei (f : Form) : List Nucleus := f.map fun u ↦ { melody := u.v.melody }

/-- The nuclei that must be expressed whatever follows: the first, since an initial empty CV
unit needs its government (fn. 21); one whose onset is a guttural, which needs an expressed
licensor (25), unless the nucleus is final; and one before a geminate, whose inner nucleus stays
empty. -/
def required (f : Form) : Finset ℕ :=
  (Finset.range f.length).filter fun i ↦
    i = 0 ∨ HasAt .A f i ∧ i + 1 < f.length ∨ GeminateInternal f (i + 1)

/-- The nuclei of a form before epenthesis, those with a vowel expressed, so that only a
contentful nucleus governs (23a). -/
def lexical (f : Form) : List Nucleus :=
  f.map fun u ↦ { melody := u.v.melody, expressed := decide (u.v.melody = .associated) }

/-- The nuclei of a form after epenthesis, those with a vowel or a mark expressed. -/
def surface (f : Form) : List Nucleus :=
  f.map fun u ↦ { melody := u.v.melody, expressed := decide (u.v ≠ .empty) }

/-! ### The operations of (30) -/

/-- Fusion ((9), (26b), (27b), (28b)) fuses the element that is the whole melody of a vowel with
the same element of an adjacent consonant. After such a consonant the vowel is licensed by its
onset; otherwise it shares the element with the next onset, or, when both are /a/, with the next
nucleus (39b). Fusion always applies (§3.2.2). -/
def fusion (f : Form) : Form :=
  f.mapIdx fun i u ↦
    match u.v with
    | .vowel v =>
      match v.element? with
      | some e =>
        if Has e u.c then ⟨u.c, .licensed (headed e v)⟩
        else if HasAt e f (i + 1) ∨ HeadedAAt f i ∧ HeadedAAt f (i + 1) then
          ⟨u.c, .shared (headed e v)⟩
        else u
      | none => u
    | _ => u

/-- Dissociation ((9), (26c)) empties a nucleus that shares its element with what follows iff the
next nucleus governs. A nucleus licensed by its own onset keeps its vowel (28). -/
def dissociation (f : Form) : Form :=
  f.mapIdx fun i u ↦
    match u.v with
    | .shared _ => if IsGovernor actorship (lexical f) (i + 1) then ⟨u.c, .empty⟩ else u
    | _ => u

/-- The nucleus at `i` is expressed in the realization of the form from the left, in which the
required nuclei and those of `R` are expressed and any other empty nucleus that the next can
govern is silent (no triconsonantal clusters). -/
def Realized (R : Finset ℕ) (f : Form) (i : ℕ) : Prop :=
  ∃ x ∈ (leftward actorship (required f ∪ R) (nuclei f))[i]?, x.expressed = true

instance (R : Finset ℕ) (f : Form) (i : ℕ) : Decidable (Realized R f i) :=
  inferInstanceAs (Decidable (∃ x ∈ _, _))

/-- Epenthesis (30)–(31) marks the empty nuclei that are realized. -/
def epenthesis (R : Finset ℕ) (f : Form) : Form :=
  f.mapIdx fun i u ↦ if u.v = .empty ∧ Realized R f i then ⟨u.c, .mark⟩ else u

/-- The derivation applies the operations in the order of (30), with the nuclei of `R` realized. -/
def derive (R : Finset ℕ) (f : Form) : Form := epenthesis R (dissociation (fusion f))

/-- The vowel at `i`, if any. -/
def vowelAt (f : Form) (i : ℕ) : Option Vowel := f[i]?.bind (·.v.vowel?)

/-- The vowels a nucleus to be realized at `i` may copy by trans-guttural harmony ((7), (19c)):
the vowel across an adjacent guttural, in either direction. -/
def harmonySources (f : Form) (i : ℕ) : List Vowel :=
  (if 0 < i ∧ HasAt .A f i then (vowelAt f (i - 1)).toList else []) ++
    if HasAt .A f (i + 1) then (vowelAt f (i + 1)).toList else []

/-- A nucleus to be realized surfaces as the weak vowel or as a copy of a harmony source. -/
def realizeMark (f : Form) (i : ℕ) : List (List Phonology.Segment) :=
  (Vowel.weak :: harmonySources f i).dedup.map fun v ↦ [v.segment]

/-- The realizations of the nucleus at `i`. -/
def realizeNuc (f : Form) (i : ℕ) : List (List Phonology.Segment) :=
  match f[i]? with
  | some ⟨_, .mark⟩ => realizeMark f i
  | some ⟨_, .vowel v⟩ | some ⟨_, .shared v⟩ | some ⟨_, .licensed v⟩ => [[v.segment]]
  | _ => [[]]

/-- The surface forms of a form are its consonants and realized nuclei in order, one form per choice
of realization. -/
def realizations (f : Form) : List (List Phonology.Segment) :=
  (List.range f.length).foldl (init := [[]]) fun acc i ↦
    acc.flatMap fun s ↦ (realizeNuc f i).map (s ++ (f[i]?.map (·.c)).toList ++ ·)

/-- A harmonized surface form read as an underlying form: a nucleus realized by trans-guttural
harmony holds the vowel it copies, a fused vowel is a vowel, and any other nucleus to be realized
is empty. -/
def harmonized (f : Form) : Form :=
  f.mapIdx fun i u ↦
    match u.v with
    | .mark => ⟨u.c, ((harmonySources f i).head?.map Nuc.vowel).getD .empty⟩
    | .shared v | .licensed v => ⟨u.c, .vowel v⟩
    | _ => u

/-! ### Fusion and dissociation -/

theorem geminateInternal_congr {f g : Form} (h : ∀ i : ℕ, g[i]?.map (·.c) = f[i]?.map (·.c))
    (i : ℕ) : GeminateInternal g i ↔ GeminateInternal f i := by
  have h1 := h i
  have h2 := h (i + 1)
  unfold GeminateInternal
  cases hf1 : f[i]? <;> cases hf2 : f[i + 1]? <;> cases hg1 : g[i]? <;> cases hg2 : g[i + 1]? <;>
    simp_all

theorem hasAt_congr {f g : Form} (h : ∀ i : ℕ, g[i]?.map (·.c) = f[i]?.map (·.c)) (e : Element)
    (i : ℕ) : HasAt e g i ↔ HasAt e f i := by
  have h1 := h i
  unfold HasAt
  cases hf : f[i]? <;> cases hg : g[i]? <;> simp_all

theorem map_c_fusion (f : Form) (i : ℕ) : (fusion f)[i]?.map (·.c) = f[i]?.map (·.c) := by
  simp only [fusion, List.getElem?_mapIdx]
  rcases f[i]? with _ | ⟨c, n⟩
  · rfl
  · cases n with
    | vowel v =>
      simp only [Option.map_some]
      rcases v.element? with _ | e
      · rfl
      · simp only; split_ifs <;> rfl
    | _ => rfl

theorem hasAt_fusion (e : Element) (f : Form) (i : ℕ) : HasAt e (fusion f) i ↔ HasAt e f i :=
  hasAt_congr (map_c_fusion f) e i

theorem lexical_fusion (f : Form) : lexical (fusion f) = lexical f := by
  refine List.ext_getElem? fun i ↦ ?_
  simp only [lexical, fusion, List.getElem?_map, List.getElem?_mapIdx]
  rcases f[i]? with _ | ⟨c, n⟩
  · rfl
  · cases n with
    | vowel v =>
      simp only [Option.map_some]
      rcases v.element? with _ | e
      · rfl
      · simp only; split_ifs <;> rfl
    | _ => rfl

-- (9), (26b), (27b), (28b), §3.2.2
theorem fusion_getElem? (f : Form) (i : ℕ) (c : Phonology.Segment) (v : Vowel) (e : Element)
    (h : f[i]? = some ⟨c, .vowel v⟩) (he : v.element? = some e) :
    (fusion f)[i]? = some ⟨c,
      if Has e c then .licensed (headed e v)
      else if HasAt e f (i + 1) ∨ HeadedAAt f i ∧ HeadedAAt f (i + 1) then .shared (headed e v)
      else .vowel v⟩ := by
  simp only [fusion, List.getElem?_mapIdx, h, Option.map_some, he]
  split_ifs <;> rfl

/-- Syneresis ((9), (26), (40)): where an element `e` is the whole melody of a vowel, dissociation
after fusion empties its nucleus exactly when its onset lacks `e`, the next onset has it, or the
two nuclei hold /a/, and the next nucleus governs. -/
theorem dissociation_empty_iff (f : Form) (i : ℕ) (c : Phonology.Segment) (v : Vowel)
    (e : Element) (h : f[i]? = some ⟨c, .vowel v⟩) (he : v.element? = some e) :
    (dissociation (fusion f))[i]? = some ⟨c, .empty⟩ ↔
      ¬ Has e c ∧ (HasAt e f (i + 1) ∨ HeadedAAt f i ∧ HeadedAAt f (i + 1)) ∧
        IsGovernor actorship (lexical f) (i + 1) := by
  simp only [dissociation, List.getElem?_mapIdx, fusion_getElem? f i c v e h he, Option.map_some,
    lexical_fusion]
  split_ifs <;> simp_all

-- (27), (28), (40)
theorem vowelAt_dissociation_iff (f : Form) (i : ℕ) (c : Phonology.Segment) (v : Vowel)
    (e : Element) (h : f[i]? = some ⟨c, .vowel v⟩) (he : v.element? = some e)
    (hA : Has e c ∨ HasAt e f (i + 1) ∨ HeadedAAt f i ∧ HeadedAAt f (i + 1)) :
    vowelAt (dissociation (fusion f)) i = some (headed e v) ↔
      Has e c ∨ ¬ IsGovernor actorship (lexical f) (i + 1) := by
  simp only [vowelAt, dissociation, List.getElem?_mapIdx, fusion_getElem? f i c v e h he,
    Option.map_some, lexical_fusion, Option.bind_some]
  split_ifs <;> simp_all [Nuc.vowel?]

/-! ### Epenthesis -/

theorem getElem?_epenthesis (R : Finset ℕ) (f : Form) (i : ℕ) :
    (epenthesis R f)[i]? =
      f[i]?.map fun u ↦ if u.v = .empty ∧ Realized R f i then ⟨u.c, .mark⟩ else u :=
  List.getElem?_mapIdx ..

theorem map_c_epenthesis (R : Finset ℕ) (f : Form) (i : ℕ) :
    (epenthesis R f)[i]?.map (·.c) = f[i]?.map (·.c) := by
  rw [getElem?_epenthesis]
  cases f[i]? with
  | none => rfl
  | some u => simp only [Option.map_some]; split_ifs <;> rfl

theorem nuclei_epenthesis (R : Finset ℕ) (f : Form) : nuclei (epenthesis R f) = nuclei f := by
  refine List.ext_getElem? fun i ↦ ?_
  simp only [nuclei, List.getElem?_map, getElem?_epenthesis]
  cases hu : f[i]? with
  | none => rfl
  | some u =>
    simp only [Option.map_some]
    split_ifs with hc
    · simp [hc.1, Nuc.melody]
    · rfl

theorem required_epenthesis (R : Finset ℕ) (f : Form) :
    required (epenthesis R f) = required f := by
  simp only [required, show (epenthesis R f).length = f.length from List.length_mapIdx,
    hasAt_congr (map_c_epenthesis R f), geminateInternal_congr (map_c_epenthesis R f)]

theorem realized_epenthesis (R : Finset ℕ) (f : Form) (i : ℕ) :
    Realized R (epenthesis R f) i ↔ Realized R f i := by
  rw [Realized, nuclei_epenthesis, required_epenthesis, Realized]

-- no nucleus is left to mark once epenthesis has applied
theorem epenthesis_epenthesis (R : Finset ℕ) (f : Form) :
    epenthesis R (epenthesis R f) = epenthesis R f := by
  refine List.ext_getElem? fun i ↦ ?_
  rw [getElem?_epenthesis (f := epenthesis R f), getElem?_epenthesis]
  cases hu : f[i]? with
  | none => rfl
  | some u =>
    simp only [Option.map_some, Option.some.injEq, realized_epenthesis]
    by_cases hc : u.v = .empty ∧ Realized R f i
    · simp [hc]
    · simp [hc]

/-! ### Patterns and endings (§2.1) -/

/-- A position of a pattern is a radical, a radical geminated where it can be, since gutturals
cannot geminate (§2.1, (12)), or fixed segmental material. -/
inductive Pos where
  | rad (i : ℕ)
  | gem (i : ℕ)
  | seg (s : Phonology.Segment)

/-- A lexical vowel. -/
abbrev V (v : Vowel) : Nuc := .vowel v

/-- A pattern is a prefix of fixed segments and a stem, each a list of positions with their
nuclei; Q, T, L are the radicals. -/
structure Pattern where
  /-- The prefix. -/
  pre : List (Pos × Nuc) := []
  /-- The stem, which begins with the first radical. -/
  stem : List (Pos × Nuc)

/-- The positions of a pattern, prefix and stem. -/
def Pattern.positions (p : Pattern) : List (Pos × Nuc) := p.pre ++ p.stem

/-- The languages of the paper. -/
inductive Lang where
  | tigrinya
  | tigre
  deriving DecidableEq, Repr

/-- The 2nd-person prefix tɨ-, an empty nucleus in the underlying forms of (31)–(39), with the /t/
of the language. -/
def prefix2 : Lang → List (Pos × Nuc)
  | .tigrinya => [(.seg Tigrinya.Phonology.t, .empty)]
  | .tigre => [(.seg Tigre.Phonology.t, .empty)]

/-- The gerund prefix mɨ-, an empty nucleus in the underlying forms of (37a) and (39b). -/
def prefixGer : List (Pos × Nuc) := [(.seg Tigrinya.Phonology.m, .empty)]

/-- The pattern of each template of the paradigms in a language. -/
def pattern (l : Lang) : Examples.Template → Pattern
  | .depPrf => ⟨[], [(.rad 0, V .aBare), (.rad 1, V .aBare), (.rad 2, .empty)]⟩
  | .depPrfB => ⟨[], [(.rad 0, V .aBare), (.gem 1, V .aBare), (.rad 2, .empty)]⟩
  | .depPrfC => ⟨[], [(.rad 0, V .a), (.rad 1, V .aBare), (.rad 2, .empty)]⟩
  | .prf => ⟨[], [(.rad 0, V .aBare), (.rad 1, V .i), (.rad 2, .empty)]⟩
  | .imprf => ⟨[], [(.rad 0, V .aBare), (.gem 1, V .weak), (.rad 2, .empty)]⟩
  | .imprf2 => ⟨prefix2 l, [(.rad 0, V .aBare), (.gem 1, V .weak), (.rad 2, .empty)]⟩
  | .imprf2NoGem => ⟨prefix2 l, [(.rad 0, V .aBare), (.rad 1, V .weak), (.rad 2, .empty)]⟩
  | .passPrf => ⟨prefix2 l, [(.rad 0, V .aBare), (.rad 1, V .i), (.rad 2, .empty)]⟩
  | .imp => ⟨[], [(.rad 0, .empty), (.rad 1, V .aBare), (.rad 2, .empty)]⟩
  | .juss2 => ⟨prefix2 l, [(.rad 0, .empty), (.rad 1, V .aBare), (.rad 2, .empty)]⟩
  | .impGem => ⟨[], [(.rad 0, V .a), (.gem 1, V .weak), (.rad 2, .empty)]⟩
  | .jussGem2 => ⟨prefix2 l, [(.rad 0, V .a), (.gem 1, V .weak), (.rad 2, .empty)]⟩
  | .gerA => ⟨prefixGer, [(.rad 0, .empty), (.rad 1, V .a), (.rad 2, .empty)]⟩
  | .gerB => ⟨prefixGer, [(.rad 0, .empty), (.gem 1, V .a), (.rad 2, .empty)]⟩
  | .gerC => ⟨prefixGer, [(.rad 0, V .a), (.rad 1, V .a), (.rad 2, .empty)]⟩
  | .caus =>
    ⟨[(.seg Tigrinya.Phonology.«ʔ», V .aBare)],
      [(.rad 0, .empty), (.rad 1, V .i), (.rad 2, .empty)]⟩
  | .prf3 => ⟨[], [(.rad 0, V .a), (.rad 1, .empty), (.rad 2, .empty)]⟩

/-- Positions instantiated by a root. -/
def instantiate (t : List (Pos × Nuc)) (r : ConsonantalRoot Phonology.Segment) : Option Form :=
  (t.mapM fun (pn : Pos × Nuc) ↦
    match pn.1 with
    | .rad i => (r.segments[i]?).map fun c ↦ [CV.mk c pn.2]
    | .gem i => (r.segments[i]?).map fun c ↦
        if Has .A c then [CV.mk c pn.2] else [CV.mk c .empty, CV.mk c pn.2]
    | .seg c => some [CV.mk c pn.2]).map List.flatten

/-- An ending is a vowel filling the stem-final nucleus, then further CV units. -/
structure Ending where
  vowel : Option Vowel := none
  rest : List (Phonology.Segment × Nuc) := []

/-- The ending of each suffix of the paradigms. -/
def ending : Examples.Suffix → Ending
  | .a => ⟨some .a, []⟩
  | .i => ⟨some .i, []⟩
  | .u => ⟨some .u, []⟩
  | .aBare => ⟨some .aBare, []⟩
  | .ej => ⟨some .e, [(Tigrinya.Phonology.j, .empty)]⟩
  | .om => ⟨some .o, [(Tigrinya.Phonology.m, .empty)]⟩
  | .ku => ⟨none, [(Tigrinya.Phonology.k, V .u)]⟩
  | .e => ⟨some .e, []⟩
  | .na => ⟨none, [(Tigrinya.Phonology.n, V .a)]⟩
  | .ka => ⟨none, [(Tigrinya.Phonology.k, V .a)]⟩

/-- A stem with an ending. -/
def attach (f : Form) (s : Ending) : Form :=
  (match s.vowel with
    | some v => f.dropLast ++ (f.getLast?.map fun u ↦ [⟨u.c, .vowel v⟩]).getD []
    | none => f) ++ s.rest.map fun cn ↦ ⟨cn.1, cn.2⟩

/-! ### Roots -/

/-- The language of each root. -/
def lang : Examples.Root → Lang
  | .whip | .hear | .arrest | .pull | .teach | .slaughter | .escape | .ask | .uncover | .bark
  | .hurt | .bless | .arf | .drink => .tigrinya
  | .weigh | .leave | .wash | .flee | .getUp | .whipTigre | .askTigre | .load | .uncoverTigre
  | .pullTigre => .tigre

/-- Each root of the paradigms, in its language's fragment. -/
def root : Examples.Root → ConsonantalRoot Phonology.Segment
  | .whip => Tigrinya.Phonology.whip
  | .hear => Tigrinya.Phonology.hear
  | .arrest => Tigrinya.Phonology.arrest
  | .pull => Tigrinya.Phonology.pull
  | .teach => Tigrinya.Phonology.teach
  | .slaughter => Tigrinya.Phonology.slaughter
  | .escape => Tigrinya.Phonology.escape
  | .ask => Tigrinya.Phonology.ask
  | .uncover => Tigrinya.Phonology.uncover
  | .bark => Tigrinya.Phonology.bark
  | .hurt => Tigrinya.Phonology.hurt
  | .bless => Tigrinya.Phonology.bless
  | .arf => Tigrinya.Phonology.arf
  | .drink => Tigrinya.Phonology.drink
  | .weigh => Tigre.Phonology.weigh
  | .leave => Tigre.Phonology.leave
  | .wash => Tigre.Phonology.wash
  | .flee => Tigre.Phonology.flee
  | .getUp => Tigre.Phonology.getUp
  | .whipTigre => Tigre.Phonology.whip
  | .askTigre => Tigre.Phonology.ask
  | .load => Tigre.Phonology.load
  | .uncoverTigre => Tigre.Phonology.uncover
  | .pullTigre => Tigre.Phonology.pull

/-! ### Transcriptions -/

/-- The PHOIBLE inventory of each language. -/
def inventory : Lang → Data.PHOIBLE.Inventory
  | .tigrinya => Data.PHOIBLE.Inventories.Tigrinya.tir
  | .tigre => Data.PHOIBLE.Inventories.Tigre.tig

/-- The glyph of a language's inventory that a consonant letter of the paper's transcription
writes, where it is not the letter itself: the coronals of Tigre are dental, and the paper writes
its ejectives with a superscript. -/
def glyph : Lang → String → String
  | _, "g" => "ɡ"
  | .tigrinya, "r" => "ɾ"
  | .tigre, "t" => "t̪"
  | .tigre, "d" => "d̪"
  | .tigre, "n" => "n̪"
  | .tigre, "tˁ" | .tigre, "tˀ" => "t̪ʼ"
  | .tigre, "kˀ" => "kʼ"
  | .tigre, "sˁ" => "tsʼ"
  | _, x => x

/-- `letter? l x` reads a letter of the paper's transcription of a form of language `l` as a
segment: a vowel, or a consonant of the language's inventory. -/
def letter? (l : Lang) (x : String) : Option Phonology.Segment :=
  ((Vowel.ofLetter? x).map Vowel.segment).orElse fun _ ↦ (inventory l).segment? (glyph l x)

/-- The letters of a transcription, a superscript or a length mark going with the letter before
it. -/
def letters : List Char → List String
  | [] => []
  | [c] => [String.singleton c]
  | c :: d :: cs =>
    if d = 'ˁ' ∨ d = 'ˀ' ∨ d = 'ː' then String.ofList [c, d] :: letters cs
    else String.singleton c :: letters (d :: cs)

/-- `read l s` reads a transcription of a form of language `l` as segments, hyphens removed, β
read as b and a long [iː] as [i] before [j]. -/
def read (l : Lang) (s : String) : Option (List Phonology.Segment) :=
  ((letters ((s.toList.filter (· ≠ '-')).map fun c ↦ if c = 'β' then 'b' else c)).flatMap
    fun x ↦ if x = "iː" then ["i", "j"] else [x]).mapM (letter? l)

/-! ### The paradigms (4)–(19) and the derivations (31)–(39) -/

/-- The underlying form of an example is its pattern instantiated by its root, with its ending. -/
def stem (x : Example) : Option Form := do
  let r ← x.root
  let t ← x.template
  let f ← instantiate (pattern (lang r) t).positions (root r)
  pure ((x.suffix.map fun s ↦ attach f (ending s)).getD f)

/-- The position of the first nucleus of the stem of an example, after its prefix. -/
def stemStart (x : Example) : ℕ :=
  (x.template.map fun t ↦ (pattern .tigrinya t).pre.length).getD 0

/-- The attested forms of an example, read as segments. -/
def forms (x : Example) : List (List Phonology.Segment) :=
  (x.root.map lang).toList.flatMap fun l ↦
    (x.datum.primaryText :: x.datum.contrasts.map Prod.fst).filterMap (read l)

/-- The surface forms the analysis yields for an example when the nuclei of `R` are realized. -/
def realizationsOf (R : Finset ℕ) (x : Example) : List (List Phonology.Segment) :=
  match stem x with
  | some f => realizations (derive R f)
  | none => []

/-- Dissociation empties the nucleus at `i`. -/
def Dissociated (f : Form) (i : ℕ) : Prop :=
  (fusion f)[i]?.map (·.v) ≠ some .empty ∧ (dissociation (fusion f))[i]?.map (·.v) = some .empty

instance (f : Form) (i : ℕ) : Decidable (Dissociated f i) := inferInstanceAs (Decidable (_ ∧ _))

/-- A Tigrinya form retains its stem-initial nucleus when the derivation dissociates that
nucleus and leaves it silent (§3.3.3, (39)). -/
def Retains (x : Example) : Prop :=
  x.root.map lang = some .tigrinya ∧ ∃ f ∈ stem x, Dissociated f (stemStart x) ∧
    (derive ∅ f)[stemStart x]?.map (·.v) = some .empty

instance (x : Example) : Decidable (Retains x) := inferInstanceAs (Decidable (_ ∧ ∃ f ∈ _, _))

theorem stem_isSome : ∀ x : Example, (stem x).isSome := by decide +kernel

-- every attested form is read
theorem length_forms : ∀ x : Example, (forms x).length = x.datum.contrasts.length + 1 := by
  decide +kernel

-- the root of each example is a root of the example's language
theorem glottocode_lang : ∀ x : Example, x.root.map lang =
    if x.datum.language = Glottocode.tigrinya then some .tigrinya else some .tigre := by
  decide +kernel

/-- Every attested form of (4)–(19) and (31)–(38) is a realization of the derivation of its
underlying form, unless the form retains its stem-initial nucleus. -/
theorem mem_realizations_of_not_retains :
    ∀ x : Example, ¬ Retains x → ∀ w ∈ forms x, w ∈ realizationsOf ∅ x := by
  decide +kernel

/-- The Tigrinya forms of (17b–d) and (18c) realize the stem-initial nucleus that the derivation
empties and leaves silent, so the derivation yields none of them (39). -/
theorem notMem_realizations_of_retains :
    ∀ x : Example, Retains x → ∀ w ∈ forms x, w ∉ realizationsOf ∅ x := by
  decide +kernel

/-- Where a stem-initial nucleus that the derivation empties must be realized, as an alignment of
the stem with the syllable requires ([buckley-2000]), the derivation yields the retaining forms. -/
theorem mem_realizations_stemStart_of_retains :
    ∀ x : Example, Retains x → ∀ w ∈ forms x, w ∈ realizationsOf {stemStart x} x := by
  decide +kernel

-- (17b–d), (18c)
theorem retains_iff : ∀ x : Example, Retains x ↔
    x ∈ [.ex_17b_imprf, .ex_17b_pass, .ex_17c_imprf, .ex_17c_pass, .ex_17d_imprf, .ex_17d_pass,
      .ex_18c_ger] := by
  decide +kernel

/-! ### The order of the operations (30) -/

/-- The underlying form of the feminine imperative of 'hear', /s_mʌʕ-i/ (36a). -/
def imperative36a : Form :=
  attach ((instantiate (pattern .tigrinya .imp).positions Tigrinya.Phonology.hear).getD [])
    (ending .i)

/-- The gerund of 'hear' with the suffix *-u*, /m_s_maʕ-u/ (37a). -/
def gerund37a : Form :=
  attach ((instantiate (pattern .tigrinya .gerA).positions Tigrinya.Phonology.hear).getD [])
    (ending .u)

/-- The dependent perfective of 'hear' with the suffix *-ku*, /sʌmʌʕ_-ku/ (37d). -/
def perfective37d : Form :=
  attach ((instantiate (pattern .tigrinya .depPrf).positions Tigrinya.Phonology.hear).getD [])
    (ending .ku)

/-- The number of nuclei of a form marked to be realized. -/
def marks (f : Form) : ℕ := f.countP (·.v = .mark)

-- (36a), (30)
theorem feeds_fusion : Feeds fusion (fun f ↦ dissociation f ≠ f) imperative36a := by
  decide +kernel

-- (37a), (30)
theorem feeds_dissociation :
    Feeds dissociation (fun f ↦ marks (epenthesis ∅ f)) (fusion gerund37a) := by
  decide +kernel

theorem derive_isFixedPt : ∀ x : Example, ∀ f ∈ stem x,
    fusion (derive ∅ f) = derive ∅ f ∧ dissociation (derive ∅ f) = derive ∅ f ∧
      epenthesis ∅ (derive ∅ f) = derive ∅ f := by
  decide +kernel

-- (9), (11): the vowel before the glide of /sʌtij-u/ is emptied as the vowel before the guttural
-- of /s_mʌʕ-i/ is, and before the consonant-initial suffix of /sʌtij-na/ it stays
theorem dissociated_drink :
    (∀ f ∈ stem .ex_8b_3msg, Dissociated f 1) ∧ Dissociated imperative36a 1 ∧
      ∀ f ∈ stem .ex_8b_1pl, (dissociation (fusion f))[1]?.map (·.v) = some (.shared .i) := by
  decide +kernel

/-! ### Trans-guttural harmony and the derivation (pp. 24–25) -/

/-- In (37d), trans-guttural harmony feeds dissociation, which does not apply to the derived
form [sʌmaʕ▪ku] and applies once the nucleus after the guttural holds a copy of [a]; the
derivation orders harmony last, so the form surfaces unsyncopated. -/
theorem feeds_harmonized :
    Feeds harmonized (fun f ↦ dissociation (fusion f) ≠ fusion f) (derive ∅ perfective37d) := by
  decide +kernel

-- (37d): a derivation that read the harmonized form again would yield *[sʌmʕaku]
theorem realizations_harmonized_37d :
    (realizations (derive ∅ (harmonized (derive ∅ perfective37d)))).map some =
        [read .tigrinya "sʌmʕaku"] ∧
      ∀ w ∈ read .tigrinya "sʌmʕaku", w ∉ realizations (derive ∅ perfective37d) := by
  decide +kernel

-- (37b,c): /s_ħʌb/ and /sʌħʌb/ are neutralized, and harmony returns the derived form to a form
-- from which it is derived again
theorem derive_harmonized_pull :
    ∀ f ∈ [instantiate (pattern .tigrinya .imp).positions Tigrinya.Phonology.pull,
        instantiate (pattern .tigrinya .depPrf).positions Tigrinya.Phonology.pull],
      ∀ g ∈ f, derive ∅ g = [⟨Tigrinya.Phonology.s, .mark⟩, ⟨Tigrinya.Phonology.ħ, .licensed .a⟩,
          ⟨Tigrinya.Phonology.b, .empty⟩] ∧
        harmonized (derive ∅ g) ≠ derive ∅ g ∧ derive ∅ (harmonized (derive ∅ g)) = derive ∅ g := by
  decide +kernel

/-! ### Proper government and the obligatory realization -/

/-- The 2nd-person jussive of 'hear', /t_-s_mʌʕ_/ (32a). -/
def jussive32a : Form :=
  (instantiate (pattern .tigrinya .juss2).positions Tigrinya.Phonology.hear).getD []

-- §3.3.1: [tɨsmaʕ] shows that the final nucleus does not govern
theorem isGovernor_32a (s : WithBot Melody) :
    IsGovernor (.ltp ↑Melody.floating s true true false) (lexical (fusion jussive32a)) 3 ↔
      s ≠ ⊥ := by
  induction s using WithBot.recBotCoe with
  | bot => decide
  | coe m => cases m <;> decide

-- (25), (32a)
theorem guttural_licensed : ∀ x : Example, ∀ f ∈ stem x, ∀ i < f.length, HasAt .A f i →
    IsLicensor actorship (surface (derive ∅ f)) i := by
  decide +kernel

-- the derived forms satisfy the Empty Category Principle
theorem emptyCategoryPrinciple_surface : ∀ x : Example, ∀ f ∈ stem x,
    surface (derive ∅ f) = leftward actorship (required (dissociation (fusion f)))
        (nuclei (dissociation (fusion f))) ∧
      EmptyCategoryPrinciple actorship (surface (derive ∅ f)) := by
  decide +kernel

/-- The realizations of a sequence of nuclei that satisfy the Empty Category Principle, express
the required nuclei, and express as few nuclei as possible. -/
def economical (l : List Nucleus) (R : Finset ℕ) : List (List Nucleus) :=
  let admissible := (l.map fun x ↦ [{ x with expressed := false },
    { x with expressed := true }]).sections.filter fun r ↦
      decide (EmptyCategoryPrinciple actorship r ∧
        ∀ i ∈ R, ∃ x ∈ r[i]?, x.expressed = true)
  admissible.filter fun r ↦ admissible.all fun r' ↦ r.countP (·.expressed) ≤ r'.countP (·.expressed)

-- (37a), §3.3.3
theorem syneresis_37a :
    (nuclei (dissociation (fusion gerund37a))).map (·.melody) =
        [.empty, .empty, .empty, .associated] ∧
      (economical (nuclei (dissociation (fusion gerund37a)))
          (required (dissociation (fusion gerund37a)))).map (·.map (·.expressed)) =
        [[true, true, false, true], [true, false, true, true]] ∧
      (obligatory actorship (required (dissociation (fusion gerund37a)))
          (nuclei (dissociation (fusion gerund37a)))).map (·.expressed) =
        [true, true, false, true] ∧
      (surface (derive ∅ gerund37a)).map (·.expressed) = [true, false, true, true] := by
  decide +kernel

/-- In the configuration of (37a), the dissociated position is the third in a left-aligned
sequence of three empty nuclei. -/
def DissociatedThird (f : Form) : Prop :=
  Dissociated f 2 ∧ ∀ i < 3, (dissociation (fusion f))[i]?.map (·.v) = some .empty

instance (f : Form) : Decidable (DissociatedThird f) := inferInstanceAs (Decidable (_ ∧ _))

-- §3.3.3
theorem pronounced_eq_obligatory_iff : ∀ x : Example, ∀ f ∈ stem x,
    (surface (derive ∅ f)).map (·.expressed) =
        (obligatory actorship (required (dissociation (fusion f)))
          (nuclei (dissociation (fusion f)))).map (·.expressed) ↔
      ¬ DissociatedThird f := by
  decide +kernel

end FaustLampitelli2026
