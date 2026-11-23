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
[sɨmʕ-i] from /s_mʌʕ-i/, the way /i/ is before /j/. In Element Theory the gutturals and the low
vowels share the element |A|, and the analysis runs in Strict CV with the lateral relations of
Government Phonology.

We define a form as a sequence of CV units and three operations on forms. `fusion` joins the |A|
of a low vowel with an adjacent |A| and lowers the vowel: the vowel then shares its |A| with what
follows, or, after a guttural, is licensed by its own onset. `dissociation` empties a nucleus
that shares its |A| with what follows when the next nucleus governs. `epenthesis` marks the
empty nuclei that must be realized, and `realizations` realizes each as the weak vowel or as a
copy of the vowel across a guttural. `derive` applies the three in this order.

A nucleus is emptied exactly when it holds a low vowel, its onset has no |A|, what follows has,
and the next nucleus governs (`dissociation_empty_iff`); in every other configuration of a low
vowel and a guttural the vowel is lowered and stays. The attested forms are realizations of the
derived forms (`mem_realizations_of_not_retains`), except the Tigrinya forms that keep a
stem-initial nucleus the derivation empties (`notMem_realizations_of_retains`), which requiring
that nucleus to be realized derives (`mem_realizations_stemStart_of_retains`). Each operation
applies to the output of the one before it and not to the input (`feeds_fusion`,
`feeds_dissociation`), and no operation applies to a derived form of the rows
(`derive_isFixedPt`). Trans-guttural harmony restores the environment of fusion and dissociation
(`feeds_harmonized`): a derivation that read the harmonized form again would not end on
/s_ħʌb/ (`derive_harmonized_pull`) and would syncopate [sʌmaʕaku] (`realizations_harmonized_37d`).

## Implementation notes

* The analysis runs over the paper's transcription, a consonant other than a guttural being its
  letter, which is read only to compare two consonants and to spell a form.
  `map_segment_radicals` shows that the roots, read as segments, are the roots of the Tigrinya and
  Tigre fragments, and `image_segment_eq_vowels` that the vowels are the Tigrinya fragment's.
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
  `lowered` joins headed |A| to the vowel.
* `fusion` also joins two /a/s in successive nuclei, as in the derivation of [mɨ-bɨrak] from
  /m_-barak/.
* `Silent` is decided from the left: an empty nucleus is realized when it is initial, when its
  onset is a guttural, when the nucleus before it is silent, when a geminate follows, or when
  its position is in the set `epenthesis` is given. `pronounced_eq_obligatory_iff` compares the
  result with the obligatory realization under the Empty Category Principle, which is decided
  from the right: they differ where the dissociated nucleus is the third of three empty nuclei,
  where `epenthesis` gives C▪C_C▪C.
* Trans-guttural harmony is optional, so `realizations` lists every option. `harmonized` reads
  one harmonized surface form back as an underlying form.
* The postvocalic spirantization of b ([nɨβaħ]) is outside the analysis; β is read as b.

## TODO

* The syneresis of |I| before a glide and the ejectives, which lower a vowel and never
  syncopate it, are not derived.
* `derive_isFixedPt` is stated of the rows; no operation applies to any derived form.

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

/-- `v.toIPA` is the IPA symbol of the vowel `v`. -/
def Vowel.toIPA : Vowel → String
  | .a => "a"
  | .aBare => "ʌ"
  | .i => "i"
  | .u => "u"
  | .e => "e"
  | .o => "o"
  | .weak => "ɨ"

/-- `v.segment` is the vowel `v` in the Tigrinya fragment. -/
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

/-- `g.toIPA` is the IPA symbol of the guttural `g`. -/
def Guttural.toIPA : Guttural → String
  | .glottalStop => "ʔ"
  | .h => "h"
  | .pharyngealVoiced => "ʕ"
  | .pharyngealVoiceless => "ħ"

/-- `Guttural.ofIPA? s` is the guttural the IPA symbol `s` writes, if any. -/
def Guttural.ofIPA? : String → Option Guttural
  | "ʔ" => some .glottalStop
  | "h" => some .h
  | "ʕ" => some .pharyngealVoiced
  | "ħ" => some .pharyngealVoiceless
  | _ => none

theorem Guttural.ofIPA?_toIPA (g : Guttural) : ofIPA? g.toIPA = some g := by cases g <;> rfl

/-- `g.segment` is the guttural `g` in the Tigrinya fragment. -/
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

/-- `IsLowA v` says that the vowel's melody is |A| alone, as for the low vowels of (21). The mid
vowels carry |A| in a complex expression, which blocks fusion (§3.2.2). -/
def IsLowA (v : Vowel) : Prop := (vowelET v).elements = {.A}

instance : DecidablePred IsLowA := fun _ ↦ inferInstanceAs (Decidable (_ = _))

theorem isLowA_iff_isLow : ∀ v : Vowel, IsLowA v ↔ v.IsLow := by decide

/-- The vowel with a given melody, if any. -/
def Vowel.ofMR? (m : MR) : Option Vowel :=
  [Vowel.a, .aBare, .i, .u, .e, .o, .weak].find? (vowelET · = m)

/-- A fused vowel is realized with |A| as its head, so that [ʌ] lowers to [a] ((21), (27)). -/
def lowered (v : Vowel) : Vowel := (Vowel.ofMR? (vowelET v ⊔ .headedSimplex .A)).getD v

theorem lowered_aBare : lowered .aBare = .a := by decide

theorem lowered_lowered : ∀ v : Vowel, lowered (lowered v) = lowered v := by decide

/-! ### Strict CV forms -/

/-- A consonantal position is a guttural, or any other consonant by its transcription. -/
inductive Cons where
  | guttural (g : Guttural)
  | plain (s : String)
  deriving DecidableEq, Repr

/-- The consonant written by a root segment. -/
def Cons.ofIPA (s : String) : Cons :=
  match Guttural.ofIPA? s with
  | some g => .guttural g
  | none => .plain s

/-- `c.HasA` says that the consonant's melody contains |A|, which every guttural's does (20). Other
consonants carry no representation here, since ejectives also lower but never trigger syneresis (fn.
8). -/
def Cons.HasA : Cons → Prop
  | .guttural g => .A ∈ (gutturalET g).elements
  | .plain _ => False

instance : DecidablePred Cons.HasA := fun c ↦ by cases c <;> unfold Cons.HasA <;> infer_instance

theorem hasA_guttural (g : Guttural) : (Cons.guttural g).HasA := mem_elements_gutturalET g

/-- The transcription of a consonant. -/
def Cons.chars : Cons → List Char
  | .guttural g => g.toIPA.toList
  | .plain s => s.toList

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
  c : Cons
  v : Nuc
  deriving DecidableEq, Repr

/-- A form is a strict iteration of CV units. -/
abbrev Form := List CV

/-- The consonant at `i` contains |A|. -/
def HasAAt (f : Form) (i : ℕ) : Prop :=
  match f[i]? with
  | some u => u.c.HasA
  | none => False

instance (f : Form) (i : ℕ) : Decidable (HasAAt f i) := by
  unfold HasAAt; split <;> infer_instance

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
unit needs its government (fn. 21), and one whose onset is a guttural, which needs an expressed
licensor (25), unless the nucleus is final. -/
def required (f : Form) : Finset ℕ :=
  (Finset.range f.length).filter fun i ↦ i = 0 ∨ HasAAt f i ∧ i + 1 < f.length

/-- The nuclei of a form before epenthesis, those with a vowel expressed, so that only a
contentful nucleus governs (23a). -/
def lexical (f : Form) : List Nucleus :=
  f.map fun u ↦ { melody := u.v.melody, expressed := decide (u.v.melody = .associated) }

/-- The nuclei of a form after epenthesis, those with a vowel or a mark expressed. -/
def surface (f : Form) : List Nucleus :=
  f.map fun u ↦ { melody := u.v.melody, expressed := decide (u.v ≠ .empty) }

/-! ### The operations of (30) -/

/-- Fusion ((26b), (27b), (28b)) fuses a low vowel with an adjacent |A| and lowers it. After a
guttural the vowel is licensed by its onset; otherwise it shares its |A| with the next onset, or,
when both are /a/, with the next nucleus (39b). Fusion always applies (§3.2.2). -/
def fusion (f : Form) : Form :=
  f.mapIdx fun i u ↦
    match u.v with
    | .vowel v =>
      if IsLowA v ∧ u.c.HasA then ⟨u.c, .licensed (lowered v)⟩
      else if IsLowA v ∧ (HasAAt f (i + 1) ∨ HeadedAAt f i ∧ HeadedAAt f (i + 1)) then
        ⟨u.c, .shared (lowered v)⟩
      else u
    | _ => u

/-- Dissociation (26c) empties a nucleus that shares its |A| with what follows iff the next
nucleus governs. A nucleus licensed by its own onset keeps its vowel (28). -/
def dissociation (f : Form) : Form :=
  f.mapIdx fun i u ↦
    match u.v with
    | .shared _ => if IsGovernor actorship (lexical f) (i + 1) then ⟨u.c, .empty⟩ else u
    | _ => u

/-- The empty nucleus at `i` stays silent: it is word-final or inside a geminate, or it is
governed, being neither initial (no initial clusters), nor the licensor of a word-internal
guttural (25), nor preceded by a silent nucleus (no triconsonantal clusters), nor followed by a
geminate, nor in `R`. -/
def Silent (R : Finset ℕ) (f : Form) : ℕ → Prop
  | 0 => f[0]?.map (·.v) = some .empty ∧ (1 = f.length ∨ GeminateInternal f 0)
  | i + 1 => f[i + 1]?.map (·.v) = some .empty ∧ (i + 2 = f.length ∨ GeminateInternal f (i + 1) ∨
      ¬ (HasAAt f (i + 1) ∨ Silent R f i ∨ GeminateInternal f (i + 2) ∨ i + 1 ∈ R))

instance instDecidableSilent (R : Finset ℕ) (f : Form) : ∀ i, Decidable (Silent R f i)
  | 0 => inferInstanceAs (Decidable (_ ∧ _))
  | i + 1 =>
    have := instDecidableSilent R f i
    inferInstanceAs (Decidable (_ ∧ (_ ∨ _ ∨ ¬ (_ ∨ _ ∨ _ ∨ _))))

/-- Epenthesis (30)–(31) marks the empty nuclei that must be realized, those that do not stay
silent. -/
def epenthesis (R : Finset ℕ) (f : Form) : Form :=
  f.mapIdx fun i u ↦ if u.v = .empty ∧ ¬ Silent R f i then ⟨u.c, .mark⟩ else u

/-- The derivation applies the operations in the order of (30), with the nuclei of `R` realized. -/
def derive (R : Finset ℕ) (f : Form) : Form := epenthesis R (dissociation (fusion f))

/-- The vowel at `i`, if any. -/
def vowelAt (f : Form) (i : ℕ) : Option Vowel := f[i]?.bind (·.v.vowel?)

/-- The vowels a nucleus to be realized at `i` may copy by trans-guttural harmony ((7), (19c)):
the vowel across an adjacent guttural, in either direction. -/
def harmonySources (f : Form) (i : ℕ) : List Vowel :=
  (if 0 < i ∧ HasAAt f i then (vowelAt f (i - 1)).toList else []) ++
    if HasAAt f (i + 1) then (vowelAt f (i + 1)).toList else []

/-- A nucleus to be realized surfaces as the weak vowel or as a copy of a harmony source. -/
def realizeMark (f : Form) (i : ℕ) : List (List Char) :=
  (['ɨ'] :: (harmonySources f i).map (·.toIPA.toList)).dedup

/-- The realizations of the nucleus at `i`. -/
def realizeNuc (f : Form) (i : ℕ) : List (List Char) :=
  match f[i]? with
  | some ⟨_, .mark⟩ => realizeMark f i
  | some ⟨_, .vowel v⟩ | some ⟨_, .shared v⟩ | some ⟨_, .licensed v⟩ => [v.toIPA.toList]
  | _ => [[]]

/-- The transcription of the consonant at `i`. -/
def consAt (f : Form) (i : ℕ) : List Char :=
  match f[i]? with
  | some u => u.c.chars
  | none => []

/-- The surface forms of a form are its consonants and realized nuclei in order, one form per choice
of realization. -/
def realizations (f : Form) : List (List Char) :=
  (List.range f.length).foldl (init := [[]]) fun acc i ↦
    acc.flatMap fun s ↦ (realizeNuc f i).map (s ++ consAt f i ++ ·)

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

theorem hasAAt_fusion (f : Form) (i : ℕ) : HasAAt (fusion f) i ↔ HasAAt f i := by
  simp only [HasAAt, fusion, List.getElem?_mapIdx]
  rcases f[i]? with _ | ⟨c, n⟩
  · simp
  · cases n <;> simp only [Option.map_some]; split_ifs <;> rfl

theorem lexical_fusion (f : Form) : lexical (fusion f) = lexical f := by
  refine List.ext_getElem? fun i ↦ ?_
  simp only [lexical, fusion, List.getElem?_map, List.getElem?_mapIdx]
  rcases f[i]? with _ | ⟨c, n⟩
  · rfl
  · cases n <;> simp only [Option.map_some]; split_ifs <;> rfl

-- (26b), (27b), (28b), §3.2.2
theorem fusion_getElem? (f : Form) (i : ℕ) (c : Cons) (v : Vowel) (h : f[i]? = some ⟨c, .vowel v⟩) :
    (fusion f)[i]? = some ⟨c,
      if IsLowA v ∧ c.HasA then .licensed (lowered v)
      else if IsLowA v ∧ (HasAAt f (i + 1) ∨ HeadedAAt f i ∧ HeadedAAt f (i + 1)) then
        .shared (lowered v)
      else .vowel v⟩ := by
  simp only [fusion, List.getElem?_mapIdx, h, Option.map_some]
  split_ifs <;> rfl

/-- Syneresis ((26), (40)): dissociation after fusion empties a nucleus exactly when it holds a
low vowel, its onset has no |A|, the next onset has, or the two nuclei hold /a/, and the next
nucleus governs. -/
theorem dissociation_empty_iff (f : Form) (i : ℕ) (c : Cons) (v : Vowel)
    (h : f[i]? = some ⟨c, .vowel v⟩) :
    (dissociation (fusion f))[i]? = some ⟨c, .empty⟩ ↔
      IsLowA v ∧ ¬ c.HasA ∧ (HasAAt f (i + 1) ∨ HeadedAAt f i ∧ HeadedAAt f (i + 1)) ∧
        IsGovernor actorship (lexical f) (i + 1) := by
  simp only [dissociation, List.getElem?_mapIdx, fusion_getElem? f i c v h, Option.map_some,
    lexical_fusion]
  split_ifs <;> simp_all

-- (27), (28), (40)
theorem vowelAt_dissociation_iff (f : Form) (i : ℕ) (c : Cons) (v : Vowel)
    (h : f[i]? = some ⟨c, .vowel v⟩) (hv : IsLowA v)
    (hA : c.HasA ∨ HasAAt f (i + 1) ∨ HeadedAAt f i ∧ HeadedAAt f (i + 1)) :
    vowelAt (dissociation (fusion f)) i = some (lowered v) ↔
      c.HasA ∨ ¬ IsGovernor actorship (lexical f) (i + 1) := by
  simp only [vowelAt, dissociation, List.getElem?_mapIdx, fusion_getElem? f i c v h,
    Option.map_some, lexical_fusion, Option.bind_some]
  split_ifs <;> simp_all [Nuc.vowel?]

/-! ### Patterns and endings (§2.1) -/

/-- A position of a pattern is a radical, a radical geminated where it can be, since gutturals
cannot geminate (§2.1, (12)), or fixed segmental material. -/
inductive Pos where
  | rad (i : ℕ)
  | gem (i : ℕ)
  | seg (s : String)

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

/-- The 2nd-person prefix tɨ-, an empty nucleus in the underlying forms of (31)–(39). -/
def prefix2 : List (Pos × Nuc) := [(.seg "t", .empty)]

/-- The gerund prefix mɨ-, an empty nucleus in the underlying forms of (37a) and (39b). -/
def prefixGer : List (Pos × Nuc) := [(.seg "m", .empty)]

/-- The pattern of each template of the paradigms. -/
def pattern : Examples.Template → Pattern
  | .depPrf => ⟨[], [(.rad 0, V .aBare), (.rad 1, V .aBare), (.rad 2, .empty)]⟩
  | .depPrfB => ⟨[], [(.rad 0, V .aBare), (.gem 1, V .aBare), (.rad 2, .empty)]⟩
  | .depPrfC => ⟨[], [(.rad 0, V .a), (.rad 1, V .aBare), (.rad 2, .empty)]⟩
  | .prf => ⟨[], [(.rad 0, V .aBare), (.rad 1, V .i), (.rad 2, .empty)]⟩
  | .imprf => ⟨[], [(.rad 0, V .aBare), (.gem 1, V .weak), (.rad 2, .empty)]⟩
  | .imprf2 => ⟨prefix2, [(.rad 0, V .aBare), (.gem 1, V .weak), (.rad 2, .empty)]⟩
  | .imprf2NoGem => ⟨prefix2, [(.rad 0, V .aBare), (.rad 1, V .weak), (.rad 2, .empty)]⟩
  | .passPrf => ⟨prefix2, [(.rad 0, V .aBare), (.rad 1, V .i), (.rad 2, .empty)]⟩
  | .imp => ⟨[], [(.rad 0, .empty), (.rad 1, V .aBare), (.rad 2, .empty)]⟩
  | .juss2 => ⟨prefix2, [(.rad 0, .empty), (.rad 1, V .aBare), (.rad 2, .empty)]⟩
  | .impGem => ⟨[], [(.rad 0, V .a), (.gem 1, V .weak), (.rad 2, .empty)]⟩
  | .jussGem2 => ⟨prefix2, [(.rad 0, V .a), (.gem 1, V .weak), (.rad 2, .empty)]⟩
  | .gerA => ⟨prefixGer, [(.rad 0, .empty), (.rad 1, V .a), (.rad 2, .empty)]⟩
  | .gerB => ⟨prefixGer, [(.rad 0, .empty), (.gem 1, V .a), (.rad 2, .empty)]⟩
  | .gerC => ⟨prefixGer, [(.rad 0, V .a), (.rad 1, V .a), (.rad 2, .empty)]⟩
  | .caus => ⟨[(.seg "ʔ", V .aBare)], [(.rad 0, .empty), (.rad 1, V .i), (.rad 2, .empty)]⟩
  | .prf3 => ⟨[], [(.rad 0, V .a), (.rad 1, .empty), (.rad 2, .empty)]⟩

/-- Positions instantiated by a root. -/
def instantiate (t : List (Pos × Nuc)) (r : ConsonantalRoot String) : Option Form :=
  (t.mapM fun (pn : Pos × Nuc) ↦
    match pn.1 with
    | .rad i => (r.segments[i]?).map fun s ↦ [CV.mk (Cons.ofIPA s) pn.2]
    | .gem i => (r.segments[i]?).map fun s ↦
        let c := Cons.ofIPA s
        if c.HasA then [CV.mk c pn.2] else [CV.mk c .empty, CV.mk c pn.2]
    | .seg s => some [CV.mk (Cons.ofIPA s) pn.2]).map List.flatten

/-- An ending is a vowel filling the stem-final nucleus, then further CV units. -/
structure Ending where
  vowel : Option Vowel := none
  rest : List (String × Nuc) := []

/-- The ending of each suffix of the paradigms. -/
def ending : Examples.Suffix → Ending
  | .a => ⟨some .a, []⟩
  | .i => ⟨some .i, []⟩
  | .u => ⟨some .u, []⟩
  | .aBare => ⟨some .aBare, []⟩
  | .ej => ⟨some .e, [("j", .empty)]⟩
  | .om => ⟨some .o, [("m", .empty)]⟩
  | .ku => ⟨none, [("k", V .u)]⟩
  | .ka => ⟨none, [("k", V .a)]⟩

/-- A stem with an ending. -/
def attach (f : Form) (s : Ending) : Form :=
  (match s.vowel with
    | some v => f.dropLast ++ (f.getLast?.map fun u ↦ [⟨u.c, .vowel v⟩]).getD []
    | none => f) ++ s.rest.map fun cn ↦ ⟨Cons.ofIPA cn.1, cn.2⟩

/-! ### Roots -/

/-- The languages of the paper. -/
inductive Lang where
  | tigrinya
  | tigre
  deriving DecidableEq, Repr

/-- The language of each root. -/
def lang : Examples.Root → Lang
  | .whip | .hear | .arrest | .pull | .teach | .slaughter | .escape | .ask | .uncover | .bark
  | .hurt | .bless | .arf => .tigrinya
  | .weigh | .leave | .wash | .flee | .getUp | .whipTigre | .askTigre | .load | .uncoverTigre
  | .pullTigre => .tigre

/-- The radicals of each root, in the paper's transcription. -/
def radicals : Examples.Root → ConsonantalRoot String
  | .whip => ⟨["g", "r", "f"]⟩
  | .hear => ⟨["s", "m", "ʕ"]⟩
  | .arrest => ⟨["ʔ", "s", "r"]⟩
  | .pull => ⟨["s", "ħ", "b"]⟩
  | .teach => ⟨["m", "h", "r"]⟩
  | .slaughter => ⟨["ħ", "r", "d"]⟩
  | .escape => ⟨["ħ", "d", "m"]⟩
  | .ask => ⟨["s", "ʔ", "l"]⟩
  | .uncover => ⟨["g", "l", "h"]⟩
  | .bark => ⟨["n", "b", "ħ"]⟩
  | .hurt => ⟨["b", "d", "l"]⟩
  | .bless => ⟨["b", "r", "k"]⟩
  | .arf => ⟨["ʕ", "r", "f"]⟩
  | .weigh => ⟨["m", "z", "n"]⟩
  | .leave => ⟨["f", "g", "r"]⟩
  | .wash => ⟨["ħ", "tˁ", "b"]⟩
  | .flee => ⟨["h", "r", "b"]⟩
  | .getUp => ⟨["kˀ", "n", "sˁ"]⟩
  | .whipTigre => ⟨["f", "g", "r"]⟩
  | .askTigre => ⟨["s", "ʔ", "l"]⟩
  | .load => ⟨["tˀ", "ʕ", "n"]⟩
  | .uncoverTigre => ⟨["s", "ħ", "k"]⟩
  | .pullTigre => ⟨["s", "ħ", "b"]⟩

/-- The root of each language's fragment that a root of the paradigms is. -/
def fragmentRoot : Examples.Root → ConsonantalRoot Phonology.Segment
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

/-- `segment l x` reads a letter of the paper's transcription of a root of language `l` as a
segment of that language's fragment. -/
def segment : Lang → String → Phonology.Segment
  | .tigrinya, "g" => Tigrinya.Phonology.«ɡ»
  | .tigrinya, "r" => Tigrinya.Phonology.«ɾ»
  | .tigrinya, "f" => Tigrinya.Phonology.f
  | .tigrinya, "s" => Tigrinya.Phonology.s
  | .tigrinya, "m" => Tigrinya.Phonology.m
  | .tigrinya, "ʕ" => Tigrinya.Phonology.«ʕ»
  | .tigrinya, "ʔ" => Tigrinya.Phonology.«ʔ»
  | .tigrinya, "ħ" => Tigrinya.Phonology.ħ
  | .tigrinya, "b" => Tigrinya.Phonology.b
  | .tigrinya, "h" => Tigrinya.Phonology.h
  | .tigrinya, "d" => Tigrinya.Phonology.d
  | .tigrinya, "l" => Tigrinya.Phonology.l
  | .tigrinya, "n" => Tigrinya.Phonology.n
  | .tigrinya, "k" => Tigrinya.Phonology.k
  | .tigre, "m" => Tigre.Phonology.m
  | .tigre, "z" => Tigre.Phonology.z
  | .tigre, "n" => Tigre.Phonology.n
  | .tigre, "f" => Tigre.Phonology.f
  | .tigre, "g" => Tigre.Phonology.«ɡ»
  | .tigre, "r" => Tigre.Phonology.r
  | .tigre, "ħ" => Tigre.Phonology.ħ
  | .tigre, "tˁ" => Tigre.Phonology.«tʼ»
  | .tigre, "b" => Tigre.Phonology.b
  | .tigre, "h" => Tigre.Phonology.h
  | .tigre, "kˀ" => Tigre.Phonology.«kʼ»
  | .tigre, "sˁ" => Tigre.Phonology.«tsʼ»
  | .tigre, "s" => Tigre.Phonology.s
  | .tigre, "ʔ" => Tigre.Phonology.«ʔ»
  | .tigre, "l" => Tigre.Phonology.l
  | .tigre, "tˀ" => Tigre.Phonology.«tʼ»
  | .tigre, "ʕ" => Tigre.Phonology.«ʕ»
  | .tigre, "k" => Tigre.Phonology.k
  | _, _ => ⊥

theorem map_segment_radicals (r : Examples.Root) :
    (radicals r).map (segment (lang r)) = fragmentRoot r := by
  cases r <;> rfl

/-! ### The paradigms (4)–(19) and the derivations (31)–(39) -/

/-- The underlying form of an example is its pattern instantiated by its root, with its ending. -/
def stem (x : Example) : Option Form := do
  let r ← x.root
  let t ← x.template
  let f ← instantiate (pattern t).positions (radicals r)
  pure ((x.suffix.map fun s ↦ attach f (ending s)).getD f)

/-- The position of the first nucleus of the stem of an example, after its prefix. -/
def stemStart (x : Example) : ℕ := (x.template.map fun t ↦ (pattern t).pre.length).getD 0

/-- `transcribe s` is a transcription as compared with the realizations, hyphens removed and β read
as b. -/
def transcribe (s : String) : List Char :=
  (s.toList.filter (· ≠ '-')).map fun c ↦ if c = 'β' then 'b' else c

/-- The attested forms of an example. -/
def forms (x : Example) : List (List Char) :=
  (x.datum.primaryText :: x.datum.contrasts.map Prod.fst).map transcribe

/-- The surface forms the analysis yields for an example when the nuclei of `R` are realized. -/
def realizationsOf (R : Finset ℕ) (x : Example) : List (List Char) :=
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
  attach ((instantiate (pattern .imp).positions (radicals .hear)).getD []) (ending .i)

/-- The gerund of 'hear' with the suffix *-u*, /m_s_maʕ-u/ (37a). -/
def gerund37a : Form :=
  attach ((instantiate (pattern .gerA).positions (radicals .hear)).getD []) (ending .u)

/-- The dependent perfective of 'hear' with the suffix *-ku*, /sʌmʌʕ_-ku/ (37d). -/
def perfective37d : Form :=
  attach ((instantiate (pattern .depPrf).positions (radicals .hear)).getD []) (ending .ku)

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

/-! ### Trans-guttural harmony and the derivation (pp. 24–25) -/

/-- In (37d), trans-guttural harmony feeds dissociation, which does not apply to the derived
form [sʌmaʕ▪ku] and applies once the nucleus after the guttural holds a copy of [a]; the
derivation orders harmony last, so the form surfaces unsyncopated. -/
theorem feeds_harmonized :
    Feeds harmonized (fun f ↦ dissociation (fusion f) ≠ fusion f) (derive ∅ perfective37d) := by
  decide +kernel

-- (37d): a derivation that read the harmonized form again would yield *[sʌmʕaku]
theorem realizations_harmonized_37d :
    realizations (derive ∅ (harmonized (derive ∅ perfective37d))) = ["sʌmʕaku".toList] ∧
      "sʌmʕaku".toList ∉ realizations (derive ∅ perfective37d) := by
  decide +kernel

-- (37b,c): /s_ħʌb/ and /sʌħʌb/ are neutralized, and harmony returns the derived form to a form
-- from which it is derived again
theorem derive_harmonized_pull :
    ∀ f ∈ [instantiate (pattern .imp).positions (radicals .pull),
        instantiate (pattern .depPrf).positions (radicals .pull)],
      ∀ g ∈ f, derive ∅ g = [⟨.plain "s", .mark⟩, ⟨.guttural .pharyngealVoiceless, .licensed .a⟩,
          ⟨.plain "b", .empty⟩] ∧
        harmonized (derive ∅ g) ≠ derive ∅ g ∧ derive ∅ (harmonized (derive ∅ g)) = derive ∅ g := by
  decide +kernel

/-! ### Proper government and the obligatory realization -/

/-- The 2nd-person jussive of 'hear', /t_-s_mʌʕ_/ (32a). -/
def jussive32a : Form := (instantiate (pattern .juss2).positions (radicals .hear)).getD []

-- §3.3.1: [tɨsmaʕ] shows that the final nucleus does not govern
theorem isGovernor_32a (s : WithBot Melody) :
    IsGovernor (.ltp ↑Melody.floating s true true false) (lexical (fusion jussive32a)) 3 ↔
      s ≠ ⊥ := by
  induction s using WithBot.recBotCoe with
  | bot => decide
  | coe m => cases m <;> decide

-- (25), (32a)
theorem guttural_licensed : ∀ x : Example, ∀ f ∈ stem x, ∀ i < f.length, HasAAt f i →
    IsLicensor actorship (surface (derive ∅ f)) i := by
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
