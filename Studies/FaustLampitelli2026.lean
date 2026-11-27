module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Phonology.GovernmentPhonology.ElementTheory.Autosegmental
public import Linglib.Phonology.GovernmentPhonology.EmptyCategoryPrinciple
public import Linglib.Phonology.GovernmentPhonology.Skeleton
public import Linglib.Phonology.RuleInteraction
public import Linglib.Phonology.Segmental.NaturalClass
public import Linglib.Languages.Tigrinya.Phonology
public import Linglib.Languages.Tigre.Phonology
public import Linglib.Data.Examples.FaustLampitelli2026
public import Linglib.Data.Examples.Languages
public import Studies.KayeLowenstammVergnaud1985

/-!
# Faust and Lampitelli (2026): Guttural syneresis in Tigrinya and Tigre

Syneresis is the merger of a glide with a preceding homorganic vowel in an open syllable. In
Tigrinya /sʌtij-u/ is pronounced [sʌtj-u]: the /i/ before /j/ is lost. In Tigrinya and Tigre a
low vowel before a guttural is lost in the same way: /s_mʌʕ-i/ is pronounced [sɨmʕ-i]. In
Element Theory [i] and [j] consist of the element |I|, and the low vowels and the gutturals
contain the element |A|. In both cases a vowel is lost before a consonant that has its element.

We define a form as a list of CV units, each a consonant and a nucleus, and three operations on
forms. Fusion makes a vowel share its element with an adjacent consonant that has it.
Dissociation empties the nucleus of a vowel that shares its element with what follows, if the
next nucleus governs. Epenthesis marks the empty nuclei that are realized. The derivation
applies the three in this order.

The main theorem, `dissociation_empty_iff`, says when a vowel is lost. Suppose its melody is the
single element `e`. Then dissociation after fusion empties its nucleus if and only if its own
consonant lacks `e`, what follows has `e`, and the next nucleus governs. The other theorems
check the derivation against the attested forms of the paper's paradigms, and show that the
order of the operations matters.

## Implementation notes

* The final nucleus may be empty, does not govern, and licenses, so a final guttural is
  licensed. [scheer-zikova-2010] take a final nucleus to govern and license together or to do
  neither.
* The paper gives the mid vowels as |A| with |I| or |U|, and derives the lowering of a fused
  vowel from the span of its |A|. Here |I| and |U| are the heads of the mid vowels, and `headed`
  makes the fused element the head of a fused vowel.
* Read as the feature matrices of [kaye-lowenstamm-vergnaud-1985], the vowel melodies have the
  language file's values of [round], [front], [high], [ATR] and [low]: headed |A| is [+low] and
  plain
  |A| is [−low]. The language file's [back] is not determined by the elements.
* Among the consonants only the gutturals and the glides have a melody. The palatals and the
  ejectives contain |I| and |A| and never trigger syneresis; they are given no elements.
* The /ɨ/ of a pattern is a vowel with no element, not an empty nucleus, so its nucleus governs.
  [faust-2025] distinguishes a weak vowel from an empty nucleus in this way.
* `fusion` also applies to two /a/s in successive nuclei, as in the derivation of [mɨ-bɨrak]
  from /m_-barak/.
* `epenthesis` follows the left-to-right realization `GovernmentPhonology.leftToRight`. The
  right-to-left realization gives a different result where the dissociated nucleus is the third
  of three empty nuclei.
* Three things are left out of the data. The 3FPL forms of the perfective paradigms are not
  recorded. The postvocalic spirantization of b is not analysed, and `read` takes β as b. `read`
  takes a long [iː] as [i] followed by [j].

## TODO

* The ejectives lower a vowel and never cause its loss. This is not derived.
* That no operation applies again to a derived form is checked on the examples and not proved
  for every form.

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
* [faust-2025]
-/

@[expose] public section

namespace FaustLampitelli2026

open Morphology ElementTheory GovernmentPhonology Phonology
open Examples (Example)

/-! ### Vowels and gutturals -/

/-- The vowels of Tigrinya and Tigre: six full vowels and the weak vowel [ɨ] (p. 5). -/
inductive Vowel where
  | a
  | aBare
  | i
  | u
  | e
  | o
  | weak
  deriving DecidableEq, Repr, Fintype

/-- The vowel that a letter of the paper's transcription writes. -/
def Vowel.ofLetter? : String → Option Vowel
  | "a" => some .a
  | "ʌ" => some .aBare
  | "i" => some .i
  | "u" => some .u
  | "e" => some .e
  | "o" => some .o
  | "ɨ" => some .weak
  | _ => none

/-- The vowel `v` as a segment of the Tigrinya language file, which serves for both languages. -/
def Vowel.segment : Vowel → Phonology.Segment
  | .a => Tigrinya.Phonology.a
  | .aBare => Tigrinya.Phonology.«ʌ»
  | .i => Tigrinya.Phonology.i
  | .u => Tigrinya.Phonology.u
  | .e => Tigrinya.Phonology.e
  | .o => Tigrinya.Phonology.o
  | .weak => Tigrinya.Phonology.«ɨ»

theorem Vowel.segment_injective : Function.Injective Vowel.segment := by decide +kernel

/-- `Vowel.segment` as an embedding. -/
def Vowel.segmentEmbedding : Vowel ↪ Phonology.Segment := ⟨segment, segment_injective⟩

@[simp] theorem Vowel.coe_segmentEmbedding : ⇑Vowel.segmentEmbedding = Vowel.segment := rfl

theorem image_segment_eq_vowels :
    Finset.univ.map Vowel.segmentEmbedding = Tigrinya.Phonology.vowels := by
  decide +kernel

/-- A vowel is low if it is [a] or [ʌ]. -/
def Vowel.IsLow : Vowel → Prop
  | .a | .aBare => True
  | _ => False

instance : DecidablePred Vowel.IsLow := fun v ↦ by cases v <;> unfold Vowel.IsLow <;> infer_instance

/-- The gutturals: the glottals [ʔ] and [h], and the pharyngeals [ʕ] and [ħ]. -/
inductive Guttural where
  | glottalStop
  | h
  | pharyngealVoiced
  | pharyngealVoiceless
  deriving DecidableEq, Repr, Fintype

/-- The guttural `g` as a segment of the Tigrinya language file, which serves for both languages. -/
def Guttural.segment : Guttural → Phonology.Segment
  | .glottalStop => Tigrinya.Phonology.«ʔ»
  | .h => Tigrinya.Phonology.h
  | .pharyngealVoiced => Tigrinya.Phonology.«ʕ»
  | .pharyngealVoiceless => Tigrinya.Phonology.ħ

theorem Guttural.segment_injective : Function.Injective Guttural.segment := by decide +kernel

/-- `Guttural.segment` as an embedding. -/
def Guttural.segmentEmbedding : Guttural ↪ Phonology.Segment := ⟨segment, segment_injective⟩

@[simp] theorem Guttural.coe_segmentEmbedding : ⇑Guttural.segmentEmbedding = Guttural.segment :=
  rfl

/-- A guttural is pharyngeal if it is [ʕ] or [ħ]. -/
def Guttural.IsPharyngeal : Guttural → Prop
  | .pharyngealVoiced | .pharyngealVoiceless => True
  | _ => False

instance : DecidablePred Guttural.IsPharyngeal :=
  fun g ↦ by cases g <;> unfold Guttural.IsPharyngeal <;> infer_instance

-- the gutturals are consonants of both language files
theorem segment_mem_consonants : ∀ g : Guttural,
    g.segment ∈ Tigrinya.Phonology.consonants ∧ g.segment ∈ Tigre.Phonology.consonants := by
  decide +kernel

-- fn. 15: whether the gutturals are a natural class
theorem not_isNaturalClass_gutturals :
    ¬ Phonology.IsNaturalClass Tigrinya.Phonology.consonants
      (Finset.univ.map Guttural.segmentEmbedding) := by
  decide +kernel

/-! ### Melodies (20)–(22) -/

/-- (21)–(22): The melody of a vowel. [ʌ] is |A| and [a] is headed |A|. The mid vowels combine |A|
with |I| or |U|. The weak vowel has no element. -/
def vowelET : Vowel → MR
  | .a => .headedSimplex .A
  | .aBare => .simplex .A
  | .i => .headedSimplex .I
  | .u => .headedSimplex .U
  | .e => .headedSimplex .I ⊔ .simplex .A
  | .o => .headedSimplex .U ⊔ .simplex .A
  | .weak => ⊥

/-- (20): The melody of a guttural. Every guttural contains |A|, and |A| is the head of the
pharyngeals. -/
def gutturalET : Guttural → MR
  | .glottalStop => .headedSimplex .glottal ⊔ .simplex .A
  | .h => .headedSimplex .H ⊔ .simplex .A
  | .pharyngealVoiceless => .headedSimplex .A ⊔ .simplex .glottal ⊔ .simplex .H
  | .pharyngealVoiced => .headedSimplex .A ⊔ .simplex .glottal ⊔ .simplex .H ⊔ .simplex .L

theorem mem_elements_gutturalET : ∀ g : Guttural, .A ∈ (gutturalET g).elements := by decide

theorem mem_heads_gutturalET_iff : ∀ g : Guttural, .A ∈ (gutturalET g).heads ↔ g.IsPharyngeal := by
  decide

/-- The element of a vowel whose melody is a single element: |A| for the low vowels, |I| for [i] and
|U| for [u]. The mid vowels have two elements, which blocks fusion (§3.2.2), and the weak vowel
has none. -/
def Vowel.element? (v : Vowel) : Option Element :=
  [Element.A, .I, .U].find? fun e ↦ (vowelET v).elements = {e}

theorem element?_eq_some_A_iff_isLow : ∀ v : Vowel, v.element? = some .A ↔ v.IsLow := by decide

/-- The vowel with the melody `m`, if there is one. -/
def Vowel.ofMR? (m : MR) : Option Vowel :=
  [Vowel.a, .aBare, .i, .u, .e, .o, .weak].find? (vowelET · = m)

/-- (21), (27): The vowel `v` with the element `e` as its head, or `v` itself if no vowel has that
melody. A fused vowel is realized in this way, so fused [ʌ] is [a]. -/
def headed (e : Element) (v : Vowel) : Vowel :=
  (Vowel.ofMR? (vowelET v ⊔ .headedSimplex e)).getD v

theorem headed_aBare : headed .A .aBare = .a := by decide

-- read as the feature matrices of [kaye-lowenstamm-vergnaud-1985], the melodies of the vowels have
-- the language file's values of [round], [front], [high], [ATR] and [low]
theorem eqOn_interpret_vowelET : ∀ v : Vowel,
    Set.EqOn (KayeLowenstammVergnaud1985.interpret (vowelET v)) v.segment
      ↑KayeLowenstammVergnaud1985.features := by
  decide +kernel

-- the language file's [back] is not a function of the elements: [ʌ] and [a] are both |A| alone and
-- differ in it, and [ʌ] is [+back] with the vowels that have |U|
theorem back_segment_iff : ∀ v : Vowel,
    v.segment Feature.back = some true ↔ .U ∈ (vowelET v).elements ∨ v = .aBare := by
  decide +kernel

theorem headed_headed : ∀ (e : Element) (v : Vowel), headed e (headed e v) = headed e v := by
  intro e v; cases e <;> cases v <;> decide

/-! ### Strict CV forms -/

/-- The melody of a consonant. A guttural has the melody of (20). The glides [j] and [w] are |I| and
|U|, the elements of the high vowels in a consonantal position (3). Every other consonant is
given no elements: the palatals and the ejectives contain |I| and |A| but never trigger syneresis
(fn. 8). -/
def consET (c : Phonology.Segment) : MR :=
  if c = Tigrinya.Phonology.j then .simplex .I
  else if c = Tigrinya.Phonology.w then .simplex .U
  else (([.glottalStop, .h, .pharyngealVoiced, .pharyngealVoiceless] : List Guttural).find?
    (·.segment = c)).elim ⊥ gutturalET

/-- The melody of the consonant `c` contains the element `e`. -/
def Has (e : Element) (c : Phonology.Segment) : Prop := e ∈ (consET c).elements

instance (e : Element) : DecidablePred (Has e) := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

theorem has_A_segment : ∀ g : Guttural, Has .A g.segment := by decide +kernel

/-- (29): A nucleus in a derivation. It is empty, or empty and marked to be realized (▪), or it
holds a vowel. A fused vowel either shares its element with what follows ((26), (27)), or licenses
the consonant of its own unit, with which it forms a self-licensing domain (28). -/
inductive Nuc where
  | empty
  | mark
  | vowel (v : Vowel)
  | shared (v : Vowel)
  | selfLicensing (v : Vowel)
  deriving DecidableEq, Repr

/-- The vowel of a nucleus, if it holds one. -/
def Nuc.vowel? : Nuc → Option Vowel
  | .vowel v | .shared v | .selfLicensing v => some v
  | .empty | .mark => none

/-- A CV unit: a consonant and a nucleus ([lowenstamm-1996]). -/
structure CV where
  c : Phonology.Segment
  v : Nuc
  deriving DecidableEq

/-- A form is a list of CV units. -/
abbrev Form := List CV

/-- The consonant of unit `i` contains the element `e`. -/
def HasAt (e : Element) (f : Form) (i : ℕ) : Prop :=
  match f[i]? with
  | some u => Has e u.c
  | none => False

instance (e : Element) (f : Form) (i : ℕ) : Decidable (HasAt e f i) := by
  unfold HasAt; split <;> infer_instance

/-- Nucleus `i` holds a vowel headed by |A| that has not fused. This vowel is /a/. -/
def HeadedAAt (f : Form) (i : ℕ) : Prop :=
  match f[i]? with
  | some ⟨_, .vowel v⟩ => .A ∈ (vowelET v).heads
  | _ => False

instance (f : Form) (i : ℕ) : Decidable (HeadedAAt f i) := by
  unfold HeadedAAt; split <;> infer_instance

/-- Units `i` and `i + 1` have the same consonant, so nucleus `i` is inside a geminate. -/
def GeminateInternal (f : Form) (i : ℕ) : Prop :=
  match f[i]?, f[i + 1]? with
  | some u, some u' => u.c = u'.c
  | _, _ => False

instance (f : Form) (i : ℕ) : Decidable (GeminateInternal f i) := by
  unfold GeminateInternal; split <;> infer_instance

/-! ### Lateral relations -/

/-- The lateral actorship of Tigrinya and Tigre. A nucleus with a vowel governs and licenses ((23a),
(24)), and so does an epenthetic one. The final nucleus may be empty. It does not govern
(§3.3.1), and it licenses, as a final guttural requires (32a). -/
def actorship : Actorship := .ltp ↑Melody.floating ⊥ true true false

/-- The melody of a nucleus for the lateral relations: associated if it holds a vowel, and empty
otherwise, also when it is marked to be realized. -/
def Nuc.melody : Nuc → Melody
  | .vowel _ | .shared _ | .selfLicensing _ => .associated
  | .empty | .mark => .empty

/-- The nuclei of a form, none of them expressed. The realization takes these as its input. -/
def nuclei (f : Form) : List Nucleus := f.map fun u ↦ { melody := u.v.melody }

/-- The nuclei that are expressed whatever follows them: the first nucleus, since an initial empty
CV unit must be governed (fn. 21); a nucleus after a guttural, unless it is final, since a
guttural needs an expressed licensor (25); and a nucleus before a geminate, since the nucleus
inside a geminate stays empty. -/
def required (f : Form) : Finset ℕ :=
  (Finset.range f.length).filter fun i ↦
    i = 0 ∨ HasAt .A f i ∧ i + 1 < f.length ∨ GeminateInternal f (i + 1)

/-- The nuclei of a form before epenthesis: a nucleus is expressed if and only if it holds a vowel.
Government is computed on these, so only a nucleus with a vowel governs (23a). -/
def lexical (f : Form) : List Nucleus :=
  f.map fun u ↦ { melody := u.v.melody, expressed := decide (u.v.melody = .associated) }

/-- The nuclei of a form after epenthesis: a nucleus is expressed if and only if it holds a vowel or
is marked. -/
def surface (f : Form) : List Nucleus :=
  f.map fun u ↦ { melody := u.v.melody, expressed := decide (u.v ≠ .empty) }

/-! ### The operations of (30) -/

/-- (9), (26b), (27b), (28b): Fusion applies to a vowel whose melody is a single element `e`. If the
consonant of its unit has `e`, the vowel and the consonant form a self-licensing domain.
Otherwise, if the next consonant has `e`, or if this nucleus and the next both hold /a/ (39b), the
vowel shares `e` with what follows. Fusion always applies (§3.2.2). -/
def fusion (f : Form) : Form :=
  f.mapIdx fun i u ↦
    match u.v with
    | .vowel v =>
      match v.element? with
      | some e =>
        if Has e u.c then ⟨u.c, .selfLicensing (headed e v)⟩
        else if HasAt e f (i + 1) ∨ HeadedAAt f i ∧ HeadedAAt f (i + 1) then
          ⟨u.c, .shared (headed e v)⟩
        else u
      | none => u
    | _ => u

/-- (9), (26c): Dissociation empties a nucleus whose vowel shares its element with what follows, if
the next nucleus governs. A vowel in a self-licensing domain stays (28). -/
def dissociation (f : Form) : Form :=
  f.mapIdx fun i u ↦
    match u.v with
    | .shared _ => if IsGovernor actorship (lexical f) (i + 1) then ⟨u.c, .empty⟩ else u
    | _ => u

/-- Nucleus `i` is expressed in the left-to-right realization of the form, in which the required
nuclei and the nuclei of `R` are always expressed. -/
def Realized (R : Finset ℕ) (f : Form) (i : ℕ) : Prop :=
  ∃ x ∈ (leftToRight actorship (required f ∪ R) (nuclei f))[i]?, x.expressed = true

instance (R : Finset ℕ) (f : Form) (i : ℕ) : Decidable (Realized R f i) :=
  inferInstanceAs (Decidable (∃ x ∈ _, _))

/-- (30)–(31): Epenthesis marks each empty nucleus that is realized. -/
def epenthesis (R : Finset ℕ) (f : Form) : Form :=
  f.mapIdx fun i u ↦ if u.v = .empty ∧ Realized R f i then ⟨u.c, .mark⟩ else u

/-- (30): The derivation is fusion, then dissociation, then epenthesis. The nuclei of `R` are
required to be realized. -/
def derive (R : Finset ℕ) (f : Form) : Form := epenthesis R (dissociation (fusion f))

/-- The vowel of nucleus `i`, if it holds one. -/
def vowelAt (f : Form) (i : ℕ) : Option Vowel := f[i]?.bind (·.v.vowel?)

/-- (7), (19c): The vowels that a marked nucleus `i` can copy by trans-guttural harmony: the vowel
before its own consonant, if that consonant is a guttural, and the vowel after the next
consonant, if that consonant is a guttural. -/
def harmonySources (f : Form) (i : ℕ) : List Vowel :=
  (if 0 < i ∧ HasAt .A f i then (vowelAt f (i - 1)).toList else []) ++
    if HasAt .A f (i + 1) then (vowelAt f (i + 1)).toList else []

/-- The realizations of a marked nucleus: the weak vowel, or a copy of a harmony source. -/
def realizeMark (f : Form) (i : ℕ) : List (List Phonology.Segment) :=
  (Vowel.weak :: harmonySources f i).dedup.map fun v ↦ [v.segment]

/-- The realizations of nucleus `i`: those of a marked nucleus, the vowel the nucleus holds, or
nothing if it is empty. -/
def realizeNuc (f : Form) (i : ℕ) : List (List Phonology.Segment) :=
  match f[i]? with
  | some ⟨_, .mark⟩ => realizeMark f i
  | some ⟨_, .vowel v⟩ | some ⟨_, .shared v⟩ | some ⟨_, .selfLicensing v⟩ => [[v.segment]]
  | _ => [[]]

/-- The surface forms of a form: its consonants and the realizations of its nuclei in order, with
one surface form for each choice of realization. -/
def realizations (f : Form) : List (List Phonology.Segment) :=
  (List.range f.length).foldl (init := [[]]) fun acc i ↦
    acc.flatMap fun s ↦ (realizeNuc f i).map (s ++ (f[i]?.map (·.c)).toList ++ ·)

/-- A surface form with harmony, read as an underlying form. A marked nucleus holds the first vowel
it can copy, or is empty if there is none, and a fused vowel is an ordinary vowel. -/
def harmonized (f : Form) : Form :=
  f.mapIdx fun i u ↦
    match u.v with
    | .mark => ⟨u.c, ((harmonySources f i).head?.map Nuc.vowel).getD .empty⟩
    | .shared v | .selfLicensing v => ⟨u.c, .vowel v⟩
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
      if Has e c then .selfLicensing (headed e v)
      else if HasAt e f (i + 1) ∨ HeadedAAt f i ∧ HeadedAAt f (i + 1) then .shared (headed e v)
      else .vowel v⟩ := by
  simp only [fusion, List.getElem?_mapIdx, h, Option.map_some, he]
  split_ifs <;> rfl

/-- Syneresis ((9), (26), (40)). If the melody of the vowel of nucleus `i` is the single element
`e`, then dissociation after fusion empties the nucleus if and only if its own consonant lacks `e`,
the next consonant has `e` or both nuclei hold /a/, and the next nucleus governs. -/
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

-- a nucleus with a vowel is expressed in the left-to-right realization
theorem realized_of_melody (R : Finset ℕ) (f : Form) (i : ℕ) (u : CV) (hu : f[i]? = some u)
    (hm : u.v.melody = .associated) : Realized R f i := by
  have h := getElem?_leftToRight (A := actorship) (R := required f ∪ R) (l := nuclei f) i
  simp only [nuclei, List.getElem?_map, hu, Option.map_some] at h
  exact ⟨_, h, expressed_of_mem_leftToRight (List.mem_of_getElem? h) hm⟩

-- the nuclei of a form after epenthesis are its left-to-right realization
theorem surface_epenthesis (R : Finset ℕ) (f : Form) (hf : ∀ u ∈ f, u.v ≠ .mark) :
    surface (epenthesis R f) = leftToRight actorship (required f ∪ R) (nuclei f) := by
  refine List.ext_getElem? fun i ↦ ?_
  rw [getElem?_leftToRight]
  simp only [surface, nuclei, List.getElem?_map, getElem?_epenthesis]
  cases hu : f[i]? with
  | none => rfl
  | some u =>
    have hmark := hf u (List.mem_of_getElem? hu)
    have hr := realized_of_melody R f i u hu
    obtain ⟨c, v⟩ := u
    cases v <;> simp_all [Nuc.melody, Realized, nuclei]
    split_ifs <;> simp_all

theorem mark_notMem_fusion (f : Form) (hf : ∀ u ∈ f, u.v ≠ .mark) :
    ∀ u ∈ fusion f, u.v ≠ .mark := by
  intro u hu
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 hu
  have := hf _ (List.getElem_mem hi)
  split <;> (try split) <;> (try split_ifs) <;> simp_all

theorem mark_notMem_dissociation (f : Form) (hf : ∀ u ∈ f, u.v ≠ .mark) :
    ∀ u ∈ dissociation f, u.v ≠ .mark := by
  intro u hu
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 hu
  have := hf _ (List.getElem_mem hi)
  split <;> (try split_ifs) <;> simp_all

-- a derived form satisfies the Empty Category Principle
theorem emptyCategoryPrinciple_surface_derive (R : Finset ℕ) (f : Form)
    (hf : ∀ u ∈ f, u.v ≠ .mark) : EmptyCategoryPrinciple actorship (surface (derive R f)) := by
  rw [derive, surface_epenthesis R _ (mark_notMem_dissociation _ (mark_notMem_fusion f hf))]
  exact emptyCategoryPrinciple_leftToRight

/-! ### Patterns and endings (§2.1) -/

/-- A position of a pattern: a radical, a radical that geminates if it can, or a fixed segment.
Gutturals do not geminate (§2.1, (12)). -/
inductive Pos where
  | rad (i : ℕ)
  | gem (i : ℕ)
  | seg (s : Phonology.Segment)

/-- The nucleus that holds the vowel `v`. -/
abbrev V (v : Vowel) : Nuc := .vowel v

/-- A pattern is a prefix and a stem, each a list of positions with their nuclei. -/
structure Pattern where
  /-- The prefix, made of fixed segments. -/
  pre : List (Pos × Nuc) := []
  /-- The stem, which begins with the first radical. -/
  stem : List (Pos × Nuc)

/-- The positions of a pattern: the prefix followed by the stem. -/
def Pattern.positions (p : Pattern) : List (Pos × Nuc) := p.pre ++ p.stem

/-- The two languages of the paper. -/
inductive Lang where
  | tigrinya
  | tigre
  deriving DecidableEq, Repr

/-- The 2nd-person prefix tɨ-, with the /t/ of the language. Its nucleus is empty in the underlying
forms of (31)–(39). -/
def prefix2 : Lang → List (Pos × Nuc)
  | .tigrinya => [(.seg Tigrinya.Phonology.t, .empty)]
  | .tigre => [(.seg Tigre.Phonology.t, .empty)]

/-- The gerund prefix mɨ-. Its nucleus is empty in the underlying forms of (37a) and (39b). -/
def prefixGer : List (Pos × Nuc) := [(.seg Tigrinya.Phonology.m, .empty)]

/-- The pattern of each template in a language. -/
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

/-- The form obtained by filling the positions of a pattern with the consonants of a root. A
geminating position gives two units, or one if its consonant is a guttural. -/
def instantiate (t : List (Pos × Nuc)) (r : ConsonantalRoot Phonology.Segment) : Option Form :=
  (t.mapM fun (pn : Pos × Nuc) ↦
    match pn.1 with
    | .rad i => (r.segments[i]?).map fun c ↦ [CV.mk c pn.2]
    | .gem i => (r.segments[i]?).map fun c ↦
        if Has .A c then [CV.mk c pn.2] else [CV.mk c .empty, CV.mk c pn.2]
    | .seg c => some [CV.mk c pn.2]).map List.flatten

/-- An ending: a vowel for the last nucleus of the stem, if any, followed by further CV units. -/
structure Ending where
  vowel : Option Vowel := none
  rest : List (Phonology.Segment × Nuc) := []

/-- The ending of each suffix. -/
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

/-- The form obtained by attaching an ending to a stem. -/
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

/-- Each root of the examples, as a root of the language file of its language. -/
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

/-- The glyph of the inventory of a language for a consonant letter of the paper's transcription,
where the two differ. The coronals of Tigre are dental in its inventory, and the paper writes
the ejectives with a superscript. -/
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

/-- The segment that a letter of the paper's transcription of language `l` writes: a vowel, or a
consonant of the inventory of `l`. -/
def letter? (l : Lang) (x : String) : Option Phonology.Segment :=
  ((Vowel.ofLetter? x).map Vowel.segment).orElse fun _ ↦ (inventory l).segment? (glyph l x)

/-- The letters of a transcription. A superscript or a length mark belongs to the letter before it.
-/
def letters : List Char → List String
  | [] => []
  | [c] => [String.singleton c]
  | c :: d :: cs =>
    if d = 'ˁ' ∨ d = 'ˀ' ∨ d = 'ː' then String.ofList [c, d] :: letters cs
    else String.singleton c :: letters (d :: cs)

/-- The segments of a transcription of a form of language `l`. Hyphens are dropped, β is read as b,
and a long [iː] is read as [i] followed by [j]. -/
def read (l : Lang) (s : String) : Option (List Phonology.Segment) :=
  ((letters ((s.toList.filter (· ≠ '-')).map fun c ↦ if c = 'β' then 'b' else c)).flatMap
    fun x ↦ if x = "iː" then ["i", "j"] else [x]).mapM (letter? l)

/-! ### The paradigms (4)–(19) and the derivations (31)–(39) -/

/-- The underlying form of an example: its pattern instantiated by its root, with its ending
attached. -/
def stem (x : Example) : Option Form := do
  let r ← x.root
  let t ← x.template
  let f ← instantiate (pattern (lang r) t).positions (root r)
  pure ((x.suffix.map fun s ↦ attach f (ending s)).getD f)

/-- The index of the first nucleus of the stem of an example, after the prefix. -/
def stemStart (x : Example) : ℕ :=
  (x.template.map fun t ↦ (pattern .tigrinya t).pre.length).getD 0

/-- The attested forms of an example, as lists of segments. -/
def forms (x : Example) : List (List Phonology.Segment) :=
  (x.root.map lang).toList.flatMap fun l ↦
    (x.datum.primaryText :: x.datum.contrasts.map Prod.fst).filterMap (read l)

/-- The surface forms that the derivation gives for an example when the nuclei of `R` are required
to be realized. -/
def realizationsOf (R : Finset ℕ) (x : Example) : List (List Phonology.Segment) :=
  match stem x with
  | some f => realizations (derive R f)
  | none => []

/-- Dissociation empties nucleus `i` of the form. -/
def Dissociated (f : Form) (i : ℕ) : Prop :=
  (fusion f)[i]?.map (·.v) ≠ some .empty ∧ (dissociation (fusion f))[i]?.map (·.v) = some .empty

instance (f : Form) (i : ℕ) : Decidable (Dissociated f i) := inferInstanceAs (Decidable (_ ∧ _))

/-- A Tigrinya example retains its stem-initial nucleus if dissociation empties that nucleus and
epenthesis does not mark it (§3.3.3, (39)). -/
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

/-- Every attested form of (4)–(19) and (31)–(38) is a realization of the derived form of its
example, unless the example retains its stem-initial nucleus. -/
theorem mem_realizations_of_not_retains :
    ∀ x : Example, ¬ Retains x → ∀ w ∈ forms x, w ∈ realizationsOf ∅ x := by
  decide +kernel

/-- No attested form of an example that retains its stem-initial nucleus is a realization of its
derived form (39). These are the Tigrinya forms of (17b–d) and (18c). -/
theorem notMem_realizations_of_retains :
    ∀ x : Example, Retains x → ∀ w ∈ forms x, w ∉ realizationsOf ∅ x := by
  decide +kernel

/-- If the stem-initial nucleus is required to be realized, every attested form of an example that
retains it is a realization of the derived form. [buckley-2000] derives the requirement from the
alignment of the stem with a syllable. -/
theorem mem_realizations_stemStart_of_retains :
    ∀ x : Example, Retains x → ∀ w ∈ forms x, w ∈ realizationsOf {stemStart x} x := by
  decide +kernel

-- (17b–d), (18c)
theorem retains_iff : ∀ x : Example, Retains x ↔
    x ∈ [.ex_17b_imprf, .ex_17b_pass, .ex_17c_imprf, .ex_17c_pass, .ex_17d_imprf, .ex_17d_pass,
      .ex_18c_ger] := by
  decide +kernel

/-! ### The order of the operations (30) -/

/-- (36a): The underlying form /s_mʌʕ-i/ of the feminine imperative of 'hear'. -/
def imperative36a : Form :=
  attach ((instantiate (pattern .tigrinya .imp).positions Tigrinya.Phonology.hear).getD [])
    (ending .i)

/-- (37a): The underlying form /m_s_maʕ-u/ of the gerund of 'hear' with the suffix *-u*. -/
def gerund37a : Form :=
  attach ((instantiate (pattern .tigrinya .gerA).positions Tigrinya.Phonology.hear).getD [])
    (ending .u)

/-- (37d): The underlying form /sʌmʌʕ_-ku/ of the dependent perfective of 'hear' with the suffix
*-ku*. -/
def perfective37d : Form :=
  attach ((instantiate (pattern .tigrinya .depPrf).positions Tigrinya.Phonology.hear).getD [])
    (ending .ku)

/-- The number of marked nuclei of a form. -/
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

-- (9), (11): dissociation empties the vowel before the glide of /sʌtij-u/ and the vowel before
-- the guttural of /s_mʌʕ-i/; before the consonant-initial suffix of /sʌtij-na/ the vowel stays
theorem dissociated_drink :
    (∀ f ∈ stem .ex_8b_3msg, Dissociated f 1) ∧ Dissociated imperative36a 1 ∧
      ∀ f ∈ stem .ex_8b_1pl, (dissociation (fusion f))[1]?.map (·.v) = some (.shared .i) := by
  decide +kernel

/-! ### The autosegmental representation of a form -/

/-- The positions of a form: for each unit, a consonantal position with the melody of the consonant
and a vocalic position with the melody of the vowel. A nucleus that holds no vowel has no root
node. -/
def positions (f : Form) : List Position :=
  f.flatMap fun u ↦ [⟨.C, some (consET u.c)⟩, ⟨.V, u.v.vowel?.map vowelET⟩]

theorem getElem?_positions_two_mul (f : Form) (i : ℕ) :
    (positions f)[2 * i]? = f[i]?.map fun u ↦ ⟨.C, some (consET u.c)⟩ := by
  induction f generalizing i with
  | nil => simp [positions]
  | cons u r ih =>
    cases i with
    | zero => simp [positions]
    | succ i => simpa [positions, Nat.mul_succ] using ih i

theorem getElem?_positions_two_mul_add_one (f : Form) (i : ℕ) :
    (positions f)[2 * i + 1]? = f[i]?.map fun u ↦ ⟨.V, u.v.vowel?.map vowelET⟩ := by
  induction f generalizing i with
  | nil => simp [positions]
  | cons u r ih =>
    cases i with
    | zero => simp [positions]
    | succ i => simpa [positions, Nat.mul_succ] using ih i

-- the skeleton of a form is a strict sequence of CV units
theorem isStrict_positions (f : Form) :
    Autosegmental.Skeleton.IsStrict ((positions f).map (·.slot)) := by
  refine ⟨f.length, ?_⟩
  induction f with
  | nil => rfl
  | cons u r ih =>
    rw [List.length_cons, List.replicate_succ, List.flatten_cons, ← ih]
    simp [positions]

-- the consonantal position of a unit has a token of an element iff its consonant has the element
theorem exists_mem_melody_positions_iff (e : Element) (f : Form) (i : ℕ) :
    (∃ s, s ∈ (ofForm (positions f)).melody tiers (2 * i) (.line e)) ↔ HasAt e f i := by
  rw [exists_mem_melody_line_ofForm_iff, getElem?_positions_two_mul]
  unfold HasAt
  cases f[i]? <;> simp [Has]

-- the vocalic position of a unit has a root node iff its nucleus holds a vowel
theorem mem_melody_rootNode_positions_iff (f : Form) (i : ℕ) :
    () ∈ (ofForm (positions f)).melody tiers (2 * i + 1) .rootNode ↔
      ∃ u ∈ f[i]?, u.v.melody = .associated := by
  rw [mem_melody_rootNode_ofForm_iff, getElem?_positions_two_mul_add_one]
  rcases f[i]? with _ | ⟨c, n⟩
  · simp
  · cases n <;> simp [Nuc.vowel?, Nuc.melody]

theorem elements_vowelET_headed : ∀ (v : Vowel) (e : Element), v.element? = some e →
    (vowelET (headed e v)).elements = (vowelET v).elements := by
  decide

theorem elements_nucleus_fusion (f : Form) (i : ℕ) :
    (fusion f)[i]?.map (fun u ↦ (u.v.vowel?.map vowelET).map (·.elements)) =
      f[i]?.map fun u ↦ (u.v.vowel?.map vowelET).map (·.elements) := by
  simp only [fusion, List.getElem?_mapIdx]
  rcases f[i]? with _ | ⟨c, n⟩
  · rfl
  · cases n with
    | vowel v =>
      simp only [Option.map_some]
      rcases he : v.element? with _ | e
      · rfl
      · simp only; split_ifs <;> simp [Nuc.vowel?, elements_vowelET_headed v e he]
    | _ => rfl

-- fusion changes the elements of no position
theorem exists_mem_melody_positions_fusion_iff (f : Form) (k : ℕ) (e : Element) :
    (∃ s, s ∈ (ofForm (positions (fusion f))).melody tiers k (.line e)) ↔
      ∃ s, s ∈ (ofForm (positions f)).melody tiers k (.line e) := by
  rw [exists_mem_melody_line_ofForm_iff, exists_mem_melody_line_ofForm_iff]
  obtain ⟨i, rfl | rfl⟩ : ∃ i, k = 2 * i ∨ k = 2 * i + 1 := ⟨k / 2, by omega⟩
  · rw [getElem?_positions_two_mul, getElem?_positions_two_mul]
    have := map_c_fusion f i
    cases h1 : (fusion f)[i]? <;> cases h2 : f[i]? <;> simp_all
  · rw [getElem?_positions_two_mul_add_one, getElem?_positions_two_mul_add_one]
    have := elements_nucleus_fusion f i
    rcases h1 : (fusion f)[i]? with _ | u' <;> rcases h2 : f[i]? with _ | u <;> simp_all
    rcases hv' : u'.v.vowel? with _ | v' <;> rcases hv : u.v.vowel? with _ | v <;> simp_all

/-- (37b): The underlying form /s_ħʌb/ of the imperative of 'pull'. -/
def imperativePull : Form :=
  (instantiate (pattern .tigrinya .imp).positions Tigrinya.Phonology.pull).getD []

/-- (7f): The underlying form /s_ʔʌl/ of the imperative of 'ask'. -/
def imperativeAsk : Form :=
  (instantiate (pattern .tigrinya .imp).positions Tigrinya.Phonology.ask).getD []

-- (20), (21), (27): when |A| spreads from its consonant, a nucleus has it as a head after a
-- pharyngeal and as a dependent after a glottal; `fusion` gives the vowel a head after both
theorem mem_melody_spread_status :
    Status.head ∈ (spread (positions imperativePull) .A 2 3).melody tiers 3 (.line .A) ∧
      Status.dependent ∈ (spread (positions imperativeAsk) .A 2 3).melody tiers 3 (.line .A) ∧
      ∀ f ∈ [imperativePull, imperativeAsk],
        ((positions (fusion f))[3]?.bind (·.melody)).map (·.status .A) = some .head := by
  decide +kernel

/-- (39b): The underlying form /m_-barak/ of the type C gerund of 'bless'. -/
def gerund39b : Form :=
  (instantiate (pattern .tigrinya .gerC).positions Tigrinya.Phonology.bless).getD []

/-- (37c): The underlying form /sʌħʌb/ of the dependent perfective of 'pull'. -/
def depPrf37c : Form :=
  (instantiate (pattern .tigrinya .depPrf).positions Tigrinya.Phonology.pull).getD []

-- (39b): spreading |A| between the two /a/s of /m_-barak/ crosses no line; spreading it between
-- the two vowels of /sʌħʌb/ crosses the line of the guttural
theorem noCrossing_spread_39b :
    (spread (positions gerund39b) .A 5 3).NoCrossing ∧
      ¬ (spread (positions depPrf37c) .A 3 1).NoCrossing := by
  decide +kernel

/-! ### Trans-guttural harmony and the derivation (pp. 24–25) -/

/-- Trans-guttural harmony feeds dissociation (37d). Dissociation does not apply to the derived form
[sʌmaʕ▪ku], and it applies once the marked nucleus holds a copy of [a]. -/
theorem feeds_harmonized :
    Feeds harmonized (fun f ↦ dissociation (fusion f) ≠ fusion f) (derive ∅ perfective37d) := by
  decide +kernel

-- (37d): a derivation that read the harmonized form again would yield *[sʌmʕaku]
theorem realizations_harmonized_37d :
    (realizations (derive ∅ (harmonized (derive ∅ perfective37d)))).map some =
        [read .tigrinya "sʌmʕaku"] ∧
      ∀ w ∈ read .tigrinya "sʌmʕaku", w ∉ realizations (derive ∅ perfective37d) := by
  decide +kernel

-- (37b,c): /s_ħʌb/ and /sʌħʌb/ have the same derived form, and deriving its harmonized form
-- gives the same form again
theorem derive_harmonized_pull :
    ∀ f ∈ [instantiate (pattern .tigrinya .imp).positions Tigrinya.Phonology.pull,
        instantiate (pattern .tigrinya .depPrf).positions Tigrinya.Phonology.pull],
      ∀ g ∈ f, derive ∅ g = [⟨Tigrinya.Phonology.s, .mark⟩,
          ⟨Tigrinya.Phonology.ħ, .selfLicensing .a⟩, ⟨Tigrinya.Phonology.b, .empty⟩] ∧
        harmonized (derive ∅ g) ≠ derive ∅ g ∧ derive ∅ (harmonized (derive ∅ g)) = derive ∅ g := by
  decide +kernel

/-! ### Proper government and the obligatory realization -/

/-- (32a): The underlying form /t_-s_mʌʕ_/ of the 2nd-person jussive of 'hear'. -/
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

-- no underlying form of the examples has a marked nucleus
theorem mark_notMem_stem : ∀ x : Example, ∀ f ∈ stem x, ∀ u ∈ f, u.v ≠ .mark := by
  decide +kernel

/-- The ways of expressing a list of nuclei that satisfy the Empty Category Principle, express the
nuclei of `R`, and express as few nuclei as possible. -/
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

/-- (37a): The first three nuclei of the form are empty after dissociation, and dissociation emptied
the third. -/
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
