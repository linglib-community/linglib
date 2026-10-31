module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Phonology.Segmental.ElementTheory
public import Linglib.Phonology.Segmental.NaturalClass
public import Linglib.Fragments.Tigrinya.Phonology
public import Linglib.Fragments.Tigre.Phonology
public import Linglib.Data.Examples.FaustLampitelli2026
public import Linglib.Phonology.StrictCV.Basic
public import Linglib.Data.Examples.Readers

/-!
# Faust and Lampitelli (2026): Guttural syneresis in Tigrinya and Tigre

In Tigrinya and Tigre a low vowel in an open syllable before a guttural is syncopated, as in
[sɨmʕ-i] from /s_mʌʕ-i/, the way /i/ is before /j/. Faust and Lampitelli explain this by Element
Theory: gutturals and low vowels share the element |A|, and two adjacent |A|s fuse into one. The
analysis runs in Strict CV with the lateral relations of Government Phonology, by fusion,
dissociation and epenthesis applied in the order "rules apply" gives, which makes syneresis
opaque in several forms. In the feature system the gutturals are no natural class, so the
analysis needs the element.

## Implementation notes

* The analysis runs over the paper's transcription, and its vowels and gutturals are the
  paper's; `fragment_roots` shows that its roots, read as segments, are the Tigrinya and Tigre
  fragments' roots.
* A form is a list of CV units; templates are positions (radical, geminable radical, fixed
  segment) with nuclei, instantiated by a fragment root. Gutturals do not geminate (§2.1), so
  a geminable position holding a guttural is a single unit ((12): -sʌʔɨl).
* The prefixes tɨ- and mɨ- carry empty nuclei realized by epenthesis, as in the paper's
  underlying forms (t_-, m_-); the causative ʔʌ- is lexical (19c).
* Government is Strict CV's, of which the paper's (23) is a simplified version (fn. 16), and the
  final nucleus of both languages may be empty and does not govern. Epenthesis is the paper's
  left-to-right procedure, in which a nucleus after a silent one is realized, so that a run of
  empty nuclei takes the Ethiosemitic option C▪C_C▪C of (37a) and not the standard one.
* Trans-guttural harmony "can, but does not have to apply" (§2.1), so `realizations` lists
  every option and `rows_derived` asks that each attested form be among them. Realization
  does not feed fusion again, the paper's first way out of the loop of (37b–d).
* The postvocalic spirantization of b ([nɨβaħ], (10b)) is outside the analysis; β is read as b.
* Not derived: the |I|-syneresis of (8)–(9) and the ejective asymmetry of fn. 8.

## TODO

That a final guttural needs no licensor ((32a)) is stipulated. The paper ascribes to Scheer and
Ziková final nuclei that license without governing, but they make a final nucleus govern and
license or do neither, and these forms need one that does not govern (`governs_32a`).

## References

* [faust-lampitelli-2026]
* [kaye-lowenstamm-vergnaud-1985]
* [backley-2011]
* [angoujard-1995]
* [lowenstamm-1996]
* [scheer-2004]
* [kaye-lowenstamm-vergnaud-1990]
* [charette-1991]
* [scheer-segeral-2001]
* [scheer-zikova-2010]
* [kaye-1992]
* [bye-2011]
* [buckley-2000]
-/

@[expose] public section

namespace FaustLampitelli2026

open Morphology ElementTheory

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

/-- The pharyngeals are [ʕ] and [ħ]. -/
def Guttural.IsPharyngeal : Guttural → Prop
  | .pharyngealVoiced | .pharyngealVoiceless => True
  | _ => False

instance : DecidablePred Guttural.IsPharyngeal :=
  fun g ↦ by cases g <;> unfold Guttural.IsPharyngeal <;> infer_instance

/-- In the feature system the gutturals form no natural class of Tigrinya consonants, whereas
Element Theory groups them by their |A| (20). -/
theorem not_isNaturalClass_gutturals :
    ¬ Phonology.IsNaturalClass Tigrinya.Phonology.consonants
      (Finset.univ.image Guttural.segment) := by
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

/-- The fused |A|, spanning nucleus and consonant, is headed ((21), (27)), so a fused vowel is
realized with |A| as its head and [ʌ] lowers to [a]. -/
def lowered (v : Vowel) : Vowel := (Vowel.ofMR? (vowelET v ⊔ .headedSimplex .A)).getD v

theorem lowered_aBare : lowered .aBare = .a := by decide

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
lexical vowel, shaded when fused with an adjacent guttural. -/
inductive Nuc where
  | empty
  | mark
  | vowel (v : Vowel) (fused : Bool)
  deriving DecidableEq, Repr

/-- A CV unit ([lowenstamm-1996]). -/
structure CV where
  c : Cons
  v : Nuc
  deriving DecidableEq, Repr

/-- A form is a strict iteration of CV units. -/
abbrev Form := List CV

/-- The consonant at `i` contains |A|. -/
def HasAAt (f : Form) (i : Nat) : Prop :=
  match f[i]? with
  | some u => u.c.HasA
  | none => False

instance (f : Form) (i : Nat) : Decidable (HasAAt f i) := by
  unfold HasAAt; split <;> infer_instance

/-- The nucleus at `i` sits inside a geminate. -/
def GeminateInternal (f : Form) (i : Nat) : Prop :=
  match f[i]?, f[i + 1]? with
  | some u, some u' => u.c = u'.c
  | _, _ => False

instance (f : Form) (i : Nat) : Decidable (GeminateInternal f i) := by
  unfold GeminateInternal; split <;> infer_instance

/-! ### Lateral relations -/

/-- The final nucleus of Tigrinya and Tigre may be empty and does not govern. -/
def final : StrictCV.FinalNucleus := ⟨true, false⟩

/-- The melody of a nucleus is associated for a lexical vowel and empty otherwise, even when the
nucleus is marked for epenthesis. -/
def Nuc.melody : Nuc → StrictCV.Melody
  | .vowel _ _ => .associated
  | .empty | .mark => .empty

/-- The nuclei of a form as the lateral computation reads them. The first nucleus must be
pronounced, since an initial empty CV unit needs its government (fn. 21), and so must a nucleus
whose onset is a guttural, which needs a pronounced licensor (25), unless the nucleus is final
((32a)). -/
def nuclei (f : Form) : List StrictCV.Nucleus :=
  f.mapIdx fun i u ↦
    { melody := u.v.melody
      forced := decide (i = 0 ∨ u.c.HasA ∧ i + 1 < f.length) }

/-- The nuclei of a form before epenthesis, those with a lexical vowel pronounced, so that only a
contentful nucleus governs (23a). -/
def lexical (f : Form) : List (StrictCV.Nucleus × Bool) :=
  (nuclei f).map fun x ↦ (x, decide (x.melody = .associated))

/-! ### The operations of (30) -/

/-- Fusion ((26b), (27b), (28b)) fuses a low vowel next to an |A| consonant, its own onset or the
next, with that consonant and lowers it. Fusion always applies (§3.2.2). -/
def fusion (f : Form) : Form :=
  f.mapIdx fun i u ↦
    match u.v with
    | .vowel v false =>
      if IsLowA v ∧ (u.c.HasA ∨ HasAAt f (i + 1)) then ⟨u.c, .vowel (lowered v) true⟩ else u
    | _ => u

/-- Dissociation (26c) empties a fused nucleus iff the nuclei after it govern it and it is not the
licensor of its own fused domain, that is, iff the guttural is the next onset (Av + Ac) rather
than its own (Ac + Av, (28)). -/
def dissociation (f : Form) : Form :=
  f.mapIdx fun i u ↦
    match u.v with
    | .vowel _ true =>
      if HasAAt f (i + 1) ∧ ¬ u.c.HasA ∧ StrictCV.Governs final ((lexical f).drop (i + 1)) then
        ⟨u.c, .empty⟩
      else u
    | _ => u

/-- Epenthesis (30)–(31) marks the empty nuclei that must be realized. The word-final nucleus and a
nucleus inside a geminate stay empty; the initial nucleus (no initial clusters), the nucleus
licensing a word-internal guttural (25), a nucleus after a silent empty one (no triconsonantal
clusters) and a nucleus before a geminate are realized; every other empty nucleus is governed and
silent. -/
def epenthesis (f : Form) : Form :=
  (f.zipIdx.foldl (init := ([], false)) fun (acc : Form × Bool) (ui : CV × Nat) ↦
    match ui.1.v with
    | .empty =>
      if ui.2 + 1 = f.length ∨ GeminateInternal f ui.2 then (acc.1 ++ [ui.1], true)
      else if ui.2 = 0 ∨ ui.1.c.HasA ∨ acc.2 ∨ GeminateInternal f (ui.2 + 1) then
        (acc.1 ++ [⟨ui.1.c, .mark⟩], false)
      else (acc.1 ++ [ui.1], true)
    | _ => (acc.1 ++ [ui.1], false)).1

/-- The derivation applies the operations in the order "rules apply" gives (30), since fusion
creates the environment of dissociation, which creates that of epenthesis. -/
def derive (f : Form) : Form := epenthesis (dissociation (fusion f))

/-- The lexical vowel at `i`, if any. -/
def vowelAt (f : Form) (i : Nat) : Option Vowel :=
  match f[i]? with
  | some ⟨_, .vowel v _⟩ => some v
  | _ => none

/-- A nucleus to be realized surfaces as the weak vowel, or, by trans-guttural harmony ((7), (19c)),
as a copy of the vowel across an adjacent guttural in either direction. -/
def realizeMark (f : Form) (i : Nat) : List (List Char) :=
  (['ɨ'] ::
    ((if 0 < i ∧ HasAAt f i then (vowelAt f (i - 1)).toList else []) ++
      (if HasAAt f (i + 1) then (vowelAt f (i + 1)).toList else [])).map
        (·.toIPA.toList)).dedup

/-- The realizations of the nucleus at `i`. -/
def realizeNuc (f : Form) (i : Nat) : List (List Char) :=
  match f[i]? with
  | some ⟨_, .mark⟩ => realizeMark f i
  | some ⟨_, .vowel v _⟩ => [v.toIPA.toList]
  | _ => [[]]

/-- The transcription of the consonant at `i`. -/
def consAt (f : Form) (i : Nat) : List Char :=
  match f[i]? with
  | some u => u.c.chars
  | none => []

/-- The surface forms of a form are its consonants and realized nuclei in order, one form per choice
of realization. -/
def realizations (f : Form) : List (List Char) :=
  (List.range f.length).foldl (init := [[]]) fun acc i ↦
    acc.flatMap fun s ↦ (realizeNuc f i).map (s ++ consAt f i ++ ·)

-- §3.2.2
theorem fusion_fuses (f : Form) (i : Nat) (c : Cons) (v : Vowel)
    (h : (fusion f)[i]? = some ⟨c, .vowel v false⟩) :
    ¬ (IsLowA v ∧ (c.HasA ∨ HasAAt f (i + 1))) := by
  simp only [fusion, List.getElem?_mapIdx, Option.map_eq_some_iff] at h
  obtain ⟨u, -, hu⟩ := h
  split at hu
  · split at hu
    · exact absurd (congrArg CV.v hu) (by simp)
    · cases hu
      simp_all
  · cases hu
    simp_all

-- (26c), (28)
theorem dissociation_empty_iff (f : Form) (i : Nat) (u : CV) (h : f[i]? = some u) :
    (dissociation f)[i]? = some ⟨u.c, .empty⟩ ↔
      u.v = .empty ∨ ∃ v, u.v = .vowel v true ∧
        HasAAt f (i + 1) ∧ ¬ u.c.HasA ∧ StrictCV.Governs final ((lexical f).drop (i + 1)) := by
  simp only [dissociation, List.getElem?_mapIdx, h, Option.map_some, Option.some.injEq]
  obtain ⟨c, n⟩ := u
  cases n with
  | empty => simp
  | mark => simp
  | vowel v fused =>
    cases fused
    · simp
    · simp only [Nuc.vowel.injEq, reduceCtorEq, false_or]
      split <;> simp_all

/-! ### Templates and suffixes (§2.1) -/

/-- A templatic position is a radical, a radical geminated where it can be, since gutturals cannot
geminate (§2.1, (12)), or fixed segmental material. -/
inductive Pos where
  | rad (i : Nat)
  | gem (i : Nat)
  | seg (s : String)

/-- A template is a list of positions with their nuclei; Q, T, L are the radicals. -/
abbrev Template := List (Pos × Nuc)

/-- A lexical vowel. -/
abbrev V (v : Vowel) : Nuc := .vowel v false

/-- A template instantiated by a root. -/
def instantiate (t : Template) (r : ConsonantalRoot String) : Option Form :=
  (t.mapM fun (pn : Pos × Nuc) ↦
    match pn.1 with
    | .rad i => (r.segments[i]?).map fun s ↦ [CV.mk (Cons.ofIPA s) pn.2]
    | .gem i => (r.segments[i]?).map fun s ↦
        let c := Cons.ofIPA s
        if c.HasA then [CV.mk c pn.2] else [CV.mk c .empty, CV.mk c pn.2]
    | .seg s => some [CV.mk (Cons.ofIPA s) pn.2]).map List.flatten

/-- A suffix is a vowel filling the stem-final nucleus, then further CV units. -/
structure Suffix where
  vowel : Option Vowel := none
  rest : List (String × Nuc) := []

/-- A stem with a suffix. -/
def attach (f : Form) (s : Suffix) : Form :=
  (match s.vowel with
    | some v => f.dropLast ++ (f.getLast?.map fun u ↦ [⟨u.c, .vowel v false⟩]).getD []
    | none => f) ++ s.rest.map fun cn ↦ ⟨Cons.ofIPA cn.1, cn.2⟩

/-- The 2nd-person prefix tɨ-, an empty nucleus in the underlying forms of (31)–(39). -/
def prefix2 : Template := [(.seg "t", .empty)]

/-- DEP.PRF QʌTʌL (4). -/
def depPrf : Template := [(.rad 0, V .aBare), (.rad 1, V .aBare), (.rad 2, .empty)]

/-- The type B DEP.PRF QʌTTʌL, with medial gemination (18b). -/
def depPrfB : Template := [(.rad 0, V .aBare), (.gem 1, V .aBare), (.rad 2, .empty)]

/-- The type C DEP.PRF QaTʌL, with [a] after the first radical (18c). -/
def depPrfC : Template := [(.rad 0, V .a), (.rad 1, V .aBare), (.rad 2, .empty)]

/-- PRF QʌTiL (4). -/
def prf : Template := [(.rad 0, V .aBare), (.rad 1, V .i), (.rad 2, .empty)]

/-- IMPRF QʌTTɨL (4), the Tigre 2-IMP.M with its prefix (12). -/
def imprf : Template := [(.rad 0, V .aBare), (.gem 1, V .weak), (.rad 2, .empty)]

/-- 2-IMPRF tɨ-QʌTTɨL ((7), (17)). -/
def imprf2 : Template := prefix2 ++ imprf

/-- The 2-IMPRF without gemination, tɨ-QʌTɨL, as (7c) [ta-ħadɨm] shows it. -/
def imprf2NoGem : Template :=
  prefix2 ++ [(.rad 0, V .aBare), (.rad 1, V .weak), (.rad 2, .empty)]

/-- PASS-PRF tɨ-QʌTiL (17). -/
def passPrf : Template := prefix2 ++ prf

/-- IMP QɨTʌL ((5), (10)). -/
def imp : Template := [(.rad 0, .empty), (.rad 1, V .aBare), (.rad 2, .empty)]

/-- 2-JUSS tɨ-QTʌL ((5)–(6), (31)–(32)). -/
def juss2 : Template := prefix2 ++ imp

/-- The Tigre IMP QaTTɨL of (5a). -/
def impGem : Template := [(.rad 0, V .a), (.gem 1, V .weak), (.rad 2, .empty)]

/-- The Tigre 2-JUSS tɨ-QaTTɨL of (5a). -/
def jussGem2 : Template := prefix2 ++ impGem

/-- The type A gerund mɨQTaL (13). -/
def gerA : Template := [(.seg "m", .empty), (.rad 0, .empty), (.rad 1, V .a), (.rad 2, .empty)]

/-- The type B gerund mɨQTTaL (18b). -/
def gerB : Template := [(.seg "m", .empty), (.rad 0, .empty), (.gem 1, V .a), (.rad 2, .empty)]

/-- The type C gerund mɨQaTaL ((18c), (39b)). -/
def gerC : Template := [(.seg "m", .empty), (.rad 0, V .a), (.rad 1, V .a), (.rad 2, .empty)]

/-- The causative PRF ʔʌQTiL (19c). -/
def caus : Template := [(.seg "ʔ", V .aBare), (.rad 0, .empty), (.rad 1, V .i), (.rad 2, .empty)]

/-- The Tigre PRF-3MSG stem QaTL- (6). -/
def prf3 : Template := [(.rad 0, V .a), (.rad 1, .empty), (.rad 2, .empty)]

/-! ### The paradigms (4)–(19) and the derivations (31)–(39) -/

/-- The languages of the rows. -/
inductive Lang where
  | tigrinya
  | tigre
  deriving DecidableEq, Repr

/-- An attested form with the root, template and suffix that build it, and whether the analysis
predicts it. -/
structure Row where
  lang : Lang
  root : ConsonantalRoot String
  template : Template
  suffix : Option Suffix
  /-- The attested forms, hyphens removed and β read as b. -/
  forms : List (List Char)
  predicted : Bool

def langTable : List (String × Lang) := [("tigr1271", .tigrinya), ("tigr1270", .tigre)]

/-- The Tigrinya roots of the rows, in the paper's transcription. -/
def tigrinyaRoots : List (String × ConsonantalRoot String) :=
  [("whip", ⟨["g", "r", "f"]⟩), ("hear", ⟨["s", "m", "ʕ"]⟩), ("arrest", ⟨["ʔ", "s", "r"]⟩),
   ("pull", ⟨["s", "ħ", "b"]⟩), ("teach", ⟨["m", "h", "r"]⟩), ("slaughter", ⟨["ħ", "r", "d"]⟩),
   ("escape", ⟨["ħ", "d", "m"]⟩), ("ask", ⟨["s", "ʔ", "l"]⟩), ("uncover", ⟨["g", "l", "h"]⟩),
   ("bark", ⟨["n", "b", "ħ"]⟩), ("hurt", ⟨["b", "d", "l"]⟩), ("bless", ⟨["b", "r", "k"]⟩),
   ("arf", ⟨["ʕ", "r", "f"]⟩)]

/-- The Tigre roots of the rows, in the paper's transcription. -/
def tigreRoots : List (String × ConsonantalRoot String) :=
  [("weigh", ⟨["m", "z", "n"]⟩), ("leave", ⟨["f", "g", "r"]⟩), ("wash", ⟨["ħ", "tˁ", "b"]⟩),
   ("flee", ⟨["h", "r", "b"]⟩), ("getUp", ⟨["kˀ", "n", "sˁ"]⟩), ("whip", ⟨["f", "g", "r"]⟩),
   ("ask", ⟨["s", "ʔ", "l"]⟩), ("load", ⟨["tˀ", "ʕ", "n"]⟩), ("uncover", ⟨["s", "ħ", "k"]⟩),
   ("pull", ⟨["s", "ħ", "b"]⟩)]

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

theorem fragment_roots :
    tigrinyaRoots.map (·.2.map (segment .tigrinya)) =
      [Tigrinya.Phonology.whip, Tigrinya.Phonology.hear, Tigrinya.Phonology.arrest,
        Tigrinya.Phonology.pull, Tigrinya.Phonology.teach, Tigrinya.Phonology.slaughter,
        Tigrinya.Phonology.escape, Tigrinya.Phonology.ask, Tigrinya.Phonology.uncover,
        Tigrinya.Phonology.bark, Tigrinya.Phonology.hurt, Tigrinya.Phonology.bless,
        Tigrinya.Phonology.arf] ∧
    tigreRoots.map (·.2.map (segment .tigre)) =
      [Tigre.Phonology.weigh, Tigre.Phonology.leave, Tigre.Phonology.wash, Tigre.Phonology.flee,
        Tigre.Phonology.getUp, Tigre.Phonology.whip, Tigre.Phonology.ask, Tigre.Phonology.load,
        Tigre.Phonology.uncover, Tigre.Phonology.pull] :=
  ⟨rfl, rfl⟩

def templateTable : List (String × Template) :=
  [("depPrf", depPrf), ("depPrfB", depPrfB), ("depPrfC", depPrfC), ("prf", prf),
   ("imprf", imprf), ("imprf2", imprf2), ("imprf2NoGem", imprf2NoGem), ("passPrf", passPrf),
   ("imp", imp), ("juss2", juss2),
   ("impGem", impGem), ("jussGem2", jussGem2), ("gerA", gerA), ("gerB", gerB), ("gerC", gerC),
   ("caus", caus), ("prf3", prf3)]

def suffixTable : List (String × Suffix) :=
  [("a", ⟨some .a, []⟩), ("i", ⟨some .i, []⟩), ("u", ⟨some .u, []⟩), ("ʌ", ⟨some .aBare, []⟩),
   ("ej", ⟨some .e, [("j", .empty)]⟩), ("om", ⟨some .o, [("m", .empty)]⟩),
   ("ku", ⟨none, [("k", V .u)]⟩), ("ka", ⟨none, [("k", V .a)]⟩)]

/-- `transcribe s` is a transcription as compared with the realizations, hyphens removed and β read
as b. -/
def transcribe (s : String) : List Char :=
  (s.toList.filter (· ≠ '-')).map fun c ↦ if c = 'β' then 'b' else c

def Row.ofDatum (ex : Datum) : Option Row := do
  let lang ← List.lookup ex.language langTable
  let root ← ex.parse? "root" (match lang with | .tigrinya => tigrinyaRoots | .tigre => tigreRoots)
  let template ← ex.parse? "template" templateTable
  pure ⟨lang, root, template, ex.parse? "suffix" suffixTable,
    (ex.primaryText :: ex.alternatives.map Prod.fst).map transcribe,
    ex.feature? "predicted" != some "no"⟩

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- The underlying form of a row is its template instantiated by its root, with its suffix. -/
def Row.stem (r : Row) : Option Form :=
  (instantiate r.template r.root).map fun f ↦ (r.suffix.map (attach f)).getD f

/-- The surface forms the analysis yields for a row. -/
def Row.realizations (r : Row) : List (List Char) :=
  match r.stem with
  | some f => FaustLampitelli2026.realizations (derive f)
  | none => []

theorem rows_stem_isSome : ∀ r ∈ rows, r.stem.isSome := by decide

/-- Every attested form of (4)–(19) and (31)–(38) is a realization of the derivation of its
underlying form. -/
theorem rows_derived : ∀ r ∈ rows, r.predicted → ∀ f ∈ r.forms, f ∈ r.realizations := by
  decide +kernel

/-- The forms of (17b–d) and (39) realize the position the analysis empties, which it does not
predict (§3.3.3). -/
theorem rows_unpredicted : ∀ r ∈ rows, ¬ r.predicted → ∀ f ∈ r.forms, f ∉ r.realizations := by
  decide +kernel

/-! ### Proper government and the standard realization -/

/-- The 2nd-person jussive of 'hear', /t_-s_mʌʕ_/ (32a). -/
def jussive32a : Form := (instantiate juss2 ⟨["s", "m", "ʕ"]⟩).getD []

/-- The fused vowel of (32a) is governed by the following nucleus iff final nuclei act, so [tɨsmaʕ]
shows the final nucleus does not govern (§3.3.1). -/
theorem governs_32a (p : StrictCV.FinalNucleus) :
    StrictCV.Governs p ((lexical (fusion jussive32a)).drop 3) ↔ p.acts = true := by
  cases p with | mk e a => cases e <;> cases a <;> decide

/-- The gerund of 'hear' with the suffix *-u*, /m_s_maʕ-u/ (37a). -/
def gerund37a : Form := attach ((instantiate gerA ⟨["s", "m", "ʕ"]⟩).getD []) ⟨some .u, []⟩

/-- `pronounced f` marks the nuclei of `f` that are pronounced, its lexical vowels and the nuclei
marked for epenthesis. -/
def pronounced (f : Form) : List Bool := f.map fun u ↦ decide (u.v ≠ .empty)

/-- The realizations of a sequence of nuclei that satisfy the ECP, pronounce the required nuclei,
and pronounce as few nuclei as possible. -/
def economical (p : StrictCV.FinalNucleus) (l : List StrictCV.Nucleus) :
    List (List (StrictCV.Nucleus × Bool)) :=
  let admissible := (l.map fun x ↦ [(x, false), (x, true)]).sections.filter fun r ↦
    decide (StrictCV.SatisfiesECP p r ∧ ∀ y ∈ r, y.1.forced = true → y.2 = true)
  admissible.filter fun r ↦ admissible.all fun r' ↦ r.countP (·.2) ≤ r'.countP (·.2)

/-- In (37a), three empty nuclei precede the lexical vowel, and the derivation yields the
Ethiosemitic realization [C▪C_C▪C] rather than the standard one (§3.3.3). -/
theorem syneresis_37a :
    (nuclei (dissociation (fusion gerund37a))).map (·.melody) =
        [.empty, .empty, .empty, .associated] ∧
      (∀ p, (economical p (nuclei (dissociation (fusion gerund37a)))).map (·.map Prod.snd) =
        [[true, true, false, true], [true, false, true, true]]) ∧
      (∀ p, (StrictCV.standard p (nuclei (dissociation (fusion gerund37a)))).map Prod.snd =
        [true, true, false, true]) ∧
      pronounced (derive gerund37a) = [true, false, true, true] := by
  decide +kernel

/-- In the configuration of (37a), the dissociated position is the third in a left-aligned
sequence of three empty nuclei. -/
def DissociatedThird (f : Form) : Prop :=
  (fusion f)[2]?.map (·.v) ≠ some .empty ∧
    ∀ i < 3, (dissociation (fusion f))[i]?.map (·.v) = some .empty

instance (f : Form) : Decidable (DissociatedThird f) := inferInstanceAs (Decidable (_ ∧ _))

/-- On every form of (4)–(19) and (31)–(39), the derivation pronounces the standard realization
except in the configuration of (37a) (§3.3.3). -/
theorem rows_pronounced_eq_standard : ∀ r ∈ rows, ∀ f ∈ r.stem,
    pronounced (derive f) = (StrictCV.standard final (nuclei (dissociation (fusion f)))).map
      Prod.snd ↔ ¬ DissociatedThird f := by
  decide +kernel

end FaustLampitelli2026
