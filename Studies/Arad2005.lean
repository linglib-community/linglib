module

public import Studies.McCarthy1981
public import Linglib.Morphology.Realization
public import Linglib.Morphology.DistributedMorphology.Locality
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Fragments.Hebrew.ConsonantalRoots
public import Linglib.Data.Forms.Arad2005
public import Mathlib.Data.List.Destutter
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Fintype.Option

/-!
# Arad (2005): Roots and Patterns: Hebrew Morpho-Syntax

Arad builds every Hebrew verb from a consonantal root under v and Voice. The binyan under v is
a CV template with vowel slots but no vowels, the root associates with it as McCarthy proposed,
and Voice fills the vowel slots by a spell-out rule whose context is the binyan; a nominal
pattern (mišqal) carries its own vowels. A root is interpreted at the first category head merged
with it, so a verb formed from a noun does not see the root and is a stem modification of the
noun instead. Conjugation classes pair the binyanim of an alternation, and two tendencies,
against conjugating a binyan with itself and against mixing geminate and non-geminate templates,
single out the natural pairs.

## Main statements

* `words_derived_seg`: over the fragment's roots and segments, every root-derived word of the
  data is derived but five verbs whose guttural, metathesis or geminate-root phonology is not
  modelled.
* `spirantize_before_degeminate`: the opposite order would give \*sifer, \*qivel, \*hitraxex.
* `denominals`: every noun-derived verb is a stem modification of its base, except the
  {o, e} verbs of (41a, b), and none is the verb its base's root derives.
* `conjugations_natural`: conjugation classes 1–4 are the natural pairs of (57), and 5 and 6
  each break one tendency.

## Implementation notes

* Root-to-template association follows McCarthy, as p. 43 says it does. CVCCVC and
  hitCVCCVC undergo McCarthy's Erasure, like Arabic II and V. The book gives the extra slot
  (p. 28) but no association apparatus of its own (Ch. 6, fn. 1).
* The book states no stem-modification rule (p. 50). `IsStemModification` checks the
  properties it names instead: the prefix is carried, the base's consonants occur in order, and
  the vowels are Voice's (Bat El's melodic overwriting, p. 47). A `+` in the base marks the
  suffixes (32) prints as outside the stem.
* The derivations run over the book's transcription, and a relabeling lifts them to the
  fragment's segments. There the alternating stops are archisegments that spirantization
  realizes by continuancy, as the one stop or fricative of the inventory that refines them.
* The data's patterns 1–7 are the numbers of (3). Ch. 7 prints CaCaC, hiCCiC, CiCCeC and
  hitCaCCeC, which p. 43 equates with them.
* The prose of p. 226 says "insertable below v" where its grid says "above". The grid is read.

## TODO

* Guttural lowering (*hexšiv*, *heʔedim*), t–sibilant metathesis (*histager*) and the
  biliteral allomorphy of √mss (*namas*, *hemes*, fn. 33).
* The {o, e} vocalism of (41a, b), which (25) does not list.
* (34)–(35), failed stem modification and recognizability, whose phonology the book leaves open.
* Conditions on insertion (16), the diacritic spell-out rules of §6.2.6.4, and the arguments
  against Doron's and Aronoff's analyses of the binyanim (Ch. 5).

## References

* [arad-2005]
* [mccarthy-1981]
* [bat-el-1994]
* [doron-2003]
* [aronoff-1994]
-/

@[expose] public section

namespace Arad2005

open Morphology DistributedMorphology

variable {α β : Type*}

/-! ### The binyanim (24b) -/

/-- A binyan is one of the five templates of (24b). Patterns 4 and 6 of (3) are the passive
vocalisms of CVCCVC and hVCCVC (25). -/
inductive Binyan where
  | cvcvc
  | nvccvc
  | cvccvc
  | hvccvc
  | hitcvccvc
  deriving DecidableEq, Repr, Fintype

/-- `Prefixes α` holds the prefixal segments, the *n-* of nVCCVC, *h-* of hVCCVC, *h-i-t* of
hitCVCCVC, and *m-*, *t-* of the mišqalim (24a). -/
structure Prefixes (α : Type*) where
  /-- `n` is the *n* of nVCCVC. -/
  n : α
  /-- `h` is the *h* of hVCCVC and hitCVCCVC. -/
  h : α
  /-- `i` is the *i* of hitCVCCVC. -/
  i : α
  /-- `t` is the *t* of hitCVCCVC and taCCiC. -/
  t : α
  /-- `m` is the *m* of the mišqalim. -/
  m : α

/-- `px.map f` relabels the prefixes by `f`. -/
def Prefixes.map (f : α → β) (px : Prefixes α) : Prefixes β :=
  ⟨f px.n, f px.h, f px.i, f px.t, f px.m⟩

/-- `b.template` is the CV template of the binyan `b`. -/
def Binyan.template : Binyan → CVTemplate
  | .cvcvc => McCarthy1981.cvcvc
  | .nvccvc | .cvccvc | .hvccvc => McCarthy1981.cvccvc
  | .hitcvccvc => ⟨[.C, .V, .C, .C, .V, .C, .C, .V, .C]⟩

/-- `b.prefix px` is the prefix of the binyan `b`. -/
def Binyan.prefix (px : Prefixes α) : Binyan → List α
  | .cvcvc | .cvccvc => []
  | .nvccvc => [px.n]
  | .hvccvc => [px.h]
  | .hitcvccvc => [px.h, px.i, px.t]

/-- The binyanim that undergo McCarthy's Erasure are CVCCVC and hitCVCCVC, the Hebrew counterparts
of Arabic II and V, whose extra slot holds the geminate (p. 28). -/
def Binyan.erasure : Binyan → Bool
  | .cvccvc | .hitcvccvc => true
  | _ => false

/-- `place pre t r` puts the prefix `pre` on the leftmost slots of `t`, with the root `r` not yet
associated. -/
def place (pre : List α) (t : CVTemplate) (r : ConsonantalRoot α) : TemplateMatch α where
  root := r
  affix := pre
  template := t
  associations := (List.range pre.length).map fun k ↦ ⟨.affix, k, k⟩

/-- The consonantism of a binyan places its prefix, associates the root by the conventions and,
under Erasure, applies the conventions again ([mccarthy-1981]). -/
def consonantism (px : Prefixes α) (b : Binyan) (r : ConsonantalRoot α) : TemplateMatch α :=
  let m := (place (b.prefix px) b.template r).associate .root
  if b.erasure then
    (((McCarthy1981.erasure m).associateOneToOne .root).associateRemaining .root).spread .root
  else m

/-! ### Voice (25) -/

/-- `Voice` is the value of the Voice head, active or passive. -/
inductive Voice where
  | active
  | passive
  deriving DecidableEq, Repr, Fintype

/-- `Vowel` lists the vowels of the transcription. -/
inductive Vowel where
  | a
  | e
  | i
  | o
  | u
  deriving DecidableEq, Repr

/-- A feature of Voice's vocabulary is a value of Voice or the binyan inserted under v. -/
inductive Feature where
  | voice (v : Voice)
  | binyan (b : Binyan)
  deriving DecidableEq, Repr

/-- An exponent of Voice is a vocalism for the binyan's vowel slots, or a binyan with its own vowels
in place of the one under v, as niCCaC is the passive of CaCaC (fn. 13). -/
inductive Exponent where
  | vocalism (vs : List Vowel)
  | rewrite (b : Binyan) (vs : List Vowel)
  deriving DecidableEq, Repr

/-- `voiceSpellout` lists the Voice spell-out (25), each item in the context of a binyan inserted
under v. -/
def voiceSpellout : List (VocabularyItem Feature Exponent) :=
  [⟨{(0, .voice .active), (-1, .binyan .cvcvc)}, .vocalism [.a, .a]⟩,
    ⟨{(0, .voice .active), (-1, .binyan .nvccvc)}, .vocalism [.i, .a]⟩,
    ⟨{(0, .voice .active), (-1, .binyan .cvccvc)}, .vocalism [.i, .e]⟩,
    ⟨{(0, .voice .active), (-1, .binyan .hvccvc)}, .vocalism [.i, .i]⟩,
    ⟨{(0, .voice .active), (-1, .binyan .hitcvccvc)}, .vocalism [.a, .e]⟩,
    ⟨{(0, .voice .passive), (-1, .binyan .cvccvc)}, .vocalism [.u, .a]⟩,
    ⟨{(0, .voice .passive), (-1, .binyan .hvccvc)}, .vocalism [.u, .a]⟩,
    ⟨{(0, .voice .passive), (-1, .binyan .cvcvc)}, .rewrite .nvccvc [.i, .a]⟩]

/-- The Voice node, once v has been spelled out, carries its value and has the binyan as its inner
neighbor. -/
def voiceNode (b : Binyan) (v : Voice) : Neighborhood (List Feature) :=
  ⟨[.voice v], [[.binyan b]], []⟩

/-- `realizeVoice b v` is the binyan and the vowels of a verb, Voice being spelled out in the
context of `b`. -/
def realizeVoice (b : Binyan) (v : Voice) : Option (Binyan × List Vowel) :=
  (subsetPrinciple voiceSpellout (voiceNode b v)).map fun
    | .vocalism vs => (b, vs)
    | .rewrite b' vs => (b', vs)

/-- The binyanim (11) marks [−tr.]. -/
def Binyan.Intransitive (b : Binyan) : Prop := b = .nvccvc ∨ b = .hitcvccvc

instance : DecidablePred Binyan.Intransitive := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Voice is spelled out in every binyan in the active, and in the passive exactly in the
binyanim (11) does not mark [−tr.]; the binyan that replaces CVCVC in the passive is one (11)
marks. -/
theorem realizeVoice_isSome :
    (∀ b v, (realizeVoice b v).isSome ↔ v = .active ∨ ¬b.Intransitive) ∧
      ∀ x ∈ realizeVoice .cvcvc .passive, x.1.Intransitive := by
  decide

/-! ### The stem -/

/-- `vocalize` associates a vocalism with the consonantism by the conventions. -/
def vocalize (px : Prefixes α) (v : Vowel → α) (b : Binyan) (vs : List Vowel)
    (r : ConsonantalRoot α) : TemplateMatch α :=
  ({ consonantism px b r with vocalism := vs.map v }).associate .vocalism

/-- The stem of a root-derived verb has the binyan under v, Voice's vowels in its context and the
root associated with it (p. 43). It is `none` where Voice has no exponent. -/
def stem (px : Prefixes α) (v : Vowel → α) (b : Binyan) (voice : Voice)
    (r : ConsonantalRoot α) : Option (TemplateMatch α) :=
  (realizeVoice b voice).map fun x ↦ vocalize px v x.1 x.2 r

/-! ### Spirantization and degemination (pp. 28–29) -/

/-- `sameElement a b` says that two lines come from one melodic element. -/
def sameElement (a b : Association) : Bool :=
  a.source == b.source && a.melodyIndex == b.melodyIndex

/-- `linked m` lists each slot with its first line and that line's segment. -/
def linked (m : TemplateMatch α) : List (ℕ × Association × α) :=
  (List.range m.template.length).filterMap fun i ↦
    (m.associations.find? (·.slotIndex == i)).bind fun a ↦ (m.segmentAt a).map (i, a, ·)

/-- `spirantize f m` realizes each segment by `f`, given whether it follows a V-slot and is not
the first slot of a geminate, whose element also occupies the next slot. -/
def spirantize (f : Bool → α → α) (m : TemplateMatch α) : List (ℕ × Association × α) :=
  let l := linked m
  l.zipIdx.map fun ((i, a, x), j) ↦
    let postVocalic := 0 < i && m.template.slots[i - 1]? == some .V
    let geminate := match l[j + 1]? with
      | some (_, b, _) => sameElement a b
      | none => false
    (i, a, f (postVocalic && !geminate) x)

/-- Since Modern Hebrew has no geminates (p. 28), slots linked to one element surface once. -/
def degeminate (l : List (ℕ × Association × α)) : List α :=
  (l.destutter fun p q ↦ !sameElement p.2.1 q.2.1).map (·.2.2)

/-- `surface f m` is the stem spirantized by `f` and degeminated. -/
def surface (f : Bool → α → α) (m : TemplateMatch α) : List α := degeminate (spirantize f m)

/-- `verb` is the surface of the stem of a root-derived verb. -/
def verb (px : Prefixes α) (v : Vowel → α) (f : Bool → α → α) (b : Binyan) (voice : Voice)
    (r : ConsonantalRoot α) : Option (List α) :=
  (stem px v b voice r).map (surface f)

/-- `surfaceDegeminatedFirst` applies the rules in the order the book rules out, degemination before
the spirantization of whatever follows a vowel. -/
def surfaceDegeminatedFirst (isV : α → Bool) (f : Bool → α → α) (m : TemplateMatch α) : List α :=
  let w := degeminate (linked m)
  w.zipIdx.map fun (x, j) ↦ f (0 < j && (w[j - 1]?.map isV).getD false) x

/-! ### The mišqalim (24a) -/

/-- `Mishqal` lists the nominal patterns of (24a) and those Ch. 7 prints. -/
inductive Mishqal where
  | miCCaC
  | miCCoC
  | maCCeC
  | taCCiC
  | CCaC
  | CaCiC
  | CeCeC
  | CaCeC
  | CuCaC
  deriving DecidableEq, Repr, Fintype

/-- `q.template` is the CV template of the mišqal `q`. -/
def Mishqal.template : Mishqal → CVTemplate
  | .miCCaC | .miCCoC | .maCCeC | .taCCiC => McCarthy1981.cvccvc
  | .CCaC => ⟨[.C, .C, .V, .C]⟩
  | .CaCiC | .CeCeC | .CaCeC | .CuCaC => McCarthy1981.cvcvc

/-- `q.prefix px` is the prefix of the mišqal `q`. -/
def Mishqal.prefix (px : Prefixes α) : Mishqal → List α
  | .miCCaC | .miCCoC | .maCCeC => [px.m]
  | .taCCiC => [px.t]
  | _ => []

/-- `q.vowels` are the mišqal's own vowels. -/
def Mishqal.vowels : Mishqal → List Vowel
  | .miCCaC => [.i, .a]
  | .miCCoC => [.i, .o]
  | .maCCeC => [.a, .e]
  | .taCCiC => [.a, .i]
  | .CCaC => [.a]
  | .CaCiC => [.a, .i]
  | .CeCeC => [.e, .e]
  | .CaCeC => [.a, .e]
  | .CuCaC => [.u, .a]

/-- The stem of a root-derived noun associates the root and the mišqal's own vowels with its
template. -/
def nounStem (px : Prefixes α) (v : Vowel → α) (q : Mishqal) (r : ConsonantalRoot α) :
    TemplateMatch α :=
  ({ (place (q.prefix px) q.template r).associate .root with
    vocalism := q.vowels.map v }).associate .vocalism

/-! ### Relabeling -/

theorem place_map (f : α → β) (pre : List α) (t : CVTemplate) (r : ConsonantalRoot α) :
    place (pre.map f) t (r.map f) = (place pre t r).map f := by
  simp [place, TemplateMatch.map, ConsonantalRoot.map]

theorem prefix_map (f : α → β) (px : Prefixes α) (b : Binyan) :
    b.prefix (px.map f) = (b.prefix px).map f := by
  cases b <;> rfl

theorem consonantism_map (f : α → β) (px : Prefixes α) (b : Binyan) (r : ConsonantalRoot α) :
    consonantism (px.map f) b (r.map f) = (consonantism px b r).map f := by
  simp only [consonantism, prefix_map, place_map, TemplateMatch.associate_map]
  split <;> simp only [McCarthy1981.erasure_map, TemplateMatch.associateOneToOne_map,
    TemplateMatch.associateRemaining_map, TemplateMatch.spread_map]

theorem vocalize_map (f : α → β) (px : Prefixes α) (v : Vowel → α) (b : Binyan)
    (vs : List Vowel) (r : ConsonantalRoot α) :
    vocalize (px.map f) (f ∘ v) b vs (r.map f) = (vocalize px v b vs r).map f := by
  have h : ({ consonantism (px.map f) b (r.map f) with vocalism := vs.map (f ∘ v) } :
      TemplateMatch β) = ({ consonantism px b r with vocalism := vs.map v }).map f := by
    rw [consonantism_map, ← List.map_map]
    rfl
  unfold vocalize
  rw [h, TemplateMatch.associate_map]

theorem stem_map (f : α → β) (px : Prefixes α) (v : Vowel → α) (b : Binyan) (voice : Voice)
    (r : ConsonantalRoot α) :
    stem (px.map f) (f ∘ v) b voice (r.map f) = (stem px v b voice r).map (·.map f) := by
  simp only [stem, Option.map_map]
  congr 1
  funext x
  exact vocalize_map f px v x.1 x.2 r

theorem nounStem_map (f : α → β) (px : Prefixes α) (v : Vowel → α) (q : Mishqal)
    (r : ConsonantalRoot α) :
    nounStem (px.map f) (f ∘ v) q (r.map f) = (nounStem px v q r).map f := by
  have hq : q.prefix (px.map f) = (q.prefix px).map f := by cases q <;> rfl
  have h : ({ (place (q.prefix (px.map f)) q.template (r.map f)).associate .root with
      vocalism := q.vowels.map (f ∘ v) } : TemplateMatch β) =
      ({ (place (q.prefix px) q.template r).associate .root with
        vocalism := q.vowels.map v }).map f := by
    rw [hq, place_map, TemplateMatch.associate_map, ← List.map_map]
    rfl
  unfold nounStem
  rw [h, TemplateMatch.associate_map]

theorem linked_map (f : α → β) (m : TemplateMatch α) :
    linked (m.map f) = (linked m).map fun (i, a, x) ↦ (i, a, f x) := by
  simp only [linked, TemplateMatch.template_map, TemplateMatch.associations_map,
    List.map_filterMap, TemplateMatch.segmentAt_map]
  congr 1
  funext i
  cases m.associations.find? (·.slotIndex == i) with
  | none => rfl
  | some a => cases h : m.segmentAt a <;> simp [h]

/-- Spirantization commutes with relabeling the underlying segments by `g` and the surface
segments by `h`, where the two realizations agree. -/
theorem spirantize_map (g h : α → β) (f : Bool → α → α) (f' : Bool → β → β)
    (hf : ∀ b x, f' b (g x) = h (f b x)) (m : TemplateMatch α) :
    spirantize f' (m.map g) = (spirantize f m).map fun (i, a, x) ↦ (i, a, h x) := by
  simp only [spirantize, linked_map, TemplateMatch.template_map, List.zipIdx_map, List.map_map,
    List.getElem?_map]
  refine List.map_congr_left fun ⟨⟨i, a, x⟩, j⟩ _ ↦ ?_
  rcases hj : (linked m)[j + 1]? with _ | ⟨_, b, _⟩ <;> simp [hj, hf]

theorem surface_map (g h : α → β) (f : Bool → α → α) (f' : Bool → β → β)
    (hf : ∀ b x, f' b (g x) = h (f b x)) (m : TemplateMatch α) :
    surface f' (m.map g) = (surface f m).map h := by
  simp only [surface, degeminate, spirantize_map g h f f' hf]
  rw [← List.map_destutter (f := fun x : ℕ × Association × α ↦ (x.1, x.2.1, h x.2.2))
    fun _ _ _ _ ↦ Iff.rfl, List.map_map, List.map_map]
  rfl

/-- A verb over relabeled underlying segments is the relabeled surface verb. -/
theorem verb_map (g h : α → β) (f : Bool → α → α) (f' : Bool → β → β)
    (hf : ∀ b x, f' b (g x) = h (f b x)) (px : Prefixes α) (v : Vowel → α) (b : Binyan)
    (voice : Voice) (r : ConsonantalRoot α) :
    verb (px.map g) (g ∘ v) f' b voice (r.map g) = (verb px v f b voice r).map (·.map h) := by
  simp only [verb, stem_map, Option.map_map]
  congr 1
  funext m
  exact surface_map g h f f' hf m

/-! ### The geminate slot and the vowel slots -/

/-- `numeralPx` numbers the prefixes for symbolic statements. -/
def numeralPx : Prefixes ℕ := ⟨100, 101, 102, 103, 104⟩

/-- `numeralVowel` numbers the vowels. -/
def numeralVowel : Vowel → ℕ
  | .a => 200 | .e => 201 | .i => 202 | .o => 203 | .u => 204

/-- `label` sends the numerals back to radicals, prefixes and vowels. -/
def label (px : Prefixes α) (v : Vowel → α) (rad : List α) (d : α) : ℕ → α
  | 100 => px.n | 101 => px.h | 102 => px.i | 103 => px.t | 104 => px.m
  | 200 => v .a | 201 => v .e | 202 => v .i | 203 => v .o | 204 => v .u
  | k => rad.getD k d

theorem numeralPx_map (px : Prefixes α) (v : Vowel → α) (rad : List α) (d : α) :
    numeralPx.map (label px v rad d) = px := rfl

theorem label_comp_numeralVowel (px : Prefixes α) (v : Vowel → α) (rad : List α) (d : α) :
    label px v rad d ∘ numeralVowel = v := by
  funext x
  cases x <;> rfl

/-- In CVCCVC a triliteral root doubles its middle radical, one element on two slots, and a
quadriliteral root fills the extra slot, as in *tirgem* (p. 28). -/
theorem consonantism_cvccvc (px : Prefixes α) (w x y z : α) :
    (consonantism px .cvccvc ⟨[x, y, z]⟩).spellout = [x, y, y, z] ∧
      (consonantism px .cvccvc ⟨[w, x, y, z]⟩).spellout = [w, x, y, z] := by
  have h₃ : consonantism px .cvccvc ⟨[x, y, z]⟩ =
      (consonantism numeralPx .cvccvc ⟨[0, 1, 2]⟩).map (label px (fun _ ↦ x) [x, y, z] x) := by
    rw [← consonantism_map]
    rfl
  have h₄ : consonantism px .cvccvc ⟨[w, x, y, z]⟩ =
      (consonantism numeralPx .cvccvc ⟨[0, 1, 2, 3]⟩).map
        (label px (fun _ ↦ x) [w, x, y, z] x) := by
    rw [← consonantism_map]
    rfl
  rw [h₃, h₄, TemplateMatch.spellout_map, TemplateMatch.spellout_map]
  have : (consonantism numeralPx .cvccvc ⟨[0, 1, 2]⟩).spellout = [0, 1, 1, 2] ∧
      (consonantism numeralPx .cvccvc ⟨[0, 1, 2, 3]⟩).spellout = [0, 1, 2, 3] := by decide
  rw [this.1, this.2]
  exact ⟨rfl, rfl⟩

/-- A binyan has two vowel slots that the root leaves empty for Voice, while a mišqal fills its own
(24), which is the noun–verb asymmetry of §2.5. -/
theorem freeBearers_vocalism (px : Prefixes α) (v : Vowel → α) (x y z : α) :
    (∀ b : Binyan, ((consonantism px b ⟨[x, y, z]⟩).freeBearers .vocalism).length = 2) ∧
      ∀ q : Mishqal, (nounStem px v q ⟨[x, y, z]⟩).freeBearers .vocalism = [] := by
  have hb : ∀ b, consonantism px b ⟨[x, y, z]⟩ =
      (consonantism numeralPx b ⟨[0, 1, 2]⟩).map (label px v [x, y, z] x) := fun b ↦ by
    rw [← consonantism_map]
    rfl
  have hq : ∀ q, nounStem px v q ⟨[x, y, z]⟩ =
      (nounStem numeralPx numeralVowel q ⟨[0, 1, 2]⟩).map (label px v [x, y, z] x) := fun q ↦ by
    rw [← nounStem_map, numeralPx_map, label_comp_numeralVowel]
    rfl
  simp only [hb, hq, TemplateMatch.freeBearers_map]
  decide

/-! ### The data -/

/-- `transcribedPx` gives the prefixes in the book's transcription. -/
def transcribedPx : Prefixes String := ⟨"n", "h", "i", "t", "m"⟩

/-- `v.transcription` is the vowel `v` in the book's transcription. -/
def Vowel.transcription : Vowel → String
  | .a => "a" | .e => "e" | .i => "i" | .o => "o" | .u => "u"

/-- `isVowel s` says that the transcribed segment `s` is a vowel. -/
def isVowel (s : String) : Bool := s ∈ ["a", "e", "i", "o", "u"]

/-- `fricative post x` is the radical `x` after a vowel (`post`) or elsewhere, the stops *p*, *b*,
*k* spirantizing to *f*, *v*, *x* after a vowel (p. 29). -/
def fricative : Bool → String → String
  | true, "p" => "f"
  | true, "b" => "v"
  | true, "k" => "x"
  | _, s => s

/-- `binyan?` reads a pattern number of (3) as a binyan and a voice, 4 and 6 being the passives of 3
and 5. -/
def binyan? : String → Option (Binyan × Voice)
  | "1" => some (.cvcvc, .active)
  | "2" => some (.nvccvc, .active)
  | "3" => some (.cvccvc, .active)
  | "4" => some (.cvccvc, .passive)
  | "5" => some (.hvccvc, .active)
  | "6" => some (.hvccvc, .passive)
  | "7" => some (.hitcvccvc, .active)
  | _ => none

/-- `mishqal?` reads a printed pattern as a mišqal. -/
def mishqal? : String → Option Mishqal
  | "miCCaC" => some .miCCaC
  | "miCCoC" => some .miCCoC
  | "maCCeC" => some .maCCeC
  | "taCCiC" => some .taCCiC
  | "CCaC" => some .CCaC
  | "CaCiC" => some .CaCiC
  | "CeCeC" => some .CeCeC
  | "CaCeC" => some .CaCeC
  | "CuCaC" => some .CuCaC
  | _ => none

/-- `root? label` is the root of a label of the data in the book's transcription, in which *q*
is the /k/ of ק and *b*, *k*, *p* spirantize. -/
def root? : String → Option (ConsonantalRoot String)
  | "lmd" => some ⟨["l", "m", "d"]⟩
  | "spr" => some ⟨["s", "p", "r"]⟩
  | "qlt" => some ⟨["q", "l", "t"]⟩
  | "pll" => some ⟨["p", "l", "l"]⟩
  | "npc" => some ⟨["n", "p", "c"]⟩
  | "xlq" => some ⟨["x", "l", "q"]⟩
  | "str" => some ⟨["s", "t", "r"]⟩
  | "pqd" => some ⟨["p", "q", "d"]⟩
  | "šmr" => some ⟨["š", "m", "r"]⟩
  | "trgm" => some ⟨["t", "r", "g", "m"]⟩
  | "qbl" => some ⟨["q", "b", "l"]⟩
  | "rkk" => some ⟨["r", "k", "k"]⟩
  | "šmn" => some ⟨["š", "m", "n"]⟩
  | "xšb" => some ⟨["x", "š", "b"]⟩
  | "sgr" => some ⟨["s", "g", "r"]⟩
  | "ptx" => some ⟨["p", "t", "x"]⟩
  | "qpʔ" => some ⟨["q", "p", "ʔ"]⟩
  | "mss" => some ⟨["m", "s", "s"]⟩
  | "xmm" => some ⟨["x", "m", "m"]⟩
  | "bhr" => some ⟨["b", "h", "r"]⟩
  | "ʔdm" => some ⟨["ʔ", "d", "m"]⟩
  | _ => none

/-- `verbCell?` reads the binyan, voice and root of a root-derived verb of the book's
analysis. -/
def verbCell? (a : Forms.Analysis) : Option (Binyan × Voice × ConsonantalRoot String) :=
  (a.binyan.bind binyan?).bind fun x ↦ (a.root.bind root?).map fun r ↦ (x.1, x.2, r)

/-- `nounCell?` reads the mišqal and root of a root-derived noun of the book's analysis. -/
def nounCell? (a : Forms.Analysis) : Option (Mishqal × ConsonantalRoot String) :=
  (a.pattern.bind mishqal?).bind fun q ↦ (a.root.bind root?).map (q, ·)

/-- Every verb with a root has its cell. -/
theorem isSome_verbCell? : ∀ a ∈ Forms.analyses, a.root.isSome →
    a.form.lexeme.pos = ↑UD.UPOS.VERB → (verbCell? a).isSome := by
  decide +kernel

/-- The derivation produces every root-derived verb of Ch. 2 and Ch. 7 except two. *hexšiv* lowers
*i* next to the guttural, and *histager* metathesizes *t* and the sibilant. -/
theorem verbs_derived :
    (Forms.analyses.filter fun a ↦ a.conjugation = none ∧ ∃ x ∈ verbCell? a,
      verb transcribedPx Vowel.transcription fricative x.1 x.2.1 x.2.2 ≠ some a.form.segments).map
        (·.form.form) = ["hexšiv", "histager"] := by
  decide +kernel

/-- The derivation produces every noun of the data in a mišqal of (24a) or of Ch. 7, with the
mišqal's own vowels. -/
theorem nouns_derived : ∀ a ∈ Forms.analyses, ∀ x ∈ nounCell? a,
    surface fricative (nounStem transcribedPx Vowel.transcription x.1 x.2) = a.form.segments := by
  decide +kernel

/-- The passive of *lamad* is the binyan nVCCVC, *nilmad* (25), (3). -/
theorem passive_lamad :
    verb transcribedPx Vowel.transcription fricative .cvcvc .passive ⟨["l", "m", "d"]⟩ =
      some ["n", "i", "l", "m", "a", "d"] := by
  decide +kernel

/-- Spirantization applies before degemination. In the opposite order the geminate would spirantize,
giving \*sifer, \*qivel, \*hitraxex for *siper*, *qibel*, *hitrakex* (p. 29). -/
theorem spirantize_before_degeminate :
    [(Binyan.cvccvc, ⟨["s", "p", "r"]⟩), (.cvccvc, ⟨["q", "b", "l"]⟩),
        (.hitcvccvc, ⟨["r", "k", "k"]⟩)].map
        (fun (b, r) ↦ (stem transcribedPx Vowel.transcription b .active r).map fun m ↦
          (surface fricative m, surfaceDegeminatedFirst isVowel fricative m)) =
      [some (["s", "i", "p", "e", "r"], ["s", "i", "f", "e", "r"]),
        some (["q", "i", "b", "e", "l"], ["q", "i", "v", "e", "l"]),
        some (["h", "i", "t", "r", "a", "k", "e", "x"],
          ["h", "i", "t", "r", "a", "x", "e", "x"])] := by
  decide +kernel

/-! ### Noun-derived verbs (§2.6, §7.5) -/

/-- `consonants isV w` keeps the consonants of `w`. -/
def consonants (isV : α → Bool) (w : List α) : List α := w.filter (!isV ·)

/-- `vowels isV w` keeps the vowels of `w`. -/
def vowels (isV : α → Bool) (w : List α) : List α := w.filter isV

/-- `clusters isV w` lists the maximal consonant clusters of `w`. -/
def clusters (isV : α → Bool) (w : List α) : List (List α) :=
  (w.splitBy fun x y ↦ !isV x && !isV y).filter fun c ↦ c.all (!isV ·)

/-- A verb is a stem modification of a base with melodic overwriting ([bat-el-1994], p. 47) when, in
the binyan Voice spells out, it is the binyan's prefix followed by a word whose consonants include
the base's in order and whose vowels are Voice's. -/
def IsStemModification [DecidableEq α] (isV : α → Bool) (px : Prefixes α) (v : Vowel → α)
    (b : Binyan) (voice : Voice) (base w : List α) : Prop :=
  ∃ x ∈ realizeVoice b voice, x.1.prefix px <+: w ∧
    (consonants isV base).Sublist (consonants isV (w.drop (x.1.prefix px).length)) ∧
      vowels isV (w.drop (x.1.prefix px).length) = x.2.map v

instance [DecidableEq α] (isV : α → Bool) (px : Prefixes α) (v : Vowel → α) (b : Binyan)
    (voice : Voice) (base w : List α) :
    Decidable (IsStemModification isV px v b voice base w) :=
  inferInstanceAs (Decidable (∃ x ∈ _, _))

/-- A verb keeps the clusters of its base (39) when every consonant cluster of the base is
contiguous in it. -/
def KeepsClusters [DecidableEq α] (isV : α → Bool) (base w : List α) : Prop :=
  ∀ c ∈ clusters isV base, c <:+: w

instance [DecidableEq α] (isV : α → Bool) (base w : List α) :
    Decidable (KeepsClusters isV base w) := inferInstanceAs (Decidable (∀ c ∈ _, _))

/-- `baseStem f` is the stem of a base, its segments before a boundary *+*. (32) prints the suffixes
after it outside the stem. -/
def baseStem (f : Data.Forms.Form Forms.Cell) : List String := f.segments.takeWhile (· ≠ "+")

/-- `candidates a` lists the binyan and voice of a verb where the book prints them, and every
active binyan where it does not. -/
def candidates (a : Forms.Analysis) : List (Binyan × Voice) :=
  match a.binyan.bind binyan? with
  | some x => [x]
  | none => [Binyan.cvcvc, .nvccvc, .cvccvc, .hvccvc, .hitcvccvc].map (·, .active)

/-- Every noun-derived verb of the data is a stem modification of its base except *xoqeq* and
*qoded* (41a, b), whose {o, e} (25) does not list. None is the verb the root of its base derives in
its binyan, so *misger* is not *siger*, *musgar* not *sugar* and *mixšev* not *xišev*. -/
theorem denominals :
    ((Forms.analysisRelations.filter fun rel : Data.Forms.FormRelation Forms.Analysis ↦
        ¬∃ x ∈ candidates rel.target,
        IsStemModification isVowel transcribedPx Vowel.transcription x.1 x.2
          (baseStem rel.form.form) rel.target.form.segments).map (·.target.form.form) =
        ["xoqeq", "qoded"]) ∧
      ∀ rel ∈ Forms.analysisRelations, ∀ r ∈ rel.form.root.bind root?,
        ∀ x ∈ candidates rel.target, verb transcribedPx Vowel.transcription fricative x.1 x.2 r ≠
          some rel.target.form.segments := by
  decide +kernel

/-- Without its stem boundary the suffix *-et* of *misgeret* would have to be kept, which the
book leaves unexplained (fn. 2, p. 246); a verb keeping a vowel of its base, \*tilefon, is not
a stem modification. -/
theorem not_isStemModification :
    ¬IsStemModification isVowel transcribedPx Vowel.transcription .cvccvc .active
      ["m", "i", "s", "g", "e", "r", "e", "t"] ["m", "i", "s", "g", "e", "r"] ∧
    ¬IsStemModification isVowel transcribedPx Vowel.transcription .cvccvc .active
      ["t", "e", "l", "e", "f", "o", "n"] ["t", "i", "l", "e", "f", "o", "n"] := by
  decide +kernel

/-- The borrowed verbs of (39) keep the clusters of their bases, unlike \*tirnsfer, \*stirptez,
\*snixren, which Hebrew phonology would allow (p. 266); *xarap* breaks the cluster of *xrop*
(29c), so cluster transfer is not a condition of stem modification. -/
theorem keepsClusters :
    KeepsClusters isVowel ["t", "r", "a", "n", "s", "f", "e", "r"]
        ["t", "r", "i", "n", "s", "f", "e", "r"] ∧
      KeepsClusters isVowel ["s", "t", "r", "e", "p", "t", "i", "z"]
        ["s", "t", "r", "i", "p", "t", "e", "z"] ∧
      KeepsClusters isVowel ["s", "i", "n", "x", "r", "o", "n", "i"]
        ["s", "i", "n", "x", "r", "e", "n"] ∧
      ¬KeepsClusters isVowel ["t", "r", "a", "n", "s", "f", "e", "r"]
        ["t", "i", "r", "n", "s", "f", "e", "r"] ∧
      ¬KeepsClusters isVowel ["s", "t", "r", "e", "p", "t", "i", "z"]
        ["s", "t", "i", "r", "p", "t", "e", "z"] ∧
      ¬KeepsClusters isVowel ["s", "i", "n", "x", "r", "o", "n", "i"]
        ["s", "n", "i", "x", "r", "e", "n"] ∧
      ¬KeepsClusters isVowel ["x", "r", "o", "p"] ["x", "a", "r", "a", "p"] := by
  decide +kernel

/-! ### The locality of root interpretation (Ch. 7 (8)) -/

/-- `Head` lists the heads above a root, the category heads n, a, v and Voice. -/
inductive Head where
  | n
  | a
  | v
  | voice
  deriving DecidableEq, Repr, Fintype

/-- `cyclic` picks out the category-assigning heads, at which a root is interpreted (8). -/
def cyclic (h : Head) : Prop := h = .n ∨ h = .a ∨ h = .v

instance : DecidablePred cyclic := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- `verbSpine base` is the structure of a verb, (26) and (7b), with v and Voice above the root, or
above the category head of the word it is formed from. -/
def verbSpine (base : Option Head) : ComplexHead Root Head := ⟨⟨0⟩, base.toList ++ [.v, .voice]⟩

/-- By (8), the v of a verb is local to the root exactly when no category head intervenes, so only a
root-derived verb's v sees the root and a noun-derived verb's sees the noun. -/
theorem verbSpine_rootLocal : ∀ base : Option Head, (∀ c ∈ base, c = .n ∨ c = .a) →
    ∀ i : Fin (verbSpine base).heads.length, (verbSpine base).heads[i] = .v →
      ((verbSpine base).RootLocal cyclic i ↔ base = none) := by
  decide

/-! ### Conjugation classes (§6.2.6) -/

/-- A binyan geminates when a triliteral root's middle radical is one element on two of its slots.
-/
def Binyan.Geminated (b : Binyan) : Prop :=
  2 ≤ McCarthy1981.linkCount (consonantism numeralPx b ⟨[0, 1, 2]⟩) .root 1

instance : DecidablePred Binyan.Geminated := fun _ ↦ inferInstanceAs (Decidable (_ ≤ _))

/-- Two binyanim form a natural pair when they obey the two tendencies of pp. 225–226, against
conjugating a binyan with itself and against mixing geminate and non-geminate binyanim. -/
def Natural (b b' : Binyan) : Prop := b ≠ b' ∧ (b.Geminated ↔ b'.Geminated)

instance (b b' : Binyan) : Decidable (Natural b b') := inferInstanceAs (Decidable (_ ∧ _))

/-- `natural57` lists the four natural types of binyan pairs (57). -/
def natural57 : List (Sym2 Binyan) :=
  [s(.cvcvc, .nvccvc), s(.cvcvc, .hvccvc), s(.nvccvc, .hvccvc), s(.cvccvc, .hitcvccvc)]

/-- The tendencies derive (57). -/
theorem natural_iff : ∀ b b', Natural b b' ↔ s(b, b') ∈ natural57 := by
  decide

/-- `conjugations` reads each conjugation of (47)–(52), with the binyan of its causative and of its
other alternant, off the verbs of the data. -/
def conjugations : List (String × Binyan × Binyan) :=
  let alts := Forms.analyses.filterMap fun a ↦ do
    pure (← a.conjugation, a.alternant == some "causative", (← a.binyan.bind binyan?).1)
  (alts.filter (·.2.1)).flatMap fun (c, _, b) ↦
    (alts.filter fun a ↦ a.1 = c ∧ !a.2.1).map fun (_, _, b') ↦ (c, b, b')

/-- The derivation produces the verbs of the conjugation classes except *namas* and *hemes*, the
biliteral allomorphy of √mss (fn. 33), and *heʔedim*, lowered next to the guttural. -/
theorem conjugation_verbs_derived :
    (Forms.analyses.filter fun a ↦ a.conjugation ≠ none ∧ ∃ x ∈ verbCell? a,
      verb transcribedPx Vowel.transcription fricative x.1 x.2.1 x.2.2 ≠ some a.form.segments).map
        (·.form.form) = ["namas", "hemes", "heʔedim", "heʔedim"] := by
  decide +kernel

/-- Conjugations 1–4 are natural and every natural pair is one of them; conjugation 5 crosses
the gemination border and conjugation 6 conjugates P5 with itself. Wherever (11) marks one
alternant [−tr.], the causative is the other (p. 226). -/
theorem conjugations_natural :
    (∀ x ∈ conjugations, (Natural x.2.1 x.2.2 ↔ x.1 ∈ ["1", "2", "3", "4"]) ∧
      (x.2.1 = x.2.2 ↔ x.1 = "6") ∧ (¬(x.2.1.Geminated ↔ x.2.2.Geminated) ↔ x.1 = "5")) ∧
    (∀ p ∈ natural57, ∃ x ∈ conjugations, s(x.2.1, x.2.2) = p) ∧
    ∀ x ∈ conjugations, ¬(x.2.1.Intransitive ↔ x.2.2.Intransitive) → ¬x.2.1.Intransitive := by
  decide +kernel

/-! ### Over the fragment's segments -/

/-- `uncovered` lists the root-derived verbs the derivation leaves out, for guttural lowering in
*hexšiv* and *heʔedim*, t–sibilant metathesis in *histager*, and the biliteral allomorphy of √mss.
-/
def uncovered : List String := ["hexšiv", "histager", "namas", "hemes", "heʔedim"]

/-- `fillContinuant post s` realizes an alternating stop, a consonant unspecified for
continuancy, as its fricative after a vowel and as its stop elsewhere; any other segment is
itself. -/
def fillContinuant (post : Bool) (s : Phonology.Segment) : Phonology.Segment :=
  if s.Unspecified .continuant ∧ s.IsConsonant then
    if s.HasValue .dorsal true then if post then Hebrew.Phonology.x else Hebrew.Phonology.k
    else if s.HasValue .voice true then if post then Hebrew.Phonology.v else Hebrew.Phonology.b
    else if post then Hebrew.Phonology.f else Hebrew.Phonology.p
  else s

/-- The rule realizes each alternating stop as the one consonant that refines it with the
contextual continuancy. -/
theorem naturalClass_fillContinuant (post : Bool) :
    ∀ a ∈ [Hebrew.Phonology.B, Hebrew.Phonology.K, Hebrew.Phonology.P],
      (a.setFeature .continuant post).naturalClass Hebrew.Phonology.consonants =
        {fillContinuant post a} := by
  obtain ⟨hb, hv, hk, hx, hp, hf⟩ := Hebrew.Phonology.naturalClass_setFeature_continuant
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  cases post
  · exact ⟨hb, hk, hp⟩
  · exact ⟨hv, hx, hf⟩

/-- `segment x` reads a letter of the book's transcription as a segment of the fragment, *b*, *k*,
*p* as the archisegments of the alternating stops, *q* as the /k/ of ק, *r* as /ʁ/, *c* as /ts/ and
*e* as /ɛ/. -/
def segment : String → Phonology.Segment
  | "b" => Hebrew.Phonology.B
  | "k" => Hebrew.Phonology.K
  | "p" => Hebrew.Phonology.P
  | "q" => Hebrew.Phonology.k
  | "d" => Hebrew.Phonology.d
  | "f" => Hebrew.Phonology.f
  | "g" => Hebrew.Phonology.«ɡ»
  | "h" => Hebrew.Phonology.h
  | "y" => Hebrew.Phonology.j
  | "l" => Hebrew.Phonology.l
  | "m" => Hebrew.Phonology.m
  | "n" => Hebrew.Phonology.n
  | "r" => Hebrew.Phonology.«ʁ»
  | "s" => Hebrew.Phonology.s
  | "š" => Hebrew.Phonology.«ʃ»
  | "t" => Hebrew.Phonology.t
  | "c" => Hebrew.Phonology.ts
  | "v" => Hebrew.Phonology.v
  | "x" => Hebrew.Phonology.x
  | "z" => Hebrew.Phonology.z
  | "ʔ" => Hebrew.Phonology.«ʔ»
  | "a" => Hebrew.Phonology.a
  | "e" => Hebrew.Phonology.«ɛ»
  | "i" => Hebrew.Phonology.i
  | "o" => Hebrew.Phonology.o
  | "u" => Hebrew.Phonology.u
  | _ => ⊥

/-- `surfaceSegment x` reads a letter of a surface form, an alternating stop as the stop. -/
def surfaceSegment (x : String) : Phonology.Segment := fillContinuant false (segment x)

theorem fillContinuant_eq_self {s : Phonology.Segment}
    (h : ¬(s.Unspecified .continuant ∧ s.IsConsonant)) (post : Bool) :
    fillContinuant post s = s := by
  simp [fillContinuant, h]

/-- Only *b*, *k* and *p* read as alternating stops. -/
theorem not_alternating_segment (x : String) (hp : x ≠ "p") (hb : x ≠ "b") (hk : x ≠ "k") :
    ¬((segment x).Unspecified .continuant ∧ (segment x).IsConsonant) := by
  unfold segment
  split <;> first | contradiction | decide +kernel

/-- Filling continuancy over the fragment's segments agrees with spirantizing the
transcription. -/
theorem fillContinuant_segment (post : Bool) (x : String) :
    fillContinuant post (segment x) = surfaceSegment (fricative post x) := by
  cases post
  · rfl
  by_cases hp : x = "p"
  · subst hp; decide +kernel
  by_cases hb : x = "b"
  · subst hb; decide +kernel
  by_cases hk : x = "k"
  · subst hk; decide +kernel
  have hx : fricative true x = x := by unfold fricative; split <;> simp_all
  have h := not_alternating_segment x hp hb hk
  rw [surfaceSegment, hx, fillContinuant_eq_self h, fillContinuant_eq_self h]

/-- The roots of the data in the fragment, by label; Arad's √qlt is the fragment's √klt. -/
def fragmentRoots : List (String × ConsonantalRoot Phonology.Segment) :=
  [("lmd", Hebrew.lmd), ("spr", Hebrew.spr), ("qlt", Hebrew.klt), ("pll", Hebrew.pll),
    ("npc", Hebrew.npc), ("xlq", Hebrew.xlq), ("str", Hebrew.str), ("pqd", Hebrew.pqd),
    ("šmr", Hebrew.«šmr»), ("trgm", Hebrew.trgm), ("qbl", Hebrew.qbl), ("rkk", Hebrew.rkk),
    ("šmn", Hebrew.«šmn»), ("xšb", Hebrew.«xšb»), ("sgr", Hebrew.sgr), ("ptx", Hebrew.ptx),
    ("qpʔ", Hebrew.«qpʔ»), ("mss", Hebrew.mss), ("xmm", Hebrew.xmm), ("bhr", Hebrew.bhr),
    ("ʔdm", Hebrew.«ʔdm»)]

/-- Each root of the transcription, read letter by letter, is the fragment's root. -/
theorem root?_map_segment :
    ∀ p ∈ fragmentRoots, (root? p.1).map (·.map segment) = some p.2 := by
  simp only [fragmentRoots, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩

private theorem verb_eq_of_not_mem_uncovered {a : Forms.Analysis} (hf : a ∈ Forms.analyses)
    {x : Binyan × Voice × ConsonantalRoot String} (hx : x ∈ verbCell? a)
    (hu : a.form.form ∉ uncovered) :
    verb transcribedPx Vowel.transcription fricative x.1 x.2.1 x.2.2 = some a.form.segments := by
  by_contra hne
  by_cases hc : a.conjugation = none
  · have h : a.form.form ∈ ["hexšiv", "histager"] := by
      rw [← verbs_derived]
      exact List.mem_map_of_mem (List.mem_filter.2 ⟨hf, decide_eq_true ⟨hc, x, hx, hne⟩⟩)
    exact hu ((by decide : ∀ y ∈ _, y ∈ uncovered) _ h)
  · have h : a.form.form ∈ ["namas", "hemes", "heʔedim", "heʔedim"] := by
      rw [← conjugation_verbs_derived]
      exact List.mem_map_of_mem (List.mem_filter.2 ⟨hf, decide_eq_true ⟨hc, x, hx, hne⟩⟩)
    exact hu ((by decide : ∀ y ∈ _, y ∈ uncovered) _ h)

/-- Over the fragment's roots and segments, the derivation produces every root-derived word of
the data read as segments, the alternating stops realized by continuancy, except the verbs it
leaves out. -/
theorem words_derived_seg : ∀ p ∈ fragmentRoots, ∀ a ∈ Forms.analyses, a.root = some p.1 →
    (∀ x ∈ verbCell? a, a.form.form ∉ uncovered →
      verb (transcribedPx.map segment) (segment ∘ Vowel.transcription) fillContinuant x.1 x.2.1
        p.2 = some (a.form.segments.map surfaceSegment)) ∧
    ∀ x ∈ nounCell? a, surface fillContinuant
      (nounStem (transcribedPx.map segment) (segment ∘ Vowel.transcription) x.1 p.2) =
        a.form.segments.map surfaceSegment := by
  intro p hp a hf hroot
  have hr : ∀ r, root? p.1 = some r → p.2 = r.map segment := fun r h ↦ by
    simpa [h] using (root?_map_segment p hp).symm
  refine ⟨fun x hx hu ↦ ?_, fun x hx ↦ ?_⟩
  · have hx' : root? p.1 = some x.2.2 := by
      simp only [verbCell?, hroot, Option.bind_some, Option.mem_def, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hx
      obtain ⟨_, -, r, hr', rfl⟩ := hx
      exact hr'
    rw [hr _ hx', verb_map segment surfaceSegment fricative fillContinuant fillContinuant_segment,
      verb_eq_of_not_mem_uncovered hf hx hu]
    rfl
  · have hx' : root? p.1 = some x.2 := by
      simp only [nounCell?, hroot, Option.bind_some, Option.mem_def, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hx
      obtain ⟨_, -, r, hr', rfl⟩ := hx
      exact hr'
    rw [hr _ hx', nounStem_map, surface_map segment surfaceSegment fricative fillContinuant
      fillContinuant_segment, nouns_derived a hf x hx]

/-! ### Multiple Contextualized Meaning (Ch. 3, Ch. 7) -/

/-- `pattern? a` is the pattern of a word, its binyan number or its mišqal. -/
def pattern? (a : Forms.Analysis) : Option String := a.binyan.orElse fun _ ↦ a.pattern

/-- `rootForms` lists the words of a root in a pattern. -/
def rootForms (root pattern : String) : Finset String :=
  ((Forms.analyses.filter fun a ↦ a.root = some root ∧ pattern? a = some pattern).map
    (·.form.form)).toFinset

/-- `rootMeanings` lists the concepts of a root in a pattern. -/
def rootMeanings (root pattern : String) : Finset String :=
  ((Forms.analyses.filter fun a ↦ a.root = some root ∧ pattern? a = some pattern).map
    (·.form.parameterId)).toFinset

/-- `roots` is the interpreted realization system of roots over the patterns. -/
def roots : Realization.Interpreted String String String String where
  realize := rootForms
  interp := rootMeanings

/-- √sgr is 'close' in P1 and 'extradite' in P5, √qlt 'input' in CeCeC and 'a record' in
taCCiC, √xšb 'think' in P1 and 'computer' in maCCeC, √šmn 'oil' in CeCeC and 'cream' in
CaCCeCet (Ch. 7 (2)–(5)). -/
theorem roots_allosemous :
    roots.IsAllosemous "sgr" ∧ roots.IsAllosemous "qlt" ∧ roots.IsAllosemous "xšb" ∧
      roots.IsAllosemous "šmn" := by
  refine ⟨⟨"1", "5", "close", ?_, "extradite", ?_, by decide⟩,
    ⟨"CeCeC", "taCCiC", "input", ?_, "a_record", ?_, by decide⟩,
    ⟨"1", "maCCeC", "to_think", ?_, "computer", ?_, by decide⟩,
    ⟨"CeCeC", "CaCCeCet", "oil_grease", ?_, "cream", ?_, by decide⟩⟩ <;> decide +kernel

end Arad2005
