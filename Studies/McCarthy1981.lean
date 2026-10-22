module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Morphology.Morphotactics.Association
public import Linglib.Fragments.Arabic.ModernStandard.ConsonantalRoots
public import Linglib.Data.Wordlist.McCarthy1981

/-!
# McCarthy (1981): A Prosodic Theory of Nonconcatenative Morphology

This file formalizes McCarthy's analysis of the Classical Arabic verb. A verb stem
is a prosodic template of C- and V-slots with a consonantal root, a vowel melody and affixal
material on separate autosegmental tiers, and the melodies are associated with the slots by the
universal conventions of `Morphology.TemplateMatch.associate`. The language-particular
apparatus is the template schema (14), the affixes and their placement, the Eighth Binyan Flop
(19) and Erasure (24), together with the vowel melodies (39)–(43) and Vowel Association (41).
With it the derivation produces every form of the paper's table of the triliteral root ktb in
fifteen binyanim and the quadriliteral root dḥrj in four, in the perfective, imperfective and
participle, active and passive (`forms_derived`), except the participles of the first binyan,
which the paper leaves to McCarthy (1979).

Gemination is one root element linked to several slots: the medial radical of the second
binyan, after Erasure and respreading, and the final radical of a biliteral root, which the
conventions spread rightward only, so that *sasam* is underivable (`consonantism_biliteral`).
The quadriliterals are the second, fifth, fourteenth and eleventh binyanim with a fourth
radical, Erasure being undone by the conventions (`consonantism_quadriliteral`), and the
twelfth and thirteenth binyanim differ only in which tier respreads after Erasure. The
derivation never looks at the melodic elements themselves (`stem_map`).

## Main definitions

* `McCarthy1981.consonantism`, `McCarthy1981.stem`: the consonantism of a binyan and the stem of
  a cell of the table.

## Main results

* `McCarthy1981.forms_derived`: the derivation produces the paper's forms.
* `McCarthy1981.schema_elide_eq`: the schema (14a) with rule (14b) generates all and only the
  templates (13).
* `McCarthy1981.consonantism_quadriliteral`: the quadriliteral binyanim are triliteral ones.
* `McCarthy1981.metathesisSites_samam`, `McCarthy1981.metathesisSites_ktatab`: the cluster
  rule (37) applies to identical consonants linked to one root element, not to identical
  consonants of different morphemes.

## Implementation notes

* The forms are compared in the paper's transcription; `stem_map` carries a derivation over to
  the segments of the Arabic fragment, and `seg` reads the transcription as those segments.
* The consonantism of a stem is derived first and the prefix [CV] of imperfectives and
  participles added after it, so the root never reaches the prefixal C, which the participle
  fills with m and which the table's imperfectives, stems without agreement, leave empty.
* The first convention associates any number of unassociated elements one to one, as the
  paper's placement of a single affix on the leftmost C-slot (16)–(18) requires. It is then
  the first convention, not the second as on p. 395, that restores the fourth radical of a
  quadriliteral after Erasure; the second never changes a derivation here.
* The [+seg] slot of the eleventh binyan is V with a triliteral root and C with a quadriliteral
  one (31d); the first binyan's vowels are the a of rule (44) and the root's ablaut vowel (45),
  associated by the conventions.

## References

* [mccarthy-1981]
* [clements-ford-1979]
-/

@[expose] public section

open Morphology Autosegmental Arabic.ModernStandard

namespace McCarthy1981

variable {α β : Type*}

/-! ### Prosodic templates -/

/-- CVCVC (13a). -/
def cvcvc : Skeleton := [.C, .V, .C, .V, .C]

/-- CVCCVC (13b). -/
def cvccvc : Skeleton := [.C, .V, .C, .C, .V, .C]

/-- CVVCVC (13c). -/
def cvvcvc : Skeleton := [.C, .V, .V, .C, .V, .C]

/-- CVCVCCVC (13d). -/
def cvcvccvc : Skeleton := [.C, .V, .C, .V, .C, .C, .V, .C]

/-- CVCVVCVC (13e). -/
def cvcvvcvc : Skeleton := [.C, .V, .C, .V, .V, .C, .V, .C]

/-- CCVCVC (13f). -/
def ccvcvc : Skeleton := [.C, .C, .V, .C, .V, .C]

/-- CCVCCVC (13g). -/
def ccvccvc : Skeleton := [.C, .C, .V, .C, .C, .V, .C]

/-- CCVVCVC (13h). -/
def ccvvcvc : Skeleton := [.C, .C, .V, .V, .C, .V, .C]

/-- The canonical patterns of the triliteral perfective (13). -/
def binyanTemplates : List Skeleton :=
  [cvcvc, cvccvc, cvvcvc, cvcvccvc, cvcvvcvc, ccvcvc, ccvccvc, ccvvcvc]

/-- CVCVCVC, the one template of the schema with two light syllables. -/
def cvcvcvc : Skeleton := [.C, .V, .C, .V, .C, .V, .C]

/-- The prosodic template schema (14a), `[({C, CV}) CV ([+seg]) CVC]`, as the nine templates its
optional choices generate. -/
def schema : List Skeleton :=
  ([[], [.C], [.C, .V]] : List (List Slot)).flatMap fun pre ↦
    ([[], [.C], [.V]] : List (List Slot)).map fun s ↦ pre ++ [.C, .V] ++ s ++ [.C, .V, .C]

/-- Rule (14b), `V → ∅ / [CVC _ CVC]`, elides the middle vowel of the whole template CVCVCVC. -/
def elide (t : Skeleton) : Skeleton := if t = cvcvcvc then cvccvc else t

/-- The schema generates the templates (13) and CVCVCVC. -/
theorem schema_eq : schema.toFinset = insert cvcvcvc binyanTemplates.toFinset := by decide

/-- The schema with rule (14b) generates all and only the templates (13). -/
theorem schema_elide_eq : (schema.map elide).toFinset = binyanTemplates.toFinset := by decide

/-! ### The consonantism of the binyanim -/

/-- The triliteral binyanim. -/
inductive Binyan where
  | I | II | III | IV | V | VI | VII | VIII | IX | X | XI | XII | XIII | XIV | XV
  deriving DecidableEq, Repr, Fintype

/-- The quadriliteral binyanim QI–QIV, which are II, V, XIV and XI with a four-consonant root
(31). -/
def Binyan.ofQuadriliteral : Fin 4 → Binyan
  | 0 => .II | 1 => .V | 2 => .XIV | 3 => .XI

/-- The affixal consonants, the ʔ, t, n and st of (26b), the w, n and y of (27), and the m of the
participle prefix. -/
structure Affixes (α : Type*) where
  /-- The glottal stop of IV. -/
  glottal : α
  /-- The t of V, VI, VIII and X. -/
  t : α
  /-- The n of VII, XIV and XV. -/
  n : α
  /-- The s of X. -/
  s : α
  /-- The w of XII and XIII. -/
  w : α
  /-- The y of XV. -/
  y : α
  /-- The m of the participle prefix. -/
  m : α

/-- The affixal consonants relabeled. -/
def Affixes.map (f : α → β) (ax : Affixes α) : Affixes β :=
  ⟨f ax.glottal, f ax.t, f ax.n, f ax.s, f ax.w, f ax.y, f ax.m⟩

/-- Where a binyan's affix goes, on the leftmost free C-slots by the conventions (p. 389), there
and then a slot to the right by the Flop (19), or on slots fixed by the rules (27). -/
inductive Placement where
  | leftmost
  | flop
  | fixed (slots : List ℕ)

/-- What the grammar specifies for a binyan (pp. 392–393), namely its template, its affix and
where the affix goes, whether Erasure (24) applies, and the tier that respreads after
Erasure (30). -/
structure Spec (α : Type*) where
  /-- The prosodic template. -/
  template : Skeleton
  /-- The affixal material. -/
  affix : List α := []
  /-- Where the affix goes. -/
  placement : Placement := .leftmost
  /-- Whether Erasure applies. -/
  erasure : Bool := false
  /-- The tier that respreads after Erasure. -/
  respread : AssocSource := .root

/-- The specification of a binyan, with `plusSeg` the realization of the [+seg] slot of XI. -/
def spec (ax : Affixes α) (plusSeg : Slot) : Binyan → Spec α
  | .I => { template := cvcvc }
  | .II => { template := cvccvc, erasure := true }
  | .III => { template := cvvcvc }
  | .IV => { template := cvccvc, affix := [ax.glottal] }
  | .V => { template := cvcvccvc, affix := [ax.t], erasure := true }
  | .VI => { template := cvcvvcvc, affix := [ax.t] }
  | .VII => { template := ccvcvc, affix := [ax.n] }
  | .VIII => { template := ccvcvc, affix := [ax.t], placement := .flop }
  | .IX => { template := ccvcvc }
  | .X => { template := ccvccvc, affix := [ax.s, ax.t] }
  | .XI => { template := [.C, .C, .V, plusSeg, .C, .V, .C] }
  | .XII => { template := ccvccvc, affix := [ax.w], placement := .fixed [3], erasure := true }
  | .XIII =>
    { template := ccvccvc
      affix := [ax.w]
      placement := .fixed [3]
      erasure := true
      respread := .affix }
  | .XIV => { template := ccvccvc, affix := [ax.n], placement := .fixed [3] }
  | .XV => { template := ccvccvc, affix := [ax.n, ax.y], placement := .fixed [3, 6] }

/-- The specification with its affix relabeled. -/
def Spec.map (f : α → β) (sp : Spec α) : Spec β :=
  { template := sp.template, affix := sp.affix.map f, placement := sp.placement,
    erasure := sp.erasure, respread := sp.respread }

@[simp] theorem Spec.erasure_map (f : α → β) (sp : Spec α) : (sp.map f).erasure = sp.erasure :=
  rfl

@[simp] theorem Spec.respread_map (f : α → β) (sp : Spec α) : (sp.map f).respread = sp.respread :=
  rfl

/-- The Eighth Binyan Flop (19) moves an affix line on the first of two adjacent C-slots to the
second. -/
def flop (m : TemplateMatch α) : TemplateMatch α :=
  match m.template with
  | .C :: .C :: _ => { m with associations := m.associations.map fun a ↦
      if a.source == .affix && a.slotIndex == 0 then { a with slotIndex := 1 } else a }
  | _ => m

/-- The affixes of a binyan placed before the root associates (p. 389). -/
def placeAffixes (sp : Spec α) (r : ConsonantalRoot α) : TemplateMatch α :=
  let m : TemplateMatch α :=
    { root := r
      affix := sp.affix
      template := sp.template
      associations := [] }
  match sp.placement with
  | .leftmost => m.associateOneToOne .affix
  | .flop => flop (m.associateOneToOne .affix)
  | .fixed slots => m.link (slots.zipIdx.map fun (i, k) ↦ ⟨.affix, k, i⟩)

/-- Erasure (24), generalized (p. 393), removes the root line on the C-slot of the final
CVC. -/
def erasure (m : TemplateMatch α) : TemplateMatch α :=
  { m with associations := m.associations.filter fun a ↦
      !(a.source == .root && a.slotIndex == m.template.length - 3) }

/-- The consonantism of a binyan, with the affixes placed, the root associated by the
conventions, and, where Erasure applies, the conventions again with the binyan's respreading
tier. -/
def consonantism (ax : Affixes α) (plusSeg : Slot) (b : Binyan) (r : ConsonantalRoot α) :
    TemplateMatch α :=
  let sp := spec ax plusSeg b
  let m := (placeAffixes sp r).associate .root
  if sp.erasure then
    (((erasure m).associateOneToOne .root).associateRemaining .root).spread sp.respread
  else m

/-- The number of lines from an element of a tier. -/
def linkCount (m : TemplateMatch α) (s : AssocSource) (k : ℕ) : ℕ :=
  m.associations.countP fun a ↦ a.source == s && a.melodyIndex == k

/-! ### The vocalism -/

/-- The vowels of the melodies, archisegments abbreviated a, i, u (fn. 8). -/
inductive Vowel where
  | a | i | u
  deriving DecidableEq, Repr

/-- The verbal categories of the table, by aspect and voice. -/
inductive Category where
  | perfActive | perfPassive | imperfActive | imperfPassive | partActive | partPassive
  deriving DecidableEq, Repr, Fintype

/-- The imperfectives and participles prefix [CV] (p. 400). -/
def Category.prefixed : Category → Bool
  | .perfActive | .perfPassive => false
  | _ => true

/-- The participles. -/
def Category.participle : Category → Bool
  | .partActive | .partPassive => true
  | _ => false

/-- The ablaut class of a root (45), the vowel of the second syllable of the first binyan active
in the perfective and the imperfective. -/
structure Ablaut where
  /-- The perfective vowel. -/
  perf : Vowel
  /-- The imperfective vowel. -/
  imperf : Vowel

/-- The vowel melody of a cell, by (39) and (43), and for the first binyan active the a of (44)
with the root's ablaut vowel. -/
def melody (abl : Ablaut) : Category → Binyan → List Vowel
  | .perfActive, .I => [.a, abl.perf]
  | .perfActive, _ => [.a]
  | .perfPassive, _ => [.u, .i]
  | .imperfActive, .I => [.a, abl.imperf]
  | .imperfActive, .II | .imperfActive, .III | .imperfActive, .IV => [.u, .a, .i]
  | .imperfActive, .V | .imperfActive, .VI => [.a]
  | .imperfActive, _ => [.a, .i]
  | .imperfPassive, _ => [.u, .a]
  | .partActive, _ => [.u, .a, .i]
  | .partPassive, _ => [.u, .a]

/-- The prefix [CV] moves every line two slots right. -/
def prefixCV (m : TemplateMatch α) : TemplateMatch α :=
  { m with
    template := [.C, .V] ++ m.template
    associations := m.associations.map fun a ↦ { a with slotIndex := a.slotIndex + 2 } }

/-- Rule (14b) on a match deletes the middle V-slot of CVCVCVC and moves the lines after it left. -/
def elideMatch (m : TemplateMatch α) : TemplateMatch α :=
  if m.template = cvcvcvc then
    { m with
      template := cvccvc
      associations := (m.associations.filter (·.slotIndex != 3)).map fun a ↦
        if 3 < a.slotIndex then { a with slotIndex := a.slotIndex - 1 } else a }
  else m

/-- The participle's m on the prefixal C-slot, before the binyan's affixes. -/
def prefixM (ax : Affixes α) (m : TemplateMatch α) : TemplateMatch α :=
  { m with
    affix := ax.m :: m.affix
    associations := ⟨.affix, 0, 0⟩ :: m.associations.map fun a ↦
      if a.source == .affix then { a with melodyIndex := a.melodyIndex + 1 } else a }

/-- Vowel Association (41) links an i ending the melody to the final V-slot first. -/
def vowelAssociation (mel : List Vowel) (m : TemplateMatch α) : TemplateMatch α :=
  match mel.getLast?, m.template.vSlots.getLast? with
  | some .i, some s => m.link [⟨.vocalism, mel.length - 1, s⟩]
  | _, _ => m

/-- The stem of a cell, built from the consonantism, the prefix of imperfectives and participles
with rule (14b), the participle's m, and the melody associated by (41) and the conventions. -/
def stem (ax : Affixes α) (v : Vowel → α) (abl : Ablaut) (c : Category) (b : Binyan)
    (r : ConsonantalRoot α) : TemplateMatch α :=
  let m := consonantism ax (if r.arity = 4 then .C else .V) b r
  let m := if c.prefixed then elideMatch (prefixCV m) else m
  let m := if c.participle then prefixM ax m else m
  let mel := melody abl c b
  (vowelAssociation mel { m with vocalism := mel.map v }).associate .vocalism

/-! ### The derivation never looks at the melody -/

section Map

variable (f : α → β) (ax : Affixes α) (m : TemplateMatch α)

theorem spec_map (plusSeg : Slot) (b : Binyan) :
    spec (ax.map f) plusSeg b = (spec ax plusSeg b).map f := by
  cases b <;> rfl

theorem flop_map : flop (m.map f) = (flop m).map f := by
  unfold flop
  simp only [TemplateMatch.template_map]
  split <;> rfl

theorem placeAffixes_map (sp : Spec α) (r : ConsonantalRoot α) :
    placeAffixes (sp.map f) (r.map f) = (placeAffixes sp r).map f := by
  obtain ⟨t, af, pl, er, rs⟩ := sp
  have h : ({ root := r.map f, affix := af.map f, template := t, associations := [] } :
      TemplateMatch β) =
      ({ root := r, affix := af, template := t, associations := [] } : TemplateMatch α).map f :=
    rfl
  cases pl <;> simp only [placeAffixes, Spec.map, h, TemplateMatch.associateOneToOne_map,
    flop_map, TemplateMatch.link_map]

theorem erasure_map : erasure (m.map f) = (erasure m).map f := rfl

theorem consonantism_map (plusSeg : Slot) (b : Binyan) (r : ConsonantalRoot α) :
    consonantism (ax.map f) plusSeg b (r.map f) = (consonantism ax plusSeg b r).map f := by
  simp only [consonantism, spec_map, placeAffixes_map, TemplateMatch.associate_map,
    Spec.erasure_map, Spec.respread_map]
  split <;> simp only [erasure_map, TemplateMatch.associateOneToOne_map,
    TemplateMatch.associateRemaining_map, TemplateMatch.spread_map]

theorem prefixCV_map : prefixCV (m.map f) = (prefixCV m).map f := rfl

theorem elideMatch_map : elideMatch (m.map f) = (elideMatch m).map f := by
  unfold elideMatch
  simp only [TemplateMatch.template_map]
  split <;> rfl

theorem prefixM_map : prefixM (ax.map f) (m.map f) = (prefixM ax m).map f := by
  simp [prefixM, TemplateMatch.map, Affixes.map]

theorem vowelAssociation_map (mel : List Vowel) :
    vowelAssociation mel (m.map f) = (vowelAssociation mel m).map f := by
  unfold vowelAssociation
  simp only [TemplateMatch.template_map]
  split <;> rfl

/-- Relabeling the melodic elements relabels the stem. -/
theorem stem_map (v : Vowel → α) (abl : Ablaut) (c : Category) (b : Binyan)
    (r : ConsonantalRoot α) :
    stem (ax.map f) (f ∘ v) abl c b (r.map f) = (stem ax v abl c b r).map f := by
  have hvoc (m : TemplateMatch α) (mel : List Vowel) :
      { m.map f with vocalism := mel.map (f ∘ v) } = ({ m with vocalism := mel.map v }).map f := by
    simp [TemplateMatch.map]
  have harity : (r.map f).arity = r.arity := by simp [ConsonantalRoot.arity]
  simp only [stem, harity, consonantism_map]
  split <;> split <;>
    simp only [prefixCV_map, elideMatch_map, prefixM_map, hvoc, vowelAssociation_map,
      TemplateMatch.associate_map]

end Map

/-! ### Gemination, quadriliterals and stranding

The consonantism of any root is that of a root of numerals relabeled (`consonantism_map`), so
each claim about arbitrary radicals is decided on numerals. -/

section Symbolic

/-- Numerals for the affixal consonants. -/
private def numeralAffixes : Affixes ℕ := ⟨100, 101, 102, 103, 104, 105, 106⟩

/-- The relabeling of numerals by the radicals `xs` and the affixal consonants `ax`. -/
private def label (ax : Affixes α) (xs : List α) : ℕ → α
  | 100 => ax.glottal | 101 => ax.t | 102 => ax.n | 103 => ax.s | 104 => ax.w | 105 => ax.y
  | 106 => ax.m | k => xs.getD k ax.m

variable (ax : Affixes α) (v w x y z : α)

private theorem consonantism_eq_map {p : Slot} {b : Binyan} {xs : List α}
    {r : ConsonantalRoot ℕ} (hr : r.map (label ax xs) = ⟨xs⟩) :
    consonantism ax p b ⟨xs⟩ = (consonantism numeralAffixes p b r).map (label ax xs) := by
  rw [← consonantism_map, hr]
  rfl

private theorem spellout_eq {p : Slot} {b : Binyan} {xs : List α} {r : ConsonantalRoot ℕ}
    (hr : r.map (label ax xs) = ⟨xs⟩) {out : List ℕ}
    (h : (consonantism numeralAffixes p b r).spellout = out) :
    (consonantism ax p b ⟨xs⟩).spellout = out.map (label ax xs) := by
  rw [consonantism_eq_map ax hr, TemplateMatch.spellout_map, h]

private theorem linkCount_eq {p : Slot} {b : Binyan} {xs : List α} {r : ConsonantalRoot ℕ}
    (hr : r.map (label ax xs) = ⟨xs⟩) (s : AssocSource) (k : ℕ) :
    linkCount (consonantism ax p b ⟨xs⟩) s k =
      linkCount (consonantism numeralAffixes p b r) s k := by
  rw [consonantism_eq_map ax hr]
  rfl

/-- The second binyan geminates its medial radical by Erasure and respreading (17), (25). -/
theorem consonantism_II :
    (consonantism ax .V .II ⟨[x, y, z]⟩).spellout = [x, y, y, z] ∧
      linkCount (consonantism ax .V .II ⟨[x, y, z]⟩) .root 1 = 2 :=
  ⟨spellout_eq ax (r := ⟨[0, 1, 2]⟩) rfl (out := [0, 1, 1, 2]) (by decide),
    (linkCount_eq ax (r := ⟨[0, 1, 2]⟩) rfl _ _).trans (by decide)⟩

/-- The twelfth binyan respreads the root after Erasure, the thirteenth the infix w (30). -/
theorem consonantism_XII_XIII :
    (consonantism ax .V .XII ⟨[x, y, z]⟩).spellout = [x, y, ax.w, y, z] ∧
      (consonantism ax .V .XIII ⟨[x, y, z]⟩).spellout = [x, y, ax.w, ax.w, z] :=
  ⟨spellout_eq ax (r := ⟨[0, 1, 2]⟩) rfl (out := [0, 1, 104, 1, 2]) (by decide),
    spellout_eq ax (r := ⟨[0, 1, 2]⟩) rfl (out := [0, 1, 104, 104, 2]) (by decide)⟩

/-- A biliteral root geminates its final radical and never its first, giving samam, never
*sasam (33). In the second and fifth binyanim the effect of Erasure is undone (34). -/
theorem consonantism_biliteral :
    (consonantism ax .V .I ⟨[x, y]⟩).spellout = [x, y, y] ∧
      linkCount (consonantism ax .V .I ⟨[x, y]⟩) .root 0 = 1 ∧
      (consonantism ax .V .II ⟨[x, y]⟩).spellout = [x, y, y, y] ∧
      (consonantism ax .V .V ⟨[x, y]⟩).spellout = [ax.t, x, y, y, y] :=
  ⟨spellout_eq ax (r := ⟨[0, 1]⟩) rfl (out := [0, 1, 1]) (by decide),
    (linkCount_eq ax (r := ⟨[0, 1]⟩) rfl _ _).trans (by decide),
    spellout_eq ax (r := ⟨[0, 1]⟩) rfl (out := [0, 1, 1, 1]) (by decide),
    spellout_eq ax (r := ⟨[0, 1]⟩) rfl (out := [101, 0, 1, 1, 1]) (by decide)⟩

/-- The quadriliteral binyanim QI–QIV (32), the effect of Erasure in QI and QII undone by the
second convention. -/
theorem consonantism_quadriliteral :
    (consonantism ax .C .II ⟨[w, x, y, z]⟩).spellout = [w, x, y, z] ∧
      (consonantism ax .C .V ⟨[w, x, y, z]⟩).spellout = [ax.t, w, x, y, z] ∧
      (consonantism ax .C .XIV ⟨[w, x, y, z]⟩).spellout = [w, x, ax.n, y, z] ∧
      (consonantism ax .C .XI ⟨[w, x, y, z]⟩).spellout = [w, x, y, z, z] :=
  ⟨spellout_eq ax (r := ⟨[0, 1, 2, 3]⟩) rfl (out := [0, 1, 2, 3]) (by decide),
    spellout_eq ax (r := ⟨[0, 1, 2, 3]⟩) rfl (out := [101, 0, 1, 2, 3]) (by decide),
    spellout_eq ax (r := ⟨[0, 1, 2, 3]⟩) rfl (out := [0, 1, 102, 2, 3]) (by decide),
    spellout_eq ax (r := ⟨[0, 1, 2, 3]⟩) rfl (out := [0, 1, 2, 3, 3]) (by decide)⟩

/-- A quinqueliteral root in QI strands its fifth radical (38). -/
theorem consonantism_quinqueliteral :
    (consonantism ax .C .II ⟨[v, w, x, y, z]⟩).spellout = [v, w, x, y] ∧
      (consonantism ax .C .II ⟨[v, w, x, y, z]⟩).unassociated .root = [4] :=
  ⟨spellout_eq ax (r := ⟨[0, 1, 2, 3, 4]⟩) rfl (out := [0, 1, 2, 3]) (by decide), by
    rw [consonantism_eq_map ax (r := ⟨[0, 1, 2, 3, 4]⟩) rfl, TemplateMatch.unassociated_map]
    decide⟩

end Symbolic

/-! ### The paper's forms -/

/-- The affixal consonants in the paper's transcription. -/
def transcribedAffixes : Affixes String := ⟨"ʔ", "t", "n", "s", "w", "y", "m"⟩

/-- The vowels in the paper's transcription. -/
def Vowel.transcription : Vowel → String
  | .a => "a" | .i => "i" | .u => "u"

/-- The ablaut class of ktb, katab–yaktub, and of smm, samam–yasummu (45b). -/
def ktbAblaut : Ablaut := ⟨.a, .u⟩

/-- The binyan of a label of the table, a quadriliteral one being its triliteral binyan (31). -/
def binyanOf : Wordlist.Binyan → Binyan
  | .i => .I | .ii => .II | .iii => .III | .iv => .IV | .v => .V | .vi => .VI | .vii => .VII
  | .viii => .VIII | .ix => .IX | .x => .X | .xi => .XI | .xii => .XII | .xiii => .XIII
  | .xiv => .XIV | .xv => .XV | .qi => .ofQuadriliteral 0 | .qii => .ofQuadriliteral 1
  | .qiii => .ofQuadriliteral 2 | .qiv => .ofQuadriliteral 3

/-- The category of a cell's aspect, verb form and voice. -/
def category? (c : Wordlist.Cell) : Option Category :=
  match (c.aspect : Option UD.Aspect), (c.verbForm : Option UD.VerbForm),
    (c.voice : Option UD.Voice) with
  | some .Perf, _, some .Act => some .perfActive
  | some .Perf, _, some .Pass => some .perfPassive
  | some .Imp, _, some .Act => some .imperfActive
  | some .Imp, _, some .Pass => some .imperfPassive
  | _, some .Part, some .Act => some .partActive
  | _, some .Part, some .Pass => some .partPassive
  | _, _, _ => none

/-- The root of a concept in the paper's transcription, the root of 'poison' being the
biliteral that the OCP (11) makes of smm (p. 396). -/
def root? : String → Option (ConsonantalRoot String)
  | "write" => some ⟨["k", "t", "b"]⟩
  | "roll" => some ⟨["d", "ḥ", "r", "j"]⟩
  | "poison" => some ⟨OCP.collapse ["s", "m", "m"]⟩
  | "magnetize" => some ⟨["m", "ğ", "n", "ṭ", "š"]⟩
  | _ => none

/-- A cell is a binyan, a category and a root. -/
structure Cell where
  /-- The binyan. -/
  binyan : Binyan
  /-- The category. -/
  category : Category
  /-- The root. -/
  root : ConsonantalRoot String

/-- The cell of a form, read off its features and its concept. -/
def cell? (f : Data.Wordlist.Form Wordlist.Cell) : Option Cell := do
  let b ← (f.cell.binyan : Option Wordlist.Binyan).map binyanOf
  let c ← category? f.cell
  pure ⟨b, c, ← root? f.parameterId⟩

/-- A cell the analysis covers, any but a participle of the first binyan, which the paper leaves
to McCarthy's dissertation (p. 402). -/
def Cell.Covered (x : Cell) : Prop := ¬(x.binyan = .I ∧ x.category.participle = true)

instance (x : Cell) : Decidable x.Covered := inferInstanceAs (Decidable ¬_)

/-- The stem of a cell in the paper's transcription. -/
def Cell.stem (x : Cell) : TemplateMatch String :=
  McCarthy1981.stem transcribedAffixes Vowel.transcription ktbAblaut x.category x.binyan x.root

/-- Every form has a cell. -/
theorem isSome_cell? : ∀ f ∈ Wordlist.all, (cell? f).isSome := by decide +kernel

/-- The derivation produces every form of the table and of (33), (34) and (38) whose cell the
analysis covers. -/
theorem forms_derived :
    ∀ f ∈ Wordlist.all, ∀ x ∈ cell? f, x.Covered → x.stem.spellout = f.segments := by
  decide +kernel

/-- The forms of uncovered cells are the participles kaatib and maktuub, which the derivation
does not produce. -/
theorem forms_uncovered :
    (Wordlist.all.filter fun f ↦ ∃ x ∈ cell? f, ¬x.Covered).map (·.form) = ["kaatib", "maktuub"] ∧
      ∀ f ∈ Wordlist.all, ∀ x ∈ cell? f, ¬x.Covered → x.stem.spellout ≠ f.segments := by
  decide +kernel

/-- Every stem of ktb and of dḥrj is well formed on each tier, in that no association lines
cross and no slot has two lines from one tier. -/
theorem orderedOn_stem :
    (∀ b c, ∀ s ∈ [AssocSource.root, .affix, .vocalism],
      (McCarthy1981.stem transcribedAffixes Vowel.transcription ktbAblaut c b
        ⟨["k", "t", "b"]⟩).OrderedOn s) ∧
    ∀ q, ∀ c, ∀ s ∈ [AssocSource.root, .affix, .vocalism],
      (McCarthy1981.stem transcribedAffixes Vowel.transcription ktbAblaut c (.ofQuadriliteral q)
        ⟨["d", "ḥ", "r", "j"]⟩).OrderedOn s := by
  decide +kernel

/-- The paper's transcription as segments of the Arabic fragment, where j is ج, ğ is غ, y the glide,
ḥ the pharyngeal fricative, ṭ the emphatic t and š the postalveolar fricative. -/
def seg : String → Phonology.Segment
  | "b" => Phonology.b | "d" => Phonology.d | "k" => Phonology.k | "l" => Phonology.l
  | "m" => Phonology.m | "n" => Phonology.n | "q" => Phonology.q | "r" => Phonology.r
  | "s" => Phonology.s | "t" => Phonology.t | "w" => Phonology.w | "y" => Phonology.j
  | "j" => Phonology.«dʒ» | "ğ" => Phonology.«ʁ» | "ḥ" => Phonology.ħ
  | "ṭ" => Phonology.«tˤ» | "š" => Phonology.«ʃ» | "ʔ" => Phonology.«ʔ»
  | "a" => Phonology.a | "i" => Phonology.i | "u" => Phonology.u | _ => ⊥

/-- The roots of the forms are the fragment's ktb, dḥrj and mğnṭš. -/
theorem root?_map_seg : (root? "write").map (·.map seg) = some ktb ∧
    (root? "roll").map (·.map seg) = some «dḥrj» ∧
    (root? "magnetize").map (·.map seg) = some «mğnṭš» := ⟨rfl, rfl, rfl⟩

/-- Over the fragment's segments the derivation produces the forms read as segments. -/
theorem forms_derived_seg : ∀ f ∈ Wordlist.all, ∀ x ∈ cell? f, x.Covered →
    (McCarthy1981.stem (transcribedAffixes.map seg) (seg ∘ Vowel.transcription) ktbAblaut
      x.category x.binyan (x.root.map seg)).spellout = f.segments.map seg := by
  intro f hf x hx hc
  rw [stem_map, TemplateMatch.spellout_map]
  exact congrArg _ (forms_derived f hf x hx hc)

/-! ### The OCP and Metathesis -/

/-- The revised OCP (11) represents the geminate root smm as the biliteral sm (p. 396). -/
theorem collapse_smm : OCP.collapse smm.segments = [Phonology.s, Phonology.m] := by
  decide +kernel

/-- The roots of the forms observe the OCP; smm does not, nor do the hypothetical *ddrj and
*drrj (p. 397). -/
theorem isOCPClean_roots :
    ktb.IsOCPClean ∧ «dḥrj».IsOCPClean ∧ qlq.IsOCPClean ∧ «mğnṭš».IsOCPClean ∧
      (⟨OCP.collapse smm.segments⟩ : ConsonantalRoot Phonology.Segment).IsOCPClean ∧
      ¬smm.IsOCPClean ∧
      ¬(⟨[Phonology.d, Phonology.d, Phonology.r, Phonology.«dʒ»]⟩ :
        ConsonantalRoot Phonology.Segment).IsOCPClean ∧
      ¬(⟨[Phonology.d, Phonology.r, Phonology.r, Phonology.«dʒ»]⟩ :
        ConsonantalRoot Phonology.Segment).IsOCPClean := by
  decide +kernel

/-- The structural description of Metathesis (37) holds when the C-slots `i` and `i + 2` on
either side of a V-slot are linked to one melodic element, which has no line left of `i`. -/
def MetathesisSite (m : TemplateMatch α) (i : ℕ) : Prop :=
  m.template[i + 1]? = some .V ∧ ∃ a ∈ m.associations, a.slotIndex = i ∧
    (∃ b ∈ m.associations, b.slotIndex = i + 2 ∧ b.source = a.source ∧
      b.melodyIndex = a.melodyIndex) ∧
    ∀ c ∈ m.associations, c.source = a.source → c.melodyIndex = a.melodyIndex → i ≤ c.slotIndex

instance (m : TemplateMatch α) (i : ℕ) : Decidable (MetathesisSite m i) := by
  unfold MetathesisSite; infer_instance

/-- The sites of Metathesis in a match. -/
def metathesisSites (m : TemplateMatch α) : List ℕ :=
  (List.range m.template.length).filter (MetathesisSite m ·)

theorem metathesisSite_iff (m : TemplateMatch α) (i : ℕ) :
    MetathesisSite m i ↔ i ∈ metathesisSites m := by
  refine ⟨fun h ↦ List.mem_filter.2 ⟨List.mem_range.2 ?_, decide_eq_true h⟩,
    fun h ↦ of_decide_eq_true (List.mem_filter.1 h).2⟩
  have := h.1
  simp only [List.getElem?_eq_some_iff] at this
  obtain ⟨hlt, -⟩ := this
  exact Nat.lt_of_succ_lt hlt

theorem metathesisSites_map (f : α → β) (m : TemplateMatch α) :
    metathesisSites (m.map f) = metathesisSites m := rfl

section Metathesis

variable (ax : Affixes α) (x y z : α)

/-- In samam the two m's are one root element, and Metathesis applies (35a). -/
theorem metathesisSites_samam : metathesisSites (consonantism ax .V .I ⟨[x, y]⟩) = [2] := by
  rw [consonantism_eq_map ax (r := ⟨[0, 1]⟩) rfl, metathesisSites_map]
  decide

/-- In ktatab the two t's are the affix and a root element, and Metathesis does not apply. -/
theorem metathesisSites_ktatab : metathesisSites (consonantism ax .V .VIII ⟨[x, y, z]⟩) = [] := by
  rw [consonantism_eq_map ax (r := ⟨[0, 1, 2]⟩) rfl, metathesisSites_map]
  decide

/-- In sammam the second m is the first element linked further left, and the revision (37)
keeps Metathesis from applying. -/
theorem metathesisSites_sammam : metathesisSites (consonantism ax .V .II ⟨[x, y]⟩) = [] := by
  rw [consonantism_eq_map ax (r := ⟨[0, 1]⟩) rfl, metathesisSites_map]
  decide

end Metathesis

/-! ### Ablaut -/

/-- Whether a vowel is [+high]. -/
def Vowel.high : Vowel → Bool
  | .a => false | .i | .u => true

/-- Whether a vowel is [+back]. -/
def Vowel.back : Vowel → Bool
  | .i => false | .a | .u => true

/-- Ablaut (46) pairs an imperfective [αhigh] vowel with a perfective [−αhigh, αback] one. -/
def Vowel.ablaut (v : Vowel) : Vowel := if v.high then .a else .i

theorem Vowel.ablaut_eq_iff (v w : Vowel) :
    v.ablaut = w ↔ w.high = !v.high ∧ w.back = v.high := by
  cases v <;> cases w <;> decide

/-- Ablaut relates the perfective and imperfective vowels of the classes (45a–c), and not those
of (45d). -/
theorem ablaut_classes :
    (∀ c ∈ [(⟨.a, .i⟩ : Ablaut), ⟨.a, .u⟩, ⟨.i, .a⟩], c.imperf.ablaut = c.perf) ∧
      (⟨.u, .u⟩ : Ablaut).imperf.ablaut ≠ .u := by
  decide

/-- The melody with Ablaut on its last element. -/
def ablautLast (mel : List Vowel) : List Vowel :=
  mel.dropLast ++ (mel.getLast?.map Vowel.ablaut).toList

/-- The perfective active melody of the derived binyanim is the basic imperfective melody u–a–i
with Ablaut on its last element, the OCP, and its initial u erased (47), (48). -/
theorem melody_perfActive (abl : Ablaut) (b : Binyan) (hb : b ≠ .I) :
    melody abl .perfActive b = (OCP.collapse (ablautLast [.u, .a, .i])).tail := by
  cases b <;> first | exact absurd rfl hb | rfl

/-- The perfective passive melody is the imperfective passive melody with Ablaut on its last
element (49). -/
theorem melody_perfPassive (abl : Ablaut) (b : Binyan) :
    melody abl .perfPassive b = ablautLast (melody abl .imperfPassive b) := by
  cases b <;> rfl

end McCarthy1981
