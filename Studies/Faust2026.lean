module

public import Linglib.Morphology.Morphotactics.Association
public import Linglib.Fragments.Amharic.ConsonantalRoots
public import Studies.Arad2005
public import Linglib.Syntax.Gender.Basic
public import Linglib.Data.Examples.Faust2026
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Faust (2026): Intrusion as template satisfaction and the QaTaT–QaTa problem in Semitic

Faust's *Misalignment principle bars a nonfinal root element from the template-final slot. A
root whose final radical cannot take a [+consonantal] C-slot then satisfies the template in one
of two ways: it leaves the slot vacant, as in Hebrew [kala], or the consonant of the feminine
suffix fills it, as in Hebrew [tadmit] and Amharic [fäʤt-o]. The derivations run McCarthy's
association conventions with slot specifications that bar glides and vowels from [+c] slots,
and the feminine morph, inherent inflection on n, merges only with a nominal base. That gives
the distribution of the intruding [t] across the Amharic paradigms, which Broselow's default
consonant left unexplained, and the No-Crossing Constraint keeps it out of the hollow verbs.

## Implementation notes

* The derivations run over the squib's transcription. `fragment_roots` shows that its roots,
  read as segments, are the Hebrew and Amharic fragments' roots, the alternating stops of √kl
  and √skt realized as stops by Arad's rule.
* The root and the feminine morph share the consonantal plane, the morph's t after the radicals
  as (10c) draws them, so the No-Crossing Constraint on intrusion is the constraint on that plane.
  The template, a morph in its own right (p. 433), carries the vocalization on the vocalic plane.
  *Misalignment reads the sponsors: a root element is nonfinal when a root element follows it.
* `segClass` lets a plain C-slot host a glide but no vowel and a [+c] slot only consonants, and
  `merge` states the squib's mergers d + j to ʤ, ä + a to a and ä + i to e.
* The medial geminate of the Amharic PFV is prespecified ({C C} in (7)). The suffix consonant
  associates to the rightmost vacant C-slot only inside its `Autosegmental.window`, and the
  morph's vowel does not surface, so the affix carries only t.
* The squib labels (13c) [mähid] where (12e) and its merger give [mähed], and the rows follow
  (12e). The IPFV and JUSS, whose templates the squib does not draw, and the PFV of √sma are
  not derived.

## References

* [faust-2026]
* [mccarthy-1981]
* [arad-2005]
* [broselow-1984]
* [greenberg-1950]
* [leslau-1995]
* [lowenstamm-1996]
* [lowenstamm-2014]
* [goldsmith-1976]
-/

@[expose] public section

namespace Faust2026

open Morphology Autosegmental

variable {α : Type}

/-- The planes of a stem (10c): the consonantal melody, root and suffix, and the template's
vocalization. -/
inductive Plane where
  | consonantal
  | vocalic
  deriving DecidableEq, Repr, Fintype

/-- The morphemes of a stem: the root, the feminine morph √(a)t, and the template, which is a
derivational morph in its own right (p. 433). -/
inductive Morpheme where
  | root
  | suffix
  | template
  deriving DecidableEq, Repr

open AR

/-! ### *Misalignment -/

/-- `Misaligned m` holds when some nonfinal root element is associated to the template-final slot,
which *Misalignment (2), (6b) bans. The root's elements precede the suffix's on the consonantal
plane, so a root element is nonfinal when a root element follows it. -/
def Misaligned (m : AR (Multiplanar Plane (Sponsored α Morpheme) (Sponsored Slot Morpheme))) :
    Prop :=
  ∃ l ∈ (m.lines (some .consonantal) none), ((m.word (some .consonantal)))[l.1]?.map (·.morpheme) =
      some .root ∧
    ((m.word (some .consonantal)))[l.1 + 1]?.map (·.morpheme) = some .root ∧
      l.2 + 1 = m.template.length

instance (m : AR (Multiplanar Plane (Sponsored α Morpheme) (Sponsored Slot Morpheme))) :
    Decidable (Misaligned m) :=
  inferInstanceAs (Decidable (∃ _ ∈ (m.lines (some .consonantal) none), _))

/-- The classes the [+consonantal] specification of a C-slot separates. -/
inductive SegClass where
  | consonant
  | glide
  | vowel
  deriving DecidableEq, Repr

/-- The glide j and the nonconsonantal radicals a, i of the Amharic hollow roots (12c–e) are
barred from [+c] slots; every other segment is a consonant. -/
def segClass : String → SegClass
  | "j" => .glide
  | "a" | "i" => .vowel
  | _ => .consonant

/-- `merge` states the mergers of two elements sharing a slot that the squib names. A glide joined
to the preceding consonant palatalizes it ((7), [fäʤʤ-ä]), and a nonconsonantal radical merges with
the vocalization, /a,ä/ yielding [a] and /i,ä/ yielding [e] (13). -/
def merge : String → String → String
  | "d", "j" => "ʤ"
  | "ä", "a" => "a"
  | "ä", "i" => "e"
  | x, _ => x

/-- `Category` is the category of the base a template builds. Gender markers are inherent inflection
on n, so only a nominal base merges with the feminine morph (11). -/
inductive Category where
  | noun
  | verb
  | adjective
  deriving DecidableEq, Repr

/-- A pattern is a template with its lexical shape, namely its skeleton, category, vocalization and
lines, segmental material outside the skeleton, and the parameters of the squib's derivations. -/
structure Pattern where
  /-- The skeleton. -/
  template : Skeleton
  /-- The C-slots prespecified [+c]. -/
  consonantal : List ℕ := []
  /-- The category of the base. -/
  category : Category
  /-- The vocalization and its association lines. -/
  vocalism : List String := []
  vocLines : List (ℕ × ℕ) := []
  /-- Segmental material preceding and following the skeleton. -/
  pre : List String := []
  post : List String := []
  /-- A slot prespecified as geminate ({C C} in (7)). -/
  geminate : Option Nat := none
  /-- A barred glide joins the consonant on its left (Amharic (7)) rather than floating
  (Hebrew (4)). -/
  joinsGlide : Bool := false
  /-- An unsatisfied final syllable is deleted (7a). -/
  truncates : Bool := false

/-- The template of a pattern, a morph of its slots and its vocalization with the vocalization's
lines (p. 433). -/
def Pattern.morph (p : Pattern) :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme)) :=
  (ofSlots .template p.template * ofMelody .vocalic .template p.vocalism :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))).link .vocalic
        p.vocLines

/-- The root associated with the C-slots by the conventions, one to one from left to right
with the final radical spreading onto leftover slots, under the pattern's vocalization. -/
def lines (p : Pattern) (r : ConsonantalRoot String) :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme)) :=
  (ofMelody Plane.consonantal Morpheme.root r.segments * p.morph).associate .consonantal .C

/-- `m.Admits l` says that the slot's specification admits the segment of the consonantal line
`l`. A [+c] slot hosts consonants only ((4), (7), (13)), and a plain C-slot anything but a
vowel. -/
def Admits (p : Pattern) (m :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))) (l : ℕ × ℕ) :
    Prop :=
  match m.template[l.2]?, (((m.word (some .consonantal)))[l.1]?).map (·.value) with
  | some .C, some x =>
    if l.2 ∈ p.consonantal then segClass x = .consonant else segClass x ≠ .vowel
  | _, _ => True

instance (p : Pattern) (m :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))) (l : ℕ × ℕ) :
    Decidable (Admits p m l) := by
  unfold Admits; split <;> infer_instance

/-- The V-slots flanking slot `i`. -/
def flankingV (m : AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))) (i
    : Nat) : List Nat :=
  [i - 1, i + 1].filter fun s ↦ m.template[s]? = some .V

/-- The vocalization line at slot `s`. -/
def vocAt (m : AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))) (s :
    Nat) : Option (ℕ × ℕ) :=
  ((List.range ((m.word (some .vocalic))).length).find? fun k ↦ (k, s) ∈ (m.lines (some .vocalic)
      none)).map (·, s)

/-- `join` places a barred root element. A glide joins the slot of the consonant on its left where
the pattern's language does that, Amharic and not Hebrew (7). A nonconsonantal radical merges with
the vocalization on the V-slots flanking its slot, the vocalization element spreading to a flanking
V-slot it did not occupy, so that the merger "occupies the two vocalic positions around the C
position" (13b–c). -/
def join (p : Pattern) (m :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))) (l : ℕ × ℕ) :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme)) :=
  match (((m.word (some .consonantal)))[l.1]?).map (segClass ·.value) with
  | some .glide =>
    if p.joinsGlide then
      match m.leftLine .consonantal l.2 with
      | some b => m.link .consonantal [(l.1, b.2)]
      | none => m
    else m
  | some .vowel =>
    let vs := flankingV m l.2
    match vs.findSome? (vocAt m) with
    | some v =>
      (m.link .consonantal (vs.map (l.1, ·))).link .vocalic
        ((vs.filter fun s ↦ (vocAt m s).isNone).map (v.1, ·))
    | none => m
  | _ => m

/-- The consonantal lines of a match, by melody position and then slot. -/
def consonantalLines (m :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))) : List (ℕ × ℕ) :=
  (List.range ((m.word (some .consonantal))).length).flatMap fun k ↦
    ((List.range (m.word none).length).filter fun s ↦ (k, s) ∈ (m.lines (some .consonantal)
        none)).map (k, ·)

/-- Association under the slot specifications removes the rejected lines and joins or merges their
elements as the pattern's language allows. -/
def associate (p : Pattern) (r : ConsonantalRoot String) :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme)) :=
  let m := lines p r
  ((consonantalLines m).filter fun l ↦ ¬ Admits p m l).foldl (join p)
    (m.filterLines .consonantal (Admits p m ·))

/-! ### Intrusion -/

/-- The feminine morph √(a)t, whose vowel does not surface, so that it carries only t. -/
def suffixMorph : AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme)) :=
  ofMelody .consonantal .suffix ["t"]

/-- The feminine morph merged with the base, its consonant associated to slot `s`. The base's root
and the morph share the consonantal plane, the morph's t after the radicals (10c). -/
def intrudeAt (m : AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))) (s
    : Nat) :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme)) :=
  (m * suffixMorph).link .consonantal [(((m.word (some .consonantal))).length, s)]

theorem lines_intrudeAt_subset (m :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))) (s : Nat) :
    (intrudeAt m s).lines (some .consonantal) none ⊆
      insert (((m.word (some .consonantal))).length, s) ((m.lines (some .consonantal) none)) := by
  intro l hl
  rw [intrudeAt, link, mem_addLines] at hl
  simp only [suffixMorph, lines_mul, lines_ofMelody, Finset.map_empty,
    Finset.union_empty, List.mem_toFinset, List.mem_singleton] at hl
  rw [Finset.mem_insert]
  tauto

/-- Intrusion (10b–c) associates the morph's consonant from right to left to the rightmost vacant
C-slot, provided that slot lies in its window, so that its line crosses none of the root's;
otherwise the consonant floats (13b–c). -/
def intrude (m : AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))) :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme)) :=
  match m.unfilledCSlots.max? with
  | some s =>
    if s ∈ window ((m.lines (some .consonantal) none) :
        SetRel ℕ ℕ) ((m.word (some .consonantal))).length then
      intrudeAt m s
    else m * suffixMorph
  | none => m * suffixMorph

theorem misaligned_mul_suffixMorph (m :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme)))
    {L : List (ℕ × ℕ)} (hL : ∀ l ∈ L, ((m.word (some .consonantal))).length ≤ l.1) :
    Misaligned ((m * suffixMorph).link .consonantal L) ↔ Misaligned m := by
  have hroot (k : ℕ) :
      (((m.word (some .consonantal)) ++ [⟨"t", .suffix⟩])[k]?.map (·.morpheme) = some .root) ↔
        ((m.word (some .consonantal)))[k]?.map (·.morpheme) = some .root := by
    rcases lt_or_ge k ((m.word (some .consonantal))).length with h | h
    · rw [List.getElem?_append_left h]
    · rw [List.getElem?_append_right h, List.getElem?_eq_none h, List.getElem?_singleton]
      split_ifs <;> simp
  have hupper : (((m * suffixMorph).link .consonantal L).word (some .consonantal)) =
      (m.word (some .consonantal)) ++ [⟨"t", .suffix⟩] := by
    simp [link, suffixMorph]
  have htemplate : ((m * suffixMorph).link .consonantal L).template = m.template := by
    simp [link, suffixMorph, template]
  simp only [Misaligned, hupper, htemplate, hroot]
  constructor
  · rintro ⟨l, hl, h1, h2, h3⟩
    rw [link, mem_addLines] at hl
    simp only [suffixMorph, lines_mul, lines_ofMelody, Finset.map_empty,
      Finset.union_empty, List.mem_toFinset, true_and] at hl
    rcases hl with hl | ⟨hl, -⟩
    · exact ⟨l, hl, h1, h2, h3⟩
    · rw [List.getElem?_eq_none (hL l hl)] at h1
      simp at h1
  · rintro ⟨l, hl, h⟩
    refine ⟨l, ?_, h⟩
    rw [link, mem_addLines]
    simp [suffixMorph, hl]

theorem misaligned_intrudeAt (m :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))) (s : Nat) :
    Misaligned (intrudeAt m s) ↔ Misaligned m :=
  misaligned_mul_suffixMorph m (by simp)

-- (8), (10)
theorem misaligned_intrude (m :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))) :
    Misaligned (intrude m) ↔ Misaligned m := by
  have h : Misaligned (m * suffixMorph) ↔ Misaligned m := by
    simpa [Misaligned, link, template] using misaligned_mul_suffixMorph m (L := []) (by simp)
  unfold intrude
  split
  · split
    · exact misaligned_intrudeAt m _
    · exact h
  · exact h

/-- The intruder's line never crosses a root line, so intrusion keeps the consonantal plane
non-crossing. -/
theorem isNonCrossing_lines_intrude (m :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme)))
    (h : IsNonCrossing ((m.lines (some .consonantal) none) : SetRel ℕ ℕ)) :
    IsNonCrossing ((intrude m).lines (some .consonantal) none : SetRel ℕ ℕ) := by
  have hsuf : (m * suffixMorph).lines (some .consonantal) none = (m.lines (some .consonantal) none)
      := by
    simp [suffixMorph]
  unfold intrude
  split
  · split
    · refine IsNonCrossing.subset (Finset.coe_subset.2 (lines_intrudeAt_subset m _)) ?_
      rw [Finset.coe_insert, isNonCrossing_insert_iff_mem_window]
      exact ⟨h, ‹_›⟩
    · rwa [hsuf]
  · rwa [hsuf]

/-- The derivation of a root in a pattern is association under the slot specifications followed, for
a nominal base whose template is unsatisfied, by merger of the feminine morph ((10b), (11)). -/
def derive (p : Pattern) (r : ConsonantalRoot String) :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme)) :=
  let m := associate p r
  if p.category = .noun ∧ ¬ m.allCSlotsFilled then intrude m else m

-- (11)
theorem derive_of_category_ne_noun (p : Pattern) (r : ConsonantalRoot String)
    (h : p.category ≠ .noun) : derive p r = associate p r := by
  simp [derive, h]

/-! ### Realization -/

/-- `hosted m s` lists the segments slot `s` hosts, vocalization first, then the consonantal
melody, root before suffix. -/
def hosted (m : AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))) (s :
    Nat) : List String :=
  (m.hostedOn .vocalic s ++ m.hostedOn .consonantal s).map (·.value)

/-- `realizeSlot m s` merges the segments slot `s` hosts onto the first. -/
def realizeSlot (m : AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme)))
    (s : Nat) : Option String :=
  match hosted m s with
  | [] => none
  | x :: xs => some (xs.foldl merge x)

/-- `collapses x l` says that the V-slot realized `x` is followed by a vacant C-slot and a V-slot
realized the same. -/
def collapses (x : String) : List (Slot × Option String) → Bool
  | (c, none) :: (.V, some y) :: _ => c == .C && x == y
  | _ => false

/-- `collapse` lists the realized slots in order, V-slots around a vacant C-slot with the same
realization surfacing once, since "the phonological length of these vowels is not translated to
phonetic length" (13). The flag records that the vowel has already been realized. -/
def collapse : Bool → List (Slot × Option String) → List String
  | _, [] => []
  | skip, (_, none) :: tl => collapse skip tl
  | true, (.V, some _) :: tl => collapse false tl
  | _, (s, some x) :: tl => x :: collapse (s == .V && collapses x tl) tl

/-- Truncation (7a) deletes the final syllable, the final C-slot and the V-slot before it, when the
pattern truncates and that slot is vacant. -/
def truncate (p : Pattern) (m :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))) : Skeleton :=
  match m.unfilledCSlots.max?, m.template.cSlots.max? with
  | some s, some s' =>
    if p.truncates ∧ s = s' then m.template.take (s - 1) else m.template
  | _, _ => m.template

/-- The surface segments of a match in a pattern are the realized slots, a filled prespecified
geminate slot counting twice ({C C} in (7)), between the pattern's outer material. -/
def realize (p : Pattern) (m :
    AR (Multiplanar Plane (Sponsored String Morpheme) (Sponsored Slot Morpheme))) : List String :=
  p.pre ++ collapse false ((truncate p m).zipIdx.flatMap fun (c, i) ↦
    let e := (c, realizeSlot m i)
    if p.geminate = some i ∧ e.2.isSome then [e, e] else [e]) ++ p.post

/-- The surface segments of a root in a pattern. -/
def surface (p : Pattern) (r : ConsonantalRoot String) : List String := realize p (derive p r)

/-- The surface form as characters, for comparison with a transcription. -/
def surfaceChars (p : Pattern) (r : ConsonantalRoot String) : List Char :=
  (surface p r).flatMap String.toList

/-! ### The roots, in the squib's transcription -/

/-- The root √klt of *kalat* 'received'. -/
def klt : ConsonantalRoot String := ⟨["k", "l", "t"]⟩

/-- The root the biradical √kl of *kalal* 'included'. -/
def kl : ConsonantalRoot String := ⟨["k", "l"]⟩

/-- The root √klj of *kala* 'roasted'. -/
def klj : ConsonantalRoot String := ⟨["k", "l", "j"]⟩

/-- The root √dmj of *tadmit*. -/
def dmj : ConsonantalRoot String := ⟨["d", "m", "j"]⟩

/-- The root √glj of *taglit*. -/
def glj : ConsonantalRoot String := ⟨["g", "l", "j"]⟩

/-- The root √rmj of *tarmit*. -/
def rmj : ConsonantalRoot String := ⟨["r", "m", "j"]⟩

/-- The root the t-final √skt of *taskit*. -/
def skt : ConsonantalRoot String := ⟨["s", "k", "t"]⟩

/-- The root Amharic √sbr 'break'. -/
def sbr : ConsonantalRoot String := ⟨["s", "b", "r"]⟩

/-- The root Amharic √wd 'like'. -/
def wd : ConsonantalRoot String := ⟨["w", "d"]⟩

/-- The root Amharic √fdj 'scorch'. -/
def fdj : ConsonantalRoot String := ⟨["f", "d", "j"]⟩

/-- The root Amharic √sma 'hear'. -/
def sma : ConsonantalRoot String := ⟨["s", "m", "a"]⟩

/-- The root Amharic √sam 'kiss'. -/
def sam : ConsonantalRoot String := ⟨["s", "a", "m"]⟩

/-- The root Amharic √hid 'go'. -/
def hid : ConsonantalRoot String := ⟨["h", "i", "d"]⟩

/-! ### Modern Hebrew: the QaTaT–QaTa problem (3)–(4) and taQTiL (9)–(10) -/

/-- The PST.3MSG template CaCaC[+c] ((3)–(4)), vocalization a,a. -/
def hebrewPst : Pattern :=
  { template := [.C, .V, .C, .V, .C], consonantal := [4], category := .verb, vocalism := ["a"],
    vocLines := [(0, 1), (0, 3)] }

/-- The action-noun template QTiLa (3). -/
def hebrewQtila : Pattern :=
  { template := [.C, .C, .V, .C, .V], category := .noun, vocalism := ["i", "a"],
    vocLines := [(0, 2), (1, 4)] }

/-- The passive-participle template QaTuL (3). -/
def hebrewQatul : Pattern :=
  { template := [.C, .V, .C, .V, .C], category := .adjective, vocalism := ["a", "u"],
    vocLines := [(0, 1), (1, 3)] }

/-- The resultative nominal template taQTiL[+c] ((9)–(10)) has its fixed ta before the skeleton. -/
def hebrewTaqtil : Pattern :=
  { template := [.C, .C, .V, .C], consonantal := [3], category := .noun, vocalism := ["i"],
    vocLines := [(0, 2)], pre := ["ta"] }

-- (3a–b), (1)
theorem klt_kl_satisfy :
    (derive hebrewPst klt).allCSlotsFilled ∧ ¬ Misaligned (derive hebrewPst klt) ∧
    (derive hebrewPst kl).allCSlotsFilled ∧ ¬ Misaligned (derive hebrewPst kl) ∧
    (1, 4) ∈ (derive hebrewPst kl).lines (some .consonantal) none := by
  decide

/-- For √klj the final [+c] slot stays vacant, since spreading would misalign the l ((4), (6)). -/
theorem klj_spread_misaligned :
    (derive hebrewPst klj).unfilledCSlots = [4] ∧
    ¬ Misaligned (derive hebrewPst klj) ∧
    Misaligned ((derive hebrewPst klj).spread .consonantal .C) ∧
    realize hebrewPst ((derive hebrewPst klj).spread .consonantal .C) = ["k", "a", "l", "a", "l"] := by
  decide

-- (3c)
theorem klj_qtila_qatul :
    (derive hebrewQtila klj).allCSlotsFilled ∧
    (derive hebrewQatul klj).allCSlotsFilled := by
  decide

-- (10)
theorem dmj_taqtil :
    (associate hebrewTaqtil dmj).unfilledCSlots = [3] ∧
    Misaligned ((associate hebrewTaqtil dmj).spread .consonantal .C) ∧
    (derive hebrewTaqtil dmj).hostedOn .consonantal 3 = [⟨"t", .suffix⟩] ∧
    (derive hebrewTaqtil dmj).allCSlotsFilled ∧
    ¬ Misaligned (derive hebrewTaqtil dmj) := by
  decide

/-! ### Amharic: (5), (7)–(8), (12)–(13) -/

/-- The type A PFV.3MSG stem CäCCäC[+c] ((5), (7)) has its medial C prespecified geminate, its final
slot [+c] and the person suffix -ä outside; a barred glide joins the consonant on its left, and an
unsatisfied final syllable is truncated (7a). -/
def amharicPfv : Pattern :=
  { template := [.C, .V, .C, .V, .C], consonantal := [4], category := .verb, vocalism := ["ä"],
    vocLines := [(0, 1), (0, 3)], post := ["-ä"], geminate := some 2,
    joinsGlide := true, truncates := true }

/-- The GRND stem CäCC[+c] with the subject suffix -o ((5), (8)). -/
def amharicGrnd : Pattern :=
  { template := [.C, .V, .C, .C], consonantal := [3], category := .noun, vocalism := ["ä"],
    vocLines := [(0, 1)], post := ["-o"], joinsGlide := true }

/-- The INF has the prefix mä- and, in Strict CV terms (13), the skeleton CVC[+c]VC[+c] with ä on
the second V-slot. -/
def amharicInf : Pattern :=
  { template := [.C, .V, .C, .V, .C], consonantal := [2, 4], category := .noun,
    vocalism := ["ä"],
    vocLines := [(0, 3)], pre := ["mä"], joinsGlide := true }

-- (7)
theorem fdj_pfv :
    (2, 2) ∈ (derive amharicPfv fdj).lines (some .consonantal) none ∧
    (derive amharicPfv fdj).unfilledCSlots = [4] ∧
    ¬ Misaligned (derive amharicPfv fdj) ∧
    Misaligned ((derive amharicPfv fdj).spread .consonantal .C) := by
  decide

-- (5b) [broselow-1984]
theorem wd_pfv :
    (derive amharicPfv wd).allCSlotsFilled ∧ ¬ Misaligned (derive amharicPfv wd) ∧
    wd.IsOCPClean ∧ ¬ (⟨["w", "d", "d"]⟩ : ConsonantalRoot String).IsOCPClean := by
  decide

-- (8)
theorem fdj_grnd :
    (derive amharicGrnd fdj).hostedOn .consonantal 3 = [⟨"t", .suffix⟩] ∧
    (derive amharicGrnd fdj).allCSlotsFilled ∧
    ¬ Misaligned (derive amharicGrnd fdj) ∧
    (derive amharicGrnd fdj).NoCrossing := by
  decide

-- (13a), (13b–c)
theorem inf_intrusion :
    (associate amharicInf sma).unfilledCSlots = [4] ∧
    (associate amharicInf sam).unfilledCSlots = [2] ∧
    (associate amharicInf hid).unfilledCSlots = [2] ∧
    (derive amharicInf sma).hostedOn .consonantal 4 = [⟨"t", .suffix⟩] ∧
    2 ∉ window ((associate amharicInf sam).lines (some .consonantal) none : SetRel ℕ ℕ) sam.arity ∧
    2 ∉ window ((associate amharicInf hid).lines (some .consonantal) none : SetRel ℕ ℕ) hid.arity ∧
    (derive amharicInf sam).unfilledCSlots = [2] ∧
    (derive amharicInf hid).unfilledCSlots = [2] ∧
    ¬ Misaligned (derive amharicInf sam) ∧
    ¬ Misaligned (derive amharicInf hid) := by
  decide

/-! ### The paradigms (3), (5), (12) and the nouns (9) -/

/-- The languages of the rows. -/
inductive Lang where
  | hebrew
  | amharic
  deriving DecidableEq, Repr

/-- The paradigm cells of (3), (5), (12). -/
inductive Cell where
  | pst3msg
  | actionNoun
  | passPrtc
  | pfv
  | ipfv
  | juss
  | grnd
  | inf
  deriving DecidableEq, Repr

/-- The pattern of a cell, for the cells the squib draws. -/
def Cell.pattern? : Cell → Option Pattern
  | .pst3msg => some hebrewPst
  | .actionNoun => some hebrewQtila
  | .passPrtc => some hebrewQatul
  | .pfv => some amharicPfv
  | .grnd => some amharicGrnd
  | .inf => some amharicInf
  | .ipfv | .juss => none

/-- The cells with a nominal base are the Amharic GRND and INF, whose subjects are marked as
possessors (§4.2), and the Hebrew action noun. -/
def Cell.IsNominal (c : Cell) : Prop := c.pattern?.map Pattern.category = some .noun

instance (c : Cell) : Decidable c.IsNominal := inferInstanceAs (Decidable (_ = _))

/-- A paradigm cell of a root. -/
structure Row where
  lang : Lang
  root : ConsonantalRoot String
  cell : Cell
  form : String
  deriving DecidableEq, Repr

/-- A taQTiL noun (9), with its root where the squib identifies it. -/
structure NounRow where
  form : String
  gender : UD.Gender
  root : Option (ConsonantalRoot String)
  deriving DecidableEq, Repr

def langTable : List (Glottocode × Lang) := [(.modernHebrew, .hebrew), (.amharic, .amharic)]

def rootTable : List (String × ConsonantalRoot String) :=
  [("klt", klt), ("kl", kl), ("klj", klj), ("dmj", dmj),
   ("glj", glj), ("rmj", rmj), ("skt", skt), ("sbr", sbr),
   ("wd", wd), ("fdj", fdj), ("sma", sma), ("sam", sam),
   ("hid", hid)]

/-- `segment l x` reads a letter of the squib's transcription of a root of language `l` as a
segment of that language's fragment. -/
def segment : Lang → String → Phonology.Segment
  | .hebrew, "k" => Hebrew.Phonology.k
  | .hebrew, "l" => Hebrew.Phonology.l
  | .hebrew, "t" => Hebrew.Phonology.t
  | .hebrew, "j" => Hebrew.Phonology.j
  | .hebrew, "d" => Hebrew.Phonology.d
  | .hebrew, "m" => Hebrew.Phonology.m
  | .hebrew, "g" => Hebrew.Phonology.«ɡ»
  | .hebrew, "r" => Hebrew.Phonology.«ʁ»
  | .hebrew, "s" => Hebrew.Phonology.s
  | .amharic, "s" => Amharic.Phonology.s
  | .amharic, "b" => Amharic.Phonology.b
  | .amharic, "r" => Amharic.Phonology.«ɾ»
  | .amharic, "w" => Amharic.Phonology.w
  | .amharic, "d" => Amharic.Phonology.d
  | .amharic, "f" => Amharic.Phonology.f
  | .amharic, "j" => Amharic.Phonology.j
  | .amharic, "m" => Amharic.Phonology.m
  | .amharic, "a" => Amharic.Phonology.a
  | .amharic, "h" => Amharic.Phonology.h
  | .amharic, "i" => Amharic.Phonology.i
  | _, _ => ⊥

theorem fragment_roots :
    [Hebrew.klt, Hebrew.kl, Hebrew.klj, Hebrew.dmj, Hebrew.glj, Hebrew.rmj, Hebrew.skt].map
        (·.map (Arad2005.fillContinuant false)) =
      [klt, kl, klj, dmj, glj, rmj, skt].map (·.map (segment .hebrew)) ∧
    [Amharic.sbr, Amharic.wd, Amharic.fdj, Amharic.sma, Amharic.sam, Amharic.hid] =
      [sbr, wd, fdj, sma, sam, hid].map (·.map (segment .amharic)) :=
  ⟨rfl, rfl⟩

def cellTable : List (String × Cell) :=
  [("pst3msg", .pst3msg), ("actionNoun", .actionNoun), ("passPrtc", .passPrtc), ("pfv", .pfv),
   ("ipfv", .ipfv), ("juss", .juss), ("grnd", .grnd), ("inf", .inf)]

def genderTable : List (String × UD.Gender) := [("masculine", .Masc), ("feminine", .Fem)]

def Row.ofDatum (ex : Datum) : Option Row := do
  let lang ← ex.byLanguage langTable
  let root ← ex.parse? "root" rootTable
  let cell ← ex.parse? "cell" cellTable
  pure ⟨lang, root, cell, ex.primaryText⟩

def NounRow.ofDatum (ex : Datum) : Option NounRow := do
  let gender ← ex.parse? "gender" genderTable
  pure ⟨ex.primaryText, gender, ex.parse? "root" rootTable⟩

theorem row_ofDatum_isSome :
    ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome ∨ (NounRow.ofDatum ex).isSome := by
  decide

def rows : List Row := Examples.all.filterMap Row.ofDatum

def nounRows : List NounRow := Examples.all.filterMap NounRow.ofDatum

/-- The surface form the pipeline derives for a row, where its cell has a pattern. -/
def Row.surface? (r : Row) : Option (List Char) := r.cell.pattern?.map (surfaceChars · r.root)

/-- The derivation reproduces every patterned cell of (3), (5), (12) except the PFV of √sma. -/
theorem rows_surface :
    ∀ r ∈ rows, r.cell.pattern?.isSome → (r.root, r.cell) ≠ (sma, .pfv) →
      r.surface? = some r.form.toList := by
  decide

-- (3)
theorem j_surfaces :
    ∀ r ∈ rows, r.lang = .hebrew →
      ('j' ∈ r.form.toList ↔ r.root = klj ∧ r.cell ≠ .pst3msg) := by
  decide

/-- A root's final radical is barred from a [+c] slot when it is a glide, as in √klj and √fdj, or a
vowel, as in √sma. -/
def BarredFinal (r : ConsonantalRoot String) : Prop :=
  match r.segments.getLast? with
  | some x => segClass x ≠ .consonant
  | none => False

instance (r : ConsonantalRoot String) : Decidable (BarredFinal r) := by
  unfold BarredFinal; split <;> infer_instance

/-- In Amharic (5) and (12), a nonradical [t] occurs exactly in the nominal cells of roots with a
barred final radical (§2.2, §4.2, against [broselow-1984]). -/
theorem intruder_distribution :
    ∀ r ∈ rows, r.lang = .amharic →
      ('t' ∈ r.form.toList ∧ "t" ∉ r.root.segments ↔ r.cell.IsNominal ∧ BarredFinal r.root) := by
  decide

-- (9)
theorem masculine_of_not_t_final :
    ∀ r ∈ nounRows, r.form.toList.getLast? ≠ some 't' → r.gender = .Masc := by
  decide

/-- The taQTiL derivation of a noun's root reproduces the noun, and the noun is feminine iff the
derivation merged the feminine morph, so [taskit] from t-final √skt is masculine and the nouns from
j-final roots feminine (9b). -/
def NounRow.Derived (r : NounRow) : Prop :=
  match r.root with
  | some ρ =>
    surfaceChars hebrewTaqtil ρ = r.form.toList ∧
      (r.gender = .Fem ↔ ∃ x ∈ ((derive hebrewTaqtil ρ).word (some .consonantal)), x.morpheme =
          .suffix)
  | none => True

instance (r : NounRow) : Decidable r.Derived := by
  unfold NounRow.Derived; split <;> infer_instance

theorem nounRows_derived : ∀ r ∈ nounRows, r.Derived := by decide

end Faust2026
