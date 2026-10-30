module

public import Linglib.Morphology.Morphotactics.Association
public import Linglib.Fragments.Amharic.ConsonantalRoots
public import Studies.Arad2005
public import Linglib.Syntax.Gender.Basic
public import Linglib.Data.Examples.Faust2026
public import Linglib.Data.Examples.Readers

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

variable {α : Type*}

/-! ### *Misalignment -/

/-- `Misaligned m` holds when some nonfinal root element is associated to the template-final slot,
which *Misalignment (2), (6b) bans. -/
def Misaligned (m : TemplateMatch α) : Prop :=
  ∃ a ∈ m.associations,
    a.source = .root ∧ m.root.IsNonfinal a.melodyIndex ∧ a.slotIndex + 1 = m.template.length

instance (m : TemplateMatch α) : Decidable (Misaligned m) :=
  inferInstanceAs (Decidable (∃ a ∈ m.associations, _))

theorem misaligned_append (m : TemplateMatch α) (l : List Association) :
    Misaligned { m with associations := m.associations ++ l } ↔
      Misaligned m ∨ ∃ a ∈ l, a.source = .root ∧ m.root.IsNonfinal a.melodyIndex ∧
        a.slotIndex + 1 = m.template.length := by
  simp only [Misaligned, List.mem_append, or_and_right, exists_or]

-- (8), (10)
theorem misaligned_append_affix (m : TemplateMatch α) (l : List Association)
    (h : ∀ a ∈ l, a.source = .affix) :
    Misaligned { m with associations := m.associations ++ l } ↔ Misaligned m := by
  rw [misaligned_append, or_iff_left]
  rintro ⟨a, ha, hr, -⟩
  exact absurd (h a ha) (by rw [hr]; decide)

/-! ### Segments, patterns, and association -/

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
  vocLines : List Association := []
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

/-- The root associated with the C-slots by the conventions, one to one from left to right
with the final radical spreading onto leftover slots, plus the pattern's vocalization lines. -/
def lines (p : Pattern) (r : ConsonantalRoot String) : TemplateMatch String :=
  (({ root := r, vocalism := p.vocalism, template := p.template, associations := [] } :
    TemplateMatch String).associate .root).link p.vocLines

/-- `m.Admits a` says that the slot's specification admits the segment. A [+c] slot hosts consonants
only ((4), (7), (13)), and a plain C-slot anything but a vowel. -/
def Admits (p : Pattern) (m : TemplateMatch String) (a : Association) : Prop :=
  match m.template[a.slotIndex]?, m.segmentAt a with
  | some .C, some x =>
    if a.slotIndex ∈ p.consonantal then segClass x = .consonant else segClass x ≠ .vowel
  | _, _ => True

instance (p : Pattern) (m : TemplateMatch String) (a : Association) :
    Decidable (Admits p m a) := by
  unfold Admits; split <;> infer_instance

/-- The V-slots flanking slot `i`. -/
def flankingV (m : TemplateMatch String) (i : Nat) : List Nat :=
  [i - 1, i + 1].filter fun s ↦ m.template[s]? = some .V

/-- The vocalization line at slot `s`. -/
def vocAt (m : TemplateMatch String) (s : Nat) : Option Association :=
  m.associations.find? fun a ↦ a.source == .vocalism && a.slotIndex == s

/-- `join` places a barred root element. A glide joins the slot of the consonant on its left where
the pattern's language does that, Amharic and not Hebrew (7). A nonconsonantal radical merges with
the vocalization on the V-slots flanking its slot, the vocalization element spreading to a flanking
V-slot it did not occupy, so that the merger "occupies the two vocalic positions around the C
position" (13b–c). -/
def join (p : Pattern) (m : TemplateMatch String) (a : Association) : TemplateMatch String :=
  match (m.segmentAt a).map segClass with
  | some .glide =>
    if p.joinsGlide then
      match m.leftLine .root a.slotIndex with
      | some b =>
        { m with associations := m.associations ++ [⟨.root, a.melodyIndex, b.slotIndex⟩] }
      | none => m
    else m
  | some .vowel =>
    let vs := flankingV m a.slotIndex
    match vs.findSome? (vocAt m) with
    | some v =>
      { m with associations := m.associations ++ vs.map (fun s ↦ ⟨.root, a.melodyIndex, s⟩) ++
          (vs.filter fun s ↦ (vocAt m s).isNone).map fun s ↦ ⟨.vocalism, v.melodyIndex, s⟩ }
    | none => m
  | _ => m

/-- Association under the slot specifications removes the rejected lines and joins or merges their
elements as the pattern's language allows. -/
def associate (p : Pattern) (r : ConsonantalRoot String) : TemplateMatch String :=
  let m := lines p r
  (m.associations.filter fun a ↦ ¬ Admits p m a).foldl (join p)
    { m with associations := m.associations.filter (Admits p m ·) }

/-! ### Intrusion -/

/-- The consonantal melody of a base merged with a suffix, root elements then the suffix's, in
the coordinates of `Autosegmental.IsNonCrossing`. -/
def melodyLinks (m : TemplateMatch String) : Finset (Nat × Nat) :=
  m.links .root ∪ (m.links .affix).image fun p ↦ (p.1 + m.root.arity, p.2)

/-- The feminine morph √(a)t merged with the base, its consonant associated to slot `s`. -/
def intrudeAt (m : TemplateMatch String) (s : Nat) : TemplateMatch String :=
  { m with affix := ["t"], associations := m.associations ++ [⟨.affix, 0, s⟩] }

theorem melodyLinks_intrudeAt (m : TemplateMatch String) (s : Nat) :
    melodyLinks (intrudeAt m s) = insert (m.root.arity, s) (melodyLinks m) := by
  ext p
  simp [melodyLinks, intrudeAt, TemplateMatch.links, List.filter_append]

/-- Intrusion (10b–c) associates the morph's consonant from right to left to the rightmost vacant
C-slot, provided that slot lies in its window, so that its line crosses none of the root's;
otherwise the consonant floats (13b–c). -/
def intrude (m : TemplateMatch String) : TemplateMatch String :=
  match m.unfilledCSlots.max? with
  | some s =>
    if s ∈ window (melodyLinks m : SetRel ℕ ℕ) m.root.arity then intrudeAt m s
    else { m with affix := ["t"] }
  | none => { m with affix := ["t"] }

theorem misaligned_intrudeAt (m : TemplateMatch String) (s : Nat) :
    Misaligned (intrudeAt m s) ↔ Misaligned m :=
  misaligned_append_affix m [⟨.affix, 0, s⟩] (by simp)

-- (8), (10)
theorem misaligned_intrude (m : TemplateMatch String) : Misaligned (intrude m) ↔ Misaligned m := by
  unfold intrude
  split
  · split
    · exact misaligned_intrudeAt m _
    · exact Iff.rfl
  · exact Iff.rfl

/-- The intruder's line never crosses a root line, so intrusion keeps the merged melody
non-crossing. -/
theorem isNonCrossing_melodyLinks_intrude (m : TemplateMatch String)
    (h : IsNonCrossing (melodyLinks m : SetRel ℕ ℕ)) :
    IsNonCrossing (melodyLinks (intrude m) : SetRel ℕ ℕ) := by
  unfold intrude
  split
  · split
    · rw [melodyLinks_intrudeAt, Finset.coe_insert, isNonCrossing_insert_iff_mem_window]
      exact ⟨h, ‹_›⟩
    · exact h
  · exact h

/-- The derivation of a root in a pattern is association under the slot specifications followed, for
a nominal base whose template is unsatisfied, by merger of the feminine morph ((10b), (11)). -/
def derive (p : Pattern) (r : ConsonantalRoot String) : TemplateMatch String :=
  let m := associate p r
  if p.category = .noun ∧ ¬ m.allCSlotsFilled then intrude m else m

-- (11)
theorem derive_of_category_ne_noun (p : Pattern) (r : ConsonantalRoot String)
    (h : p.category ≠ .noun) : derive p r = associate p r := by
  simp [derive, h]

/-! ### Realization -/

/-- `hosted m s` lists the segments slot `s` hosts, vocalization first, then root, then affix lines.
-/
def hosted (m : TemplateMatch String) (s : Nat) : List String :=
  [AssocSource.vocalism, .root, .affix].flatMap fun src ↦
    (m.associations.filter fun a ↦ a.source == src && a.slotIndex == s).filterMap m.segmentAt

/-- `realizeSlot m s` merges the segments slot `s` hosts onto the first. -/
def realizeSlot (m : TemplateMatch String) (s : Nat) : Option String :=
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
def truncate (p : Pattern) (m : TemplateMatch String) : Skeleton :=
  match m.unfilledCSlots.max?, m.template.cSlots.max? with
  | some s, some s' =>
    if p.truncates ∧ s = s' then m.template.take (s - 1) else m.template
  | _, _ => m.template

/-- The surface segments of a match in a pattern are the realized slots, a filled prespecified
geminate slot counting twice ({C C} in (7)), between the pattern's outer material. -/
def realize (p : Pattern) (m : TemplateMatch String) : List String :=
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
    vocLines := [⟨.vocalism, 0, 1⟩, ⟨.vocalism, 0, 3⟩] }

/-- The action-noun template QTiLa (3). -/
def hebrewQtila : Pattern :=
  { template := [.C, .C, .V, .C, .V], category := .noun, vocalism := ["i", "a"],
    vocLines := [⟨.vocalism, 0, 2⟩, ⟨.vocalism, 1, 4⟩] }

/-- The passive-participle template QaTuL (3). -/
def hebrewQatul : Pattern :=
  { template := [.C, .V, .C, .V, .C], category := .adjective, vocalism := ["a", "u"],
    vocLines := [⟨.vocalism, 0, 1⟩, ⟨.vocalism, 1, 3⟩] }

/-- The resultative nominal template taQTiL[+c] ((9)–(10)) has its fixed ta before the skeleton. -/
def hebrewTaqtil : Pattern :=
  { template := [.C, .C, .V, .C], consonantal := [3], category := .noun, vocalism := ["i"],
    vocLines := [⟨.vocalism, 0, 2⟩], pre := ["ta"] }

-- (3a–b), (1)
theorem klt_kl_satisfy :
    (derive hebrewPst klt).allCSlotsFilled ∧ ¬ Misaligned (derive hebrewPst klt) ∧
    (derive hebrewPst kl).allCSlotsFilled ∧ ¬ Misaligned (derive hebrewPst kl) ∧
    ⟨.root, 1, 4⟩ ∈ (derive hebrewPst kl).associations := by
  decide

/-- For √klj the final [+c] slot stays vacant, since spreading would misalign the l ((4), (6)). -/
theorem klj_spread_misaligned :
    (derive hebrewPst klj).unfilledCSlots = [4] ∧
    ¬ Misaligned (derive hebrewPst klj) ∧
    Misaligned ((derive hebrewPst klj).spread .root) ∧
    realize hebrewPst ((derive hebrewPst klj).spread .root) = ["k", "a", "l", "a", "l"] := by
  decide

-- (3c)
theorem klj_qtila_qatul :
    (derive hebrewQtila klj).allCSlotsFilled ∧
    (derive hebrewQatul klj).allCSlotsFilled := by
  decide

-- (10)
theorem dmj_taqtil :
    (associate hebrewTaqtil dmj).unfilledCSlots = [3] ∧
    Misaligned ((associate hebrewTaqtil dmj).spread .root) ∧
    ⟨.affix, 0, 3⟩ ∈ (derive hebrewTaqtil dmj).associations ∧
    (derive hebrewTaqtil dmj).allCSlotsFilled ∧
    ¬ Misaligned (derive hebrewTaqtil dmj) := by
  decide

/-! ### Amharic: (5), (7)–(8), (12)–(13) -/

/-- The type A PFV.3MSG stem CäCCäC[+c] ((5), (7)) has its medial C prespecified geminate, its final
slot [+c] and the person suffix -ä outside; a barred glide joins the consonant on its left, and an
unsatisfied final syllable is truncated (7a). -/
def amharicPfv : Pattern :=
  { template := [.C, .V, .C, .V, .C], consonantal := [4], category := .verb, vocalism := ["ä"],
    vocLines := [⟨.vocalism, 0, 1⟩, ⟨.vocalism, 0, 3⟩], post := ["-ä"], geminate := some 2,
    joinsGlide := true, truncates := true }

/-- The GRND stem CäCC[+c] with the subject suffix -o ((5), (8)). -/
def amharicGrnd : Pattern :=
  { template := [.C, .V, .C, .C], consonantal := [3], category := .noun, vocalism := ["ä"],
    vocLines := [⟨.vocalism, 0, 1⟩], post := ["-o"], joinsGlide := true }

/-- The INF has the prefix mä- and, in Strict CV terms (13), the skeleton CVC[+c]VC[+c] with ä on
the second V-slot. -/
def amharicInf : Pattern :=
  { template := [.C, .V, .C, .V, .C], consonantal := [2, 4], category := .noun,
    vocalism := ["ä"],
    vocLines := [⟨.vocalism, 0, 3⟩], pre := ["mä"], joinsGlide := true }

-- (7)
theorem fdj_pfv :
    ⟨.root, 2, 2⟩ ∈ (derive amharicPfv fdj).associations ∧
    (derive amharicPfv fdj).unfilledCSlots = [4] ∧
    ¬ Misaligned (derive amharicPfv fdj) ∧
    Misaligned ((derive amharicPfv fdj).spread .root) := by
  decide

-- (5b) [broselow-1984]
theorem wd_pfv :
    (derive amharicPfv wd).allCSlotsFilled ∧ ¬ Misaligned (derive amharicPfv wd) ∧
    wd.IsOCPClean ∧ ¬ (⟨["w", "d", "d"]⟩ : ConsonantalRoot String).IsOCPClean := by
  decide

-- (8)
theorem fdj_grnd :
    ⟨.affix, 0, 3⟩ ∈ (derive amharicGrnd fdj).associations ∧
    (derive amharicGrnd fdj).allCSlotsFilled ∧
    ¬ Misaligned (derive amharicGrnd fdj) ∧
    IsNonCrossing (melodyLinks (derive amharicGrnd fdj) : SetRel ℕ ℕ) := by
  decide

-- (13a), (13b–c)
theorem inf_intrusion :
    (associate amharicInf sma).unfilledCSlots = [4] ∧
    (associate amharicInf sam).unfilledCSlots = [2] ∧
    (associate amharicInf hid).unfilledCSlots = [2] ∧
    ⟨.affix, 0, 4⟩ ∈ (derive amharicInf sma).associations ∧
    2 ∉ window (melodyLinks (associate amharicInf sam)) sam.arity ∧
    2 ∉ window (melodyLinks (associate amharicInf hid)) hid.arity ∧
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

def langTable : List (String × Lang) := [("hebr1245", .hebrew), ("amha1245", .amharic)]

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
  let lang ← List.lookup ex.language langTable
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
      (r.gender = .Fem ↔ (derive hebrewTaqtil ρ).affix ≠ [])
  | none => True

instance (r : NounRow) : Decidable r.Derived := by
  unfold NounRow.Derived; split <;> infer_instance

theorem nounRows_derived : ∀ r ∈ nounRows, r.Derived := by decide

end Faust2026
