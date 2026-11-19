module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Indices
public import Linglib.Phonology.OptimalityTheory.Constraint.ForbiddenFactors
public import Linglib.Phonology.OptimalityTheory.Filtration
public import Linglib.Data.Wordlist.McCarthy2005
public import Studies.Benua1997
public import Linglib.Core.Data.List.OffDiag

/-!
# McCarthy (2005): Optimal Paradigms

This file formalizes optimal paradigms after [mccarthy-2005]. Entire inflectional paradigms
are candidates: markedness and input–output faithfulness are summed over the members, and
the stem of every member stands in a correspondence relation with the stem of every other,
with no distinguished base, the symmetric counterpart of the base priority of [benua-1997],
which optimal paradigms leave to derivational morphology. Faithfulness on that relation
resists alternation within the paradigm, and three consequences follow from the architecture
alone: overapplication only, attraction to the unmarked, and majority rules. A paradigm
carries the shared input and its members with their cells, surface stems, and input–stem
indices (`Paradigm`), two stems are related where their segments are coindexed, symmetrically
and with no base, and `markedness`, `ioFaith`, and
`opFaith` sum a constraint over the members or the ordered member pairs. The Classical
Arabic tableaux for the right and left edges of the verb stem and for geminate verbs, the
Moroccan nouns and majority-rules paradigm, and the Hebrew jussive paradigms of Benua are rerun
under the paper's ranking.

## Implementation notes

* In the paper each candidate paradigm brings its own relation ℜ_OP between the stems. Here the
  relation is computed from the members' input–stem correspondences (`Correspondence.through`):
  two positions correspond when they realise the same input position or are epenthetic at the
  same site, so that the epenthetic vowels of ⟨faʕila, faʕiltu⟩ correspond and those of
  ⟨faʕla, faʕiltu⟩ do not. Candidates that differ only in ℜ_OP are not represented.

## References

* [mccarthy-2005]: the Moroccan nouns (30) (pp. 202–203)
* [benua-1997]
-/

@[expose] public section

namespace McCarthy2005

open OptimalityTheory

variable {α ι : Type*}

/-! ### Paradigms as candidates -/

/-- A paradigm member: its inflectional cell and its surface stem, each segment with the
indices it bears. -/
structure Member (α ι : Type*) where
  cell : ι
  stem : List (Correspondence.Segment α)

/-- A candidate paradigm (2a): the inflected forms of one input stem. -/
structure Paradigm (α ι : Type*) where
  input : List α
  members : List (Member α ι)

/-- A markedness constraint on the word of each cell, summed over the members (2b). -/
def markedness (m : ι → List α → ℕ) : Constraint (Paradigm α ι) :=
  fun P ↦ (P.members.map fun x ↦ m x.cell (x.stem.map (·.seg))).sum

/-- An input–output faithfulness constraint summed over the members (2b), the input indexed
by position. -/
def ioFaith (f : (s t : List (Correspondence.Segment α)) → ℕ) : Constraint (Paradigm α ι) :=
  fun P ↦ (P.members.map fun m ↦ f (Correspondence.indexed P.input) m.stem).sum

/-- An OP faithfulness constraint (2d): a correspondence constraint between two stems, ℛ_OP
(2c) relating their coindexed segments, summed over the ordered pairs of distinct members. -/
def opFaith (f : (s t : List (Correspondence.Segment α)) → ℕ) : Constraint (Paradigm α ι) :=
  fun P ↦ (P.members.offDiag.map fun p ↦ f p.1.stem p.2.stem).sum

section

variable (f : (s t : List (Correspondence.Segment α)) → ℕ) {input : List α}
  {l₁ l₂ : List (Member α ι)}

-- OP faithfulness does not depend on the order of the members.
theorem opFaith_perm (h : l₁.Perm l₂) : opFaith f ⟨input, l₁⟩ = opFaith f ⟨input, l₂⟩ :=
  (h.offDiag.map _).sum_eq

/-- A paradigm whose members fall into two classes, alike within a class and `k` marks apart
across them in the two directions together, draws `k` marks for each pair of members of
different classes. -/
theorem opFaith_append {k : ℕ}
    (h₁ : ∀ x ∈ l₁, ∀ y ∈ l₁, f x.stem y.stem = 0)
    (h₂ : ∀ x ∈ l₂, ∀ y ∈ l₂, f x.stem y.stem = 0)
    (h : ∀ x ∈ l₁, ∀ y ∈ l₂, f x.stem y.stem + f y.stem x.stem = k) :
    opFaith f ⟨input, l₁ ++ l₂⟩ = l₁.length * l₂.length * k := by
  have hrow : ∀ x ∈ l₁, (l₂.map fun y ↦ f x.stem y.stem + f y.stem x.stem).sum =
      l₂.length * k :=
    fun x hx ↦ by
      rw [List.map_congr_left (h x hx), List.map_const', List.sum_replicate, smul_eq_mul]
  rw [opFaith, List.sum_map_offDiag_append, List.sum_map_offDiag_eq_zero h₁,
    List.sum_map_offDiag_eq_zero h₂, List.map_congr_left hrow, List.map_const',
    List.sum_replicate, smul_eq_mul, zero_add, zero_add, mul_assoc]

end

/-- The candidate paradigms of a tableau. -/
inductive Cand
  | a | b | c | d | e
  deriving DecidableEq, Repr

/-! ### Palatalization before *-i* (§8.2)

From /mat/ with the plural suffix *-i*, the paradigm ⟨mat, maʧi⟩ draws two OP-IDENT(high)
marks, one on each direction of ℛ_OP, and ⟨ma, maʧi⟩ one OP-MAX and one OP-DEP mark (fn. 5). -/

namespace Palatalization

inductive Seg
  | m | a | t | ch | i
  deriving DecidableEq, Repr

/-- The feature distinguishing *t* from *ʧ*. -/
def high : Seg → Option Bool
  | .t => some false
  | .ch => some true
  | _ => none

/-- ⟨mat, maʧi⟩. -/
def mat : Paradigm Seg (List Seg) :=
  ⟨[.m, .a, .t], [⟨[], Correspondence.indexed [.m, .a, .t]⟩,
    ⟨[.i], Correspondence.indexed [.m, .a, .ch]⟩]⟩

example : opFaith (Correspondence.Segment.identViol high) mat = 2 := by decide +kernel

/-- ⟨ma, maʧi⟩. -/
def ma : Paradigm Seg (List Seg) :=
  ⟨[.m, .a, .t], [⟨[], Correspondence.indexed [.m, .a]⟩,
    ⟨[.i], Correspondence.indexed [.m, .a, .ch]⟩]⟩

example : opFaith (Correspondence.Segment.maxViol) ma = 1 ∧
    opFaith (Correspondence.Segment.depViol) ma = 1 := by
  decide +kernel

end Palatalization

/-! ### Arabic syllables and feet

The markedness constraints of §8.4 read syllable weight and foot structure. Each vowel is a
nucleus, long or short by `weight`; the consonants before a vowel but the last, its onset,
close the preceding syllable. Feet are right-to-left moraic trochees with the final
syllable extrametrical, as the paper assumes; SWP marks a stressed light syllable, so an
(LL) foot. -/

namespace Arabic

inductive Seg
  | f | ayn | l | s | sh | t | j | k | b | n | m | r | hh | g | d | ch | x | q | w | z | zh | gh
  | mw | a | aa | i | ii | u | schwa
  deriving DecidableEq, Repr

def IsVowel (c : Seg) : Prop := c ∈ [Seg.a, .aa, .i, .ii, .u, .schwa]

instance : DecidablePred IsVowel := fun c ↦ inferInstanceAs (Decidable (c ∈ _))

/-- The weight of a vowel: long or short. -/
def weight : Seg → Option Bool
  | .aa | .ii => some true
  | .a | .i | .u | .schwa => some false
  | _ => none

/-- A syllable by its nucleus and coda. -/
structure Syllable where
  nucleus : Seg
  coda : List Seg
  deriving DecidableEq, Repr

def Syllable.moras (σ : Syllable) : ℕ :=
  (if weight σ.nucleus = some true then 2 else 1) + σ.coda.length

/-- Close the latest syllable with `coda`. -/
def closeLast (coda : List Seg) : List Syllable → List Syllable
  | [] => []
  | σ :: σs => { σ with coda := coda } :: σs

/-- The syllables of a word, latest first: a vowel opens a syllable, the consonants pending
before it but its onset close the previous one, and the final consonants close the last. -/
def syllabifyRev : List Syllable → List Seg → List Seg → List Syllable
  | σs, pending, [] => closeLast pending σs
  | σs, pending, c :: rest =>
    if IsVowel c then syllabifyRev (⟨c, []⟩ :: closeLast pending.dropLast σs) [] rest
    else syllabifyRev σs (pending ++ [c]) rest

def syllabify (w : List Seg) : List Syllable := (syllabifyRev [] [] w).reverse

/-- Right-to-left moraic trochees over syllables listed latest first, carrying a light
syllable awaiting a partner: a heavy syllable is a foot, two light syllables are a foot, a
lone light syllable is unparsed. -/
def footRev (pending : Option Syllable) : List Syllable → List (List Syllable)
  | [] => []
  | σ :: rest =>
    if 2 ≤ σ.moras then [σ] :: footRev none rest
    else
      match pending with
      | none => footRev (some σ) rest
      | some σ₀ => [σ, σ₀] :: footRev none rest

/-- The feet of a word, the final syllable extrametrical unless nothing else can be footed
(fn. 22). -/
def feet (w : List Seg) : List (List Syllable) :=
  match footRev none (syllabifyRev [] [] w).tail with
  | [] => footRev none (syllabifyRev [] [] w)
  | fs => fs

/-- SWP: stressed light syllables, the heads of (LL) feet. -/
def swp (w : List Seg) : ℕ := ((feet w).filter fun ft ↦ ft.length = 2).length

/-- Superheavy syllables, parsed with a moraic coda (\*µµµ]σ) or a syllable appendix
(\*APP-σ). -/
def superheavy (w : List Seg) : ℕ := ((syllabify w).filter fun σ ↦ 3 ≤ σ.moras).length

/-- ALIGN-L(Stem, σ): a stem-initial consonant before another is never syllable-initial. -/
def alignL : List Seg → ℕ
  | c₁ :: c₂ :: _ => if ¬IsVowel c₁ ∧ ¬IsVowel c₂ then 1 else 0
  | _ => 0

/-- \*.CᵢV.CᵢV: identical consonants in the onsets of successive syllables. -/
def identicalOnsets : List Seg → ℕ
  | c :: v :: c' :: v' :: rest =>
    (if ¬IsVowel c ∧ IsVowel v ∧ c = c' ∧ IsVowel v' then 1 else 0)
      + identicalOnsets (v :: c' :: v' :: rest)
  | _ => 0

/-- An inflectional cell of the Classical Arabic verb or noun: its affixes, and whether a
superheavy coda is parsed as an appendix. -/
structure Cell where
  prefixes : List Seg := []
  suffixes : List Seg := []
  appendix : Bool := false
  deriving DecidableEq, Repr

/-- The word of a stem in a cell. -/
def Cell.word (c : Cell) (stem : List Seg) : List Seg := c.prefixes ++ stem ++ c.suffixes

/-! ### The Classical Arabic verb (§8.4)

Verb stems end in CVC] and may begin with [CCV; noun stems may end in CVːC] or CVCC] and
begin only with [CV. Verbs alone have C-initial suffixes and CV- prefixes: before a
C-initial suffix a superheavy coda is shortened or broken up and OP faithfulness carries the
repair through the paradigm; after a CV- prefix SWP blocks the epenthesis that alignment
would force into a stem-initial cluster, and OP faithfulness carries the blocking to the
unprefixed forms. The noun's one-member paradigms leave each form to markedness alone. -/

/-- \*µµµ]σ. -/
def starTrimoraic : Constraint (Paradigm Seg Cell) :=
  markedness fun c s ↦ if c.appendix then 0 else superheavy (c.word s)

/-- \*APP-σ. -/
def starAppendix : Constraint (Paradigm Seg Cell) :=
  markedness fun c s ↦ if c.appendix then superheavy (c.word s) else 0

def swpParadigm : Constraint (Paradigm Seg Cell) := markedness fun c s ↦ swp (c.word s)

def alignLParadigm : Constraint (Paradigm Seg Cell) := markedness fun _ s ↦ alignL s

def opDepV : Constraint (Paradigm Seg Cell) := opFaith (Correspondence.Segment.depViolOn IsVowel)

def opIdentWt : Constraint (Paradigm Seg Cell) :=
  opFaith (Correspondence.Segment.identViol weight)

def ioDepV : Constraint (Paradigm Seg Cell) := ioFaith (Correspondence.Segment.depViolOn IsVowel)

def ioMaxV : Constraint (Paradigm Seg Cell) := ioFaith (Correspondence.Segment.maxViolOn IsVowel)

def ioMaxC : Constraint (Paradigm Seg Cell) :=
  ioFaith (Correspondence.Segment.maxViolOn (fun c ↦ ¬IsVowel c))

def ioIdentWt : Constraint (Paradigm Seg Cell) :=
  ioFaith (Correspondence.Segment.identViol weight)

/-- The summary ranking (21): IO-MAX-V, OP-DEP-V, \*µµµ]σ, \*APP-σ, IO-MAX-C, OP-IDENT-WT >>
SWP >> ALIGN-L(Stem, σ) >> IO-DEP-V >> IO-IDENT-WT. -/
def ranking : List (Constraint (Paradigm Seg Cell)) :=
  [ioMaxV, opDepV, starTrimoraic, starAppendix, ioMaxC, opIdentWt, swpParadigm, alignLParadigm,
   ioDepV, ioIdentWt]

/-- The 3sg.m. perfective, suffix *-a*. -/
def perfective : Cell := { suffixes := [.a] }

/-- The 1sg perfective, suffix *-tu*. -/
def perfective1 : Cell := { suffixes := [.t, .u] }

/-- The 3sg.m. imperfective, *ja-* … *-u*. -/
def imperfective : Cell := { prefixes := [.j, .a], suffixes := [.u] }

/-- The 3pl.f. imperfective, *ja-* … *-na*. -/
def imperfectiveF : Cell := { prefixes := [.j, .a], suffixes := [.n, .a] }

/-- The paradigms of /faʕaːl/ in (12): shortened throughout, long throughout with the
superheavy coda an appendix or moraic, or alternating. -/
def long : Cand → Paradigm Seg Cell
  | .a => ⟨input, [⟨perfective, short⟩, ⟨perfective1, short⟩]⟩
  | .b => ⟨input, [⟨perfective, faithful⟩, ⟨{ perfective1 with appendix := true }, faithful⟩]⟩
  | .c => ⟨input, [⟨perfective, faithful⟩, ⟨perfective1, faithful⟩]⟩
  | _ => ⟨input, [⟨perfective, faithful⟩, ⟨perfective1, short⟩]⟩
where
  input : List Seg := [.f, .a, .ayn, .aa, .l]
  faithful : List (Correspondence.Segment Seg) := Correspondence.indexed input
  short : List (Correspondence.Segment Seg) := Correspondence.indexed [.f, .a, .ayn, .a, .l]

-- (12)
theorem shortening_overapplies :
    Constraint.evalOn long {.a, .b, .c, .d} ranking = {.a} := by
  decide +kernel

/-- The paradigms of /faʕl/ in (13): epenthesis throughout, the cluster kept throughout with
the superheavy coda an appendix or moraic, or alternating. -/
def cluster : Cand → Paradigm Seg Cell
  | .a => ⟨input, [⟨perfective, epenthesized⟩, ⟨perfective1, epenthesized⟩]⟩
  | .b => ⟨input, [⟨perfective, faithful⟩, ⟨{ perfective1 with appendix := true }, faithful⟩]⟩
  | .c => ⟨input, [⟨perfective, faithful⟩, ⟨perfective1, faithful⟩]⟩
  | _ => ⟨input, [⟨perfective, faithful⟩, ⟨perfective1, epenthesized⟩]⟩
where
  input : List Seg := [.f, .a, .ayn, .l]
  faithful : List (Correspondence.Segment Seg) := Correspondence.indexed input
  /-- A vowel epenthesized into the final cluster. -/
  epenthesized : List (Correspondence.Segment Seg) := faithful.insertIdx 3 (.ofIndex .i 4)

-- (13)
theorem epenthesis_overapplies :
    Constraint.evalOn cluster {.a, .b, .c, .d} ranking = {.a} := by
  decide +kernel

/-- The paradigms of /faʕal/ in (17): the (LL) feet kept, or syncopated. -/
def syncope : Cand → Paradigm Seg Cell
  | .a => ⟨input, [⟨{ suffixes := [.u] }, faithful⟩, ⟨perfective, faithful⟩]⟩
  | _ => ⟨input, [⟨{ suffixes := [.u] }, syncopated⟩, ⟨perfective, syncopated⟩]⟩
where
  input : List Seg := [.f, .a, .ayn, .a, .l]
  faithful : List (Correspondence.Segment Seg) := Correspondence.indexed input
  syncopated : List (Correspondence.Segment Seg) := faithful.eraseIdx 3

-- (17)
theorem no_syncope : Constraint.evalOn syncope {.a, .b} ranking = {.a} := by decide +kernel

/-- The noun /fʕal/ with the case suffixes in (24): epenthesis, or the initial cluster. -/
def noun : Cand → Paradigm Seg Cell
  | .a => ⟨input, cases.map fun v ↦ ⟨{ suffixes := [v] }, faithful.insertIdx 1 (.ofIndex .i 4)⟩⟩
  | _ => ⟨input, cases.map fun v ↦ ⟨{ suffixes := [v] }, faithful⟩⟩
where
  input : List Seg := [.f, .ayn, .a, .l]
  cases : List Seg := [.u, .a, .i]
  faithful : List (Correspondence.Segment Seg) := Correspondence.indexed input

-- (24)
theorem noun_epenthesis : Constraint.evalOn noun {.a, .b} ranking = {.a} := by
  decide +kernel

/-- The four representative cells of a verbal paradigm: the perfectives *-a*, *-tu* and the
imperfectives *ja-…-u*, *ja-…-na*. -/
def verbal (pfA pfTu impfU impfNa : Member Seg Cell) : List (Member Seg Cell) :=
  [pfA, pfTu, impfU, impfNa]

/-- The paradigms of the eighth conjugation /ftaʕal/ in (19) and (25): the initial cluster
kept throughout, epenthesis throughout, or epenthesis in the unprefixed forms only. -/
def eighth : Cand → Paradigm Seg Cell
  | .a => ⟨input, verbal ⟨perfective, faithful⟩ ⟨perfective1, faithful⟩
      ⟨imperfective, ablaut⟩ ⟨imperfectiveF, ablaut⟩⟩
  | .b => ⟨input, verbal ⟨perfective, epenthesized faithful⟩
      ⟨perfective1, epenthesized faithful⟩ ⟨imperfective, epenthesized ablaut⟩
      ⟨imperfectiveF, epenthesized ablaut⟩⟩
  | _ => ⟨input, verbal ⟨perfective, epenthesized faithful⟩
      ⟨perfective1, epenthesized faithful⟩ ⟨imperfective, ablaut⟩ ⟨imperfectiveF, ablaut⟩⟩
where
  input : List Seg := [.f, .t, .a, .ayn, .a, .l]
  faithful : List (Correspondence.Segment Seg) := Correspondence.indexed input
  /-- The imperfective stem vowel. -/
  ablaut : List (Correspondence.Segment Seg) :=
    Correspondence.indexed [.f, .t, .a, .ayn, .i, .l]
  /-- A vowel epenthesized into the initial cluster. -/
  epenthesized (s : List (Correspondence.Segment Seg)) :
      List (Correspondence.Segment Seg) := s.insertIdx 1 (.ofIndex .i 6)

-- (25)
theorem attraction_to_the_unmarked :
    Constraint.evalOn eighth {.a, .b, .c} ranking = {.a} := by decide +kernel

/-- The paradigms of /stafʕaːl/ in (27), the candidates obeying the undominated constraints:
levelled to the short, unepenthesized stem; epenthesized throughout; long before V-initial
suffixes; epenthesized in the perfectives; or both. -/
def tenth : Cand → Paradigm Seg Cell
  | .a => ⟨input, verbal ⟨perfective, short⟩ ⟨perfective1, short⟩
      ⟨imperfective, shortAblaut⟩ ⟨imperfectiveF, shortAblaut⟩⟩
  | .b => ⟨input, verbal ⟨perfective, epenthesized short⟩ ⟨perfective1, epenthesized short⟩
      ⟨imperfective, epenthesized shortAblaut⟩ ⟨imperfectiveF, epenthesized shortAblaut⟩⟩
  | .c => ⟨input, verbal ⟨perfective, long⟩ ⟨perfective1, short⟩
      ⟨imperfective, ablaut⟩ ⟨imperfectiveF, shortAblaut⟩⟩
  | .d => ⟨input, verbal ⟨perfective, epenthesized short⟩ ⟨perfective1, epenthesized short⟩
      ⟨imperfective, shortAblaut⟩ ⟨imperfectiveF, shortAblaut⟩⟩
  | .e => ⟨input, verbal ⟨perfective, epenthesized long⟩ ⟨perfective1, epenthesized short⟩
      ⟨imperfective, ablaut⟩ ⟨imperfectiveF, shortAblaut⟩⟩
where
  input : List Seg := [.s, .t, .a, .f, .ayn, .aa, .l]
  long : List (Correspondence.Segment Seg) := Correspondence.indexed input
  short : List (Correspondence.Segment Seg) :=
    Correspondence.indexed [.s, .t, .a, .f, .ayn, .a, .l]
  ablaut : List (Correspondence.Segment Seg) :=
    Correspondence.indexed [.s, .t, .a, .f, .ayn, .ii, .l]
  shortAblaut : List (Correspondence.Segment Seg) :=
    Correspondence.indexed [.s, .t, .a, .f, .ayn, .i, .l]
  /-- A vowel epenthesized into the initial cluster. -/
  epenthesized (s : List (Correspondence.Segment Seg)) :
      List (Correspondence.Segment Seg) := s.insertIdx 1 (.ofIndex .i 7)

-- (27), (21)
theorem two_attractors : Constraint.evalOn tenth {.a, .b, .c, .d, .e} ranking = {.a} := by
  decide +kernel

/-! ### Domination of OP faithfulness (§8.4.4)

Geminate verbs delete the vowel between their identical consonants before V-initial
suffixes, *ħmarra ~ ħmarartu*, so \*.CᵢV.CᵢV dominates IO-MAX-V and OP-MAX-V (29). -/

def opMaxV : Constraint (Paradigm Seg Cell) := opFaith (Correspondence.Segment.maxViolOn IsVowel)

/-- The paradigms of /ħmarar/ in (29): the vowel deleted before V-initial suffixes, or kept
throughout. -/
def geminate : Cand → Paradigm Seg Cell
  | .a => ⟨input, verbal ⟨perfective, deleted⟩ ⟨perfective1, faithful⟩
      ⟨imperfective, deleted⟩ ⟨imperfectiveF, ablaut⟩⟩
  | _ => ⟨input, verbal ⟨perfective, faithful⟩ ⟨perfective1, faithful⟩
      ⟨imperfective, ablaut⟩ ⟨imperfectiveF, ablaut⟩⟩
where
  input : List Seg := [.hh, .m, .a, .r, .a, .r]
  faithful : List (Correspondence.Segment Seg) := Correspondence.indexed input
  ablaut : List (Correspondence.Segment Seg) :=
    Correspondence.indexed [.hh, .m, .a, .r, .i, .r]
  /-- The vowel between the identical consonants deleted. -/
  deleted : List (Correspondence.Segment Seg) := faithful.eraseIdx 4

-- (29)
theorem geminate_alternation :
    Constraint.evalOn geminate {.a, .b}
      (markedness (fun c s ↦ identicalOnsets (c.word s)) :: ranking) = {.a} := by
  decide +kernel

/-! ### Moroccan Arabic majority rules (§8.5.1)

Schwa is banned from open syllables and triconsonantal clusters are prohibited, so the
phonology fixes CCəC before C-initial and CəCC before V-initial suffixes; the unaffixed
verb joins the larger class, *ʃrəb*, whereas nouns, paradigms of one, follow SONCON (30). The
paper states no sonority scale, and SONCON reads that of [benua-1997], with the pharyngeals
[ʕ ħ] among the fricatives, where their features put them, rather than among the glides, where
Benua puts the Tiberian Hebrew gutturals. -/

/-- \*ə]σ. -/
def schwaOpen (w : List Seg) : ℕ :=
  ((syllabify w).filter fun σ ↦ σ.nucleus = .schwa ∧ σ.coda = []).length

/-- The factors of three consonants in a row. -/
def cccFactors : Set (Augmented Seg) :=
  {f | ∃ c₁ c₂ c₃, ¬ IsVowel c₁ ∧ ¬ IsVowel c₂ ∧ ¬ IsVowel c₃ ∧ f = [some c₁, some c₂, some c₃]}

instance : DecidablePred (· ∈ cccFactors) := fun f ↦ match f with
  | [some c₁, some c₂, some c₃] =>
    decidable_of_iff (¬ IsVowel c₁ ∧ ¬ IsVowel c₂ ∧ ¬ IsVowel c₃) (by simp [cccFactors])
  | [] | [_] | [_, _] | [none, _, _] | [some _, none, _] | [some _, some _, none]
  | _ :: _ :: _ :: _ :: _ => isFalse (by simp [cccFactors])

/-- \*CCC. -/
def ccc : Constraint (List Seg) := Constraint.ofForbiddenFactors 3 cccFactors

/-- The class of a segment on the sonority scale of [benua-1997]. -/
def Seg.toBenua : Seg → Benua1997.Hebrew.Seg
  | .a | .aa | .i | .ii | .u | .schwa => .vowel
  | .j | .w => .glide
  | .l | .r => .liquid
  | .n | .m | .mw => .nasal
  | .s | .sh | .z | .zh => .sibilant
  | .f | .x | .gh | .ayn | .hh => .spirant
  | .t | .k | .b | .g | .d | .ch | .q => .stop

/-- Sonority, on the scale of [benua-1997]. -/
def sonority (c : Seg) : ℕ := Benua1997.Hebrew.sonority c.toBenua

/-- Whether SONCON (30) wants a schwa before `c₂ c₃`: `c₂` is more sonorous than `c₃`, or the
two are a geminate. -/
def SchwaFirst (c₂ c₃ : Seg) : Prop :=
  c₂ = c₃ ∨ Phonology.Sonority.profile sonority c₂ c₃ = .gt

instance (c₂ c₃ : Seg) : Decidable (SchwaFirst c₂ c₃) := inferInstanceAs (Decidable (_ ∨ _))

/-- SONCON (30), on a word of three consonants and a schwa. -/
def sonCon : List Seg → ℕ
  | [_, .schwa, c₂, c₃] => if SchwaFirst c₂ c₃ then 0 else 1
  | [_, c₂, .schwa, c₃] => if SchwaFirst c₂ c₃ then 1 else 0
  | _ => 0

/-- The segment an IPA symbol writes. -/
def Seg.ofIPA? : String → Option Seg
  | "f" => some .f | "ʕ" => some .ayn | "l" => some .l | "s" => some .s | "ʃ" => some .sh
  | "t" => some .t | "j" => some .j | "k" => some .k | "b" => some .b | "n" => some .n
  | "m" => some .m | "r" => some .r | "ħ" => some .hh | "g" => some .g | "d" => some .d
  | "x" => some .x | "q" => some .q | "w" => some .w | "z" => some .z | "ʒ" => some .zh
  | "ɣ" => some .gh | "mʷ" => some .mw | "a" => some .a | "aː" => some .aa | "i" => some .i
  | "iː" => some .ii | "u" => some .u | "ə" => some .schwa
  | _ => none

/-- A word of three consonants with its schwa moved to the other gap. -/
def moveSchwa : List Seg → List Seg
  | [c₁, .schwa, c₂, c₃] => [c₁, c₂, .schwa, c₃]
  | [c₁, c₂, .schwa, c₃] => [c₁, .schwa, c₂, c₃]
  | w => w

-- (30)
theorem sonCon_nouns :
    ∀ f ∈ Wordlist.all, ∃ w ∈ f.segments.mapM Seg.ofIPA?, sonCon w < sonCon (moveSchwa w) := by
  decide +kernel

/-- The ranking of (32): \*ə]σ, \*CCC >> OP-MAX-V >> SONCON >> IO-MAX-V, IO-DEP-V. -/
def moroccanRanking : List (Constraint (Paradigm Seg (List Seg))) :=
  [markedness fun suf s ↦ schwaOpen (s ++ suf), markedness fun suf s ↦ ccc (s ++ suf),
   opFaith (Correspondence.Segment.maxViolOn IsVowel), markedness fun suf s ↦ sonCon (s ++ suf),
   ioFaith (Correspondence.Segment.maxViolOn IsVowel),
   ioFaith (Correspondence.Segment.depViolOn IsVowel)]

/-- A CCəC member from /ʃərb/: the input schwa deleted, a schwa epenthesized. -/
def ccec (suffix : List Seg) : Member Seg (List Seg) :=
  ⟨suffix, [.ofIndex .sh 0, .ofIndex .r 2, .ofIndex .schwa 4, .ofIndex .b 3]⟩

/-- A CəCC member from /ʃərb/. -/
def cecc (suffix : List Seg) : Member Seg (List Seg) :=
  ⟨suffix, Correspondence.indexed [.sh, .schwa, .r, .b]⟩

/-- The suffixes of the perfective paradigm (31): none, four C-initial, two V-initial. -/
def suffixes : List (List Seg) := [[], [.t], [.n, .a], [.t, .i], [.t, .u], [.u], [.schwa, .t]]

/-- The paradigms of /ʃərb/ in (32): the unaffixed verb CCəC or CəCC with the rest fixed by
the phonology, or levelled to CCəC or to CəCC throughout. -/
def drink : Cand → Paradigm Seg (List Seg)
  | .a => ⟨input, (suffixes.take 5).map ccec ++ (suffixes.drop 5).map cecc⟩
  | .b => ⟨input, cecc [] :: ((suffixes.drop 1).take 4).map ccec ++ (suffixes.drop 5).map cecc⟩
  | .c => ⟨input, suffixes.map ccec⟩
  | _ => ⟨input, suffixes.map cecc⟩
where
  input : List Seg := [.sh, .schwa, .r, .b]

-- (32)
theorem majority_rules :
    Constraint.evalOn drink {.a, .b, .c, .d} moroccanRanking = {.a} := by
  decide +kernel

end Arabic

/-! ### Tiberian Hebrew jussives (§8.5.2)

The jussive truncates the final vowel of the imperfective, *jibkɛ ~ jeːbk*, and the final
cluster is not broken up by the epenthesis nouns undergo — the underapplication
[benua-1997] derives from base priority. Under OP every candidate loses a vowel to
truncation, and ⟨jibkɛ, jeːbk⟩ wins because its levelled rival ⟨jibəkɛ, jibɛk⟩ puts a schwa
between an open and a following syllable, \*VCəCV >> OP-MAX-V >> \*CC# (33); into a
rising-sonority cluster epenthesis applies in the jussive alone, SON-CON >> OP-MAX-V
(fn. 34). The segments and the markedness constraints are those of the [benua-1997] study,
whose winners the OP tableaux reproduce. -/

namespace Hebrew

open Benua1997.Hebrew (Seg sonCon complexCoda)

/-- \*VCəCV: a vowel between an open syllable and a following one. -/
def twoSidedOpen : List Seg → ℕ
  | v₁ :: c₁ :: v₂ :: c₂ :: v₃ :: rest =>
    (if v₁ = .vowel ∧ c₁ ≠ .vowel ∧ v₂ = .vowel ∧ c₂ ≠ .vowel ∧ v₃ = .vowel then 1 else 0)
      + twoSidedOpen (c₁ :: v₂ :: c₂ :: v₃ :: rest)
  | _ => 0

/-- \*VCəCV, SON-CON >> OP-MAX-V >> \*CC#. -/
def ranking : List (Constraint (Paradigm Seg Unit)) :=
  [markedness fun _ s ↦ twoSidedOpen s, markedness fun _ s ↦ sonCon s,
   opFaith (Correspondence.Segment.maxViolOn (· = .vowel)), markedness fun _ s ↦ complexCoda s]

/-- The paradigms of an imperfective and its truncated jussive from a stem ending in the
cluster `x y`: the cluster kept, epenthesis throughout, or epenthesis in the jussive alone. -/
def jussive (x y : Seg) : Cand → Paradigm Seg Unit
  | .a => ⟨stem, [⟨(), faithful⟩, ⟨(), faithful.take 4⟩]⟩
  | .b => ⟨stem, [⟨(), epenthesized faithful⟩, ⟨(), epenthesized (faithful.take 4)⟩]⟩
  | _ => ⟨stem, [⟨(), faithful⟩, ⟨(), epenthesized (faithful.take 4)⟩]⟩
where
  stem : List Seg := [.glide, .vowel, x, y, .vowel]
  faithful : List (Correspondence.Segment Seg) := Correspondence.indexed stem
  /-- A vowel epenthesized into the cluster. -/
  epenthesized (s : List (Correspondence.Segment Seg)) :
      List (Correspondence.Segment Seg) := s.insertIdx 3 (.ofIndex .vowel 5)

-- (33)
theorem cry : Constraint.evalOn (jussive .spirant .stop) {.a, .b, .c} ranking = {.a} := by
  decide +kernel

-- fn. 34
theorem uncover :
    Constraint.evalOn (jussive .spirant .liquid) {.a, .b, .c} ranking = {.c} := by
  decide +kernel

/-- The OP winners for *yišbē ~ yišb* 'take captive' and 'uncover' carry the forms of the
[benua-1997] winners, (82) and (87). -/
example :
    Constraint.evalOn (jussive .sibilant .stop) {.a, .b, .c} ranking = {.a} ∧
    (jussive .sibilant .stop .a).members.map (·.stem.map (·.seg)) =
      [(Benua1997.Hebrew.captive .d).string .base,
        (Benua1997.Hebrew.captive .d).string .derivative] ∧
    (jussive .spirant .liquid .c).members.map (·.stem.map (·.seg)) =
      [(Benua1997.Hebrew.uncover .b).string .base,
        (Benua1997.Hebrew.uncover .b).string .derivative] :=
  ⟨by decide, rfl, rfl⟩

end Hebrew

end McCarthy2005
