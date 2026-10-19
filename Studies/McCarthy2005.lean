module

public import Linglib.Phonology.OptimalityTheory.Correspondence
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Studies.Benua1997

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
correspondences (`Paradigm`), the correspondence diagram is read off those
(`Paradigm.corr`), symmetric and base-free by construction, and `markedness`, `ioFaith`, and
`opFaith` sum a constraint over the members or the ordered member pairs. The Classical
Arabic tableaux for the right and left edges of the verb stem and for geminate verbs, the
Moroccan majority-rules paradigm, and the Hebrew jussive paradigms of Benua are rerun under
the paper's ranking.

## References

* [mccarthy-2005]
* [benua-1997]
-/

@[expose] public section

namespace McCarthy2005

open OptimalityTheory

variable {α ι : Type*}

/-! ### Paradigms as candidates -/

/-- The roles of a candidate paradigm: the shared input stem and the stem of each member. -/
inductive Role
  | input
  | member (i : ℕ)
  deriving DecidableEq, Repr

/-- A paradigm member: its inflectional cell, its surface stem, and the correspondence from
the input to the stem. -/
structure Member (α ι : Type*) where
  cell : ι
  stem : List α
  io : List (ℕ × ℕ)

/-- A candidate paradigm (2a): the inflected forms of one input stem. -/
structure Paradigm (α ι : Type*) where
  input : List α
  members : List (Member α ι)

/-- The stem of the `i`th member, empty beyond the paradigm. -/
def Paradigm.stem (P : Paradigm α ι) (i : ℕ) : List α :=
  ((P.members[i]?).map Member.stem).getD []

/-- The input correspondence of the `i`th member, empty beyond the paradigm. -/
def Paradigm.io (P : Paradigm α ι) (i : ℕ) : List (ℕ × ℕ) :=
  ((P.members[i]?).map Member.io).getD []

/-- The positions of two stems that realise the same input position. -/
def compose (l₁ l₂ : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  l₁.flatMap fun (r, p) ↦ l₂.filterMap fun (r', q) ↦ if r = r' then some (p, q) else none

/-- The positions of a stem of length `n` without an input correspondent. -/
def epenthetic (l : List (ℕ × ℕ)) (n : ℕ) : List ℕ :=
  (List.range n).filter fun p ↦ ∀ rp ∈ l, rp.2 ≠ p

/-- The site of a stem position: the last input position realised at or before it. -/
def site (l : List (ℕ × ℕ)) (p : ℕ) : Option ℕ :=
  ((l.filter fun rp ↦ rp.2 ≤ p).map Prod.fst).max?

/-- ℛ_OP between two stems of lengths `n₁`, `n₂` with input correspondences `l₁`, `l₂`: the
positions realising the same input position, and the epenthetic positions at the same site. -/
def opPairs (l₁ l₂ : List (ℕ × ℕ)) (n₁ n₂ : ℕ) : List (ℕ × ℕ) :=
  compose l₁ l₂ ++ (epenthetic l₁ n₁).flatMap fun p ↦
    (epenthetic l₂ n₂).filterMap fun q ↦ if site l₁ p = site l₂ q then some (p, q) else none

/-- The correspondence diagram of a candidate (2c): each member's input–stem relation, and
between the stems of distinct members the relation ℛ_OP of `opPairs`. -/
def Paradigm.corr (P : Paradigm α ι) : Correspondence Role α :=
  .ofPairs (fun | .input => P.input | .member i => P.stem i)
    fun | .input, .member i => P.io i
        | .member i, .member j =>
          if i = j then [] else opPairs (P.io i) (P.io j) (P.stem i).length (P.stem j).length
        | _, _ => []

/-- A markedness constraint on the word of each cell, summed over the members (2b). -/
def markedness (m : ι → List α → ℕ) : Constraint (Paradigm α ι) :=
  fun P ↦ (P.members.map fun x ↦ m x.cell x.stem).sum

/-- An input–output faithfulness constraint summed over the members (2b). -/
def ioFaith (f : Correspondence Role α → Role → Role → ℕ) : Constraint (Paradigm α ι) :=
  fun P ↦ ((List.range P.members.length).map fun i ↦ f P.corr .input (.member i)).sum

/-- An OP faithfulness constraint (2d): a correspondence constraint summed over the ordered
pairs of distinct members. -/
def opFaith (f : Correspondence Role α → Role → Role → ℕ) : Constraint (Paradigm α ι) :=
  fun P ↦ ((List.range P.members.length).flatMap fun i ↦ (List.range P.members.length).map fun j ↦
    if i = j then 0 else f P.corr (.member i) (.member j)).sum

/-- The tableau of the labelled candidate paradigms under a ranking. -/
def tableau {L : Type*} [DecidableEq L] (cand : L → Paradigm α ι) (labels : Finset L)
    (ranking : List (Constraint (Paradigm α ι))) :=
  Tableau.ofList labels (ranking.map (Constraint.comap cand))

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
  ⟨[.m, .a, .t], [⟨[], [.m, .a, .t], Correspondence.diagonalPairs 3⟩,
    ⟨[.i], [.m, .a, .ch], Correspondence.diagonalPairs 3⟩]⟩

example : opFaith (Correspondence.identViolFeature high) mat = 2 := by decide

/-- ⟨ma, maʧi⟩. -/
def ma : Paradigm Seg (List Seg) :=
  ⟨[.m, .a, .t], [⟨[], [.m, .a], Correspondence.diagonalPairs 2⟩,
    ⟨[.i], [.m, .a, .ch], Correspondence.diagonalPairs 3⟩]⟩

example : opFaith Correspondence.maxViol ma = 1 ∧ opFaith Correspondence.depViol ma = 1 := by
  decide

end Palatalization

/-! ### Arabic syllables and feet

The markedness constraints of §8.4 read syllable weight and foot structure. Each vowel is a
nucleus, long or short by `weight`; the consonants before a vowel but the last, its onset,
close the preceding syllable. Feet are right-to-left moraic trochees with the final
syllable extrametrical, as the paper assumes; SWP marks a stressed light syllable, so an
(LL) foot. -/

namespace Arabic

inductive Seg
  | f | ayn | l | s | sh | t | j | k | b | n | m | r | hh | g | d | ch | x | q | w | z | zh
  | a | aa | i | ii | u | schwa
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

def opDepV : Constraint (Paradigm Seg Cell) := opFaith (Correspondence.depViolOn IsVowel)

def opIdentWt : Constraint (Paradigm Seg Cell) :=
  opFaith (Correspondence.identViolFeature weight)

def ioDepV : Constraint (Paradigm Seg Cell) := ioFaith (Correspondence.depViolOn IsVowel)

def ioMaxV : Constraint (Paradigm Seg Cell) := ioFaith (Correspondence.maxViolOn IsVowel)

def ioMaxC : Constraint (Paradigm Seg Cell) :=
  ioFaith (Correspondence.maxViolOn fun c ↦ ¬IsVowel c)

def ioIdentWt : Constraint (Paradigm Seg Cell) :=
  ioFaith (Correspondence.identViolFeature weight)

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
  | .a => ⟨input, [⟨perfective, short, diag⟩, ⟨perfective1, short, diag⟩]⟩
  | .b => ⟨input, [⟨perfective, input, diag⟩, ⟨{ perfective1 with appendix := true }, input, diag⟩]⟩
  | .c => ⟨input, [⟨perfective, input, diag⟩, ⟨perfective1, input, diag⟩]⟩
  | _ => ⟨input, [⟨perfective, input, diag⟩, ⟨perfective1, short, diag⟩]⟩
where
  input : List Seg := [.f, .a, .ayn, .aa, .l]
  short : List Seg := [.f, .a, .ayn, .a, .l]
  diag : List (ℕ × ℕ) := Correspondence.diagonalPairs 5

/-- (12): the long vowel of /faʕaːl/ is shortened throughout the paradigm, ⟨faʕala, faʕaltu⟩ —
overapplication of closed-syllable shortening, under OP-IDENT-WT >> IO-IDENT-WT. -/
theorem shortening_overapplies : (tableau long {.a, .b, .c, .d} ranking).optimal = {.a} := by
  decide

/-- The paradigms of /faʕl/ in (13): epenthesis throughout, the cluster kept throughout with
the superheavy coda an appendix or moraic, or alternating. -/
def cluster : Cand → Paradigm Seg Cell
  | .a => ⟨input, [⟨perfective, epenthesized, epenthetic⟩,
      ⟨perfective1, epenthesized, epenthetic⟩]⟩
  | .b => ⟨input, [⟨perfective, input, diag⟩, ⟨{ perfective1 with appendix := true }, input, diag⟩]⟩
  | .c => ⟨input, [⟨perfective, input, diag⟩, ⟨perfective1, input, diag⟩]⟩
  | _ => ⟨input, [⟨perfective, input, diag⟩, ⟨perfective1, epenthesized, epenthetic⟩]⟩
where
  input : List Seg := [.f, .a, .ayn, .l]
  epenthesized : List Seg := [.f, .a, .ayn, .i, .l]
  diag : List (ℕ × ℕ) := Correspondence.diagonalPairs 4
  /-- A vowel epenthesized into the final cluster. -/
  epenthetic : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 2), (3, 4)]

/-- (13): epenthesis into the final cluster of /faʕl/ carries through the paradigm,
⟨faʕila, faʕiltu⟩, under OP-DEP-V >> IO-DEP-V. -/
theorem epenthesis_overapplies : (tableau cluster {.a, .b, .c, .d} ranking).optimal = {.a} := by
  decide

/-- The paradigms of /faʕal/ in (17): the (LL) feet kept, or syncopated. -/
def syncope : Cand → Paradigm Seg Cell
  | .a => ⟨input, [⟨{ suffixes := [.u] }, input, Correspondence.diagonalPairs 5⟩,
      ⟨perfective, input, Correspondence.diagonalPairs 5⟩]⟩
  | _ => ⟨input, [⟨{ suffixes := [.u] }, [.f, .a, .ayn, .l], syncopated⟩,
      ⟨perfective, [.f, .a, .ayn, .l], syncopated⟩]⟩
where
  input : List Seg := [.f, .a, .ayn, .a, .l]
  syncopated : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 2), (4, 3)]

/-- (17): SWP cannot force syncope, IO-MAX-V >> SWP. -/
theorem no_syncope : (tableau syncope {.a, .b} ranking).optimal = {.a} := by decide

/-- The noun /fʕal/ with the case suffixes in (24): epenthesis, or the initial cluster. -/
def noun : Cand → Paradigm Seg Cell
  | .a => ⟨input, cases.map fun v ↦ ⟨{ suffixes := [v] }, [.f, .i, .ayn, .a, .l], epenthetic⟩⟩
  | _ => ⟨input, cases.map fun v ↦ ⟨{ suffixes := [v] }, input, Correspondence.diagonalPairs 4⟩⟩
where
  input : List Seg := [.f, .ayn, .a, .l]
  cases : List Seg := [.u, .a, .i]
  epenthetic : List (ℕ × ℕ) := [(0, 0), (1, 2), (2, 3), (3, 4)]

/-- (24): a [CCV noun stem is broken up by epenthesis, which SWP does not block in a
prefixless paradigm, ALIGN-L(Stem, σ) >> IO-DEP-V. -/
theorem noun_epenthesis : (tableau noun {.a, .b} ranking).optimal = {.a} := by decide

/-- The four representative cells of a verbal paradigm: the perfectives *-a*, *-tu* and the
imperfectives *ja-…-u*, *ja-…-na*. -/
def verbal (pfA pfTu impfU impfNa : Member Seg Cell) : List (Member Seg Cell) :=
  [pfA, pfTu, impfU, impfNa]

/-- The paradigms of the eighth conjugation /ftaʕal/ in (19) and (25): the initial cluster
kept throughout, epenthesis throughout, or epenthesis in the unprefixed forms only. -/
def eighth : Cand → Paradigm Seg Cell
  | .a => ⟨input, verbal ⟨perfective, input, diag⟩ ⟨perfective1, input, diag⟩
      ⟨imperfective, ablaut, diag⟩ ⟨imperfectiveF, ablaut, diag⟩⟩
  | .b => ⟨input, verbal ⟨perfective, epenthesized input, epenthetic⟩
      ⟨perfective1, epenthesized input, epenthetic⟩ ⟨imperfective, epenthesized ablaut, epenthetic⟩
      ⟨imperfectiveF, epenthesized ablaut, epenthetic⟩⟩
  | _ => ⟨input, verbal ⟨perfective, epenthesized input, epenthetic⟩
      ⟨perfective1, epenthesized input, epenthetic⟩ ⟨imperfective, ablaut, diag⟩
      ⟨imperfectiveF, ablaut, diag⟩⟩
where
  input : List Seg := [.f, .t, .a, .ayn, .a, .l]
  /-- The imperfective stem vowel. -/
  ablaut : List Seg := [.f, .t, .a, .ayn, .i, .l]
  epenthesized (s : List Seg) : List Seg := s.take 1 ++ [.i] ++ s.drop 1
  diag : List (ℕ × ℕ) := Correspondence.diagonalPairs 6
  epenthetic : List (ℕ × ℕ) := [(0, 0), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]

/-- (25): attraction to the unmarked — the prefixed *jaftaʕilu*, where epenthesis would
make an (LL) foot, is the attractor, and *ftaʕala* keeps its misaligned cluster:
OP-DEP-V >> SWP >> ALIGN-L(Stem, σ). -/
theorem attraction_to_the_unmarked :
    (tableau eighth {.a, .b, .c} ranking).optimal = {.a} := by decide

/-- The paradigms of /stafʕaːl/ in (27), the candidates obeying the undominated constraints:
levelled to the short, unepenthesized stem; epenthesized throughout; long before V-initial
suffixes; epenthesized in the perfectives; or both. -/
def tenth : Cand → Paradigm Seg Cell
  | .a => ⟨input, verbal ⟨perfective, short, diag⟩ ⟨perfective1, short, diag⟩
      ⟨imperfective, shortAblaut, diag⟩ ⟨imperfectiveF, shortAblaut, diag⟩⟩
  | .b => ⟨input, verbal ⟨perfective, epenthesized short, epenthetic⟩
      ⟨perfective1, epenthesized short, epenthetic⟩
      ⟨imperfective, epenthesized shortAblaut, epenthetic⟩
      ⟨imperfectiveF, epenthesized shortAblaut, epenthetic⟩⟩
  | .c => ⟨input, verbal ⟨perfective, input, diag⟩ ⟨perfective1, short, diag⟩
      ⟨imperfective, ablaut, diag⟩ ⟨imperfectiveF, shortAblaut, diag⟩⟩
  | .d => ⟨input, verbal ⟨perfective, epenthesized short, epenthetic⟩
      ⟨perfective1, epenthesized short, epenthetic⟩ ⟨imperfective, shortAblaut, diag⟩
      ⟨imperfectiveF, shortAblaut, diag⟩⟩
  | .e => ⟨input, verbal ⟨perfective, epenthesized input, epenthetic⟩
      ⟨perfective1, epenthesized short, epenthetic⟩ ⟨imperfective, ablaut, diag⟩
      ⟨imperfectiveF, shortAblaut, diag⟩⟩
where
  input : List Seg := [.s, .t, .a, .f, .ayn, .aa, .l]
  short : List Seg := [.s, .t, .a, .f, .ayn, .a, .l]
  ablaut : List Seg := [.s, .t, .a, .f, .ayn, .ii, .l]
  shortAblaut : List Seg := [.s, .t, .a, .f, .ayn, .i, .l]
  epenthesized (s : List Seg) : List Seg := s.take 1 ++ [.i] ++ s.drop 1
  diag : List (ℕ × ℕ) := Correspondence.diagonalPairs 7
  epenthetic : List (ℕ × ℕ) := [(0, 0), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7)]

/-- (27): different members attract different edges — the prefixed imperfectives block
epenthesis at the left edge via OP-DEP-V, the C-suffixed forms force shortening at the right
edge via OP-IDENT-WT — under the single ranking (21). -/
theorem two_attractors : (tableau tenth {.a, .b, .c, .d, .e} ranking).optimal = {.a} := by
  decide

/-! ### Domination of OP faithfulness (§8.4.4)

Geminate verbs delete the vowel between their identical consonants before V-initial
suffixes, *ħmarra ~ ħmarartu*, so \*.CᵢV.CᵢV dominates IO-MAX-V and OP-MAX-V (29). -/

def opMaxV : Constraint (Paradigm Seg Cell) := opFaith (Correspondence.maxViolOn IsVowel)

/-- The paradigms of /ħmarar/ in (29): the vowel deleted before V-initial suffixes, or kept
throughout. -/
def geminate : Cand → Paradigm Seg Cell
  | .a => ⟨input, verbal ⟨perfective, [.hh, .m, .a, .r, .r], deleted⟩ ⟨perfective1, input, diag⟩
      ⟨imperfective, [.hh, .m, .a, .r, .r], deleted⟩ ⟨imperfectiveF, ablaut, diag⟩⟩
  | _ => ⟨input, verbal ⟨perfective, input, diag⟩ ⟨perfective1, input, diag⟩
      ⟨imperfective, ablaut, diag⟩ ⟨imperfectiveF, ablaut, diag⟩⟩
where
  input : List Seg := [.hh, .m, .a, .r, .a, .r]
  ablaut : List Seg := [.hh, .m, .a, .r, .i, .r]
  diag : List (ℕ × ℕ) := Correspondence.diagonalPairs 6
  deleted : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 2), (3, 3), (5, 4)]

/-- (29): normal application — neither levelling wins, the vowel/zero alternation staying in
the paradigm, \*.CᵢV.CᵢV >> IO-MAX-V, OP-MAX-V. -/
theorem geminate_alternation :
    (tableau geminate {.a, .b}
      (markedness (fun c s ↦ identicalOnsets (c.word s)) :: ranking)).optimal = {.a} := by
  decide

/-! ### Moroccan Arabic majority rules (§8.5.1)

Schwa is banned from open syllables and triconsonantal clusters are prohibited, so the
phonology fixes CCəC before C-initial and CəCC before V-initial suffixes; the unaffixed
verb joins the larger class, *ʃrəb*, whereas nouns — paradigms of one — follow SONCON. -/

/-- \*ə]σ. -/
def schwaOpen (w : List Seg) : ℕ :=
  ((syllabify w).filter fun σ ↦ σ.nucleus = .schwa ∧ σ.coda = []).length

/-- \*CCC. -/
def ccc : List Seg → ℕ
  | c₁ :: c₂ :: c₃ :: rest =>
    (if ¬IsVowel c₁ ∧ ¬IsVowel c₂ ∧ ¬IsVowel c₃ then 1 else 0) + ccc (c₂ :: c₃ :: rest)
  | _ => 0

/-- Sonority: glide > liquid > nasal > fricative > stop. -/
def sonority : Seg → ℕ
  | .j | .w => 5
  | .l | .r => 4
  | .n | .m => 3
  | .f | .s | .sh | .hh | .ayn | .x | .z | .zh => 2
  | _ => 1

/-- SONCON (30), on a word of three consonants and a schwa: CəC₂C₃ wants C₂ more sonorous
than C₃, CC₂əC₃ not. -/
def sonCon : List Seg → ℕ
  | [_, .schwa, c₂, c₃] => if sonority c₂ > sonority c₃ then 0 else 1
  | [_, c₂, .schwa, c₃] => if sonority c₂ > sonority c₃ then 1 else 0
  | _ => 0

/-- The ranking of (32): \*ə]σ, \*CCC >> OP-MAX-V >> SONCON >> IO-MAX-V, IO-DEP-V. -/
def moroccanRanking : List (Constraint (Paradigm Seg (List Seg))) :=
  [markedness fun suf s ↦ schwaOpen (s ++ suf), markedness fun suf s ↦ ccc (s ++ suf),
   opFaith (Correspondence.maxViolOn IsVowel), markedness fun suf s ↦ sonCon (s ++ suf),
   ioFaith (Correspondence.maxViolOn IsVowel), ioFaith (Correspondence.depViolOn IsVowel)]

/-- A CCəC member from /ʃərb/: the input schwa deleted, a schwa epenthesized. -/
def ccec (suffix : List Seg) : Member Seg (List Seg) :=
  ⟨suffix, [.sh, .r, .schwa, .b], [(0, 0), (2, 1), (3, 3)]⟩

/-- A CəCC member from /ʃərb/. -/
def cecc (suffix : List Seg) : Member Seg (List Seg) :=
  ⟨suffix, [.sh, .schwa, .r, .b], Correspondence.diagonalPairs 4⟩

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

/-- (32): majority rules — the unaffixed *ʃrəb* joins the five CCəC members against the two
CəCC members, OP-MAX-V being violated once in each direction by every CCəC–CəCC pair
(twenty against twenty-four marks). -/
theorem majority_rules : (tableau drink {.a, .b, .c, .d} moroccanRanking).optimal = {.a} := by
  decide

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
   opFaith (Correspondence.maxViolOn (· = .vowel)), markedness fun _ s ↦ complexCoda s]

/-- The paradigms of an imperfective and its truncated jussive from a stem ending in the
cluster `x y`: the cluster kept, epenthesis throughout, or epenthesis in the jussive alone. -/
def jussive (x y : Seg) : Cand → Paradigm Seg Unit
  | .a => ⟨stem, [⟨(), stem, Correspondence.diagonalPairs 5⟩,
      ⟨(), [.glide, .vowel, x, y], Correspondence.diagonalPairs 4⟩]⟩
  | .b => ⟨stem, [⟨(), [.glide, .vowel, x, .vowel, y, .vowel],
      [(0, 0), (1, 1), (2, 2), (3, 4), (4, 5)]⟩, ⟨(), epenthesized, epenthetic⟩]⟩
  | _ => ⟨stem, [⟨(), stem, Correspondence.diagonalPairs 5⟩, ⟨(), epenthesized, epenthetic⟩]⟩
where
  stem : List Seg := [.glide, .vowel, x, y, .vowel]
  epenthesized : List Seg := [.glide, .vowel, x, .vowel, y]
  epenthetic : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 2), (3, 4)]

/-- (33): *jibkɛ ~ jeːbk* 'cry' — the cluster is kept, overapplication of epenthesis being
blocked. -/
theorem cry : (tableau (jussive .spirant .stop) {.a, .b, .c} ranking).optimal = {.a} := by
  decide

/-- fn. 34: *jɛɣlɛ ~ jɛɣɛl* 'uncover' — into a rising-sonority cluster epenthesis applies in
the jussive alone, OP-MAX-V being dominated by SON-CON. -/
theorem uncover :
    (tableau (jussive .spirant .liquid) {.a, .b, .c} ranking).optimal = {.c} := by decide

/-- The OP winners for *yišbē ~ yišb* 'take captive' and 'uncover' carry the forms of the
[benua-1997] winners, (87) and (92). -/
example :
    (tableau (jussive .sibilant .stop) {.a, .b, .c} ranking).optimal = {.a} ∧
    (Benua1997.Hebrew.captive .d).form .base = (jussive .sibilant .stop .a).stem 0 ∧
    (Benua1997.Hebrew.captive .d).form .derivative = (jussive .sibilant .stop .a).stem 1 ∧
    (Benua1997.Hebrew.uncover .b).form .base = (jussive .spirant .liquid .c).stem 0 ∧
    (Benua1997.Hebrew.uncover .b).form .derivative = (jussive .spirant .liquid .c).stem 1 :=
  ⟨by decide, rfl, rfl, rfl, rfl⟩

end Hebrew

end McCarthy2005
