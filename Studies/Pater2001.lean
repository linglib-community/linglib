module

public import Linglib.Fragments.Indonesian.Phonology
public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Data.PHOIBLE.Inventories.Muna
public import Linglib.Data.Wordlist.Pater2001
public import Linglib.Morphology.Morph
public import Mathlib.Data.Fintype.Perm

/-!
# Pater (2001): Austronesian nasal substitution revisited

Pater argues that nasal substitution, the fusion of a prefix nasal with a following voiceless
obstruent, is not an effect of *NC̥. Muna *-um-* fuses with a root-initial voiceless labial
although [no candidate has a nasal before a voiceless obstruent](##nc_muna), and [the Muna forms
follow](##muna_predicts) from a ban on two labials and faithfulness to [Pharyngeal Expansion],
which voiced obstruents bear. The same faithfulness, ranked above a ban on place shared across
the left edge of a Prosodic Word, [derives the Indonesian forms](##indonesian_predicts), among
them assimilation between two prefixes, where [the earlier *NC̥ analysis
fuses](##ncRanking_mispredicts_per). With NASASSIM on top, no reranking [makes only some voiced
stops fuse](##fusingStops_mem), as the intermediate types of Newman's typology do.

## Implementation notes

* The page images read are those of the manuscript at
  `https://hdl.handle.net/20.500.14394/32431`, whose cover sheet calls the chapter a slightly
  revised version of it. Example numbers are the manuscript's.
* A candidate is a correspondence from the input to the output, and each constraint reads it:
  faithfulness the relation, markedness the output. The Indonesian fused nasal is the nasal that
  the Indonesian rules assimilate the prefix nasal to (`NasalSubstitution.substitute`), so fusion
  and assimilation followed by loss of the consonant give one string. The Muna fused nasal is
  Muna's nasal homorganic with the consonant in the same way: *m* before *p* and *f*, and the *m*
  of *-um-* unchanged before *w*, whose double articulation no Muna nasal has.
* [Pharyngeal Expansion] is [−sonorant, +voice], and two segments are homorganic when they agree
  on the major articulators (`Segment.Homorganic`). The input carries the morph of each segment
  and the Prosodic Word is read off it, prefixes outside and an output segment inside when one
  of its correspondents is. *PL/LAB² counts non-syllabic labials, since PHOIBLE makes round
  vowels [+labial].
* With NASASSIM dominated, [the velars alone fuse](##exists_fusingStops_eq_velars), a type
  Newman's typology lacks.

## TODO

* The other NC effects of (5) and (6), the infixation of (7) to (10), the co-occurrence table
  (13), and the hiatus evidence for CRISPEDGE[PRWD] of (26) to (34).
* Before a sonorant consonant, which the paper does not discuss, [the ranking
  fuses](##optimal_ranking_l) where Indonesian loses the nasal, and loss is not a candidate.

## References

* [pater-2001]
* [pater-1999]
* [newman-1984]
* [sneddon-1996]
-/

@[expose] public section

namespace Pater2001

open Phonology OptimalityTheory
open Morphology (Morph)

/-! ### Features -/

/-- [Pharyngeal Expansion], the feature Pater gives voiced obstruents and implosives and denies
nasals and voiceless obstruents: here the [−sonorant, +voice] segments. -/
def PharExp (s : Segment) : Prop := s.HasValue .sonorant false ∧ s.HasValue .voice true

instance : DecidablePred PharExp := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The adjacent pairs of a word. -/
def pairs (w : List Segment) : List (Segment × Segment) := w.zip w.tail

/-! ### Constraints

A candidate is an input and an output related as Pater's subscripts relate them, a
correspondence from the input to the output. -/

/-- A candidate, a correspondence from the input to the output. -/
abbrev Cand := Correspondence BinaryRole Segment

/-- *NC̥: a nasal before a voiceless obstruent. -/
def nc : Constraint Cand := fun c ↦
  (pairs (c.form .rhs)).countP fun p ↦
    p.1.HasValue .nasal true ∧ p.2.HasValue .sonorant false ∧ p.2.HasValue .voice false

/-- NASASSIM (36): a nasal not homorganic with the consonant after it. -/
def nasAssim : Constraint Cand := fun c ↦
  (pairs (c.form .rhs)).countP fun p ↦
    p.1.HasValue .nasal true ∧ p.2.IsConsonant ∧ ¬ p.1.Homorganic p.2

/-- *PL/LAB², the self-conjunction of *PL/LAB (15): two labial consonants or glides in a
word, the non-syllabic segments with labial place. -/
def plab2 : Constraint Cand := fun c ↦
  if 2 ≤ (c.form .rhs).countP (fun s ↦ s.HasValue .syllabic false ∧ s.HasValue .labial true)
  then 1 else 0

/-- MAX: an input segment with no output correspondent. -/
def maxIO : Constraint Cand := fun c ↦ c.maxViol .lhs .rhs

/-- UNIFORMITY: an output segment with two input correspondents. -/
def uniformity : Constraint Cand := fun c ↦ c.uniformityViol .lhs .rhs

/-- IDENT[PHAREXP]: corresponding segments that differ in [Pharyngeal Expansion]. -/
def identPharExp : Constraint Cand := fun c ↦
  c.identViolFeature (fun s ↦ decide (PharExp s)) .lhs .rhs

/-- IDENT[PLACE]: corresponding segments that differ in place. -/
def identPlace : Constraint Cand := fun c ↦
  c.identViolFeature (Segment.restrict FeatureClass.place) .lhs .rhs

/-! ### The Prosodic Word

The input carries the morph each segment belongs to, and the Prosodic Word is read off it as
ALIGN-WD places it: prefixes lie outside, and roots and suffixes inside. -/

/-- The kind of a prefix. -/
abbrev prefixKind : Morph.Kind := .bound .before .affix

/-- A morph is inside the Prosodic Word unless it is bound before its host, as a prefix is. -/
def InPrWd (k : Morph.Kind) : Prop := k.side? ≠ some .before

instance : DecidablePred InPrWd := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- The output segment at `j` is in the Prosodic Word when one of its input correspondents
belongs to a morph inside it, `kinds` giving the morph of each input segment. -/
def OutInPrWd (kinds : List Morph.Kind) (c : Cand) (j : ℕ) : Prop :=
  ∃ p ∈ c.edge .lhs .rhs, p.2.val = j ∧ ∃ k ∈ kinds[p.1.val]?, InPrWd k

instance (kinds : List Morph.Kind) (c : Cand) : DecidablePred (OutInPrWd kinds c) := fun j ↦
  inferInstanceAs
    (Decidable (∃ p ∈ c.edge .lhs .rhs, p.2.val = j ∧ ∃ k ∈ kinds[p.1.val]?, InPrWd k))

/-- CRISPEDGE[PRWD] (32): homorganic neighbours on the two sides of an edge of the Prosodic
Word, whose place is linked across it. -/
def crispEdge (kinds : List Morph.Kind) : Constraint Cand := fun c ↦
  (pairs (c.form .rhs)).zipIdx.countP fun q ↦
    ¬ (OutInPrWd kinds c q.2 ↔ OutInPrWd kinds c (q.2 + 1)) ∧ q.1.1.Homorganic q.1.2

/-- UNIFORMITY of roots: an output segment with two input correspondents in a root. -/
def uniformityRt (kinds : List Morph.Kind) : Constraint Cand := fun c ↦
  ((Finset.univ : Finset (Fin (c.form .rhs).length)).filter fun j ↦
    1 < ((c.edge .lhs .rhs).filter fun p ↦ p.2 = j ∧ kinds[p.1.val]? = some .root).card).card

/-- The outcomes of Pater's tableaux: fusion of the nasal and the consonant into one nasal,
assimilation of the nasal, and the faithful cluster. -/
inductive Outcome
  | fuse
  | assimilate
  | faithful
  deriving DecidableEq, Fintype

/-- The candidates of the nasal `N` before `x` under each outcome, with `y` the nasal that `N`
assimilates to, which is also the fused nasal. -/
def junctureCorr (N x y : Segment) : Outcome → Cand
  | .fuse => .ofPairs (fun | .lhs => [N, x] | .rhs => [y])
      (fun | .lhs, .rhs => [(0, 0), (1, 0)] | _, _ => [])
  | .assimilate => .parallel [N, x] [y, x]
  | .faithful => .identity [N, x]

/-! ### Indonesian -/

open Indonesian.Phonology

/-- The Indonesian candidates of a nasal `N` before `x`, whose assimilated and fused nasal is the
one the Indonesian rules give. -/
def corr (N x : Segment) : Outcome → Cand :=
  junctureCorr N x (NasalSubstitution.substitute consonants trigger N x)

/-- The tableau of the nasal `N` of a morph of kind `kN` before the consonant `x` of a morph of
kind `kx`, under the constraints `cs` in rank order. -/
def tableau (cs : List Morph.Kind → List (Constraint Cand)) (N x : Segment) (kN kx : Morph.Kind)
    (cands : Finset Outcome) :=
  Tableau.ofList cands ((cs [kN, kx]).map (Constraint.comap (corr N x)))

/-- [pater-1999]'s analysis as (3) and (4) state it: UNIFORMITY of roots ≫ *NC̥ ≫ UNIFORMITY. -/
def ncRanking (kinds : List Morph.Kind) : List (Constraint Cand) :=
  [uniformityRt kinds, nc, uniformity]

/-- The reanalysis (38), (39) and (42): NASASSIM, IDENT[PHAREXP] ≫ CRISPEDGE[PRWD] ≫ UNIFORMITY
≫ IDENT[PLACE]. -/
def ranking (kinds : List Morph.Kind) : List (Constraint Cand) :=
  [nasAssim, identPharExp, crispEdge kinds, uniformity, identPlace]

/-- The output of the winners of a tableau over the outcomes of the nasal `N` before `x`, if
they have one output. -/
def winningOutput {n : ℕ} (N x : Segment) (t : Tableau Outcome n) : Option (List Segment) :=
  match (([Outcome.fuse, .assimilate, .faithful].filter (· ∈ t.optimal)).map
      fun o ↦ (corr N x o).form .rhs).dedup with
  | [w] => some w
  | _ => none

/-- What *meN-* before `base` comes out as under `cs`, among the outcomes `cands`. -/
def meN (cs : List Morph.Kind → List (Constraint Cand)) (cands : Finset Outcome) :
    List Segment → Option (List Segment)
  | x :: w => (winningOutput ng x (tableau cs ng x prefixKind .root cands)).map fun o ↦
      [m, e] ++ o ++ w
  | [] => none

/-- What *meN-* before *per-* before `base` comes out as under `cs`, among the outcomes
`cands`. -/
def meNper (cs : List Morph.Kind → List (Constraint Cand)) (cands : Finset Outcome)
    (base : List Segment) : Option (List Segment) :=
  (winningOutput ng p (tableau cs ng p prefixKind prefixKind cands)).map fun o ↦
    [m, e] ++ o ++ [e, r] ++ base

/-- What an Indonesian relation of the table predicts for its base. -/
def predict (cs : List Morph.Kind → List (Constraint Cand)) (cands : Finset Outcome) :
    String → List Segment → Option (List Segment)
  | "meN-", w => meN cs cands w
  | "meN- per-", w => meNper cs cands w
  | _, _ => none

/-! ### Muna -/

/-- The outcomes of Muna *-um-* before a root in Pater's tableaux: infixation, deletion of the
affix, and fusion of its nasal with the root-initial consonant. -/
inductive UmOutcome
  | infix
  | delete
  | fuse
  deriving DecidableEq, Fintype

namespace Muna

/-- The vowel /u/ of *-um-*. -/
def u : Segment := .ofChart .«u»

/-- The nasal /m/ of *-um-*. -/
def m : Segment := .ofChart .«m»

/-- The consonants a nasal fuses with, Hayes's [−syllabic] segments. -/
def trigger : Segment := Segment.ofSpecs [(.syllabic, false)]

/-- The output of each outcome of *-um-* before the root `x :: w`. -/
def output (x : Segment) (w : List Segment) : UmOutcome → List Segment
  | .infix => x :: u :: m :: w
  | .delete => x :: w
  | .fuse =>
    NasalSubstitution.substitute Data.PHOIBLE.Inventories.Muna.mnb.segments trigger m x :: w

/-- The correspondence of each outcome, from the positions of `u :: m :: x :: w` to those of its
output: infixation reorders, deletion leaves the affix without correspondents, and fusion maps
the nasal and the consonant to one nasal. -/
def edges (n : ℕ) : UmOutcome → List (ℕ × ℕ)
  | .infix => [(0, 1), (1, 2), (2, 0)] ++ (List.range n).map fun i ↦ (i + 3, i + 3)
  | .delete => (List.range (n + 1)).map fun i ↦ (i + 2, i)
  | .fuse => [(1, 0), (2, 0)] ++ (List.range n).map fun i ↦ (i + 3, i + 1)

/-- The candidates of *-um-* before the root `x :: w`. -/
def corr (x : Segment) (w : List Segment) (o : UmOutcome) : Cand :=
  .ofPairs (fun | .lhs => u :: m :: x :: w | .rhs => output x w o)
    (fun | .lhs, .rhs => edges w.length o | _, _ => [])

/-- The candidates of *-um-* before `root`. -/
def cands : List Segment → List Cand
  | x :: w => [corr x w .infix, corr x w .delete, corr x w .fuse]
  | [] => []

/-- (23), (24): *PL/LAB², IDENT[PHAREXP] ≫ MAX ≫ UNIFORMITY. -/
def ranking : List (Constraint Cand) := [plab2, identPharExp, maxIO, uniformity]

/-- The tableau of *-um-* before the root `x :: w` under `cs`. -/
def tableau (cs : List (Constraint Cand)) (x : Segment) (w : List Segment) :=
  Tableau.ofList .univ (cs.map (Constraint.comap (corr x w)))

/-- What *-um-* before `root` comes out as under `cs`. -/
def um (cs : List (Constraint Cand)) : List Segment → Option (List Segment)
  | x :: w =>
    match [UmOutcome.infix, .delete, .fuse].filter (· ∈ (tableau cs x w).optimal) with
    | [o] => some (output x w o)
    | _ => none
  | [] => none

end Muna

/-! ### The forms -/

/-- The segments of a form, each read through its glyph in the PHOIBLE inventory `I`. -/
def segmentsOf (I : Data.PHOIBLE.Inventory) (w : CLDF.Wordlist.Form Wordlist.Cell) :
    Option (List Segment) :=
  w.segments.mapM I.segment?

open Data.PHOIBLE.Inventories

/-! ### The *NC̥ analysis -/

/-- The candidates of (3) and (4). -/
def ncCands : Finset Outcome := {.fuse, .assimilate}

-- (3), and (4) at the left edge of a root
theorem optimal_ncRanking_prefix_root :
    (tableau ncRanking ng p prefixKind .root ncCands).optimal = {.fuse} ∧
      (tableau ncRanking ng b prefixKind .root ncCands).optimal = {.assimilate} := by
  decide +kernel

-- (4), left: the fused candidate violates UNIFORMITY, the faithful one *NC̥
theorem uniformity_empat : uniformity (corr m p .fuse) = 1 ∧ uniformity (corr m p .assimilate) = 0 ∧
    nc (corr m p .assimilate) = 1 := by
  decide +kernel

-- (4) inside a root, *əmpat*
theorem optimal_ncRanking_root :
    (tableau ncRanking m p .root .root ncCands).optimal = {.assimilate} := by
  decide +kernel

/-- UNIFORMITY of roots keeps *NC̥ from fusing inside a root but not between two prefixes, so
*meN-* before *per-* fuses, contrary to *məmpərbesar*. -/
theorem ncRanking_mispredicts_per :
    (segmentsOf Indonesian.ind Wordlist.besar).bind (meNper ncRanking ncCands) ≠
      segmentsOf Indonesian.ind Wordlist.memperbesar := by
  decide +kernel

/-! ### Muna -/

/-- *-um-* creates no nasal before a voiceless obstruent, so *NC̥ rates every Muna candidate
alike and cannot be what makes voiceless consonants fuse. -/
theorem nc_muna : ∀ r ∈ Wordlist.relations, r.relation = "-um-" →
    ∀ root ∈ segmentsOf Muna.mnb r.form, ∀ c ∈ Muna.cands root, nc c = 0 := by
  decide +kernel

/-- Under *PL/LAB², IDENT[PHAREXP] ≫ MAX ≫ UNIFORMITY, *-um-* fuses with a root-initial
voiceless labial and is deleted before a voiced or implosive one. Every form of the table
follows but *wanu*, which Pater leaves to a lexically specific faithfulness constraint. -/
theorem muna_predicts : ∀ r ∈ Wordlist.relations, r.relation = "-um-" →
    ((segmentsOf Muna.mnb r.form).bind (Muna.um Muna.ranking) = segmentsOf Muna.mnb r.target ↔
      r.target ≠ Wordlist.wanu_irr) := by
  decide +kernel

-- MAX of infixation, deletion and fusion before *baru*
theorem max_baru :
    (segmentsOf Muna.mnb Wordlist.baru).map (fun root ↦ (Muna.cands root).map maxIO) =
      some [0, 2, 1] := by
  decide +kernel

/-! ### The reanalysis of Indonesian -/

/-- Under NASASSIM, IDENT[PHAREXP] ≫ CRISPEDGE[PRWD] ≫ UNIFORMITY ≫ IDENT[PLACE], every Indonesian
form of the table follows: the prefix nasal fuses with a voiceless obstruent at the left edge of
a root, and assimilates to a voiced one and to the *p* of *per-*. -/
theorem indonesian_predicts : ∀ r ∈ Wordlist.relations, r.relation ≠ "-um-" →
    (segmentsOf Indonesian.ind r.form).bind (predict ranking .univ r.relation) =
      segmentsOf Indonesian.ind r.target := by
  decide +kernel

-- (4) inside a root under the reanalysis: assimilation and the faithful cluster are one output
theorem optimal_ranking_root :
    (tableau ranking m p .root .root .univ).optimal = {.assimilate, .faithful} := by
  decide +kernel

-- (42): the fused nasal corresponds to the prefix's ŋ
theorem identPlace_fuse : identPlace (corr ng p .fuse) = 1 := by
  decide +kernel

-- (40)
theorem optimal_kalinga :
    (tableau (fun kinds ↦ [nasAssim, crispEdge kinds, identPharExp, uniformity, identPlace])
      ng b prefixKind .root .univ).optimal = {.fuse} := by
  decide +kernel

-- the voiceless obstruents, which add *c* and the loan fricatives to the substituting
-- consonants of Sneddon's grammar
theorem consonants_filter_fuse :
    consonants.filter (fun x ↦ x.IsObstruent ∧
        (tableau ranking ng x prefixKind .root .univ).optimal = {.fuse}) =
      substituting ∪ {c, f, sy, kh} := by
  decide +kernel

-- before *l*, which the paper does not discuss, the nasal fuses; Indonesian loses it, as in
-- *melihat*, and loss is not among the candidates
theorem optimal_ranking_l : (tableau ranking ng l prefixKind .root .univ).optimal = {.fuse} := by
  decide +kernel

/-! ### Typology -/

/-- The constraints of (38) to (40), NASASSIM, IDENT[PHAREXP], CRISPEDGE[PRWD] and UNIFORMITY,
on the candidates of the prefix nasal before `x` at the left edge of a root. -/
def typologyCon (x : Segment) : ConstraintSet Outcome (Fin 4) :=
  ConstraintSet.comap (corr ng x)
    ![nasAssim, identPharExp, crispEdge [prefixKind, .root], uniformity]

/-- The stops of Newman's typology (41) that fuse with the prefix nasal under the ranking `ρ`. -/
def fusingStops (ρ : Ranking (Fin 4) 4) : List Segment :=
  [p, t, k, b, d, g].filter fun x ↦ (Tableau.ofRanking (typologyCon x) ρ .univ).optimal = {.fuse}

/-- With NASASSIM undominated, the stops that fuse are none, the voiceless ones or all of them,
as in Newman's Malay and Kalinga types, never only some of the voiced ones, as in his
intermediate types. -/
theorem fusingStops_mem : ∀ ρ : Ranking (Fin 4) 4, ρ 0 = 0 →
    fusingStops ρ ∈ [[], [p, t, k], [p, t, k, b, d, g]] := by
  decide +kernel

-- with NASASSIM dominated, the velars alone fuse, since the unassimilated cluster before them is
-- already homorganic
theorem exists_fusingStops_eq_velars : ∃ ρ : Ranking (Fin 4) 4, fusingStops ρ = [k, g] := by
  decide +kernel

end Pater2001
