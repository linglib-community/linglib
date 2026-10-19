module

public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Data.Examples.RoseWalker2004
public import Mathlib.Tactic.DeriveFintype

/-!
# Rose & Walker (2004): A Typology of Consonant Agreement as Correspondence

This file formalizes the paper's account of long-distance consonant agreement: consonants of
an output that are similar enough stand in a correspondence relation, demanded by CORR
constraints arrayed in a fixed hierarchy by similarity, and IDENT-CC constraints require
correspondents to agree in the harmonizing feature, so that intervening segments are neutral
and agreement holds between exactly the pairs whose CORR constraint outranks the input–output
faithfulness resisting the change. The nasal case studies are formalized: the nasal
correspondence hierarchy (`nasalSimilarity`, `corr`), IDENT-OI(nasal) interpolated at a cut in
it, and the typology `winner_eq`, that a nasal and an oral consonant agree in the optimal output
exactly when their pair is at least as similar as the cut, so that demoting the faithfulness
constraint only widens the agreeing class (`agree_of_le`). Ngbaka cuts the hierarchy below the
homorganic nasal–prenasal pairs, and its words are the fixed points of that grammar
(`ngbaka_rows`); Kikongo cuts it below every nasal–voiced-stop and nasal–approximant pair and
splits IDENT-CC by direction, so that only consonants to the right of a nasal agree, and its
alternations are the rows of `kikongo_rows`, with the paper's tableaux for the agreeing suffix,
the neutral voiceless stop, and the direction of agreement reproduced over generated or the
paper's own candidates.

## Implementation notes

Segments are the paper's chart of stop series on the nasality–voicing continuum by place,
approximants, fricatives, and vocoids; a candidate is an output string aligned with the input
and a correspondence relation among its consonants, listed as coindexed pairs. CORR constraints
count the consonant pairs at least as similar as their stratum that fail to correspond, the
directional IDENT-CC constraints the coindexed pairs in which a nasal is followed, or preceded,
by an oral correspondent, and IDENT-OI(nasal) the consonants nasalized. GEN keeps or nasalizes
each consonant and coindexes the consonants by any partition; the tableau of the paper's
five-consonant directional example is over the paper's own candidates. Kikongo's surface map
`harmonize` is the analysis's generalization, rightward agreement at the Kikongo cut with NC
clusters neither triggering nor undergoing, which the paper attributes to a constraint on the
structural roles of correspondents; that constraint, the exclusion of prefixes from the stem
domain, and the laryngeal case studies are not formalized. Transcriptions omit tone, and the
example numbers of the rows are those of the manuscript [rose-walker-2001].

## References

* [rose-walker-2004]
* [rose-walker-2001]
* [mccarthy-prince-1995]
* [prince-smolensky-1993]
-/

@[expose] public section

namespace RoseWalker2004

open OptimalityTheory

/-! ### Segments and similarity -/

/-- The places of articulation of the stops. -/
inductive Place
  | labial
  | coronal
  | dorsal
  deriving DecidableEq, Repr, Fintype

/-- The series of stops on the nasality–voicing continuum. -/
inductive Series
  | voiceless
  | voiced
  | prenasal
  | nasal
  deriving DecidableEq, Repr, Fintype

/-- A segment: a stop of some place and series, an approximant consonant, a fricative, or a
vocoid. -/
inductive Seg
  | stop (place : Place) (series : Series)
  | approximant
  | fricative
  | vocoid
  deriving DecidableEq, Repr, Fintype

namespace Seg

/-- A nasal stop. -/
def IsNasal : Seg → Prop
  | stop _ .nasal => True
  | _ => False

instance : DecidablePred IsNasal
  | stop _ .nasal => isTrue trivial
  | stop _ .voiceless | stop _ .voiced | stop _ .prenasal | approximant | fricative | vocoid =>
    isFalse id

/-- A consonant. -/
def IsConsonant (s : Seg) : Prop := s ≠ vocoid

instance : DecidablePred IsConsonant := fun s ↦ inferInstanceAs (Decidable (s ≠ vocoid))

/-- The nasal counterpart of a consonant: the nasal at a stop's place, the coronal nasal for
an approximant. -/
def nasalize : Seg → Seg
  | stop p _ => stop p .nasal
  | approximant => stop .coronal .nasal
  | s => s

end Seg

/-- The strata of the nasal correspondence hierarchy, the similarity of a nasal to another
consonant: identical nasals; heterorganic nasals or a homorganic nasal and prenasal stop; a
heterorganic nasal and prenasal stop or a homorganic nasal and voiced stop; a heterorganic nasal
and voiced stop or a nasal and an approximant. Pairs without a nasal, and pairs with a
voiceless stop, a fricative, or a vocoid, are below the threshold of similarity. -/
def nasalSimilarity : Seg → Seg → Option (Fin 4)
  | .stop p .nasal, .stop q .nasal => some (if p = q then 0 else 1)
  | .stop p .nasal, .stop q .prenasal | .stop q .prenasal, .stop p .nasal =>
    some (if p = q then 1 else 2)
  | .stop p .nasal, .stop q .voiced | .stop q .voiced, .stop p .nasal =>
    some (if p = q then 2 else 3)
  | .stop _ .nasal, .approximant | .approximant, .stop _ .nasal => some 3
  | _, _ => none

/-- A pair at least as similar as stratum `k`. -/
def AtLeast (k : Fin 4) (a b : Seg) : Prop :=
  match nasalSimilarity a b with
  | some r => r ≤ k
  | none => False

instance (k : Fin 4) (a b : Seg) : Decidable (AtLeast k a b) := by
  unfold AtLeast; split <;> infer_instance

theorem AtLeast.mono {k k' : Fin 4} {a b : Seg} (h : AtLeast k a b) (hk : k ≤ k') :
    AtLeast k' a b := by
  unfold AtLeast at h ⊢
  revert h
  cases nasalSimilarity a b with
  | none => exact id
  | some r => exact fun h ↦ h.trans hk

/-! ### Candidates and constraints -/

/-- The positions of the consonants of a string. -/
def consonants (w : List Seg) : List ℕ :=
  (List.range w.length).filter fun i ↦ (w.getD i .vocoid).IsConsonant

/-- The pairs of consonant positions of a string, left position first. -/
def consonantPairs (w : List Seg) : List (ℕ × ℕ) :=
  (consonants w).flatMap fun i ↦ ((consonants w).filter (i < ·)).map (i, ·)

/-- An output candidate: the output string, aligned position by position with the input, and
the correspondence relation among its consonants as coindexed pairs of positions, each written
left position first. -/
structure Cand where
  out : List Seg
  corr : List (ℕ × ℕ)
  deriving DecidableEq, Repr

/-- The segment of a candidate at a position. -/
def Cand.seg (c : Cand) (i : ℕ) : Seg := c.out.getD i .vocoid

/-- CORR at stratum `k`: a violation for each consonant pair at least as similar as the stratum
that does not correspond. -/
def corr (k : Fin 4) : Constraint Cand := fun c ↦
  ((consonantPairs c.out).filter fun p ↦ AtLeast k (c.seg p.1) (c.seg p.2) ∧ p ∉ c.corr).length

/-- IDENT-CLCR(nasal): a violation for each coindexed pair whose left member is nasal and
whose right member is oral. -/
def identCLCR : Constraint Cand := fun c ↦
  (c.corr.filter fun p ↦ (c.seg p.1).IsNasal ∧ ¬ (c.seg p.2).IsNasal).length

/-- IDENT-CRCL(nasal): a violation for each coindexed pair whose right member is nasal and
whose left member is oral. -/
def identCRCL : Constraint Cand := fun c ↦
  (c.corr.filter fun p ↦ ¬ (c.seg p.1).IsNasal ∧ (c.seg p.2).IsNasal).length

/-- IDENT-OI(nasal) for an input: a violation for each segment nasal in the output but not in
the input. -/
def identOI (input : List Seg) : Constraint Cand := fun c ↦
  ((List.range input.length).filter fun i ↦
    ¬ (input.getD i .vocoid).IsNasal ∧ (c.seg i).IsNasal).length

/-- The nasal correspondence hierarchy with IDENT-OI(nasal) interpolated below stratum `k`,
under the IDENT-CC constraints `top` and above `bottom`. -/
def hierarchy (top : List (Constraint Cand)) (k : Fin 4) (input : List Seg)
    (bottom : List (Constraint Cand)) : List (Constraint Cand) :=
  top ++ ((List.finRange 4).map corr).insertIdx (k.val + 1) (identOI input) ++ bottom

/-- The Ngbaka ranking: both directional IDENT-CC constraints undominated and IDENT-OI(nasal)
below the homorganic nasal–prenasal stratum. -/
def ngbaka (input : List Seg) : List (Constraint Cand) :=
  hierarchy [identCLCR, identCRCL] 1 input []

/-- The Kikongo ranking: IDENT-CLCR undominated, IDENT-OI(nasal) below every stratum, and
IDENT-CRCL at the bottom. -/
def kikongo (input : List Seg) : List (Constraint Cand) :=
  hierarchy [identCLCR] 3 input [identCRCL]

/-! ### GEN -/

/-- The outputs for an input: each consonant kept or nasalized. -/
def outputs : List Seg → List (List Seg)
  | [] => [[]]
  | s :: rest =>
    (outputs rest).flatMap fun o ↦ (s :: o) :: if s.nasalize = s then [] else [s.nasalize :: o]

/-- The partitions of a list into blocks. -/
def partitions : List ℕ → List (List (List ℕ))
  | [] => [[]]
  | x :: xs =>
    (partitions xs).flatMap fun P ↦
      ([x] :: P) :: (List.range P.length).map fun i ↦ P.modify i (x :: ·)

/-- The coindexed pairs of a partition, left position first. -/
def corrOf (P : List (List ℕ)) : List (ℕ × ℕ) :=
  P.flatMap fun b ↦ b.flatMap fun i ↦ (b.filter (i < ·)).map (i, ·)

/-- GEN: every output under every coindexation of the consonants. -/
def gen (input : List Seg) : List Cand :=
  (outputs input).flatMap fun o ↦ (partitions (consonants input)).map fun P ↦ ⟨o, corrOf P⟩

/-- The tableau of an input under a ranking, over GEN. -/
def tableau (ranking : List Seg → List (Constraint Cand)) (input : List Seg) :
    Tableau Cand (ranking input).length :=
  Tableau.ofList (gen input).toFinset (ranking input)

/-! ### The typology of the cut -/

/-- A nasal and a consonant across a vocoid. -/
def pair (a b : Seg) : List Seg := [a, .vocoid, b]

/-- Both directional IDENT-CC constraints undominated and IDENT-OI(nasal) below stratum `k`. -/
def cut (k : Fin 4) (input : List Seg) : List (Constraint Cand) :=
  hierarchy [identCLCR, identCRCL] k input []

/-- The typology: a nasal followed by an oral consonant agrees with it, the two corresponding,
exactly when the pair is at least as similar as the cut below which IDENT-OI(nasal) sits;
otherwise the input surfaces faithfully with no correspondence. -/
theorem winner_eq (k : Fin 4) (p : Place) (b : Seg) (hb : b.IsConsonant) (hn : ¬ b.IsNasal) :
    (tableau (cut k) (pair (.stop p .nasal) b)).optimal =
      {if AtLeast k (.stop p .nasal) b then ⟨[.stop p .nasal, .vocoid, b.nasalize], [(0, 2)]⟩
        else ⟨pair (.stop p .nasal) b, []⟩} := by
  revert k p b; decide +kernel

/-- Demoting IDENT-OI(nasal) only widens the agreeing class: a pair that agrees at a cut agrees
at every lower cut. -/
theorem agree_of_le {k k' : Fin 4} (hk : k ≤ k') (p : Place) (b : Seg) (hb : b.IsConsonant)
    (hn : ¬ b.IsNasal)
    (h : (tableau (cut k) (pair (.stop p .nasal) b)).optimal =
      {⟨[.stop p .nasal, .vocoid, b.nasalize], [(0, 2)]⟩}) :
    (tableau (cut k') (pair (.stop p .nasal) b)).optimal =
      {⟨[.stop p .nasal, .vocoid, b.nasalize], [(0, 2)]⟩} := by
  rw [winner_eq k p b hb hn] at h
  rw [winner_eq k' p b hb hn]
  split_ifs at h ⊢ <;>
    first
    | rfl
    | exact absurd (AtLeast.mono ‹AtLeast k _ _› hk) ‹¬ AtLeast k' _ _›
    | exact absurd (Finset.singleton_inj.mp h) (by simp)

/-! ### The rows -/

/-- The segment of a transcription character: nasals *m n ŋ*, voiced stops *b d g*, voiceless
stops *p t k*, the approximant *l*, the fricatives *s z f v*, and vocoids. -/
def segment : Char → Option Seg
  | 'm' => some (.stop .labial .nasal)
  | 'n' => some (.stop .coronal .nasal)
  | 'ŋ' => some (.stop .dorsal .nasal)
  | 'b' => some (.stop .labial .voiced)
  | 'd' => some (.stop .coronal .voiced)
  | 'g' => some (.stop .dorsal .voiced)
  | 'p' => some (.stop .labial .voiceless)
  | 't' => some (.stop .coronal .voiceless)
  | 'k' => some (.stop .dorsal .voiceless)
  | 'l' => some .approximant
  | 's' | 'z' | 'f' | 'v' => some .fricative
  | 'a' | 'e' | 'i' | 'o' | 'u' | 'ɛ' | 'ɔ' | 'w' => some .vocoid
  | _ => none

/-- The segments of a transcription, prenasal stops written with a superscript nasal and
hyphens marking morpheme boundaries. -/
def parse : List Char → List Seg
  | 'ᵐ' :: 'b' :: cs => .stop .labial .prenasal :: parse cs
  | 'ⁿ' :: 'd' :: cs => .stop .coronal .prenasal :: parse cs
  | 'ᵑ' :: 'g' :: cs => .stop .dorsal .prenasal :: parse cs
  | c :: cs => (segment c).toList ++ parse cs
  | [] => []

/-- The words of a language as the fixed points of its grammar: some optimal candidate has the
input as its output. -/
def IsFixedPoint (ranking : List Seg → List (Constraint Cand)) (w : List Seg) : Prop :=
  ∃ c ∈ (tableau ranking w).optimal, c.out = w

instance (ranking : List Seg → List (Constraint Cand)) (w : List Seg) :
    Decidable (IsFixedPoint ranking w) :=
  inferInstanceAs (Decidable (∃ c ∈ (tableau ranking w).optimal, c.out = w))

/-- The Ngbaka words of the rows, with their judgments. -/
def ngbakaData : List (List Seg × Judgment) :=
  (Examples.all.filter (·.language = "ngba1284")).map fun r ↦
    (parse r.primaryText.toList, r.judgment)

/-- Ngbaka's tableaux: a homorganic nasal and prenasal stop agree, the prenasal nasalized, while
a heterorganic pair surfaces faithfully. -/
theorem ngbaka_tableaux :
    (tableau ngbaka (parse "naⁿdɛ".toList)).optimal = {⟨parse "nanɛ".toList, [(0, 2)]⟩} ∧
      (tableau ngbaka (parse "maᵑga".toList)).optimal = {⟨parse "maᵑga".toList, []⟩} := by
  decide +kernel

/-- The morpheme structure constraint: a word of the rows is well formed exactly when it is a
fixed point of the Ngbaka grammar. -/
theorem ngbaka_rows : ∀ d ∈ ngbakaData, d.2 = .acceptable ↔ IsFixedPoint ngbaka d.1 := by
  decide +kernel

/-- The Kikongo alternations of the rows: the underlying and surface stems. -/
def kikongoData : List (List Seg × List Seg) :=
  Examples.all.filterMap fun r ↦ do
    let ur ← r.feature? "underlying"
    let sr ← r.feature? "stem"
    pure (parse ur.toList, parse sr.toList)

/-- A nasal that triggers agreement: a singleton nasal, not the first half of an NC cluster. -/
def Triggers (w : List Seg) (i : ℕ) : Prop :=
  (w.getD i .vocoid).IsNasal ∧ ¬ (w.getD (i + 1) .vocoid).IsConsonant

instance (w : List Seg) (i : ℕ) : Decidable (Triggers w i) := inferInstanceAs (Decidable (_ ∧ _))

/-- Kikongo's surface map: rightward agreement at the Kikongo cut, a consonant at least as
similar as the cut to a preceding trigger nasalized unless it is the second half of an NC
cluster. -/
def harmonize (w : List Seg) : List Seg :=
  w.mapIdx fun j s ↦
    if (∃ i < j, Triggers w i ∧ AtLeast 3 (w.getD i .vocoid) s) ∧
        ¬ (w.getD (j - 1) .vocoid).IsNasal then s.nasalize else s

/-- Every alternation of the rows is the surface map of its underlying stem. -/
theorem kikongo_rows : ∀ d ∈ kikongoData, harmonize d.1 = d.2 := by
  decide +kernel

/-- A stem without NC clusters. -/
def NoCluster (w : List Seg) : Prop :=
  ∀ i < w.length, (w.getD i .vocoid).IsNasal → ¬ (w.getD (i + 1) .vocoid).IsConsonant

instance (w : List Seg) : Decidable (NoCluster w) := inferInstanceAs (Decidable (∀ i < _, _))

/-- The grammar agrees with the map: for the stems without NC clusters and with at most four
consonants, some optimal candidate of the Kikongo ranking has the map's output. -/
theorem kikongo_grammar :
    ∀ d ∈ kikongoData, (consonants d.1).length ≤ 4 → NoCluster d.1 →
      ∃ c ∈ (tableau kikongo d.1).optimal, c.out = harmonize d.1 := by
  decide +kernel

/-- *tum-idi*: the suffix consonant nasalizes and corresponds with the nasal. -/
theorem tumidi :
    (tableau kikongo (parse "tum-idi".toList)).optimal = {⟨parse "tum-ini".toList, [(2, 4)]⟩} := by
  decide +kernel

/-- *nik-ulu*: the voiceless stop is neutral, agreeing with nothing and corresponding with
nothing, while the approximant nasalizes. -/
theorem nikulu :
    (tableau kikongo (parse "nik-ulu".toList)).optimal = {⟨parse "nik-unu".toList, [(0, 4)]⟩} := by
  decide +kernel

/-- The paper's candidates for *kudumuk-ila*: the voiced stop, nasal, and suffix consonant
coindexed with only the suffix nasalized; both nasalized; the stop nasalized and coindexed with
the nasal alone; the nasal and suffix coindexed; the stop and suffix coindexed; and all three
coindexed with nothing nasalized. -/
def kudumukila : List Cand :=
  let k := Seg.stop .dorsal .voiceless
  let d := Seg.stop .coronal .voiced
  let m := Seg.stop .labial .nasal
  let n := Seg.stop .coronal .nasal
  let v := Seg.vocoid
  [⟨[k, v, d, v, m, v, k, v, n, v], [(2, 4), (2, 8), (4, 8)]⟩,
   ⟨[k, v, n, v, m, v, k, v, n, v], [(2, 4), (2, 8), (4, 8)]⟩,
   ⟨[k, v, n, v, m, v, k, v, .approximant, v], [(2, 4)]⟩,
   ⟨[k, v, d, v, m, v, k, v, n, v], [(4, 8)]⟩,
   ⟨[k, v, d, v, m, v, k, v, .approximant, v], [(2, 8)]⟩,
   ⟨[k, v, d, v, m, v, k, v, .approximant, v], [(2, 4), (2, 8), (4, 8)]⟩]

/-- The direction of agreement: with IDENT-CLCR above IDENT-OI(nasal) and IDENT-CRCL below
it, the suffix consonant to the right of the nasal nasalizes and the voiced stop to its left
stays oral. -/
theorem kudumukila_winner :
    (Tableau.ofList kudumukila.toFinset (kikongo (parse "kudumuk-ila".toList))).optimal =
      {kudumukila[0]} := by
  decide +kernel

end RoseWalker2004
