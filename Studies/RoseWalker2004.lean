module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Data.Examples.RoseWalker2004
public import Mathlib.Tactic.DeriveFintype

/-!
# Rose & Walker (2004): A Typology of Consonant Agreement as Correspondence

Similar consonants of an output stand in correspondence, demanded by CORR constraints ranked by
similarity, and IDENT-CC constraints require correspondents to agree, so intervening segments are
neutral. A candidate is a correspondence: input and output aligned position by position, and the
consonants of the output corresponding among themselves, read left to right. The directional
IDENT-CC constraints are MAX and DEP of [nasal] along that relation, as the paper frames them, and
IDENT-OI(nas) is DEP of [nasal] from input to output.

## Main results

* `winner_eq`, `agree_of_le`: a nasal and an oral consonant agree exactly when their pair is at
  least as similar as the cut below which IDENT-OI(nas) sits.
* `ngbaka_rows`: the Ngbaka words of (41) and (42) are the fixed points of its grammar.
* `kikongo_rows`, `kikongo_grammar`: the Kikongo alternations of (43) and (44) are the map
  `harmonize`, which the grammar derives for the stems without NC clusters.
* `tumidi`, `nikulu`, `kudumukila_winner`: the paper's Kikongo tableaux.
* `not_isFaithfulness_corr`, `not_isMarkedness_corr`: CORR is neither faithfulness nor
  markedness, while the IDENT constraints are faithfulness.

## Implementation notes

* GEN keeps or nasalizes each consonant and coindexes the consonants by any partition; the
  tableau of *kudumuk-ila* is over the paper's own candidates.
* `harmonize` is the analysis's generalization for Kikongo, NC clusters neither triggering nor
  undergoing. The paper derives that neutrality from SROLE-CC (55), which is not formalized, nor
  are the exclusion of prefixes from the stem domain and the laryngeal case studies.
* Transcriptions omit tone.

## References

* [rose-walker-2004]
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

/-- An output candidate: the output string, aligned position by position with the input, and
the correspondence relation among its consonants as coindexed pairs of positions, each written
left position first. -/
structure Cand where
  out : List Seg
  corr : List (ℕ × ℕ)
  deriving DecidableEq, Repr

/-- The correspondence of a candidate to an input: input and output correspond position by
position, and the consonants of the output correspond as the candidate coindexes them, each pair
read left to right. -/
def Cand.correspondence (input : List Seg) (c : Cand) : Correspondence BinaryRole Seg :=
  .ofPairs (fun | .lhs => input | .rhs => c.out) fun
    | .lhs, .rhs | .rhs, .lhs => Correspondence.diagonalPairs input.length
    | .rhs, .rhs => c.corr
    | .lhs, .lhs => []

/-- CORR at stratum `k` of the nasal correspondence hierarchy (47): a violation for each pair of
output consonants at least as similar as the stratum, left first, that do not correspond. -/
def corr (k : Fin 4) : Constraint (Correspondence BinaryRole Seg) := fun c ↦
  let C := Finset.univ.filter fun i : Fin (c.form .rhs).length ↦ (c.form .rhs)[i].IsConsonant
  ((C ×ˢ C).filter fun p ↦ p.1 < p.2 ∧ AtLeast k (c.form .rhs)[p.1] (c.form .rhs)[p.2] ∧
    p ∉ c.edge .rhs .rhs).card

/-- IDENT-CLCR(nas) (51a): MAX of [nasal] along the correspondence of the output read left to
right, a violation for each nasal with an oral correspondent to its right. -/
def identCLCR : Constraint (Correspondence BinaryRole Seg) :=
  (·.maxViolFeature Seg.IsNasal .rhs .rhs)

/-- IDENT-CRCL(nas) (51b): DEP of [nasal] along the correspondence of the output read left to
right, a violation for each nasal with an oral correspondent to its left. -/
def identCRCL : Constraint (Correspondence BinaryRole Seg) :=
  (·.depViolFeature Seg.IsNasal .rhs .rhs)

/-- IDENT-OI(nas): DEP of [nasal] from input to output, a violation for each segment nasal in the
output but not in the input. -/
def identOI : Constraint (Correspondence BinaryRole Seg) :=
  (·.depViolFeature Seg.IsNasal .lhs .rhs)

/-- The nasal correspondence hierarchy with IDENT-OI(nas) interpolated below stratum `k`, under
the IDENT-CC constraints `top` and above `bottom`. -/
def hierarchy (top : List (Constraint (Correspondence BinaryRole Seg))) (k : Fin 4)
    (bottom : List (Constraint (Correspondence BinaryRole Seg))) :
    List (Constraint (Correspondence BinaryRole Seg)) :=
  top ++ ((List.finRange 4).map corr).insertIdx (k.val + 1) identOI ++ bottom

/-- The Ngbaka ranking (57b): both directional IDENT-CC constraints undominated and
IDENT-OI(nas) below the homorganic nasal–prenasal stratum. -/
def ngbaka : List (Constraint (Correspondence BinaryRole Seg)) :=
  hierarchy [identCLCR, identCRCL] 1 []

/-- The Kikongo ranking (57a): IDENT-CLCR undominated, IDENT-OI(nas) below every stratum, and
IDENT-CRCL at the bottom. -/
def kikongo : List (Constraint (Correspondence BinaryRole Seg)) :=
  hierarchy [identCLCR] 3 [identCRCL]

/-! ### Faithfulness and correspondence -/

theorem isFaithfulness_identCLCR : Correspondence.IsFaithfulness identCLCR := fun s ↦ by
  simp [identCLCR, Correspondence.maxViolFeature, Correspondence.identity]

theorem isFaithfulness_identCRCL : Correspondence.IsFaithfulness identCRCL := fun s ↦ by
  simp [identCRCL, Correspondence.depViolFeature, Correspondence.identity]

theorem isFaithfulness_identOI : Correspondence.IsFaithfulness identOI := fun s ↦ by
  rw [identOI, Correspondence.identity, Correspondence.depViolFeature_of_diagonal _ _ _ _
    (Correspondence.parallel_edge_lhs_rhs s s)]
  induction s with
  | nil => rfl
  | cons a s ih => simpa [List.countP_cons] using ih

/-- CORR is neither faithfulness, since the fully faithful candidate of two identical nasals
violates it, nor markedness, since two candidates with the same output can differ on it: it
demands correspondence itself. -/
theorem not_isFaithfulness_corr (k : Fin 4) : ¬ Correspondence.IsFaithfulness (corr k) := by
  have : ∀ k, corr k (.identity [.stop .coronal .nasal, .vocoid, .stop .coronal .nasal]) ≠ 0 := by
    decide
  exact fun h ↦ this k (h _)

theorem not_isMarkedness_corr (k : Fin 4) : ¬ Correspondence.IsMarkedness .rhs (corr k) := by
  let w : List Seg := [.stop .coronal .nasal, .vocoid, .stop .coronal .nasal]
  have : ∀ k, corr k ((⟨w, []⟩ : Cand).correspondence []) ≠
      corr k ((⟨w, [(0, 2)]⟩ : Cand).correspondence []) := by
    decide
  exact fun h ↦ this k (h rfl)

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

/-- The tableau of an input under a ranking, over GEN, each candidate evaluated as its
correspondence to the input. -/
def tableau (ranking : List (Constraint (Correspondence BinaryRole Seg))) (input : List Seg) :=
  Tableau.ofList (gen input).toFinset (ranking.map (·.comap (Cand.correspondence input)))

/-! ### The typology of the cut -/

/-- A nasal and a consonant across a vocoid. -/
def pair (a b : Seg) : List Seg := [a, .vocoid, b]

/-- Both directional IDENT-CC constraints undominated and IDENT-OI(nasal) below stratum `k`. -/
def cut (k : Fin 4) : List (Constraint (Correspondence BinaryRole Seg)) :=
  hierarchy [identCLCR, identCRCL] k []

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
def IsFixedPoint (ranking : List (Constraint (Correspondence BinaryRole Seg))) (w : List Seg) :
    Prop :=
  ∃ c ∈ (tableau ranking w).optimal, c.out = w

instance (ranking : List (Constraint (Correspondence BinaryRole Seg))) (w : List Seg) :
    Decidable (IsFixedPoint ranking w) :=
  inferInstanceAs (Decidable (∃ c ∈ (tableau ranking w).optimal, c.out = w))

/-- The Ngbaka words of the rows, with their judgments. -/
def ngbakaData : List (List Seg × Judgment) :=
  (Examples.all.filter (·.language = "ngba1284")).map fun r ↦
    (parse r.primaryText.toList, r.judgment)

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
    (Tableau.ofList kudumukila.toFinset
      (kikongo.map (·.comap (Cand.correspondence (parse "kudumuk-ila".toList))))).optimal =
      {kudumukila[0]} := by
  decide +kernel

end RoseWalker2004
