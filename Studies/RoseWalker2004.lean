module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Coindexation
public import Linglib.Phonology.OptimalityTheory.Filtration
public import Linglib.Data.Examples.RoseWalker2004
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Rose & Walker (2004): A Typology of Consonant Agreement as Correspondence

Similar consonants of an output stand in correspondence, demanded by CORR constraints ranked by
similarity, and IDENT-CC constraints require correspondents to agree, so intervening segments are
neutral. A candidate is an output whose consonants are coindexed, input and output being
coindexed position by position. The directional IDENT-CC constraints read the corresponding
pairs of the output left to right, and IDENT-OI(nas) is DEP of [nasal] from input to output.

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

/-- An output candidate: the output string, each segment with the indices it bears on its
correspondence with the other consonants of the output. -/
abbrev Cand := List (Correspondence.Segment Seg)

/-- The string `w` with the positions of each block of `P` coindexed, a block of one position
bearing no index. -/
def coindex (w : List Seg) (P : List (List ℕ)) : Cand :=
  w.zipIdx.map fun x ↦
    ⟨x.1, ((P.filter (1 < ·.length)).zipIdx.filter fun b ↦ x.2 ∈ b.1).map (·.2)⟩

/-- The coindexation of a candidate with an input: input and output are coindexed position by
position, and each output segment bears toward the output the indices of the candidate. -/
def Cand.correspondence (input : List Seg) (c : Cand) :
    Correspondence.Coindexation BinaryRole Seg where
  form
    | .lhs => input.zipIdx.map fun x ↦ (x.1, fun | .rhs => [x.2] | .lhs => [])
    | .rhs => c.zipIdx.map fun x ↦ (x.1.seg, fun | .lhs => [x.2] | .rhs => x.1.indices)

/-- The pairs of the members of a list, the earlier member first. -/
def precedencePairs {β : Type*} : List β → List (β × β)
  | [] => []
  | x :: l => l.map (x, ·) ++ precedencePairs l

/-- The pairs of segments of the output, the left one first, with the indices they bear toward
the output. -/
def outputPairs (c : Correspondence.Coindexation BinaryRole Seg) :
    List (Correspondence.Segment Seg × Correspondence.Segment Seg) :=
  precedencePairs (c.toward .rhs .rhs)

/-- CORR at stratum `k` of the nasal correspondence hierarchy (47): a violation for each pair of
output consonants at least as similar as the stratum, left first, that do not correspond. -/
def corr (k : Fin 4) : Constraint (Correspondence.Coindexation BinaryRole Seg) := fun c ↦
  (outputPairs c).countP fun p ↦ p.1.seg.IsConsonant ∧ p.2.seg.IsConsonant ∧
    AtLeast k p.1.seg p.2.seg ∧ ¬ p.1.Corresponds p.2

/-- IDENT-CLCR(nas) (51a): a violation for each nasal of the output with an oral correspondent
to its right. -/
def identCLCR : Constraint (Correspondence.Coindexation BinaryRole Seg) := fun c ↦
  (outputPairs c).countP fun p ↦ p.1.Corresponds p.2 ∧ p.1.seg.IsNasal ∧ ¬ p.2.seg.IsNasal

/-- IDENT-CRCL(nas) (51b): a violation for each nasal of the output with an oral correspondent
to its left. -/
def identCRCL : Constraint (Correspondence.Coindexation BinaryRole Seg) := fun c ↦
  (outputPairs c).countP fun p ↦ p.1.Corresponds p.2 ∧ ¬ p.1.seg.IsNasal ∧ p.2.seg.IsNasal

/-- IDENT-OI(nas) (10b): DEP of [nasal] from the input to the output, a violation for each
output nasal whose input correspondent is oral. -/
def identOI : Constraint (Correspondence.Coindexation BinaryRole Seg) :=
  (·.depViolFeature Seg.IsNasal .lhs .rhs)

/-- The nasal correspondence hierarchy with IDENT-OI(nas) interpolated below stratum `k`, under
the IDENT-CC constraints `top` and above `bottom`. -/
def hierarchy (top : List (Constraint (Correspondence.Coindexation BinaryRole Seg))) (k : Fin 4)
    (bottom : List (Constraint (Correspondence.Coindexation BinaryRole Seg))) :
    List (Constraint (Correspondence.Coindexation BinaryRole Seg)) :=
  top ++ ((List.finRange 4).map corr).insertIdx (k.val + 1) identOI ++ bottom

/-- The Ngbaka ranking (57b): both directional IDENT-CC constraints undominated and
IDENT-OI(nas) below the homorganic nasal–prenasal stratum. -/
def ngbaka : List (Constraint (Correspondence.Coindexation BinaryRole Seg)) :=
  hierarchy [identCLCR, identCRCL] 1 []

/-- The Kikongo ranking (57a): IDENT-CLCR undominated, IDENT-OI(nas) below every stratum, and
IDENT-CRCL at the bottom. -/
def kikongo : List (Constraint (Correspondence.Coindexation BinaryRole Seg)) :=
  hierarchy [identCLCR] 3 [identCRCL]

/-! ### Faithfulness and correspondence -/

theorem mem_of_mem_precedencePairs {β : Type*} {l : List β} {p : β × β}
    (h : p ∈ precedencePairs l) : p.1 ∈ l ∧ p.2 ∈ l := by
  induction l with
  | nil => simp [precedencePairs] at h
  | cons x l ih =>
    rcases List.mem_append.1 h with h | h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ hy⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, List.mem_cons_of_mem _ (ih h).2⟩

/-- No two segments of the output of the fully faithful candidate correspond. -/
private theorem not_corresponds_of_mem_outputPairs_identity {s : List Seg}
    {p : Correspondence.Segment Seg × Correspondence.Segment Seg}
    (hp : p ∈ outputPairs (.identity s)) : ¬ p.1.Corresponds p.2 := by
  have h := (mem_of_mem_precedencePairs hp).1
  rw [Correspondence.Coindexation.toward_identity_self] at h
  obtain ⟨a, -, ha⟩ := List.mem_map.1 h
  simp [Correspondence.Segment.Corresponds, ← ha]

theorem isFaithfulness_identCLCR : Correspondence.Coindexation.IsFaithfulness identCLCR :=
  fun _ ↦ List.countP_eq_zero.2 fun _ hp ↦ by
    simp [not_corresponds_of_mem_outputPairs_identity hp]

theorem isFaithfulness_identCRCL : Correspondence.Coindexation.IsFaithfulness identCRCL :=
  fun _ ↦ List.countP_eq_zero.2 fun _ hp ↦ by
    simp [not_corresponds_of_mem_outputPairs_identity hp]

theorem isFaithfulness_identOI : Correspondence.Coindexation.IsFaithfulness identOI := fun s ↦ by
  rw [identOI, Correspondence.Coindexation.depViolFeature,
    Correspondence.Coindexation.toward_identity (by decide),
    Correspondence.Coindexation.toward_identity (by decide)]
  exact Correspondence.maxViolFeature_indexed_self _ s

/-- CORR is neither faithfulness, since the fully faithful candidate of two identical nasals
violates it, nor markedness, since two candidates with the same output can differ on it: it
demands correspondence itself. -/
theorem not_isFaithfulness_corr (k : Fin 4) :
    ¬ Correspondence.Coindexation.IsFaithfulness (corr k) := by
  have : ∀ k, corr k (.identity [.stop .coronal .nasal, .vocoid, .stop .coronal .nasal]) ≠ 0 := by
    decide
  exact fun h ↦ this k (h _)

theorem not_isMarkedness_corr (k : Fin 4) :
    ¬ Correspondence.Coindexation.IsMarkedness .rhs (corr k) := by
  let w : List Seg := [.stop .coronal .nasal, .vocoid, .stop .coronal .nasal]
  have : ∀ k, corr k ((coindex w []).correspondence []) ≠
      corr k ((coindex w [[0, 2]]).correspondence []) := by
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

/-- GEN: every output under every coindexation of the consonants. -/
def gen (input : List Seg) : List Cand :=
  (outputs input).flatMap fun o ↦ (partitions (consonants input)).map fun P ↦ coindex o P

/-- The optimal candidates of an input under a ranking, over GEN, each candidate evaluated as
its correspondence to the input. -/
def optimal (ranking : List (Constraint (Correspondence.Coindexation BinaryRole Seg)))
    (input : List Seg) : Finset Cand :=
  Constraint.evalOn (Cand.correspondence input) (gen input).toFinset ranking

/-! ### The typology of the cut -/

/-- A nasal and a consonant across a vocoid. -/
def pair (a b : Seg) : List Seg := [a, .vocoid, b]

/-- Both directional IDENT-CC constraints undominated and IDENT-OI(nasal) below stratum `k`. -/
def cut (k : Fin 4) : List (Constraint (Correspondence.Coindexation BinaryRole Seg)) :=
  hierarchy [identCLCR, identCRCL] k []

/-- The typology: a nasal followed by an oral consonant agrees with it, the two corresponding,
exactly when the pair is at least as similar as the cut below which IDENT-OI(nasal) sits;
otherwise the input surfaces faithfully with no correspondence. -/
theorem winner_eq (k : Fin 4) (p : Place) (b : Seg) (hb : b.IsConsonant) (hn : ¬ b.IsNasal) :
    optimal (cut k) (pair (.stop p .nasal) b) =
      {if AtLeast k (.stop p .nasal) b then coindex [.stop p .nasal, .vocoid, b.nasalize] [[0, 2]]
        else coindex (pair (.stop p .nasal) b) []} := by
  revert k p b; decide +kernel

/-- Demoting IDENT-OI(nasal) only widens the agreeing class: a pair that agrees at a cut agrees
at every lower cut. -/
theorem agree_of_le {k k' : Fin 4} (hk : k ≤ k') (p : Place) (b : Seg) (hb : b.IsConsonant)
    (hn : ¬ b.IsNasal)
    (h : optimal (cut k) (pair (.stop p .nasal) b) =
      {coindex [.stop p .nasal, .vocoid, b.nasalize] [[0, 2]]}) :
    optimal (cut k') (pair (.stop p .nasal) b) =
      {coindex [.stop p .nasal, .vocoid, b.nasalize] [[0, 2]]} := by
  rw [winner_eq k p b hb hn] at h
  rw [winner_eq k' p b hb hn]
  split_ifs at h ⊢ <;>
    first
    | rfl
    | exact absurd (AtLeast.mono ‹AtLeast k _ _› hk) ‹¬ AtLeast k' _ _›
    | exact absurd (Finset.singleton_inj.mp h) (by simp [coindex, pair])

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
def IsFixedPoint (ranking : List (Constraint (Correspondence.Coindexation BinaryRole Seg)))
    (w : List Seg) : Prop :=
  ∃ c ∈ optimal ranking w, c.map (·.seg) = w

instance (ranking : List (Constraint (Correspondence.Coindexation BinaryRole Seg))) (w : List Seg) :
    Decidable (IsFixedPoint ranking w) :=
  inferInstanceAs (Decidable (∃ c ∈ optimal ranking w, c.map (·.seg) = w))

/-- The Ngbaka words of the rows, with their judgments. -/
def ngbakaData : List (List Seg × Judgment) :=
  (Examples.all.filter (·.language = .ngbakaMabo)).map fun r ↦
    (parse r.primaryText.toList, r.judgment)

theorem ngbaka_tableaux :
    optimal ngbaka (parse "naⁿdɛ".toList) = {coindex (parse "nanɛ".toList) [[0, 2]]} ∧
      optimal ngbaka (parse "maᵑga".toList) = {coindex (parse "maᵑga".toList) []} := by
  decide +kernel

/-- The morpheme structure constraint: a word of the rows is well formed exactly when it is a
fixed point of the Ngbaka grammar ((41), (42)). -/
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
      ∃ c ∈ optimal kikongo d.1, c.map (·.seg) = harmonize d.1 := by
  decide +kernel

/-- *tum-idi*: the suffix consonant nasalizes and corresponds with the nasal. -/
theorem tumidi :
    optimal kikongo (parse "tum-idi".toList) =
      {coindex (parse "tum-ini".toList) [[2, 4]]} := by
  decide +kernel

/-- *nik-ulu*: the voiceless stop is neutral, agreeing with nothing and corresponding with
nothing, while the approximant nasalizes. -/
theorem nikulu :
    optimal kikongo (parse "nik-ulu".toList) =
      {coindex (parse "nik-unu".toList) [[0, 4]]} := by
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
  [coindex [k, v, d, v, m, v, k, v, n, v] [[2, 4, 8]],
   coindex [k, v, n, v, m, v, k, v, n, v] [[2, 4, 8]],
   coindex [k, v, n, v, m, v, k, v, .approximant, v] [[2, 4]],
   coindex [k, v, d, v, m, v, k, v, n, v] [[4, 8]],
   coindex [k, v, d, v, m, v, k, v, .approximant, v] [[2, 8]],
   coindex [k, v, d, v, m, v, k, v, .approximant, v] [[2, 4, 8]]]

/-- The direction of agreement: with IDENT-CLCR above IDENT-OI(nasal) and IDENT-CRCL below
it, the suffix consonant to the right of the nasal nasalizes and the voiced stop to its left
stays oral. -/
theorem kudumukila_winner :
    Constraint.eval kudumukila.toFinset
      (kikongo.map (·.comap (Cand.correspondence (parse "kudumuk-ila".toList)))) =
      {kudumukila[0]} := by
  decide +kernel

end RoseWalker2004
