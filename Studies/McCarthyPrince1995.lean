module

public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.McCarthyPrince1995
public import Linglib.Fragments.Akan.Phonology
public import Linglib.Phonology.OptimalityTheory.Constraint.ForbiddenFactors
public import Linglib.Phonology.OptimalityTheory.Correspondence.Coindexation
public import Linglib.Phonology.OptimalityTheory.Evaluation
public import Mathlib.Tactic.FinCases

/-!
# McCarthy and Prince (1995): Faithfulness and Reduplicative Identity

In the basic model of [mccarthy-prince-1995] a reduplicated form has an input stem, a base and a
reduplicant. Faithfulness constraints relate the input to the base, identity constraints relate
the base to the reduplicant, and a phonological constraint reads the surface string. A candidate
is a base and a reduplicant, its marks are computed from the correspondence between the three
strings and from the surface string, and each result says which rankings select which candidate.

Javanese deletes intervocalic *h*: the ranking that does so in the unreduplicated *ara–e* is
`Javanese.DeletesH`. Under it the suffixed reduplication of *bəḍah* loses *h* from both copies,
though only one is intervocalic, exactly when MAX-BR dominates MAX-IO
(`Javanese.overapplication_iff`), and no ranking keeps both
(`Javanese.underapplication_notMem`). Balangao copies the first two syllables of *tagtag*
without the final coda exactly when MAX-IO dominates NO-CODA and NO-CODA dominates MAX-BR
(`Balangao.optimal_iff`). Akan palatalizes a velar before a front vowel, as in *tɕɛ*
(`Akan.Palatalizes`), but not when a coronal begins the next syllable, as in *kɛsɪ*
(`Akan.Blocks`). The reduplicant of *kɪ–ka* is unpalatalized exactly when a ranking blocks
palatalization in *kɛsɪ* and has IDENT-BR dominate PAL (`Akan.underapplication_iff`).

## Implementation notes

Javanese is analysed with suffixing reduplication. Its prefixing alternative, where DEP-BR does
the work of MAX-BR, is not formalized. A coda is counted as a consonant that no vowel follows,
which suffices for the CV(C) syllables of the Balangao forms.

The paper measures OCP(+cor) by featural duplication in dissimilar constituents: a syllable
whose onset and vowel share [+coronal, −anterior] may not be followed by a coronal that does
not share those features with its own vowel. Here a syllable is a consonant and a vowel, and the
constraint is violated once by a syllable of palatal onset and front vowel before a syllable of
coronal onset that is not itself of that kind. The overapplying candidate of the summary tableau
then has one mark where the paper prints three; no ranking result depends on the count. The top
constraint of the paper's Akan ranking, IDENT-IO(+cor), which no candidate here violates, is
left out. The Akan segments are those of the Akan fragment.

## References

* [mccarthy-prince-1995]
-/

@[expose] public section

namespace McCarthyPrince1995

open Phonology OptimalityTheory Subregular

/-! ### Phonological constraints on a surface string -/

section Surface

variable {σ : Type*} (IsVowel : σ → Prop) [DecidablePred IsVowel]

/-- The factors that mark a coda, a consonant followed by a consonant or by the right edge. -/
def codaFactors : Set (Augmented σ) :=
  {f | ∃ a b, ¬ IsVowel a ∧ (∀ y ∈ b, ¬ IsVowel y) ∧ f = [some a, b]}

instance : DecidablePred (· ∈ codaFactors IsVowel) := fun f ↦ match f with
  | [some a, b] => decidable_of_iff (¬ IsVowel a ∧ ∀ y ∈ b, ¬ IsVowel y) (by simp [codaFactors])
  | [] | [_] | [none, _] | _ :: _ :: _ :: _ => isFalse (by simp [codaFactors])

/-- The number of codas of a string, a coda being a consonant that no vowel follows. -/
def codas : Constraint (List σ) := Constraint.ofForbiddenFactors 2 (codaFactors IsVowel)

/-- The factors in which `x` stands between two vowels. -/
def intervocalicFactors (x : σ) : Set (Augmented σ) :=
  {f | ∃ a c, IsVowel a ∧ IsVowel c ∧ f = [some a, some x, some c]}

instance [DecidableEq σ] (x : σ) : DecidablePred (· ∈ intervocalicFactors IsVowel x) := fun f ↦
  match f with
  | [some a, some b, some c] =>
    decidable_of_iff (IsVowel a ∧ IsVowel c ∧ b = x) (by simp [intervocalicFactors, eq_comm])
  | [] | [_] | [_, _] | [none, _, _] | [some _, none, _] | [some _, some _, none]
  | _ :: _ :: _ :: _ :: _ => isFalse (by simp [intervocalicFactors])

/-- The number of occurrences of `x` between two vowels. -/
def intervocalic [DecidableEq σ] (x : σ) : Constraint (List σ) :=
  Constraint.ofForbiddenFactors 3 (intervocalicFactors IsVowel x)

end Surface

/-! ### Contiguity and anchoring

The paper illustrates the two contiguity constraints of its Appendix A on maps between strings of
*x*, *y* and *z*: deleting or inserting a medial segment violates one of them, and deleting or
inserting a final segment violates neither. -/

/-- The map from the string `s` to the string `t` relating the positions paired in `l`. -/
private def map (s t : List Char) (l : List (ℕ × ℕ)) :
    Correspondence.Coindexation BinaryRole Char :=
  .ofPairs (fun | .lhs => s | .rhs => t) [(.lhs, .rhs, l)]

/-- The map *xyz* → *xz* skips *y* and violates I-CONTIG. -/
example : (map ['x', 'y', 'z'] ['x', 'z'] [(0, 0), (2, 1)]).contigIViol .lhs .rhs = 1 := by decide

/-- The map *xyz* → *xy* deletes at the edge and satisfies I-CONTIG. -/
example : (map ['x', 'y', 'z'] ['x', 'y'] [(0, 0), (1, 1)]).contigIViol .lhs .rhs = 0 := by decide

/-- The map *xz* → *xyz* intrudes *y* and violates O-CONTIG. -/
example : (map ['x', 'z'] ['x', 'y', 'z'] [(0, 0), (1, 2)]).contigOViol .lhs .rhs = 1 := by decide

/-- The map *xy* → *xyz* inserts at the edge and satisfies O-CONTIG. -/
example : (map ['x', 'y'] ['x', 'y', 'z'] [(0, 0), (1, 1)]).contigOViol .lhs .rhs = 0 := by decide

/-- Deleting the final segment keeps the left edges in correspondence and not the right. -/
example : (map ['x', 'y', 'z'] ['x', 'y'] [(0, 0), (1, 1)]).anchorLViol .lhs .rhs = 0 ∧
    (map ['x', 'y', 'z'] ['x', 'y'] [(0, 0), (1, 1)]).anchorRViol .lhs .rhs = 1 := by decide

/-! ### Candidates of the basic model -/

/-- A candidate of the basic model: the base and the reduplicant of an output form. -/
structure Candidate (α : Type*) where
  /-- The base, the output of the stem. -/
  base : List α
  /-- The reduplicant, the output of the reduplicative affix. -/
  reduplicant : List α
  deriving DecidableEq

namespace Candidate

variable {α : Type*}

/-- An unreduplicated word, a candidate with no reduplicant. -/
def ofWord (w : List α) : Candidate α := ⟨w, []⟩

/-- The correspondence of a candidate with the input `stem`, the three strings coindexed
position by position. -/
def correspondence (stem : List α) (c : Candidate α) :
    Correspondence.Coindexation ReduplicationRole α :=
  .reduplication stem c.base c.reduplicant

end Candidate

/-! ### Javanese *h*-deletion: overapplication -/

namespace Javanese

/-- The segments of *bəḍah* 'broken', *arah* 'direction' and the demonstrative suffix *-e*. -/
inductive Seg where
  | b | schwa | d | a | h | e | r
  deriving DecidableEq, Repr

/-- The vowels. -/
def Seg.IsVowel : Seg → Prop
  | .schwa | .a | .e => True
  | _ => False

instance : DecidablePred Seg.IsVowel := fun s ↦ by cases s <;> unfold Seg.IsVowel <;> infer_instance

/-- The marks of the unreduplicated word `out–e` for the input `stem–e`: none for MAX-BR, then
*VhV and MAX-IO. -/
def wordMarks (stem out : List Seg) : Fin 3 → ℕ :=
  ![0, intervocalic Seg.IsVowel .h (out ++ [.e]),
    (Correspondence.Coindexation.parallel stem out).maxViol .lhs .rhs]

/-- (36): a ranking deletes intervocalic *h* when it selects *ara–e* over *arah–e* for
/arah–e/. -/
def DeletesH (r : Ranking.Enumeration (Fin 3) 3) : Prop :=
  r.optimal (wordMarks [.a, .r, .a, .h]) {[.a, .r, .a], [.a, .r, .a, .h]} = {[.a, .r, .a]}

-- (36)
theorem deletesH_iff {r : Ranking.Enumeration (Fin 3) 3} : DeletesH r ↔ r.Dominates 1 2 := by
  rw [DeletesH, Ranking.Enumeration.optimal_eq_singleton_iff_pair rfl (by decide),
    Ranking.Enumeration.profile_lt_iff_dominates (i := 1) (j := 2) (by decide) (by decide)]

/-- The stem *bəḍah*. -/
def stem : List Seg := [.b, .schwa, .d, .a, .h]

/-- (6): the candidates for /bəḍah–RED–e/. Overapplication is *bəḍa–bəḍa–e*, with *h* lost from
base and reduplicant, underapplication *bəḍah–bəḍah–e*, with *h* kept in both, and normal
application *bəḍah–bəḍa–e*, with *h* lost where it is intervocalic. -/
def candidate : Examples.Application → Candidate Seg
  | .over => ⟨[.b, .schwa, .d, .a], [.b, .schwa, .d, .a]⟩
  | .under => ⟨stem, stem⟩
  | .normal => ⟨stem, [.b, .schwa, .d, .a]⟩

/-- The candidates of tableau (39). -/
def candidates : Finset (Candidate Seg) := Finset.univ.image candidate

/-- The constraints of (39) are MAX-BR, *VhV and MAX-IO; the surface string is the base followed
by the reduplicant and the suffix. -/
def marks (c : Candidate Seg) : Fin 3 → ℕ :=
  ![(c.correspondence stem).maxViol .base .reduplicant,
    intervocalic Seg.IsVowel .h (c.base ++ c.reduplicant ++ [.e]),
    (c.correspondence stem).maxViol .input .base]

-- (39)
theorem marks_eq :
    marks (candidate .over) = ![0, 0, 1] ∧ marks (candidate .under) = ![0, 1, 0] ∧
      marks (candidate .normal) = ![1, 0, 0] := by
  decide

section

open Ranking.Enumeration

variable {r : Ranking.Enumeration (Fin 3) 3}

/-- A ranking that deletes intervocalic *h* loses it from both copies of *bəḍah* exactly when
MAX-BR dominates MAX-IO. -/
theorem overapplication_iff (h : DeletesH r) :
    r.optimal marks candidates = {candidate .over} ↔ r.Dominates 0 2 := by
  have hu := profile_lt_iff_dominates (σ := r) (T := marks) (c := candidate .over)
    (d := candidate .under) (i := 1) (j := 2) (by decide) (by decide)
  have hn := profile_lt_iff_dominates (σ := r) (T := marks) (c := candidate .over)
    (d := candidate .normal) (i := 0) (j := 2) (by decide) (by decide)
  rw [optimal_eq_singleton_iff_profile_lt]
  refine ⟨fun hw ↦ hn.1 (hw.2 _ (by decide) (by decide)), fun h02 ↦ ⟨by decide, fun d hd hne ↦ ?_⟩⟩
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hd
  cases a
  exacts [absurd rfl hne, hu.2 (deletesH_iff.1 h), hn.2 h02]

-- the paragraph after (39)
theorem normalApplication_iff (h : DeletesH r) :
    r.optimal marks candidates = {candidate .normal} ↔ r.Dominates 2 0 := by
  have ho := profile_lt_iff_dominates (σ := r) (T := marks) (c := candidate .normal)
    (d := candidate .over) (i := 2) (j := 0) (by decide) (by decide)
  have hu := profile_lt_iff_dominates (σ := r) (T := marks) (c := candidate .normal)
    (d := candidate .under) (i := 1) (j := 0) (by decide) (by decide)
  rw [optimal_eq_singleton_iff_profile_lt]
  refine ⟨fun hw ↦ ho.1 (hw.2 _ (by decide) (by decide)), fun h20 ↦ ⟨by decide, fun d hd hne ↦ ?_⟩⟩
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hd
  cases a
  exacts [ho.2 h20, hu.2 (lt_trans (deletesH_iff.1 h) h20), absurd rfl hne]

/-- Underapplication is out of reach: no ranking that deletes intervocalic *h* keeps both *h*s
of the reduplicated form. -/
theorem underapplication_notMem (h : DeletesH r) :
    candidate .under ∉ r.optimal marks candidates :=
  notMem_optimal_of_forall_dominates (d := candidate .over) (i := 1) (by decide) (by decide)
    fun k hk ↦ (by decide : ∀ k, marks (candidate .under) k < marks (candidate .over) k → k = 2)
      k hk ▸ deletesH_iff.1 h

-- (6)
theorem judgments (h : DeletesH r) (h02 : r.Dominates 0 2) :
    ∀ e ∈ Examples.all, e.language = .javanese → ∀ a ∈ Examples.application e,
      (candidate a ∈ r.optimal marks candidates ↔ e.judgment = .acceptable) := by
  rw [(overapplication_iff h).2 h02]
  decide

end

end Javanese

/-! ### Balangao: emergence of the unmarked -/

namespace Balangao

/-- The segments of *tagtag*. -/
inductive Seg where
  | t | a | g
  deriving DecidableEq, Repr

/-- The vowel. -/
def Seg.IsVowel : Seg → Prop
  | .a => True
  | _ => False

instance : DecidablePred Seg.IsVowel := fun s ↦ by cases s <;> unfold Seg.IsVowel <;> infer_instance

/-- The stem *tagtag*. -/
def stem : List Seg := [.t, .a, .g, .t, .a, .g]

/-- The marks of the unreduplicated word `out` for the input /tagtag/: MAX-IO and NO-CODA, and
none for MAX-BR. -/
def wordMarks (out : List Seg) : Fin 3 → ℕ :=
  ![(Correspondence.Coindexation.parallel stem out).maxViol .lhs .rhs, codas Seg.IsVowel out, 0]

/-- (16): a ranking keeps codas when it selects *tagtag* over *tagta* for /tagtag/. -/
def KeepsCodas (r : Ranking.Enumeration (Fin 3) 3) : Prop :=
  r.optimal wordMarks {stem, [.t, .a, .g, .t, .a]} = {stem}

-- (16)
theorem keepsCodas_iff {r : Ranking.Enumeration (Fin 3) 3} : KeepsCodas r ↔ r.Dominates 0 1 := by
  rw [KeepsCodas, Ranking.Enumeration.optimal_eq_singleton_iff_pair rfl (by decide),
    Ranking.Enumeration.profile_lt_iff_dominates (i := 0) (j := 1) (by decide) (by decide)]

/-- *tagta–tagta*, with the final coda lost from the base too. -/
def unfaithfulBase : Candidate Seg := ⟨[.t, .a, .g, .t, .a], [.t, .a, .g, .t, .a]⟩

/-- *tagtag–tagtag*, an exact copy. -/
def exactCopy : Candidate Seg := ⟨stem, stem⟩

/-- *tagta–tagtag*, with a reduplicant that lacks the final coda. -/
def codalessReduplicant : Candidate Seg := ⟨stem, [.t, .a, .g, .t, .a]⟩

/-- The candidates of tableau (106) for /RED–tagtag/. -/
def candidates : Finset (Candidate Seg) := {unfaithfulBase, exactCopy, codalessReduplicant}

/-- The constraints of (106) are MAX-IO, NO-CODA and MAX-BR; the surface string is the
reduplicant followed by the base. -/
def marks (c : Candidate Seg) : Fin 3 → ℕ :=
  ![(c.correspondence stem).maxViol .input .base, codas Seg.IsVowel (c.reduplicant ++ c.base),
    (c.correspondence stem).maxViol .base .reduplicant]

-- (106)
theorem marks_eq :
    marks unfaithfulBase = ![1, 2, 0] ∧ marks exactCopy = ![0, 4, 0] ∧
      marks codalessReduplicant = ![0, 3, 1] := by
  decide

open Ranking.Enumeration in
/-- The coda-sparing reduplicant wins exactly when a ranking keeps codas in unreduplicated words
and has NO-CODA dominate MAX-BR, the ranking for emergence of the unmarked. -/
theorem optimal_iff (r : Ranking.Enumeration (Fin 3) 3) :
    r.optimal marks candidates = {codalessReduplicant} ↔ KeepsCodas r ∧ r.Dominates 1 2 := by
  have ha := profile_lt_iff_forall_dominates (σ := r) (T := marks) (c := codalessReduplicant)
    (d := unfaithfulBase) (i := 0) (by decide)
  have hb := profile_lt_iff_dominates (σ := r) (T := marks) (c := codalessReduplicant)
    (d := exactCopy) (i := 1) (j := 2) (by decide) (by decide)
  rw [keepsCodas_iff, optimal_eq_singleton_iff_profile_lt]
  refine ⟨fun hw ↦ ⟨ha.1 (hw.2 _ (by decide) (by decide)) 1 (by decide),
    hb.1 (hw.2 _ (by decide) (by decide))⟩, fun ⟨h01, h12⟩ ↦ ⟨by decide, fun d hd hne ↦ ?_⟩⟩
  simp only [candidates, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl
  · refine ha.2 fun j hj ↦ ?_
    obtain rfl | rfl :=
      (by decide : ∀ j, marks unfaithfulBase j < marks codalessReduplicant j → j = 1 ∨ j = 2) j hj
    exacts [h01, lt_trans h01 h12]
  · exact hb.2 h12
  · exact absurd rfl hne

end Balangao

/-! ### Akan palatalization: underapplication -/

namespace Akan

open _root_.Akan

/-- A coronal consonant. -/
def IsCoronal (s : Segment) : Prop := s .syllabic = false ∧ s .coronal = true

/-- A palatal consonant, [+coronal, −anterior]. -/
def IsPalatal (s : Segment) : Prop := IsCoronal s ∧ s .anterior = false

/-- A plain velar, which PAL requires to palatalize before a front vowel. -/
def IsVelar (s : Segment) : Prop :=
  s .syllabic = false ∧ s .dorsal = true ∧ s .coronal = false

/-- A front vowel. -/
def IsFrontVowel (s : Segment) : Prop := s .syllabic = true ∧ s .front = true

instance : DecidablePred IsCoronal := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsPalatal := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsVelar := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsFrontVowel := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- PAL counts the plain velars that stand before a front vowel. -/
def pal : Constraint (List Segment) :=
  Constraint.ofForbiddenPairs fun c v ↦ IsVelar c ∧ IsFrontVowel v

/-- OCP(+cor) counts the syllables of palatal onset and front vowel that stand before a syllable
of coronal onset which is not itself of palatal onset and front vowel, the clash of syllabic and
segmental coronality. -/
def ocpCoronal : List Segment → ℕ
  | c₁ :: v₁ :: c₂ :: v₂ :: rest =>
    (if IsPalatal c₁ ∧ IsFrontVowel v₁ ∧ IsCoronal c₂ ∧ ¬ (IsPalatal c₂ ∧ IsFrontVowel v₂)
      then 1 else 0) + ocpCoronal (c₂ :: v₂ :: rest)
  | _ => 0

-- (127), (128), and *si–se* of the paragraph before (129)
theorem ocpCoronal_eq :
    ocpCoronal [k, i, t, a] = 0 ∧ ocpCoronal [tcCurl, i, t, a] = 1 ∧
      ocpCoronal [tcCurl, i, tcCurl, e] = 0 ∧ ocpCoronal [k, epsilon, s, smallCapitalI] = 0 ∧
      ocpCoronal [tcCurl, epsilon, s, smallCapitalI] = 1 ∧ ocpCoronal [s, i, s, e] = 0 := by
  decide

/-- The constraints of (131) are OCP(+cor), IDENT-BR(−cor), PAL and IDENT-IO(−cor); the surface
string is the reduplicant followed by the base. An IDENT(−cor) constraint is violated by a
[−coronal] segment whose correspondent is not [−coronal]. -/
def marks (stem : List Segment) (c : Candidate Segment) : Fin 4 → ℕ :=
  ![ocpCoronal (c.reduplicant ++ c.base),
    (c.correspondence stem).maxViolFeature (fun s : Segment ↦ s .coronal = false)
      .base .reduplicant,
    pal (c.reduplicant ++ c.base),
    (c.correspondence stem).maxViolFeature (fun s : Segment ↦ s .coronal = false) .input .base]

/-- (126): a ranking palatalizes when it selects *tɕɛ* over *kɛ* for /kɛ/. -/
def Palatalizes (r : Ranking.Enumeration (Fin 4) 4) : Prop :=
  r.optimal (marks [k, epsilon]) {.ofWord [tcCurl, epsilon], .ofWord [k, epsilon]} =
    {.ofWord [tcCurl, epsilon]}

/-- (128): a ranking blocks palatalization before a coronal when it selects *kɛsɪ* over *tɕɛsɪ*
for /kɛsɪ/. -/
def Blocks (r : Ranking.Enumeration (Fin 4) 4) : Prop :=
  r.optimal (marks [k, epsilon, s, smallCapitalI])
      {.ofWord [k, epsilon, s, smallCapitalI], .ofWord [tcCurl, epsilon, s, smallCapitalI]} =
    {.ofWord [k, epsilon, s, smallCapitalI]}

/-- The stem *ka* 'bite'. -/
def stem : List Segment := [k, a]

/-- (130): the candidates for /RED–ka/. Overapplication is *tɕɪ–tɕa*, palatalized in reduplicant
and base, normal application *tɕɪ–ka*, palatalized before the front vowel only, and
underapplication the unpalatalized *kɪ–ka*. -/
def candidate : Examples.Application → Candidate Segment
  | .over => ⟨[tcCurl, a], [tcCurl, smallCapitalI]⟩
  | .normal => ⟨stem, [tcCurl, smallCapitalI]⟩
  | .under => ⟨stem, [k, smallCapitalI]⟩

/-- The candidates of tableau (131). -/
def candidates : Finset (Candidate Segment) := Finset.univ.image candidate

-- (131)
theorem marks_eq :
    marks stem (candidate .over) = ![1, 0, 0, 1] ∧ marks stem (candidate .normal) = ![0, 1, 0, 0] ∧
      marks stem (candidate .under) = ![0, 0, 1, 0] := by
  decide

section

open Ranking.Enumeration

variable {r : Ranking.Enumeration (Fin 4) 4}

-- (126)
theorem palatalizes_iff : Palatalizes r ↔ r.Dominates 2 3 := by
  rw [Palatalizes, optimal_eq_singleton_iff_pair rfl (by decide),
    profile_lt_iff_dominates (i := 2) (j := 3) (by decide) (by decide)]

/-- An unpalatalized form beats a palatalized one that violates OCP(+cor) iff OCP(+cor) dominates
PAL, given that PAL dominates IDENT-IO(−cor). -/
private theorem profile_lt_iff {C : Type*} {T : Tableau C (Fin 4)} {c d : C}
    (h : r.Dominates 2 3) (hc : T c = ![0, 0, 1, 0]) (hd : T d = ![1, 0, 0, 1]) :
    r.profile T c < r.profile T d ↔ r.Dominates 0 2 := by
  rw [profile_lt_iff_exists_dominates, hc, hd]
  constructor
  · rintro ⟨i, hi, hdi⟩
    have h2 := hdi 2 (by simp)
    fin_cases i
    · exact h2
    · simp at hi
    · simp at hi
    · exact absurd h2 (lt_asymm h)
  · exact fun h02 ↦ ⟨0, by simp, fun j hj ↦ by fin_cases j <;> first | exact h02 | simp at hj⟩

-- (128)
theorem blocks_iff (h : Palatalizes r) : Blocks r ↔ r.Dominates 0 2 := by
  rw [Blocks, optimal_eq_singleton_iff_pair rfl (by decide)]
  exact profile_lt_iff (palatalizes_iff.1 h) (by decide) (by decide)

/-- A ranking that palatalizes leaves the reduplicant of *kɪ–ka* unpalatalized exactly when it
blocks palatalization before a coronal in unreduplicated words and has IDENT-BR(−cor) dominate
PAL. -/
theorem underapplication_iff (h : Palatalizes r) :
    r.optimal (marks stem) candidates = {candidate .under} ↔ Blocks r ∧ r.Dominates 1 2 := by
  have ho := profile_lt_iff (r := r) (T := marks stem) (c := candidate .under)
    (d := candidate .over) (palatalizes_iff.1 h) (by decide) (by decide)
  have hn := profile_lt_iff_dominates (σ := r) (T := marks stem) (c := candidate .under)
    (d := candidate .normal) (i := 1) (j := 2) (by decide) (by decide)
  rw [blocks_iff h, optimal_eq_singleton_iff_profile_lt]
  refine ⟨fun hw ↦ ⟨ho.1 (hw.2 _ (by decide) (by decide)), hn.1 (hw.2 _ (by decide) (by decide))⟩,
    fun ⟨h02, h12⟩ ↦ ⟨by decide, fun d hd hne ↦ ?_⟩⟩
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hd
  cases a
  exacts [ho.2 h02, absurd rfl hne, hn.2 h12]

-- (125) and the candidates of (130)
theorem judgments (h : Palatalizes r) (hb : Blocks r) (h12 : r.Dominates 1 2) :
    ∀ e ∈ Examples.all, e.language = .akan → ∀ a ∈ Examples.application e,
      (candidate a ∈ r.optimal (marks stem) candidates ↔ e.judgment = .acceptable) := by
  rw [(underapplication_iff h).2 ⟨hb, h12⟩]
  decide

end

end Akan

end McCarthyPrince1995
