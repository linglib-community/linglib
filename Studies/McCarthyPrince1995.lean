module

public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.McCarthyPrince1995
public import Linglib.Fragments.Akan.Phonology
public import Linglib.Phonology.OptimalityTheory.Constraint.ForbiddenFactors
public import Linglib.Phonology.OptimalityTheory.Correspondence.Coindexation
public import Linglib.Phonology.OptimalityTheory.Typology

/-!
# McCarthy and Prince (1995): Faithfulness and Reduplicative Identity

In the basic model of [mccarthy-prince-1995] a reduplicated form has an input stem, a base and a
reduplicant. Faithfulness constraints relate the input to the base, identity constraints relate
the base to the reduplicant, and a phonological constraint reads the surface string. Each
language here is a constraint system whose inputs are an unreduplicated word and a reduplicated
one. An output is a base and a reduplicant with the correspondence between them, its marks are
computed from the correspondence between the three strings and from the surface string, and
each result says, of the rankings that pick the attested unreduplicated word, which pick which
reduplicated form.

Javanese deletes intervocalic *h*, as in *ara–e* from /arah–e/. A ranking that does so loses *h*
from both copies of the suffixed reduplication of *bəḍah*, though only one is intervocalic,
exactly when MAX-BR dominates MAX-IO (`Javanese.overapplication_iff`), and never keeps both
(`Javanese.not_picksAt_underapplication`). Balangao keeps the codas of *tagtag*. A ranking that
does so copies its first two syllables without the final coda exactly when NO-CODA dominates
MAX-BR and CONTIG-BR dominates NO-CODA (`Balangao.picksAt_codalessReduplicant_iff`); the second
condition excludes a reduplicant that skips the medial coda too.

Akan palatalizes a velar before a front vowel, as in *tɕɛ*, but not when a coronal begins the
next syllable, as in *kɛsɪ*. A ranking that palatalizes leaves the reduplicant of *kɪ–ka*
unpalatalized exactly when it blocks palatalization in *kɛsɪ* and has IDENT-BR dominate PAL
(`Akan.underapplication_iff`), and under such a ranking the outputs are the forms the paper
judges acceptable (`Akan.judgments`).

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

/-! ### Outputs of the basic model -/

/-- An output form of the basic model: a base, a reduplicant and the correspondence between
them. -/
structure Form (α : Type*) where
  /-- The base, the output of the stem. -/
  base : List α
  /-- The reduplicant, the output of the reduplicative affix. -/
  reduplicant : List α
  /-- The positions of the base and of the reduplicant that correspond. -/
  pairs : List (ℕ × ℕ)
  deriving DecidableEq

namespace Form

variable {α : Type*}

/-- The form whose base and reduplicant correspond position by position. -/
def aligned (base reduplicant : List α) : Form α :=
  ⟨base, reduplicant, Correspondence.diagonalPairs (min base.length reduplicant.length)⟩

/-- An unreduplicated word, a form with no reduplicant. -/
def ofWord (w : List α) : Form α := ⟨w, [], []⟩

/-- The correspondence of a form with the input `stem`: the stem and the base correspond position
by position, the base and the reduplicant as the form says. -/
def correspondence (stem : List α) (c : Form α) :
    Correspondence.Coindexation ReduplicationRole α :=
  .ofPairs (fun | .input => stem | .base => c.base | .reduplicant => c.reduplicant)
    [(.input, .base, Correspondence.diagonalPairs (min stem.length c.base.length)),
      (.base, .reduplicant, c.pairs)]

end Form

section

open Ranking.Enumeration

variable {C ι : Type*} {n : ℕ} {σ : Ranking.Enumeration ι n} {T : Tableau C ι} {c d : C}
  {i i' j : ι}

-- If `i`, `i'` prefer `c`, only `j` prefers `d`, and `j ≫ i'`, then `c` beats `d` iff `i ≫ j`.
private theorem profile_lt_iff_of_dominates (h : σ.Dominates j i')
    (hc : ∀ k, T c k < T d k ↔ k = i ∨ k = i') (hd : ∀ k, T d k < T c k ↔ k = j) :
    σ.profile T c < σ.profile T d ↔ σ.Dominates i j := by
  rw [profile_lt_iff_exists_dominates]
  refine ⟨fun ⟨k, hk, hkj⟩ ↦ ?_, fun hij ↦ ⟨i, (hc i).2 (.inl rfl), fun k hk ↦ (hd k).1 hk ▸ hij⟩⟩
  have hj := hkj j ((hd j).2 rfl)
  obtain rfl | rfl := (hc k).1 hk
  exacts [hj, absurd hj (lt_asymm h)]

end

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

/-- The constraints of (36) and (39). -/
inductive Con where
  /-- MAX-BR: every segment of the base has a correspondent in the reduplicant. -/
  | maxBR
  /-- *VhV: no *h* between vowels. -/
  | noVhV
  /-- MAX-IO: every segment of the input has a correspondent in the output. -/
  | maxIO
  deriving DecidableEq, Fintype, Repr

/-- The inputs. -/
inductive Input where
  /-- /arah–e/ of (36). -/
  | word
  /-- /bəḍah–RED–e/ of (39). -/
  | reduplicated
  deriving DecidableEq, Repr

/-- The stem of an input. -/
def Input.stem : Input → List Seg
  | .word => [.a, .r, .a, .h]
  | .reduplicated => [.b, .schwa, .d, .a, .h]

/-- *ara–e*, with intervocalic *h* lost. -/
def deleted : Form Seg := .ofWord [.a, .r, .a]

/-- *arah–e*, with *h* kept. -/
def retained : Form Seg := .ofWord [.a, .r, .a, .h]

/-- (6): the candidates for /bəḍah–RED–e/. Overapplication is *bəḍa–bəḍa–e*, with *h* lost from
base and reduplicant, underapplication *bəḍah–bəḍah–e*, with *h* kept in both, and normal
application *bəḍah–bəḍa–e*, with *h* lost where it is intervocalic. -/
def candidate : Examples.Application → Form Seg
  | .over => .aligned [.b, .schwa, .d, .a] [.b, .schwa, .d, .a]
  | .under => .aligned Input.reduplicated.stem Input.reduplicated.stem
  | .normal => .aligned Input.reduplicated.stem [.b, .schwa, .d, .a]

/-- The tableaux (36) and (39). The surface string is the base followed by the reduplicant and
the suffix, and MAX-BR assesses only the input with a reduplicative affix. -/
def system : ConstraintSystem Input (Form Seg) Con where
  gen
    | .word => {deleted, retained}
    | .reduplicated => Finset.univ.image candidate
  marks i c
    | .maxBR => match i with
      | .word => 0
      | .reduplicated => (c.correspondence i.stem).maxViol .base .reduplicant
    | .noVhV => intervocalic Seg.IsVowel .h (c.base ++ c.reduplicant ++ [.e])
    | .maxIO => (c.correspondence i.stem).maxViol .input .base

-- (39)
theorem marks_reduplicated :
    system.marks .reduplicated (candidate .over) = (fun | .maxIO => 1 | _ => 0) ∧
      system.marks .reduplicated (candidate .under) = (fun | .noVhV => 1 | _ => 0) ∧
      system.marks .reduplicated (candidate .normal) = (fun | .maxBR => 1 | _ => 0) := by
  decide

section

open Ranking.Enumeration

variable {r : Ranking Con}

-- (36)
theorem picksAt_deleted_iff : system.PicksAt r .word deleted ↔ r.Dominates .noVhV .maxIO :=
  (optimal_eq_singleton_iff_pair (c := deleted) (d := retained) rfl (by decide)).trans
    (profile_lt_iff_dominates (by decide) (by decide))

/-- A ranking that deletes intervocalic *h* loses it from both copies of *bəḍah* exactly when
MAX-BR dominates MAX-IO. -/
theorem overapplication_iff (h : system.PicksAt r .word deleted) :
    system.PicksAt r .reduplicated (candidate .over) ↔ r.Dominates .maxBR .maxIO := by
  have hu := profile_lt_iff_dominates (σ := r) (T := system.marks .reduplicated)
    (c := candidate .over) (d := candidate .under) (i := .noVhV) (j := .maxIO)
    (by decide) (by decide)
  have hn := profile_lt_iff_dominates (σ := r) (T := system.marks .reduplicated)
    (c := candidate .over) (d := candidate .normal) (i := .maxBR) (j := .maxIO)
    (by decide) (by decide)
  rw [ConstraintSystem.picksAt_iff]
  refine ⟨fun hw ↦ hn.1 (hw.2 _ (by decide) (by decide)), fun h02 ↦ ⟨by decide, fun d hd hne ↦ ?_⟩⟩
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hd
  cases a
  exacts [absurd rfl hne, hu.2 (picksAt_deleted_iff.1 h), hn.2 h02]

-- the paragraph after (39)
theorem normalApplication_iff (h : system.PicksAt r .word deleted) :
    system.PicksAt r .reduplicated (candidate .normal) ↔ r.Dominates .maxIO .maxBR := by
  have ho := profile_lt_iff_dominates (σ := r) (T := system.marks .reduplicated)
    (c := candidate .normal) (d := candidate .over) (i := .maxIO) (j := .maxBR)
    (by decide) (by decide)
  have hu := profile_lt_iff_dominates (σ := r) (T := system.marks .reduplicated)
    (c := candidate .normal) (d := candidate .under) (i := .noVhV) (j := .maxBR)
    (by decide) (by decide)
  rw [ConstraintSystem.picksAt_iff]
  refine ⟨fun hw ↦ ho.1 (hw.2 _ (by decide) (by decide)), fun h20 ↦ ⟨by decide, fun d hd hne ↦ ?_⟩⟩
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hd
  cases a
  exacts [ho.2 h20, hu.2 (lt_trans (picksAt_deleted_iff.1 h) h20), absurd rfl hne]

/-- Underapplication is out of reach: no ranking that deletes intervocalic *h* keeps both *h*s
of the reduplicated form. -/
theorem not_picksAt_underapplication (h : system.PicksAt r .word deleted) :
    candidate .under ∉ system.language r .reduplicated :=
  notMem_optimal_of_forall_dominates (d := candidate .over) (i := .noVhV) (by decide) (by decide)
    fun k hk ↦ (by decide : ∀ k, system.marks .reduplicated (candidate .under) k <
      system.marks .reduplicated (candidate .over) k → k = .maxIO) k hk ▸ picksAt_deleted_iff.1 h

-- (6)
theorem judgments (h : system.PicksAt r .word deleted) (h02 : r.Dominates .maxBR .maxIO) :
    ∀ e ∈ Examples.all, e.language = .javanese → ∀ a ∈ Examples.application e,
      (candidate a ∈ system.language r .reduplicated ↔ e.judgment = .acceptable) := by
  rw [show system.language r .reduplicated = {candidate .over} from (overapplication_iff h).2 h02]
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

/-- The constraints of (16) and (106), with the CONTIG-BR of the discussion of (15). -/
inductive Con where
  /-- MAX-IO: every segment of the input has a correspondent in the output. -/
  | maxIO
  /-- NO-CODA: syllables have no coda. -/
  | noCoda
  /-- MAX-BR: every segment of the base has a correspondent in the reduplicant. -/
  | maxBR
  /-- CONTIG-BR: the segments of the base with a correspondent in the reduplicant are
  contiguous. -/
  | contigBR
  deriving DecidableEq, Fintype, Repr

/-- The inputs. -/
inductive Input where
  /-- /tagtag/ of (16). -/
  | word
  /-- /RED–tagtag/ of (106). -/
  | reduplicated
  deriving DecidableEq, Repr

/-- The stem *tagtag*. -/
def stem : List Seg := [.t, .a, .g, .t, .a, .g]

/-- *tagtag*, the faithful word. -/
def faithful : Form Seg := .ofWord stem

/-- *tagta*, the word without its final coda. -/
def codaless : Form Seg := .ofWord [.t, .a, .g, .t, .a]

/-- *tagta–tagta*, with the final coda lost from the base too. -/
def unfaithfulBase : Form Seg := .aligned [.t, .a, .g, .t, .a] [.t, .a, .g, .t, .a]

/-- *tagtag–tagtag*, an exact copy. -/
def exactCopy : Form Seg := .aligned stem stem

/-- *tagta–tagtag*, with a reduplicant that lacks the final coda. -/
def codalessReduplicant : Form Seg := .aligned stem [.t, .a, .g, .t, .a]

/-- *tata–tagtag*, with a reduplicant that skips the medial coda of the base as well. -/
def skippingReduplicant : Form Seg := ⟨stem, [.t, .a, .t, .a], [(0, 0), (1, 1), (3, 2), (4, 3)]⟩

/-- The tableaux (16) and (106), with the candidate that CONTIG-BR excludes. The surface string
is the reduplicant followed by the base, and the B-R constraints assess only the input with a
reduplicative affix. -/
def system : ConstraintSystem Input (Form Seg) Con where
  gen
    | .word => {faithful, codaless}
    | .reduplicated => {unfaithfulBase, exactCopy, codalessReduplicant, skippingReduplicant}
  marks i c
    | .maxIO => (c.correspondence stem).maxViol .input .base
    | .noCoda => codas Seg.IsVowel (c.reduplicant ++ c.base)
    | .maxBR => match i with
      | .word => 0
      | .reduplicated => (c.correspondence stem).maxViol .base .reduplicant
    | .contigBR => match i with
      | .word => 0
      | .reduplicated => (c.correspondence stem).contigIViol .base .reduplicant

-- (106), and the reduplicant *tata* of the discussion of (15)
theorem marks_reduplicated :
    system.marks .reduplicated unfaithfulBase = (fun | .maxIO => 1 | .noCoda => 2 | _ => 0) ∧
      system.marks .reduplicated exactCopy = (fun | .noCoda => 4 | _ => 0) ∧
      system.marks .reduplicated codalessReduplicant =
        (fun | .noCoda => 3 | .maxBR => 1 | _ => 0) ∧
      system.marks .reduplicated skippingReduplicant =
        (fun | .maxIO => 0 | .noCoda => 2 | .maxBR => 2 | .contigBR => 1) := by
  decide

section

open Ranking.Enumeration

variable {r : Ranking Con}

-- (16)
theorem picksAt_faithful_iff : system.PicksAt r .word faithful ↔ r.Dominates .maxIO .noCoda :=
  (optimal_eq_singleton_iff_pair (c := faithful) (d := codaless) rfl (by decide)).trans
    (profile_lt_iff_dominates (by decide) (by decide))

/-- The coda-sparing reduplicant wins exactly when a ranking keeps codas in unreduplicated words,
has NO-CODA dominate MAX-BR, the ranking for emergence of the unmarked, and has CONTIG-BR
dominate NO-CODA. -/
theorem picksAt_codalessReduplicant_iff :
    system.PicksAt r .reduplicated codalessReduplicant ↔
      system.PicksAt r .word faithful ∧ r.Dominates .noCoda .maxBR ∧
        r.Dominates .contigBR .noCoda := by
  have ha := profile_lt_iff_forall_dominates (σ := r) (T := system.marks .reduplicated)
    (c := codalessReduplicant) (d := unfaithfulBase) (i := .maxIO) (by decide)
  have hb := profile_lt_iff_dominates (σ := r) (T := system.marks .reduplicated)
    (c := codalessReduplicant) (d := exactCopy) (i := .noCoda) (j := .maxBR)
    (by decide) (by decide)
  have hs (h : r.Dominates .noCoda .maxBR) := profile_lt_iff_of_dominates (σ := r)
    (T := system.marks .reduplicated) (c := codalessReduplicant) (d := skippingReduplicant)
    (i := .contigBR) (i' := .maxBR) (j := .noCoda) h (by decide) (by decide)
  rw [picksAt_faithful_iff, ConstraintSystem.picksAt_iff]
  refine ⟨fun hw ↦ ?_, fun ⟨h01, h12, h31⟩ ↦ ⟨by decide, fun d hd hne ↦ ?_⟩⟩
  · have h12 := hb.1 (hw.2 _ (by decide) (by decide))
    exact ⟨ha.1 (hw.2 _ (by decide) (by decide)) .noCoda (by decide), h12,
      (hs h12).1 (hw.2 _ (by decide) (by decide))⟩
  · simp only [system, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · refine ha.2 fun j hj ↦ ?_
      obtain rfl | rfl := (by decide : ∀ j, system.marks .reduplicated unfaithfulBase j <
        system.marks .reduplicated codalessReduplicant j → j = .noCoda ∨ j = .maxBR) j hj
      exacts [h01, lt_trans h01 h12]
    · exact hb.2 h12
    · exact absurd rfl hne
    · exact (hs h12).2 h31

end

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

/-- The constraints of (131). An IDENT(−cor) constraint is violated by a [−coronal] segment whose
correspondent is not [−coronal]. -/
inductive Con where
  /-- OCP(+cor). -/
  | ocp
  /-- IDENT-BR(−cor). -/
  | identBR
  /-- PAL. -/
  | pal
  /-- IDENT-IO(−cor). -/
  | identIO
  deriving DecidableEq, Fintype, Repr

/-- The stem of an input. -/
def stem : Examples.Input → List Segment
  | .divide => [k, epsilon]
  | .big => [k, epsilon, s, smallCapitalI]
  | .polish => [k, i, t, a]
  | .bite => [k, a]

/-- The word of an input with its initial velar as given. -/
def word (i : Examples.Input) : Examples.Velar → Form Segment
  | .plain => .ofWord (stem i)
  | .palatalized => .ofWord (tcCurl :: (stem i).tail)

/-- (130): the candidates for /RED–ka/. Overapplication is *tɕɪ–tɕa*, palatalized in reduplicant
and base, normal application *tɕɪ–ka*, palatalized before the front vowel only, and
underapplication the unpalatalized *kɪ–ka*. -/
def candidate : Examples.Application → Form Segment
  | .over => .aligned [tcCurl, a] [tcCurl, smallCapitalI]
  | .normal => .aligned [k, a] [tcCurl, smallCapitalI]
  | .under => .aligned [k, a] [k, smallCapitalI]

/-- The tableaux (126), (128) and (131), and that of *kita*. The surface string is the
reduplicant followed by the base. -/
def system : ConstraintSystem Examples.Input (Form Segment) Con where
  gen
    | .bite => Finset.univ.image candidate
    | i => Finset.univ.image (word i)
  marks i c
    | .ocp => ocpCoronal (c.reduplicant ++ c.base)
    | .identBR => (c.correspondence (stem i)).maxViolFeature
        (fun s : Segment ↦ s .coronal = false) .base .reduplicant
    | .pal => pal (c.reduplicant ++ c.base)
    | .identIO => (c.correspondence (stem i)).maxViolFeature
        (fun s : Segment ↦ s .coronal = false) .input .base

/-- The attested output of each input: *tɕɛ*, *kɛsɪ*, *kita* and *kɪ–ka*. -/
def attested : Examples.Input → Form Segment
  | .divide => word .divide .palatalized
  | .bite => candidate .under
  | i => word i .plain

/-- The form a row records: its candidate for /RED–ka/, or its word. -/
def form (e : Datum) : Option (Form Segment) :=
  ((Examples.application e).map candidate).orElse fun _ ↦
    (Examples.input e).bind fun i ↦ (Examples.velar e).map (word i)

-- (131)
theorem marks_bite :
    system.marks .bite (candidate .over) = (fun | .ocp => 1 | .identIO => 1 | _ => 0) ∧
      system.marks .bite (candidate .normal) = (fun | .identBR => 1 | _ => 0) ∧
      system.marks .bite (candidate .under) = (fun | .pal => 1 | _ => 0) := by
  decide

section

open Ranking.Enumeration

variable {r : Ranking Con}

private theorem picksAt_word_iff {i : Examples.Input} {v v' : Examples.Velar} (hi : i ≠ .bite)
    (hv : v ≠ v') :
    system.PicksAt r i (word i v) ↔ r.profile (system.marks i) (word i v) <
      r.profile (system.marks i) (word i v') := by
  refine (optimal_eq_singleton_iff_pair (c := word i v) (d := word i v') ?_ ?_)
  · cases i <;> cases v <;> cases v' <;> first | exact absurd rfl hi | exact absurd rfl hv | decide
  · cases i <;> cases v <;> cases v' <;> first | exact absurd rfl hi | exact absurd rfl hv | decide

-- (126)
theorem picksAt_divide_iff :
    system.PicksAt r .divide (attested .divide) ↔ r.Dominates .pal .identIO :=
  (picksAt_word_iff (i := .divide) (v := .palatalized) (v' := .plain) (by decide) (by decide)).trans
    (profile_lt_iff_dominates (i := Con.pal) (j := Con.identIO) (by decide) (by decide))

-- (128)
theorem picksAt_big_iff (h : system.PicksAt r .divide (attested .divide)) :
    system.PicksAt r .big (attested .big) ↔ r.Dominates .ocp .pal :=
  (picksAt_word_iff (i := .big) (v := .plain) (v' := .palatalized) (by decide) (by decide)).trans
    (profile_lt_iff_of_dominates (i := Con.ocp) (i' := Con.identIO) (j := Con.pal)
      (picksAt_divide_iff.1 h) (by decide) (by decide))

-- (127a)
theorem picksAt_polish_iff (h : system.PicksAt r .divide (attested .divide)) :
    system.PicksAt r .polish (attested .polish) ↔ r.Dominates .ocp .pal :=
  (picksAt_word_iff (i := .polish) (v := .plain) (v' := .palatalized) (by decide)
    (by decide)).trans
    (profile_lt_iff_of_dominates (i := Con.ocp) (i' := Con.identIO) (j := Con.pal)
      (picksAt_divide_iff.1 h) (by decide) (by decide))

/-- A ranking that palatalizes leaves the reduplicant of *kɪ–ka* unpalatalized exactly when it
blocks palatalization before a coronal in unreduplicated words and has IDENT-BR(−cor) dominate
PAL. -/
theorem underapplication_iff (h : system.PicksAt r .divide (attested .divide)) :
    system.PicksAt r .bite (attested .bite) ↔
      system.PicksAt r .big (attested .big) ∧ r.Dominates .identBR .pal := by
  have ho := profile_lt_iff_of_dominates (σ := r) (T := system.marks .bite)
    (c := candidate .under) (d := candidate .over) (i := .ocp) (i' := .identIO) (j := .pal)
    (picksAt_divide_iff.1 h) (by decide) (by decide)
  have hn := profile_lt_iff_dominates (σ := r) (T := system.marks .bite)
    (c := candidate .under) (d := candidate .normal) (i := .identBR) (j := .pal)
    (by decide) (by decide)
  rw [picksAt_big_iff h, ConstraintSystem.picksAt_iff]
  refine ⟨fun hw ↦ ⟨ho.1 (hw.2 _ (by decide) (by decide)), hn.1 (hw.2 _ (by decide) (by decide))⟩,
    fun ⟨h02, h12⟩ ↦ ⟨by decide, fun d hd hne ↦ ?_⟩⟩
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hd
  cases a
  exacts [ho.2 h02, absurd rfl hne, hn.2 h12]

/-- Under a ranking that palatalizes, blocks palatalization before a coronal and has
IDENT-BR(−cor) dominate PAL, a form the paper judges is an output iff it is judged acceptable. -/
theorem judgments (h : system.PicksAt r .divide (attested .divide))
    (hb : system.PicksAt r .big (attested .big)) (h12 : r.Dominates .identBR .pal) :
    ∀ e ∈ Examples.all, ∀ i ∈ Examples.input e, ∀ f ∈ form e,
      (f ∈ system.language r i ↔ e.judgment = .acceptable) := by
  have hl : ∀ i, system.language r i = {attested i}
    | .divide => h
    | .big => hb
    | .polish => (picksAt_polish_iff h).2 ((picksAt_big_iff h).1 hb)
    | .bite => (underapplication_iff h).2 ⟨hb, h12⟩
  intro e he i hi f hf
  rw [hl i]
  exact (by decide : ∀ e ∈ Examples.all, ∀ i ∈ Examples.input e, ∀ f ∈ form e,
    (f ∈ ({attested i} : Finset _) ↔ e.judgment = .acceptable)) e he i hi f hf

end

end Akan

end McCarthyPrince1995
