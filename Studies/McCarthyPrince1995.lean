module

public import Linglib.Fragments.Akan.Phonology
public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Mathlib.Tactic.FinCases

/-!
# McCarthy and Prince (1995): Faithfulness and Reduplicative Identity

This file formalizes three analyses from McCarthy and Prince's correspondence theory of
reduplication. In the basic model a reduplicated form has an input stem, a base and a
reduplicant, with faithfulness between input and base and identity between base and
reduplicant, and a phonological constraint interacts with both. Javanese deletes
intervocalic *h*, and in a suffixed reduplication the *h* is lost from both copies although
only one is intervocalic, which is overapplication (§3.4). Balangao copies the first two
syllables of the base without the final coda although the language allows codas, which is
emergence of the unmarked (§4.2). Akan palatalizes a velar before a front vowel, but not in
the reduplicant of *kɪ–ka*, which is underapplication (§5.1).

A candidate here is a correspondence between the input stem, the base and the reduplicant,
and every constraint is computed from it: MAX and IDENT from the correspondence, and the
phonological constraints from the surface string. The rankings are not fixed in advance.
Each result says which rankings of the paper's constraints select which candidate.

## Main definitions

* `Javanese.Candidate`, `Balangao.Candidate`, `Akan.Candidate`: the candidates of tableaux
  (39), (106) and (131), each with its `correspondence` and `surface`.
* `Javanese.con`, `Balangao.con`, `Akan.con`: the constraints of those tableaux.

## Main results

* `Javanese.optimal_eq`: each candidate of (39) violates one constraint, and the winner is the
  candidate whose constraint is ranked last.
* `Javanese.overapplication`, `Javanese.normalApplication`,
  `Javanese.underapplication_notMem`: with *VhV above MAX-IO, MAX-BR above MAX-IO gives
  overapplication and the reverse gives normal application, and the underapplying candidate
  wins under no such ranking.
* `Balangao.optimal_iff`: the coda-sparing reduplicant wins exactly under MAX-IO ≫ NO-CODA ≫
  MAX-BR.
* `Akan.optimal_iff`: with PAL above IDENT-IO(−cor), the unpalatalized *kɪ–ka* wins exactly
  when OCP(+cor) and IDENT-BR(−cor) both dominate PAL.

## Implementation notes

Javanese is analysed with suffixing reduplication, the paper's tableau (39). Its prefixing
alternative (38), where DEP-BR does the work of MAX-BR, is not formalized. A coda is counted
as a consonant that no vowel follows, which suffices for the CV(C) syllables of the Balangao
forms. The paper measures OCP(+cor) by featural duplication in dissimilar constituents and
prints three marks for the overapplying candidate of (131) without spelling the count out.
Here the constraint is violated once by a syllable with a palatal onset and a front vowel
before a syllable with a coronal onset and a vowel that is not front, which agrees with the
paper's verdicts on *kita*, *tɕita*, *dʑidʑe* and the three candidates. The Akan segments are
those of the Akan fragment.

## References

* [mccarthy-prince-1995]
-/

@[expose] public section

namespace McCarthyPrince1995

open Phonology OptimalityTheory

/-! ### Phonological constraints on a surface string -/

section Surface

variable {σ : Type*} (IsVowel : σ → Prop) [DecidablePred IsVowel]

/-- The number of codas of a string, a coda being a consonant that no vowel follows. -/
def codas : List σ → ℕ
  | [] => 0
  | [x] => if IsVowel x then 0 else 1
  | x :: y :: rest =>
    (if ¬ IsVowel x ∧ ¬ IsVowel y then 1 else 0) + codas (y :: rest)

/-- The number of occurrences of `x` between two vowels. -/
def intervocalic [DecidableEq σ] (x : σ) : List σ → ℕ
  | a :: b :: c :: rest =>
    (if IsVowel a ∧ b = x ∧ IsVowel c then 1 else 0) + intervocalic x (b :: c :: rest)
  | _ => 0

end Surface

/-! ### Javanese *h*-deletion: overapplication -/

namespace Javanese

/-- The segments of *bədah* 'broken' and the demonstrative suffix *-e*. -/
inductive Seg where
  | b | schwa | d | a | h | e
  deriving DecidableEq, Repr

/-- The vowels. -/
def Seg.IsVowel : Seg → Prop
  | .schwa | .a | .e => True
  | _ => False

instance : DecidablePred Seg.IsVowel := fun s ↦ by cases s <;> unfold Seg.IsVowel <;> infer_instance

/-- The stem *bədah*. -/
def stem : List Seg := [.b, .schwa, .d, .a, .h]

/-- The stem without its *h*. -/
def stemNoH : List Seg := [.b, .schwa, .d, .a]

/-- The candidates of tableau (39) for /bədah–RED–e/. -/
inductive Candidate where
  /-- *bəda–bəda–e*, with *h* lost from base and reduplicant. -/
  | overapplication
  /-- *bədah–bədah–e*, with *h* kept in both. -/
  | underapplication
  /-- *bədah–bəda–e*, with *h* lost where it is intervocalic. -/
  | normalApplication
  deriving DecidableEq, Fintype, Repr

namespace Candidate

/-- The base of a candidate. -/
def base : Candidate → List Seg
  | overapplication => stemNoH
  | underapplication | normalApplication => stem

/-- The reduplicant of a candidate. -/
def reduplicant : Candidate → List Seg
  | underapplication => stem
  | overapplication | normalApplication => stemNoH

/-- The correspondence of a candidate between the stem, its base and its reduplicant. -/
def correspondence (c : Candidate) : Correspondence ReduplicationRole Seg :=
  .reduplication stem c.base c.reduplicant

/-- The surface string, the base followed by the reduplicant and the suffix. -/
def surface (c : Candidate) : List Seg := c.base ++ c.reduplicant ++ [.e]

end Candidate

/-- The constraints of (39) are MAX-BR, *VhV and MAX-IO. -/
def con : ConstraintSet Candidate (Fin 3) :=
  ![fun c ↦ c.correspondence.maxViol .base .reduplicant,
    fun c ↦ intervocalic Seg.IsVowel .h c.surface,
    fun c ↦ c.correspondence.maxViol .input .base]

/-- The constraint a candidate violates. -/
def Candidate.violated : Candidate → Fin 3
  | .normalApplication => 0
  | .underapplication => 1
  | .overapplication => 2

/-- The candidate that violates a given constraint. -/
def violator : Fin 3 → Candidate
  | 0 => .normalApplication
  | 1 => .underapplication
  | 2 => .overapplication

@[simp] theorem violated_violator : ∀ i, (violator i).violated = i := by decide

theorem violated_injective : Function.Injective Candidate.violated := by decide

/-- The cells of tableau (39), in which each candidate violates one constraint, once. -/
theorem con_apply : ∀ (i : Fin 3) (c : Candidate), con i c = if i = c.violated then 1 else 0 := by
  decide

/-- Tableau (39) under a ranking of its constraints. -/
def tableau (r : Ranking (Fin 3) 3) : Tableau Candidate 3 :=
  .ofRanking con r {.overapplication, .underapplication, .normalApplication}

/-- The winner of (39) is the candidate whose one violated constraint is ranked last. -/
theorem optimal_eq (r : Ranking (Fin 3) 3) : (tableau r).optimal = {violator (r 2)} := by
  refine Tableau.ofRanking_optimal_eq_singleton_iff.2
    ⟨by cases violator (r 2) <;> simp, fun d _ hne ↦ ?_⟩
  have hd : d.violated ≠ r 2 := fun h ↦
    hne (violated_injective (h.trans (violated_violator _).symm))
  refine ⟨d.violated, by simp [con_apply, hd], fun j hj ↦ ?_⟩
  have hj' : j = r 2 := by
    by_contra hjne
    simp [con_apply, hjne] at hj
  subst hj'
  have hne2 : r.symm d.violated ≠ 2 := fun h ↦ hd (by rw [← h, Equiv.apply_symm_apply])
  show r.symm d.violated < r.symm (r 2)
  rw [Equiv.symm_apply_apply]
  omega

private theorem apply_two_eq {r : Ranking (Fin 3) 3} {i j k : Fin 3} (hij : i ≠ j)
    (hi : r.Dominates i k) (hj : r.Dominates j k) : r 2 = k := by
  have hne : r.symm i ≠ r.symm j := fun h ↦ hij (r.symm.injective h)
  have : r.symm k = 2 := by
    unfold Ranking.Dominates at hi hj
    omega
  rw [← this, Equiv.apply_symm_apply]

theorem overapplication {r : Ranking (Fin 3) 3} (h₁ : r.Dominates 0 2) (h₂ : r.Dominates 1 2) :
    (tableau r).optimal = {.overapplication} := by
  rw [optimal_eq, apply_two_eq (by decide) h₁ h₂]; rfl

theorem normalApplication {r : Ranking (Fin 3) 3} (h₁ : r.Dominates 1 2) (h₂ : r.Dominates 2 0) :
    (tableau r).optimal = {.normalApplication} := by
  rw [optimal_eq, apply_two_eq (by decide) (lt_trans h₁ h₂) h₂]; rfl

theorem underapplication_notMem {r : Ranking (Fin 3) 3} (h : r.Dominates 1 2) :
    .underapplication ∉ (tableau r).optimal := by
  rw [optimal_eq, Finset.mem_singleton]
  intro he
  have h2 : r 2 = 1 := by
    have := congrArg Candidate.violated he
    rw [violated_violator] at this
    exact this.symm
  have : r.symm 1 = 2 := by rw [← h2, Equiv.symm_apply_apply]
  unfold Ranking.Dominates at h
  omega

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

/-- The stem without its final coda. -/
def stemNoCoda : List Seg := [.t, .a, .g, .t, .a]

/-- The candidates of tableau (106) for /RED–tagtag/. -/
inductive Candidate where
  /-- *tagta–tagta*, with the final coda lost from the base too. -/
  | unfaithfulBase
  /-- *tagtag–tagtag*, an exact copy. -/
  | exactCopy
  /-- *tagta–tagtag*, with a reduplicant that lacks the final coda. -/
  | codalessReduplicant
  deriving DecidableEq, Fintype, Repr

namespace Candidate

/-- The base of a candidate. -/
def base : Candidate → List Seg
  | unfaithfulBase => stemNoCoda
  | exactCopy | codalessReduplicant => stem

/-- The reduplicant of a candidate. -/
def reduplicant : Candidate → List Seg
  | exactCopy => stem
  | unfaithfulBase | codalessReduplicant => stemNoCoda

/-- The correspondence of a candidate between the stem, its base and its reduplicant. -/
def correspondence (c : Candidate) : Correspondence ReduplicationRole Seg :=
  .reduplication stem c.base c.reduplicant

/-- The surface string, the reduplicant followed by the base. -/
def surface (c : Candidate) : List Seg := c.reduplicant ++ c.base

end Candidate

/-- The constraints of (106) are MAX-IO, NO-CODA and MAX-BR. -/
def con : ConstraintSet Candidate (Fin 3) :=
  ![fun c ↦ c.correspondence.maxViol .input .base,
    fun c ↦ codas Seg.IsVowel c.surface,
    fun c ↦ c.correspondence.maxViol .base .reduplicant]

/-- The cells of tableau (106). -/
theorem con_apply :
    (con · .unfaithfulBase) = ![1, 2, 0] ∧ (con · .exactCopy) = ![0, 4, 0] ∧
      (con · .codalessReduplicant) = ![0, 3, 1] := by
  decide

/-- Tableau (106) under a ranking of its constraints. -/
def tableau (r : Ranking (Fin 3) 3) : Tableau Candidate 3 :=
  .ofRanking con r {.unfaithfulBase, .exactCopy, .codalessReduplicant}

theorem optimal_iff (r : Ranking (Fin 3) 3) :
    (tableau r).optimal = {.codalessReduplicant} ↔ r.Dominates 0 1 ∧ r.Dominates 1 2 := by
  obtain ⟨ha, hb, hc⟩ := con_apply
  have va (i) : con i .unfaithfulBase = ![1, 2, 0] i := congrFun ha i
  have vb (i) : con i .exactCopy = ![0, 4, 0] i := congrFun hb i
  have vc (i) : con i .codalessReduplicant = ![0, 3, 1] i := congrFun hc i
  rw [tableau, Tableau.ofRanking_optimal_eq_singleton_iff, and_iff_right (by simp)]
  constructor
  · intro h
    obtain ⟨i, hi, hdi⟩ := h .unfaithfulBase (by simp) (by decide)
    obtain ⟨j, hj, hdj⟩ := h .exactCopy (by simp) (by decide)
    have i0 : i = 0 := by fin_cases i <;> simp [va, vc] at hi ⊢
    have j1 : j = 1 := by fin_cases j <;> simp [vb, vc] at hj ⊢
    subst i0 j1
    exact ⟨hdi 1 (by simp [va, vc]), hdj 2 (by simp [vb, vc])⟩
  · rintro ⟨h01, h12⟩ d _ hd
    cases d with
    | codalessReduplicant => exact absurd rfl hd
    | unfaithfulBase =>
      refine ⟨0, by simp [va, vc], fun j hj ↦ ?_⟩
      fin_cases j
      · simp [va, vc] at hj
      · exact h01
      · exact lt_trans h01 h12
    | exactCopy =>
      refine ⟨1, by simp [vb, vc], fun j hj ↦ ?_⟩
      fin_cases j
      · simp [vb, vc] at hj
      · simp [vb, vc] at hj
      · exact h12

end Balangao

/-! ### Akan palatalization: underapplication -/

namespace Akan

open _root_.Akan Data.PHOIBLE

/-- A coronal consonant. -/
def IsCoronal (s : Segment) : Prop := s.HasValue .syllabic false ∧ s.HasValue .coronal true

/-- A plain velar, which PAL requires to palatalize before a front vowel. -/
def IsVelar (s : Segment) : Prop :=
  s.HasValue .syllabic false ∧ s.HasValue .dorsal true ∧ s.HasValue .coronal false

/-- A front vowel. -/
def IsFrontVowel (s : Segment) : Prop := s.HasValue .syllabic true ∧ s.HasValue .front true

instance : DecidablePred IsCoronal := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsVelar := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsFrontVowel := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- PAL counts the plain velars that stand before a front vowel. -/
def pal : List Segment → ℕ
  | c :: v :: rest => (if IsVelar c ∧ IsFrontVowel v then 1 else 0) + pal (v :: rest)
  | _ => 0

/-- OCP(+cor) counts the syllables of palatal onset and front vowel that stand before a
syllable of coronal onset and a vowel that is not front, the clash of syllabic and segmental
palatality. -/
def ocpCoronal : List Segment → ℕ
  | c₁ :: v₁ :: c₂ :: v₂ :: rest =>
    (if IsCoronal c₁ ∧ IsFrontVowel v₁ ∧ IsCoronal c₂ ∧ ¬ IsFrontVowel v₂ then 1 else 0) +
      ocpCoronal (c₂ :: v₂ :: rest)
  | _ => 0

/-- By the paper's verdicts on OCP(+cor) in (127), *kita* obeys it and *tɕita* violates it,
while a word whose two syllables are both palatal obeys it. -/
theorem ocpCoronal_kita :
    ocpCoronal [k, i, FeatureMatrix.«t».toSegment, a] = 0 ∧
      ocpCoronal [tcCurl, i, FeatureMatrix.«t».toSegment, a] = 1 ∧
      ocpCoronal [tcCurl, i, tcCurl, e] = 0 := by
  decide

/-- The stem *ka* 'bite'. -/
def stem : List Segment := [k, a]

/-- The candidates of tableau (131) for /RED–ka/. -/
inductive Candidate where
  /-- *tɕɪ–tɕa*, palatalized in reduplicant and base. -/
  | overapplication
  /-- *tɕɪ–ka*, palatalized before the front vowel only. -/
  | normalApplication
  /-- *kɪ–ka*, not palatalized. -/
  | underapplication
  deriving DecidableEq, Fintype, Repr

namespace Candidate

/-- The base of a candidate. -/
def base : Candidate → List Segment
  | overapplication => [tcCurl, a]
  | normalApplication | underapplication => stem

/-- The reduplicant of a candidate, a consonant and a high vowel. -/
def reduplicant : Candidate → List Segment
  | underapplication => [k, smallCapitalI]
  | overapplication | normalApplication => [tcCurl, smallCapitalI]

/-- The correspondence of a candidate between the stem, its base and its reduplicant. -/
def correspondence (c : Candidate) : Correspondence ReduplicationRole Segment :=
  .reduplication stem c.base c.reduplicant

/-- The surface string, the reduplicant followed by the base. -/
def surface (c : Candidate) : List Segment := c.reduplicant ++ c.base

end Candidate

/-- The constraints of (131) are OCP(+cor), IDENT-BR(−cor), PAL and IDENT-IO(−cor). An
IDENT(−cor) constraint is violated by a [−coronal] segment whose correspondent is not [−coronal]. -/
def con : ConstraintSet Candidate (Fin 4) :=
  ![fun c ↦ ocpCoronal c.surface,
    fun c ↦ c.correspondence.maxViolFeature (·.HasValue .coronal false) .base .reduplicant,
    fun c ↦ pal c.surface,
    fun c ↦ c.correspondence.maxViolFeature (·.HasValue .coronal false) .input .base]

/-- The cells of tableau (131), with one mark where the paper prints three for OCP(+cor). -/
theorem con_apply :
    (con · .overapplication) = ![1, 0, 0, 1] ∧ (con · .normalApplication) = ![0, 1, 0, 0] ∧
      (con · .underapplication) = ![0, 0, 1, 0] := by
  decide

/-- Tableau (131) under a ranking of its constraints. -/
def tableau (r : Ranking (Fin 4) 4) : Tableau Candidate 4 :=
  .ofRanking con r {.overapplication, .normalApplication, .underapplication}

theorem optimal_iff {r : Ranking (Fin 4) 4} (h : r.Dominates 2 3) :
    (tableau r).optimal = {.underapplication} ↔ r.Dominates 0 2 ∧ r.Dominates 1 2 := by
  obtain ⟨ha, hb, hc⟩ := con_apply
  have va (i) : con i .overapplication = ![1, 0, 0, 1] i := congrFun ha i
  have vb (i) : con i .normalApplication = ![0, 1, 0, 0] i := congrFun hb i
  have vc (i) : con i .underapplication = ![0, 0, 1, 0] i := congrFun hc i
  rw [tableau, Tableau.ofRanking_optimal_eq_singleton_iff, and_iff_right (by simp)]
  constructor
  · intro hw
    obtain ⟨i, hi, hdi⟩ := hw .overapplication (by simp) (by decide)
    obtain ⟨j, hj, hdj⟩ := hw .normalApplication (by simp) (by decide)
    have h2i := hdi 2 (by simp [va, vc])
    have j1 : j = 1 := by fin_cases j <;> simp [vb, vc] at hj ⊢
    subst j1
    refine ⟨?_, hdj 2 (by simp [vb, vc])⟩
    fin_cases i
    · exact h2i
    · simp [va, vc] at hi
    · simp [va, vc] at hi
    · exact absurd h2i (lt_asymm h)
  · rintro ⟨h02, h12⟩ d _ hd
    cases d with
    | underapplication => exact absurd rfl hd
    | overapplication =>
      refine ⟨0, by simp [va, vc], fun j hj ↦ ?_⟩
      fin_cases j <;> first | exact h02 | simp [va, vc] at hj
    | normalApplication =>
      refine ⟨1, by simp [vb, vc], fun j hj ↦ ?_⟩
      fin_cases j <;> first | exact h12 | simp [vb, vc] at hj

end Akan

end McCarthyPrince1995
