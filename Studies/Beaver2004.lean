module

public import Linglib.Discourse.Centering.Basic
public import Linglib.Discourse.Centering.GrammaticalRole
public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Data.Examples.Beaver2004
import all Mathlib.Data.List.Sort  -- for unfolding `List.insertionSort`

/-!
# Beaver (2004): The Optimization of Discourse Anaphora

Centering's BFP algorithm ([brennan-friedman-pollard-1987]) is restated as six
ranked OT constraints, COT (4): AGREE > DISJOINT > PRO-TOP > FAM-DEF >
COHERE > ALIGN. Three of the six are Centering primitives this library already
carries — PRO-TOP is Rule 1 without its if-clause (`CbPronominalized`), COHERE
and ALIGN are the transition-classification tests (`cb`, `cp`) — so on those
the correspondence with BFP holds by construction. The paper's Theorem (20)
says COT and BFP resolve anaphora identically; its core is table (19), which
matches COHERE/ALIGN violation patterns to the transition ranking, proved here
in general. Because COT constraints are rerankable, demoting PRO-TOP below
FAM-DEF (§4.1) recovers the coreferential reading of (2c) that BFP wrongly
filters out.

## Main statements

* `cot_iff_bfp`: table (19) — for candidates tied on the four higher-ranked
  constraints, the COT profile comparison is the BFP transition preference.
* `d2_canonical_picks_two_marys`, `d2_demoted_picks_bound`: the §4.1
  reranking flips (2c) from the two-Marys reading to the coreferential one.
* `cohere_factors_through_cb`, `align_factors_through_cb_and_cp`: the reused
  constraints see a candidate only through `cb` (and `cp`).

## References

* [beaver-2004]: The optimization of discourse anaphora.
  *Linguistics and Philosophy* 27.
* [brennan-friedman-pollard-1987]: A centering approach to pronouns.
* [grosz-joshi-weinstein-1995]: Centering: a framework for modeling the local
  coherence of discourse.
* [gordon-grosz-gilliom-1993]: Pronouns, names, and the centering of attention
  in discourse.
* [strube-1998]: Never look back: an alternative to centering.
* [poesio-stevenson-eugenio-hitzeman-2004]: Centering: a parametric theory and
  its instantiations.
-/

@[expose] public section

namespace Beaver2004

open Discourse.Centering OptimalityTheory

/-! ### Candidates -/

/-- A COT candidate: a fully-resolved utterance (pronouns bound to entities)
plus verdict flags for the three constraints whose inputs the `Utterance`
substrate does not carry — φ-features (AGREE), predicate-argument structure
(DISJOINT) and definiteness/familiarity (FAM-DEF). -/
structure Candidate (E : Type) (R : Type) where
  /-- The resolved utterance. -/
  utt : Utterance E R
  /-- AGREE verdict: pronoun–antecedent number/gender match. -/
  agreementOK : Bool
  /-- DISJOINT verdict: co-arguments of each predicate are distinct. -/
  argDisjointOK : Bool
  /-- FAM-DEF verdict: every definite NP is familiar. -/
  famDefOK : Bool
  deriving Repr, DecidableEq

/-! ### The six constraints (4) -/

variable {E R : Type}

/-- AGREE: anaphoric expressions agree with their antecedents in number and
gender. -/
def agree : Constraint (Candidate E R) :=
  Constraint.binary (fun c => ¬ c.agreementOK = true)

/-- DISJOINT: co-arguments of a predicate are disjoint (the effect of
Principle B). -/
def disjoint : Constraint (Candidate E R) :=
  Constraint.binary (fun c => ¬ c.argDisjointOK = true)

/-- PRO-TOP: the topic is pronominalized — Rule 1 without its if-clause,
via the unconditional `CbPronominalized` ([gordon-grosz-gilliom-1993]).
With no pronoun in the sentence every candidate violates PRO-TOP alike
(p. 16), so the conditional Rule-1 form would be the wrong primitive. -/
def proTop [DecidableEq E] [LinearOrder R]
    (prev : Utterance E R) : Constraint (Candidate E R) :=
  Constraint.binary (fun c => ¬ CbPronominalized prev c.utt)

/-- FAM-DEF: each definite NP is familiar. -/
def famDef : Constraint (Candidate E R) :=
  Constraint.binary (fun c => ¬ c.famDefOK = true)

/-- COHERE: the topic of the current sentence is the topic of the previous
one — satisfied only when both are defined and equal (p. 17); an undefined
topic counts as a violation. -/
def cohere [DecidableEq E] [LinearOrder R]
    (prev : Utterance E R) (priorTopic : Option E) :
    Constraint (Candidate E R) :=
  Constraint.binary (fun c =>
    ¬ ((cb prev c.utt).isSome ∧ cb prev c.utt = priorTopic))

/-- ALIGN: the topic is in subject position — for canonical sentences, the
topic is the preferred center (p. 18); an undefined topic counts as a
violation. -/
def align [DecidableEq E] [LinearOrder R]
    (prev : Utterance E R) : Constraint (Candidate E R) :=
  Constraint.binary (fun c =>
    ¬ ((cb prev c.utt).isSome ∧ cb prev c.utt = c.utt.cp))

/-- The COT ranking (4): AGREE > DISJOINT > PRO-TOP > FAM-DEF > COHERE >
ALIGN. -/
def cotRanking [DecidableEq E] [LinearOrder R]
    (prev : Utterance E R) (priorTopic : Option E) :
    List (Constraint (Candidate E R)) :=
  [agree, disjoint, proTop prev, famDef, cohere prev priorTopic, align prev]

/-- The §4.1 reranking: PRO-TOP demoted below FAM-DEF. -/
def cotRankingDemoted [DecidableEq E] [LinearOrder R]
    (prev : Utterance E R) (priorTopic : Option E) :
    List (Constraint (Candidate E R)) :=
  [agree, disjoint, famDef, proTop prev, cohere prev priorTopic, align prev]

/-! ### COHERE and ALIGN factor through `cb` (and `cp`) -/

/-- COHERE cannot distinguish candidates whose `cb` agrees. -/
theorem cohere_factors_through_cb [DecidableEq E] [LinearOrder R]
    (prev : Utterance E R) (priorTopic : Option E)
    (c1 c2 : Candidate E R) (h : cb prev c1.utt = cb prev c2.utt) :
    (cohere prev priorTopic) c1 = (cohere prev priorTopic) c2 := by
  simp only [cohere, Constraint.binary_apply, h]

/-- ALIGN cannot distinguish candidates whose `cb` and `cp` both agree. -/
theorem align_factors_through_cb_and_cp [DecidableEq E] [LinearOrder R]
    (prev : Utterance E R)
    (c1 c2 : Candidate E R)
    (h_cb : cb prev c1.utt = cb prev c2.utt)
    (h_cp : c1.utt.cp = c2.utt.cp) :
    (align prev) c1 = (align prev) c2 := by
  simp only [align, Constraint.binary_apply, h_cb, h_cp]

/-! ### Table (19): the COT ranking is the BFP transition preference -/

/-- BFP's four transition types. -/
inductive BFPTransition where
  | continue_
  | retain
  | smoothShift
  | roughShift
  deriving DecidableEq, Repr

/-- The BFP preference: continue > retain > smooth shift > rough shift. -/
def BFPTransition.rank : BFPTransition → ℕ
  | .continue_ => 3
  | .retain => 2
  | .smoothShift => 1
  | .roughShift => 0

/-- The transition a candidate realizes, read off its COHERE and ALIGN
verdicts: topic kept and aligned is a continuation, kept but unaligned a
retain, changed but aligned a smooth shift, changed and unaligned a rough
shift. -/
def bfpTransition [DecidableEq E] [LinearOrder R] (prev : Utterance E R)
    (priorTopic : Option E) (c : Candidate E R) : BFPTransition :=
  if (cohere prev priorTopic) c = 0 then
    if (align prev) c = 0 then .continue_ else .retain
  else
    if (align prev) c = 0 then .smoothShift else .roughShift

private theorem profile_lt_iff_last_two {p q : ViolationProfile 6}
    (h : ∀ i : Fin 6, i.val < 4 → p i = q i) :
    p < q ↔ p 4 < q 4 ∨ (p 4 = q 4 ∧ p 5 < q 5) := by
  constructor
  · rintro ⟨i, hpre, hlt⟩
    rcases Nat.lt_or_ge i.val 4 with hi | hi
    · exact absurd hlt (by rw [h i hi]; exact lt_irrefl _)
    rcases Nat.lt_or_ge i.val 5 with hi5 | hi5
    · have hi4 : i = 4 := Fin.ext (by omega)
      subst hi4
      exact Or.inl hlt
    · have hi6 : i.val < 6 := i.isLt
      have hi5' : i = 5 := Fin.ext (by omega)
      subst hi5'
      exact Or.inr ⟨hpre 4 (by decide), hlt⟩
  · rintro (h4 | ⟨he, h5⟩)
    · exact ⟨4, fun j hj => h j hj, h4⟩
    · refine ⟨5, fun j hj => ?_, h5⟩
      rcases Nat.lt_or_ge j.val 4 with hj4 | hj4
      · exact h j hj4
      · have hj5 : j.val < 5 := hj
        have : j = 4 := Fin.ext (by omega)
        subst this
        exact he

/-- Table (19), in general: for two candidates tied on AGREE, DISJOINT,
PRO-TOP and FAM-DEF, the COT profile comparison under the canonical ranking
coincides with the BFP preference between the transitions they realize —
the core of the equivalence Theorem (20). -/
theorem cot_iff_bfp [DecidableEq E] [LinearOrder R]
    (prev : Utterance E R) (priorTopic : Option E) (c1 c2 : Candidate E R)
    (h : ∀ i : Fin 6, i.val < 4 →
      toLex ((cotRanking prev priorTopic).get · c1) i =
        toLex ((cotRanking prev priorTopic).get · c2) i) :
    toLex ((cotRanking prev priorTopic).get · c1) <
        toLex ((cotRanking prev priorTopic).get · c2) ↔
      (bfpTransition prev priorTopic c2).rank <
        (bfpTransition prev priorTopic c1).rank := by
  rw [profile_lt_iff_last_two h]
  have e1 : ∀ c : Candidate E R,
      toLex ((cotRanking prev priorTopic).get · c) (4 : Fin 6) =
        (cohere prev priorTopic) c := fun _ => rfl
  have e2 : ∀ c : Candidate E R,
      toLex ((cotRanking prev priorTopic).get · c) (5 : Fin 6) =
        (align prev) c := fun _ => rfl
  rw [e1 c1, e1 c2, e2 c1, e2 c2]
  have b1 : (cohere prev priorTopic) c1 ≤ 1 := Constraint.binary_le_one _ _
  have b2 : (cohere prev priorTopic) c2 ≤ 1 := Constraint.binary_le_one _ _
  have b3 : (align prev) c1 ≤ 1 := Constraint.binary_le_one _ _
  have b4 : (align prev) c2 ≤ 1 := Constraint.binary_le_one _ _
  unfold bfpTransition
  split_ifs <;> simp only [BFPTransition.rank] <;> omega

/-! ### Example (12): a retain -/

namespace D12

abbrev Utt := Utterance String GrammaticalRole

/-- (12a) "Jane is happy." -/
def a : Utt := ⟨[⟨"Jane", .subject, false⟩]⟩

/-- (12b) "She was congratulated by Freda." She = Jane. -/
def b : Utt :=
  ⟨[⟨"Jane", .subject, true⟩, ⟨"Freda", .other, false⟩]⟩

/-- (12c) with her = Jane: the winner. -/
def c_l_eq_i : Utt :=
  ⟨[⟨"Mary", .subject, false⟩, ⟨"Jane", .object, true⟩,
    ⟨"present", .other, false⟩]⟩

/-- (12c) with her = Freda: the loser. -/
def c_l_eq_j : Utt :=
  ⟨[⟨"Mary", .subject, false⟩, ⟨"Freda", .object, true⟩,
    ⟨"present", .other, false⟩]⟩

/-- her = Jane, wrapped: AGREE, DISJOINT and FAM-DEF are all satisfied. -/
def cand_l_eq_i : Candidate String GrammaticalRole :=
  ⟨c_l_eq_i, true, true, true⟩

/-- her = Freda, wrapped. -/
def cand_l_eq_j : Candidate String GrammaticalRole :=
  ⟨c_l_eq_j, true, true, true⟩

/-- The prior topic, from (12a) → (12b): Jane. -/
def priorTopic : Option String := cb a b

end D12

/-- The (12c) winner's profile under the canonical ranking. -/
def d12_profile_l_eq_i : ViolationProfile 6 :=
  toLex ((cotRanking D12.b D12.priorTopic).get · D12.cand_l_eq_i)

/-- The (12c) loser's profile. -/
def d12_profile_l_eq_j : ViolationProfile 6 :=
  toLex ((cotRanking D12.b D12.priorTopic).get · D12.cand_l_eq_j)

/-- Tableau (13): the her = Jane candidate wins the lexicographic
comparison. -/
theorem d12_lex_picks_l_eq_i :
    d12_profile_l_eq_i < d12_profile_l_eq_j := by decide

/-- The (12c) winner realizes a retain: Jane stays topic but leaves subject
position. -/
theorem d12_transition_retain :
    bfpTransition D12.b D12.priorTopic D12.cand_l_eq_i = .retain := by decide

/-! ### Example (2): breaking Rule 1 by reranking (§4.1) -/

namespace D2

abbrev Utt := Utterance String GrammaticalRole

/-- (2a) "Mary likes tennis." -/
def a : Utt :=
  ⟨[⟨"Mary", .subject, false⟩, ⟨"tennis", .object, false⟩]⟩

/-- (2b) "She plays Jim quite often." She = Mary. -/
def b : Utt :=
  ⟨[⟨"Mary", .subject, true⟩, ⟨"Jim", .object, false⟩]⟩

/-- (2c), coreferential reading: He = Jim, Mary = the (2a) Mary. -/
def c_bound : Utt :=
  ⟨[⟨"Jim", .subject, true⟩, ⟨"Mary", .other, false⟩]⟩

/-- (2c), two-Marys reading: the object "Mary" is a new entity. -/
def c_two_marys : Utt :=
  ⟨[⟨"Jim", .subject, true⟩, ⟨"Mary_new", .other, false⟩]⟩

/-- Coreferential candidate: the anaphoric "Mary" is familiar. -/
def cand_bound : Candidate String GrammaticalRole :=
  ⟨c_bound, true, true, true⟩

/-- Two-Marys candidate: the new "Mary" is an unfamiliar definite, so
FAM-DEF fires. -/
def cand_two_marys : Candidate String GrammaticalRole :=
  ⟨c_two_marys, true, true, false⟩

/-- The prior topic for (2c): Mary. -/
def priorTopic : Option String := cb a b

end D2

/-- Under the canonical ranking (18), the two-Marys reading wins — BFP's
(incorrect) prediction, driven by PRO-TOP over FAM-DEF. -/
theorem d2_canonical_picks_two_marys :
    toLex ((cotRanking D2.b D2.priorTopic).get · D2.cand_two_marys) <
      toLex ((cotRanking D2.b D2.priorTopic).get · D2.cand_bound) := by
  decide

/-- Under the demoted ranking (21), the coreferential reading wins: FAM-DEF
now outranks PRO-TOP, so introducing a second Mary costs more than leaving
the topic unpronominalized. -/
theorem d2_demoted_picks_bound :
    toLex ((cotRankingDemoted D2.b D2.priorTopic).get · D2.cand_bound) <
      toLex ((cotRankingDemoted D2.b D2.priorTopic).get ·
        D2.cand_two_marys) := by
  decide

/-! ### ALIGN and Strube's cheapness -/

/-- ALIGN is satisfied exactly when the topic is defined and is the current
preferred center — the within-utterance analogue of [strube-1998]'s cheap
transitions, which test the same shape against the *previous* Cp. -/
theorem align_eq_zero_iff [DecidableEq E] [LinearOrder R]
    (prev : Utterance E R) (c : Candidate E R) :
    (align prev) c = 0 ↔
      ((cb prev c.utt).isSome ∧ cb prev c.utt = c.utt.cp) := by
  simp [align]

end Beaver2004
