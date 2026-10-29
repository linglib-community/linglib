module

public import Linglib.Discourse.Centering.Transition
public import Linglib.Discourse.Centering.GrammaticalRole
public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Data.Examples.Beaver2004
public import Linglib.Data.UD.Features
import all Mathlib.Data.List.Sort  -- for unfolding `List.insertionSort`

/-!
# Beaver (2004): The Optimization of Discourse Anaphora

Centering Optimality Theory (COT) restates the centering algorithm of
[brennan-friedman-pollard-1987] (BFP) as six ranked constraints on the interpretations of a
sentence, AGREE > DISJOINT > PRO-TOP > FAM-DEF > COHERE > ALIGN, each counting its violations
from the referents, the forms and the previous sentence. Between two fully anaphoric
interpretations that pass BFP's filters only COHERE and ALIGN decide, so
[COT prefers one exactly when BFP ranks its transition higher](##cot_lt_iff_bfp_lt), and by the
paper's Proposition (20) the two models resolve anaphors alike whenever either predicts a fully
anaphoric interpretation (`cot_iff_bfp`). Because COT constraints are rerankable,
[demoting PRO-TOP below FAM-DEF](##d2_demoted_picks_bound) recovers the coreferential reading of
(2c) that BFP filters out.

## Implementation notes

* A noun phrase is a pronoun with its gender, a proper name or an indefinite (`Form`). Definite
  descriptions, whose familiarity turns on what the discourse establishes about the referent,
  are left out, as Proposition (20) leaves them out. The gender of an antecedent is that of its
  referent.
* A definite is familiar when its referent is mentioned in the previous sentence and, for a
  proper name, has been called by that name in the discourse: the fully anaphoric
  interpretations of Appendix A are anaphoric on elements explicit in the previous sentence, and
  no antecedent in the paper's examples lies further back. AGREE reads anaphora the same way.
* Each sentence of the examples is one clause, so its noun phrases are co-arguments of one
  predicate, and DISJOINT is violated when two of them corefer.
* The interpretations of a sentence give its indefinites new referents (fn. 20). BFP's
  prediction is its algorithm as Appendix A reads it: the fully anaphoric interpretations that
  agree survive the filters for disjoint co-arguments and Rule 1 (`Filtered`), and the one with
  the highest transition is chosen.

## Errata

* Tableau (13) marks no FAM-DEF violation, though *Mary* in (12c) is a proper name new to the
  discourse, which FAM-DEF counts (fn. 14, and the tableaux for (5c) and (8c)). Both
  candidates incur it (`d12_famDef`), so the winner is unaffected.

## TODO

* Of Proposition (20), the half from BFP to COT is `cot_optimal_of_bfp`, and the half from COT
  to BFP rests on `filtered_of_cot_optimal`, stated with `sorry`: a fully anaphoric COT optimum
  passes BFP's filters. Following Appendix A, an interpretation violating AGREE or DISJOINT loses
  to the one giving every noun phrase a new referent (Proposition 1), and one violating Rule 1
  loses at PRO-TOP to the one keeping its pronouns and giving its other noun phrases new
  referents (Proposition 2). Building these interpretations uses `Infinite E` and a lemma
  computing `cb` when the previous sentence's entities are realized only by pronouns.

## References

* [beaver-2004]
* [brennan-friedman-pollard-1987]
* [walker-iida-cote-1994]
* [grosz-joshi-weinstein-1995]
* [gordon-grosz-gilliom-1993]
* [strube-1998]
* [poesio-stevenson-eugenio-hitzeman-2004]
-/

@[expose] public section

namespace Beaver2004

open Discourse.Centering OptimalityTheory

/-! ### Interpretations -/

/-- The form of a noun phrase: a pronoun with its gender, a proper name, or an indefinite. -/
inductive Form (Φ N : Type) where
  | pronoun (φ : Φ)
  | name (n : N)
  | indefinite
  deriving DecidableEq, Repr

/-- A form is a pronoun. -/
def Form.IsPronoun {Φ N : Type} : Form Φ N → Prop
  | .pronoun _ => True
  | _ => False

instance {Φ N : Type} : DecidablePred (Form.IsPronoun : Form Φ N → Prop) := fun f ↦ by
  cases f <;> unfold Form.IsPronoun <;> infer_instance

/-- The pronouns, the forms PRO-TOP and Rule 1 count. -/
def pronouns {Φ N : Type} : Set (Form Φ N) := {f | f.IsPronoun}

instance {Φ N : Type} : DecidablePred (· ∈ (pronouns : Set (Form Φ N))) := fun f ↦
  inferInstanceAs (Decidable f.IsPronoun)

/-- A candidate interpretation of a sentence: its noun phrases, each with its role, its form and
the referent the interpretation gives it. -/
abbrev Candidate (E R Φ N : Type) := Utterance E R (Form Φ N)

variable {E R Φ N : Type}

/-- The noun phrases of a candidate in role and form, which the interpretations of one sentence
share. -/
def sentence (c : Candidate E R Φ N) : List (R × Form Φ N) :=
  c.realizations.map fun r ↦ (r.role, r.form)

/-- A noun phrase is familiar after the previous sentence `prev` in the discourse `ctx` when it
is no definite, or its referent is mentioned in `prev` and, for a proper name, has been called by
that name in the discourse, so that the definite gives no new information about it. -/
def Familiar (ctx : List (Candidate E R Φ N)) (prev : Candidate E R Φ N)
    (r : Realization E R (Form Φ N)) : Prop :=
  match r.form with
  | .pronoun _ => r.entity ∈ prev
  | .name n => r.entity ∈ prev ∧
      ∃ u ∈ ctx, ∃ r' ∈ u.realizations, r'.entity = r.entity ∧ r'.form = .name n
  | .indefinite => True

/-- A pronoun whose referent the previous sentence mentions disagrees with its antecedent when
its gender is not its referent's. -/
def Disagrees (feat : E → Φ) (prev : Candidate E R Φ N) (r : Realization E R (Form Φ N)) :
    Prop :=
  match r.form with
  | .pronoun φ => r.entity ∈ prev ∧ φ ≠ feat r.entity
  | _ => False

variable [DecidableEq E] [DecidableEq Φ] [DecidableEq N]

instance (ctx : List (Candidate E R Φ N)) (prev : Candidate E R Φ N)
    (r : Realization E R (Form Φ N)) : Decidable (Familiar ctx prev r) := by
  unfold Familiar; split <;> infer_instance

instance (feat : E → Φ) (prev : Candidate E R Φ N) (r : Realization E R (Form Φ N)) :
    Decidable (Disagrees feat prev r) := by
  unfold Disagrees; split <;> infer_instance

/-! ### The six constraints (4) -/

/-- AGREE: anaphoric pronouns agree with their antecedents in gender. -/
def agree (feat : E → Φ) (prev : Candidate E R Φ N) : Constraint (Candidate E R Φ N) :=
  fun c ↦ c.realizations.countP fun r ↦ decide (Disagrees feat prev r)

/-- DISJOINT: co-arguments of a predicate are disjoint. -/
def disjoint : Constraint (Candidate E R Φ N) :=
  Constraint.binary fun c ↦ ¬ (c.realizations.map (·.entity)).Nodup

/-- FAM-DEF: each definite NP is familiar. -/
def famDef (ctx : List (Candidate E R Φ N)) (prev : Candidate E R Φ N) :
    Constraint (Candidate E R Φ N) :=
  fun c ↦ c.realizations.countP fun r ↦ decide (¬ Familiar ctx prev r)

theorem famDef_eq_zero_iff {ctx : List (Candidate E R Φ N)} {prev c : Candidate E R Φ N} :
    famDef ctx prev c = 0 ↔ ∀ r ∈ c.realizations, Familiar ctx prev r := by
  simp [famDef, List.countP_eq_zero]

variable [LinearOrder R]

/-- PRO-TOP: the topic is pronominalized. A candidate with no topic violates it (p. 16), as does
one with no pronoun, so it needs none of Rule 1's if-clause. -/
def proTop (prev : Candidate E R Φ N) : Constraint (Candidate E R Φ N) :=
  Constraint.binary fun c ↦ ¬ ∃ t ∈ cb prev c, c.Pronominalizes pronouns t

/-- COHERE: the topic of the current sentence is the topic of the previous one, so that a
candidate with no topic violates it (p. 17). -/
def cohere (prev : Candidate E R Φ N) (priorTopic : Option E) : Constraint (Candidate E R Φ N) :=
  Constraint.binary fun c ↦ ¬ ((cb prev c).isSome ∧ cb prev c = priorTopic)

/-- ALIGN: the topic is in subject position, for canonical sentences the preferred center
(p. 18); a candidate with no topic violates it. -/
def align (prev : Candidate E R Φ N) : Constraint (Candidate E R Φ N) :=
  Constraint.binary fun c ↦ ¬ ((cb prev c).isSome ∧ cb prev c = c.cp)

/-- The COT ranking (4): AGREE > DISJOINT > PRO-TOP > FAM-DEF > COHERE > ALIGN. -/
def cotRanking (feat : E → Φ) (ctx : List (Candidate E R Φ N)) (prev : Candidate E R Φ N)
    (priorTopic : Option E) : List (Constraint (Candidate E R Φ N)) :=
  [agree feat prev, disjoint, proTop prev, famDef ctx prev, cohere prev priorTopic, align prev]

/-- The reranking of §4.1, PRO-TOP below FAM-DEF. -/
def cotRankingDemoted (feat : E → Φ) (ctx : List (Candidate E R Φ N)) (prev : Candidate E R Φ N)
    (priorTopic : Option E) : List (Constraint (Candidate E R Φ N)) :=
  [agree feat prev, disjoint, famDef ctx prev, proTop prev, cohere prev priorTopic, align prev]

omit [DecidableEq Φ] [DecidableEq N] in
theorem cohere_factors_through_cb (prev : Candidate E R Φ N) (priorTopic : Option E)
    (c₁ c₂ : Candidate E R Φ N) (h : cb prev c₁ = cb prev c₂) :
    cohere prev priorTopic c₁ = cohere prev priorTopic c₂ := by
  simp only [cohere, Constraint.binary_apply, h]

omit [DecidableEq Φ] [DecidableEq N] in
theorem align_factors_through_cb_and_cp (prev c₁ c₂ : Candidate E R Φ N)
    (h_cb : cb prev c₁ = cb prev c₂) (h_cp : c₁.cp = c₂.cp) :
    align prev c₁ = align prev c₂ := by
  simp only [align, Constraint.binary_apply, h_cb, h_cp]

-- [strube-1998]
omit [DecidableEq Φ] [DecidableEq N] in
theorem align_eq_zero_iff (prev c : Candidate E R Φ N) :
    align prev c = 0 ↔ (cb prev c).isSome ∧ cb prev c = c.cp := by
  simp [align]

/-! ### BFP's filters and its transition ranking (19) -/

/-- An interpretation survives the construction and filtering stages of BFP's algorithm: it is
fully anaphoric, its pronouns agree with their antecedents, its co-arguments are disjoint, and it
satisfies Rule 1. -/
structure Filtered (feat : E → Φ) (ctx : List (Candidate E R Φ N)) (prev c : Candidate E R Φ N) :
    Prop where
  agree_eq : agree feat prev c = 0
  disjoint_eq : disjoint c = 0
  famDef_eq : famDef ctx prev c = 0
  rule1 : PronominalizationConstraint pronouns prev c

/-- The transition a candidate realizes, read off its COHERE and ALIGN verdicts. -/
def bfpTransition (prev : Candidate E R Φ N) (priorTopic : Option E) (c : Candidate E R Φ N) :
    ExtendedTransition :=
  .ofTests (cohere prev priorTopic c = 0) (align prev c = 0)

-- p. 17 [brennan-friedman-pollard-1987]
omit [DecidableEq Φ] [DecidableEq N] in
theorem bfpTransition_some {prev c : Candidate E R Φ N} {p x : E} (h : cb prev c = some x) :
    bfpTransition prev (some p) c = .ofCenters (some p) x c.cp := by
  ext <;> simp [bfpTransition, ExtendedTransition.ofCenters, cohere, align, h] <;> exact eq_comm

-- p. 17 [walker-iida-cote-1994]
omit [DecidableEq Φ] [DecidableEq N] in
theorem bfpTransition_none_cohesion (prev c : Candidate E R Φ N) :
    (bfpTransition prev none c).cohesion = false := by
  simp [bfpTransition, cohere, Option.isSome_iff_ne_none]

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

-- (19)
theorem cot_lt_iff_bfp_lt_of_tied (feat : E → Φ) (ctx : List (Candidate E R Φ N))
    (prev : Candidate E R Φ N) (priorTopic : Option E) (c₁ c₂ : Candidate E R Φ N)
    (h : ∀ i : Fin 6, i.val < 4 →
      toLex ((cotRanking feat ctx prev priorTopic).get · c₁) i =
        toLex ((cotRanking feat ctx prev priorTopic).get · c₂) i) :
    toLex ((cotRanking feat ctx prev priorTopic).get · c₁) <
        toLex ((cotRanking feat ctx prev priorTopic).get · c₂) ↔
      bfpTransition prev priorTopic c₂ < bfpTransition prev priorTopic c₁ := by
  rw [profile_lt_iff_last_two h]
  have e1 : ∀ c : Candidate E R Φ N,
      toLex ((cotRanking feat ctx prev priorTopic).get · c) (4 : Fin 6) =
        cohere prev priorTopic c := fun _ => rfl
  have e2 : ∀ c : Candidate E R Φ N,
      toLex ((cotRanking feat ctx prev priorTopic).get · c) (5 : Fin 6) = align prev c :=
    fun _ => rfl
  rw [e1 c₁, e1 c₂, e2 c₁, e2 c₂]
  have b1 : cohere prev priorTopic c₁ ≤ 1 := Constraint.binary_le_one _ _
  have b2 : cohere prev priorTopic c₂ ≤ 1 := Constraint.binary_le_one _ _
  have b3 : align prev c₁ ≤ 1 := Constraint.binary_le_one _ _
  have b4 : align prev c₂ ≤ 1 := Constraint.binary_le_one _ _
  simp only [ExtendedTransition.lt_iff_toLex_lt, Prod.Lex.toLex_lt_toLex, bfpTransition,
    ExtendedTransition.cohesion_ofTests, ExtendedTransition.salience_ofTests, Bool.lt_iff,
    decide_eq_true_eq, decide_eq_false_iff_not, decide_eq_decide]
  omega

omit [DecidableEq Φ] [DecidableEq N] in
private theorem proTop_eq_one {prev c : Candidate E R Φ N}
    (h : ¬ ∃ x ∈ sentence c, x.2 ∈ pronouns) : proTop prev c = 1 := by
  have hn : ¬ ∃ t ∈ cb prev c, c.Pronominalizes pronouns t :=
    fun ⟨_, _, r, hr, _, hrp⟩ ↦ h ⟨_, List.mem_map_of_mem hr, hrp⟩
  rw [proTop, Constraint.binary_apply, ite_eq_left hn]

-- p. 51: under Rule 1, PRO-TOP is met exactly when the sentence has a pronoun
private theorem proTop_eq {ctx : List (Candidate E R Φ N)} {prev c : Candidate E R Φ N}
    (hf : famDef ctx prev c = 0) (h1 : PronominalizationConstraint pronouns prev c) :
    proTop prev c = if ∃ x ∈ sentence c, x.2 ∈ pronouns then 0 else 1 := by
  rw [proTop, Constraint.binary_apply]
  by_cases hp : ∃ x ∈ sentence c, x.2 ∈ pronouns
  · obtain ⟨_, hx, hxp⟩ := hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    have hfam := famDef_eq_zero_iff.1 hf r hr
    have he : r.entity ∈ prev := by
      rcases r with ⟨e, ρ, φ | n | _⟩
      · exact hfam
      · exact (hxp : False).elim
      · exact (hxp : False).elim
    have hcf : r.entity ∈ prev.cf := prev.mem_cf.2 he
    obtain ⟨t, ht⟩ : ∃ t, cb prev c = some t :=
      Option.ne_none_iff_exists'.1 fun h ↦ cb_eq_none_iff.1 h _ hcf ⟨r, hr, rfl⟩
    have htop : ∃ t ∈ cb prev c, c.Pronominalizes pronouns t :=
      ⟨t, ht, h1 ⟨_, hcf, r, hr, rfl, hxp⟩ t ht⟩
    have hp : ∃ x ∈ sentence c, x.2 ∈ pronouns := ⟨_, hx, hxp⟩
    rw [ite_eq_right (not_not.2 htop), ite_eq_left hp]
  · rw [ite_eq_right hp]
    exact proTop_eq_one hp

/-- Proposition 3: between two fully anaphoric interpretations of a sentence that pass BFP's
filters, COT prefers one exactly when BFP ranks its transition higher, the pairwise
competitions of table (19). -/
theorem cot_lt_iff_bfp_lt {feat : E → Φ} {ctx : List (Candidate E R Φ N)}
    {prev c₁ c₂ : Candidate E R Φ N} {priorTopic : Option E} (hs : sentence c₁ = sentence c₂)
    (h₁ : Filtered feat ctx prev c₁) (h₂ : Filtered feat ctx prev c₂) :
    toLex ((cotRanking feat ctx prev priorTopic).get · c₁) <
        toLex ((cotRanking feat ctx prev priorTopic).get · c₂) ↔
      bfpTransition prev priorTopic c₂ < bfpTransition prev priorTopic c₁ := by
  refine cot_lt_iff_bfp_lt_of_tied feat ctx prev priorTopic c₁ c₂ fun i hi ↦ ?_
  match i, hi with
  | ⟨0, _⟩, _ => exact h₁.agree_eq.trans h₂.agree_eq.symm
  | ⟨1, _⟩, _ => exact h₁.disjoint_eq.trans h₂.disjoint_eq.symm
  | ⟨2, _⟩, _ =>
    change proTop prev c₁ = proTop prev c₂
    rw [proTop_eq h₁.famDef_eq h₁.rule1, proTop_eq h₂.famDef_eq h₂.rule1, hs]
  | ⟨3, _⟩, _ => exact h₁.famDef_eq.trans h₂.famDef_eq.symm
  | ⟨n + 4, _⟩, h => exact absurd h (Nat.not_lt.2 (Nat.le_add_left 4 n))

/-- The interpretations of the sentence `s` in the discourse `ctx`: its noun phrases with a
referent each, the indefinites new ones (fn. 20). -/
def interpretations (ctx : List (Candidate E R Φ N)) (s : List (R × Form Φ N)) :
    Set (Candidate E R Φ N) :=
  {c | sentence c = s ∧ ∀ r ∈ c.realizations, r.form = .indefinite → ∀ u ∈ ctx, r.entity ∉ u}

private theorem lt_of_le_of_not_tied {p q : ViolationProfile 6}
    (hle : ∀ i : Fin 6, i.val < 4 → p i ≤ q i) (hne : ¬ ∀ i : Fin 6, i.val < 4 → p i = q i) :
    p < q := by
  classical
  have hex : ∃ n, n < 4 ∧ ∃ h : n < 6, p ⟨n, h⟩ ≠ q ⟨n, h⟩ := by
    obtain ⟨i, hne⟩ := not_forall.1 hne
    obtain ⟨hi, hpq⟩ := not_imp.1 hne
    exact ⟨i.val, hi, i.isLt, hpq⟩
  have h4 := (Nat.find_spec hex).1
  refine ⟨⟨Nat.find hex, by omega⟩, fun j hj ↦ ?_, ?_⟩
  · have hj' : j.val < Nat.find hex := hj
    by_contra hpq
    exact Nat.find_min hex hj' ⟨by omega, j.isLt, hpq⟩
  · obtain ⟨-, _, hpq⟩ := Nat.find_spec hex
    exact lt_of_le_of_ne (hle _ h4) hpq

-- Appendix A, Propositions 1 to 3, from BFP to COT
theorem cot_optimal_of_bfp {feat : E → Φ} {ctx : List (Candidate E R Φ N)}
    {prev c d : Candidate E R Φ N} {priorTopic : Option E} {s : List (R × Form Φ N)}
    (hc : c ∈ interpretations ctx s) (hf : Filtered feat ctx prev c)
    (hb : ∀ d ∈ interpretations ctx s, Filtered feat ctx prev d → d ≠ c →
      bfpTransition prev priorTopic d < bfpTransition prev priorTopic c)
    (hd : d ∈ interpretations ctx s) (hdc : d ≠ c) :
    toLex ((cotRanking feat ctx prev priorTopic).get · c) <
      toLex ((cotRanking feat ctx prev priorTopic).get · d) := by
  have hs : sentence c = sentence d := hc.1.trans hd.1.symm
  have hpro : proTop prev c ≤ proTop prev d ∧
      (proTop prev d = proTop prev c → PronominalizationConstraint pronouns prev d) := by
    rw [proTop_eq hf.famDef_eq hf.rule1]
    by_cases hp : ∃ x ∈ sentence c, x.2 ∈ pronouns
    · rw [ite_eq_left hp]
      refine ⟨Nat.zero_le _, fun h0 ↦ ?_⟩
      rw [proTop, Constraint.binary_apply] at h0
      have htop : ∃ t ∈ cb prev d, d.Pronominalizes pronouns t := by
        by_contra hn
        rw [ite_eq_left hn] at h0
        exact one_ne_zero h0
      obtain ⟨t, ht, htp⟩ := htop
      exact CbPronominalized.constraint fun t' ht' ↦ Option.mem_unique ht ht' ▸ htp
    · rw [ite_eq_right hp, proTop_eq_one (prev := prev) (c := d) (hs ▸ hp)]
      refine ⟨le_rfl, fun _ ↦ pronominalizationConstraint_of_forall_not ?_⟩
      rintro e ⟨r, hr, -, hrp⟩
      have hd' : ∃ x ∈ sentence d, x.2 ∈ pronouns := ⟨_, List.mem_map_of_mem hr, hrp⟩
      exact hp (hs ▸ hd')
  by_cases htied : ∀ i : Fin 6, i.val < 4 →
      toLex ((cotRanking feat ctx prev priorTopic).get · c) i =
        toLex ((cotRanking feat ctx prev priorTopic).get · d) i
  · have hfd : Filtered feat ctx prev d :=
      { agree_eq := (htied 0 (by decide)).symm.trans hf.agree_eq
        disjoint_eq := (htied 1 (by decide)).symm.trans hf.disjoint_eq
        famDef_eq := (htied 3 (by decide)).symm.trans hf.famDef_eq
        rule1 := hpro.2 (htied 2 (by decide)).symm }
    exact (cot_lt_iff_bfp_lt_of_tied feat ctx prev priorTopic c d htied).2 (hb d hd hfd hdc)
  refine lt_of_le_of_not_tied (fun i hi ↦ ?_) htied
  match i, hi with
  | ⟨0, _⟩, _ =>
    change agree feat prev c ≤ agree feat prev d
    exact hf.agree_eq ▸ Nat.zero_le _
  | ⟨1, _⟩, _ =>
    change disjoint c ≤ disjoint d
    exact hf.disjoint_eq ▸ Nat.zero_le _
  | ⟨2, _⟩, _ => exact hpro.1
  | ⟨3, _⟩, _ =>
    change famDef ctx prev c ≤ famDef ctx prev d
    exact hf.famDef_eq ▸ Nat.zero_le _
  | ⟨n + 4, _⟩, h => exact absurd h (Nat.not_lt.2 (Nat.le_add_left 4 n))

-- Appendix A, Propositions 1 and 2, from COT to BFP
theorem filtered_of_cot_optimal [Infinite E] {feat : E → Φ} {ctx : List (Candidate E R Φ N)}
    {prev c : Candidate E R Φ N} {priorTopic : Option E} {s : List (R × Form Φ N)}
    (hc : c ∈ interpretations ctx s) (hf : famDef ctx prev c = 0)
    (ho : ∀ d ∈ interpretations ctx s, d ≠ c →
      toLex ((cotRanking feat ctx prev priorTopic).get · c) <
        toLex ((cotRanking feat ctx prev priorTopic).get · d)) :
    Filtered feat ctx prev c := by
  sorry

/-- Proposition (20): for a sentence whose definites are proper names and pronouns, COT predicts
a unique interpretation that is fully anaphoric exactly when BFP's algorithm predicts it uniquely,
so that the two models then resolve the anaphors alike. -/
theorem cot_iff_bfp [Infinite E] (feat : E → Φ) (ctx : List (Candidate E R Φ N))
    (prev : Candidate E R Φ N) (priorTopic : Option E) (s : List (R × Form Φ N))
    (c : Candidate E R Φ N) :
    (c ∈ interpretations ctx s ∧ famDef ctx prev c = 0 ∧
        ∀ d ∈ interpretations ctx s, d ≠ c →
          toLex ((cotRanking feat ctx prev priorTopic).get · c) <
            toLex ((cotRanking feat ctx prev priorTopic).get · d)) ↔
      c ∈ interpretations ctx s ∧ Filtered feat ctx prev c ∧
        ∀ d ∈ interpretations ctx s, Filtered feat ctx prev d → d ≠ c →
          bfpTransition prev priorTopic d < bfpTransition prev priorTopic c := by
  refine ⟨fun ⟨hc, hf, ho⟩ ↦ ?_, fun ⟨hc, hfc, hb⟩ ↦
    ⟨hc, hfc.famDef_eq, fun _ hd hdc ↦ cot_optimal_of_bfp hc hfc hb hd hdc⟩⟩
  have hfc := filtered_of_cot_optimal hc hf ho
  exact ⟨hc, hfc, fun d hd hfd hdc ↦
    (cot_lt_iff_bfp_lt (hc.1.trans hd.1.symm) hfc hfd).1 (ho d hd hdc)⟩

/-! ### Examples (12) and (2) -/

/-- The individuals of examples (12) and (2), `mary₂` the second Mary of a reading of (2c). -/
inductive Entity
  | jane | freda | mary | present | tennis | jim | mary₂
  deriving DecidableEq, Repr

/-- The proper names of the examples. -/
inductive Name
  | jane | freda | mary | jim
  deriving DecidableEq, Repr

/-- The gender of each individual. -/
def Entity.gender : Entity → UD.Gender
  | .jim => .Masc
  | .present | .tennis => .Neut
  | _ => .Fem

/-- An interpretation of a sentence of the examples. -/
abbrev Interpretation := Candidate Entity GrammaticalRole UD.Gender Name

namespace D12

/-- (12a) *Jane is happy.* -/
def a : Interpretation := ⟨[⟨.jane, .subject, .name .jane⟩]⟩

/-- (12b) *She was congratulated by Freda*, she = Jane. -/
def b : Interpretation := ⟨[⟨.jane, .subject, .pronoun .Fem⟩, ⟨.freda, .other, .name .freda⟩]⟩

/-- (12c) *and Mary gave her a present* with her = Jane, the winner. -/
def c_l_eq_i : Interpretation :=
  ⟨[⟨.mary, .subject, .name .mary⟩, ⟨.jane, .object, .pronoun .Fem⟩,
    ⟨.present, .other, .indefinite⟩]⟩

/-- (12c) with her = Freda, the loser. -/
def c_l_eq_j : Interpretation :=
  ⟨[⟨.mary, .subject, .name .mary⟩, ⟨.freda, .object, .pronoun .Fem⟩,
    ⟨.present, .other, .indefinite⟩]⟩

/-- The prior topic, from (12a) to (12b): Jane. -/
def priorTopic : Option Entity := cb a b

/-- The violation profile of a reading of (12c) under the COT ranking. -/
def profile (c : Interpretation) : ViolationProfile 6 :=
  toLex ((cotRanking Entity.gender [a, b] b priorTopic).get · c)

end D12

-- (13)
theorem d12_lex_picks_l_eq_i : D12.profile D12.c_l_eq_i < D12.profile D12.c_l_eq_j := by decide

-- (12c)
theorem d12_transition_retain :
    bfpTransition D12.b D12.priorTopic D12.c_l_eq_i = .retain := by decide

-- (13)
theorem d12_famDef : famDef [D12.a, D12.b] D12.b D12.c_l_eq_i = 1 ∧
    famDef [D12.a, D12.b] D12.b D12.c_l_eq_j = 1 := by decide

namespace D2

/-- (2a) *Mary likes tennis.* -/
def a : Interpretation := ⟨[⟨.mary, .subject, .name .mary⟩, ⟨.tennis, .object, .indefinite⟩]⟩

/-- (2b) *She plays Jim quite often*, she = Mary. -/
def b : Interpretation := ⟨[⟨.mary, .subject, .pronoun .Fem⟩, ⟨.jim, .object, .name .jim⟩]⟩

/-- (2c) *He used to play doubles with Mary* with he = Jim and Mary the Mary of (2a). -/
def c_bound : Interpretation :=
  ⟨[⟨.jim, .subject, .pronoun .Masc⟩, ⟨.mary, .other, .name .mary⟩]⟩

/-- (2c) with he = Jim and a second Mary, a proper name new to the discourse. -/
def c_two_marys : Interpretation :=
  ⟨[⟨.jim, .subject, .pronoun .Masc⟩, ⟨.mary₂, .other, .name .mary⟩]⟩

/-- The prior topic, from (2a) to (2b): Mary. -/
def priorTopic : Option Entity := cb a b

end D2

/-- Under the ranking (4) the two-Marys reading of (2c) wins, BFP's prediction, since PRO-TOP
outranks FAM-DEF (18). -/
theorem d2_canonical_picks_two_marys :
    toLex ((cotRanking Entity.gender [D2.a, D2.b] D2.b D2.priorTopic).get · D2.c_two_marys) <
      toLex ((cotRanking Entity.gender [D2.a, D2.b] D2.b D2.priorTopic).get · D2.c_bound) := by
  decide

/-- With PRO-TOP demoted below FAM-DEF (21) the coreferential reading of (2c) wins: introducing a
second Mary costs more than leaving the topic unpronominalized. -/
theorem d2_demoted_picks_bound :
    toLex ((cotRankingDemoted Entity.gender [D2.a, D2.b] D2.b D2.priorTopic).get · D2.c_bound) <
      toLex ((cotRankingDemoted Entity.gender [D2.a, D2.b] D2.b D2.priorTopic).get ·
        D2.c_two_marys) := by
  decide

end Beaver2004
