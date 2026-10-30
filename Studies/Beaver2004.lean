module

public import Linglib.Discourse.Centering.Transition
public import Linglib.Discourse.Centering.GrammaticalRole
public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Data.Examples.Beaver2004
public import Linglib.Data.UD.Features
import all Mathlib.Data.List.Sort  -- for unfolding `List.insertionSort`
import Mathlib.Data.List.FinRange
import Mathlib.Data.Set.Finite.Basic

/-!
# Beaver (2004): The Optimization of Discourse Anaphora

Centering Optimality Theory (COT) restates the centering algorithm of
[brennan-friedman-pollard-1987] (BFP) as six ranked constraints, AGREE > DISJOINT > PRO-TOP >
FAM-DEF > COHERE > ALIGN. Between two fully anaphoric interpretations that pass BFP's filters,
[COT prefers one exactly when BFP ranks its transition higher](##cot_lt_iff_bfp_lt), and
[the two models predict the same unique fully anaphoric interpretation](##cot_iff_bfp), as
[for (1c)](##d1_cot_optimal). BFP's Rule 1 [filters out the coreferential reading of
(2c)](##d2_bound_not_filtered), which COT recovers by
[demoting PRO-TOP below FAM-DEF](##d2_demoted_picks_bound).

## Implementation notes

* A noun phrase is a pronoun with its gender, a proper name or an indefinite (`Form`). Definite
  descriptions are left out, as Proposition (20) leaves them out, and the gender of an
  antecedent is that of its referent.
* A definite is familiar when its referent is mentioned in the previous sentence and, for a
  proper name, has been called by that name in the discourse: the fully anaphoric
  interpretations of Appendix A are anaphoric on elements explicit in the previous sentence.
  AGREE reads anaphora the same way.
* Each sentence of the examples is one clause, so DISJOINT is violated, once, when two of its
  noun phrases corefer.
* The interpretations of a sentence give its indefinites new referents (fn. 20), and the
  discourse includes the previous sentence (`prev ∈ ctx`), so that no indefinite realizes an
  entity of it. BFP's prediction is the fully anaphoric interpretation surviving the filters
  (`Filtered`) with the highest transition (`bfpTransition`), an interpretation without a topic
  having none.
* COHERE is satisfied only when the topic is defined and unchanged (p. 17), so with no prior
  topic every candidate violates it (`cohere_none`), while the first transition test of
  [walker-iida-cote-1994] passes when there is no prior center
  (`bfpTransition_none_eq_ofTests`). Both treat the candidates of a sentence alike, and the
  comparison of (19) holds either way (`cot_lt_iff_bfp_lt_of_tied`).
* Both readings of (12c) violate FAM-DEF (`d12_famDef`), *Mary* being new, so (12) lies outside
  `Filtered` and Proposition (20); (1) instantiates them.

## Errata

* Tableau (13) marks no FAM-DEF violation, though *Mary* in (12c) is a proper name new to the
  discourse, which FAM-DEF counts (fn. 14, and the tableaux for (5c) and (8c)). Both
  candidates incur it (`d12_famDef`), so the winner is unaffected.

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
inductive Form (Φ N : Type*) where
  | pronoun (φ : Φ)
  | name (n : N)
  | indefinite
  deriving DecidableEq, Repr

variable {E R Φ N : Type*}

/-- The pronouns, the forms PRO-TOP and Rule 1 count. -/
def pronouns : Set (Form Φ N) := Set.range .pronoun

instance : DecidablePred (· ∈ (pronouns : Set (Form Φ N)))
  | .pronoun φ => isTrue (Set.mem_range_self φ)
  | .name _ => isFalse fun h ↦ by simp [pronouns] at h
  | .indefinite => isFalse fun h ↦ by simp [pronouns] at h

/-- A candidate interpretation of a sentence: its noun phrases, each with its role, its form and
the referent the interpretation gives it. -/
abbrev Candidate (E R Φ N : Type*) := Utterance E R (Form Φ N)

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

theorem Disagrees.mem {feat : E → Φ} {prev : Candidate E R Φ N} {r : Realization E R (Form Φ N)}
    (h : Disagrees feat prev r) : r.entity ∈ prev := by
  unfold Disagrees at h
  split at h
  · exact h.1
  · exact h.elim

/-- The interpretations of the sentence `s` in the discourse `ctx`: its noun phrases with a
referent each, the indefinites new ones (fn. 20). -/
def interpretations (ctx : List (Candidate E R Φ N)) (s : List (R × Form Φ N)) :
    Set (Candidate E R Φ N) :=
  {c | sentence c = s ∧ ∀ r ∈ c.realizations, r.form = .indefinite → ∀ u ∈ ctx, r.entity ∉ u}

/-! ### Reassigning referents -/

section Reassign

variable {ctx : List (Candidate E R Φ N)} {c : Candidate E R Φ N} {s : List (R × Form Φ N)}

/-- The interpretation of the sentence of `c` that gives its `i`-th noun phrase the referent
`ent i`. -/
private def reassign (c : Candidate E R Φ N) (ent : Fin c.realizations.length → E) :
    Candidate E R Φ N :=
  ⟨List.ofFn fun i ↦ ⟨ent i, c.realizations[i].role, c.realizations[i].form⟩⟩

/-- The referents keeping that of the `k`-th noun phrase of `c` and drawing the others from
`g`. -/
private def keepOne (c : Candidate E R Φ N) (g : ℕ → E) (k : ℕ)
    (i : Fin c.realizations.length) : E :=
  if i.val = k then c.realizations[i].entity else g i

private theorem mem_reassign {ent : Fin c.realizations.length → E}
    {r : Realization E R (Form Φ N)} : r ∈ (reassign c ent).realizations ↔
      ∃ i, (⟨ent i, c.realizations[i].role, c.realizations[i].form⟩ : Realization _ _ _) = r :=
  List.mem_ofFn

private theorem sentence_reassign (ent : Fin c.realizations.length → E) :
    sentence (reassign c ent) = sentence c :=
  List.ext_getElem (by simp [sentence, reassign]) fun i _ _ ↦ by simp [sentence, reassign]

private theorem reassign_mem_interpretations {ent : Fin c.realizations.length → E}
    (hc : c ∈ interpretations ctx s)
    (hent : ∀ i, c.realizations[i].form = .indefinite → ∀ u ∈ ctx, ent i ∉ u) :
    reassign c ent ∈ interpretations ctx s := by
  refine ⟨(sentence_reassign ent).trans hc.1, fun r hr hind u hu ↦ ?_⟩
  obtain ⟨i, rfl⟩ := mem_reassign.1 hr
  exact hent i hind u hu

private theorem keepOne_injective {g : ℕ → E} {k : ℕ} (hg : Function.Injective g)
    (hgc : ∀ n, g n ∉ c) : Function.Injective (keepOne c g k) := by
  intro i j h
  by_cases hi : i.val = k <;> by_cases hj : j.val = k <;>
    simp only [keepOne, hi, hj, ↓reduceIte] at h
  · exact Fin.ext (hi.trans hj.symm)
  · exact (hgc _ ⟨_, List.getElem_mem _, h⟩).elim
  · exact (hgc _ ⟨_, List.getElem_mem _, h.symm⟩).elim
  · exact Fin.ext (hg h)

private theorem exists_fresh [Infinite E] (S : Finset E) :
    ∃ g : ℕ → E, Function.Injective g ∧ ∀ n, g n ∉ S :=
  let f := S.finite_toSet.infinite_compl.natEmbedding _
  ⟨fun n ↦ f n, Subtype.val_injective.comp f.injective, fun n ↦ (f n).2⟩

end Reassign

variable [DecidableEq E]

/-! ### The six constraints (4) -/

/-- DISJOINT: co-arguments of a predicate are disjoint. -/
def disjoint : Constraint (Candidate E R Φ N) :=
  Constraint.binary fun c ↦ ¬ (c.realizations.map (·.entity)).Nodup

theorem disjoint_eq_zero_iff {c : Candidate E R Φ N} :
    disjoint c = 0 ↔ (c.realizations.map (·.entity)).Nodup := by
  simp [disjoint]

private theorem disjoint_reassign {c : Candidate E R Φ N} {g : ℕ → E} {k : ℕ}
    (hg : Function.Injective g) (hgc : ∀ n, g n ∉ c) :
    disjoint (reassign c (keepOne c g k)) = 0 := by
  refine disjoint_eq_zero_iff.2 ?_
  simpa [reassign, Function.comp_def] using List.nodup_ofFn.2 (keepOne_injective hg hgc)

section Order

variable [LinearOrder R] {prev c : Candidate E R Φ N} {x : E}

/-- PRO-TOP: the topic is pronominalized. A candidate with no topic violates it (p. 16), as does
one with no pronoun, so it needs none of Rule 1's if-clause. -/
def proTop (prev : Candidate E R Φ N) : Constraint (Candidate E R Φ N) :=
  Constraint.binary fun c ↦ ¬ ∃ t ∈ cb prev c, c.Pronominalizes pronouns t

/-- COHERE: the topic of the current sentence is the topic of the previous one, so that a
candidate with no topic violates it, as does every candidate when there is no prior topic
(p. 17). -/
def cohere (prev : Candidate E R Φ N) (priorTopic : Option E) : Constraint (Candidate E R Φ N) :=
  Constraint.binary fun c ↦ ¬ ∃ t ∈ cb prev c, priorTopic = some t

/-- ALIGN: the topic is in subject position, for canonical sentences the preferred center
(p. 18); a candidate with no topic violates it. -/
def align (prev : Candidate E R Φ N) : Constraint (Candidate E R Φ N) :=
  Constraint.binary fun c ↦ ¬ ∃ t ∈ cb prev c, c.cp = some t

theorem cohere_none (prev c : Candidate E R Φ N) : cohere prev none c = 1 := by
  simp [cohere]

theorem cohere_of_cb_eq_none (priorTopic : Option E) (h : cb prev c = none) :
    cohere prev priorTopic c = 1 := by
  simp [cohere, h]

theorem align_of_cb_eq_none (h : cb prev c = none) : align prev c = 1 := by
  simp [align, h]

-- [strube-1998]
theorem align_eq_zero_iff : align prev c = 0 ↔ ∃ t ∈ cb prev c, c.cp = some t := by
  simp [align]

private theorem proTop_eq_one (h : ¬ ∃ x ∈ sentence c, x.2 ∈ pronouns) : proTop prev c = 1 := by
  have hn : ¬ ∃ t ∈ cb prev c, c.Pronominalizes pronouns t :=
    fun ⟨_, _, r, hr, _, hrp⟩ ↦ h ⟨_, List.mem_map_of_mem hr, hrp⟩
  rw [proTop, Constraint.binary_apply, ite_eq_left hn]

/-! ### BFP's transitions and table (19) -/

/-- BFP's transition into a candidate, from the prior topic, its backward-looking center and its
preferred center; `⊥` when it has no backward-looking center, which the transitions do not
classify. -/
def bfpTransition (prev : Candidate E R Φ N) (priorTopic : Option E) (c : Candidate E R Φ N) :
    WithBot ExtendedTransition :=
  match cb prev c with
  | some x => ExtendedTransition.ofCenters priorTopic x c.cp
  | none => ⊥

theorem bfpTransition_of_cb_eq_none (priorTopic : Option E) (h : cb prev c = none) :
    bfpTransition prev priorTopic c = ⊥ := by
  simp [bfpTransition, h]

theorem bfpTransition_of_cb_eq_some (priorTopic : Option E) (h : cb prev c = some x) :
    bfpTransition prev priorTopic c = ExtendedTransition.ofCenters priorTopic x c.cp := by
  simp [bfpTransition, h]

-- (19): with a prior topic, the transition is read off the COHERE and ALIGN verdicts
theorem bfpTransition_eq_ofTests {p : E} (h : cb prev c = some x) :
    bfpTransition prev (some p) c =
      ExtendedTransition.ofTests (cohere prev (some p) c = 0) (align prev c = 0) := by
  rw [bfpTransition_of_cb_eq_some _ h, WithBot.coe_inj]
  ext <;> simp [ExtendedTransition.ofCenters, cohere, align, h, eq_comm]

-- [walker-iida-cote-1994]: the first test passes when there is no prior center
theorem bfpTransition_none_eq_ofTests (h : cb prev c = some x) :
    bfpTransition prev none c = ExtendedTransition.ofTests True (align prev c = 0) := by
  rw [bfpTransition_of_cb_eq_some _ h, WithBot.coe_inj]
  ext <;> simp [ExtendedTransition.ofCenters, align, h]

end Order

/-! ### AGREE, FAM-DEF and the COT ranking (4) -/

variable [DecidableEq Φ]

instance (feat : E → Φ) (prev : Candidate E R Φ N) (r : Realization E R (Form Φ N)) :
    Decidable (Disagrees feat prev r) := by
  unfold Disagrees; split <;> infer_instance

/-- AGREE: anaphoric pronouns agree with their antecedents in gender. -/
def agree (feat : E → Φ) (prev : Candidate E R Φ N) : Constraint (Candidate E R Φ N) :=
  fun c ↦ c.realizations.countP fun r ↦ decide (Disagrees feat prev r)

private theorem agree_reassign {feat : E → Φ} {prev c : Candidate E R Φ N} {g : ℕ → E} {k : ℕ}
    (hgp : ∀ n, g n ∉ prev)
    (hk : ∀ i : Fin c.realizations.length, i.val = k → ¬ Disagrees feat prev c.realizations[i]) :
    agree feat prev (reassign c (keepOne c g k)) = 0 := by
  refine List.countP_eq_zero.2 fun r hr hd ↦ ?_
  replace hd := of_decide_eq_true hd
  obtain ⟨i, rfl⟩ := mem_reassign.1 hr
  by_cases hi : i.val = k
  · exact hk i hi (by simpa [keepOne, hi] using hd)
  · exact hgp i (by simpa [keepOne, hi] using hd.mem)

variable [DecidableEq N]

instance (ctx : List (Candidate E R Φ N)) (prev : Candidate E R Φ N)
    (r : Realization E R (Form Φ N)) : Decidable (Familiar ctx prev r) := by
  unfold Familiar; split <;> infer_instance

/-- FAM-DEF: each definite NP is familiar. -/
def famDef (ctx : List (Candidate E R Φ N)) (prev : Candidate E R Φ N) :
    Constraint (Candidate E R Φ N) :=
  fun c ↦ c.realizations.countP fun r ↦ decide (¬ Familiar ctx prev r)

theorem famDef_eq_zero_iff {ctx : List (Candidate E R Φ N)} {prev c : Candidate E R Φ N} :
    famDef ctx prev c = 0 ↔ ∀ r ∈ c.realizations, Familiar ctx prev r := by
  simp [famDef, List.countP_eq_zero]

variable [LinearOrder R]

/-- The COT ranking (4): AGREE > DISJOINT > PRO-TOP > FAM-DEF > COHERE > ALIGN. -/
def cotRanking (feat : E → Φ) (ctx : List (Candidate E R Φ N)) (prev : Candidate E R Φ N)
    (priorTopic : Option E) : List (Constraint (Candidate E R Φ N)) :=
  [agree feat prev, disjoint, proTop prev, famDef ctx prev, cohere prev priorTopic, align prev]

/-- The reranking of §4.1, PRO-TOP below FAM-DEF. -/
def cotRankingDemoted (feat : E → Φ) (ctx : List (Candidate E R Φ N)) (prev : Candidate E R Φ N)
    (priorTopic : Option E) : List (Constraint (Candidate E R Φ N)) :=
  [agree feat prev, disjoint, famDef ctx prev, proTop prev, cohere prev priorTopic, align prev]

/-- The violation profile of a candidate under the COT ranking (4). -/
def cotProfile (feat : E → Φ) (ctx : List (Candidate E R Φ N)) (prev : Candidate E R Φ N)
    (priorTopic : Option E) (c : Candidate E R Φ N) : ViolationProfile 6 :=
  toLex ((cotRanking feat ctx prev priorTopic).get · c)

private theorem toLex_lt_toLex_iff_six {a b : Fin 6 → ℕ} : toLex a < toLex b ↔
    a 0 < b 0 ∨ a 0 = b 0 ∧ (a 1 < b 1 ∨ a 1 = b 1 ∧ (a 2 < b 2 ∨ a 2 = b 2 ∧
      (a 3 < b 3 ∨ a 3 = b 3 ∧ (a 4 < b 4 ∨ a 4 = b 4 ∧ a 5 < b 5)))) := by
  have h0 (x y : Fin 0 → ℕ) : ¬ toLex x < toLex y := fun ⟨i, _⟩ ↦ i.elim0
  simp only [Pi.toLex_lt_toLex_iff_succ, h0, and_false, or_false]
  exact Iff.rfl

section Prediction

variable {feat : E → Φ} {ctx : List (Candidate E R Φ N)} {prev c d c₁ c₂ : Candidate E R Φ N}
  {priorTopic : Option E} {s : List (R × Form Φ N)}

theorem cotProfile_lt_iff :
    cotProfile feat ctx prev priorTopic c < cotProfile feat ctx prev priorTopic d ↔
      agree feat prev c < agree feat prev d ∨ agree feat prev c = agree feat prev d ∧
      (disjoint c < disjoint d ∨ disjoint c = disjoint d ∧
      (proTop prev c < proTop prev d ∨ proTop prev c = proTop prev d ∧
      (famDef ctx prev c < famDef ctx prev d ∨ famDef ctx prev c = famDef ctx prev d ∧
      (cohere prev priorTopic c < cohere prev priorTopic d ∨
        cohere prev priorTopic c = cohere prev priorTopic d ∧ align prev c < align prev d)))) :=
  toLex_lt_toLex_iff_six

/-! ### BFP's filters -/

/-- An interpretation survives the construction and filtering stages of BFP's algorithm: it is
fully anaphoric, its pronouns agree with their antecedents, its co-arguments are disjoint, and it
satisfies Rule 1. -/
structure Filtered (feat : E → Φ) (ctx : List (Candidate E R Φ N)) (prev c : Candidate E R Φ N) :
    Prop where
  agree_eq : agree feat prev c = 0
  disjoint_eq : disjoint c = 0
  famDef_eq : famDef ctx prev c = 0
  rule1 : PronominalizationConstraint pronouns prev c

-- p. 51: under Rule 1, PRO-TOP is met exactly when the sentence has a pronoun
private theorem proTop_eq (hf : famDef ctx prev c = 0)
    (h1 : PronominalizationConstraint pronouns prev c) :
    proTop prev c = if ∃ x ∈ sentence c, x.2 ∈ pronouns then 0 else 1 := by
  rw [proTop, Constraint.binary_apply]
  by_cases hp : ∃ x ∈ sentence c, x.2 ∈ pronouns
  · obtain ⟨_, hx, hxp⟩ := hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    have he : r.entity ∈ prev := by
      rcases r with ⟨e, ρ, φ | n | _⟩
      · exact famDef_eq_zero_iff.1 hf _ hr
      · exact absurd hxp (by simp [pronouns])
      · exact absurd hxp (by simp [pronouns])
    have hcf : r.entity ∈ prev.cf := prev.mem_cf.2 he
    obtain ⟨t, ht⟩ : ∃ t, cb prev c = some t :=
      Option.ne_none_iff_exists'.1 fun h ↦ cb_eq_none_iff.1 h _ hcf ⟨r, hr, rfl⟩
    have htop : ∃ t ∈ cb prev c, c.Pronominalizes pronouns t :=
      ⟨t, ht, h1 ⟨_, hcf, r, hr, rfl, hxp⟩ t ht⟩
    have hp : ∃ x ∈ sentence c, x.2 ∈ pronouns := ⟨_, hx, hxp⟩
    rw [ite_eq_right (not_not.2 htop), ite_eq_left hp]
  · rw [ite_eq_right hp]
    exact proTop_eq_one hp

-- in a discourse that includes the previous sentence, a fully anaphoric interpretation has no
-- topic exactly when its sentence has no definite
theorem cb_eq_none_iff_of_famDef (hprev : prev ∈ ctx) (hc : c ∈ interpretations ctx s)
    (hf : famDef ctx prev c = 0) : cb prev c = none ↔ ∀ x ∈ s, x.2 = .indefinite := by
  rw [cb_eq_none_iff, ← hc.1]
  constructor
  · rintro h _ hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    have hfam := famDef_eq_zero_iff.1 hf r hr
    rcases r with ⟨e, ρ, φ | n | _⟩
    · exact (h e (prev.mem_cf.2 hfam) ⟨_, hr, rfl⟩).elim
    · exact (h e (prev.mem_cf.2 hfam.1) ⟨_, hr, rfl⟩).elim
    · rfl
  · rintro h e he ⟨r, hr, rfl⟩
    exact hc.2 r hr (h _ (List.mem_map_of_mem hr)) prev hprev (prev.mem_cf.1 he)

/-! ### From BFP to COT -/

-- (19)
theorem cot_lt_iff_bfp_lt_of_tied (h0 : agree feat prev c₁ = agree feat prev c₂)
    (h1 : disjoint c₁ = disjoint c₂) (h2 : proTop prev c₁ = proTop prev c₂)
    (h3 : famDef ctx prev c₁ = famDef ctx prev c₂)
    (hcb : cb prev c₁ = none ↔ cb prev c₂ = none) :
    cotProfile feat ctx prev priorTopic c₁ < cotProfile feat ctx prev priorTopic c₂ ↔
      bfpTransition prev priorTopic c₂ < bfpTransition prev priorTopic c₁ := by
  simp only [cotProfile_lt_iff, h0, h1, h2, h3, lt_self_iff_false, false_or, true_and]
  have b1 : cohere prev priorTopic c₁ ≤ 1 := Constraint.binary_le_one _ _
  have b2 : cohere prev priorTopic c₂ ≤ 1 := Constraint.binary_le_one _ _
  have b3 : align prev c₁ ≤ 1 := Constraint.binary_le_one _ _
  have b4 : align prev c₂ ≤ 1 := Constraint.binary_le_one _ _
  rcases hx₁ : cb prev c₁ with _ | x₁ <;> rcases hx₂ : cb prev c₂ with _ | x₂
  · rw [bfpTransition_of_cb_eq_none _ hx₁, bfpTransition_of_cb_eq_none _ hx₂,
      cohere_of_cb_eq_none _ hx₁, cohere_of_cb_eq_none _ hx₂, align_of_cb_eq_none hx₁,
      align_of_cb_eq_none hx₂]
    simp
  · simp [hx₁, hx₂] at hcb
  · simp [hx₁, hx₂] at hcb
  rcases priorTopic with _ | p
  · rw [bfpTransition_none_eq_ofTests hx₁, bfpTransition_none_eq_ofTests hx₂, cohere_none,
      cohere_none, WithBot.coe_lt_coe]
    simp only [ExtendedTransition.lt_iff_toLex_lt, Prod.Lex.toLex_lt_toLex,
      ExtendedTransition.cohesion_ofTests, ExtendedTransition.salience_ofTests, Bool.lt_iff,
      decide_true, decide_eq_true_eq, decide_eq_false_iff_not, false_or, lt_self_iff_false,
      true_and]
    omega
  · rw [bfpTransition_eq_ofTests hx₁, bfpTransition_eq_ofTests hx₂, WithBot.coe_lt_coe]
    simp only [ExtendedTransition.lt_iff_toLex_lt, Prod.Lex.toLex_lt_toLex,
      ExtendedTransition.cohesion_ofTests, ExtendedTransition.salience_ofTests, Bool.lt_iff,
      decide_eq_true_eq, decide_eq_false_iff_not, decide_eq_decide]
    omega

/-- Proposition 3: between two fully anaphoric interpretations of a sentence that pass BFP's
filters, COT prefers one exactly when BFP ranks its transition higher, the pairwise
competitions of table (19). -/
theorem cot_lt_iff_bfp_lt (hprev : prev ∈ ctx) (hc₁ : c₁ ∈ interpretations ctx s)
    (hc₂ : c₂ ∈ interpretations ctx s) (h₁ : Filtered feat ctx prev c₁)
    (h₂ : Filtered feat ctx prev c₂) :
    cotProfile feat ctx prev priorTopic c₁ < cotProfile feat ctx prev priorTopic c₂ ↔
      bfpTransition prev priorTopic c₂ < bfpTransition prev priorTopic c₁ :=
  cot_lt_iff_bfp_lt_of_tied (h₁.agree_eq.trans h₂.agree_eq.symm)
    (h₁.disjoint_eq.trans h₂.disjoint_eq.symm)
    (by rw [proTop_eq h₁.famDef_eq h₁.rule1, proTop_eq h₂.famDef_eq h₂.rule1, hc₁.1, hc₂.1])
    (h₁.famDef_eq.trans h₂.famDef_eq.symm)
    (by rw [cb_eq_none_iff_of_famDef hprev hc₁ h₁.famDef_eq,
      cb_eq_none_iff_of_famDef hprev hc₂ h₂.famDef_eq])

-- Appendix A, Propositions 1 to 3, from BFP to COT
theorem cot_optimal_of_bfp (hprev : prev ∈ ctx) (hc : c ∈ interpretations ctx s)
    (hf : Filtered feat ctx prev c)
    (hb : ∀ d' ∈ interpretations ctx s, Filtered feat ctx prev d' → d' ≠ c →
      bfpTransition prev priorTopic d' < bfpTransition prev priorTopic c)
    (hd : d ∈ interpretations ctx s) (hdc : d ≠ c) :
    cotProfile feat ctx prev priorTopic c < cotProfile feat ctx prev priorTopic d := by
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
      exact hp (hs ▸ ⟨_, List.mem_map_of_mem hr, hrp⟩)
  by_cases htied : agree feat prev d = 0 ∧ disjoint d = 0 ∧ proTop prev d = proTop prev c ∧
      famDef ctx prev d = 0
  · obtain ⟨ha, hj, hp, hfd⟩ := htied
    have hfd' : Filtered feat ctx prev d := ⟨ha, hj, hfd, hpro.2 hp⟩
    exact (cot_lt_iff_bfp_lt hprev hc hd hf hfd').2 (hb d hd hfd' hdc)
  · have := hf.agree_eq
    have := hf.disjoint_eq
    have := hf.famDef_eq
    have := hpro.1
    rw [cotProfile_lt_iff]
    omega

/-! ### From COT to BFP -/

-- Appendix A, Propositions 1 and 2, from COT to BFP
theorem agree_disjoint_rule1_of_cot_optimal [Infinite E] (hc : c ∈ interpretations ctx s)
    (ho : ∀ d ∈ interpretations ctx s,
      ¬ cotProfile feat ctx prev priorTopic d < cotProfile feat ctx prev priorTopic c) :
    agree feat prev c = 0 ∧ disjoint c = 0 ∧ PronominalizationConstraint pronouns prev c := by
  let S : Finset E := ((c :: prev :: ctx).flatMap fun u ↦ u.realizations.map (·.entity)).toFinset
  have hS : ∀ u ∈ c :: prev :: ctx, ∀ e ∈ u, e ∈ S := fun u hu e ⟨r, hr, he⟩ ↦
    List.mem_toFinset.2 (List.mem_flatMap.2 ⟨u, hu, List.mem_map.2 ⟨r, hr, he⟩⟩)
  obtain ⟨g, hg, hgS⟩ := exists_fresh S
  have hgc : ∀ n, g n ∉ c := fun n hn ↦ hgS n (hS c (by simp) _ hn)
  have hgp : ∀ n, g n ∉ prev := fun n hn ↦ hgS n (hS prev (by simp) _ hn)
  have hmem (k : ℕ) : reassign c (keepOne c g k) ∈ interpretations ctx s :=
    reassign_mem_interpretations hc fun i hind u hu ↦ by
      by_cases hi : i.val = k
      · simpa [keepOne, hi] using hc.2 _ (List.getElem_mem _) hind u hu
      · simpa [keepOne, hi] using fun hn ↦ hgS i (hS u (by simp [hu]) _ hn)
  have hfresh : agree feat prev (reassign c (keepOne c g c.realizations.length)) = 0 :=
    agree_reassign hgp fun i hi ↦ absurd hi (Nat.ne_of_lt i.isLt)
  have hdj := disjoint_reassign (k := c.realizations.length) hg hgc
  have ha : agree feat prev c = 0 := by
    by_contra ha
    refine ho _ (hmem c.realizations.length) ?_
    rw [cotProfile_lt_iff]
    omega
  have hj : disjoint c = 0 := by
    by_contra hj
    refine ho _ (hmem c.realizations.length) ?_
    rw [cotProfile_lt_iff]
    omega
  refine ⟨ha, hj, fun ⟨e, he, r₀, hr₀, hre, hrp⟩ ↦ ?_⟩
  by_contra hnB
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hr₀
  have hed : e ∈ reassign c (keepOne c g k) :=
    ⟨_, mem_reassign.2 ⟨⟨k, hk⟩, rfl⟩, by simp [keepOne, hre]⟩
  obtain ⟨t, ht⟩ : ∃ t, cb prev (reassign c (keepOne c g k)) = some t :=
    Option.ne_none_iff_exists'.1 fun h ↦ cb_eq_none_iff.1 h e he hed
  have hpd : proTop prev (reassign c (keepOne c g k)) = 0 := by
    obtain ⟨r, hr, hrt⟩ := mem_of_cb ht
    obtain ⟨i, rfl⟩ := mem_reassign.1 hr
    have hi : i.val = k := by
      by_contra hi
      have hrt' : g i = t := by simpa [keepOne, hi] using hrt
      exact hgp i (hrt' ▸ prev.mem_cf.1 (cb_mem_cf ht))
    have hpron : (reassign c (keepOne c g k)).Pronominalizes pronouns t := ⟨_, hr, hrt, by
      obtain rfl : i = ⟨k, hk⟩ := Fin.ext hi
      exact hrp⟩
    rw [proTop, Constraint.binary_apply, ite_eq_right (not_not.2 ⟨t, ht, hpron⟩)]
  have hpc : proTop prev c = 1 := by
    have hn : ¬ ∃ t ∈ cb prev c, c.Pronominalizes pronouns t :=
      fun ⟨t, ht, hp⟩ ↦ hnB fun t' ht' ↦ Option.mem_unique ht ht' ▸ hp
    rw [proTop, Constraint.binary_apply, ite_eq_left hn]
  have hda : agree feat prev (reassign c (keepOne c g k)) = 0 := agree_reassign hgp
    fun i _ hdis ↦ List.countP_eq_zero.1 ha _ (List.getElem_mem _) (decide_eq_true hdis)
  have hdk := disjoint_reassign (k := k) hg hgc
  refine ho _ (hmem k) ?_
  rw [cotProfile_lt_iff]
  omega

theorem Filtered.of_cot_optimal [Infinite E] (hc : c ∈ interpretations ctx s)
    (hf : famDef ctx prev c = 0)
    (ho : ∀ d ∈ interpretations ctx s,
      ¬ cotProfile feat ctx prev priorTopic d < cotProfile feat ctx prev priorTopic c) :
    Filtered feat ctx prev c :=
  have h := agree_disjoint_rule1_of_cot_optimal hc ho
  ⟨h.1, h.2.1, hf, h.2.2⟩

/-- Proposition (20): for a sentence whose definites are proper names and pronouns, in a
discourse that includes the previous sentence and offers new referents without end (`Infinite E`),
COT predicts a unique interpretation that is fully anaphoric exactly when BFP's algorithm predicts
it uniquely, so that the two models then resolve the anaphors alike. -/
theorem cot_iff_bfp [Infinite E] (hprev : prev ∈ ctx) (hc : c ∈ interpretations ctx s) :
    (famDef ctx prev c = 0 ∧ ∀ d ∈ interpretations ctx s, d ≠ c →
        cotProfile feat ctx prev priorTopic c < cotProfile feat ctx prev priorTopic d) ↔
      Filtered feat ctx prev c ∧ ∀ d ∈ interpretations ctx s, Filtered feat ctx prev d → d ≠ c →
        bfpTransition prev priorTopic d < bfpTransition prev priorTopic c := by
  refine ⟨fun ⟨hf, ho⟩ ↦ ?_, fun ⟨hfc, hb⟩ ↦
    ⟨hfc.famDef_eq, fun _ hd hdc ↦ cot_optimal_of_bfp hprev hc hfc hb hd hdc⟩⟩
  have hfc : Filtered feat ctx prev c := Filtered.of_cot_optimal (priorTopic := priorTopic) hc hf
    fun d hd hlt ↦ by
      by_cases hdc : d = c
      · subst hdc
        exact lt_irrefl _ hlt
      · exact (ho d hd hdc).asymm hlt
  exact ⟨hfc, fun d hd hfd hdc ↦ (cot_lt_iff_bfp_lt hprev hc hd hfc hfd).1 (ho d hd hdc)⟩

end Prediction

/-! ### Examples (1), (12) and (2) -/

/-- The individuals of examples (1), (12) and (2), `mary₂` the second Mary of a reading of (2c),
and `other n` the further individuals a reading may introduce. -/
inductive Entity
  | jane | freda | mary | flowers | present | tennis | jim | mary₂
  | other (n : ℕ)
  deriving DecidableEq, Repr

instance : Infinite Entity := Infinite.of_injective Entity.other fun _ _ ↦ Entity.other.inj

/-- The proper names of the examples. -/
inductive Name
  | jane | freda | mary | jim
  deriving DecidableEq, Repr

/-- The gender of each individual. -/
def Entity.gender : Entity → UD.Gender
  | .jane | .freda | .mary | .mary₂ => .Fem
  | .jim => .Masc
  | .flowers | .present | .tennis | .other _ => .Neut

/-- An interpretation of a sentence of the examples. -/
abbrev Interpretation := Candidate Entity GrammaticalRole UD.Gender Name

namespace D1

/-- (1a) *Jane likes Mary* (`Examples.ex_1`). -/
def a : Interpretation := ⟨[⟨.jane, .subject, .name .jane⟩, ⟨.mary, .object, .name .mary⟩]⟩

/-- (1b) *She often brings her flowers*, she = Jane and her = Mary. -/
def b : Interpretation :=
  ⟨[⟨.jane, .subject, .pronoun .Fem⟩, ⟨.mary, .object, .pronoun .Fem⟩,
    ⟨.flowers, .other, .indefinite⟩]⟩

/-- (1c) *She chats with her for ages* with she = Jane and her = Mary. -/
def c_continue : Interpretation :=
  ⟨[⟨.jane, .subject, .pronoun .Fem⟩, ⟨.mary, .other, .pronoun .Fem⟩]⟩

/-- (1c) with she = Mary and her = Jane. -/
def c_retain : Interpretation :=
  ⟨[⟨.mary, .subject, .pronoun .Fem⟩, ⟨.jane, .other, .pronoun .Fem⟩]⟩

/-- The prior topic, from (1a) to (1b): Jane. -/
def priorTopic : Option Entity := cb a b

end D1

-- (1c)
theorem d1_filtered : Filtered Entity.gender [D1.a, D1.b] D1.b D1.c_continue ∧
    Filtered Entity.gender [D1.a, D1.b] D1.b D1.c_retain :=
  ⟨⟨by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩⟩

-- (1c), Table I
theorem d1_transitions :
    bfpTransition D1.b D1.priorTopic D1.c_continue = ExtendedTransition.continue ∧
      bfpTransition D1.b D1.priorTopic D1.c_retain = ExtendedTransition.retain := by
  decide

theorem d1_lex_picks_continue :
    cotProfile Entity.gender [D1.a, D1.b] D1.b D1.priorTopic D1.c_continue <
      cotProfile Entity.gender [D1.a, D1.b] D1.b D1.priorTopic D1.c_retain := by
  decide

private theorem d1_mem_interpretations {c : Interpretation}
    (hc : c = D1.c_continue ∨ c = D1.c_retain) :
    c ∈ interpretations [D1.a, D1.b] (sentence D1.c_continue) := by
  rcases hc with rfl | rfl <;> exact ⟨by decide, by decide⟩

-- (1c): the fully anaphoric readings that pass the filters are the two of Table I
private theorem d1_filtered_cases {d : Interpretation}
    (hd : d ∈ interpretations [D1.a, D1.b] (sentence D1.c_continue))
    (hf : Filtered Entity.gender [D1.a, D1.b] D1.b d) : d = D1.c_continue ∨ d = D1.c_retain := by
  obtain ⟨rs⟩ := d
  have hs := hd.1
  have hfam := famDef_eq_zero_iff.1 hf.famDef_eq
  rcases rs with _ | ⟨⟨e₁, ρ₁, f₁⟩, _ | ⟨⟨e₂, ρ₂, f₂⟩, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [sentence, D1.c_continue, List.map_cons, List.map_nil, List.cons.injEq,
      Prod.mk.injEq, reduceCtorEq, and_false, and_true] at hs
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hs
  obtain ⟨r₁, hr₁, rfl⟩ : e₁ ∈ D1.b := hfam ⟨e₁, .subject, .pronoun .Fem⟩ (by simp)
  obtain ⟨r₂, hr₂, rfl⟩ : e₂ ∈ D1.b := hfam ⟨e₂, .other, .pronoun .Fem⟩ (by simp)
  simp only [D1.b, List.mem_cons, List.not_mem_nil, or_false] at hr₁ hr₂
  rcases hr₁ with rfl | rfl | rfl <;> rcases hr₂ with rfl | rfl | rfl <;>
    first
    | decide
    | exact absurd hf.agree_eq (by decide)
    | exact absurd hf.disjoint_eq (by decide)

/-- Of all the interpretations of (1c), COT uniquely prefers she = Jane and her = Mary, BFP's
continue, since the two readings that pass BFP's filters are a continue and a retain
(Table I). -/
theorem d1_cot_optimal : ∀ d ∈ interpretations [D1.a, D1.b] (sentence D1.c_continue),
    d ≠ D1.c_continue → cotProfile Entity.gender [D1.a, D1.b] D1.b D1.priorTopic D1.c_continue <
      cotProfile Entity.gender [D1.a, D1.b] D1.b D1.priorTopic d :=
  ((cot_iff_bfp (by decide) (d1_mem_interpretations (.inl rfl))).2 ⟨d1_filtered.1,
    fun d hd hf hne ↦ by
      rcases d1_filtered_cases hd hf with rfl | rfl
      · exact absurd rfl hne
      · decide⟩).2

namespace D12

/-- (12a) *Jane is happy* (`Examples.ex_12`). -/
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

end D12

-- (13)
theorem d12_lex_picks_l_eq_i :
    cotProfile Entity.gender [D12.a, D12.b] D12.b D12.priorTopic D12.c_l_eq_i <
      cotProfile Entity.gender [D12.a, D12.b] D12.b D12.priorTopic D12.c_l_eq_j := by
  decide

-- (12c)
theorem d12_transition_retain :
    bfpTransition D12.b D12.priorTopic D12.c_l_eq_i = ExtendedTransition.retain := by decide

-- (13)
theorem d12_famDef : famDef [D12.a, D12.b] D12.b D12.c_l_eq_i = 1 ∧
    famDef [D12.a, D12.b] D12.b D12.c_l_eq_j = 1 := by decide

namespace D2

/-- (2a) *Mary likes tennis* (`Examples.ex_2`). -/
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

-- (2c): the topic, Mary, is named while *he* is a pronoun, so Rule 1 fails
theorem d2_bound_not_filtered : ¬ Filtered Entity.gender [D2.a, D2.b] D2.b D2.c_bound :=
  fun h ↦ absurd h.rule1 (by decide)

-- (2c): the second Mary is new to the discourse
theorem d2_two_marys_not_filtered : ¬ Filtered Entity.gender [D2.a, D2.b] D2.b D2.c_two_marys :=
  fun h ↦ absurd h.famDef_eq (by decide)

/-- Under the ranking (4) the two-Marys reading of (2c) beats the coreferential one (18), since
PRO-TOP outranks FAM-DEF; neither passes BFP's filters (`d2_bound_not_filtered`,
`d2_two_marys_not_filtered`). -/
theorem d2_canonical_picks_two_marys :
    cotProfile Entity.gender [D2.a, D2.b] D2.b D2.priorTopic D2.c_two_marys <
      cotProfile Entity.gender [D2.a, D2.b] D2.b D2.priorTopic D2.c_bound := by
  decide

/-- With PRO-TOP demoted below FAM-DEF (21) the coreferential reading of (2c) wins: introducing a
second Mary costs more than leaving the topic unpronominalized. -/
theorem d2_demoted_picks_bound :
    toLex ((cotRankingDemoted Entity.gender [D2.a, D2.b] D2.b D2.priorTopic).get · D2.c_bound) <
      toLex ((cotRankingDemoted Entity.gender [D2.a, D2.b] D2.b D2.priorTopic).get ·
        D2.c_two_marys) := by
  decide

end Beaver2004
