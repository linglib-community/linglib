module

public import Eval.Parser
public import Eval.Presupposition.Account
public import Studies.Chemla2009a

/-!
# Scoring theories on Chemla (2009)

Chemla's first experiment asks whether a sentence with a presupposition trigger in the scope of a
quantifier over ten students suggests the universal inference, that every one of them satisfies
the presupposition. The text reports the acceptance rates pooled over two groups of quantifiers,
*each* and *no* on one side and the numerical quantifiers on the other, and the comparison is
scored in four steps. The fact is the order of the two rates (`observed`). The parse of a sentence
that every theory shares is the quantified clause `(Q these students. trigger)` (`clause`). A theory
parses it into a clause of its own: the same clause, or the clause with the trigger's
presupposition accommodated in the scope, where it joins the assertion and the clause presupposes
nothing (`accommodateScope`). A theory that covers quantified clauses says which contexts accept
its parse (`Theory.acceptsClause`). The linking hypothesis, that subjects endorse the inferences a
theory predicts and endorse alike the inferences it predicts alike, turns the acceptance conditions
into a predicted order of the two rates (`predicted`).

The verdicts hold of every theory that accepts a clause only where symmetric Transparency does and
accepts every clause without a trigger: Schlenker's Transparency and local satisfaction, checked
incrementally or symmetrically, and any theory under development with these two properties. With
every presupposition accommodated in the context (`Accommodation.global`), such a theory predicts
the universal inference from all five quantifiers, and so no difference between the groups, and it
is wrong (`verdict_global_of`). Chemla's §4.1.2 considers an amendment: the universal presupposition
is not accommodated after the numerical quantifiers. A parser can stipulate this sentence by
sentence, at the cost of three stipulations (`Accommodation.stipulated`). The section and Appendix F
suggest a rule instead: keep the presupposition in the context where transparency derives it in one
step (`Accommodation.oneStep`). The rule parses every sentence as the stipulations do, without any
of them (`parse_oneStep`), so the two give every theory the same verdict (`verdict_stipulated_eq`),
and by the rule such a theory is right (`verdict_oneStep_of`).

A theory that accepts a clause wherever supervaluation defines it, the trigger being transparent at
its assertion, predicts the universal inference from none of the quantifiers. Where four students
satisfy both parts of the trigger and a fifth only its presupposition, every quantifier of the
experiment takes one value however the other students are resolved. So it predicts no difference
between the groups and is wrong wherever it accommodates (`verdict_of_transparentAt`), as
Schlenker's Strong Kleene and supervaluationist accounts are on either version
(`Schlenker2009.QuantifiedClause.strongKleeneAcceptable_trigger_iff`). A theory silent on quantified
clauses is silent here (`verdict_eq_silent`).

The experiment scores a theory together with where it accommodates the presupposition
(`experiment1`), since that is part of the theory, not of the fact. The registered accounts get
their verdicts from the general theorems (`verdict_experiment1`).

## Implementation notes

* A presupposition not accommodated in the context is accommodated in the scope, where the clause
  no longer presupposes it; §4.1.2 says only that it is weakened or not accommodated.
* In every model the linking hypothesis consults, the restrictor denotes the ten students at every
  world.
* The linking hypothesis reads a theory's inference off acceptance alone. A Strong Kleene sentence
  with *no* that is true as well as defined has every student satisfying the presupposition, an
  inference from the assertion together with the presupposition that the hypothesis does not
  consult.

## References

* [chemla-2009a]
* [schlenker-2009]
* [heim-1983]
-/

@[expose] public section

namespace Eval.Presupposition.Chemla2009a

open _root_.Presupposition Quantifier _root_.Chemla2009a

/-- The students of the domain. -/
abbrev Student := Fin domainSize

/-- The predicates of the experiment's sentences. -/
inductive Predicate where
  /-- Being one of the students. -/
  | student
  /-- The presupposition of the trigger. -/
  | presupposition
  /-- The assertion of the trigger. -/
  | assertion
  deriving DecidableEq

/-- The parse that every theory shares of the sentence with a determiner,
`(Q these students. trigger)`. -/
def clause (d : Determiner) : QuantifiedClause Predicate :=
  ⟨d.tree, .atom .student, .trigger .presupposition .assertion⟩

/-! ### Local accommodation -/

/-- The clause with the presuppositions of its scope locally accommodated in the scope
(`Presupposition.Formula.accommodate`). -/
def accommodateScope {Atom : Type*} (c : QuantifiedClause Atom) : QuantifiedClause Atom :=
  ⟨c.quantifier, c.restrictor, c.scope.accommodate⟩

/-! ### Linking hypothesis and verdicts -/

/-- The linking hypothesis for one sentence. An acceptance condition predicts the universal
inference from a clause when, in every model whose restrictor denotes the ten students at every
world, every context that accepts the clause entails that every student satisfies the
presupposition. -/
def PredictsUniversal (acc : ClauseAcceptance) (c : QuantifiedClause Predicate) : Prop :=
  ∀ (W : Type) (I : Predicate → Set (W × Student)), I .student = Set.univ →
    ∀ C : Set W, acc Predicate W Student I C c → ∀ w ∈ C, ∀ e, (w, e) ∈ I .presupposition

open Classical in
/-- The linking hypothesis for the comparison of the groups, as a rule. A theory predicts the same
rate for both groups when it predicts the universal inference from every sentence of both or from
none, a higher rate for the group from whose sentences alone it predicts it, and nothing
otherwise. -/
noncomputable def orderOf (predicts : Determiner → Prop) : Option Ordering :=
  let all g := ∀ d, (experiment1Groups d).group = g → predicts d
  let none' g := ∀ d, (experiment1Groups d).group = g → ¬ predicts d
  if all .eachOrNo ∧ all .numeral ∨ none' .eachOrNo ∧ none' .numeral then some .eq
  else if all .eachOrNo ∧ none' .numeral then some .gt
  else if none' .eachOrNo ∧ all .numeral then some .lt
  else none

open Classical in
/-- The order a theory predicts, by the linking hypothesis, from its parses of the sentences, if it
covers quantified clauses and parses every sentence. -/
noncomputable def predicted (T : Theory)
    (parse : Determiner → Option (QuantifiedClause Predicate)) : Option Ordering :=
  match T.acceptsClause with
  | none => none
  | some acc =>
    if h : ∀ d, (parse d).isSome then
      orderOf fun d ↦ PredictsUniversal acc ((parse d).get (h d))
    else none

/-- The order of the acceptance rates of the universal inference for *each* and *no* and for the
numerical quantifiers (§2.3.4). -/
def observed : Option Ordering :=
  match experiment1Universal.find? (·.group = .eachOrNo),
      experiment1Universal.find? (·.group = .numeral) with
  | some r, some r' => some (compare r.acceptance.toRat r'.acceptance.toRat)
  | _, _ => none

/-- A theory's parser of the experiment's sentences, from their shared parses to its own. -/
abbrev ClauseParser := Parser Determiner (QuantifiedClause Predicate) (QuantifiedClause Predicate)

/-- The verdict on a theory under a parser. -/
noncomputable def verdict (T : Theory) (π : ClauseParser) : Eval.Verdict :=
  .of (predicted T (π.parse clause)) observed

/-! ### Parsers -/

/-- Where a theory accommodates the presupposition of the trigger, which fixes how it parses the
experiment's sentences. -/
inductive Accommodation where
  /-- Every presupposition in the context. -/
  | global
  /-- §4.1.2: the universal presupposition is not accommodated after the numerical quantifiers,
  stipulated for each of their sentences. -/
  | stipulated
  /-- Appendix F: the presupposition of the scope is accommodated in the context where
  transparency derives it in one step, and in the scope otherwise. -/
  | oneStep
  deriving DecidableEq

open Classical in
/-- The parser of an accommodation. -/
noncomputable def Accommodation.parser : Accommodation → ClauseParser
  | .global => .ofRule some
  | .stipulated =>
    ⟨some, List.toFinmap
      [⟨.lessThan3, accommodateScope (clause .lessThan3)⟩,
       ⟨.moreThan3, accommodateScope (clause .moreThan3)⟩,
       ⟨.exactly3, accommodateScope (clause .exactly3)⟩]⟩
  | .oneStep => .ofRule fun c ↦ some (if OneStep c.quantifier then c else accommodateScope c)

/-- Appendix F's rule parses every sentence as §4.1.2's stipulations do, with none of them. -/
theorem parse_oneStep :
    Accommodation.oneStep.parser.parse clause = Accommodation.stipulated.parser.parse clause := by
  refine Parser.parse_ofRule_eq _ _ (fun d p h ↦ ?_) fun d hd ↦ ?_
  · cases d <;> simp_all [Accommodation.parser, clause, oneStep_tree_iff, experiment1Groups]
  · cases d <;> simp_all [Accommodation.parser, clause, Parser.stipulations, Finmap.mem_keys,
      Finmap.mem_list_toFinmap, oneStep_tree_iff, experiment1Groups]

/-- Accommodating every presupposition in the context stipulates no parse. -/
theorem stipulations_global : Accommodation.global.parser.stipulations = ∅ :=
  Parser.stipulations_ofRule _

/-- §4.1.2's parser stipulates the parses of the three numerical quantifiers' sentences. -/
theorem stipulations_stipulated :
    Accommodation.stipulated.parser.stipulations = {.lessThan3, .moreThan3, .exactly3} := by
  decide

/-- Appendix F's rule stipulates no parse. -/
theorem stipulations_oneStep : Accommodation.oneStep.parser.stipulations = ∅ :=
  Parser.stipulations_ofRule _

/-- Experiment 1 of [chemla-2009a]: whether the universal inference is endorsed more after *each*
and *no* than after the numerical quantifiers (§2.3.4), for a theory with where it accommodates the
presupposition. -/
noncomputable def experiment1 : Experiment (Theory × Accommodation) Unit Ordering where
  observed _ := observed
  predicted T _ := predicted T.1 (T.2.parser.parse clause)

theorem verdict_experiment1_eq (T : Theory) (p : Accommodation) :
    experiment1.verdict (T, p) () = verdict T p.parser :=
  rfl

/-! ### Predictions -/

private theorem ncard_students : (Set.univ : Set Student).ncard = 10 := by simp [domainSize]

/-- Every quantifier of the experiment varies on the row of ten. -/
private theorem not_constantOnRow (d : Determiner) : ¬ d.tree.ConstantOnRow 10 := by
  cases d <;> intro h
  · have := h 10 0 0 10 rfl rfl; simp [Determiner.tree, NumberTree.all] at this
  · have := h 10 0 0 10 rfl rfl; simp [Determiner.tree, NumberTree.no] at this
  · have := h 10 0 0 10 rfl rfl; simp [Determiner.tree, NumberTree.cardinal] at this
  · have := h 10 0 0 10 rfl rfl; simp [Determiner.tree, NumberTree.cardinal] at this
  · have := h 10 0 7 3 rfl rfl; simp [Determiner.tree, NumberTree.cardinal] at this

variable {T : Theory} {acc : ClauseAcceptance}

/-- An acceptance condition within symmetric Transparency predicts the universal inference from
every quantifier of the experiment. -/
private theorem predictsUniversal_clause
    (hT : ∀ Atom W E I C c, acc Atom W E I C c →
      Schlenker2009.Transparency .symmetric C (QuantifiedClause.occurrences I c))
    (d : Determiner) : PredictsUniversal acc (clause d) := fun W I hI C hC w hw e ↦ by
  have h := (Schlenker2009.QuantifiedClause.transparency_symmetric_trigger_iff I rfl).1
    (hT _ _ _ _ _ _ hC) w hw
  simp only [Formula.truth, hI, Set.mem_univ, Set.ofPred_true, ncard_students, forall_const] at h
  exact h (not_constantOnRow d) e

/-- An acceptance condition that accepts every clause without a trigger predicts nothing from a
clause with its presupposition accommodated in the scope. -/
private theorem not_predictsUniversal_accommodateScope
    (hU : ∀ Atom W E I C (c : QuantifiedClause Atom), c.triggers = [] → acc Atom W E I C c)
    (d : Determiner) : ¬ PredictsUniversal acc (accommodateScope (clause d)) := fun h ↦ by
  let I : Predicate → Set (Unit × Student) := fun | .student => Set.univ | _ => ∅
  exact h Unit I rfl Set.univ (hU _ _ _ _ _ _ (by simp [QuantifiedClause.triggers,
    accommodateScope, clause, Formula.triggers])) () trivial ⟨0, by decide⟩

/-- A model in which four students satisfy the presupposition and the assertion, the fifth only
the presupposition, and the other five neither. -/
private def countermodel : Predicate → Set (Unit × Student)
  | .student => Set.univ
  | .presupposition => {x | x.2.val < 5}
  | .assertion => {x | x.2.val < 4}

/-- In the countermodel every scope that resolves the trigger holds of at least the four students
that satisfy both parts and fails of the fifth, which fixes the value of every quantifier of the
experiment. -/
private theorem toDet_countermodel {D : Set Student}
    (hD : ∀ e : Student, e.val < 5 → (e ∈ D ↔ e.val < 4)) (d : Determiner) :
    d.tree.toDet Set.univ D ↔ d = .moreThan3 := by
  have h4 : 4 ≤ (Set.univ ∩ D).ncard := by
    have : {x : Student | x.val < 4}.ncard = 4 := by
      rw [Set.ncard_eq_toFinset_card']; decide
    exact this ▸ Set.ncard_le_ncard (fun x (hx : x.val < 4) ↦ ⟨trivial, (hD x (by omega)).2 hx⟩)
      (Set.toFinite _)
  have h1 : 1 ≤ (Set.univ \ D).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨⟨4, by decide⟩, trivial, fun h ↦
      absurd ((hD ⟨4, by decide⟩ (by decide)).1 h) (by decide)⟩
  rw [NumberTree.toDet_apply]
  cases d <;> simp only [Determiner.tree, NumberTree.all, NumberTree.no, NumberTree.cardinal_apply,
    Set.mem_ofPred_eq, Set.mem_singleton_iff, reduceCtorEq, iff_false, iff_true] <;> omega

/-- An acceptance condition that accepts a clause whose scope is a trigger wherever the trigger is
transparent at its assertion predicts the universal inference from no quantifier of the
experiment. -/
private theorem not_predictsUniversal_clause
    (hK : ∀ Atom W E I C q (R : Formula Atom) (p a : Atom), R.triggers = [] →
      TransparentAt C {scopeTruth q fun w e ↦ (w, e) ∈ R.truth I} (I p) (I a) →
        acc Atom W E I C ⟨q, R, .trigger p a⟩)
    (d : Determiner) : ¬ PredictsUniversal acc (clause d) := fun h ↦ by
  refine absurd (h Unit countermodel rfl Set.univ (hK _ _ _ _ _ _ _ _ _ rfl ?_) () trivial
    ⟨9, by decide⟩) (by simp [countermodel])
  refine transparentAt_scopeTruth_iff.2 fun _ _ D D' hD hD' ↦ ?_
  have hA : (fun e ↦ ((), e) ∈ (Formula.atom Predicate.student).truth countermodel) =
      (Set.univ : Set Student) := funext fun _ ↦ eq_true (Set.mem_univ _)
  rw [hA, toDet_countermodel (fun e he ↦ hD e he) d, toDet_countermodel (fun e he ↦ hD' e he) d]

private theorem predicted_of_parse (hacc : T.acceptsClause = some acc)
    (p : Determiner → QuantifiedClause Predicate) :
    predicted T (fun d ↦ some (p d)) = orderOf fun d ↦ PredictsUniversal acc (p d) := by
  unfold predicted
  rw [hacc]
  simp

private theorem orderOf_of_forall_not {predicts : Determiner → Prop} (h : ∀ d, ¬ predicts d) :
    orderOf predicts = some .eq := by
  unfold orderOf
  rw [ite_eq_left (.inr ⟨fun d _ ↦ h d, fun d _ ↦ h d⟩)]

private theorem observed_eq : observed = some .gt := by decide +kernel

/-- By §2.3.4, the universal inference is endorsed more after *each* and *no* than after the
numerical quantifiers. -/
theorem observed_experiment1 : experiment1.observed () = some .gt := observed_eq

private theorem parse_global :
    Accommodation.global.parser.parse clause = fun d ↦ some (clause d) := by
  funext d; simp [Accommodation.parser]

private theorem parse_oneStep_eq : Accommodation.oneStep.parser.parse clause = fun d ↦
    some (if (experiment1Groups d).group = .eachOrNo then clause d
      else accommodateScope (clause d)) := by
  funext d; simp [Accommodation.parser, clause, oneStep_tree_iff]

/-- With every presupposition accommodated in the context, a theory within symmetric Transparency
predicts no difference between the groups and is wrong. -/
theorem verdict_global_of (hacc : T.acceptsClause = some acc)
    (hT : ∀ Atom W E I C c, acc Atom W E I C c →
      Schlenker2009.Transparency .symmetric C (QuantifiedClause.occurrences I c)) :
    verdict T Accommodation.global.parser = .wrong := by
  rw [verdict, parse_global, predicted_of_parse hacc, observed_eq]
  unfold orderOf
  rw [ite_eq_left (.inl ⟨fun d _ ↦ predictsUniversal_clause hT d,
    fun d _ ↦ predictsUniversal_clause hT d⟩)]
  rfl

/-- By Appendix F's rule, a theory within symmetric Transparency that accepts every clause without a
trigger predicts the universal inference from *each* and *no* alone and is right. -/
theorem verdict_oneStep_of (hacc : T.acceptsClause = some acc)
    (hT : ∀ Atom W E I C c, acc Atom W E I C c →
      Schlenker2009.Transparency .symmetric C (QuantifiedClause.occurrences I c))
    (hU : ∀ Atom W E I C (c : QuantifiedClause Atom), c.triggers = [] → acc Atom W E I C c) :
    verdict T Accommodation.oneStep.parser = .correct := by
  rw [verdict, parse_oneStep_eq, predicted_of_parse hacc, observed_eq]
  have he := predictsUniversal_clause hT
  have hn := not_predictsUniversal_accommodateScope hU
  unfold orderOf
  rw [ite_eq_right, ite_eq_left]
  · rfl
  · refine ⟨fun d hd ↦ ?_, fun d hd ↦ ?_⟩
    · beta_reduce; rw [ite_eq_left hd]; exact he d
    · beta_reduce; rw [ite_eq_right (by rw [hd]; decide)]; exact hn d
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact hn .lessThan3 (by simpa [experiment1Groups] using h .lessThan3 rfl)
    · exact h .each rfl (by simpa [experiment1Groups] using he .each)

/-- A theory silent on quantified clauses is silent on the experiment. -/
theorem verdict_eq_silent (h : T.acceptsClause = none) (π : ClauseParser) :
    verdict T π = .silent := by
  rw [verdict, predicted, h]
  rfl

/-- §4.1.2's stipulations give every theory the verdict that Appendix F's rule gives it. -/
theorem verdict_stipulated_eq (T : Theory) :
    verdict T Accommodation.stipulated.parser = verdict T Accommodation.oneStep.parser := by
  rw [verdict, verdict, parse_oneStep]

/-- A theory that accepts a clause whose scope is a trigger wherever the trigger is transparent at
its assertion, so wherever supervaluation defines the clause, and accepts every clause without a
trigger, predicts the universal inference from no quantifier of the experiment, so no difference
between the groups, and is wrong wherever it accommodates the presupposition. -/
theorem verdict_of_transparentAt (hacc : T.acceptsClause = some acc)
    (hK : ∀ Atom W E I C q (R : Formula Atom) (p a : Atom), R.triggers = [] →
      TransparentAt C {scopeTruth q fun w e ↦ (w, e) ∈ R.truth I} (I p) (I a) →
        acc Atom W E I C ⟨q, R, .trigger p a⟩)
    (hU : ∀ Atom W E I C (c : QuantifiedClause Atom), c.triggers = [] → acc Atom W E I C c)
    (π : Accommodation) : verdict T π.parser = .wrong := by
  have hn := not_predictsUniversal_clause hK
  have ha := not_predictsUniversal_accommodateScope hU
  have hone : verdict T Accommodation.oneStep.parser = .wrong := by
    rw [verdict, parse_oneStep_eq, predicted_of_parse hacc, observed_eq,
      orderOf_of_forall_not fun d ↦ ?_]
    · rfl
    · split_ifs
      exacts [hn d, ha d]
  cases π
  · rw [verdict, parse_global, predicted_of_parse hacc, observed_eq, orderOf_of_forall_not hn]
    rfl
  · exact (verdict_stipulated_eq _).trans hone
  · exact hone

/-! ### The registered accounts -/

open Schlenker2009.QuantifiedClause

/-- An account within symmetric Transparency is wrong with every presupposition accommodated in
the context and right by §4.1.2's stipulations or Appendix F's rule. -/
private theorem verdict_of_transparency {a : Account} (h : a.AcceptsClause = some acc)
    (hT : ∀ Atom W E I C c, acc Atom W E I C c →
      Schlenker2009.Transparency .symmetric C (QuantifiedClause.occurrences I c))
    (hU : ∀ Atom W E I C (c : QuantifiedClause Atom), c.triggers = [] → acc Atom W E I C c)
    (π : Accommodation) :
    verdict a.theory π.parser = if π = .global then .wrong else .correct := by
  cases π
  · exact verdict_global_of h hT
  · exact (verdict_stipulated_eq _).trans (verdict_oneStep_of h hT hU)
  · exact verdict_oneStep_of h hT hU

/-- On Experiment 1, Schlenker's Transparency and local satisfaction are wrong with every
presupposition accommodated in the context and right by §4.1.2's stipulations or Appendix F's rule,
on either version. The Strong Kleene and supervaluationist accounts are wrong wherever they
accommodate, and dynamic semantics, filtering and Limited Symmetry are silent. -/
theorem verdict_experiment1 (a : Account) (π : Accommodation) :
    experiment1.verdict (a.theory, π) () = match a with
      | .transparencyIncremental | .transparencySymmetric | .satisfactionIncremental
      | .satisfactionSymmetric => if π = .global then .wrong else .correct
      | .kleeneIncremental | .kleeneSymmetric | .supervaluationIncremental
      | .supervaluationSymmetric => .wrong
      | .dynamic | .filtering | .limitedSymmetry => .silent := by
  rw [verdict_experiment1_eq]
  have hU {r : Schlenker2009.Version} {Atom W E : Type} {I : Atom → Set (W × E)} {C : Set W}
      {c : QuantifiedClause Atom} (hc : c.triggers = []) :
      Schlenker2009.Transparency r C (QuantifiedClause.occurrences I c) ∧
        Schlenker2009.Satisfaction r C (QuantifiedClause.occurrences I c) :=
    ⟨fun _ ho ↦ by simp [QuantifiedClause.occurrences, hc] at ho,
      fun _ ho ↦ by simp [QuantifiedClause.occurrences, hc] at ho⟩
  cases a
  · exact verdict_eq_silent rfl _
  · exact verdict_eq_silent rfl _
  · exact verdict_of_transparency rfl (fun _ _ _ _ _ _ h ↦ h.symmetric)
      (fun _ _ _ _ _ _ hc ↦ (hU hc).1) π
  · exact verdict_of_transparency rfl (fun _ _ _ _ _ _ h ↦ h) (fun _ _ _ _ _ _ hc ↦ (hU hc).1) π
  · exact verdict_of_transparency rfl (fun _ _ _ _ _ _ h ↦ h.transparency.symmetric)
      (fun _ _ _ _ _ _ hc ↦ (hU hc).2) π
  · exact verdict_of_transparency rfl (fun _ _ _ _ _ _ h ↦ h.transparency)
      (fun _ _ _ _ _ _ hc ↦ (hU hc).2) π
  · exact verdict_of_transparentAt rfl
      (fun _ _ _ I _ _ _ _ _ hR h ↦ (strongKleeneAcceptable_trigger_iff I hR _).2 h)
      (fun _ _ _ I _ _ hc ↦ strongKleeneAcceptable_of_triggers_eq_nil I _ hc) π
  · exact verdict_of_transparentAt rfl
      (fun _ _ _ I _ _ _ _ _ hR h ↦ (strongKleeneAcceptable_trigger_iff I hR _).2 h)
      (fun _ _ _ I _ _ hc ↦ strongKleeneAcceptable_of_triggers_eq_nil I _ hc) π
  · exact verdict_of_transparentAt rfl
      (fun _ _ _ I _ _ _ _ _ hR h ↦ (supervaluationAcceptable_trigger_iff I hR _).2 h)
      (fun _ _ _ I _ _ hc ↦ supervaluationAcceptable_of_triggers_eq_nil I _ hc) π
  · exact verdict_of_transparentAt rfl
      (fun _ _ _ I _ _ _ _ _ hR h ↦ (supervaluationAcceptable_trigger_iff I hR _).2 h)
      (fun _ _ _ I _ _ hc ↦ supervaluationAcceptable_of_triggers_eq_nil I _ hc) π
  · exact verdict_eq_silent rfl _

end Eval.Presupposition.Chemla2009a
