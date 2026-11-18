module

public import Linglib.Semantics.PolarityItem.LicensingContext
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Fragments.English.PolarityItems
public import Linglib.Data.Examples.Ladusaw1979
public import Linglib.Data.Examples.Readers

/-!
# Ladusaw (1979): Polarity Sensitivity as Inherent Scope Relations

*Some* and *any* mean the same and differ in the scope they tolerate, so that [*John didn't talk to
some students* has only the wide reading of its object and *John didn't talk to any students* only
the narrow one](##some_any_complementary). The Inherent Scope Convention makes this compositional.
A meaning inherits a mark from a polarity item; a trigger removes the mark of a negative polarity
item [for good](##not_isN_scope), and no meaning so marked reaches the root; a clause boundary
removes the mark of a positive polarity item, and no meaning so marked becomes the scope of a
negation. A trigger is a downward-entailing expression, the condition [the library's licensing
theory agrees with](##licenses_iff_isDownwardEntailing), whereas [only some triggers block positive
polarity items](##exists_trigger_not_negation), the overt negations. The convention [gives the
paper's judgments](##rows_predicted), but for *few* in its restrictor, which the paper itself
concedes.

## Implementation notes

* A reading is an `Interp`, the scope relations the convention looks at. The composition rules and
  NP storage of the paper's fragment are not formalized: a row records what they deliver, the
  expressions over its polarity item, whether a trigger follows the item, and whether a clause
  boundary intervenes. Its readings are the one with the item in scope and, for an NP, the one that
  stores the item above the expressions.
* Expressions denote the library's licensers. *Never* reads as *no* over times, *rarely*, *seldom*
  and *hardly* as *few*, which the paper takes them to parallel, and *fail* as negation over an
  infinitive, its assertion. *Upward* stands for the expressions the paper's entailment tests find
  upward entailing, whose meanings it does not give.
* *Only* denotes its assertion, as in the paper, with the implicature left out. The library's
  `LicensingContext.onlyFocus` is von Fintel's, downward entailing modulo that presupposition.
* Ladusaw reads a conditional antecedent as the antecedent of a material conditional, which is
  downward entailing (`materialAntecedent`); the library's `LicensingContext.conditionalAntecedent`
  is von Fintel's counterfactual, downward entailing only modulo its presupposition.
* The library's licensing condition asks in addition that the operator not be upward entailing,
  which a constant operator is, though the definition of downward entailment counts it as downward
  entailing; the biconditional is stated for the operators that are not. The anti-additive licensers
  and the strong polarity items postdate the dissertation.
* The denial negation of chapter VII and the pragmatics of questions of chapter VIII are not
  formalized, nor are the attitude verbs *surprised* and *amazed*, for which the paper appeals to
  intuitions of likelihood rather than entailment. The rows that are denials are marked, and
  [the convention filters their plain reading](##rows_denial_filtered).

## References

* [ladusaw-1979]
-/

@[expose] public section

namespace Ladusaw1979

open PolarityItem NaturalLogic Quantifier Quantifier.Det LicensingContext Licenser

/-! ### Downward entailment -/

/-- An environment is downward entailing when every operator it places over the item reverses
entailment, the inclusion of its arguments. -/
def IsDownwardEntailing (L : Licenser) : Prop := L.Holds .anti

/-- An environment is upward entailing when every operator it places over the item preserves
entailment. -/
def IsUpwardEntailing (L : Licenser) : Prop := L.Holds .mono

-- (37), p. 145
theorem isDownwardEntailing_classical_iff {F : OperatorFamily} :
    IsDownwardEntailing (.classical F) ↔ ∀ p, Antitone (F.op p) :=
  forall_congr' fun _ ↦ ProjectivitySignature.holdsFor_anti_iff

-- (39), p. 146
theorem isUpwardEntailing_classical_iff {F : OperatorFamily} :
    IsUpwardEntailing (.classical F) ↔ ∀ p, Monotone (F.op p) :=
  forall_congr' fun _ ↦ ProjectivitySignature.holdsFor_mono_iff

/-- The other clause of a conditional, over worlds. -/
structure OtherClause where
  /-- The worlds. -/
  W : Type
  /-- The clause. -/
  q : Set W

/-- The antecedent of a material conditional, Ladusaw's reading of conditional antecedents. -/
def materialAntecedent : Licenser :=
  .classical ⟨OtherClause, fun p ↦ Set p.W, fun p ↦ Set p.W, fun p P ↦ Pᶜ ∪ p.q⟩

/-- The consequent of a material conditional. -/
def materialConsequent : Licenser :=
  .classical ⟨OtherClause, fun p ↦ Set p.W, fun p ↦ Set p.W, fun p P ↦ p.qᶜ ∪ P⟩

-- (128), p. 167
theorem isDownwardEntailing_materialAntecedent : IsDownwardEntailing materialAntecedent :=
  fun _ ↦ ProjectivitySignature.holdsFor_anti_iff.mpr fun _ _ h ↦ Set.union_subset_union_left _
    (Set.compl_subset_compl.mpr h)

-- (129), p. 167
theorem isUpwardEntailing_materialConsequent : IsUpwardEntailing materialConsequent :=
  isUpwardEntailing_classical_iff.2 fun _ _ _ h ↦ Set.union_subset_union_right _ h

/-- The environments of §4 that the library's licensing contexts cover: *not* (38), *no* NP (46a),
*without* (104), the restrictor of *every* (47b), *few* NP (61), *at most n* NP (52a), the
antecedent of a conditional (128), *before* (123) and *too* ADJ *to* (99), with the comparative,
which is on the list of triggers on p. 133 but which §4 does not test. -/
noncomputable def environments : List Licenser :=
  [negation.licenser, nobody.licenser, withoutClause.licenser, universalRestrictor.licenser,
    few.licenser, atMost.licenser, materialAntecedent, beforeClause.licenser, tooTo.licenser,
    clausalComparative.licenser]

theorem isDownwardEntailing_of_mem_environments : ∀ c ∈ environments, IsDownwardEntailing c := by
  simp only [environments, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨holds_negation .weak, (holds_nobody_iff (s := .weak)).2 (by decide),
    (holds_withoutClause_iff (s := .weak)).2 (by decide),
    (holds_universalRestrictor_iff (s := .weak)).2 (by decide), holds_few_iff.2 le_rfl,
    holds_atMost_iff.2 le_rfl, isDownwardEntailing_materialAntecedent,
    (holds_beforeClause_iff (s := .weak)).2 (by decide),
    (holds_tooTo_iff (s := .weak)).2 (by decide),
    (holds_clausalComparative_iff (s := .weak)).2 (by decide)⟩

-- by construction: `Licenser.Holds` is `False` at the question licenser, which licenses by
-- relevance rather than by entailment
theorem not_isDownwardEntailing_question : ¬ IsDownwardEntailing question.licenser := id

theorem licenses_of_isDownwardEntailing {L : Licenser} {e : PolarityItem}
    (hc : IsDownwardEntailing L) (hn : ¬ L.IsStrawsonUE) (he : e.licensor = some .weak) :
    L.Licenses e :=
  .inl ⟨.weak, he, isStrawsonDE_of_holds_anti hc, hn⟩

theorem isDownwardEntailing_of_licenses {F : OperatorFamily} {e : PolarityItem}
    (h : (Licenser.classical F).Licenses e) : IsDownwardEntailing (.classical F) := by
  obtain ⟨_, -, hr⟩ | ⟨⟨⟩, -⟩ | ⟨⟨⟩, -⟩ := h
  exact isDownwardEntailing_classical_iff.mpr hr.weak.1

/-- A construction whose operators are functions between lattices, and not all upward entailing,
licenses the weak negative polarity items exactly when it is downward entailing, (40), p. 147. -/
theorem licenses_iff_isDownwardEntailing {F : OperatorFamily} {e : PolarityItem}
    (he : e.licensor = some .weak) (hn : ¬ (Licenser.classical F).IsStrawsonUE) :
    (Licenser.classical F).Licenses e ↔ IsDownwardEntailing (.classical F) :=
  ⟨isDownwardEntailing_of_licenses, fun h ↦ licenses_of_isDownwardEntailing h hn he⟩

-- negation licenses the weak item *ever*, being downward and not upward entailing
example : negation.licenser.Licenses English.PolarityItems.ever :=
  (licenses_iff_isDownwardEntailing rfl not_isStrawsonUE_negation).2 (holds_negation .weak)

/-- A constant operator into truth values. -/
abbrev constFamily : OperatorFamily := ⟨PUnit, fun _ ↦ Prop, fun _ ↦ Prop, fun _ _ ↦ True⟩

-- a constant operator is downward entailing, as Ladusaw's condition counts it, but it licenses
-- nothing, being upward entailing as well
example : IsDownwardEntailing (.classical constFamily) ∧
    ¬ (Licenser.classical constFamily).Licenses English.PolarityItems.ever := by
  refine ⟨isDownwardEntailing_classical_iff.2 fun _ _ _ _ ↦ le_rfl, fun h ↦ ?_⟩
  obtain ⟨_, -, hr⟩ | ⟨⟨⟩, -⟩ | ⟨⟨⟩, -⟩ := h
  exact hr.weak.2 fun _ _ _ _ ↦ le_rfl

/-! ### The theorem about modifiers -/

-- (63), p. 154
theorem not_forall_monotone_of_le :
    ¬ ∀ δ : Set Bool → Set Bool, (∀ a, δ a ⊆ a) → Monotone δ := by
  classical
  intro h
  let δ : Set Bool → Set Bool := fun a ↦ if a = Set.univ then ∅ else a
  have hne : ({true} : Set Bool) ≠ Set.univ := fun e ↦ by
    have : false ∈ ({true} : Set Bool) := e ▸ Set.mem_univ false
    simp at this
  have hle : ∀ a, δ a ⊆ a := fun a ↦ by
    by_cases ha : a = Set.univ
    · simp only [δ, ha, ↓reduceIte, Set.empty_subset]
    · simp only [δ, ha, ↓reduceIte, Set.Subset.refl]
  have hmem : true ∈ δ {true} := by simp only [δ, hne, ↓reduceIte, Set.mem_singleton_iff]
  have huniv := h δ hle (Set.subset_univ ({true} : Set Bool)) hmem
  simp only [δ, ↓reduceIte, Set.mem_empty_iff_false] at huniv

-- An intersective modifier is upward entailing, which covers the identity meanings of *still*,
-- *yet*, *anymore* and *already* in the fragment, p. 130.
example {W : Type*} (c : Set W) : Monotone (· ∩ c) := fun _ _ h ↦ Set.inter_subset_inter_left c h

/-! ### Determiners and quantifier NPs -/

section Determiners

variable {α : Type*}

-- (51), p. 151, boxes I, II and III, and the scopes of IV and V
theorem determiner_boxes [Finite α] (n : ℕ) :
    ((Det.some : Det α).RestrictorMonotone ∧ (Det.some : Det α).ScopeMonotone ∧
      (atLeast n : Det α).RestrictorMonotone ∧ (atLeast n : Det α).ScopeMonotone) ∧
    ((every : Det α).RestrictorAntitone ∧ (every : Det α).ScopeMonotone) ∧
    ((no : Det α).RestrictorAntitone ∧ (no : Det α).ScopeAntitone ∧
      (atMost n : Det α).RestrictorAntitone ∧ (atMost n : Det α).ScopeAntitone) ∧
    (most : Det α).ScopeMonotone ∧ (few : Det α).ScopeAntitone :=
  ⟨⟨restrictorMonotone_some, scopeMonotone_some, restrictorMonotone_atLeast n,
      scopeMonotone_atLeast n⟩,
    ⟨restrictorAntitone_every, scopeMonotone_every⟩,
    ⟨restrictorAntitone_no, scopeAntitone_no, restrictorAntitone_atMost n, scopeAntitone_atMost n⟩,
    scopeMonotone_most, scopeAntitone_few⟩

-- (55), p. 152: *few men are fathers* does not entail *few fathers are fathers*.
theorem not_restrictorAntitone_few : ¬ (few : Det (Fin 3)).RestrictorAntitone := fun h ↦ by
  have : few Set.univ {x : Fin 3 | x = 0} → few {x : Fin 3 | x = 0} {x | x = 0} :=
    h _ (Set.subset_univ _)
  revert this; decide

-- (54), p. 152: *few fathers walk* does not entail *few men walk*.
theorem not_restrictorMonotone_few : ¬ (few : Det (Fin 3)).RestrictorMonotone := fun h ↦ by
  have : few {x : Fin 3 | x = 0} {x | x ≠ 0} → few Set.univ {x : Fin 3 | x ≠ 0} :=
    h _ (Set.subset_univ _)
  revert this; decide

-- (51), box VI
theorem exactly_neither :
    ¬ (exactly 1 : Det (Fin 2)).RestrictorMonotone ∧
      ¬ (exactly 1 : Det (Fin 2)).RestrictorAntitone ∧
      ¬ (exactly 1 : Det (Fin 2)).ScopeMonotone ∧ ¬ (exactly 1 : Det (Fin 2)).ScopeAntitone := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · have : exactly 1 {x : Fin 2 | x = 0} Set.univ →
        exactly 1 (Set.univ : Set (Fin 2)) Set.univ := h _ (Set.subset_univ _)
    revert this; decide
  · have : exactly 1 (Set.univ : Set (Fin 2)) {x | x = 0} →
        exactly 1 {x : Fin 2 | x = 1} {x | x = 0} := h _ (Set.subset_univ _)
    revert this; decide
  · have : exactly 1 Set.univ {x : Fin 2 | x = 0} →
        exactly 1 (Set.univ : Set (Fin 2)) Set.univ := h _ (Set.subset_univ _)
    revert this; decide
  · have : exactly 1 {x : Fin 2 | x = 0} Set.univ →
        exactly 1 {x : Fin 2 | x = 0} {x | x ≠ x} := h _ (Set.subset_univ _)
    revert this; decide

end Determiners

/-! ### Expressions -/

/-- The determiners of the paper's sentences. -/
inductive Determiner where
  | someDet | everyDet | noDet | atLeastThree | atMostThree | mostDet | fewDet
  deriving DecidableEq

/-- The denotation of a determiner. -/
noncomputable def Determiner.denote {α : Type} : Determiner → Det α
  | .someDet => Det.some
  | .everyDet => every
  | .noDet => no
  | .atLeastThree => atLeast 3
  | .atMostThree => atMost 3
  | .mostDet => most
  | .fewDet => few

/-- The expressions that take a polarity item in their scope in the paper's sentences. A determiner
has its NOM as its scope and the quantifier NP it forms has its VP (p. 148). -/
inductive Expression where
  | not
  | det (d : Determiner)
  | qnp (d : Determiner)
  | without
  | before
  | tooTo
  | doubt
  | antecedent
  | onlyNP
  | «only»
  | upward
  deriving DecidableEq

/-- The assertion of NP-focus *only*, *no one who is not NP* (113b), for an NP denoting a set of
sets. -/
def onlyNP : Licenser :=
  .classical ⟨Predicate, fun p ↦ Set (Set p.ι), fun _ ↦ Prop, fun p Q ↦ p.A ⊆ ⋂₀ Q⟩

/-- The assertion of *only* NP in its scope. -/
def onlyScope : Licenser :=
  .classical ⟨Predicate, fun p ↦ Set p.ι, fun _ ↦ Prop, fun p P ↦ P ⊆ p.A⟩

/-- An expression that the paper's entailment tests find upward entailing and whose meaning it does
not give, *with*, *after*, *enough*, *in favor of*, *sure*, *suspect*, *manage*, *if S*. -/
def upwardOperator : Licenser := .classical ⟨PUnit, fun _ ↦ Prop, fun _ ↦ Prop, fun _ P ↦ P⟩

/-- The meaning of an expression, the licenser it places over its scope. -/
noncomputable def Expression.meaning : Expression → Licenser
  | .not => negation.licenser
  | .det d => .classical ⟨FinitePredicate, fun p ↦ Set p.ι, fun _ ↦ Prop, fun p R ↦ d.denote R p.A⟩
  | .qnp d => .classical ⟨FinitePredicate, fun p ↦ Set p.ι, fun _ ↦ Prop, fun p ↦ d.denote p.A⟩
  | .without => withoutClause.licenser
  | .before => beforeClause.licenser
  | .tooTo => LicensingContext.tooTo.licenser
  | .doubt => doubtVerb.licenser
  | .antecedent => materialAntecedent
  | .onlyNP => Ladusaw1979.onlyNP
  | .«only» => onlyScope
  | .upward => upwardOperator

-- For a proper name the assertion of *only* is *no one who is not that individual*, (113b), p. 165.
theorem subset_sInter_name_iff {ι : Type} (j : ι) (P : Set ι) :
    P ⊆ ⋂₀ {S | j ∈ S} ↔ ∀ x ∈ P, x = j := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx S hS ↦ h x hx ▸ hS⟩
  simpa using h hx {y | y = j} rfl

/-- An expression is a trigger when it is downward entailing, (40), p. 147. -/
def Expression.IsTrigger (e : Expression) : Prop := IsDownwardEntailing e.meaning

/-- The triggers among the expressions. -/
def triggers : List Expression :=
  [.not, .det .everyDet, .det .noDet, .det .atMostThree, .qnp .noDet, .qnp .atMostThree,
    .qnp .fewDet, .without, .before, .tooTo, .doubt, .antecedent, .onlyNP, .«only»]

private theorem isTrigger_det_iff (d : Determiner) :
    (Expression.det d).IsTrigger ↔ ∀ (ι : Type) [Fintype ι] (A : Set ι),
      Antitone fun R ↦ (d.denote R A : Prop) :=
  isDownwardEntailing_classical_iff.trans
    ⟨fun h ι _ A ↦ h ⟨⟨ι, A⟩⟩, fun h p ↦ h p.ι p.A⟩

private theorem isTrigger_qnp_iff (d : Determiner) :
    (Expression.qnp d).IsTrigger ↔ ∀ (ι : Type) [Fintype ι] (A : Set ι),
      Antitone (d.denote A) :=
  isDownwardEntailing_classical_iff.trans
    ⟨fun h ι _ A ↦ h ⟨⟨ι, A⟩⟩, fun h p ↦ h p.ι p.A⟩

theorem isTrigger_iff (e : Expression) : e.IsTrigger ↔ e ∈ triggers := by
  have hdet (d : Determiner) (h : Expression.det d ∉ triggers)
      (hd : ¬ ∀ (ι : Type) [Fintype ι] (A : Set ι), Antitone fun R ↦ (d.denote R A : Prop)) :
      (Expression.det d).IsTrigger ↔ Expression.det d ∈ triggers :=
    iff_of_false (fun ht ↦ hd ((isTrigger_det_iff d).1 ht)) h
  have hqnp (d : Determiner) (h : Expression.qnp d ∉ triggers)
      (hd : ¬ ∀ (ι : Type) [Fintype ι] (A : Set ι), Antitone (d.denote A)) :
      (Expression.qnp d).IsTrigger ↔ Expression.qnp d ∈ triggers :=
    iff_of_false (fun ht ↦ hd ((isTrigger_qnp_iff d).1 ht)) h
  cases e with
  | not => exact iff_of_true (holds_negation .weak) (by decide)
  | det d =>
    cases d with
    | someDet =>
      refine hdet _ (by decide) fun h ↦ ?_
      obtain ⟨_, hx, _⟩ := h (Fin 1) Set.univ (Set.empty_subset _)
        (⟨0, trivial, trivial⟩ : (Det.some Set.univ Set.univ : Prop))
      exact hx
    | everyDet =>
      exact iff_of_true ((isTrigger_det_iff _).2 fun _ _ A ↦ restrictorAntitone_every A) (by decide)
    | noDet =>
      exact iff_of_true ((isTrigger_det_iff _).2 fun _ _ A ↦ restrictorAntitone_no A) (by decide)
    | atLeastThree =>
      refine hdet _ (by decide) fun h ↦ ?_
      have : atLeast 3 Set.univ (Set.univ : Set (Fin 3)) →
          atLeast 3 {x : Fin 3 | x ≠ x} Set.univ := h (Fin 3) Set.univ (Set.subset_univ _)
      revert this; decide
    | atMostThree =>
      exact iff_of_true ((isTrigger_det_iff _).2 fun _ _ A ↦ restrictorAntitone_atMost 3 A)
        (by decide)
    -- (56)–(57), p. 152: the restrictor of *most*, box IV.
    | mostDet => exact hdet _ (by decide) fun h ↦ not_restrictorAntitone_most fun B ↦ h (Fin 3) B
    | fewDet => exact hdet _ (by decide) fun h ↦ not_restrictorAntitone_few fun B ↦ h (Fin 3) B
  | qnp d =>
    cases d with
    | someDet => exact hqnp _ (by decide) fun h ↦
        not_scopeAntitone_some (α := Fin 1) fun A ↦ h (Fin 1) A
    | everyDet => exact hqnp _ (by decide) fun h ↦
        not_scopeAntitone_every (α := Fin 1) fun A ↦ h (Fin 1) A
    | noDet =>
      exact iff_of_true ((isTrigger_qnp_iff _).2 fun _ _ A ↦ scopeAntitone_no A) (by decide)
    | atLeastThree =>
      refine hqnp _ (by decide) fun h ↦ ?_
      have : atLeast 3 Set.univ (Set.univ : Set (Fin 3)) →
          atLeast 3 Set.univ {x : Fin 3 | x ≠ x} := h (Fin 3) Set.univ (Set.subset_univ _)
      revert this; decide
    | atMostThree =>
      exact iff_of_true ((isTrigger_qnp_iff _).2 fun _ _ A ↦ scopeAntitone_atMost 3 A) (by decide)
    | mostDet => exact hqnp _ (by decide) fun h ↦
        not_scopeAntitone_most (α := Fin 1) fun A ↦ h (Fin 1) A
    | fewDet =>
      exact iff_of_true ((isTrigger_qnp_iff _).2 fun _ _ A ↦ scopeAntitone_few A) (by decide)
  | without => exact iff_of_true ((holds_withoutClause_iff (s := .weak)).2 (by decide)) (by decide)
  | before => exact iff_of_true ((holds_beforeClause_iff (s := .weak)).2 (by decide)) (by decide)
  | tooTo => exact iff_of_true ((holds_tooTo_iff (s := .weak)).2 (by decide)) (by decide)
  | doubt => exact iff_of_true ((holds_doubtVerb_iff (s := .weak)).2 (by decide)) (by decide)
  | antecedent => exact iff_of_true isDownwardEntailing_materialAntecedent (by decide)
  | onlyNP =>
    have hde : IsDownwardEntailing Ladusaw1979.onlyNP := isDownwardEntailing_classical_iff.2
      fun _ _ _ h hP ↦ Set.Subset.trans hP (Set.sInter_subset_sInter h)
    exact iff_of_true hde (by decide)
  | «only» =>
    have hde : IsDownwardEntailing onlyScope := isDownwardEntailing_classical_iff.2
      fun _ _ _ h hP ↦ Set.Subset.trans h hP
    exact iff_of_true hde (by decide)
  | upward =>
    refine iff_of_false (fun h ↦ ?_) (by decide)
    exact (isDownwardEntailing_classical_iff.1 h ⟨⟩ (le_top : False ≤ True) : True → False) trivial

instance : DecidablePred Expression.IsTrigger := fun e ↦ decidable_of_iff _ (isTrigger_iff e).symm

/-- The overt negations *not*, *no* NP and *never* (p. 171), the only anti-triggers. -/
def Expression.IsNegation : Expression → Prop
  | .not | .qnp .noDet => True
  | _ => False

instance : DecidablePred Expression.IsNegation := fun e ↦ by
  cases e with
  | qnp d => cases d <;> unfold Expression.IsNegation <;> infer_instance
  | _ => unfold Expression.IsNegation; infer_instance

theorem Expression.IsNegation.isTrigger {e : Expression} (h : e.IsNegation) : e.IsTrigger := by
  rw [isTrigger_iff]
  cases e with
  | not => decide
  | qnp d => cases d <;> first | decide | exact absurd h id
  | _ => exact absurd h id

/-- The anti-triggers are a proper part of the triggers: *at most three* is a trigger and does not
block a positive polarity item, (139d), p. 170. -/
theorem exists_trigger_not_negation : ∃ e : Expression, e.IsTrigger ∧ ¬ e.IsNegation :=
  ⟨.qnp .atMostThree, (isTrigger_iff _).2 (by decide), id⟩

-- (139)–(141), p. 170: the fragment's positive polarity items are blocked by *no one* and not by
-- *few* or *at most*.
theorem antiLicenses_someone_already_rather :
    ∀ e ∈ [English.PolarityItems.someone, English.PolarityItems.already,
        English.PolarityItems.rather],
      nobody.licenser.AntiLicenses e ∧ ¬ few.licenser.AntiLicenses e ∧
        ¬ atMost.licenser.AntiLicenses e := by
  decide

/-! ### The Inherent Scope Convention -/

/-- Whether an expression precedes the polarity items in its scope, which matters when they are its
clausemates, (47a), p. 112. -/
inductive Order where
  | precedes | follows
  deriving DecidableEq

/-- A reading of a sentence, as far as the convention looks at it: the polarity items and the
expressions and clause boundaries over them. -/
inductive Interp where
  /-- The meaning of a polarity item. -/
  | item (e : PolarityItem)
  /-- An expression taking a meaning in its scope. -/
  | scope (f : Expression) (o : Order) (s : Interp)
  /-- A meaning forming an S̄. -/
  | clause (s : Interp)
  /-- A meaning with two immediate components. -/
  | pair (s t : Interp)

namespace Interp

/-- The meaning has an N-mark from a clausemate: inherited, (48A.i), p. 113, and removed by a
trigger that precedes, (48A.ii). -/
def NMate : Interp → Prop
  | .item e => e.IsNPI
  | .scope f o s => s.NMate ∧ ¬ (f.IsTrigger ∧ o = .precedes)
  | .clause _ => False
  | .pair s t => s.NMate ∨ t.NMate

/-- The meaning has an N-mark from a lower clause, which any trigger removes, (47a), p. 112. -/
def NLow : Interp → Prop
  | .item _ => False
  | .scope f _ s => s.NLow ∧ ¬ f.IsTrigger
  | .clause s => s.NMate ∨ s.NLow
  | .pair s t => s.NLow ∨ t.NLow

/-- The meaning is an N-meaning. -/
def IsN (i : Interp) : Prop := i.NMate ∨ i.NLow

/-- The meaning is a W-meaning: inherited, (48A.i), and lost at an S̄, (48A.iii), p. 113. -/
def IsW : Interp → Prop
  | .item e => e.IsPPI
  | .scope _ _ s => s.IsW
  | .clause _ => False
  | .pair s t => s.IsW ∨ t.IsW

/-- No W-meaning is the scope of a negation in the reading, (48B.ii), p. 113. -/
def Licit : Interp → Prop
  | .item _ => True
  | .scope f _ s => s.Licit ∧ (f.IsNegation → ¬ s.IsW)
  | .clause s => s.Licit
  | .pair s t => s.Licit ∧ t.Licit

/-- A reading survives the convention when it is not an N-meaning, (48B.i), p. 113, and no W-meaning
is the scope of a negation, (48B.ii). -/
def Survives (i : Interp) : Prop := ¬ i.IsN ∧ i.Licit

instance decidableNMate : DecidablePred NMate
  | .item _ => inferInstanceAs (Decidable (_ = _))
  | .scope _ _ s => @instDecidableAnd _ _ (decidableNMate s) inferInstance
  | .clause _ => inferInstanceAs (Decidable False)
  | .pair s t => @instDecidableOr _ _ (decidableNMate s) (decidableNMate t)

instance decidableNLow : DecidablePred NLow
  | .item _ => inferInstanceAs (Decidable False)
  | .scope _ _ s => @instDecidableAnd _ _ (decidableNLow s) inferInstance
  | .clause s => @instDecidableOr _ _ (decidableNMate s) (decidableNLow s)
  | .pair s t => @instDecidableOr _ _ (decidableNLow s) (decidableNLow t)

instance decidableIsW : DecidablePred IsW
  | .item _ => inferInstanceAs (Decidable (_ = _))
  | .scope _ _ s => decidableIsW s
  | .clause _ => inferInstanceAs (Decidable False)
  | .pair s t => @instDecidableOr _ _ (decidableIsW s) (decidableIsW t)

instance decidableLicit : DecidablePred Licit
  | .item _ => inferInstanceAs (Decidable True)
  | .scope _ _ s => @instDecidableAnd _ _ (decidableLicit s) inferInstance
  | .clause s => decidableLicit s
  | .pair s t => @instDecidableAnd _ _ (decidableLicit s) (decidableLicit t)

instance : DecidablePred IsN := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))
instance : DecidablePred Survives := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Once triggered, a negative polarity item stays triggered: no further expression can restore the
N-mark, so the convention predicts that nothing reverses polarity for negative polarity items, fn. 1
of chapter IX, p. 211. -/
theorem not_isN_scope {s : Interp} (h : ¬ s.IsN) (f : Expression) (o : Order) :
    ¬ (scope f o s).IsN := by
  rintro (hm | hl)
  · exact h (.inl hm.1)
  · exact h (.inr hl.1)

end Interp

open Interp English.PolarityItems

/-- Under negation *some* has only the reading above it and *any* only the reading below it, so
(4c) and (4d) are unambiguous and not synonymous, p. 91. -/
theorem some_any_complementary :
    (¬ (scope .not .precedes (item someone)).Survives ∧ (item someone).Survives) ∧
      ((scope .not .precedes (item any)).Survives ∧ ¬ (item any).Survives) := by
  decide

-- (7b), p. 135: two negations make an upward-entailing context, and the convention admits the item
-- all the same, having discharged its mark at the lower one.
example {W : Type*} : Monotone fun P : Set W ↦ Pᶜᶜ := fun _ _ h ↦ by simpa using h

theorem survives_iff_licenses {e : PolarityItem} (f : Expression) (he : e.licensor = some .weak)
    (hp : e.antiLicensor = none) (hc : ∃ F, f.meaning = .classical F)
    (hn : ¬ f.meaning.IsStrawsonUE) :
    (scope f .precedes (item e)).Survives ↔ f.meaning.Licenses e := by
  obtain ⟨F, hF⟩ := hc
  have hN : e.IsNPI := by simp [IsNPI, he]
  have hP : ¬ e.IsPPI := by simp [IsPPI, hp]
  rw [hF] at hn ⊢
  rw [licenses_iff_isDownwardEntailing he hn, ← hF]
  refine ⟨fun ⟨h, _⟩ ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · by_contra ht
    exact h (.inl ⟨hN, fun hh ↦ ht hh.1⟩)
  · rintro (⟨_, hh⟩ | ⟨hh, _⟩)
    · exact hh ⟨h, rfl⟩
    · exact hh
  · exact ⟨trivial, fun _ ↦ hP⟩

/-! ### The judgments -/

/-- The polarity items of the rows. -/
def items : List (String × PolarityItem) :=
  [(any.form, any), (ever.form, ever), (yet.form, yet), (someone.form, someone),
    (already.form, already), (rather.form, rather)]

/-- The expressions of the rows. *Never* and *no* NP are `no`; *rarely*, *seldom*, *hardly* and
*few* NP are `few`; *fail* is `not`. -/
def expressions : List (String × Expression) :=
  [("not", .not), ("no", .qnp .noDet), ("few", .qnp .fewDet), ("some", .qnp .someDet),
    ("every", .qnp .everyDet), ("most", .qnp .mostDet), ("atMost", .qnp .atMostThree),
    ("atLeast", .qnp .atLeastThree), ("no-det", .det .noDet), ("every-det", .det .everyDet),
    ("some-det", .det .someDet), ("few-det", .det .fewDet), ("most-det", .det .mostDet),
    ("atMost-det", .det .atMostThree), ("atLeast-det", .det .atLeastThree),
    ("without", .without), ("before", .before),
    ("tooTo", .tooTo), ("doubt", .doubt), ("if", .antecedent), ("only-np", .onlyNP),
    ("only", .«only»), ("upward", .upward)]

/-- The branch of a row's reading under the given item and the given expression columns, the first
outermost. -/
def branch? (r : Datum) (item : String) (columns : List String) : Option Interp := do
  let e ← r.parse? item items
  let fs ← (columns.filter fun c ↦ (r.feature? c).isSome).mapM fun c ↦ r.parse? c expressions
  let o := if r.feature? "order" = some "follows" then Order.follows else .precedes
  let core := if r.feature? "clause" = some "true" then Interp.clause (.item e) else .item e
  pure (fs.foldr (fun f s ↦ .scope f o s) core)

/-- A row's reading with its polarity items in the scope of its expressions. -/
def narrow? (r : Datum) : Option Interp := do
  let s ← branch? r "item" ["over2", "over", "functor"]
  match branch? r "item2" ["functor2"] with
  | some t => pure (.pair s t)
  | none => pure s

/-- A row's reading with its NP stored above the expressions, for the rows that allow it, survives
the convention. -/
def WideSurvives (r : Datum) : Prop :=
  r.feature? "wide" = some "true" ∧ ∃ e ∈ r.parse? "item" items, (item e).Survives

instance (r : Datum) : Decidable (WideSurvives r) := inferInstanceAs (Decidable (_ ∧ _))

/-- The convention gives every judgment of the rows but the denials and *few* in its restrictor: a
sentence is unstarred exactly when one of its readings survives. -/
theorem rows_predicted :
    ∀ r ∈ Examples.all, ∃ i ∈ narrow? r,
      r.feature? "denial" = some "true" ∨ r.feature? "functor" = some "few-det" ∨
        (r.judgment ≠ .ungrammatical ↔ i.Survives ∨ WideSurvives r) := by
  decide

-- (4), (142)
theorem rows_denial_filtered :
    ∀ r ∈ Examples.all, r.feature? "denial" = some "true" →
      r.judgment = .marginal ∧ ∀ i ∈ narrow? r, ¬ i.Survives := by
  decide

-- (53a), p. 152: the exception, the restrictor of *few* being no trigger.
theorem few_restrictor_mispredicted :
    Examples.vi_53a.judgment = .acceptable ∧ ∀ i ∈ narrow? Examples.vi_53a, ¬ i.Survives := by
  decide

end Ladusaw1979
