module

public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Quantification.Counting

/-!
# Ladusaw (1979): Polarity Sensitivity as Inherent Scope Relations

Ladusaw's licensing condition says that an expression triggers negative polarity items in its
scope exactly when it is downward entailing, its denotation reversing the inclusion of its
arguments, so that the affective environments of the earlier literature are characterized rather
than listed. For a construction whose operators are functions between lattices the library's
licensing theory agrees: it licenses the weak polarity items
[exactly when it is downward entailing](##licenses_iff_isDownwardEntailing), once the operators that
are upward entailing as well are set aside. Every environment credited to the dissertation denotes a
downward-entailing operator (`cited_environments_de`), and a question is not downward entailing by
construction, licensing by relevance instead (`question_not_de`). The determiners behind three of
these environments are downward entailing in exactly the argument where they license: *no* in its
scope and its restrictor, *few* in its scope, and *every* in its restrictor but not its scope
(`determiner_monotonicity`).

## Implementation notes

* Ladusaw reads a conditional antecedent as the antecedent of a material conditional, which is
  downward entailing (`materialAntecedent`); the library's `LicensingContext.conditionalAntecedent`
  is von Fintel's counterfactual, downward entailing only modulo its presupposition.
* The library's licensing condition asks in addition that the operator not be upward entailing,
  which a constant operator is, though the definition of downward entailment counts it as downward
  entailing; the biconditional is stated for the operators that are not.
* The dissertation's scan in the library has no text layer; `environments` is the list the library
  credits to it. The anti-additive licensers and the strong polarity items postdate the
  dissertation. The converse of licensing by downward entailment is stated for the operators that
  are functions between lattices, the denotations the definition is given for; the Strawsonian
  licensers and questions license weak items by other routes.

## References

* [ladusaw-1979]
-/

@[expose] public section

namespace Ladusaw1979

open PolarityItem NaturalLogic Quantifier Quantifier.GQ LicensingContext Licenser

/-- An environment is downward entailing when every operator it places over the item reverses
entailment, the inclusion of its arguments. -/
def IsDownwardEntailing (L : Licenser) : Prop := L.Holds .anti

-- (37): an operator is downward entailing when it reverses the inclusion of its arguments
theorem isDownwardEntailing_classical_iff {F : OperatorFamily} :
    IsDownwardEntailing (.classical F) ↔ ∀ p, Antitone (F.op p) :=
  forall_congr' fun _ ↦ Signature.holdsFor_anti_iff

/-- A conditional's consequent, over worlds. -/
structure Consequent where
  /-- The worlds. -/
  W : Type
  /-- The consequent. -/
  q : Set W

/-- The antecedent of a material conditional, Ladusaw's reading of conditional antecedents. -/
def materialAntecedent : Licenser :=
  .classical ⟨Consequent, fun p ↦ Set p.W, fun p ↦ Set p.W, fun p P ↦ Pᶜ ∪ p.q⟩

theorem isDownwardEntailing_materialAntecedent : IsDownwardEntailing materialAntecedent :=
  fun _ ↦ Signature.holdsFor_anti_iff.mpr fun _ _ h ↦ Set.union_subset_union_left _
    (Set.compl_subset_compl.mpr h)

-- UNVERIFIED: the list is the library's record, not checked against the dissertation.
/-- The licensing environments credited to the dissertation are negation, negative quantifiers,
*without*, the restrictor of a universal, *few*, *at most*, the antecedent of a conditional,
*before*, *too … to*, and the clausal comparative. -/
noncomputable def environments : List Licenser :=
  [negation.licenser, nobody.licenser, withoutClause.licenser, universalRestrictor.licenser,
    few.licenser, atMost.licenser, materialAntecedent, beforeClause.licenser, tooTo.licenser,
    clausalComparative.licenser]

theorem cited_environments_de : ∀ c ∈ environments, IsDownwardEntailing c := by
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
theorem question_not_de : ¬ IsDownwardEntailing question.licenser := id

theorem licenses_of_isDownwardEntailing {L : Licenser} {e : PolarityItem}
    (hc : IsDownwardEntailing L) (hn : ¬ L.IsStrawsonUE) (he : e.licensor = some .weak) :
    L.Licenses e :=
  .inl ⟨.weak, he, isStrawsonDE_of_holds_anti hc, hn⟩

theorem isDownwardEntailing_of_licenses {F : OperatorFamily} {e : PolarityItem}
    (h : (Licenser.classical F).Licenses e) : IsDownwardEntailing (.classical F) := by
  rcases h with ⟨_, -, hr⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact isDownwardEntailing_classical_iff.mpr hr.weak.1
  · exact (h : False).elim
  · exact (h : False).elim

-- (40)
/-- A construction whose operators are functions between lattices, and not upward entailing,
licenses the weak negative polarity items exactly when it is downward entailing. -/
theorem licenses_iff_isDownwardEntailing {F : OperatorFamily} {e : PolarityItem}
    (he : e.licensor = some .weak) (hn : ¬ (Licenser.classical F).IsStrawsonUE) :
    (Licenser.classical F).Licenses e ↔ IsDownwardEntailing (.classical F) :=
  ⟨isDownwardEntailing_of_licenses, fun h ↦ licenses_of_isDownwardEntailing h hn he⟩

variable {α : Type*}

theorem determiner_monotonicity [Fintype α] [Nonempty α] :
    ScopeAntitone (no : GQ α) ∧ RestrictorAntitone (no : GQ α) ∧ ScopeAntitone (few : GQ α) ∧
      RestrictorAntitone (every : GQ α) ∧ ¬ ScopeAntitone (every : GQ α) :=
  ⟨scopeAntitone_no, restrictorAntitone_no, scopeAntitone_few, restrictorAntitone_every,
    not_scopeAntitone_every⟩

end Ladusaw1979
