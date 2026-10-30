module

public import Linglib.Discourse.QUD.Basic
public import Linglib.Semantics.Questions.HamblinSet
public import Studies.FarkasBruce2010
public import Linglib.Data.Examples.GarassinoJacob2018
public import Linglib.Data.Examples.Readers

/-!
# Garassino and Jacob (2018): Polarity focus and non-canonical syntax in Italian, French and Spanish

This file formalizes [garassino-jacob-2018]'s account of clitic left dislocation and the *sì che*
~ *sí que* constructions as realizations of polarity focus. Polarity focus is focus whose
background is the whole proposition and whose alternatives are the proposition and its negation,
so a polarity-focus utterance is a congruent answer to a polar question under discussion
(`orbit_eq_alt_query`). The chapter's corpus passages are read as discourse trees in the
manner of [buring-2003] and [roberts-2012]: a *wh*-question such as *who has been sitting back?*
is pursued through the polar question for each candidate, each answered with a polarity-focus
utterance, and a polar question about a hyperonymous proposition through the polar questions of
its instances. Both strategies are complete: jointly resolving the subquestions resolves the
question (`agentStrategy_isComplete`, `scalarStrategy_isComplete`), the former because the polar
questions of a family are its partition question.

The rows are the chapter's examples with the lexical and syntactic means they use, the kind of
antecedent, the dislocated constituent and, where the chapter says, whether the utterance stands
to its antecedent in situational identity or analogy and whether it answers a subquestion. In
situational identity a positive answer contradicts the negative proposition the context gives;
in situational analogy it does not exclude its truth. Whether polarity focus reacts to a denial
of the proposition is a separate criterion of the chapter, and the rows attest denials in both
relations (`rows_denies_identity_and_analogy`). French *si* is limited to answering a preceding
opposite turn: every attested *si* is a response of the kind [farkas-bruce-2010] say it marks,
[reverse, +] (`rows_si_mem_reversePositive`), while *sì che* and *sí que* are attested in
responses outside it (`rows_siChe_siQue_not_mem_reversePositive`).

## Implementation notes

* In the Direct Europarl corpus the chapter counts 6 Italian and 4 French polar left dislocations
  against none in Spanish, and 61 Spanish *sí que* against none in Italian, with 36 of the 61
  carrying a left element (26 subjects, 2 objects, 8 adverbials); it draws the complementary
  distribution and Spanish's preference for a transparent assertive particle from these figures
  and offers no quantitative analysis, so the counts stay in prose.
* The chapter endorses [matic-nikolaeva-2018]'s view that dislocation is no structural means of
  polarity focus but makes the reading available in context.
* An utterance with a preceding turn, a statement or a polar question, is a
  `Discourse.Response` to it (`Antecedent.response`), positive since it affirms; an inferred
  negation, an open question, a modal statement or no antecedent is no such turn.
* The discourse trees are stated for finitely many worlds, which is what the substrate's strategy
  completeness needs to pass from lattice entailment to alternative entailment.

## References

* [garassino-jacob-2018]
* [dimroth-sudhoff-2018]
* [matic-nikolaeva-2018]
* [buring-2003]
* [roberts-2012]
* [hohle-1992]
* [batllori-hernanz-2013]
* [poletto-zanuttini-2013]
-/

@[expose] public section

namespace GarassinoJacob2018

open Question Discourse

variable {W F : Type*}

/-! ### Polarity focus as a polar question under discussion -/

theorem orbit_eq_alt_query {p : Set W} (hp : p.Nonempty) (hpc : pᶜ.Nonempty) :
    MulAction.orbit Polarity p = alt (ofSet p).query := by
  rw [query_ofSet, alt_polar_eq_orbit hp.ne_empty (Set.nonempty_compl.mp hpc)]

/-! ### Discourse strategies of polar subquestions -/

/-- The tree of the sitting-back passage pursues a *wh*-question over candidates through the
polar question for each candidate. -/
def agentStrategy (agents : List F) (P : F → Set W) : Strategy W :=
  .node (fromSetoid (partition (Set.range P))) (agents.map fun f ↦ .leaf (ofSet (P f)).query)

theorem agentStrategy_isComplete {agents : List F} (hcov : ∀ f, f ∈ agents)
    (P : F → Set W) : (agentStrategy agents P).IsComplete := by
  refine .node (fun _ ↦ ?_) (fun c hc ↦ ?_)
  · have hmem : ∀ q, q ∈ ((agents.map fun f ↦ RoseTree.leaf (ofSet (P f)).query).map
        RoseTree.value : Multiset (Question W)) ↔ ∃ f, (ofSet (P f)).query = q := by
      intro q
      simp only [Multiset.mem_coe, List.mem_map, List.map_map, Function.comp_def, RoseTree.leaf,
        RoseTree.value_node]
      exact ⟨fun ⟨f, _, h⟩ ↦ ⟨f, h⟩, fun ⟨f, h⟩ ↦ ⟨f, hcov f, h⟩⟩
    rw [fromSetoid_partition, iInf_range]
    simp_rw [← query_ofSet]
    refine (le_antisymm ?_ ?_).le
    · exact le_iInf fun f ↦ Multiset.inf_le ((hmem _).mpr ⟨f, rfl⟩)
    · exact Multiset.le_inf.mpr fun q hq ↦ by obtain ⟨f, rfl⟩ := (hmem q).mp hq; exact iInf_le _ f
  · obtain ⟨f, _, rfl⟩ := List.mem_map.mp hc
    exact .leaf _

/-- The tree of the treaty passage pursues a polar question about a disjunction of instances
through the polar questions of the instances. -/
def scalarStrategy (p q : Set W) : Strategy W :=
  .node (ofSet (p ∪ q)).query [.leaf (ofSet p).query, .leaf (ofSet q).query]

theorem scalarStrategy_isComplete (p q : Set W) : (scalarStrategy p q).IsComplete := by
  refine .node_pair (le_def.mpr fun σ hσ ↦ ?_) (.leaf _) (.leaf _)
  rw [RoseTree.leaf, RoseTree.leaf, RoseTree.value_node, RoseTree.value_node] at hσ
  obtain ⟨h₁, h₂⟩ := hσ
  have h₁' : σ ∈ (ofSet p).query := h₁
  have h₂' : σ ∈ (ofSet q).query := h₂
  show σ ∈ (ofSet (p ∪ q)).query
  rw [mem_query, mem_ofSet, info_ofSet] at h₁' h₂' ⊢
  rcases h₁' with h₁' | h₁' <;> rcases h₂' with h₂' | h₂'
  · exact Or.inl (h₁'.trans Set.subset_union_left)
  · exact Or.inl (h₁'.trans Set.subset_union_left)
  · exact Or.inl (h₂'.trans Set.subset_union_right)
  · exact Or.inr fun w hw ↦ (Set.compl_union p q).symm ▸ ⟨h₁' hw, h₂' hw⟩

/-! ### The chapter's examples -/

/-- The lexical and syntactic means of polarity focus the chapter surveys. -/
inductive Means
  | emphaticDo | verumAccent | embedding | juxtaposed | ellipticEmbedding | fronting | faireCleft
  | leftDislocation | rightDislocation | siChe | siQue | siOnly | siParticle
  deriving DecidableEq, Repr

/-- What the polarity-focus utterance reacts to. -/
inductive Antecedent
  | explicitNegation | explicitQuestion | inferredNegation | openQuestion | modal | positive
  | absent
  deriving DecidableEq, Repr

/-- The dislocated constituent, if any. -/
inductive Dislocated
  | absent | subject | object | adverbial | both
  deriving DecidableEq, Repr

/-- Whether the utterance's situation is the antecedent's or an analogous one. -/
inductive Relation
  | identity | analogy | unstated
  deriving DecidableEq, Repr

/-- When the antecedent is a preceding turn, a polarity-focus utterance responds to it with an
affirmation, after a negative statement, a positive statement or a polar question. -/
def Antecedent.response : Antecedent → Option Discourse.Response
  | .explicitNegation => some ⟨.assertion, .negative, .positive⟩
  | .positive => some ⟨.assertion, .positive, .positive⟩
  | .explicitQuestion => some ⟨.polarQuestion, .positive, .positive⟩
  | .inferredNegation | .modal | .openQuestion | .absent => none

/-- The antecedent is a previous denial of the proposition, explicit or inferable: polarity focus
after it presupposes the negation rather than an open question or a given affirmation. -/
def Antecedent.Denies : Antecedent → Prop
  | .explicitNegation | .inferredNegation => True
  | _ => False

instance : DecidablePred Antecedent.Denies := fun a ↦ by
  cases a <;> simp only [Antecedent.Denies] <;> infer_instance

structure Row where
  means : Means
  antecedent : Antecedent
  dislocated : Dislocated
  relation : Relation
  subquestion : Bool
  deriving DecidableEq, Repr

def Row.ofDatum (ex : Datum) : Option Row := do
  let means ← ex.parse? "strategy" [("emphaticDo", Means.emphaticDo),
    ("verumAccent", .verumAccent), ("embedding", .embedding), ("juxtaposed", .juxtaposed),
    ("ellipticEmbedding", .ellipticEmbedding), ("fronting", .fronting), ("faireCleft", .faireCleft),
    ("leftDislocation", .leftDislocation), ("rightDislocation", .rightDislocation),
    ("siChe", .siChe), ("siQue", .siQue), ("siOnly", .siOnly), ("siParticle", .siParticle)]
  let antecedent ← ex.parse? "antecedent" [("explicitNegation", Antecedent.explicitNegation),
    ("explicitQuestion", .explicitQuestion), ("inferredNegation", .inferredNegation),
    ("openQuestion", .openQuestion), ("modal", .modal), ("positive", .positive), ("none", .absent)]
  let dislocated ← ex.parse? "dislocated" [("none", Dislocated.absent), ("subject", .subject),
    ("object", .object), ("adverbial", .adverbial), ("both", .both)]
  let relation ← ex.parse? "relation" [("identity", Relation.identity), ("analogy", .analogy),
    ("unstated", .unstated)]
  let subquestion ← ex.parse? "subquestion" [("yes", true), ("no", false)]
  pure ⟨means, antecedent, dislocated, relation, subquestion⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_denies_identity_and_analogy :
    (∃ r ∈ rows, r.antecedent.Denies ∧ r.relation = .identity) ∧
      ∃ r ∈ rows, r.antecedent.Denies ∧ r.relation = .analogy := by
  decide

theorem rows_si_mem_reversePositive : ∀ r ∈ rows, r.means = .siParticle →
    ∃ x ∈ r.antecedent.response, x ∈ FarkasBruce2010.reversePositive := by
  decide

theorem rows_siChe_siQue_not_mem_reversePositive :
    (∃ r ∈ rows, r.means = .siChe ∧
      ∃ x ∈ r.antecedent.response, x ∉ FarkasBruce2010.reversePositive) ∧
    ∃ r ∈ rows, r.means = .siQue ∧
      ∃ x ∈ r.antecedent.response, x ∉ FarkasBruce2010.reversePositive := by
  decide

theorem rows_subquestion_analogy :
    (∀ r ∈ rows, r.subquestion = true → r.relation = .analogy) ∧
      ∃ r ∈ rows, r.relation = .analogy ∧ r.subquestion = false := by
  decide

end GarassinoJacob2018
