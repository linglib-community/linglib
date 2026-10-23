module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.IntervalCases
public import Linglib.Semantics.Causation.Morphological
public import Linglib.Data.Examples.Song1996
public import Linglib.Fragments.Korean.Verbs

/-!
# Song (1996): Causatives and causation

Song classifies causative constructions by what joins the expression of cause to the
expression of effect. In the COMPACT type [Vcause] and [Veffect] share one clause, fused (English
*kill*), bound (Turkish *öl-dür*) or free (French *faire lire*); in the AND type a clause of cause
and a clause of effect are coordinated, in that order (Vata *le*); in the PURP type the clause of
effect is a clause of purpose (Korean *-ke*) (chapter 2). The traditional typology, lexical,
morphological and syntactic, splits the COMPACT type and lumps the other two together (§1.2). The
COMPACT type being the diachronic residue of the other two, what distinguishes those is
implicativity: the AND type expresses the EVENT and RESULT stages of the cognitive structure of
causation GOAL → EVENT → RESULT and entails its effect, the PURP type expresses GOAL and EVENT and
does not, except through the inference that people realize the goals they act for (chapter 5).
The grammatical relation of the causee follows no hierarchy of its own: a language caps the core
NPs of a simplex clause, causative or not, and its causatives keep within the cap (chapter 6).

`Form.type` computes the type of a form and `Form.traditional` its traditional class, and on
Song's examples neither classification refines the other (`not_factorsThrough_type`,
`not_factorsThrough_traditional`). A biclausal type entails its effect in every model exactly
when it expresses RESULT (`forall_meaning_subset_iff`), so the AND type is implicative and the
PURP type is not (`and_meaning_subset`, `purp_not_implicative`), as the example (7) bears out
(`effectNegated_rows`), while COMPACT causatives go either way (`compact_implicativity_varies`);
the success assumption restores implicativity (`meaning_subset_of_success`). The paradigm
causative of Comrie's case hierarchy never has more than three core NPs
(`paradigmCoreNPs_le_three`), so a language capped at two refutes the hierarchy for transitive
bases (`paradigmCoreNPs_two`). Korean has causatives of all three traditional classes
(`korean_types`). Its causative *ha-* needs its clause of effect, which a purposive main verb does
not (`clause_omitted_rows`), and the causee is nominative exactly where *ha-* controls nothing
(`causee_rows`), as the subject of a clause of purpose always is (`purposive_subject_rows`).

## Implementation notes

* A form records the structure Song reads off an example: one clause and how [Vcause] is
  realized, or two clauses, their link and their order. The forms of the examples are row
  features, and their types are computed.
* The traditional class of a free [Vcause] is morphological, after Comrie's treatment of
  the French causative as quasi-morphological, which Song reports (p. 161); Song's own
  description of the traditional typology (p. 135) does not place it.
* The semantic structures are those of the prototypical types. A model interprets the three
  stages by arbitrary propositions, so that entailing the effect is doing so in every model. The
  cline of implicativity within the PURP type (p. 136; a survey of sixteen Korean speakers, §4.5)
  and the implicativity of COMPACT causatives are outside the model.
* `paradigmCoreNPs` counts the indirect object as a core NP, as in a language capped at three
  (p. 174). That the paradigm case keeps within a cap of three is drawn here rather than stated
  by Song, who argues the reinterpretation for extended demotion and doubling (§6.5).

## TODO

* The diachronic model of causative affixes (chapter 3): four stages from a construction whose
  [Vcause] is obligatory to a causative affix, and the argument that PURP, overt and meaningful,
  can take over [Vcause] while AND, often covert and empty, cannot (pp. 80–85).
* The measures by which causatives keep within the cap (§§6.4–6.6): omission, demotion to an
  adjunct, doubling and detransitivization.

## References

* [song-1996]
* [comrie-1989]
-/

@[expose] public section

namespace Song1996

open Causation.Morphological (CausativeComplexity causeeDemotion)

/-! ### Forms and types (chapter 2) -/

/-- How [Vcause] is realized in a one-clause causative (§2.3): fused with [Veffect] beyond
morphological analysis (English *kill*), bound to it (Turkish *-dür*), or a free verb beside it
(French *faire*). -/
inductive Vcause where
  | fused
  | bound
  | free
  deriving DecidableEq, Repr, Fintype

/-- The term joining the two clauses of a biclausal causative is AND, a coordinator or nothing,
the order of the clauses registering their sequence (§2.4), or PURP, a marker of goal or purpose
on the clause of effect (§2.5). -/
inductive Link where
  | and_
  | purp
  deriving DecidableEq, Repr, Fintype

/-- The order of the clause of cause and the clause of effect. -/
inductive ClauseOrder where
  | causeEffect
  | effectCause
  deriving DecidableEq, Repr, Fintype

/-- A causative construction's form, in Song's operating terms (§2.2), is [Vcause] and [Veffect]
in one clause, or a clause of cause and a clause of effect joined by a link. -/
inductive Form where
  | oneClause (v : Vcause)
  | twoClauses (link : Link) (order : ClauseOrder)
  deriving DecidableEq, Repr

/-- The three types of causative construction; the names are mnemonic (p. 9). -/
inductive CausativeType where
  | compact
  | and_
  | purp
  deriving DecidableEq, Repr

namespace Form

/-- The type of a form follows the schemas (3), (29) and (60). One clause is COMPACT whatever
the order of [Vcause] and [Veffect], a clause of purpose makes PURP in either order of the
clauses, and coordinated clauses make AND only with the clause of cause first, their order being
fixed (p. 35). -/
def type : Form → Option CausativeType
  | oneClause _ => some .compact
  | twoClauses .purp _ => some .purp
  | twoClauses .and_ .causeEffect => some .and_
  | twoClauses .and_ .effectCause => none

/-- The class of a form in the traditional typology, on [comrie-1989]'s scale (§1.1, p. 135):
lexical when [Vcause] and [Veffect] are fused, morphological when [Vcause] is bound or a free verb
forming one unit with [Veffect], syntactic when they stand in different clauses. -/
def traditional : Form → CausativeComplexity
  | oneClause .fused => .lexical
  | oneClause .bound => .morphological
  | oneClause .free => .morphological
  | twoClauses _ _ => .periphrastic

/-- The COMPACT type is the traditional lexical and morphological types together (p. 9). -/
theorem type_eq_compact_iff {f : Form} :
    f.type = some .compact ↔ f.traditional ≠ .periphrastic := by
  cases f with
  | oneClause v => cases v <;> decide
  | twoClauses l o => cases l <;> cases o <;> decide

/-- The form of an example, as Song describes it. -/
def ofRow (e : Datum) : Option Form :=
  match e.feature? "clauses" with
  | some "one" => oneClause <$> e.parse? "vcause" [("fused", .fused), ("bound", .bound),
      ("free", .free)]
  | some "two" => twoClauses <$> e.parse? "link" [("AND", .and_), ("PURP", .purp)] <*>
      e.parse? "order" [("cause-effect", .causeEffect), ("effect-cause", .effectCause)]
  | _ => none

end Form

/-- Song's typology does not refine the traditional one: English *kill* (1.b) and Turkish
*öl-dür* (2.b) are both COMPACT, the one lexical and the other morphological (pp. 3, 9). -/
theorem not_factorsThrough_type : ¬ Function.FactorsThrough Form.traditional Form.type :=
  fun h ↦ absurd (h (a := (Form.ofRow Examples.ex_1b).get (by decide))
    (b := (Form.ofRow Examples.ex_2b).get (by decide)) (by decide)) (by decide)

/-- The traditional typology does not refine Song's: Vata *le* (5) and Korean *-ke* (3.b) are
both syntactic, the one AND and the other PURP (p. 10). -/
theorem not_factorsThrough_traditional : ¬ Function.FactorsThrough Form.type Form.traditional :=
  fun h ↦ absurd (h (a := (Form.ofRow Examples.ex_5).get (by decide))
    (b := (Form.ofRow Examples.ex_3b).get (by decide)) (by decide)) (by decide)

/-! ### Implicativity and the cognitive structure of causation (chapter 5) -/

/-- The stages of the cognitive structure of causation are, in their temporal order (10), the
perception of a desire or wish (GOAL), the deliberate attempt to realize it (EVENT), and its
accomplishment (RESULT). -/
inductive Stage where
  | goal
  | event
  | result
  deriving DecidableEq, Repr, Fintype

section Meaning

variable {W : Type*}

/-- The proposition a stage contributes, given the causer's goal that the effect come about, the
causing event, and the effect. -/
def Stage.prop (goal event effect : Set W) : Stage → Set W
  | .goal => goal
  | .event => event
  | .result => effect

/-- The semantic structure of the type a link forms (11) is EVENT and RESULT for the AND type and
GOAL and EVENT for the PURP type. -/
def Link.stages : Link → Finset Stage
  | .and_ => {.event, .result}
  | .purp => {.goal, .event}

/-- A biclausal causative asserts every stage its semantic structure expresses. -/
def Link.meaning (l : Link) (goal event effect : Set W) : Set W :=
  l.stages.inf (Stage.prop goal event effect)

/-- Both types express the causer's attempt, without which there is no causation (pp. 142–143). -/
theorem event_mem_stages (l : Link) : Stage.event ∈ l.stages := by
  cases l <;> decide

/-- A biclausal type entails its effect in every model iff it expresses RESULT (p. 142). -/
theorem forall_meaning_subset_iff (l : Link) :
    (∀ (W : Type) (goal event effect : Set W), l.meaning goal event effect ⊆ effect) ↔
      Stage.result ∈ l.stages := by
  refine ⟨fun h ↦ by_contra fun hr ↦ ?_, fun hr W goal event effect ↦ Finset.inf_le hr⟩
  have htop : l.meaning (W := Unit) Set.univ Set.univ ∅ = Set.univ :=
    (Finset.inf_eq_top_iff _ _).2 fun s hs ↦ by cases s <;> first | rfl | exact absurd hs hr
  exact (h Unit Set.univ Set.univ ∅ (by rw [htop]; trivial) : () ∈ (∅ : Set Unit))

/-- The AND type is fully implicative (p. 136). -/
theorem and_meaning_subset (goal event effect : Set W) :
    Link.and_.meaning goal event effect ⊆ effect :=
  Finset.inf_le (by decide : Stage.result ∈ Link.and_.stages)

/-- The prototypical PURP type is nonimplicative (p. 136). -/
theorem purp_not_implicative :
    ¬ ∀ (W : Type) (goal event effect : Set W), Link.purp.meaning goal event effect ⊆ effect :=
  fun h ↦ absurd ((forall_meaning_subset_iff .purp).1 h) (by decide)

/-- Under assumption (19), a causative of either type entails its effect, the PURP type by the
inference from (20) to (21) (§5.4). -/
theorem meaning_subset_of_success (l : Link) {goal event effect : Set W}
    (h : goal ∩ event ⊆ effect) : l.meaning goal event effect ⊆ effect := by
  cases l
  · exact and_meaning_subset goal event effect
  · simpa [Link.meaning, Link.stages, Stage.prop] using h

end Meaning

/-- Denying the effect of a biclausal causative is acceptable iff its link lacks RESULT, as for the
PURP causatives (7) (pp. 12–13) and ch. 4 (11). -/
theorem effectNegated_rows : ∀ e ∈ Examples.all, e.feature? "effect" = some "negated" →
    ∀ l o, Form.ofRow e = some (.twoClauses l o) →
      (e.judgment = .acceptable ↔ Stage.result ∉ l.stages) := by
  decide +kernel

/-- Every example that records its clauses has a form, and every example with its effect denied
records them, so that `effectNegated_rows` reads each such row. -/
example : ∀ e ∈ Examples.all, ((e.feature? "clauses").isSome → (Form.ofRow e).isSome) ∧
    (e.feature? "effect" = some "negated" → (e.feature? "clauses").isSome) := by
  decide +kernel

/-- The PURP causative (7) meets the premises of `effectNegated_rows`. -/
example : Examples.ex_7.feature? "effect" = some "negated" ∧
    Form.ofRow Examples.ex_7 = some (.twoClauses .purp .effectCause) := by decide +kernel

/-- Compactness does not settle implicativity, since denying the effect is contradictory for English
*kill* (6) and acceptable for Kammu *p-* (104) (§2.6; Figure 5.2, points A and B). -/
theorem compact_implicativity_varies : ∃ e₁ ∈ Examples.all, ∃ e₂ ∈ Examples.all,
    e₁.feature? "effect" = some "negated" ∧ e₂.feature? "effect" = some "negated" ∧
    (Form.ofRow e₁).bind Form.type = some .compact ∧
    (Form.ofRow e₂).bind Form.type = some .compact ∧
    e₁.judgment = .ungrammatical ∧ e₂.judgment = .acceptable :=
  ⟨Examples.ex_6, by simp [Examples.all], Examples.ex_104, by simp [Examples.all],
    by decide +kernel⟩

/-! ### Korean (chapter 4) -/

/-- Korean has a lexical, a morphological and a syntactic causative, the first two COMPACT and the
third PURP (§4.2 (1)–(3)). -/
theorem korean_types :
    [Examples.ch4_1b, Examples.ch4_2b, Examples.ch4_3].map (fun e ↦
        (Form.ofRow e).map fun f ↦ (f.traditional, f.type)) =
      [some (.lexical, some .compact), some (.morphological, some .compact),
        some (.periphrastic, some .purp)] := by
  decide +kernel

/-- *ha-* takes its clause of effect in every diathesis, so (3) without its clause is out (6) while
(4) without its clause stands (7) (§4.2). -/
theorem clause_omitted_rows : (∀ fr ∈ Korean.ha.valency.frames, fr.HasClausal) ∧
    ∀ e ∈ Examples.all, e.feature? "clause" = some "omitted" →
      (e.judgment = .acceptable ↔ e.feature? "construction" = some "purposive") := by
  decide +kernel

/-- The causative (6) and the purposive (7) meet the premises of `clause_omitted_rows`. -/
example : Examples.ch4_6.feature? "clause" = some "omitted" ∧
    Examples.ch4_6.feature? "construction" = some "PURP causative" ∧
    Examples.ch4_7.feature? "clause" = some "omitted" ∧
    Examples.ch4_7.feature? "construction" = some "purposive" := by
  decide +kernel

/-- The diathesis of `Korean.ha` that a long causative realizes, by Song's name for the
construction. -/
def haDiathesis? (e : Datum) : Option (Diathesis 3) :=
  e.parse? "construction"
    [("PURP causative", Korean.purpCausative), ("complement causative", Korean.complementCausative)]

/-- The causee of a long causative is nominative iff no participant of *ha-* controls the clause of
effect (§4.2 (3), (5), (8), (11); §4.6). -/
theorem causee_rows : Korean.ha.valency.diatheses = [Korean.purpCausative,
      Korean.complementCausative] ∧ Korean.purpCausative.controllerRole = some .P ∧
    ∀ e ∈ Examples.all, ∀ d ∈ haDiathesis? e, ∀ c ∈ e.feature? "causee",
      e.judgment = .acceptable → (c = "NOM" ↔ d.controller = none) := by
  decide +kernel

/-- The PURP causative (3) and the complement causative (5) meet the premises of `causee_rows`,
the one with a dative causee and the other with a nominative one. -/
example : haDiathesis? Examples.ch4_3 = some Korean.purpCausative ∧
    Examples.ch4_3.feature? "causee" = some "DAT" ∧
    haDiathesis? Examples.ch4_5 = some Korean.complementCausative ∧
    Examples.ch4_5.feature? "causee" = some "NOM" := by
  decide +kernel

/-- The subject of a clause of purpose is nominative only (§4.2 (4), (9), (10)). -/
theorem purposive_subject_rows : ∀ e ∈ Examples.all,
    e.feature? "construction" = some "purposive" → ∀ c ∈ e.feature? "subject",
      (e.judgment = .acceptable ↔ c = "NOM") := by
  decide +kernel

/-- The purposives (4) and (9) meet the premises of `purposive_subject_rows`, with a nominative
and an accusative subject. -/
example : Examples.ch4_4.feature? "construction" = some "purposive" ∧
    Examples.ch4_4.feature? "subject" = some "NOM" ∧
    Examples.ch4_9_acc.feature? "construction" = some "purposive" ∧
    Examples.ch4_9_acc.feature? "subject" = some "ACC" := by
  decide +kernel

/-! ### NP density control and the case hierarchy (chapter 6) -/

/-- The core NPs of the paradigm causative of [comrie-1989]'s case hierarchy on a base of valency
`v`: the causer, the base's other arguments keeping their relations, and the causee unless the
hierarchy makes it an oblique, which is no core NP (p. 178). -/
def paradigmCoreNPs (v : ℕ) : ℕ :=
  v + if causeeDemotion v = .oblique then 0 else 1

/-- The paradigm causative of a base of valency 1 to 3 has at most three core NPs (p. 175). -/
theorem paradigmCoreNPs_le_three {v : ℕ} (hv : v ∈ Set.Icc 1 3) : paradigmCoreNPs v ≤ 3 := by
  obtain ⟨h₁, h₃⟩ := hv
  interval_cases v <;> decide

/-- In a language capped at two core NPs, the paradigm causative of a transitive base exceeds the
cap (§6.4, p. 174). -/
theorem paradigmCoreNPs_two : causeeDemotion 2 = .indirectObject ∧ 2 < paradigmCoreNPs 2 := by
  decide

/-- Causative productivity declines with the valency of the base (p. 172). -/
theorem isLowerSet_setOf_add_one_le (n : ℕ) : IsLowerSet {v : ℕ | v + 1 ≤ n} :=
  fun _ _ h h' ↦ le_trans (Nat.add_le_add_right h 1) h'

end Song1996
