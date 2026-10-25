module

public import Linglib.Logic.Team.QBSML.FreeChoice
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Data.Examples.AloniVanOrmondt2023
public import Mathlib.Tactic.DeriveFintype

/-!
# Aloni and van Ormondt (2023): modified numerals and split disjunction

Superlative modifiers (*at least n*, *at most n*) generate ignorance inferences
that comparative modifiers (*more than n*, *fewer than n*) do not, and the
inferences are obviated under universal quantifiers and modals, distribute
under universals, license free choice under modals, and vanish under negation
— exactly the profile of plain disjunction. Following Büring, superlative
modifiers are split disjunctions, `at least n ↦ n ∨ more` and
`at most n ↦ n ∨ less`, and the whole profile falls out of [aloni-2022]'s
neglect-zero enrichment `[·]⁺` once BSML is raised to the first-order QBSML.

The QBSML facts of §5 are the universal theorems of
`Logic/Team/QBSML/FreeChoice`; here the denotations (14) and (16) are the
split of the `≥` and `≤` intervals of `Degree.Comparison`, the
results (56)–(61) and (63) are those facts for the paper's `three`/`more`
predicates in every model, under the paper's side conditions, and the
obviation claim (57) is the Fig. 14 countermodel. Its worlds are, as
throughout the paper, the sets of atomic facts true at them: `w_{Pa}` is "the
world `w` in which some object `a` has property `P`" (Example 3.1, p. 549).
The example rows record the inference profile the analysis answers to.

## References

* [aloni-vanormondt-2023]
* [aloni-2022]
* [chemla-2009b]
-/

@[expose] public section

namespace AloniVanOrmondt2023

open QBSML Degree FirstOrder Language

/-! ### Superlative modifiers as disjunctions -/

/-- *At least n* means *exactly n or more than n*, (14). -/
theorem atLeast_eq_bare_union_moreThan (m : ℕ) :
    Comparison.ge.interval m = Comparison.eq.interval m ∪ Comparison.gt.interval m := by
  simp [Set.Ioi_insert]

/-- *At most n* means *exactly n or fewer than n*, (16). -/
theorem atMost_eq_bare_union_fewerThan (m : ℕ) :
    Comparison.le.interval m = Comparison.eq.interval m ∪ Comparison.lt.interval m := by
  simp [Set.Iio_insert]

/-- Superlative rows carry the ignorance inference in unembedded position and
    comparative rows never do (the contrast of (2)–(7)). -/
theorem modifier_rows :
    ∀ row ∈ Examples.all, ∀ m ∈ row.feature? "modifier", ∀ i ∈ row.feature? "inference",
      (m = "comparative" → i = "none") ∧
      (m = "superlative" → row.feature? "embedding" = none → i = "ignorance") := by
  decide +kernel

/-! ### The predicates -/

/-- `three` and `more` are the paper's numeral predicates; they instantiate the `P` and `Q`
    of the §5 facts. -/
inductive Predicate
  | three
  | more
  deriving DecidableEq, Repr, Fintype

inductive Var
  | x
  deriving DecidableEq, Repr, Fintype

variable {W Domain Const : Type*} [DecidableEq W] [DecidableEq Domain] [Fintype Domain]
  {M : Model W Domain Const Predicate} {s : Finset (Index W Var Domain)} {c : Const}

/-- `threeOrMore c` is `three ∨ more` (45b) said of the individual `c`. -/
def threeOrMore (c : Const) : Formula Var Const Predicate :=
  .disj (.predc .three c) (.predc .more c)

def three : Formula Var Const Predicate := .pred .three .x

def more : Formula Var Const Predicate := .pred .more .x

theorem three_neFree : (three (Const := Const)).NEFree := .pred _ _
theorem more_neFree : (more (Const := Const)).NEFree := .pred _ _

/-- By Proposition 4.1, a state supports the NE-free `∀x(three(x) ∨ more(x))` iff its
    first-order translation, computed by `rfl`, is true at every index. -/
theorem classicality_univ {v : Index W Var Domain → Var → Domain}
    (hv : ∀ i ∈ s, ∀ y, i.assign y = some (v i y)) :
    support M (.univ .x (.disj three more)) s ↔
      ∀ i ∈ s,
        (FirstOrder.Language.Formula.all₁ Var.x
          ((predSymb Predicate.three).formula₁ (FirstOrder.Language.Term.var Var.x) ⊔
            (predSymb Predicate.more).formula₁
              (FirstOrder.Language.Term.var Var.x))).RealizeAt
          M.interp i.world (v i) :=
  support_iff_forall_realizeAt M rfl s v hv

/-! ### The results (56)–(61) -/

/-- Ignorance (56), Fact 3, is `[three ∨ more]⁺ ⊨ ◇three ∧ ◇more` on a state-based
    accessibility relation, the paper's epistemic reading. -/
theorem ignorance (hSB : Team.IsStateBased M.access (State.worldProj s))
    (h : support M (threeOrMore c).enrich s) :
    support M (.poss (.predc .three c)) s ∧ support M (.poss (.predc .more c)) s :=
  QBSML.ignorance M hSB h

/-- At a state of maximal information, a single index, `[∀x(three(x) ∨ more(x))]⁺`
    supports `∃x three(x) ∧ ∃x more(x)`, the distribution of (51) (Fact 5). -/
theorem distribution {i : Index W Var Domain}
    (h : support M (Formula.univ .x (.disj three more)).enrich {i}) :
    support M (.exi .x three) {i} ∧ support M (.exi .x more) {i} :=
  QBSML.distribution M three_neFree more_neFree h

/-- Distribution under partial information (58), Fact 6, yields the modalized conclusion
    `∃x◇three(x) ∧ ∃x◇more(x)` on a state-based accessibility relation. -/
theorem distributionEpi (hSB : Team.IsStateBased M.access (State.worldProj s))
    (h : support M (Formula.univ .x (.disj three more)).enrich s) :
    support M (.exi .x (.poss three)) s ∧ support M (.exi .x (.poss more)) s :=
  QBSML.distributionEpi M hSB h

/-- Free choice under necessity (59), Fact 7, is `[□(three ∨ more)]⁺ ⊨ ◇three ∧ ◇more`. -/
theorem boxFreeChoice (h : support M (Formula.enrich (Formula.nec (threeOrMore c))) s) :
    support M (.poss (.predc .three c)) s ∧ support M (.poss (.predc .more c)) s :=
  QBSML.boxFC M (.predc _ _) (.predc _ _) h

/-- Free choice under possibility (60), Fact 8, is `[◇(three ∨ more)]⁺ ⊨ ◇three ∧ ◇more`. -/
theorem diamondFreeChoice (h : support M (Formula.enrich (.poss (threeOrMore c))) s) :
    support M (.poss (.predc .three c)) s ∧ support M (.poss (.predc .more c)) s :=
  QBSML.narrowScopeFC M (.predc _ _) (.predc _ _) h

/-- Universal free choice (63), Fact 9, is `[∀x◇(three(x) ∨ more(x))]⁺ ⊨
    ∀x◇three(x) ∧ ∀x◇more(x)`, the inference [chemla-2009b] attests. -/
theorem universalFreeChoice
    (h : support M (Formula.univ .x (.poss (.disj three more))).enrich s) :
    support M (.univ .x (.poss three)) s ∧ support M (.univ .x (.poss more)) s :=
  QBSML.universalFC M three_neFree more_neFree h

/-- Under negation the enrichment is inert, `[¬(three ∨ more)]⁺ ⊨ ¬three ∧ ¬more` ((61),
    Fact 10), so the simpler *fewer than three* blocks (61a). -/
theorem negation (h : support M (Formula.enrich (.neg (threeOrMore c))) s) :
    support M (.neg (.predc .three c)) s ∧ support M (.neg (.predc .more c)) s :=
  QBSML.negationStrip M (.predc _ _) (.predc _ _) h

/-! ### Obviation: the Fig. 14 countermodel

A single index at the world `w_{PaQb}` with the empty assignment; that world alone
sees itself. The domain is the paper's two objects, and a world is the set of
atomic facts true at it. -/

/-- `Entity` is the Fig. 14 domain of two objects, each its own individual constant. -/
inductive Entity
  | a
  | b
  deriving DecidableEq, Repr, Fintype

/-- `wPaQb` is the world `w_{PaQb}`, where `three` (the figure's `P`) holds of `a` and
    `more` (`Q`) holds of `b`. -/
def wPaQb : Finset (Predicate × Entity) := {(.three, .a), (.more, .b)}

/-- In the Fig. 14 model only `w_{PaQb}` has an arrow, to itself. -/
def fig14Model : Model (Finset (Predicate × Entity)) Entity Entity Predicate :=
  .ofMonadic (fun w ↦ if w = wPaQb then {wPaQb} else ∅) (fun _ ↦ id) fun w P d ↦ (P, d) ∈ w

def fig14Index : Index (Finset (Predicate × Entity)) Var Entity := (wPaQb, fun _ ↦ none)

def fig14State : Finset (Index (Finset (Predicate × Entity)) Var Entity) := {fig14Index}

/-- The accessibility is state-based on the Fig. 14 state, so obviation is not an
    artefact of dropping the frame condition behind ignorance. -/
theorem fig14_stateBased :
    Team.IsStateBased fig14Model.access (State.worldProj fig14State) := by decide

/-- As Fig. 15 shows, the universal extension splits into the `x/a` index supporting
    `[three(x)]⁺` and the `x/b` index supporting `[more(x)]⁺`. -/
theorem fig14_premise :
    support fig14Model (Formula.univ .x (.disj three more)).enrich fig14State := by
  refine ⟨?_, Finset.singleton_nonempty _⟩
  show support fig14Model (Formula.disj three more).enrich
    (State.extendUniversal fig14State Var.x)
  refine ⟨⟨{fig14Index.update .x .a}, ⟨?_, Finset.singleton_nonempty _⟩,
    {fig14Index.update .x .b}, ⟨?_, Finset.singleton_nonempty _⟩, ?_⟩,
    ⟨fig14Index.update .x .a, ?_⟩⟩
  · intro j hj
    obtain rfl := Finset.mem_singleton.mp hj
    exact ⟨.a, rfl, by simp [fig14Model, wPaQb, fig14Index, Index.world]⟩
  · intro j hj
    obtain rfl := Finset.mem_singleton.mp hj
    exact ⟨.b, rfl, by simp [fig14Model, wPaQb, fig14Index, Index.world]⟩
  · show ({fig14Index.update .x .a} ∪ {fig14Index.update .x .b} : Finset _)
      = State.extendUniversal fig14State Var.x
    decide
  · decide

/-- As Fig. 16 shows, at the `x/b` index the only accessible world is `w_{PaQb}`, where
    `three` holds of `a` alone, so `◇three(x)` fails. -/
theorem fig14_conclusion_fails :
    ¬ support fig14Model (.univ .x (.conj (.poss three) (.poss more))) fig14State := by
  intro h
  obtain ⟨X, hX, hne, hsupp⟩ := support_poss_iff.mp h.1 (fig14Index.update .x .b) (by decide)
  have hX' : X ⊆ {wPaQb} := by
    simpa [fig14Model, Model.ofMonadic, Index.update, fig14Index] using hX
  obtain rfl : X = {wPaQb} := hne.subset_singleton_iff.mp hX'
  obtain ⟨d, hd, hP⟩ := hsupp (wPaQb, (fig14Index.update .x .b).assign)
    (State.mem_modalLift.mpr ⟨Finset.mem_singleton_self _, rfl⟩)
  obtain rfl := Option.some.inj hd
  simp [fig14Model, wPaQb, Index.world] at hP

/-- The universal quantifier obviates ignorance, `[∀x(three(x) ∨ more(x))]⁺ ⊭
    ∀x(◇three(x) ∧ ◇more(x))` ((57), Fact 4). -/
theorem obviation :
    ∃ (M : Model (Finset (Predicate × Entity)) Entity Entity Predicate)
      (s : Finset (Index (Finset (Predicate × Entity)) Var Entity)),
      support M (Formula.univ .x (.disj three more)).enrich s ∧
        ¬ support M (.univ .x (.conj (.poss three) (.poss more))) s :=
  ⟨fig14Model, fig14State, fig14_premise, fig14_conclusion_fails⟩

end AloniVanOrmondt2023
