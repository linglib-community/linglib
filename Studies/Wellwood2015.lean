module

public import Linglib.Core.Algebra.Order.Group.Indicator
public import Linglib.Semantics.Composition.Constituency
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Sorts
public import Linglib.Semantics.Composition.PredicateAbstraction
public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Mereology
public import Linglib.Semantics.ArgumentStructure.ThematicRole
public import Linglib.Data.Examples.Wellwood2015
public import Studies.Bresnan1973

/-!
# Wellwood (2015): On the Semantics of Comparison Across Categories

Wellwood proposes that nominal, verbal and adjectival comparatives contain one
degree-introducing morpheme, *much*, which denotes an assignment-supplied measure function, while
*-er* and *as* compare the measure of what the base predicate applies to with the maximal degree
of the than-clause, after von Stechow and Rullmann. The three comparatives are derived by one
set of rules, [measuring coffee](##Wellwood2015.meanings_nominalTree), [running
events](##Wellwood2015.meanings_verbalTree) or [heat
states](##Wellwood2015.meanings_adjectivalTree). What *much* measures must be
non-trivially ordered by part-whole structure, which a quantized domain is not, and measured
monotonically, [in the strict sense](##monotoneOn_and_not_strictMonoOn) that excludes temperature
for portions of coffee. Which dimensions a comparative allows follows from what is measured and
how it is ordered rather than from the category of the measuring word, and on the paper's truth
conditions [each of two compared things is more than the other under some
dimension](##incompRel_iff_exists_comparativeTruth) exactly when neither is part of the other.
The obligatory *much* of *very* with nouns and verbs is Bresnan's Much Deletion.

## Implementation notes

* Degrees form an abstract preordered type, linearly ordered for the derivations and a nontrivial
  linearly ordered additive group where dimensions are compared. Eventualities are an abstract
  type, the eventuality sort `v` beside the individuals of `e`, as in the paper's sorted domains
  `D_e` and `D_v`.
* The paper leaves open what closes the event variable; here a silent word does, at the top of
  the sentence and below the operator of the *than*-clause, where (40) has the closure.
* The maximal degree of *than* is the greatest member of its set, and an arbitrary degree where
  there is none; the silent determiner *e* is Hilbert's ε, as in the paper.
* *Much* carries index 1 where it measures individuals and index 2 where it measures
  eventualities, and the operator of the *than*-clause binds index 0; the paper's assignment
  gives one variable μ a measure of whichever type.
* `nominalComparative` measures the theme of the agent's event, where the paper's (42), derived
  here, measures the coffee its determiner chooses.

The paper's
non-trivially structured domains are the predicates that are not quantized, `¬ QUA P`. An
admissible measure is `StrictMono` on the type of what is measured, the ordered domain of (26), or
`StrictMonoOn` the satisfiers of a predicate. The bare-adjective, measure-phrase and scalar-change
discussions of the paper's objections section are not formalized.

## References

* [wellwood-2015]
* [bresnan-1973]
* [heim-kratzer-1998]
* [kratzer-1996]
* [rullmann-1995]
* [schwarzschild-2006]
* [von-stechow-1984]
-/

@[expose] public section

namespace Wellwood2015

open ArgumentStructure (ThematicFrame)

/-! ### The truth conditions -/

/-- The comparative, (42), (48), (65), holds when some eventuality bearing the role to `a` satisfies
`P` and measures strictly above the maximal than-clause degree of `b`. -/
def comparativeTruth {Ent α Measured D : Type*} [Preorder D] (role : Ent → α → Prop)
    (P : α → Prop) (extract : α → Measured) (μ : Measured → D) (a b : Ent) : Prop :=
  MaxComparative .gt (fun e ↦ role a e ∧ P e) (fun e ↦ role b e ∧ P e) (fun e ↦ μ (extract e))

/-- The equative, (27ii), is the comparative with a weak comparison. -/
def equativeTruth {Ent α Measured D : Type*} [Preorder D] (role : Ent → α → Prop)
    (P : α → Prop) (extract : α → Measured) (μ : Measured → D) (a b : Ent) : Prop :=
  MaxComparative .ge (fun e ↦ role a e ∧ P e) (fun e ↦ role b e ∧ P e) (fun e ↦ μ (extract e))

theorem comparativeTruth_entails_equativeTruth {Ent α Measured D : Type*} [Preorder D]
    (role : Ent → α → Prop) (P : α → Prop) (extract : α → Measured)
    (μ : Measured → D) (a b : Ent) :
    comparativeTruth role P extract μ a b → equativeTruth role P extract μ a b :=
  MaxComparative.mono fun _ _ ↦ le_of_lt

/-! ### The derivation -/

section Derivation

variable {Ent α D : Type*}

/-- The degree phrase with *-er*, (37i), sets a strict threshold on the measure. -/
def matrixDegP [LT D] (μ : α → D) (δ : D) (e : α) : Prop := δ < μ e

/-- The degree phrase with *abs*, (38ii), sets a weak threshold. -/
def absDegP [LE D] (μ : α → D) (d : D) (e : α) : Prop := d ≤ μ e

/-- The than-clause, (40), (41), denotes the degrees that some eventuality of `b`'s reaches. -/
def thanClause [LE D] (role : Ent → α → Prop) (P : α → Prop) (μ : α → D) (b : Ent) :
    Set D :=
  {d | ∃ e, role b e ∧ P e ∧ absDegP μ d e}

/-- The matrix clause, (37viii), existentially closes the role, the predicate and the degree
phrase at the standard `δ`. -/
def matrixClause [LT D] (role : Ent → α → Prop) (P : α → Prop) (μ : α → D) (a : Ent)
    (δ : D) : Prop :=
  ∃ e, role a e ∧ P e ∧ matrixDegP μ δ e

theorem derivation_eq_comparativeTruth {Measured : Type*} [PartialOrder D] (role : Ent → α → Prop)
    (P : α → Prop) (extract : α → Measured) (μ : Measured → D) (a b : Ent) :
    (∃ δ, IsGreatest (thanClause role P (fun e ↦ μ (extract e)) b) δ ∧
        matrixClause role P (fun e ↦ μ (extract e)) a δ) ↔
      comparativeTruth role P extract μ a b := by
  have : thanClause role P (fun e ↦ μ (extract e)) b =
      Quantifier.scopeDegrees (Quantifier.Det.some {e | role b e ∧ P e})
        (Set.Iic ∘ fun e ↦ μ (extract e)) := by
    ext
    simp [thanClause, absDegP, Quantifier.mem_scopeDegrees, Quantifier.Det.some, Set.Nonempty,
      and_assoc]
  rw [this, Quantifier.scopeDegrees_some_Iic]
  simp only [comparativeTruth, MaxComparative, isGreatest_lowerClosure_iff, matrixClause,
    matrixDegP, Comparison.Rel, and_assoc]

end Derivation

/-! ### The derivations

The paper's three comparatives, (35), (43) and (59), each with its *than*-clause in place: the
trees (36), (44) and (60) over (39), (46) and (62), by Functional Application, Predicate
Modification, Event Identification and Predicate Abstraction over the degree the operator of
the *than*-clause binds. -/

section Derivations

open Interpreter
open PhraseStructure (Tree)

/-- The maximal degree of a set of degrees (38i): its greatest member, and an arbitrary degree
where it has none. -/
noncomputable def maxDegree {D : Type} [LE D] [Nonempty D] (S : Set D) : D :=
  Classical.epsilon fun d ↦ IsGreatest S d

theorem maxDegree_eq {D : Type} [PartialOrder D] [Nonempty D] {S : Set D} {δ : D}
    (h : IsGreatest S δ) : maxDegree S = δ :=
  (Classical.epsilon_spec (p := fun d ↦ IsGreatest S d) ⟨δ, h⟩).unique h

/-- A model of the three sentences: the thematic relations, the predicates, and the
individuals. -/
structure Model (Ent Ev : Type) where
  agent : Ent → Ev → Prop
  holder : Ent → Ev → Prop
  drink : Ent → Ev → Prop
  coffee : Ent → Prop
  run : Ev → Prop
  hot : Ev → Prop
  al : Ent
  bill : Ent
  alsCoffee : Ent
  billsCoffee : Ent

/-- The words of (36), (39), (44), (46), (60) and (62). *Much* and the trace of the
*than*-clause's operator are indexed expressions. -/
inductive Word
  | al | bill | alsCoffee | billsCoffee
  /-- The head *v* that introduces the agent, and *v*ₛ that introduces the holder of a state. -/
  | v | vS
  | drank | coffee | run | hot
  /-- The silent indefinite determiner *e*. -/
  | e
  | er | abs | than
  /-- Existential closure of the event variable. -/
  | closure

/-- The lexical items by type. *-er* and *abs* (27i), (38ii) and *much* (28) measure individuals
or eventualities; the determiner *e* (32) is a choice of an individual; *than* (38i) takes a set
of degrees. -/
inductive Item : Ty Base → Type
  | al : Item .e
  | bill : Item .e
  | alsCoffee : Item .e
  | billsCoffee : Item .e
  | v : Item .evt
  | vS : Item .evt
  | drank : Item .evt
  | coffee : Item .et
  | run : Item .vt
  | hot : Item .vt
  | e : Item (.et ⇒ .e)
  | er (a : Ty Base) : Item ((a ⇒ .d) ⇒ .d ⇒ a ⇒ .t)
  | abs (a : Ty Base) : Item ((a ⇒ .d) ⇒ .d ⇒ a ⇒ .t)
  | than : Item ((.d ⇒ .t) ⇒ .d)
  | closure : Item (.vt ⇒ .t)
  | degree (n : ℕ) : Item .d
  | much (n : ℕ) (a : Ty Base) : Item (a ⇒ .d)

/-- The typing of the indices: the operator of the *than*-clause binds index 0, a degree, and
*much* has index 1 where it measures individuals and index 2 where it measures eventualities. -/
def indexTy : ℕ → Ty Base
  | 0 => .d
  | 1 => .e ⇒ .d
  | _ => .v ⇒ .d

/-- The items of a word, and of an index: *-er* and *abs* are of either sort of what is
measured. -/
def items : Word ⊕ ℕ → List (Σ a, Item a)
  | .inl .al => [⟨_, .al⟩]
  | .inl .bill => [⟨_, .bill⟩]
  | .inl .alsCoffee => [⟨_, .alsCoffee⟩]
  | .inl .billsCoffee => [⟨_, .billsCoffee⟩]
  | .inl .v => [⟨_, .v⟩]
  | .inl .vS => [⟨_, .vS⟩]
  | .inl .drank => [⟨_, .drank⟩]
  | .inl .coffee => [⟨_, .coffee⟩]
  | .inl .run => [⟨_, .run⟩]
  | .inl .hot => [⟨_, .hot⟩]
  | .inl .e => [⟨_, .e⟩]
  | .inl .er => [⟨_, .er .e⟩, ⟨_, .er .v⟩]
  | .inl .abs => [⟨_, .abs .e⟩, ⟨_, .abs .v⟩]
  | .inl .than => [⟨_, .than⟩]
  | .inl .closure => [⟨_, .closure⟩]
  | .inr 0 => [⟨_, .degree 0⟩]
  | .inr 1 => [⟨_, .much 1 .e⟩]
  | .inr (n + 2) => [⟨_, .much (n + 2) .v⟩]

variable {Ent Ev D : Type}

/-- The domains: individuals, the degrees `D`, and events and states together as the
eventualities. -/
abbrev Dom (Ent Ev D : Type) : Base → Type :=
  Base.Dom Ent Unit { degree := D, eventuality := Ev }

/-- An assignment gives each index a value of its type: index 0 a degree, the others a measure. -/
abbrev Assignment (Ent Ev D : Type) : Type := ∀ n, (indexTy n).Dom (Dom Ent Ev D)

/-- The denotations (27), (28), (31)–(34), (38), (57), (58). -/
noncomputable def Item.val [LinearOrder D] [Nonempty D] [Nonempty Ent] (M : Model Ent Ev) :
    {a : Ty Base} → Item a → Assignment Ent Ev D → a.Dom (Dom Ent Ev D)
  | _, .al => fun _ ↦ M.al
  | _, .bill => fun _ ↦ M.bill
  | _, .alsCoffee => fun _ ↦ M.alsCoffee
  | _, .billsCoffee => fun _ ↦ M.billsCoffee
  | _, .v => fun _ ↦ M.agent
  | _, .vS => fun _ ↦ M.holder
  | _, .drank => fun _ ↦ M.drink
  | _, .coffee => fun _ ↦ M.coffee
  | _, .run => fun _ ↦ M.run
  | _, .hot => fun _ ↦ M.hot
  | _, .e => fun _ P ↦ Classical.epsilon P
  | _, .er _ => fun _ m d x ↦ d < m x
  | _, .abs _ => fun _ m d x ↦ d ≤ m x
  | _, .than => fun _ S ↦ maxDegree {d | S d}
  | _, .closure => fun _ p ↦ ∃ e, p e
  | _, .degree 0 => fun g ↦ g 0
  | _, .degree (_ + 1) => fun g ↦ g 0
  | _, .much 1 .e => fun g ↦ g 1
  | _, .much (n + 2) .v => fun g ↦ g (n + 2)
  | _, .much _ _ => fun _ _ ↦ Classical.arbitrary D

/-- The rules: Functional Application, Predicate Modification, Event Identification, and
abstraction over an index. -/
abbrev rules : Interpreter (((application.sum predicateModification).sum
    (eventIdentification .e .v)).withAbstraction indexTy) ℕ :=
  (typeDriven ((application.sum predicateModification).sum
    (eventIdentification .e .v))).withAbstraction indexTy

/-- The denotations of a tree, relative to an assignment. -/
noncomputable def meanings [LinearOrder D] [Nonempty D] [Nonempty Ent] (M : Model Ent Ev)
    (t : Tree Unit Word) :
    List (Σ a : Ty Base, Assignment Ent Ev D → a.Dom (Dom Ent Ev D)) :=
  t.values rules (ManySorted.Language.withAbstraction.structure (Assignments.total (Dom Ent Ev D)
      indexTy))
    (Item.val M) items

/-- A *than*-clause (39), (46), (62): *than* over the operator's λ, the closed clause below it. -/
def thanP (clause : Tree Unit Word) : Tree Unit Word :=
  .bin (.leaf .than) (.binder 0 (.bin (.leaf .closure) clause))

/-- The degree phrase of a *than*-clause, `[tᵢ [much ABS]]`, with the index of *much*. -/
def absDegPTree (μ : ℕ) : Tree Unit Word := .bin (.tr 0) (.bin (.tr μ) (.leaf .abs))

/-- The degree phrase of a matrix clause, `[[much -er] thanP]`. -/
def erDegPTree (μ : ℕ) (than : Tree Unit Word) : Tree Unit Word :=
  .bin (.bin (.tr μ) (.leaf .er)) than

/-- The clause of (36) and (39) with a subject and a degree phrase:
`[subject [v [drank [e [coffee DegP]]]]]`. -/
def drankCoffee (subject degP : Tree Unit Word) : Tree Unit Word :=
  .bin subject (.bin (.leaf .v) (.bin (.leaf .drank) (.bin (.leaf .e)
    (.bin (.leaf .coffee) degP))))

/-- The clause of (44) and (46): `[subject [v [run DegP]]]`. -/
def ranClause (subject degP : Tree Unit Word) : Tree Unit Word :=
  .bin subject (.bin (.leaf .v) (.bin (.leaf .run) degP))

/-- The clause of (60) and (62): `[subject [vₛ [hot DegP]]]`. -/
def hotClause (subject degP : Tree Unit Word) : Tree Unit Word :=
  .bin subject (.bin (.leaf .vS) (.bin (.leaf .hot) degP))

/-- (35) *Al drank more coffee than Bill did*: (36) with (39) as its *than*-clause. -/
def nominalTree : Tree Unit Word :=
  .bin (.leaf .closure) (drankCoffee (.leaf .al)
    (erDegPTree 1 (thanP (drankCoffee (.leaf .bill) (absDegPTree 1)))))

/-- (43) *Al ran more than Bill did*: (44) with (46). -/
def verbalTree : Tree Unit Word :=
  .bin (.leaf .closure) (ranClause (.leaf .al)
    (erDegPTree 2 (thanP (ranClause (.leaf .bill) (absDegPTree 2)))))

/-- (59) *Al's coffee is hotter than Bill's is*: (60) with (62). -/
def adjectivalTree : Tree Unit Word :=
  .bin (.leaf .closure) (hotClause (.leaf .alsCoffee)
    (erDegPTree 2 (thanP (hotClause (.leaf .billsCoffee) (absDegPTree 2)))))

variable [LinearOrder D] [Nonempty D] [Nonempty Ent] (M : Model Ent Ev)

/-- (42): Al is the agent of a drinking of some coffee whose measure exceeds the maximal degree
that the measure of some coffee Bill drank reaches. The coffee is the determiner's choice. -/
theorem meanings_nominalTree :
    meanings (D := D) M nominalTree = [⟨.t, fun g ↦ ∃ e, M.agent M.al e ∧
      M.drink (Classical.epsilon fun x ↦ M.coffee x ∧
        maxDegree {d | ∃ e', M.agent M.bill e' ∧
          M.drink (Classical.epsilon fun y ↦ M.coffee y ∧ d ≤ g 1 y) e'} < g 1 x) e⟩] :=
  rfl

-- (48), (45), (47)
theorem meanings_verbalTree :
    meanings (D := D) M verbalTree = [⟨.t, fun g ↦
      matrixClause M.agent M.run (g 2) M.al (maxDegree (thanClause M.agent M.run (g 2) M.bill))⟩] :=
  rfl

-- (65), (61), (64)
theorem meanings_adjectivalTree :
    meanings (D := D) M adjectivalTree = [⟨.t, fun g ↦ matrixClause M.holder M.hot (g 2)
      M.alsCoffee (maxDegree (thanClause M.holder M.hot (g 2) M.billsCoffee))⟩] :=
  rfl

omit [Nonempty Ent] in
/-- Where the *than*-clause has a maximal degree, the verbal comparative (48) is the comparison
of the two agents' runnings by the measure the assignment gives *much*. -/
theorem verbalTree_iff_comparativeTruth (μ : Ev → D)
    (h : ∃ δ, IsGreatest (thanClause M.agent M.run μ M.bill) δ) :
    matrixClause M.agent M.run μ M.al (maxDegree (thanClause M.agent M.run μ M.bill)) ↔
      comparativeTruth M.agent M.run id μ M.al M.bill := by
  obtain ⟨δ, hδ⟩ := h
  rw [maxDegree_eq hδ, ← derivation_eq_comparativeTruth]
  exact ⟨fun hm ↦ ⟨δ, hδ, hm⟩, fun ⟨δ', hδ', hm⟩ ↦ hδ.unique hδ' ▸ hm⟩

end Derivations

/-! ### The three domains -/

section Domains

variable {Entity E D : Type*} [Preorder D]

/-- The nominal comparative, (42), measures the theme of the agent's event. -/
def nominalComparative (frame : ThematicFrame Entity E) (P : E → Prop)
    (themeOf : E → Entity) (μ : Entity → D) (a b : Entity) : Prop :=
  comparativeTruth frame.agent P themeOf μ a b

/-- The verbal comparative, (48), measures the agent's event itself. -/
def verbalComparative (frame : ThematicFrame Entity E) (P : E → Prop)
    (μ : E → D) (a b : Entity) : Prop :=
  comparativeTruth frame.agent P id μ a b

/-- The adjectival comparative, (65), measures the holder's state itself. -/
def adjectivalComparative (frame : ThematicFrame Entity E) (P : E → Prop)
    (μ : E → D) (a b : Entity) : Prop :=
  comparativeTruth frame.holder P id μ a b

end Domains

/-! ### What *much* measures (26) -/

section Structure

open Mereology

variable {α D : Type*} [Preorder D]

theorem not_qua_of_cum [SemilatticeSup α] {P : α → Prop} (hC : CUM P) {x y : α} (hx : P x)
    (hy : P y) (hne : x ≠ y) : ¬ QUA P := fun hQ ↦
  hne <| (hQ.eq hx (hC hx hy) le_sup_left).trans (hQ.eq hy (hC hx hy) le_sup_right).symm

theorem strictMonoOn_of_qua [PartialOrder α] {P : α → Prop} (hQ : QUA P) (μ : α → D) :
    StrictMonoOn μ {x | P x} :=
  fun _ hx _ hy hlt ↦ absurd hlt (hQ.not_lt hx hy)

/-- Monotonicity (15) must preserve the strict part-whole order: a measure on which every part
agrees with its whole, as temperature on a portion of coffee, preserves the weak order and is still
not monotonic on a domain that is not quantized. -/
theorem monotoneOn_and_not_strictMonoOn [PartialOrder α] {P : α → Prop} (hP : ¬ QUA P)
    {μ : α → D} (hμ : ∀ x y, P x → P y → x ≤ y → μ x = μ y) :
    MonotoneOn μ {x | P x} ∧ ¬ StrictMonoOn μ {x | P x} :=
  ⟨fun x hx y hy hxy ↦ (hμ x y hx hy hxy).le, fun h ↦
    hP (.of_strictMonoOn_antitoneOn h fun x hx y hy hxy ↦ (hμ x y hx hy hxy).ge)⟩

end Structure

/-! ### Dimensions -/

section Dimensions

variable {Ent α Measured D : Type*} [Preorder α] {role : Ent → α → Prop} {P : α → Prop}
  {extract : α → Measured} {a b : Ent} {xa xb : α}

-- Between greatest satisfiers, the comparative compares their measures.
theorem comparativeTruth_iff_of_isGreatest [Preorder D] {μ : Measured → D}
    (ha : IsGreatest {e | role a e ∧ P e} xa) (hb : IsGreatest {e | role b e ∧ P e} xb)
    (hμ : Monotone (μ ∘ extract)) :
    comparativeTruth role P extract μ a b ↔ μ (extract xb) < μ (extract xa) :=
  maxComparative_gt_iff_of_isGreatest ha (hμ.monotoneOn _) hb (hμ.monotoneOn _)

/-- On the truth conditions (42), (48) and (65), *a ran more than b* is true under one admissible
measure and *b ran more than a* under another, as with the duration and distance of (5b), exactly
when neither's greatest running is part of the other's; a nominal comparative measures the themes,
through a monotone theme map. -/
theorem incompRel_iff_exists_comparativeTruth [PartialOrder Measured] [AddCommGroup D]
    [LinearOrder D] [IsOrderedAddMonoid D] [Nontrivial D] (hext : Monotone extract)
    (ha : IsGreatest {e | role a e ∧ P e} xa) (hb : IsGreatest {e | role b e ∧ P e} xb)
    {μ₀ : Measured → D} (hμ₀ : StrictMono μ₀) :
    IncompRel (· ≤ ·) (extract xa) (extract xb) ↔
      (∃ μ : Measured → D, StrictMono μ ∧ comparativeTruth role P extract μ a b) ∧
        ∃ μ : Measured → D, StrictMono μ ∧ comparativeTruth role P extract μ b a :=
  hμ₀.incompRel_iff_exists_strictMono.trans <| and_comm.trans <| and_congr
    (exists_congr fun _ ↦ and_congr_right fun hμ ↦
      (comparativeTruth_iff_of_isGreatest ha hb (hμ.monotone.comp hext)).symm)
    (exists_congr fun _ ↦ and_congr_right fun hμ ↦
      (comparativeTruth_iff_of_isGreatest hb ha (hμ.monotone.comp hext)).symm)

-- On the plane over a linearly ordered additive group, the portions `(ε, 0)` and `(0, ε)`,
-- neither part of the other, are each more than the other under some dimension, and no dimension
-- makes the part `(0, 0)` more than `(ε, 0)`.
example {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] {ε : G} (hε : 0 < ε) :
    let role : G × G → G × G → Prop := fun a e ↦ e = a
    ((∃ μ : G × G → G, StrictMono μ ∧ comparativeTruth role (fun _ ↦ True) id μ (ε, 0) (0, ε)) ∧
      ∃ μ : G × G → G, StrictMono μ ∧ comparativeTruth role (fun _ ↦ True) id μ (0, ε) (ε, 0)) ∧
    ¬ ∃ μ : G × G → G, StrictMono μ ∧ comparativeTruth role (fun _ ↦ True) id μ (0, 0) (ε, 0) := by
  intro role
  have : Nontrivial G := ⟨0, ε, hε.ne⟩
  have hg (a : G × G) : IsGreatest {e | role a e ∧ True} a := ⟨⟨rfl, trivial⟩, fun _ h ↦ h.1.le⟩
  have hμ₀ : StrictMono fun p : G × G ↦ p.1 + p.2 := fun p q h ↦
    (Prod.lt_iff.1 h).elim (fun h ↦ add_lt_add_of_lt_of_le h.1 h.2)
      fun h ↦ add_lt_add_of_le_of_lt h.1 h.2
  refine ⟨(incompRel_iff_exists_comparativeTruth monotone_id (hg _) (hg _) hμ₀).1 ?_,
    fun ⟨μ, hμ, h⟩ ↦ ((comparativeTruth_iff_of_isGreatest (hg _) (hg _) hμ.monotone).1 h).asymm
      (hμ ?_)⟩ <;> simp [IncompRel, Prod.le_def, Prod.lt_iff, hε, hε.not_ge]

end Dimensions

/-! ### Much Deletion (§3.3, §6.3) -/

/-- [bresnan-1973]'s *-er* with *much* is the source of *more* in every domain. -/
def crossCategorialQP : Bresnan1973.QP := ⟨{ clitic := some .er }, .much⟩

theorem crossCategorialQP_suppletion : crossCategorialQP.suppletion = some .more := rfl

/-- *Much* deletes exactly before an adjective (74), so *very* needs *much* before a noun or verb
phrase ((117), (118)). -/
theorem very_much_deletion :
    Bresnan1973.MuchDeletes ⟨{}, .much⟩ .adjective ∧
      ¬ Bresnan1973.MuchDeletes ⟨{}, .much⟩ .noun ∧
      ¬ Bresnan1973.MuchDeletes ⟨{}, .much⟩ .phrase := by
  decide

end Wellwood2015
