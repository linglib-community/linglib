module

public import Linglib.Semantics.Degree.Measure.Basic
public import Linglib.Semantics.Composition.Tree
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
of the than-clause, after von Stechow and Rullmann. The three domains share one truth condition,
and the paper's derivations are one tree interpreted by Heim and Kratzer's engine at three
lexical cells, measuring coffee, running events or heat states. What *much* measures must be
non-trivially ordered by part-whole structure and measured monotonically, which a quantized
domain cannot be. Which dimensions a comparative allows follows from what is measured rather
than from the category of the measuring word, and the obligatory *much* of *very* with nouns and
verbs is Bresnan's Much Deletion.

## Main definitions

* `comparativeTruth`: the cross-categorial truth condition of the comparative.
* `NontriviallyStructured`: a domain with a satisfier properly part of another.
* `MeasuredDomain.Model`: the order model of what a comparative measures.

## Implementation notes

Degrees are rationals and eventualities an abstract type, the engine's eventuality sort `v` beside
the individuals of `e`, as in the paper's sorted domains `D_e` and `D_v`, and the degree phrase
modifies the base predicate by predicate modification at `⟨v,t⟩`, which the paper allows beside
`⟨e,t⟩`. Existential closure is a lexical item. The order models of the measured domains are the
reals for states and the componentwise-ordered plane for entities and events. The bare-adjective,
measure-phrase and scalar-change discussions of the paper's objections section are not formalized.

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
open Degree

/-! ### The truth conditions -/

/-- The comparative, (42), (48), (65), holds when some eventuality bearing the role to `a` satisfies
`P` and measures strictly above the maximal than-clause degree of `b`. -/
def comparativeTruth {Ent α Measured : Type*} (role : Ent → α → Prop) (P : α → Prop)
    (extract : α → Measured) (μ : Measured → ℚ) (a b : Ent) : Prop :=
  MaxComparative .gt (fun e ↦ role a e ∧ P e) (fun e ↦ role b e ∧ P e) (fun e ↦ μ (extract e))

/-- The equative, (27ii), is the comparative with a weak comparison. -/
def equativeTruth {Ent α Measured : Type*} (role : Ent → α → Prop) (P : α → Prop)
    (extract : α → Measured) (μ : Measured → ℚ) (a b : Ent) : Prop :=
  MaxComparative .ge (fun e ↦ role a e ∧ P e) (fun e ↦ role b e ∧ P e) (fun e ↦ μ (extract e))

theorem comparativeTruth_entails_equativeTruth {Ent α Measured : Type*}
    (role : Ent → α → Prop) (P : α → Prop) (extract : α → Measured)
    (μ : Measured → ℚ) (a b : Ent) :
    comparativeTruth role P extract μ a b → equativeTruth role P extract μ a b :=
  MaxComparative.mono fun _ _ ↦ le_of_lt

/-! ### The derivation -/

section Derivation

variable {Ent α : Type*}

/-- The degree phrase with *-er*, (37i), sets a strict threshold on the measure. -/
def matrixDegP (μ : α → ℚ) (δ : ℚ) (e : α) : Prop := δ < μ e

/-- The degree phrase with *abs*, (38ii), sets a weak threshold. -/
def absDegP (μ : α → ℚ) (d : ℚ) (e : α) : Prop := d ≤ μ e

/-- The than-clause, (40), (41), denotes the degrees that some eventuality of `b`'s reaches. -/
def thanClause (role : Ent → α → Prop) (P : α → Prop) (μ : α → ℚ) (b : Ent) :
    Set ℚ :=
  {d | ∃ e, role b e ∧ P e ∧ absDegP μ d e}

/-- The matrix clause, (37viii), existentially closes the role, the predicate and the degree
phrase at the standard `δ`. -/
def matrixClause (role : Ent → α → Prop) (P : α → Prop) (μ : α → ℚ) (a : Ent)
    (δ : ℚ) : Prop :=
  ∃ e, role a e ∧ P e ∧ matrixDegP μ δ e

theorem derivation_eq_comparativeTruth {Measured : Type*} (role : Ent → α → Prop)
    (P : α → Prop) (extract : α → Measured) (μ : Measured → ℚ) (a b : Ent) :
    (∃ δ, IsGreatest (thanClause role P (fun e ↦ μ (extract e)) b) δ ∧
        matrixClause role P (fun e ↦ μ (extract e)) a δ) ↔
      comparativeTruth role P extract μ a b := by
  have : thanClause role P (fun e ↦ μ (extract e)) b =
      Degree.scopeDegrees (Quantifier.GQ.some fun e ↦ role b e ∧ P e)
        (Set.Iic ∘ fun e ↦ μ (extract e)) := by
    ext
    simp [thanClause, absDegP, Degree.scopeDegrees, Quantifier.GQ.some, and_assoc,
      Function.comp_apply]
  rw [this, Degree.scopeDegrees_some_Iic]
  simp only [comparativeTruth, MaxComparative, isGreatest_lowerClosure_iff, matrixClause,
    matrixDegP, Degree.Comparison.Rel, and_assoc]

end Derivation

/-! ### The derivation, type-driven -/

section TypeDriven

open PhraseStructure.Tree
open Montague
open PhraseStructure (Tree)

variable {Ent α : Type}

/-- In the lexicon *much* is the measure (7) of the eventualities, *-er* and *abs* the strict and
weak degree heads ((27i), (38ii)), the role head composes by event identification
([kratzer-1996]), and existential closure is an item. -/
def lexicon {D : Type} [LinearOrder D] (role : Ent → α → Prop) (P : α → Prop) (μ0 : α → D)
    (subj : Ent) (δ : D) : Lexicon Ent Unit Id { degree := D, eventuality := α } := fun w ↦
  match w with
  | "much" => some ⟨.v ⇒ .d, show α → D from μ0⟩
  | "er" => some ⟨(.v ⇒ .d) ⇒ .d ⇒ .v ⇒ .t,
      show (α → D) → D → α → Prop from fun m d e ↦ d < m e⟩
  | "abs" => some ⟨(.v ⇒ .d) ⇒ .d ⇒ .v ⇒ .t,
      show (α → D) → D → α → Prop from fun m d e ↦ d ≤ m e⟩
  | "δ" => some ⟨.d, show D from δ⟩
  | "pred" => some ⟨Ty.vt, show α → Prop from P⟩
  | "role" => some ⟨Ty.evt, show Ent → α → Prop from role⟩
  | "subj" => some ⟨.e, show Ent from subj⟩
  | "EC" => some ⟨Ty.vt ⇒ .t, show (α → Prop) → Prop from fun p ↦ ∃ e, p e⟩
  | _ => none

/-- In the matrix tree, (36), (44), (60), the degree phrase modifies the base predicate, the role
head adds the subject, and the event variable is closed. -/
def matrixTree : Tree Unit String :=
  .node () [.terminal () "EC",
    .node () [.terminal () "subj",
      .node () [.terminal () "role",
        .node () [.terminal () "pred",
          .node () [.node () [.terminal () "er", .terminal () "much"],
            .terminal () "δ"]]]]]

/-- The than-clause body, (39), (46), (62), is the matrix tree with *abs* for *-er*. -/
def thanTree : Tree Unit String :=
  .node () [.terminal () "EC",
    .node () [.terminal () "subj",
      .node () [.terminal () "role",
        .node () [.terminal () "pred",
          .node () [.node () [.terminal () "abs", .terminal () "much"],
            .terminal () "δ"]]]]]

/-- The engine derives the matrix clause (37), (45), (61). -/
theorem matrix_derivation_denotes (role : Ent → α → Prop) (P : α → Prop) (μ0 : α → ℚ)
    (a : Ent) (δ : ℚ) (g : Assignment Ent) :
    interp (lexicon role P μ0 a δ) g matrixTree =
      some ⟨.t, pure (matrixClause role P μ0 a δ)⟩ :=
  rfl

-- (40), (47), (63)
theorem than_derivation_denotes (role : Ent → α → Prop) (P : α → Prop) (μ0 : α → ℚ)
    (b : Ent) (d : ℚ) (g : Assignment Ent) :
    interp (lexicon role P μ0 b d) g thanTree =
      some ⟨.t, pure (d ∈ thanClause role P μ0 b)⟩ :=
  rfl

end TypeDriven

/-! ### The three domains -/

section Domains

variable {Entity E : Type*}

/-- The nominal comparative, (42), measures the theme of the agent's event. -/
def nominalComparative (frame : ThematicFrame Entity E) (P : E → Prop)
    (themeOf : E → Entity) (μ : Entity → ℚ) (a b : Entity) : Prop :=
  comparativeTruth frame.agent P themeOf μ a b

/-- The verbal comparative, (48), measures the agent's event itself. -/
def verbalComparative (frame : ThematicFrame Entity E) (P : E → Prop)
    (μ : E → ℚ) (a b : Entity) : Prop :=
  comparativeTruth frame.agent P id μ a b

/-- The adjectival comparative, (65), measures the holder's state itself. -/
def adjectivalComparative (frame : ThematicFrame Entity E) (P : E → Prop)
    (μ : E → ℚ) (a b : Entity) : Prop :=
  comparativeTruth frame.holder P id μ a b

end Domains

/-! ### What *much* measures (26) -/

section Structure

open Mereology

variable {α : Type*}

/-- A domain is non-trivially structured when some satisfier is a proper part of another. -/
def NontriviallyStructured [PartialOrder α] (P : α → Prop) : Prop :=
  ∃ x y, P x ∧ P y ∧ x < y

theorem not_nontriviallyStructured_of_qua [PartialOrder α] {P : α → Prop} (hQ : QUA P) :
    ¬ NontriviallyStructured P :=
  fun ⟨_, _, hx, hy, hlt⟩ ↦ hQ hx hy hlt.ne hlt.le

/-- A cumulative domain with two satisfiers is non-trivially structured, since their sum has one
of them as a proper part. -/
theorem nontriviallyStructured_of_cum [SemilatticeSup α] {P : α → Prop} (hC : CUM P) {x y : α}
    (hx : P x) (hy : P y) (hne : x ≠ y) : NontriviallyStructured P := by
  by_cases h : x < x ⊔ y
  · exact ⟨x, x ⊔ y, hx, hC hx hy, h⟩
  · have hle : y ≤ x := sup_eq_left.mp (le_sup_left.eq_of_not_lt h).symm
    exact ⟨y, x, hy, hx, lt_of_le_of_ne hle hne.symm⟩

theorem strictMonoOn_of_qua [PartialOrder α] {P : α → Prop} (hQ : QUA P) (μ : α → ℚ) :
    StrictMonoOn μ {x | P x} :=
  fun _ hx _ hy hlt ↦ absurd hlt.le (hQ hx hy hlt.ne)

theorem exists_lt_of_strictMonoOn [PartialOrder α] {P : α → Prop}
    (hP : NontriviallyStructured P) {μ : α → ℚ} (hμ : StrictMonoOn μ {x | P x}) :
    ∃ x y, P x ∧ P y ∧ μ x < μ y :=
  let ⟨x, y, hx, hy, hlt⟩ := hP
  ⟨x, y, hx, hy, hμ hx hy hlt⟩

end Structure

/-! ### Dimension tracks the measured domain (§3.4) -/

/-- A `MeasuredDomain` is what a comparative measures, entities, events, or states. -/
inductive MeasuredDomain
  | entity | event | state
  deriving DecidableEq, Repr

/-- In the order model of a measured domain states are linearly ordered, while entities and events
have incomparable parts, like coffee by weight and by volume. -/
abbrev MeasuredDomain.Model : MeasuredDomain → Type
  | .state => ℝ
  | .entity => ℝ × ℝ
  | .event => ℝ × ℝ

instance : (m : MeasuredDomain) → Preorder m.Model
  | .state => inferInstanceAs (Preorder ℝ)
  | .entity => inferInstanceAs (Preorder (ℝ × ℝ))
  | .event => inferInstanceAs (Preorder (ℝ × ℝ))

/-- Only the state domain fixes the comparative ordering for every admissible measure, so *hotter*
measures intensively and *fuller* extensively ((82)–(85)). -/
theorem model_restricted_iff :
    ∀ m : MeasuredDomain, DimensionallyRestricted m.Model ↔ m = .state
  | .state => iff_of_true (linearOrder_dimensionallyRestricted (α := ℝ)) rfl
  | .entity => iff_of_false prod_not_dimensionallyRestricted (by decide)
  | .event => iff_of_false prod_not_dimensionallyRestricted (by decide)

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
