module

public import Linglib.Core.Algebra.Order.Group.Indicator
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
non-trivially ordered by part-whole structure, which a quantized domain is not, and measured
monotonically, [in the strict sense](##monotoneOn_and_not_strictMonoOn) that excludes temperature
for portions of coffee. Which dimensions a comparative allows follows from what is measured and
how it is ordered rather than from the category of the measuring word, and on the paper's truth
conditions [each of two compared things is more than the other under some
dimension](##incompRel_iff_exists_comparativeTruth) exactly when neither is part of the other.
The obligatory *much* of *very* with nouns and verbs is Bresnan's Much Deletion.

## Implementation notes

Degrees form an abstract preordered type, linearly ordered for the engine and a nontrivial linearly
ordered additive group where dimensions are compared. Eventualities are an abstract type, the
engine's eventuality sort `v` beside the individuals of `e`, as in the paper's sorted domains `D_e`
and `D_v`, and the degree phrase modifies the base predicate by predicate modification at `⟨v,t⟩`,
which the paper allows beside `⟨e,t⟩`. Existential closure is a lexical item. The paper's
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
open Degree

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
      Degree.scopeDegrees (Quantifier.Det.some {e | role b e ∧ P e})
        (Set.Iic ∘ fun e ↦ μ (extract e)) := by
    ext
    simp [thanClause, absDegP, Degree.mem_scopeDegrees, Quantifier.Det.some, Set.Nonempty,
      and_assoc]
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
theorem matrix_derivation_denotes {D : Type} [LinearOrder D] (role : Ent → α → Prop)
    (P : α → Prop) (μ0 : α → D) (a : Ent) (δ : D) (g : Assignment Ent) :
    interp (lexicon role P μ0 a δ) g matrixTree =
      some ⟨.t, pure (matrixClause role P μ0 a δ)⟩ :=
  rfl

-- (40), (47), (63)
theorem than_derivation_denotes {D : Type} [LinearOrder D] (role : Ent → α → Prop)
    (P : α → Prop) (μ0 : α → D) (b : Ent) (d : D) (g : Assignment Ent) :
    interp (lexicon role P μ0 b d) g thanTree =
      some ⟨.t, pure (d ∈ thanClause role P μ0 b)⟩ :=
  rfl

end TypeDriven

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

/-- A cumulative domain with two satisfiers is not quantized, since their sum has one of them as
a proper part. -/
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
