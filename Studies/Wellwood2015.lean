module

public import Linglib.Core.Algebra.Order.Group.Indicator
public import Linglib.Semantics.Composition.Interpreter.Constituency
public import Linglib.Semantics.Composition.Interpreter.Rules
public import Linglib.Semantics.Composition.Interpreter.Sorts
public import Linglib.Semantics.Composition.Interpreter.PredicateAbstraction
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
and the paper's derivations are one tree interpreted by Heim and Kratzer's rules at three
lexical cells, measuring coffee, running events or heat states. What *much* measures must be
non-trivially ordered by part-whole structure, which a quantized domain is not, and measured
monotonically, [in the strict sense](##monotoneOn_and_not_strictMonoOn) that excludes temperature
for portions of coffee. Which dimensions a comparative allows follows from what is measured and
how it is ordered rather than from the category of the measuring word, and on the paper's truth
conditions [each of two compared things is more than the other under some
dimension](##incompRel_iff_exists_comparativeTruth) exactly when neither is part of the other.
The obligatory *much* of *very* with nouns and verbs is Bresnan's Much Deletion.

## Implementation notes

Degrees form an abstract preordered type, linearly ordered for the derivation and a nontrivial
linearly ordered additive group where dimensions are compared. Eventualities are an abstract type,
the eventuality sort `v` beside the individuals of `e`, as in the paper's sorted domains `D_e` and
`D_v`, and the degree phrase modifies the base predicate by predicate modification at `⟨v,t⟩`,
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

/-! ### The derivation, type-driven -/

section TypeDriven

open Interpreter Interpreter.Grammar
open PhraseStructure (Tree)

variable {Ent α D : Type}

/-- The words of the derivation: the degree heads *-er* and *abs*, a standard, the base
predicate, the role head, the subject, and existential closure. *Much* is an indexed
expression. -/
inductive Word
  | er
  | abs
  | standard
  | pred
  | role
  | subj
  | closure

/-- The lexical items by type: *-er* and *abs* take a measure and a degree ((27i), (38ii)), the
base predicate is of events, the role head relates an individual to them (34), and *much* with
its index is a measure of them (7). -/
inductive Item : Ty Base → Type
  | er : Item ((.v ⇒ .d) ⇒ .d ⇒ .vt)
  | abs : Item ((.v ⇒ .d) ⇒ .d ⇒ .vt)
  | standard : Item .d
  | pred : Item .vt
  | role : Item .evt
  | subj : Item .e
  | closure : Item (.vt ⇒ .t)
  | much (n : ℕ) : Item (.v ⇒ .d)

/-- The item of a word, and of the index of *much*. -/
def items : Word ⊕ ℕ → List (Σ a, Item a)
  | .inl .er => [⟨_, .er⟩]
  | .inl .abs => [⟨_, .abs⟩]
  | .inl .standard => [⟨_, .standard⟩]
  | .inl .pred => [⟨_, .pred⟩]
  | .inl .role => [⟨_, .role⟩]
  | .inl .subj => [⟨_, .subj⟩]
  | .inl .closure => [⟨_, .closure⟩]
  | .inr n => [⟨_, .much n⟩]

/-- The domains: individuals, the degrees `D`, and what is measured as the eventualities. -/
abbrev Dom (Ent α D : Type) : Base → Type :=
  Base.Dom Ent Unit { degree := D, eventuality := α }

/-- Every index is of the type of a measure: the assignment supplies the measure of *much*. -/
abbrev indexTy : ℕ → Ty Base := fun _ ↦ .v ⇒ .d

/-- The denotations: *-er* and *abs* are the strict and the weak comparison of a measure with a
degree, and *much* with index `n` is the measure the assignment gives `n`. -/
def Item.val [LinearOrder D] (role : Ent → α → Prop) (P : α → Prop) (subj : Ent) (δ : D) :
    {a : Ty Base} → Item a → (∀ n, (indexTy n).Dom (Dom Ent α D)) → a.Dom (Dom Ent α D)
  | _, .er => fun _ m d e ↦ d < m e
  | _, .abs => fun _ m d e ↦ d ≤ m e
  | _, .standard => fun _ ↦ δ
  | _, .pred => fun _ ↦ P
  | _, .role => fun _ ↦ role
  | _, .subj => fun _ ↦ subj
  | _, .closure => fun _ p ↦ ∃ e, p e
  | _, .much n => fun g ↦ g n

/-- The grammar: Functional Application, Predicate Modification, at ⟨v,t⟩ as at ⟨e,t⟩, and
Event Identification, with indexed expressions. -/
abbrev grammar : Grammar (Ty Base) :=
  ((Grammar.application.sum .predicateModification).sum
    (.eventIdentification .e .v)).withAbstraction indexTy

/-- The denotations of a tree, relative to an assignment of measures to indices. -/
def meanings [LinearOrder D] (role : Ent → α → Prop) (P : α → Prop) (subj : Ent) (δ : D)
    (t : Tree Unit Word) :
    List (Σ a : Ty Base, (∀ n, (indexTy n).Dom (Dom Ent α D)) → a.Dom (Dom Ent α D)) :=
  t.values ((typeDriven ((Grammar.application.sum .predicateModification).sum
      (.eventIdentification .e .v))).withAbstraction indexTy)
    (Grammar.withAbstraction.structure (Assignments.total (Dom Ent α D) indexTy))
    (Item.val role P subj δ) items

/-- In the matrix tree, (36), (44), (60), the degree phrase modifies the base predicate, the role
head adds the subject, and the event variable is closed. -/
def matrixTree : Tree Unit Word :=
  .bin (.leaf .closure) (.bin (.leaf .subj) (.bin (.leaf .role)
    (.bin (.leaf .pred) (.bin (.bin (.leaf .er) (.tr 0)) (.leaf .standard)))))

/-- The than-clause body, (39), (46), (62), is the matrix tree with *abs* for *-er*. -/
def thanTree : Tree Unit Word :=
  .bin (.leaf .closure) (.bin (.leaf .subj) (.bin (.leaf .role)
    (.bin (.leaf .pred) (.bin (.bin (.leaf .abs) (.tr 0)) (.leaf .standard)))))

/-- The rules derive the matrix clause (37), (45), (61), with the measure the assignment gives
*much*. -/
theorem meanings_matrixTree [LinearOrder D] (role : Ent → α → Prop) (P : α → Prop) (a : Ent)
    (δ : D) :
    meanings role P a δ matrixTree = [⟨.t, fun g ↦ matrixClause role P (g 0) a δ⟩] :=
  rfl

-- (40), (47), (63)
theorem meanings_thanTree [LinearOrder D] (role : Ent → α → Prop) (P : α → Prop) (b : Ent)
    (d : D) :
    meanings role P b d thanTree = [⟨.t, fun g ↦ d ∈ thanClause role P (g 0) b⟩] :=
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
