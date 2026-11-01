module

public import Linglib.Core.Data.Fin.VecNotation
public import Linglib.Core.Data.Set.Image
public import Linglib.Logic.PIP.Felicity
public import Linglib.Logic.PIP.Intensional
public import Linglib.Data.Examples.KeshetAbney2024

/-!
# Keshet and Abney (2024): Intensional Anaphora

This file formalizes the account of anaphora under modals of [keshet-abney-2024]: a pronoun
presupposes that its antecedent description has a non-empty extension ((9)), and in the paper's
logic PIP (`Logic/PIP/Syntax.lean`) the antecedent description of a summation pronoun is a formula
label, so *Andrea might be eating a cheeseburger. #It is large.* ((79)) is
`might_w(ΣwE) ∧ E ≡ … ∧ large_w(ΣbE | single(ΣbE))`: the world variable of `E` is bound by the
summation inside *might* at its first use and by the discourse at the pronoun, so the pronoun's
description is evaluated at the discourse world and felicity ((83)) demands `single(ΣbE)` in
every world where Andrea might be eating one, including those where she is not
(`felicitous_discourseMight_iff`, `not_felicitous_burger`). With *must* ((88)–(90)) the realistic
modal base guarantees the description at the world of evaluation and the pronoun is fine
(`felicitous_discourseMust_of_realistic`), whereas a value-based presupposition of existence
would wrongly license *she* for the mayoral candidates of (85), who all exist. The unembedded
discourse (74) is felicitous ((78), `felicitous_plain`), and the bathroom disjunction (95) exactly
when a bathroom, if there is one, is unique ((97), `felicitous_bathroom_iff`). Read as a
trivalent connective, PIP's conjunction is neither Strong nor Weak Kleene (fn. 21,
`exists_toTrivalent_conj_ne_inf`, `exists_toTrivalent_conj_ne_meetWeak`), and a sentence extends
a felicitous discourse felicitously iff the discourse strictly implies the sentence's felicity
((51), `felicitous_sigma_conj_iff`).

## Implementation notes

The paper's felicity conditions (78), (83), (87), (90) and (97) quantify over worlds; the
statements here take a world of evaluation `w₀` and an assignment sending `w` to it, at the level
of a `Scenario` (accessibility, antecedent description, continuation) and its PIP model
`Scenario.model`. The modals are `Modal.apply` ((35)), the summation pronoun `Term.sgPronoun`
((71)), and the discourses `discourseMight` ((80b) with (82b)), `discourseMust` ((89)), `plain`
((75) with (76)) and `bathroom` ((95)), each expanded from its label by `Formula.expandSelf`.

## References

* [keshet-abney-2024]
* [peters-1979]
* [stone-1999]
* [brasoveanu-2010]
-/

@[expose] public section

namespace KeshetAbney2024

open PIP

/-- The variables of the discourses: the world `w`, the modal-base world `u`,
the antecedent's individual `b`. -/
inductive Var
  | w
  | u
  | b
  deriving DecidableEq

/-- The formula labels: the antecedent description `E`, and `X` of (95). -/
inductive Lab
  | E
  | X
  deriving DecidableEq

/-- Relation symbols, by number of non-world arguments: accessibility between
worlds, and the antecedent description and continuation of entities. -/
inductive Sym : ℕ → Type
  | acc : Sym 1
  | desc : Sym 1
  | cont : Sym 1

/-- Terms of the discourses. -/
abbrev Tm := Term Var Lab Sym

/-- Formulas of the discourses. -/
abbrev Fm := Formula Var Lab Sym

/-! ### Felicity

PIP's conjunction lets its first conjunct satisfy the presuppositions of its second ((42)). As a
trivalent connective it is Peters' Middle Kleene conjunction (`Formula.toTrivalent_conj`), and so
neither Strong nor Weak Kleene (fn. 21). A sentence extends a felicitous discourse felicitously
iff the discourse strictly implies the sentence's felicity ((48)–(51)). -/

section Felicity

variable {V L : Type*} {P : ℕ → Type*} [DecidableEq V] {α : Type*} (M : Model P α)
  (g : V → Set α)

/-- Conjunction is not Strong Kleene (fn. 21). -/
theorem exists_toTrivalent_conj_ne_inf : ∃ φ ψ : Formula V L P,
    Formula.toTrivalent M g (.conj φ ψ) ≠ φ.toTrivalent M g ⊓ ψ.toTrivalent M g := by
  obtain ⟨φ, hφ⟩ := Formula.toTrivalent_surjective (L := L) M g 0
  obtain ⟨ψ, hψ⟩ := Formula.toTrivalent_surjective (L := L) M g (-1)
  exact ⟨φ, ψ, by rw [Formula.toTrivalent_conj, hφ, hψ]; decide⟩

/-- Conjunction is not Weak Kleene (fn. 21). -/
theorem exists_toTrivalent_conj_ne_meetWeak : ∃ φ ψ : Formula V L P,
    Formula.toTrivalent M g (.conj φ ψ) ≠ (φ.toTrivalent M g).meetWeak (ψ.toTrivalent M g) := by
  obtain ⟨φ, hφ⟩ := Formula.toTrivalent_surjective (L := L) M g (-1)
  obtain ⟨ψ, hψ⟩ := Formula.toTrivalent_surjective (L := L) M g 0
  exact ⟨φ, ψ, by rw [Formula.toTrivalent_conj, hφ, hψ]; decide⟩

/-- Given a felicitous discourse `γ` ((48)), its extension by `φ` is felicitous iff `γ` strictly
implies the felicity of `φ` ((51)), where the local variables of `φ` not local to `γ` do not occur
in `γ`. -/
theorem felicitous_sigma_conj_iff {w : V} {γ φ : Formula V L P}
    (hγ : Expr.Felicitous M g (.sigma w γ)) (hφ : ∀ y ∈ φ.locals, y ∉ γ.locals → y ∉ γ.vars) :
    Expr.Felicitous M g (.sigma w (.conj γ φ)) ↔
      ∀ g', Set.EqOn g' g {y | y ∉ (Expr.conj γ φ).locals ∧ y ≠ w} →
        Formula.Realize M g' γ → φ.Felicitous M g' := by
  classical
  refine ⟨fun h g' hg => (h g' hg).2, fun h g' hg => ⟨?_, h g' hg⟩⟩
  refine (γ.felicitous_congr M (Set.piecewise_eqOn γ.vars g' g)).1
    ((Term.felicitous_sigma M g w γ).1 hγ _ fun y hy => ?_)
  by_cases hyγ : y ∈ γ.vars
  · rw [Set.piecewise_eq_of_mem _ _ _ hyγ]
    refine hg ⟨fun hl => ?_, hy.2⟩
    rcases List.mem_append.1 hl with hl | hl
    exacts [hy.1 hl, hφ y hl hy.1 hyγ]
  · rw [Set.piecewise_eq_of_notMem _ _ _ hyγ]

end Felicity

/-! ### Scenarios -/

variable {W E : Type}

/-- A scenario: accessibility between worlds, the antecedent description and
the continuation's predicate, each relative to a world. -/
structure Scenario (W E : Type) where
  acc : W → W → Prop
  desc : W → E → Prop
  cont : W → E → Prop

/-- The model of a scenario. -/
def Scenario.model (S : Scenario W E) : Model Sym (Atom W E) :=
  Model.intensional fun {_} r w as => match r with
    | .acc => as 0 ∈ Sum.inl '' {u | S.acc w u}
    | .desc => as 0 ∈ Sum.inr '' {e | S.desc w e}
    | .cont => as 0 ∈ Sum.inr '' {e | S.cont w e}

/-! ### The discourses -/

/-- `E ≡ desc_w([b]) ∧ single(b)`: the antecedent description of (80b),
with a bracketed local variable for the indefinite. -/
def descE : Fm := .conj (.atom .desc (.var .w) ![.bvar .b]) (.sg (.var .b))

/-- `acc(w, u)`: `u` is accessible from `w`. -/
def access : Fm := .atom .acc (.var .w) ![.var .u]

/-- `Σu acc(w, u)`: the modal base `β_w`. -/
def base : Tm := .sigma .u access

/-- The one-place modals (35): `might_w(Σwφ) = some(β_w, Σwφ)` and
`must_w(Σwφ) = every(β_w, Σwφ)`. -/
inductive Modal
  | might
  | must

/-- A modal applied to its base and its prejacent. -/
def Modal.apply : Modal → Tm → Tm → Fm
  | .might, β, ψ => Formula.some_ β ψ
  | .must, β, ψ => .subset β ψ

/-- `cont_w(Σbφ | single(Σbφ))`: the continuation (82b), with the summation pronoun
`Term.sgPronoun` (71). -/
def continuation (φ : Fm) : Fm := .atom .cont (.var .w) ![Term.sgPronoun .b φ]

/-- `modal_w(Σwφ) ∧ E ≡ desc_w([b]) ∧ single(b) ∧ cont_w(Σbφ | single(Σbφ))`. -/
def discourse (m : Modal) (φ : Fm) : Fm :=
  .conj (.conj (m.apply base (.sigma .w φ)) (.labelDef .E descE)) (continuation φ)

/-- (80b) ∧ (82b): "Andrea might be eating a cheeseburger. It is large." -/
def discourseMight : Fm := discourse .might (.label .E)

/-- (89): "There must be some sort of animal in the shed. It's making quite a
racket!" -/
def discourseMust : Fm := discourse .must (.label .E)

/-- (75) ∧ (76): "Andrea is eating a cheeseburger. It is large.", with the
simple pronoun `b | single(b)`. -/
def plain : Fm := .conj descE (.atom .cont (.var .w) ![.presup (.var .b) (.sg (.var .b))])

/-- (95): "Either there's no bathroom in this house or it's in a funny place.",
`(¬∃bX ∨ cont_w(ΣbX | single(ΣbX))) ∧ X ≡ desc_w([b]) ∧ single(b)`. -/
def bathroom : Fm :=
  .conj (Formula.disj (.neg (.exists_ .b (.label .X))) (continuation (.label .X)))
    (.labelDef .X descE)

/-! ### Label expansion -/

theorem expandSelf_discourseMight : discourseMight.expandSelf = discourse .might descE := by
  rw [Formula.expandSelf, show discourseMight.defs = [(.E, descE)] from rfl, Formula.expand]
  simp only [List.length_cons, Function.iterate_succ_apply', List.length_nil,
    Function.iterate_zero_apply, discourseMight, discourse, Modal.apply, Formula.some_,
    continuation, Term.sgPronoun, descE, access, base, Expr.substLabels, List.lookup_cons_self,
    Matrix.comp_vecCons', Matrix.comp_vecEmpty', Option.getD_some]

theorem expandSelf_discourseMust : discourseMust.expandSelf = discourse .must descE := by
  rw [Formula.expandSelf, show discourseMust.defs = [(.E, descE)] from rfl, Formula.expand]
  simp only [List.length_cons, Function.iterate_succ_apply', List.length_nil,
    Function.iterate_zero_apply, discourseMust, discourse, Modal.apply, continuation,
    Term.sgPronoun, descE, access, base, Expr.substLabels, List.lookup_cons_self,
    Matrix.comp_vecCons', Matrix.comp_vecEmpty', Option.getD_some]

theorem expandSelf_bathroom :
    bathroom.expandSelf =
      .conj (Formula.disj (.neg (.exists_ .b descE)) (continuation descE))
        (.labelDef .X descE) := by
  rw [Formula.expandSelf, show bathroom.defs = [(.X, descE)] from rfl, Formula.expand]
  simp only [List.length_cons, Function.iterate_succ_apply', List.length_nil,
    Function.iterate_zero_apply, bathroom, Formula.disj, continuation, Term.sgPronoun, descE,
    Expr.substLabels, List.lookup_cons_self, Matrix.comp_vecCons', Matrix.comp_vecEmpty',
    Option.getD_some]

/-! ### Values and felicity at a world of evaluation -/

variable (S : Scenario W E) (h : Var → Set (Atom W E)) {w₀ : W}

theorem felicitous_descE : descE.Felicitous S.model h :=
  Expr.felicitous_of_presupFree _ _ (by decide) _

theorem felicitous_access : access.Felicitous S.model h :=
  Expr.felicitous_of_presupFree _ _ (by decide) _

theorem realize_descE :
    descE.Realize S.model h ↔ ∃ w e, h .w = world w ∧ h .b = {Sum.inr e} ∧ S.desc w e := by
  simp only [descE, Formula.realize_conj, Formula.realize_atom, Formula.realize_sg,
    Matrix.comp_vecCons, Matrix.comp_vecEmpty, Term.realize_var, Term.realize_bvar, Scenario.model,
    Model.intensional_apply₁, Matrix.cons_val_zero]
  constructor
  · rintro ⟨⟨w, hw, -, hall⟩, a, ha⟩
    obtain ⟨e, he, rfl⟩ := hall a (by rw [ha]; exact Set.mem_singleton a)
    exact ⟨w, e, hw, ha, he⟩
  · rintro ⟨w, e, hw, hb, he⟩
    exact ⟨⟨w, hw, ⟨_, by rw [hb]; exact Set.mem_singleton _⟩,
      fun a ha => ⟨e, he, (by rw [hb] at ha; exact ha : a = _).symm⟩⟩, _, hb⟩

theorem realize_sigmaB_descE (hw : h .w = world w₀) :
    Term.realize S.model h (.sigma .b descE) = Sum.inr '' {e | S.desc w₀ e} :=
  Term.realize_sigma_eq_image S.model h fun g' hg => by
    rw [realize_descE, hg (by decide : Var.w ∈ _), hw]
    simp only [world_inj, exists_and_left, exists_eq_left', Set.mem_ofPred_eq]

theorem realize_sigmaW_descE :
    Term.realize S.model h (.sigma .w descE) = Sum.inl '' {w | ∃ e, S.desc w e} := by
  rw [Term.realize_sigma_world_eq S.model h (y := .b) (by decide)
    (B := fun X w => ∃ e, X = {Sum.inr e} ∧ S.desc w e)
    (fun g' _ => (realize_descE S g').trans (exists_congr fun _ => exists_and_left)) (by decide)]
  simp

theorem realize_base (hw : h .w = world w₀) :
    base.realize S.model h = Sum.inl '' {u | S.acc w₀ u} :=
  Term.realize_sigma_eq_of_distributive S.model h fun g' hg => by
    simp only [access, Formula.realize_atom, Matrix.comp_vecCons, Matrix.comp_vecEmpty,
      Term.realize_var, Scenario.model, Model.intensional_apply₁, Matrix.cons_val_zero,
      hg (by decide : Var.w ∈ _), hw, world_inj, exists_eq_left']
    rfl

theorem realize_might (hw : h .w = world w₀) :
    (Modal.apply .might base (.sigma .w descE)).Realize S.model h ↔
      ∃ u e, S.acc w₀ u ∧ S.desc u e := by
  rw [Modal.apply, Formula.realize_some, realize_base S h hw, realize_sigmaW_descE,
    ← Set.image_inter Sum.inl_injective, Set.image_nonempty]
  simp [Set.Nonempty]

theorem realize_must (hw : h .w = world w₀) :
    (Modal.apply .must base (.sigma .w descE)).Realize S.model h ↔
      ∀ u, S.acc w₀ u → ∃ e, S.desc u e := by
  rw [Modal.apply, Formula.realize_subset, realize_base S h hw, realize_sigmaW_descE,
    Set.image_subset_image_iff Sum.inl_injective]
  rfl

theorem felicitous_modal (m : Modal) :
    (m.apply base (.sigma .w descE)).Felicitous S.model h := by
  cases m <;> simp only [Modal.apply, Formula.felicitous_some, Formula.felicitous_subset, base,
    Term.felicitous_sigma_of_forall _ _ (felicitous_access S),
    Term.felicitous_sigma_of_forall _ _ (felicitous_descE S), and_self]

theorem felicitous_pronoun_iff (hw : h .w = world w₀) :
    (Term.sgPronoun .b descE).Felicitous S.model h ↔ ∃! e, S.desc w₀ e := by
  rw [Term.felicitous_sgPronoun, realize_sigmaB_descE S h hw,
    Sum.inr_injective.exists_image_eq_singleton_iff, Set.singleton_iff_unique_mem]
  exact and_iff_right (Term.felicitous_sigma_of_forall _ _ (felicitous_descE S))

theorem felicitous_continuation_iff (hw : h .w = world w₀) :
    (continuation descE).Felicitous S.model h ↔ ∃! e, S.desc w₀ e := by
  simp only [continuation, Formula.felicitous_atom, Term.felicitous_var, Fin.forall_fin_one,
    Matrix.cons_val_zero, true_and, felicitous_pronoun_iff S h hw]

theorem felicitous_discourse_iff (m : Modal) (hw : h .w = world w₀) :
    (discourse m descE).Felicitous S.model h ↔
      ((m.apply base (.sigma .w descE)).Realize S.model h → ∃! e, S.desc w₀ e) := by
  simp only [discourse, Formula.felicitous_conj, Formula.realize_conj, Formula.felicitous_labelDef,
    Formula.realize_labelDef, felicitous_modal, felicitous_continuation_iff S h hw, implies_true,
    and_true, true_and]

/-- With *might*, the discourse is felicitous at `w₀` iff accessible satisfiers imply a unique
satisfier at `w₀` (83). -/
theorem felicitous_discourseMight_iff (hw : h .w = world w₀) :
    discourseMight.expandSelf.Felicitous S.model h ↔
      ((∃ u e, S.acc w₀ u ∧ S.desc u e) → ∃! e, S.desc w₀ e) := by
  rw [expandSelf_discourseMight, felicitous_discourse_iff S h _ hw, realize_might S h hw]

-- (90)
theorem felicitous_discourseMust_iff (hw : h .w = world w₀) :
    discourseMust.expandSelf.Felicitous S.model h ↔
      ((∀ u, S.acc w₀ u → ∃ e, S.desc u e) → ∃! e, S.desc w₀ e) := by
  rw [expandSelf_discourseMust, felicitous_discourse_iff S h _ hw, realize_must S h hw]

/-- (88)–(90): a realistic modal base and the scalar implicature that a
satisfier is unique make the `must` discourse felicitous at every world. -/
theorem felicitous_discourseMust_of_realistic (hr : ∀ w, S.acc w w)
    (hu : ∀ w, (∃ e, S.desc w e) → ∃! e, S.desc w e) (hw : h .w = world w₀) :
    discourseMust.expandSelf.Felicitous S.model h :=
  (felicitous_discourseMust_iff S h hw).2 fun H => hu _ (H _ (hr _))

/-- (78): the unembedded discourse (74) is felicitous under every assignment,
the assertion `single(b)` satisfying the pronoun's presupposition. -/
theorem felicitous_plain : plain.Felicitous S.model h :=
  ⟨felicitous_descE S h, fun hd =>
    ⟨trivial, Fin.forall_fin_one.2 ⟨trivial, Fin.forall_fin_one.2 trivial, hd.2⟩⟩⟩

theorem felicitous_exists_descE : (Expr.exists_ .b descE).Felicitous S.model h :=
  fun g' _ => felicitous_descE S g'

theorem realize_exists_descE (hw : h .w = world w₀) :
    Formula.Realize S.model h (.exists_ .b descE) ↔ ∃ e, S.desc w₀ e := by
  simp only [Formula.realize_exists, realize_descE, Function.update_self,
    Function.update_of_ne (show Var.w ≠ .b by decide), hw, world_inj]
  constructor
  · rintro ⟨_, _, e, rfl, -, he⟩
    exact ⟨e, he⟩
  · rintro ⟨e, he⟩
    exact ⟨_, _, e, rfl, rfl, he⟩

/-- (97): the bathroom disjunction is felicitous at `w₀` iff a bathroom there,
if any, is unique. -/
theorem felicitous_bathroom_iff (hw : h .w = world w₀) :
    bathroom.expandSelf.Felicitous S.model h ↔
      ((∃ e, S.desc w₀ e) → ∃! e, S.desc w₀ e) := by
  rw [expandSelf_bathroom]
  simp only [Formula.felicitous_conj, Formula.felicitous_disj, Formula.felicitous_neg,
    Formula.felicitous_labelDef, Formula.realize_neg, not_not, felicitous_exists_descE,
    realize_exists_descE S h hw, felicitous_continuation_iff S h hw, implies_true, and_true,
    true_and]

/-! ### Possible burgers -/

/-- (79): at `false` Andrea is fasting and at `true` she is eating a
cheeseburger, and for all anyone knows at either world, either is actual. -/
def burger : Scenario Bool Unit where
  acc _ _ := True
  desc w _ := w = true
  cont _ _ := True

/-- (79) is infelicitous at the world where Andrea is fasting but might be
eating a cheeseburger: `ΣbE` is empty there. -/
theorem not_felicitous_burger (h : Var → Set (Atom Bool Unit)) (hw : h .w = world false) :
    ¬ discourseMight.expandSelf.Felicitous burger.model h := by
  rw [felicitous_discourseMight_iff burger h hw]
  intro H
  obtain ⟨_, h1⟩ := (H ⟨true, (), trivial, rfl⟩).exists
  exact Bool.false_ne_true h1

end KeshetAbney2024
