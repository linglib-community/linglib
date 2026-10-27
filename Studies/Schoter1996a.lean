module

public import Linglib.Data.Examples.Schoter1996a
public import Linglib.Logic.Trivalent.Four
public import Linglib.Logic.Bilattice.Guard
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card
public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Order.OrderIsoNat

/-!
# Schöter (1996a): The Computational Application of Bilattice Logic to Natural Reasoning

The thesis develops Evidential Bilattice Logic for natural reasoning and applies it to
presupposition. Its values are pairs of degrees of evidence for and against a proposition, over
the chain `0 < ½ < 1` the bilattice `PRESUP`. Evidential links pass evidence between sentences,
strict links at full strength and defeasible ones at `½`, and closure applies them strongest
first, so strict evidence overrides defeasible evidence and conflicting defaults leave the agent
confused.

Presupposition is a bundle of links, implication's two and a defeasible link from the negated
carrier, so a positive carrier entails its presupposition and a negative one presumes it.
Fitting's guard `φ : ψ`, read as `ψ` presupposing `φ`, encodes Burton-Roberts's truth-gap and
salient presuppositional intuitions, but the thesis rejects it: it makes denying the
presupposition a contradiction after a negative carrier as well as a positive one.

## Implementation notes

* The thesis writes a value as `⟨against, for⟩`; this file keeps the substrate's
  `(for, against)` order, so the thesis's `⟨a, b⟩` is `.mk b a` here.
* The formulas are those of a single setup: atoms, negation and the guard. A conjunction is
  asserted conjunct by conjunct (Definition 3.13, clause 3), so the examples join infons.
* The link set is the lexicon's, fixed in advance, where Definitions 3.17 and 3.20 add a
  predicate's links when a sentence of it is first asserted or queried; the two differ only for
  inferences chained through a sentence nothing mentions.
* The journal version condenses chapters 3 and 6: its Definitions 17, 27 and 29 are Definitions
  3.24, 6.1 and 6.5, its §4.1 is §3.7.3, and its (13) and (14) are (6.11) and (6.12).

## Errata

* Definition 3.8 makes `σᵢ(⟨a, b⟩)` true when `a ≤ b` and `i < b` (the journal version's
  Definition 17 also has `a < b`), but glosses it as evidence "at least as strong as `i`", and
  §3.7.3 passes the `½` evidence for John's adulthood on to his employment. Read strictly, no link
  could fire at the top level, a presumed antecedent would pass nothing on, and the weak Tweety
  triangle would come out `P⁻` rather than `C`. The file reads `σᵢ` with `i ≤ b`.
* §3.5.6 claims that an assertion with neither defeasible nor inconsistent components, such as
  `ψ ∧ ¬ψ`, is exactly true after closure in `E⊥`. The lexicon's links can still make it
  inconsistent: (6.12c) asserts `R ∧ ¬F` and both conjuncts come out `I`
  (`consistent_assertion_eq_I`). The weaker claim, at least true, holds in any state.

## TODO

* Epistemic states of several setups (Definition 3.27), disjunction and the pragmatic
  translations of §3.6, for the scalar implicatures of §6.2.2 and the compounds of §6.4;
  object-language links and evidential entailment (Definitions 3.14, 3.15, 3.30–3.32).

## References

* [schoter-1996a]
* [schoter-1996b]
* [fitting-1994]
* [ginsberg-1988]
* [belnap-1977]
* [burton-roberts-1989a]
-/

@[expose] public section

open Bilattice

namespace Schoter1996a

/-- The thesis's `PRESUP` (§3.2.2): the evidential bilattice over the 3-chain `Fin 3 ~ {0, ½, 1}`,
`FOUR` with defeasible and presumed values added. -/
abbrev PRESUP := Fin 3 ⊙ Fin 3

/-- The degree `½` of the chain `{0, ½, 1}`. -/
abbrev half : Fin 3 := 1

/-- Fitting's conflation on `PRESUP` (Definition 3.4), complementing each coordinate on the chain
by `Fin.rev`. -/
instance : Conflation PRESUP := Product.conflation Fin.rev Fin.rev_involutive Fin.rev_anti

namespace PRESUP

/-- `⊥`: no information, a presupposition gap. -/
def U : PRESUP := .mk 0 0
/-- Definite truth: full evidence for, none against. -/
def T : PRESUP := .mk 2 0
/-- Definite falsity. -/
def F : PRESUP := .mk 0 2
/-- Inconsistent or overdefined, a glut. -/
def I : PRESUP := .mk 2 2
/-- Presumably true: defeasible (`½`) evidence for, none against. -/
def Pplus : PRESUP := .mk 1 0
/-- Presumably false. -/
def Pminus : PRESUP := .mk 0 1
/-- Confused: conflicting defeasible evidence, not as strong a contradiction as `I`. -/
def C : PRESUP := .mk 1 1
/-- The defeated default `D⁺`: default evidence for falsity overridden by definite evidence for
truth. -/
def Dplus : PRESUP := .mk 2 1
/-- The defeated default `D⁻`: default evidence for truth overridden by definite evidence for
falsity. -/
def Dminus : PRESUP := .mk 1 2

end PRESUP

/-- `Bool ↪ Fin 3`: `false ↦ 0` (no evidence), `true ↦ 2` (full evidence). -/
def boolToFin3 : Bool → Fin 3 := fun b ↦ if b then 2 else 0

/-- The embedding of `FOUR`, the bilattice over `{0, 1}`, into `PRESUP` (§3.2.2). -/
def embed (x : FOUR) : PRESUP := .mk (boolToFin3 x.pro) (boolToFin3 x.con)

theorem embed_le (x y : FOUR) : x ≤ y ↔ embed x ≤ embed y := by
  obtain ⟨xa, xb⟩ := x; obtain ⟨ya, yb⟩ := y
  cases xa <;> cases xb <;> cases ya <;> cases yb <;> decide

theorem embed_kLE (x y : FOUR) : x ≤ₖ y ↔ embed x ≤ₖ embed y := by
  obtain ⟨xa, xb⟩ := x; obtain ⟨ya, yb⟩ := y
  cases xa <;> cases xb <;> cases ya <;> cases yb <;> decide

theorem gap_and_presumption_consistent :
    IsConsistent PRESUP.U ∧ IsConsistent PRESUP.Pplus ∧ ¬ IsConsistent PRESUP.I := by
  decide

/-! ### Partitions of the evidential space (§3.2.3)

The classical and consistent subspaces are Fitting's (`IsExact`, `IsConsistent`); the designated
and semi-designated subspaces are the thesis's, with its footnote characterizations
`DES = {x | t ≤ₖ x}` and `SEMI = {x | ¬x ≤ x, U <ₖ x}` proved as order-theoretic facts. -/

section Partitions

variable {S : Type*} [LinearOrder S] [BoundedOrder S]

/-- A designated value has maximal evidence for: `DES = {⟨a, b⟩ | b = 1}`. -/
@[reducible] def Designated (x : S ⊙ S) : Prop := x.pro = ⊤

/-- A semi-designated value has some evidence for, at least as strong as its evidence against:
`SEMI = {⟨a, b⟩ | a ≤ b, 0 < b}`. -/
@[reducible] def SemiDesignated (x : S ⊙ S) : Prop :=
  x.con ≤ x.pro ∧ ⊥ < x.pro

theorem designated_iff_top_kLE {x : S ⊙ S} :
    Designated x ↔ (⊤ : S ⊙ S) ≤ₖ x :=
  ⟨fun h ↦ ⟨h.ge, bot_le⟩, fun h ↦ le_antisymm le_top h.1⟩

theorem semiDesignated_iff {x : S ⊙ S} :
    SemiDesignated x ↔ xᶜ ≤ x ∧ (⊥ : Know (S ⊙ S)) < toKnow x := by
  constructor
  · rintro ⟨hle, hlt⟩
    exact ⟨⟨hle, hle⟩, bot_lt_iff_ne_bot.mpr fun h ↦ hlt.ne' (congrArg Prod.fst h)⟩
  · rintro ⟨hneg, hlt⟩
    refine ⟨hneg.1, bot_lt_iff_ne_bot.mpr fun hp ↦ hlt.ne' ?_⟩
    exact Prod.ext hp (le_bot_iff.mp (hneg.1.trans hp.le))

theorem designated_cases :
    ∀ x : PRESUP, Designated x ↔ x = PRESUP.T ∨ x = PRESUP.Dplus ∨ x = PRESUP.I := by
  decide

theorem semiDesignated_cases :
    ∀ x : PRESUP, SemiDesignated x ↔ x = PRESUP.Pplus ∨ x = PRESUP.C ∨ x = PRESUP.T
      ∨ x = PRESUP.Dplus ∨ x = PRESUP.I := by
  decide

theorem four_semiDesignated_iff_designated :
    ∀ x : FOUR, SemiDesignated x ↔ Designated x := by
  decide

theorem four_consistent_closed :
    ∀ x y : FOUR, IsConsistent x → IsConsistent y →
      IsConsistent xᶜ ∧ IsConsistent (x ⊓ y) ∧ IsConsistent (x ⊔ y) ∧ IsConsistent (x ⊓ₖ y) :=
  fun _ y hx hy ↦ ⟨hx.compl, hx.inf hy, hx.sup hy, hx.kInf y⟩

theorem four_consistent_not_closed_kSup :
    ¬ ∀ x y : FOUR, IsConsistent x → IsConsistent y → IsConsistent (x ⊔ₖ y) :=
  fun h ↦ absurd (h FOUR.T FOUR.F (by decide) (by decide)) (by decide)

theorem four_isClassical_closed :
    ∀ x y : FOUR, IsExact x → IsExact y → IsExact xᶜ ∧ IsExact (x ⊓ y) ∧ IsExact (x ⊔ y) :=
  fun _ _ hx hy ↦ ⟨hx.compl, hx.inf hy, hx.sup hy⟩

end Partitions

/-! ### Value-level connectives

The evaluation clauses of Definition 3.21 are value-functional except for the link connective:
clause 1 is Ginsberg negation `ᶜ`, clauses 3 and 4 are `⊓` and `⊔`, clause 5 is Fitting's guard,
and clause 2, the `presumably` operator, is built from the guard and semi-designation. -/

section Connectives

open Bilattice.Product (guard)

variable {S : Type*} [LinearOrder S] [BoundedOrder S]

/-- Semi-designation at degree `i` (Definition 3.8): dominant evidence for, at least `i`. -/
@[reducible] def SemiDesignatedAt (i : S) (x : S ⊙ S) : Prop :=
  x.con ≤ x.pro ∧ i ≤ x.pro

/-- The specific semi-designation function `σᵢ` (Definition 3.8): `T` on the values
semi-designated at `i`, `F` elsewhere. -/
def semiDesignation (i : S) (x : S ⊙ S) : S ⊙ S :=
  if SemiDesignatedAt i x then ⊤ else ⊥

/-- The `presumably` operator `πᵢ` (Definition 3.21, clause 2): `σᵢ(v) : T ⊕ σᵢ(¬v) : F`,
presumably true if the value is semi-designated, presumably false if its negation is, the two
unified informationally. -/
def presumably (i : S) (v : S ⊙ S) : S ⊙ S :=
  guard (semiDesignation i v) ⊤ ⊔ₖ guard (semiDesignation i vᶜ) ⊥

theorem presumably_table :
    presumably half PRESUP.Pplus = PRESUP.T ∧ presumably half PRESUP.T = PRESUP.T ∧
      presumably half PRESUP.F = PRESUP.F ∧ presumably half PRESUP.U = PRESUP.U ∧
      presumably half PRESUP.I = PRESUP.I := by
  decide

/-- The evidential threshold function `ω` (Definition 3.23) suppresses the dominated evidence, so
that only the dominant evidence figures in evaluation. -/
def weight (x : S ⊙ S) : S ⊙ S :=
  if x.con < x.pro then .mk x.pro ⊥ else if x.pro < x.con then .mk ⊥ x.con else x

theorem weight_dplus : weight PRESUP.Dplus = PRESUP.T := by decide

theorem weight_dminus : weight PRESUP.Dminus = PRESUP.F := by decide

-- §3.5.3, Figure 3.5 [ginsberg-1988]
theorem weight_mem_default :
    ∀ x : PRESUP, weight x ∈ [PRESUP.U, PRESUP.Pminus, PRESUP.Pplus, PRESUP.C,
      PRESUP.F, PRESUP.T, PRESUP.I] := by
  decide

-- §3.5.3
theorem weight_not_kSup_hom :
    ¬ ∀ x y : PRESUP, weight (x ⊔ₖ y) = weight x ⊔ₖ weight y := by
  decide

end Connectives

/-! ### Setups, links and closure (§3.5)

A setup assigns each atomic sentence an infon, the evidence held for and against it, so it is an
element of `α → Know (S ⊙ S)` ordered by information; asserting a formula joins in the infons the
formula contributes. An evidential link `⟨φ, j, ψ⟩` passes evidence for `φ`, attenuated to
strength `j`, to `ψ`. Closure applies the links level by level, strongest first, repeating each
level's rounds until nothing is added. -/

section Closure

variable {α S : Type*}

/-- The formulas of a setup: atoms, negation and Fitting's guard (Definition 3.10). -/
inductive Formula (α : Type*) where
  | atom (p : α)
  | neg (φ : Formula α)
  | guard (φ ψ : Formula α)
  deriving DecidableEq

namespace Formula

variable [LinearOrder S] [BoundedOrder S]

/-- The value of a formula in a setup (Definitions 3.21 and 3.22): an atom takes the weighted
value of its infon. -/
def eval (I : α → Know (S ⊙ S)) : Formula α → S ⊙ S
  | atom p => weight (ofKnow (I p))
  | neg φ => (eval I φ)ᶜ
  | guard φ ψ => Product.guard (eval I φ) (eval I ψ)

variable [DecidableEq α]

/-- The infons that asserting (`true`) or denying (`false`) a formula to degree `i` adds
(Definitions 3.13 and 3.16). -/
def infons (i : S) : Bool → Formula α → α → Know (S ⊙ S)
  | b, atom p => Function.update ⊥ p (toKnow (if b then .mk i ⊥ else .mk ⊥ i))
  | b, neg φ => infons i (!b) φ
  | b, guard φ ψ => infons i true φ ⊔ infons i b ψ

end Formula

/-- An evidential link `⟨φ, j, ψ⟩` (Definition 3.11): evidence for `φ`, attenuated to strength
`j`, is evidence for `ψ`. -/
structure Link (α S : Type*) where
  ante : Formula α
  strength : S
  cons : Formula α
  deriving DecidableEq

/-- The strict link `φ ⇀ ψ`, of full strength (§3.5.1). -/
def Link.strict [Top S] (φ ψ : Formula α) : Link α S := ⟨φ, ⊤, ψ⟩

@[inherit_doc] scoped infixr:25 " ⇀ " => Link.strict

/-- `πⱼ` attenuates a link to strength `j` (§3.5.1; Definition 3.13, clause 2). -/
def Link.presumably [Min S] (j : S) (l : Link α S) : Link α S :=
  { l with strength := j ⊓ l.strength }

variable [LinearOrder S] [BoundedOrder S]

/-- A link fires at level `i` (Definition 3.24) when its strength is at least `i` and its
antecedent is semi-designated at `i`. -/
@[reducible] def Link.Fires (i : S) (I : α → Know (S ⊙ S)) (l : Link α S) : Prop :=
  i ≤ l.strength ∧ SemiDesignatedAt i (l.ante.eval I)

variable [DecidableEq α] (L : Finset (Link α S)) (i : S) (I : α → Know (S ⊙ S))

/-- A round of closure at level `i` (Definitions 3.24 and 3.25): each firing link asserts its
consequent to its antecedent's evidence for, attenuated by the link's strength. -/
def step : α → Know (S ⊙ S) :=
  I ⊔ (L.filter (Link.Fires i I)).sup
    fun l ↦ l.cons.infons ((l.ante.eval I).pro ⊓ l.strength) true

theorem le_step : I ≤ step L i I := le_sup_left

variable [Finite α] [Fintype S]

theorem exists_iterate_step_eq : ∃ n, ∀ m, n ≤ m → (step L i)^[n] I = (step L i)^[m] I :=
  WellFoundedGT.monotone_chain_condition
    ⟨fun n ↦ (step L i)^[n] I, fun _ _ h ↦ Function.monotone_iterate_of_id_le (le_step L i) h I⟩

/-- The closure of a setup at level `i` (Definition 3.26): the setup its rounds settle on. -/
noncomputable def closureAt : α → Know (S ⊙ S) :=
  (step L i)^[(exists_iterate_step_eq L i I).choose] I

/-- The closure of a setup (Definition 3.28): closure at every nonzero level, strongest first. -/
noncomputable def closure : α → Know (S ⊙ S) :=
  ((Finset.univ.filter (⊥ < ·)).sort (· ≥ ·)).foldl (fun I j ↦ closureAt L j I) I

variable {L i I}

theorem step_closureAt : step L i (closureAt L i I) = closureAt L i I := by
  rw [closureAt, ← Function.iterate_succ_apply' (step L i)]
  exact ((exists_iterate_step_eq L i I).choose_spec _ (Nat.le_succ _)).symm

theorem closureAt_eq_iterate {k : ℕ} (h : step L i ((step L i)^[k] I) = (step L i)^[k] I) :
    closureAt L i I = (step L i)^[k] I := by
  have hn := (exists_iterate_step_eq L i I).choose_spec
  rw [closureAt, hn _ (Nat.le_add_right _ k), Function.iterate_add_apply,
    (Function.IsFixedPt.iterate h _).eq]

theorem closure_eq_iterate {L : Finset (Link α (Fin 3))} {I : α → Know (Fin 3 ⊙ Fin 3)} {m n : ℕ}
    (h₂ : step L 2 ((step L 2)^[m] I) = (step L 2)^[m] I)
    (h₁ : step L 1 ((step L 1)^[n] ((step L 2)^[m] I)) = (step L 1)^[n] ((step L 2)^[m] I)) :
    closure L I = (step L 1)^[n] ((step L 2)^[m] I) := by
  rw [closure, show Finset.univ.filter (⊥ < ·) = ({2, 1} : Finset (Fin 3)) by decide,
    Finset.sort_insert (r := (· ≥ ·)) (s := {1}) (a := (2 : Fin 3)) (by decide) (by decide),
    Finset.sort_singleton]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [closureAt_eq_iterate h₂, closureAt_eq_iterate h₁]

theorem le_closureAt : I ≤ closureAt L i I :=
  Function.monotone_iterate_of_id_le (le_step L i) (Nat.zero_le _) I

theorem le_closure : I ≤ closure L I := by
  rw [closure]
  generalize (Finset.univ.filter (fun j : S ↦ ⊥ < j)).sort (· ≥ ·) = l
  induction l generalizing I with
  | nil => exact le_rfl
  | cons j l ih =>
    rw [List.foldl_cons]
    exact le_closureAt.trans ih

end Closure

/-! ### Assertion and evaluation (§3.5.6)

A formula asserted to full degree is at least true in any setup holding its infons, since the
weighting never removes full evidence and the guard passes its second argument through once its
first is at least true. Closure only adds information, so an assertion is verified after closure
whatever the state and the lexicon. -/

section Verification

variable {α S : Type*} [LinearOrder S] [BoundedOrder S]

theorem pro_weight_eq_top {x : S ⊙ S} (h : x.pro = ⊤) : (weight x).pro = ⊤ := by
  unfold weight
  split_ifs with h₁ h₂
  · exact h
  · exact absurd h₂ (h ▸ not_top_lt)
  · exact h

theorem con_weight_eq_top {x : S ⊙ S} (h : x.con = ⊤) : (weight x).con = ⊤ := by
  unfold weight
  split_ifs with h₁ h₂
  · exact absurd h₁ (h ▸ not_top_lt)
  · exact h
  · exact h

variable [DecidableEq α] {J : α → Know (S ⊙ S)}

theorem designated_eval_of_infons_le :
    ∀ (φ : Formula α) (b : Bool), φ.infons ⊤ b ≤ J →
      Designated (bif b then φ.eval J else (φ.eval J)ᶜ)
  | .atom p, false, h => by
    have hp : (.mk ⊥ ⊤ : S ⊙ S) ≤ₖ ofKnow (J p) :=
      kLE_def.mpr (by simpa [Formula.infons] using h p)
    rw [← Product.mk_pro_con (ofKnow (J p))] at hp
    exact con_weight_eq_top (le_top.antisymm (Product.mk_kLE_mk.mp hp).2)
  | .atom p, true, h => by
    have hp : (.mk ⊤ ⊥ : S ⊙ S) ≤ₖ ofKnow (J p) :=
      kLE_def.mpr (by simpa [Formula.infons] using h p)
    rw [← Product.mk_pro_con (ofKnow (J p))] at hp
    exact pro_weight_eq_top (le_top.antisymm (Product.mk_kLE_mk.mp hp).1)
  | .neg φ, b, h => by
    have := designated_eval_of_infons_le φ (!b) h
    cases b <;> simpa [Formula.eval] using this
  | .guard φ ψ, b, h => by
    have hφ := designated_eval_of_infons_le φ true (le_sup_left.trans h)
    have hψ := designated_eval_of_infons_le ψ b (le_sup_right.trans h)
    have hg : (Formula.guard φ ψ).eval J = ψ.eval J :=
      Product.guard_of_top_kLE (designated_iff_top_kLE.mp hφ) _
    rwa [hg]

variable [Finite α] [Fintype S]

/-- An agent that accepts a full assertion verifies it after closure, whatever its state and its
lexicon (§3.5.6; verification is Definition 3.31). -/
theorem top_kLE_eval_closure (L : Finset (Link α S)) (I : α → Know (S ⊙ S)) (φ : Formula α) :
    (⊤ : S ⊙ S) ≤ₖ φ.eval (closure L (I ⊔ φ.infons ⊤ true)) :=
  designated_iff_top_kLE.mp
    (designated_eval_of_infons_le φ true (le_sup_right.trans le_closure))

end Verification

/-! ### Defeasible reasoning (§3.7.3)

Strict evidence overrides defeasible evidence, and conflicting defaults leave the agent confused.
Defaults chain as strict links do, so a more specific default does not override a less specific
one, which the thesis takes to be a wrong prediction. -/

section Defeasible

open Formula

/-- The atomic sentences of (3.4) and (3.5): Tweety is a bird, a penguin, and flies. -/
inductive Tweety
  | bird
  | penguin
  | flies
  deriving DecidableEq, Fintype

/-- The atomic sentences of (3.6) and (3.7): Nixon is a quaker, a republican, and a pacifist. -/
inductive Nixon
  | quaker
  | republican
  | pacifist
  deriving DecidableEq, Fintype

/-- The atomic sentences of (3.8) and (3.9): John is a student, an adult, and employed. -/
inductive Student
  | student
  | adult
  | employed
  deriving DecidableEq, Fintype

open Tweety in
/-- Birds presumably fly, and penguins are birds that do not fly. -/
def tweetyLinks : Finset (Link Tweety (Fin 3)) :=
  {(atom bird ⇀ atom flies).presumably half, atom penguin ⇀ atom bird,
    atom penguin ⇀ neg (atom flies)}

open Nixon in
/-- Quakers tend to be pacifists and republicans tend not to be (3.6). -/
def nixonLinks : Finset (Link Nixon (Fin 3)) :=
  {(atom quaker ⇀ atom pacifist).presumably half,
    (atom republican ⇀ neg (atom pacifist)).presumably half}

open Student in
/-- Students are normally adults and normally not employed, and adults normally employed (3.8). -/
def studentLinks : Finset (Link Student (Fin 3)) :=
  {(atom student ⇀ atom adult).presumably half,
    (atom student ⇀ neg (atom employed)).presumably half,
    (atom adult ⇀ atom employed).presumably half}

open Tweety in
/-- The penguin principle (3.4)–(3.5): Tweety presumably flies until it turns out to be a
penguin. -/
theorem penguin_principle :
    (atom flies).eval (closure tweetyLinks ((atom bird).infons ⊤ true)) = PRESUP.Pplus ∧
    (atom flies).eval (closure tweetyLinks (closure tweetyLinks ((atom bird).infons ⊤ true) ⊔
      (atom penguin).infons ⊤ true)) = PRESUP.F := by
  refine ⟨?_, ?_⟩
  · rw [closure_eq_iterate (m := 2) (n := 2)] <;> decide
  · rw [closure_eq_iterate (I := (atom bird).infons ⊤ true) (m := 2) (n := 2),
      closure_eq_iterate (m := 2) (n := 2)] <;> decide

open Nixon in
/-- The Nixon diamond (3.6)–(3.7): conflicting defaults leave the agent confused. -/
theorem nixon_diamond :
    (atom pacifist).eval (closure nixonLinks
      ((atom republican).infons ⊤ true ⊔ (atom quaker).infons ⊤ true)) = PRESUP.C := by
  rw [closure_eq_iterate (m := 2) (n := 2)] <;> decide

open Student in
/-- The weak Tweety triangle (3.8)–(3.9): the default from adulthood to employment is not
overridden by the more specific one from studenthood, and the agent is confused. -/
theorem weak_tweety_triangle :
    (atom employed).eval (closure studentLinks ((atom student).infons ⊤ true)) = PRESUP.C := by
  rw [closure_eq_iterate (m := 2) (n := 2)] <;> decide

end Defeasible

/-! ### Implication and presupposition (§6.2)

Entailment and presupposition are bundles of links. Presupposition adds to implication's modus
ponens and modus tollens links a defeasible link from the negated carrier. -/

section Presupposition

open Formula

variable {α : Type*} [DecidableEq α]

/-- Implication `φ → ψ` (Definition 6.1): a modus ponens and a modus tollens link. -/
def implication (φ ψ : Formula α) : Finset (Link α (Fin 3)) :=
  {φ ⇀ ψ, neg ψ ⇀ neg φ}

/-- Presupposition `φ ≫ ψ` (Definition 6.5): strict modus ponens, defeasible modus ponens from
`¬φ`, and strict modus tollens. -/
def presupposition (φ ψ : Formula α) : Finset (Link α (Fin 3)) :=
  {φ ⇀ ψ, (neg φ ⇀ ψ).presumably half, neg ψ ⇀ neg φ}

-- §6.2.3
theorem implication_subset_presupposition (φ ψ : Formula α) :
    implication φ ψ ⊆ presupposition φ ψ := by
  simp [implication, presupposition, Finset.insert_subset_iff]

/-- The atomic sentences of (6.1) and (6.2): John passed the exam, and John took it. -/
inductive Exam
  | pass
  | take
  deriving DecidableEq, Fintype

open Exam in
-- (6.1), (6.2)
theorem implication_rows :
    (atom take).eval (closure (implication (atom pass) (atom take))
      ((atom pass).infons ⊤ true)) = PRESUP.T ∧
    (atom pass).eval (closure (implication (atom pass) (atom take))
      ((neg (atom take)).infons ⊤ true)) = PRESUP.F := by
  refine ⟨?_, ?_⟩ <;> rw [closure_eq_iterate (m := 2) (n := 2)] <;> decide

/-- The atomic sentences of (6.11): John regrets failing the exam, and John failed it. -/
inductive Regret
  | regret
  | fail
  deriving DecidableEq, Fintype

open Regret

/-- "Regret" presupposes its complement, `λxλφ[R(x, φ) ≫ φ] ∈ lexl(R)`. -/
def regretLinks : Finset (Link Regret (Fin 3)) := presupposition (atom regret) (atom fail)

/-- (6.12): a positive carrier entails its presupposition (a), which it cannot then deny (c); a
negative carrier presumes it (b), which can be denied consistently (d); and denying the
presupposition falsifies the carrier (e). -/
theorem presupposition_rows :
    (atom fail).eval (closure regretLinks ((atom regret).infons ⊤ true)) = PRESUP.T ∧
    (atom fail).eval (closure regretLinks ((neg (atom regret)).infons ⊤ true)) = PRESUP.Pplus ∧
    ((atom fail).eval (closure regretLinks ((atom regret).infons ⊤ true ⊔
        (neg (atom fail)).infons ⊤ true)) = PRESUP.I ∧
      (atom regret).eval (closure regretLinks ((atom regret).infons ⊤ true ⊔
        (neg (atom fail)).infons ⊤ true)) = PRESUP.I) ∧
    ((atom fail).eval (closure regretLinks ((neg (atom regret)).infons ⊤ true ⊔
        (neg (atom fail)).infons ⊤ true)) = PRESUP.F ∧
      (atom regret).eval (closure regretLinks ((neg (atom regret)).infons ⊤ true ⊔
        (neg (atom fail)).infons ⊤ true)) = PRESUP.F) ∧
    (atom regret).eval (closure regretLinks ((neg (atom fail)).infons ⊤ true)) = PRESUP.F := by
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    rw [closure_eq_iterate (m := 2) (n := 2)] <;> decide

-- Definition 3.28
theorem link_carries_presumption :
    (atom fail).eval (closure regretLinks ((atom regret).infons half true)) = PRESUP.Pplus := by
  rw [closure_eq_iterate (m := 2) (n := 2)] <;> decide

-- (6.12c), Definition 3.21
theorem consistent_assertion_eq_I :
    (atom regret).eval (closure regretLinks
        ((atom regret).infons ⊤ true ⊔ (neg (atom fail)).infons ⊤ true)) ⊓
      (neg (atom fail)).eval (closure regretLinks
        ((atom regret).infons ⊤ true ⊔ (neg (atom fail)).infons ⊤ true)) = PRESUP.I := by
  rw [closure_eq_iterate (m := 2) (n := 2)] <;> decide

end Presupposition

/-! ### Presupposition and the guard (§6.2.3) -/

section Guard

open Formula

open FOUR (U T F I) in
-- Table 6.1
theorem guard_table :
    ∀ y : FOUR, Product.guard T y = y ∧ Product.guard U y = U ∧ Product.guard F y = U ∧
      Product.guard I y = y := by
  decide

theorem guard_truth_gap {α : Type*} {I : α → Know PRESUP} {φ ψ : Formula α}
    (h : φ.eval I = PRESUP.F) : (guard φ ψ).eval I = PRESUP.U :=
  (congrArg (Product.guard · (ψ.eval I)) h).trans (Product.guard_of_pro_bot rfl _)

open Regret

/-- "John regrets failing the exam" with its presupposition as a guard, `F : R`. -/
abbrev guarded : Formula Regret := guard (atom fail) (atom regret)

theorem guard_presupposes_alike :
    (atom fail).eval (guarded.infons (⊤ : Fin 3) true) = PRESUP.T ∧
    (atom fail).eval ((neg guarded).infons (⊤ : Fin 3) true) = PRESUP.T := by
  decide

/-- (6.10), in the forms of (6.11c) and (6.11d): denying the presupposition contradicts a positive
carrier but not a negative one. The links of Definition 6.5 make the denial inconsistent exactly
where the thesis marks a contradiction; the guard makes it inconsistent after both carriers. -/
theorem cancellation_contrast :
    ((atom fail).eval (closure regretLinks ((atom regret).infons ⊤ true ⊔
        (neg (atom fail)).infons ⊤ true)) = PRESUP.I ↔
      Examples.ex6_11c.judgment = .unacceptable) ∧
    ((atom fail).eval (closure regretLinks ((neg (atom regret)).infons ⊤ true ⊔
        (neg (atom fail)).infons ⊤ true)) = PRESUP.I ↔
      Examples.ex6_11d.judgment = .unacceptable) ∧
    ((atom fail).eval (guarded.infons ⊤ true ⊔ (neg (atom fail)).infons (⊤ : Fin 3) true) =
        PRESUP.I ↔
      Examples.ex6_11c.judgment = .unacceptable) ∧
    ¬ ((atom fail).eval ((neg guarded).infons ⊤ true ⊔
        (neg (atom fail)).infons (⊤ : Fin 3) true) = PRESUP.I ↔
      Examples.ex6_11d.judgment = .unacceptable) := by
  refine ⟨?_, ?_, by decide, by decide⟩ <;> rw [closure_eq_iterate (m := 2) (n := 2)] <;> decide

end Guard

/-! ### Contextual factors (§6.3) -/

section Context

open Formula

/-- The atomic sentences of (6.13) and (6.14): John was wrong about Mary regretting failing the
logic exam, Mary regrets failing it, and Mary failed it. -/
inductive Wrong
  | wrong
  | regret
  | fail
  deriving DecidableEq, Fintype

open Wrong

/-- Being wrong about something implies its negation and not being wrong implies it, and
"regret" presupposes its complement. -/
def wrongLinks : Finset (Link Wrong (Fin 3)) :=
  {atom wrong ⇀ neg (atom regret), neg (atom wrong) ⇀ atom regret} ∪
    presupposition (atom regret) (atom fail)

/-- (6.13) and (6.14): from "John was wrong about Mary regretting failing the exam" the agent
presumes that Mary failed, unless the context `E'` denies it; from "John wasn't wrong about it"
the agent concludes that she failed, and in `E'` becomes inconsistent. -/
theorem context_rows :
    ((neg (atom regret)).eval (closure wrongLinks ((atom wrong).infons ⊤ true)) = PRESUP.T ∧
      (atom fail).eval (closure wrongLinks ((atom wrong).infons ⊤ true)) = PRESUP.Pplus) ∧
    ((neg (atom regret)).eval (closure wrongLinks
        ((neg (atom fail)).infons ⊤ true ⊔ (atom wrong).infons ⊤ true)) = PRESUP.T ∧
      (atom fail).eval (closure wrongLinks
        ((neg (atom fail)).infons ⊤ true ⊔ (atom wrong).infons ⊤ true)) = PRESUP.F) ∧
    ((atom regret).eval (closure wrongLinks ((neg (atom wrong)).infons ⊤ true)) = PRESUP.T ∧
      (atom fail).eval (closure wrongLinks ((neg (atom wrong)).infons ⊤ true)) = PRESUP.T) ∧
    (atom fail).eval (closure wrongLinks
      ((neg (atom fail)).infons ⊤ true ⊔ (neg (atom wrong)).infons ⊤ true)) = PRESUP.I := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    rw [closure_eq_iterate (m := 2) (n := 2)] <;> decide

end Context

end Schoter1996a
