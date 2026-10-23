module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.ModelTheory.Basic
public import Mathlib.Tactic.FinCases
public import Linglib.Data.Examples.Mandelkern2022
public import Linglib.Logic.Assignment
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Quantification.NumberTree

/-!
# Mandelkern (2022): Witnesses

This file formalizes Mandelkern's bounded theory of definites and indefinites. The language is
first-order with a two-place indefinite `ɜx(p, q)`, a two-place definite `ιx(p, q)`, of which a
pronoun is the case with the tautological restrictor `⊤x`, and quantifiers `Q x^δ (p, q)` over
domain variables. Truth at an assignment–world pair is classical. A second dimension, the
bounds, is satisfied (*satt*) relative to a context, a set of such pairs: an indefinite's witness
bound, that if it is true its variable denotes a witness; a definite's familiarity bound, that its
restrictor is true and satt throughout the context; and a quantifier's bounds, that it pairs each
individual with an assignment making its restrictor and scope satt without moving familiar
variables. Bounds project through local contexts, asymmetric or symmetric, and updating a context
keeps the points at which a sentence is true and satt.

At a context the two dimensions form a trivalent proposition (`Formula.toTrivalent`), undefined
where the bounds fail, so bound entailment is Strawson entailment at every context
(`BoundEntails`). An indefinite keeps the points whose
variable is a witness, so a later pronoun finds it familiar, while the logically equivalent *Sue
is a parent* licenses none; double negation and the bathroom disjunction keep the indefinite's
witness. Under a quantifier the same contrast is covariation: *everyone who has a child loves
them* pairs each parent with a child, while *every parent loves them* can only be about one
familiar individual. With asymmetric local contexts a pronoun cannot precede its indefinite in a
conjunction; with symmetric ones it can. The three renderings of open scope in (20) are true and
satt at the same indices without being logically equivalent, and footnote 20's extension of their
bound equivalences to arbitrary formulae fails for one of them (`not_boundEntails_ex20b_ex20a`).

## Main statements

* `update_indef_then_it`, `logicallyEquivalent_hasChild_isParent`, `update_isParent_then_it`: an
  indefinite licenses a later pronoun, and a logically equivalent sentence without one does not.
* `realize_ex22b_iff`, `realize_ex21b_iff_of_familiar`: a pronoun covaries under a quantifier
  only with an indefinite in the restrictor.
* `felicitous_ex15a_asymmetric`, `not_felicitous_ex15b_asymmetric`, `satt_ex15b_symmetric`: a
  pronoun after its indefinite in a conjunction is felicitous, and one before it depends on the
  order of local contexts.

## Implementation notes

* An atomic valuation is a world-indexed family of structures `I : W → L.Structure E`, and atoms
  take variables only. Bounds fill the presupposition slot, the support of the trivalent
  proposition, though the paper leaves open whether they are presuppositions;
  `not_univ_subset_support_indef_atom₁` shows why update keeps the true and satt points rather
  than requiring admission.
* A domain variable's value pairs every individual with an assignment, which builds in the bound
  that each individual has one pair, and the paired assignments value individual variables only;
  in the paper the value is a set of pairs whose assignments value domain variables too.
* The quantifier bound on variables *not novel* in the context reads them, as the paper's
  parenthetical does, as the already familiar ones, valued at every point; §3's gloss of novelty
  as nowhere defined would fix every variable in the null context and block (22-b).
* Determiners are number trees: `.all` is the paper's *every* on finite domains, and `.most` its
  *most* where the restrictor set is finite and nonempty.

## TODO

* The weak and strong readings of donkey sentences (p. 1111).
* The cross-world witness bound for modal subordination sketched in the conclusion, (23)–(24).

## References

* [mandelkern-2022]
* [heim-1982]
* [karttunen-1976]
* [schlenker-2009]
* [stalnaker-1978]
* [von-fintel-1999]
-/

@[expose] public section

open FirstOrder Presupposition
open Trivalent (posExt)

namespace Mandelkern2022

/-- The two orders of local contexts the paper compares (p. 1106). -/
inductive Order where
  /-- The left junct's local context is the global context, and the right junct's is the global
  context updated with the left junct (p. 1105). -/
  | asymmetric
  /-- Each junct's local context is the global context updated with the other junct
  (p. 1106). -/
  | symmetric
  deriving DecidableEq

/-- An assignment of both sorts of variable (p. 1110). Individual variables take individuals,
partially, and a domain variable pairs every individual with an assignment. -/
structure Assign (V Δ E : Type*) where
  /-- The values of the individual variables. -/
  ind : PartialAssign V E
  /-- The value of each domain variable, pairing every individual with an assignment. -/
  dom : Δ → E → PartialAssign V E

namespace Assign

variable {V Δ E : Type*}

instance : CoeFun (Assign V Δ E) (fun _ ↦ V → Flat E) := ⟨fun g ↦ g.ind⟩

/-- The assignment valuing no individual variable and pairing every individual with it. -/
instance : Bot (Assign V Δ E) := ⟨⟨⊥, fun _ _ ↦ ⊥⟩⟩

@[simp] theorem coe_mk (i : PartialAssign V E) (d : Δ → E → PartialAssign V E) (x : V) :
    (⟨i, d⟩ : Assign V Δ E) x = i x := rfl

@[simp] theorem bot_apply (x : V) : (⊥ : Assign V Δ E) x = ⊥ := rfl

variable [DecidableEq V] {g : Assign V Δ E} {x y : V} {a : E}

/-- `g[x→a]`, the assignment resetting the individual variable `x` to `a`. -/
def update (g : Assign V Δ E) (x : V) (a : E) : Assign V Δ E := ⟨g.ind.update x a, g.dom⟩

@[simp] theorem update_apply_self : g.update x a x = ↑a := PartialAssign.update_self x a g.ind

@[simp] theorem update_apply_of_ne (h : y ≠ x) : g.update x a y = g y :=
  PartialAssign.update_of_ne h a g.ind

theorem update_eq_self (h : g x = ↑a) : g.update x a = g := by
  cases g
  simp only [update, mk.injEq, and_true]
  exact PartialAssign.update_eq_self h

/-- The assignment at which a quantifier over the domain variable `δ` evaluates its restrictor
and scope at the individual `a`, the paired assignment reset at `x` to `a` (p. 1110). -/
def pair (g : Assign V Δ E) (δ : Δ) (x : V) (a : E) : Assign V Δ E :=
  ⟨(g.dom δ a).update x a, g.dom⟩

@[simp] theorem pair_apply (δ : Δ) (a : E) (y : V) :
    g.pair δ x a y = (g.dom δ a).update x a y := rfl

end Assign

/-- The language of the paper (pp. 1101 and 1110), with atoms over variables, the pronoun
restrictor `⊤x`, the classical connectives, the two-place indefinite and definite, and the
generalized quantifiers. -/
inductive Formula (L : Language) (V Δ : Type*) where
  /-- The atom `A(x₁, …, xₙ)`. -/
  | atom {n : ℕ} (R : L.Relations n) (xs : Fin n → V)
  /-- The tautological restrictor `⊤x` of a pronoun. -/
  | top (x : V)
  /-- Conjunction `p & q`. -/
  | conj (p q : Formula L V Δ)
  /-- Disjunction `p ∨ q`. -/
  | disj (p q : Formula L V Δ)
  /-- Negation `¬p`. -/
  | neg (p : Formula L V Δ)
  /-- The indefinite `ɜx(p, q)`, *some p is q*. -/
  | indef (x : V) (p q : Formula L V Δ)
  /-- The definite `ιx(p, q)`, *the p is q*. -/
  | iota (x : V) (p q : Formula L V Δ)
  /-- The quantifier `Q x^δ (p, q)` over the domain variable `δ`, whose determiner is a number
  tree, *every* being `.all` and *most* `.most` (p. 1110). -/
  | quant (Q : Quantifier.NumberTree) (x : V) (δ : Δ) (p q : Formula L V Δ)

/-- The local contexts of a junction of `p` and `q` in each order (pp. 1105–1106), where `sp` and
`sq` are the juncts' bounds and `kp`, `kq` select the points of a junct's local context, where it
is true in a conjunction and false in a disjunction. -/
def Order.junct {A W : Type*} (o : Order) (sp sq : Set (A × W) → A → W → Prop)
    (kp kq : A → W → Prop) (c : Set (A × W)) (g : A) (w : W) : Prop :=
  match o with
  | .asymmetric => sp c g w ∧ sq {i ∈ c | kp i.1 i.2 ∧ sp c i.1 i.2} g w
  | .symmetric =>
    sp {i ∈ c | kq i.1 i.2 ∧ sq c i.1 i.2} g w ∧ sq {i ∈ c | kp i.1 i.2 ∧ sp c i.1 i.2} g w

theorem Order.junct_right {A W : Type*} {o : Order} {sp sq : Set (A × W) → A → W → Prop}
    {kp kq : A → W → Prop} {c : Set (A × W)} {g : A} {w : W} (h : o.junct sp sq kp kq c g w) :
    sq {i ∈ c | kp i.1 i.2 ∧ sp c i.1 i.2} g w := by
  cases o <;> exact h.2

/-- A variable is familiar in a context when every point of the context values it (p. 1103); the
paper's *not novel* in the bounds of quantifiers. -/
def Familiar {V Δ E W : Type*} (c : Set (Assign V Δ E × W)) (y : V) : Prop := ∀ i ∈ c, i.1 y ≠ ⊥

section ValuedIn

variable {L : Language} {V Δ W E : Type*}

/-- The extension `A_w` of a one-place relation symbol at a world (p. 1103). -/
def extension (I : W → L.Structure E) (R : L.Relations 1) (w : W) : Set E :=
  {a | (I w).RelMap R ![a]}

/-- The points at which `x` has a value in `S`, as given at the point's world. -/
def valuedIn (x : V) (S : W → Set E) : Set (Assign V Δ E × W) :=
  {i | ∃ a ∈ S i.2, i.1 x = a}

variable {I : W → L.Structure E} {S T : W → Set E} {R : L.Relations 1} {x : V} {w : W}

@[simp] theorem mem_extension {a : E} : a ∈ extension I R w ↔ (I w).RelMap R ![a] := Iff.rfl

@[simp] theorem mem_valuedIn {i : Assign V Δ E × W} :
    i ∈ valuedIn x S ↔ ∃ a ∈ S i.2, i.1 x = a :=
  Iff.rfl

theorem valuedIn_inter_valuedIn :
    (valuedIn x S ∩ valuedIn x T : Set (Assign V Δ E × W)) = valuedIn x (S ⊓ T) := by
  ext ⟨g, w⟩
  simp only [Set.mem_inter_iff, mem_valuedIn, Pi.inf_apply, Set.inf_eq_inter]
  constructor
  · rintro ⟨⟨a, hS, ha⟩, b, hT, hb⟩
    obtain rfl : b = a := Flat.coe_injective (hb.symm.trans ha)
    exact ⟨b, ⟨hS, hT⟩, ha⟩
  · rintro ⟨a, ⟨hS, hT⟩, ha⟩
    exact ⟨⟨a, hS, ha⟩, a, hT, ha⟩

theorem valuedIn_mono (h : S ≤ T) : (valuedIn x S : Set (Assign V Δ E × W)) ⊆ valuedIn x T :=
  fun _ ⟨a, ha, hx⟩ ↦ ⟨a, h _ ha, hx⟩

theorem ne_bot_of_mem_valuedIn {i : Assign V Δ E × W} (h : i ∈ valuedIn x S) : i.1 x ≠ ⊥ :=
  Flat.ne_bot_iff_exists.2 (h.imp fun _ ↦ And.right)

end ValuedIn

namespace Formula

variable {L : Language} {V Δ W E : Type*} [DecidableEq V] (I : W → L.Structure E)

/-- Truth at an assignment and a world (pp. 1101, 1110 and 1114). An atom is true when its
variables are valued and their values stand in the relation, and `⊤x` is true when `x` is
valued. A quantifier relates, by its number tree, the individuals whose paired assignments make
the restrictor true to those that make the restrictor and scope true. -/
def Realize : Formula L V Δ → Assign V Δ E → W → Prop
  | atom R xs, g, w => ∃ es : Fin _ → E, (∀ i, g (xs i) = es i) ∧ (I w).RelMap R es
  | top x, g, _ => g x ≠ ⊥
  | conj p q, g, w => p.Realize g w ∧ q.Realize g w
  | disj p q, g, w => p.Realize g w ∨ q.Realize g w
  | neg p, g, w => ¬ p.Realize g w
  | indef x p q, g, w => ∃ a, p.Realize (g.update x a) w ∧ q.Realize (g.update x a) w
  | iota _ p q, g, w => p.Realize g w ∧ q.Realize g w
  | quant Q x δ p q, g, w => Q.toGQ (fun a ↦ p.Realize (g.pair δ x a) w)
      (fun a ↦ p.Realize (g.pair δ x a) w ∧ q.Realize (g.pair δ x a) w)

/-- The bounds of a formula are satisfied (*satt*) at a context, an assignment and a world, in the
order `o` (pp. 1105–1106, 1110 and 1114). A quantifier's bounds hold at every individual's
paired assignment, whose restrictor and conjunction of restrictor and scope must be satt, and
which agrees with the given assignment on the familiar variables. -/
def Satt (o : Order) :
    Formula L V Δ → Set (Assign V Δ E × W) → Assign V Δ E → W → Prop
  | atom _ xs, _, g, _ => ∀ i, g (xs i) ≠ ⊥
  | top x, _, g, _ => g x ≠ ⊥
  | conj p q, c, g, w => o.junct (p.Satt o) (q.Satt o) (p.Realize I) (q.Realize I) c g w
  | disj p q, c, g, w => o.junct (p.Satt o) (q.Satt o) (fun g w ↦ ¬ p.Realize I g w)
      (fun g w ↦ ¬ q.Realize I g w) c g w
  | neg p, c, g, w => p.Satt o c g w
  | indef x p q, c, g, w =>
      (∃ g', o.junct (p.Satt o) (q.Satt o) (p.Realize I) (q.Realize I) c g' w) ∧
      ((∃ a, p.Realize I (g.update x a) w ∧ q.Realize I (g.update x a) w) →
        (p.Realize I g w ∧ q.Realize I g w) ∧
          o.junct (p.Satt o) (q.Satt o) (p.Realize I) (q.Realize I) c g w)
  | iota _ p q, c, g, w =>
      (∀ i ∈ c, p.Realize I i.1 i.2 ∧ p.Satt o c i.1 i.2) ∧
      (p.Realize I g w → q.Satt o {i ∈ c | p.Realize I i.1 i.2 ∧ p.Satt o c i.1 i.2} g w)
  | quant _ x δ p q, c, g, w => ∀ a,
      p.Satt o c (g.pair δ x a) w ∧
      o.junct (p.Satt o) (q.Satt o) (p.Realize I) (q.Realize I) c (g.pair δ x a) w ∧
      ∀ y, Familiar c y → g.dom δ a y = g y

open Classical in
/-- The two dimensions of a formula's meaning at a context as a trivalent proposition, undefined
where the bounds fail and otherwise the formula's truth value. -/
noncomputable def toTrivalent (o : Order) (c : Set (Assign V Δ E × W)) (p : Formula L V Δ) :
    Assign V Δ E × W → SignType :=
  {i | p.Satt I o c i.1 i.2}.indicator fun i ↦ SignType.ofProp (p.Realize I i.1 i.2)

/-- Updating `c` with `p` keeps the points of `c` at which `p` is true and satt (p. 1103). This
set is also the local context `cᵖ` of the projection clauses. -/
def update (o : Order) (c : Set (Assign V Δ E × W)) (p : Formula L V Δ) :
    Set (Assign V Δ E × W) :=
  {i ∈ c | p.Realize I i.1 i.2 ∧ p.Satt I o c i.1 i.2}

/-- A sentence is felicitous in a context when its bounds hold at some point of it; infelicity
is their failure at every point (p. 1104). -/
def Felicitous (o : Order) (c : Set (Assign V Δ E × W)) (p : Formula L V Δ) : Prop :=
  ∃ i ∈ c, p.Satt I o c i.1 i.2

variable {I} {o : Order} {c : Set (Assign V Δ E × W)} {g : Assign V Δ E} {w : W}
  {p q : Formula L V Δ} {x : V}

/-! ### Truth and bounds -/

@[simp] theorem realize_atom {n : ℕ} {R : L.Relations n} {xs : Fin n → V} :
    (atom R xs).Realize I g w ↔ ∃ es : Fin n → E, (∀ i, g (xs i) = es i) ∧ (I w).RelMap R es :=
  Iff.rfl

@[simp] theorem realize_top : (top x : Formula L V Δ).Realize I g w ↔ g x ≠ ⊥ := Iff.rfl

@[simp] theorem realize_conj : (conj p q).Realize I g w ↔ p.Realize I g w ∧ q.Realize I g w :=
  Iff.rfl

@[simp] theorem realize_disj : (disj p q).Realize I g w ↔ p.Realize I g w ∨ q.Realize I g w :=
  Iff.rfl

@[simp] theorem realize_neg : (neg p).Realize I g w ↔ ¬ p.Realize I g w := Iff.rfl

@[simp] theorem realize_indef :
    (indef x p q).Realize I g w ↔
      ∃ a, p.Realize I (g.update x a) w ∧ q.Realize I (g.update x a) w :=
  Iff.rfl

@[simp] theorem realize_iota : (iota x p q).Realize I g w ↔ p.Realize I g w ∧ q.Realize I g w :=
  Iff.rfl

@[simp] theorem realize_quant {Q : Quantifier.NumberTree} {δ : Δ} :
    (quant Q x δ p q).Realize I g w ↔ Q.toGQ (fun a ↦ p.Realize I (g.pair δ x a) w)
      (fun a ↦ p.Realize I (g.pair δ x a) w ∧ q.Realize I (g.pair δ x a) w) :=
  Iff.rfl

/-- A quantifier is satt iff, at each individual's paired assignment, its restrictor and junction
are satt and familiar variables keep their values (p. 1114). -/
theorem satt_quant {Q : Quantifier.NumberTree} {δ : Δ} :
    (quant Q x δ p q).Satt I o c g w ↔ ∀ a,
      p.Satt I o c (g.pair δ x a) w ∧
      o.junct (p.Satt I o) (q.Satt I o) (p.Realize I) (q.Realize I) c (g.pair δ x a) w ∧
      ∀ y, Familiar c y → g.dom δ a y = g y :=
  Iff.rfl

@[simp] theorem mem_update {i : Assign V Δ E × W} :
    i ∈ update I o c p ↔ i ∈ c ∧ p.Realize I i.1 i.2 ∧ p.Satt I o c i.1 i.2 :=
  Iff.rfl

theorem update_subset : update I o c p ⊆ c := Set.sep_subset _ _

@[simp] theorem toTrivalent_eq_zero_iff {i : Assign V Δ E × W} :
    p.toTrivalent I o c i = 0 ↔ ¬ p.Satt I o c i.1 i.2 := by
  simp [toTrivalent]

@[simp] theorem toTrivalent_eq_one_iff {i : Assign V Δ E × W} :
    p.toTrivalent I o c i = 1 ↔ p.Satt I o c i.1 i.2 ∧ p.Realize I i.1 i.2 := by
  simp [toTrivalent]

theorem update_eq_inter_posExt : update I o c p = c ∩ posExt (p.toTrivalent I o c) :=
  Set.ext fun _ ↦ and_congr_right' (toTrivalent_eq_one_iff.trans and_comm).symm

@[simp] theorem satt_atom {n : ℕ} {R : L.Relations n} {xs : Fin n → V} :
    (atom R xs).Satt I o c g w ↔ ∀ i, g (xs i) ≠ ⊥ :=
  Iff.rfl

@[simp] theorem satt_top : (top x : Formula L V Δ).Satt I o c g w ↔ g x ≠ ⊥ := Iff.rfl

theorem satt_conj :
    (conj p q).Satt I .asymmetric c g w ↔
      p.Satt I .asymmetric c g w ∧ q.Satt I .asymmetric (update I .asymmetric c p) g w :=
  Iff.rfl

theorem satt_disj :
    (disj p q).Satt I .asymmetric c g w ↔
      p.Satt I .asymmetric c g w ∧ q.Satt I .asymmetric (update I .asymmetric c (neg p)) g w :=
  Iff.rfl

@[simp] theorem satt_neg : (neg p).Satt I o c g w ↔ p.Satt I o c g w := Iff.rfl

/-- An indefinite is satt iff its body is satt somewhere and, if the indefinite is true, its body is
true and satt (p. 1114). -/
theorem satt_indef :
    (indef x p q).Satt I o c g w ↔ (∃ g', (conj p q).Satt I o c g' w) ∧
      ((indef x p q).Realize I g w → (conj p q).Realize I g w ∧ (conj p q).Satt I o c g w) :=
  Iff.rfl

/-- A definite is satt iff its restrictor leaves the context unchanged and, if the restrictor is
true, its scope is satt at `cᵖ` (p. 1114). -/
theorem satt_iota :
    (iota x p q).Satt I o c g w ↔
      update I o c p = c ∧ (p.Realize I g w → q.Satt I o (update I o c p) g w) :=
  and_congr_left' Set.sep_eq_self_iff_mem_true.symm

theorem realize_indef_of_ne_bot (hx : g x ≠ ⊥) (hp : p.Realize I g w) (hq : q.Realize I g w) :
    (indef x p q).Realize I g w := by
  obtain ⟨a, ha⟩ := Flat.ne_bot_iff_exists.1 hx
  exact ⟨a, by rwa [Assign.update_eq_self ha], by rwa [Assign.update_eq_self ha]⟩

theorem realize_conj_of_satt_indef (hs : (indef x p q).Satt I o c g w)
    (hr : (indef x p q).Realize I g w) : p.Realize I g w ∧ q.Realize I g w :=
  (hs.2 hr).1

/-! ### The calculus of positive extensions

The points at which a formula is true and satt at a context, the positive extension
`posExt (p.toTrivalent I o c)`, decompose along the connectives; updating a context intersects
it with this set (`update_eq_inter_posExt`). -/

theorem posExt_conj : posExt ((conj p q).toTrivalent I .asymmetric c) =
    posExt (p.toTrivalent I .asymmetric c) ∩
      posExt (q.toTrivalent I .asymmetric (update I .asymmetric c p)) := by
  ext
  simp only [Trivalent.mem_posExt, toTrivalent_eq_one_iff, satt_conj, realize_conj,
    Set.mem_inter_iff]
  tauto

theorem posExt_indef : posExt ((indef x p q).toTrivalent I o c) =
    {i ∈ posExt ((conj p q).toTrivalent I o c) | (indef x p q).Realize I i.1 i.2} := by
  ext ⟨g, w⟩
  simp only [Trivalent.mem_posExt, toTrivalent_eq_one_iff]
  exact ⟨fun ⟨hs, hr⟩ ↦ ⟨⟨(hs.2 hr).2, (hs.2 hr).1⟩, hr⟩,
    fun ⟨⟨hs, hr⟩, hi⟩ ↦ ⟨⟨⟨g, hs⟩, fun _ ↦ ⟨hr, hs⟩⟩, hi⟩⟩

theorem posExt_indef_of_ne_bot (hp : ∀ g w, p.Realize I g w → g x ≠ ⊥) :
    posExt ((indef x p q).toTrivalent I o c) = posExt ((conj p q).toTrivalent I o c) := by
  rw [posExt_indef]
  refine Set.sep_eq_self_iff_mem_true.2 fun _ hi ↦ ?_
  obtain ⟨-, hr⟩ := toTrivalent_eq_one_iff.1 hi
  exact realize_indef_of_ne_bot (hp _ _ hr.1) hr.1 hr.2

theorem posExt_iota_of_update_eq (h : update I o c p = c) :
    posExt ((iota x p q).toTrivalent I o c) =
      {i | p.Realize I i.1 i.2} ∩ posExt (q.toTrivalent I o c) := by
  ext
  simp only [Trivalent.mem_posExt, toTrivalent_eq_one_iff, satt_iota, h, realize_iota,
    Set.mem_inter_iff, Set.mem_ofPred_eq, true_and]
  tauto

/-- A definite whose restrictor changes the context is satt nowhere (p. 1104). -/
theorem posExt_iota_eq_empty (h : update I o c p ≠ c) :
    posExt ((iota x p q).toTrivalent I o c) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hi ↦
    h ((satt_iota (x := x) (q := q)).1 (toTrivalent_eq_one_iff.1 hi).1).1

/-- Double negation changes neither dimension of a meaning (p. 1109). -/
@[simp] theorem toTrivalent_neg_neg :
    (neg (neg p)).toTrivalent I o c = p.toTrivalent I o c :=
  funext fun _ ↦ SignType.eq_of_eq_zero_iff_of_eq_one_iff (by simp) (by simp)

/-! ### The update calculus -/

/-- A conjunction updates in sequence, the reason the paper's points carry over to sequences
(fn. 20). -/
theorem update_conj : update I .asymmetric c (conj p q) =
    update I .asymmetric (update I .asymmetric c p) q := by
  rw [update_eq_inter_posExt, posExt_conj, ← Set.inter_assoc, ← update_eq_inter_posExt,
    ← update_eq_inter_posExt]

theorem update_indef :
    update I o c (indef x p q) =
      {i ∈ update I o c (conj p q) | (indef x p q).Realize I i.1 i.2} := by
  rw [update_eq_inter_posExt, posExt_indef, update_eq_inter_posExt]
  exact Set.ext fun _ ↦ and_assoc.symm

theorem update_indef_of_ne_bot (hp : ∀ g w, p.Realize I g w → g x ≠ ⊥) :
    update I o c (indef x p q) = update I o c (conj p q) := by
  rw [update_eq_inter_posExt, posExt_indef_of_ne_bot hp, ← update_eq_inter_posExt]

theorem update_iota_of_update_eq (h : update I .asymmetric c p = c) :
    update I .asymmetric c (iota x p q) = update I .asymmetric c (conj p q) := by
  have hp : c ⊆ {i | p.Realize I i.1 i.2} := fun i hi ↦ (h.ge hi).2.1
  rw [update_conj, h, update_eq_inter_posExt, posExt_iota_of_update_eq h,
    ← Set.inter_assoc, Set.inter_eq_left.2 hp, ← update_eq_inter_posExt]

/-- A definite whose restrictor is not idle on the context empties it (p. 1104). -/
theorem update_iota_eq_empty (h : update I o c p ≠ c) : update I o c (iota x p q) = ∅ := by
  rw [update_eq_inter_posExt, posExt_iota_eq_empty h, Set.inter_empty]

theorem update_iota_top_eq_empty (h : ∃ i ∈ c, i.1 x = ⊥) :
    update I o c (iota x (top x) q) = ∅ := by
  obtain ⟨i, hi, hx⟩ := h
  exact update_iota_eq_empty fun he ↦ (he.ge hi).2.1 hx

@[simp] theorem update_neg_neg : update I o c (neg (neg p)) = update I o c p := by
  rw [update_eq_inter_posExt, toTrivalent_neg_neg, ← update_eq_inter_posExt]

/-! ### One-place atoms -/

/-- The one-place atom `Rx`. -/
def atom₁ (R : L.Relations 1) (x : V) : Formula L V Δ := atom R ![x]

variable {S : W → Set E} {R : L.Relations 1}

@[simp] theorem realize_atom₁ : (atom₁ R x).Realize I g w ↔ ∃ a ∈ extension I R w, g x = a := by
  refine ⟨fun ⟨es, h, hR⟩ ↦ ⟨es 0, ?_, h 0⟩, fun ⟨a, ha, hx⟩ ↦ ⟨![a], fun i ↦ ?_, ha⟩⟩
  · rw [mem_extension]; convert hR; ext i; fin_cases i; rfl
  · fin_cases i; exact hx

@[simp] theorem satt_atom₁ : (atom₁ R x).Satt I o c g w ↔ g x ≠ ⊥ := by
  simp [atom₁]

theorem ne_bot_of_realize_atom₁ (h : (atom₁ R x).Realize I g w) : g x ≠ ⊥ :=
  ne_bot_of_mem_valuedIn (S := extension I R) (i := (g, w)) (realize_atom₁.1 h)

/-- The two-place atom `R(x, y)`. -/
def atom₂ (R : L.Relations 2) (x y : V) : Formula L V Δ := atom R ![x, y]

theorem realize_atom₂ {R : L.Relations 2} {y : V} :
    (atom₂ R x y : Formula L V Δ).Realize I g w ↔
      ∃ a b : E, g x = a ∧ g y = b ∧ (I w).RelMap R ![a, b] := by
  refine ⟨fun ⟨es, h, hR⟩ ↦ ⟨es 0, es 1, h 0, h 1, ?_⟩,
    fun ⟨a, b, hx, hy, hR⟩ ↦ ⟨![a, b], fun k ↦ ?_, hR⟩⟩
  · convert hR; ext k; fin_cases k <;> rfl
  · fin_cases k
    · exact hx
    · exact hy

theorem satt_atom₂ {R : L.Relations 2} {y : V} :
    (atom₂ R x y : Formula L V Δ).Satt I o c g w ↔ g x ≠ ⊥ ∧ g y ≠ ⊥ := by
  refine ⟨fun h ↦ ⟨h 0, h 1⟩, fun ⟨hx, hy⟩ k ↦ ?_⟩
  fin_cases k
  · exact hx
  · exact hy

theorem setOf_realize_atom₁ :
    {i : Assign V Δ E × W | (atom₁ R x).Realize I i.1 i.2} = valuedIn x (extension I R) :=
  Set.ext fun _ ↦ realize_atom₁

theorem posExt_atom₁ : posExt ((atom₁ R x).toTrivalent I o c) = valuedIn x (extension I R) := by
  ext
  rw [Trivalent.mem_posExt, toTrivalent_eq_one_iff, satt_atom₁, realize_atom₁]
  exact ⟨And.right, fun h ↦ ⟨ne_bot_of_mem_valuedIn h, h⟩⟩

theorem posExt_top : posExt ((top x : Formula L V Δ).toTrivalent I o c) = {i | i.1 x ≠ ⊥} :=
  Set.ext fun _ ↦ toTrivalent_eq_one_iff.trans and_self_iff

theorem update_atom₁ : update I o c (atom₁ R x) = c ∩ valuedIn x (extension I R) := by
  rw [update_eq_inter_posExt, posExt_atom₁]

theorem update_atom₁_of_subset (h : c ⊆ valuedIn x (extension I R)) :
    update I o c (atom₁ R x) = c := by
  rw [update_atom₁, Set.inter_eq_left.2 h]

theorem update_top_of_subset (h : c ⊆ valuedIn x S) : update I o c (top x) = c := by
  have hx : c ⊆ {i | i.1 x ≠ ⊥} := fun i hi ↦ ne_bot_of_mem_valuedIn (h hi)
  rw [update_eq_inter_posExt, posExt_top, Set.inter_eq_left.2 hx]

end Formula

open Formula

variable {L : Language} {V Δ W E : Type*} [DecidableEq V] {I : W → L.Structure E} {o : Order}
  {c : Set (Assign V Δ E × W)} {g : Assign V Δ E} {w : W} {p q : Formula L V Δ} {x : V}

/-! ### Indefinites open files (§5.4) -/

section Updating

variable (F G H : L.Relations 1)

theorem realize_indef_atom₁ : (indef x (atom₁ F x) (atom₁ G x)).Realize I g w ↔
    (extension I F w ∩ extension I G w).Nonempty := by
  simp [Set.Nonempty]

theorem satt_indef_atom₁ [Nonempty E] : (indef x (atom₁ F x) (atom₁ G x)).Satt I .asymmetric c g w ↔
    ((extension I F w ∩ extension I G w).Nonempty →
      (g, w) ∈ valuedIn x (extension I F ⊓ extension I G)) := by
  obtain ⟨e⟩ := ‹Nonempty E›
  have hg' : ∃ g' : Assign V Δ E, g' x ≠ ⊥ ∧ g' x ≠ ⊥ := ⟨⟨fun _ ↦ e, fun _ _ ↦ ⊥⟩, by simp⟩
  rw [satt_indef, realize_indef_atom₁, ← valuedIn_inter_valuedIn]
  simp only [satt_conj, satt_atom₁, hg', true_and, realize_conj, realize_atom₁, Set.mem_inter_iff,
    mem_valuedIn]
  grind [Flat.coe_ne_bot]

theorem exists_satt_indef_atom₁ [Nonempty E] (c : Set (Assign V Δ E × W)) (w : W) :
    ∃ g, (indef x (atom₁ F x) (atom₁ G x)).Satt I .asymmetric c g w := by
  obtain h | ⟨a, ha⟩ := (extension I F w ∩ extension I G w).eq_empty_or_nonempty
  · exact ⟨⊥, (satt_indef_atom₁ F G).2 fun hne ↦ absurd h hne.ne_empty⟩
  · exact ⟨⟨fun _ ↦ a, fun _ _ ↦ ⊥⟩, (satt_indef_atom₁ F G).2 fun _ ↦ ⟨a, ha, rfl⟩⟩

theorem posExt_indef_atom₁ :
    posExt ((indef x (atom₁ F x) (atom₁ G x)).toTrivalent I .asymmetric c) =
      valuedIn x (extension I F ⊓ extension I G) := by
  rw [posExt_indef_of_ne_bot fun _ _ ↦ ne_bot_of_realize_atom₁, posExt_conj, posExt_atom₁,
    posExt_atom₁, valuedIn_inter_valuedIn]

/-- Updating with `ɜx(Fx, Gx)` keeps the points whose `x` is an `F` and a `G` (p. 1103). -/
theorem update_indef_atom₁ :
    update I .asymmetric c (indef x (atom₁ F x) (atom₁ G x)) =
      c ∩ valuedIn x (extension I F ⊓ extension I G) := by
  rw [update_eq_inter_posExt, posExt_indef_atom₁]

/-- Once some world has an `F` that is `G`, the null context does not admit `ɜx(Fx, Gx)` in
Stalnaker's sense (p. 1103). -/
theorem not_univ_subset_support_indef_atom₁
    (h : ∃ w, (extension I F w ∩ extension I G w).Nonempty) :
    ¬ Set.univ ⊆ Function.support (toTrivalent I .asymmetric (Set.univ : Set (Assign V Δ E × W))
      (indef x (atom₁ F x) (atom₁ G x))) := by
  obtain ⟨w, a, hF, hG⟩ := h
  intro hadm
  have hs : (indef x (atom₁ F x) (atom₁ G x)).Satt I .asymmetric Set.univ (⊥ : Assign V Δ E) w :=
    toTrivalent_eq_zero_iff.not_left.1 (hadm (Set.mem_univ ((⊥ : Assign V Δ E), w)))
  have hr : (indef x (atom₁ F x) (atom₁ G x)).Realize I (⊥ : Assign V Δ E) w :=
    ⟨a, realize_atom₁.2 ⟨a, hF, by simp⟩, realize_atom₁.2 ⟨a, hG, by simp⟩⟩
  exact ne_bot_of_realize_atom₁ (realize_conj_of_satt_indef hs hr).1 rfl

/-- After `ɜx(Fx, Gx)`, the definite `ιx(Fx, Hx)` is familiar, and true and satt where `x` is an
`F` and an `H` (p. 1104). -/
theorem posExt_iota_after_indef_atom₁ :
    posExt ((iota x (atom₁ F x) (atom₁ H x)).toTrivalent I
        .asymmetric (update I .asymmetric c (indef x (atom₁ F x) (atom₁ G x)))) =
      valuedIn x (extension I F ⊓ extension I H) := by
  have hc : update I .asymmetric c (indef x (atom₁ F x) (atom₁ G x))
      ⊆ valuedIn x (extension I F) := by
    rw [update_indef_atom₁]
    exact fun i hi ↦ valuedIn_mono inf_le_left hi.2
  rw [posExt_iota_of_update_eq (update_atom₁_of_subset hc), setOf_realize_atom₁,
    posExt_atom₁, valuedIn_inter_valuedIn]

/-- After `ɜx(Fx, Gx)`, the pronoun `ιx(⊤x, Hx)` is familiar, and true and satt where `x` is an
`H` (p. 1104). -/
theorem posExt_iota_top_after_indef_atom₁ :
    posExt ((iota x (top x) (atom₁ H x)).toTrivalent I
        .asymmetric (update I .asymmetric c (indef x (atom₁ F x) (atom₁ G x)))) =
      valuedIn x (extension I H) := by
  have hc : update I .asymmetric c (indef x (atom₁ F x) (atom₁ G x))
      ⊆ valuedIn x (extension I F) := by
    rw [update_indef_atom₁]
    exact fun i hi ↦ valuedIn_mono inf_le_left hi.2
  rw [posExt_iota_of_update_eq (update_top_of_subset hc), posExt_atom₁]
  exact Set.inter_eq_right.2 fun _ hi ↦ ne_bot_of_mem_valuedIn hi

theorem satt_iota_top_after_indef_atom₁ : (iota x (top x) (atom₁ H x)).Satt I .asymmetric
    (update I .asymmetric c (indef x (atom₁ F x) (atom₁ G x))) g w := by
  rw [satt_iota, update_top_of_subset (S := extension I F) fun i hi ↦ by
    rw [update_indef_atom₁] at hi; exact valuedIn_mono inf_le_left hi.2]
  exact ⟨rfl, satt_atom₁.2⟩

/-- *There is a cat. The cat is tabby.* keeps the points whose `x` is a cat that exists and is
tabby (p. 1104). -/
theorem update_indef_then_the :
    update I .asymmetric (update I .asymmetric c (indef x (atom₁ F x) (atom₁ G x)))
      (iota x (atom₁ F x) (atom₁ H x)) =
      c ∩ valuedIn x (extension I F ⊓ extension I G ⊓ extension I H) := by
  rw [update_eq_inter_posExt, posExt_iota_after_indef_atom₁, update_indef_atom₁,
    Set.inter_assoc, valuedIn_inter_valuedIn, ← inf_inf_distrib_left, ← inf_assoc]

/-- *There is a cat. It is tabby.* keeps the same points (p. 1104). -/
theorem update_indef_then_it :
    update I .asymmetric (update I .asymmetric c (indef x (atom₁ F x) (atom₁ G x)))
      (iota x (top x) (atom₁ H x)) =
      c ∩ valuedIn x (extension I F ⊓ extension I G ⊓ extension I H) := by
  rw [update_eq_inter_posExt, posExt_iota_top_after_indef_atom₁, update_indef_atom₁,
    Set.inter_assoc, valuedIn_inter_valuedIn]

/-! ### Negated indefinites (§5.5) -/

/-- A negated indefinite is true and satt where the negated existential is true, at the worlds
with no `F` that is `G` (pp. 1106–1107). -/
theorem posExt_neg_indef_atom₁ [Nonempty E] :
    posExt ((neg (indef x (atom₁ F x) (atom₁ G x))).toTrivalent I .asymmetric c) =
      {i | extension I F i.2 ∩ extension I G i.2 = ∅} := by
  ext ⟨g, w⟩
  simp only [Trivalent.mem_posExt, toTrivalent_eq_one_iff, realize_neg, satt_neg, satt_indef_atom₁,
    realize_indef_atom₁, Set.mem_ofPred_eq, Set.not_nonempty_iff_eq_empty]
  exact ⟨And.right, fun hr ↦ ⟨fun h ↦ absurd hr h.ne_empty, hr⟩⟩

/-- If some world has no `F` that is `G`, updating the null context with `¬ɜx(Fx, Gx)` and then a
pronoun on `x` leaves nothing (19) (p. 1106). -/
theorem update_null_neg_indef_then_it (h : ∃ w, extension I F w ∩ extension I G w = ∅) :
    update I .asymmetric (update I .asymmetric (Set.univ : Set (Assign V Δ E × W))
      (neg (indef x (atom₁ F x) (atom₁ G x))))
      (iota x (top x) (atom₁ H x)) = ∅ := by
  cases isEmpty_or_nonempty E
  · refine Set.subset_eq_empty (update_subset.trans fun i hi ↦ ?_) rfl
    obtain ⟨⟨g', hg', -⟩, -⟩ := hi.2.2
    obtain ⟨a, -⟩ := Flat.ne_bot_iff_exists.1 (satt_atom₁.1 hg')
    exact isEmptyElim a
  obtain ⟨w, hw⟩ := h
  refine update_iota_top_eq_empty ⟨(⊥, w), ?_, rfl⟩
  rw [update_eq_inter_posExt, posExt_neg_indef_atom₁]
  exact ⟨Set.mem_univ _, hw⟩

end Updating

/-! ### Bound entailment (§5.6) -/

section Entailment

variable (I) in
/-- `p` bound-entails `q` when at every context `p` Strawson-entails `q`, with the bounds in the
role of presuppositions, so that `q` is true wherever both are satt and `p` is true (p. 1108). -/
def BoundEntails (o : Order) (p q : Formula L V Δ) : Prop :=
  ∀ c, strawsonEntails (p.toTrivalent I o c) (q.toTrivalent I o c)

variable (I) in
/-- Bound entailment in both directions. -/
def BoundEquiv (o : Order) (p q : Formula L V Δ) : Prop := AntisymmRel (BoundEntails I o) p q

variable (I) in
/-- `p` logically entails `q` when `q` is true wherever `p` is (p. 1108). -/
def LogicallyEntails (p q : Formula L V Δ) : Prop := ∀ g w, p.Realize I g w → q.Realize I g w

theorem boundEntails_iff : BoundEntails I o p q ↔
    ∀ c g w, p.Satt I o c g w → q.Satt I o c g w → p.Realize I g w → q.Realize I g w := by
  simp only [BoundEntails, strawsonEntails, Prod.forall, toTrivalent_eq_one_iff, ne_eq,
    toTrivalent_eq_zero_iff, not_not]
  exact forall₃_congr fun _ _ _ ↦
    ⟨fun h hp hq hr ↦ (h ⟨hp, hr⟩ hq).2, fun h ⟨hp, hr⟩ hq ↦ ⟨hq, h hp hq hr⟩⟩

@[refl] protected theorem BoundEntails.refl (o : Order) (p : Formula L V Δ) :
    BoundEntails I o p p :=
  fun _ _ h _ ↦ h

instance (o : Order) : Std.Refl (BoundEntails (V := V) (Δ := Δ) I o) := ⟨BoundEntails.refl o⟩

/-- The bounded logic extends the logic (p. 1109). -/
theorem LogicallyEntails.boundEntails (h : LogicallyEntails I p q) (o : Order) :
    BoundEntails I o p q :=
  boundEntails_iff.2 fun _ g w _ _ ↦ h g w

end Entailment

/-! ### Open scope (§5.6) -/

section OpenScope

/-- (20-a) `ɜx(F, G & H)`, *some F is G and H*. -/
def ex20a (x : V) (F G H : Formula L V Δ) : Formula L V Δ := indef x F (conj G H)

/-- (20-b) `ɜx(F, G) & ιx(F, H)`, *some F is G, and the F is H*. -/
def ex20b (x : V) (F G H : Formula L V Δ) : Formula L V Δ := conj (indef x F G) (iota x F H)

/-- (20-c) `ɜx(F, G) & ιx(⊤x, H)`, *some F is G, and it is H*. -/
def ex20c (x : V) (F G H : Formula L V Δ) : Formula L V Δ := conj (indef x F G) (iota x (top x) H)

variable {F G H : Formula L V Δ}

theorem boundEntails_ex20a_ex20b : BoundEntails I .asymmetric (ex20a x F G H) (ex20b x F G H) := by
  rw [boundEntails_iff]
  rintro c g w hs - hr
  obtain ⟨hF, -, hH⟩ := realize_conj_of_satt_indef hs hr
  obtain ⟨a, haF, haG, -⟩ := hr
  exact ⟨⟨a, haF, haG⟩, hF, hH⟩

theorem boundEntails_ex20c_ex20b : BoundEntails I .asymmetric (ex20c x F G H) (ex20b x F G H) := by
  rw [boundEntails_iff]
  rintro c g w hs - ⟨hl, -, hH⟩
  exact ⟨hl, (realize_conj_of_satt_indef hs.1 hl).1, hH⟩

theorem boundEntails_ex20c_ex20a : BoundEntails I .asymmetric (ex20c x F G H) (ex20a x F G H) := by
  rw [boundEntails_iff]
  rintro c g w hs - ⟨hl, hx, hH⟩
  obtain ⟨hF, hG⟩ := realize_conj_of_satt_indef hs.1 hl
  exact realize_indef_of_ne_bot hx hF ⟨hG, hH⟩

theorem boundEntails_ex20b_ex20a (hF : ∀ g w, F.Realize I g w → g x ≠ ⊥) :
    BoundEntails I .asymmetric (ex20b x F G H) (ex20a x F G H) := by
  rw [boundEntails_iff]
  rintro c g w hs - ⟨hl, hFg, hH⟩
  exact realize_indef_of_ne_bot (hF g w hFg) hFg ⟨(realize_conj_of_satt_indef hs.1 hl).2, hH⟩

theorem boundEntails_ex20b_ex20c (hF : ∀ g w, F.Realize I g w → g x ≠ ⊥) :
    BoundEntails I .asymmetric (ex20b x F G H) (ex20c x F G H) := by
  rw [boundEntails_iff]
  rintro c g w - - ⟨hl, hFg, hH⟩
  exact ⟨hl, hF g w hFg, hH⟩

theorem boundEntails_ex20a_ex20c (hF : ∀ g w, F.Realize I g w → g x ≠ ⊥) :
    BoundEntails I .asymmetric (ex20a x F G H) (ex20c x F G H) := by
  rw [boundEntails_iff]
  rintro c g w hs - hr
  obtain ⟨hFg, -, hH⟩ := realize_conj_of_satt_indef hs hr
  obtain ⟨a, haF, haG, -⟩ := hr
  exact ⟨⟨a, haF, haG⟩, hF g w hFg, hH⟩

/-- (20-a) and (20-b) are bound-equivalent when the restrictor's truth values `x` (p. 1108). -/
theorem boundEquiv_ex20a_ex20b (hF : ∀ g w, F.Realize I g w → g x ≠ ⊥) :
    BoundEquiv I .asymmetric (ex20a x F G H) (ex20b x F G H) :=
  ⟨boundEntails_ex20a_ex20b, boundEntails_ex20b_ex20a hF⟩

/-- (20-b) and (20-c) are bound-equivalent when the restrictor's truth values `x` (p. 1108). -/
theorem boundEquiv_ex20b_ex20c (hF : ∀ g w, F.Realize I g w → g x ≠ ⊥) :
    BoundEquiv I .asymmetric (ex20b x F G H) (ex20c x F G H) :=
  ⟨boundEntails_ex20b_ex20c hF, boundEntails_ex20c_ex20b⟩

/-- (20-a) and (20-c) are bound-equivalent when the restrictor's truth values `x` (p. 1108). -/
theorem boundEquiv_ex20a_ex20c (hF : ∀ g w, F.Realize I g w → g x ≠ ⊥) :
    BoundEquiv I .asymmetric (ex20a x F G H) (ex20c x F G H) :=
  ⟨boundEntails_ex20a_ex20c hF, boundEntails_ex20c_ex20a⟩

/-- At a point of its context, (20-a) bound-entails (20-c) for any formulae. -/
theorem realize_ex20c_of_realize_ex20a (hc : (g, w) ∈ c)
    (hs : (ex20a x F G H).Satt I .asymmetric c g w)
    (hs' : (ex20c x F G H).Satt I .asymmetric c g w) (hr : (ex20a x F G H).Realize I g w) :
    (ex20c x F G H).Realize I g w := by
  obtain ⟨hFg, hG, hH⟩ := realize_conj_of_satt_indef hs hr
  obtain ⟨a, haF, haG, haH⟩ := hr
  obtain ⟨⟨g', hg'F, hg'G, -⟩, hw⟩ := hs
  have hmem : (g, w) ∈ update I .asymmetric c (indef x F G) :=
    ⟨hc, ⟨a, haF, haG⟩, ⟨g', hg'F, hg'G⟩, fun _ ↦
      ⟨⟨hFg, hG⟩, (hw ⟨a, haF, haG, haH⟩).2.1, (hw ⟨a, haF, haG, haH⟩).2.2.1⟩⟩
  exact ⟨⟨a, haF, haG⟩, ((satt_iota.1 hs'.2).1.ge hmem).2.1, hH⟩

/-- At a point of its context, (20-b) bound-entails (20-c) for any formulae. -/
theorem realize_ex20c_of_realize_ex20b (hc : (g, w) ∈ c)
    (hs : (ex20b x F G H).Satt I .asymmetric c g w)
    (hs' : (ex20c x F G H).Satt I .asymmetric c g w) (hr : (ex20b x F G H).Realize I g w) :
    (ex20c x F G H).Realize I g w :=
  ⟨hr.1, ((satt_iota.1 hs'.2).1.ge ⟨hc, hr.1, hs.1⟩).2.1, hr.2.2⟩

variable (F G H : L.Relations 1)

/-- (20-a) is true and satt exactly where `x` is an `F`, a `G` and an `H` (p. 1108). -/
theorem posExt_ex20a :
    posExt ((ex20a x (atom₁ F x) (atom₁ G x) (atom₁ H x)).toTrivalent I .asymmetric c) =
      valuedIn x (extension I F ⊓ extension I G ⊓ extension I H) := by
  rw [ex20a, posExt_indef_of_ne_bot fun _ _ ↦ ne_bot_of_realize_atom₁, posExt_conj,
    posExt_conj, posExt_atom₁, posExt_atom₁, posExt_atom₁, ← Set.inter_assoc,
    valuedIn_inter_valuedIn, valuedIn_inter_valuedIn]

/-- So is (20-b) (p. 1108). -/
theorem posExt_ex20b :
    posExt ((ex20b x (atom₁ F x) (atom₁ G x) (atom₁ H x)).toTrivalent I .asymmetric c) =
      valuedIn x (extension I F ⊓ extension I G ⊓ extension I H) := by
  rw [ex20b, posExt_conj, posExt_indef_atom₁, posExt_iota_after_indef_atom₁,
    valuedIn_inter_valuedIn, ← inf_inf_distrib_left, ← inf_assoc]

/-- (20-c) is satt and true exactly where `x` is an `F` that is `G` and `H`, so (20-a)–(20-c) update
alike (p. 1108, footnote 23). -/
theorem posExt_ex20c :
    posExt ((ex20c x (atom₁ F x) (atom₁ G x) (atom₁ H x)).toTrivalent I .asymmetric c) =
      valuedIn x (extension I F ⊓ extension I G ⊓ extension I H) := by
  rw [ex20c, posExt_conj, posExt_indef_atom₁, posExt_iota_top_after_indef_atom₁,
    valuedIn_inter_valuedIn]

/-- The formulations of (20) differ, since where some `F` is `G` and `H` but `x` is not `H`, (20-a)
is true and (20-b) false (p. 1108). -/
theorem realize_ex20a_and_not_realize_ex20b
    (h : (extension I F w ∩ extension I G w ∩ extension I H w).Nonempty) {b : E}
    (hb : g x = b) (hH : b ∉ extension I H w) :
    (ex20a x (atom₁ F x) (atom₁ G x) (atom₁ H x)).Realize I g w ∧
      ¬ (ex20b x (atom₁ F x) (atom₁ G x) (atom₁ H x)).Realize I g w := by
  obtain ⟨a, ⟨hF, hG⟩, haH⟩ := h
  refine ⟨⟨a, by simpa using hF, by simpa using hG, by simpa using haH⟩, fun ⟨_, _, h⟩ ↦ ?_⟩
  obtain ⟨c, hc, hgc⟩ := realize_atom₁.1 h
  exact hH (Flat.coe_injective (hb.symm.trans hgc) ▸ hc)

end OpenScope

/-! ### Classicality (§5.7) -/

section Classicality

/-- `¬¬p` and `p` are logically, hence bound-, equivalent (p. 1109). -/
theorem boundEquiv_neg_neg : BoundEquiv I o (neg (neg p)) p :=
  ⟨LogicallyEntails.boundEntails (fun _ _ ↦ by simp) o,
    LogicallyEntails.boundEntails (fun _ _ ↦ by simp) o⟩

/-- `¬p ∨ q` and `¬p ∨ (p & q)` are logically, hence bound-, equivalent (p. 1109). -/
theorem boundEquiv_disj_neg_conj : BoundEquiv I o (disj (neg p) q) (disj (neg p) (conj p q)) :=
  ⟨LogicallyEntails.boundEntails (fun _ _ ↦ by simp; tauto) o,
    LogicallyEntails.boundEntails (fun _ _ ↦ by simp; tauto) o⟩

variable (F G H : L.Relations 1)

/-- A doubly negated indefinite licenses a subsequent definite as the indefinite does (p. 1109). -/
theorem update_neg_neg_indef_then_the :
    update I .asymmetric (update I .asymmetric c (neg (neg (indef x (atom₁ F x) (atom₁ G x)))))
        (iota x (atom₁ F x) (atom₁ H x)) =
      c ∩ valuedIn x (extension I F ⊓ extension I G ⊓ extension I H) := by
  rw [update_neg_neg, update_indef_then_the]

/-- The bathroom disjunction is true and satt exactly where Susie is childless or `x` is her child
at boarding school (p. 1109). -/
theorem posExt_bathroom [Nonempty E] :
    posExt ((disj (neg (indef x (atom₁ F x) (atom₁ G x)))
        (iota x (atom₁ F x) (atom₁ H x))).toTrivalent I .asymmetric c) =
      {i | extension I F i.2 ∩ extension I G i.2 = ∅} ∪
        valuedIn x (extension I F ⊓ extension I G ⊓ extension I H) := by
  obtain ⟨e⟩ := ‹Nonempty E›
  have hι : ∀ (g : Assign V Δ E) w, (iota x (atom₁ F x) (atom₁ H x)).Satt I .asymmetric
      (update I .asymmetric c (neg (neg (indef x (atom₁ F x) (atom₁ G x))))) g w := fun g w ↦ by
    rw [update_neg_neg, satt_iota, update_atom₁_of_subset fun i hi ↦ by
      rw [update_indef_atom₁] at hi; exact valuedIn_mono inf_le_left hi.2]
    exact ⟨rfl, fun h ↦ satt_atom₁.2 (ne_bot_of_realize_atom₁ h)⟩
  ext ⟨g, w⟩
  simp only [Trivalent.mem_posExt, toTrivalent_eq_one_iff, satt_disj, hι, and_true, satt_neg,
    satt_indef, satt_conj, satt_atom₁, realize_disj, realize_neg, realize_conj, realize_iota,
    realize_indef_atom₁, Set.mem_union, Set.mem_ofPred_eq, mem_valuedIn,
    ← Set.not_nonempty_iff_eq_empty]
  simp only [show ∃ g' : Assign V Δ E, g' x ≠ ⊥ ∧ g' x ≠ ⊥ from ⟨⟨fun _ ↦ e, fun _ _ ↦ ⊥⟩, by simp⟩,
    true_and]
  obtain hgx | ⟨b, hgx⟩ := (em (g x = ⊥)).imp_right Flat.ne_bot_iff_exists.1
  · simp [hgx]
  · simp only [Set.Nonempty, Set.mem_inter_iff, mem_extension, realize_atom₁, hgx, Flat.coe_inj,
      exists_eq_right', ne_eq, Flat.coe_ne_bot, not_false_eq_true, and_self, and_true,
      forall_exists_index, and_imp, not_exists, not_and, Pi.inf_apply, Set.inf_eq_inter]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact .inl h2
      · by_cases hA : ∀ a : E, (I w).RelMap F ![a] → ¬ (I w).RelMap G ![a]
        · exact .inl hA
        · obtain ⟨a, hF, hG⟩ : ∃ a : E, (I w).RelMap F ![a] ∧ (I w).RelMap G ![a] := by
            simpa using hA
          exact .inr ⟨h1 a hF hG, h2.2⟩
    · rintro (hA | ⟨hFG, hH⟩)
      · exact ⟨fun a hF hG ↦ (hA a hF hG).elim, .inl hA⟩
      · exact ⟨fun _ _ _ ↦ hFG, .inr ⟨hFG.1, hH⟩⟩

/-- (16-a) *Either there isn't a bathroom, or it is upstairs* is felicitous in the null context (p.
1105). -/
theorem felicitous_bathroom [Nonempty W] [Nonempty E] : Felicitous I .asymmetric Set.univ
    (disj (neg (indef x (atom₁ F x) (atom₁ G x))) (iota x (top x) (atom₁ H x)) :
      Formula L V Δ) := by
  obtain ⟨w⟩ := ‹Nonempty W›
  obtain ⟨g, hg⟩ := exists_satt_indef_atom₁ (I := I) (x := x) F G Set.univ w
  exact ⟨(g, w), trivial, satt_disj.2
    ⟨hg, by rw [update_neg_neg]; exact satt_iota_top_after_indef_atom₁ F G H⟩⟩

end Classicality

/-! ### Order (§5.5) -/

section Order

variable (S M C : L.Relations 1) (x : V)

/-- With asymmetric local contexts, (15-a) `ɜx(Mx, Cx) & ιx(⊤x, Sx)` is felicitous in the null
context (p. 1105). -/
theorem felicitous_ex15a_asymmetric [Nonempty W] [Nonempty E] : Felicitous I .asymmetric Set.univ
    (conj (indef x (atom₁ M x) (atom₁ C x)) (iota x (top x) (atom₁ S x)) : Formula L V Δ) := by
  obtain ⟨w⟩ := ‹Nonempty W›
  obtain ⟨g, hg⟩ := exists_satt_indef_atom₁ (I := I) (x := x) M C Set.univ w
  exact ⟨(g, w), trivial, hg, satt_iota_top_after_indef_atom₁ M C S⟩

/-- (15-b) *He sat down and a man came in*, `ιx(⊤x, Sx) & ɜx(Mx, Cx)`. -/
def ex15b : Formula L V Δ := conj (iota x (top x) (atom₁ S x)) (indef x (atom₁ M x) (atom₁ C x))

/-- With asymmetric local contexts (15-b) is infelicitous in the null context, since its
pronoun's familiarity bound fails at the points not valuing `x` (p. 1106). -/
theorem not_felicitous_ex15b_asymmetric [Nonempty W] :
    ¬ Felicitous I .asymmetric Set.univ (ex15b (Δ := Δ) S M C x) := by
  rintro ⟨i, -, hi⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  exact (hi.1.1 (⊥, w) trivial).1 rfl

/-- With symmetric local contexts, (15-b) is satt in the null context wherever `x` is a man who came
in (p. 1106). -/
theorem satt_ex15b_symmetric (hM : (atom₁ M x : Formula L V Δ).Realize I g w)
    (hC : (atom₁ C x : Formula L V Δ).Realize I g w) :
    (ex15b (Δ := Δ) S M C x).Satt I .symmetric Set.univ g w := by
  have hx : g x ≠ ⊥ := ne_bot_of_realize_atom₁ hM
  have hj : ∀ j ∈ {j ∈ (Set.univ : Set (Assign V Δ E × W)) |
      (indef x (atom₁ M x) (atom₁ C x)).Realize I j.1 j.2 ∧
        (indef x (atom₁ M x) (atom₁ C x)).Satt I .symmetric Set.univ j.1 j.2}, j.1 x ≠ ⊥ :=
    fun j hj ↦ ne_bot_of_realize_atom₁ (hj.2.2.2 hj.2.1).1.1
  exact ⟨⟨fun j hj' ↦ ⟨hj j hj', hj j hj'⟩, fun _ ↦ satt_atom₁.2 hx⟩,
    ⟨⟨g, satt_atom₁.2 hx, satt_atom₁.2 hx⟩,
      fun _ ↦ ⟨⟨hM, hC⟩, satt_atom₁.2 hx, satt_atom₁.2 hx⟩⟩⟩

end Order

/-! ### Logically equivalent, differently updating (§2) -/

section Partee

variable (Ch Sues B : L.Relations 1) (Par : L.Relations 0) (x : V)

/-- *Sue has a child*, `ɜx(child(x), Sue's(x))`. -/
def hasChild : Formula L V Δ := indef x (atom₁ Ch x) (atom₁ Sues x)

/-- *Sue is a parent*, an atom with no variable. -/
def isParent : Formula L V Δ := atom Par ![]

variable {Ch Sues B Par x}

/-- Where being a parent is having a child, *Sue has a child* and *Sue is a parent* are
logically equivalent ((2), p. 1093). -/
theorem logicallyEquivalent_hasChild_isParent
    (hPar : ∀ w, (I w).RelMap Par ![] ↔ ∃ b, (I w).RelMap Ch ![b] ∧ (I w).RelMap Sues ![b]) :
    LogicallyEntails I (hasChild (Δ := Δ) Ch Sues x) (isParent Par) ∧
      LogicallyEntails I (isParent (Δ := Δ) Par) (hasChild Ch Sues x) := by
  constructor
  · rintro g w ⟨b, h₁, h₂⟩
    obtain ⟨a, ha, hx⟩ := realize_atom₁.1 h₁
    obtain ⟨a', ha', hx'⟩ := realize_atom₁.1 h₂
    obtain rfl := Flat.coe_injective (hx.symm.trans hx')
    exact ⟨![], fun i ↦ i.elim0, (hPar w).2 ⟨a, ha, ha'⟩⟩
  · rintro g w ⟨es, -, hR⟩
    rw [Subsingleton.elim es ![]] at hR
    obtain ⟨b, hb, hb'⟩ := (hPar w).1 hR
    exact ⟨b, realize_atom₁.2 ⟨b, hb, by simp⟩, realize_atom₁.2 ⟨b, hb', by simp⟩⟩

/-- After *Sue is a parent*, a pronoun on `x` empties any context with a point not valuing `x` ((2),
(9), pp. 1093 and 1104). -/
theorem update_isParent_then_it (c : Set (Assign V Δ E × W))
    (h : ∃ i ∈ update I .asymmetric c (isParent Par), i.1 x = ⊥) :
    update I .asymmetric (update I .asymmetric c (isParent Par)) (iota x (top x) (atom₁ B x)) =
      ∅ :=
  update_iota_top_eq_empty h

end Partee

/-! ### Quantifiers (§5.8) -/

section Quantifiers

variable (Pa Ch : L.Relations 1) (Of Lv : L.Relations 2) (x y : V) (δ : Δ)

/-- (21-b) *Every parent loves them*, `Q x^δ (parent(x), ιy(⊤y, loves(x, y)))`. -/
def ex21b (Q : Quantifier.NumberTree) : Formula L V Δ :=
  quant Q x δ (atom₁ Pa x) (iota y (top y) (atom₂ Lv x y))

/-- *Has a child*, `ɜy(child(y), of(y, x))`. -/
def hasChildOf : Formula L V Δ := indef y (atom₁ Ch y) (atom₂ Of y x)

/-- (22-b) *Everyone who has a child loves them*,
`Q x^δ (ɜy(child(y), of(y, x)), ιy(⊤y, loves(x, y)))`. -/
def ex22b (Q : Quantifier.NumberTree) : Formula L V Δ :=
  quant Q x δ (hasChildOf Ch Of x y) (iota y (top y) (atom₂ Lv x y))

variable {Pa Ch Of Lv x y δ} {Q : Quantifier.NumberTree}

/-- (21-b) is satt only if `y` is valued at every point of the context where `x` is a parent (p.
1111). -/
theorem familiar_of_satt_ex21b (a : E) (h : (ex21b Pa Lv x y δ Q).Satt I o c g w) :
    ∀ j ∈ c, (atom₁ Pa x).Realize I j.1 j.2 → j.1 y ≠ ⊥ := fun j hj hP ↦
  ((Order.junct_right (h a).2.1).1 j ⟨hj, hP, satt_atom₁.2 (ne_bot_of_realize_atom₁ hP)⟩).1

/-- So in the null context (21-b) is infelicitous once some world has a parent (p. 1111). -/
theorem not_felicitous_ex21b (hxy : x ≠ y) (hP : ∃ (w : W) (a : E), (I w).RelMap Pa ![a]) :
    ¬ Felicitous I o Set.univ (ex21b Pa Lv x y δ Q) := by
  rintro ⟨i, -, hi⟩
  obtain ⟨w, a, ha⟩ := hP
  refine familiar_of_satt_ex21b a hi (((⊥ : Assign V Δ E).update x a), w) trivial
    (realize_atom₁.2 ⟨a, ha, by simp⟩) ?_
  simp [Assign.update_apply_of_ne (Ne.symm hxy)]

/-- Where `y` is familiar, (21-b) has only the reading on which every parent loves one fixed
individual (p. 1111). -/
theorem realize_ex21b_iff_of_familiar (hxy : x ≠ y)
    (hs : (ex21b Pa Lv x y δ Q).Satt I o c g w) (hy : Familiar c y) :
    (ex21b Pa Lv x y δ Q).Realize I g w ↔ Q.toGQ (fun a ↦ (I w).RelMap Pa ![a])
      (fun a ↦ (I w).RelMap Pa ![a] ∧ ∃ b : E, g y = ↑b ∧ (I w).RelMap Lv ![a, b]) := by
  have hdom : ∀ a, (g.pair δ x a) y = g y := fun a ↦ by
    rw [Assign.pair_apply, PartialAssign.update_of_ne (Ne.symm hxy), (hs a).2.2 y hy]
  have hP : ∀ a, (atom₁ Pa x : Formula L V Δ).Realize I (g.pair δ x a) w ↔ (I w).RelMap Pa ![a] :=
    fun a ↦ by simp [Assign.pair_apply]
  have hL : ∀ a, (iota y (top y) (atom₂ Lv x y) : Formula L V Δ).Realize I (g.pair δ x a) w ↔
      ∃ b : E, g y = ↑b ∧ (I w).RelMap Lv ![a, b] := fun a ↦ by
    simp only [realize_iota, realize_top, realize_atom₂, hdom, Assign.pair_apply,
      PartialAssign.update_self, Flat.coe_inj]
    constructor
    · rintro ⟨-, a', b, rfl, hb, hR⟩; exact ⟨b, hb, hR⟩
    · rintro ⟨b, hb, hR⟩; exact ⟨by rw [hb]; exact Flat.coe_ne_bot, a, b, rfl, hb, hR⟩
  simp only [ex21b, realize_quant, hP, hL]

theorem satt_hasChildOf_iff [Nonempty E] :
    (hasChildOf Ch Of x y : Formula L V Δ).Satt I o c g w ↔
      ((hasChildOf Ch Of x y).Realize I g w →
        (atom₁ Ch y).Realize I g w ∧ (atom₂ Of y x).Realize I g w) := by
  obtain ⟨e⟩ := ‹Nonempty E›
  have hj : ∀ (g' : Assign V Δ E), g' y ≠ ⊥ → g' x ≠ ⊥ →
      o.junct ((atom₁ Ch y : Formula L V Δ).Satt I o) ((atom₂ Of y x).Satt I o)
        ((atom₁ Ch y).Realize I) ((atom₂ Of y x).Realize I) c g' w := fun g' hy hx ↦ by
    cases o <;> exact ⟨satt_atom₁.2 hy, satt_atom₂.2 ⟨hy, hx⟩⟩
  refine ⟨fun h hr ↦ (h.2 hr).1, fun h ↦ ⟨⟨⟨fun _ ↦ e, fun _ _ ↦ ⊥⟩,
    hj _ Flat.coe_ne_bot Flat.coe_ne_bot⟩, fun hr ↦ ⟨h hr, ?_⟩⟩⟩
  obtain ⟨a, b, ha, hb, -⟩ := realize_atom₂.1 (h hr).2
  exact hj g (by rw [ha]; exact Flat.coe_ne_bot) (by rw [hb]; exact Flat.coe_ne_bot)

/-- (22-b) is satt, even with `y` novel, iff its pairing gives each individual with a child one of
its children and fixes familiar variables (p. 1110). -/
theorem satt_ex22b_iff [Nonempty E] :
    (ex22b Ch Of Lv x y δ Q).Satt I o c g w ↔ ∀ a,
      ((hasChildOf Ch Of x y).Realize I (g.pair δ x a) w →
        (atom₁ Ch y).Realize I (g.pair δ x a) w ∧ (atom₂ Of y x).Realize I (g.pair δ x a) w) ∧
      ∀ z, Familiar c z → g.dom δ a z = g z := by
  refine ⟨fun h a ↦ ⟨satt_hasChildOf_iff.1 (h a).1, (h a).2.2⟩, fun h a ↦ ?_⟩
  have hp : ∀ c', (hasChildOf Ch Of x y).Satt I o c' (g.pair δ x a) w :=
    fun _ ↦ satt_hasChildOf_iff.2 (h a).1
  have hq : (iota y (top y) (atom₂ Lv x y)).Satt I o
      {j ∈ c | (hasChildOf Ch Of x y).Realize I j.1 j.2 ∧
        (hasChildOf Ch Of x y).Satt I o c j.1 j.2} (g.pair δ x a) w := by
    refine ⟨fun j hj ↦ ?_, fun hy ↦ satt_atom₂.2 ⟨by simp [Assign.pair_apply], hy⟩⟩
    have := ne_bot_of_realize_atom₁ (satt_hasChildOf_iff.1 hj.2.2 hj.2.1).1
    exact ⟨this, this⟩
  refine ⟨hp c, ?_, (h a).2⟩
  cases o
  · exact ⟨hp c, hq⟩
  · exact ⟨hp _, hq⟩

/-- (22-b) is true iff the number tree relates the individuals with a child to those loving their
paired child, the covarying reading (p. 1111). -/
theorem realize_ex22b_iff (hxy : x ≠ y) :
    (ex22b Ch Of Lv x y δ Q).Realize I g w ↔
      Q.toGQ (fun a ↦ ∃ b, (I w).RelMap Ch ![b] ∧ (I w).RelMap Of ![b, a])
        (fun a ↦ (∃ b, (I w).RelMap Ch ![b] ∧ (I w).RelMap Of ![b, a]) ∧
          ∃ b : E, g.dom δ a y = ↑b ∧ (I w).RelMap Lv ![a, b]) := by
  have hp : ∀ a, (hasChildOf Ch Of x y : Formula L V Δ).Realize I (g.pair δ x a) w ↔
      ∃ b, (I w).RelMap Ch ![b] ∧ (I w).RelMap Of ![b, a] := fun a ↦ by
    simp only [hasChildOf, realize_indef, realize_atom₁, realize_atom₂, mem_extension]
    constructor
    · rintro ⟨b, ⟨b', hb', hy'⟩, b₁, a₁, hb₁, ha₁, hOf⟩
      rw [Assign.update_apply_self, Flat.coe_inj] at hy' hb₁
      rw [Assign.update_apply_of_ne hxy, Assign.pair_apply, PartialAssign.update_self,
        Flat.coe_inj] at ha₁
      subst hy' hb₁ ha₁
      exact ⟨b, hb', hOf⟩
    · rintro ⟨b, hCh, hOf⟩
      exact ⟨b, ⟨b, hCh, by simp⟩, b, a, by simp, by
        rw [Assign.update_apply_of_ne hxy, Assign.pair_apply, PartialAssign.update_self], hOf⟩
  have hq : ∀ a, (iota y (top y) (atom₂ Lv x y) : Formula L V Δ).Realize I (g.pair δ x a) w ↔
      ∃ b : E, g.dom δ a y = ↑b ∧ (I w).RelMap Lv ![a, b] := fun a ↦ by
    simp only [realize_iota, realize_top, realize_atom₂, Assign.pair_apply,
      PartialAssign.update_of_ne (Ne.symm hxy), PartialAssign.update_self, Flat.coe_inj]
    constructor
    · rintro ⟨-, a', b, rfl, hb, hR⟩; exact ⟨b, hb, hR⟩
    · rintro ⟨b, hb, hR⟩; exact ⟨by rw [hb]; exact Flat.coe_ne_bot, a, b, rfl, hb, hR⟩
  simp only [ex22b, realize_quant, hp, hq]

end Quantifiers

/-! ### Footnote 20 -/

section Footnote20

/-- A language with two relation symbols of each arity, `false` and `true`. -/
abbrev L₂ : Language := ⟨fun _ ↦ Empty, fun _ ↦ Bool⟩

/-- Two worlds over a one-element domain, at both of which the relation `false` is empty, while
the relation `true` is full at world `true` and empty at world `false`. -/
@[reducible] def I₂ (w : Bool) : L₂.Structure Unit where
  funMap f := f.elim
  RelMap r _ := r = true ∧ w = true

@[simp] theorem relMap_I₂ {w : Bool} {n : ℕ} {r : L₂.Relations n} {es : Fin n → Unit} :
    (I₂ w).RelMap r es ↔ r = true ∧ w = true :=
  Iff.rfl

/-- The formula `¬ɜy(⊤y, r(x, y))` with `x = 0` and `y = 1`, saying that `x` bears `r` to
nothing; it is free in `x`, yet true when `x` is unvalued. -/
def bearsNothing (r : Bool) : Formula L₂ ℕ Empty :=
  neg (indef 1 (top 1) (atom (show L₂.Relations 2 from r) ![0, 1]))

theorem realize_bearsNothing_false (g : Assign ℕ Empty Unit) (w : Bool) :
    (bearsNothing false).Realize I₂ g w := by
  simp [bearsNothing]

theorem realize_bearsNothing_bot (r w : Bool) : (bearsNothing r).Realize I₂ ⊥ w := by
  simp [bearsNothing]

theorem realize_bearsNothing_true_iff (a : Unit) (w : Bool) :
    (bearsNothing true).Realize I₂ ((⊥ : Assign ℕ Empty Unit).update 0 a) w ↔ w = false := by
  cases w <;> simp [bearsNothing]

theorem satt_bearsNothing_false (c) (g : Assign ℕ Empty Unit) (w : Bool) :
    (bearsNothing false).Satt I₂ .asymmetric c g w :=
  ⟨⟨⟨fun _ ↦ (↑() : Flat Unit), fun _ _ ↦ ⊥⟩, by simp, by simp⟩,
    fun h ↦ absurd h (realize_neg.1 (realize_bearsNothing_false g w))⟩

theorem satt_bearsNothing_bot (r : Bool) (c) (w : Bool) :
    (bearsNothing r).Satt I₂ .asymmetric c ⊥ w :=
  ⟨⟨⟨fun _ ↦ (↑() : Flat Unit), fun _ _ ↦ ⊥⟩, by simp, by simp⟩,
    fun h ↦ absurd h (realize_neg.1 (realize_bearsNothing_bot r w))⟩

local notation "F₀" => bearsNothing false
local notation "H₀" => bearsNothing true

/-- (20-b) is satt and true at every context and the empty assignment. -/
theorem holds_ex20b (c) (w : Bool) :
    (ex20b 0 F₀ F₀ H₀).Satt I₂ .asymmetric c ⊥ w ∧ (ex20b 0 F₀ F₀ H₀).Realize I₂ ⊥ w :=
  ⟨⟨⟨⟨⊥, satt_bearsNothing_false _ _ _, satt_bearsNothing_false _ _ _⟩, fun _ ↦
      ⟨⟨realize_bearsNothing_false _ _, realize_bearsNothing_false _ _⟩,
        satt_bearsNothing_false _ _ _, satt_bearsNothing_false _ _ _⟩⟩,
      fun _ _ ↦ ⟨realize_bearsNothing_false _ _, satt_bearsNothing_false _ _ _⟩,
      fun _ ↦ satt_bearsNothing_bot _ _ _⟩,
    ⟨⟨(), realize_bearsNothing_false _ _, realize_bearsNothing_false _ _⟩,
      realize_bearsNothing_bot _ _, realize_bearsNothing_bot _ _⟩⟩

theorem realize_ex20a_iff (w : Bool) : (ex20a 0 F₀ F₀ H₀).Realize I₂ ⊥ w ↔ w = false := by
  simp only [ex20a, realize_indef, realize_conj, realize_bearsNothing_true_iff,
    realize_bearsNothing_false, true_and, exists_const]

theorem satt_ex20a (c) (w : Bool) : (ex20a 0 F₀ F₀ H₀).Satt I₂ .asymmetric c ⊥ w :=
  ⟨⟨⊥, satt_bearsNothing_false _ _ _, satt_bearsNothing_false _ _ _, satt_bearsNothing_bot _ _ _⟩,
    fun _ ↦ ⟨⟨realize_bearsNothing_bot _ _, realize_bearsNothing_bot _ _,
      realize_bearsNothing_bot _ _⟩, satt_bearsNothing_bot _ _ _, satt_bearsNothing_bot _ _ _,
      satt_bearsNothing_bot _ _ _⟩⟩

/-- (20-c) is satt but false at the empty context and assignment, where its pronoun's variable
is unvalued. -/
theorem satt_ex20c (w : Bool) : (ex20c 0 F₀ F₀ H₀).Satt I₂ .asymmetric ∅ ⊥ w :=
  ⟨(holds_ex20b ∅ w).1.1, fun _ hi ↦ absurd hi.1 (Set.notMem_empty _), fun h ↦ (h rfl).elim⟩

theorem not_realize_ex20c (w : Bool) : ¬ (ex20c 0 F₀ F₀ H₀).Realize I₂ ⊥ w :=
  fun h ↦ h.2.1 rfl

/-- (20-b) does not bound-entail (20-a) when the restrictor is `¬ɜy(⊤y, R(x, y))`. -/
theorem not_boundEntails_ex20b_ex20a :
    ¬ BoundEntails I₂ .asymmetric (ex20b 0 F₀ F₀ H₀) (ex20a 0 F₀ F₀ H₀) :=
  fun h ↦ Bool.noConfusion <| (realize_ex20a_iff true).1 <|
    boundEntails_iff.1 h Set.univ ⊥ true (holds_ex20b _ _).1 (satt_ex20a _ _)
      (holds_ex20b Set.univ _).2

/-- (20-a) does not bound-entail (20-c) for the same restrictor, though it does at points of the
context. -/
theorem not_boundEntails_ex20a_ex20c :
    ¬ BoundEntails I₂ .asymmetric (ex20a 0 F₀ F₀ H₀) (ex20c 0 F₀ F₀ H₀) :=
  fun h ↦ not_realize_ex20c false <|
    boundEntails_iff.1 h ∅ ⊥ false (satt_ex20a _ _) (satt_ex20c _) ((realize_ex20a_iff false).2 rfl)

/-- Nor does (20-b) bound-entail (20-c), again at a point outside the empty context
(`realize_ex20c_of_realize_ex20b`). -/
theorem not_boundEntails_ex20b_ex20c :
    ¬ BoundEntails I₂ .asymmetric (ex20b 0 F₀ F₀ H₀) (ex20c 0 F₀ F₀ H₀) :=
  fun h ↦ not_realize_ex20c true <|
    boundEntails_iff.1 h ∅ ⊥ true (holds_ex20b _ _).1 (satt_ex20c _) (holds_ex20b ∅ _).2

end Footnote20

end Mandelkern2022
