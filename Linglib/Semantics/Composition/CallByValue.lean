module

public import Linglib.Semantics.Composition.Mode.Basic
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.PredicateAbstraction

/-!
# Partial functions

Heim and Kratzer let a function be undefined at some of its arguments, as the definite article is
at a predicate not true of exactly one individual, and from there on every function type is the
type of partial functions. This is the call-by-value translation of types at the effect of
partiality: a function returns a partial value, and a constituent has one. Functional
application is then [Structured App followed by Join](##Interpreter.Application.evalCbv_fa), and
predicate modification is defined where both predicates are. A total value has a partial value
that is it, and [application](##Interpreter.Application.partRel_evalCbv) and [predicate
modification](##Interpreter.PredicateModification.partRel_evalCbv) keep the two related, so a
constituent with no partial word in it never lacks a value.

## Main definitions

* `Interpreter.Ty.cbv`: the type whose functions are partial.
* `Interpreter.Application.evalCbv`, `Interpreter.PredicateModification.evalCbv`: application and
  predicate modification on partial values of partial functions.
* `Interpreter.Ty.PDom`: the partial values of a type whose functions are partial, with the
  structures of application and predicate modification on them.
* `Interpreter.Assignments.partial`: partial assignments, with abstracts that are partial
  functions.
* `Interpreter.partialValued`: constituents as partial values where only some words are partial,
  undefined where a daughter is.
* `Interpreter.Ty.CbvRel`, `Interpreter.Ty.PartRel`: a total value and the value, or partial
  value, that is it.
## References

* [heim-kratzer-1998]
* [moggi-1991]
-/

@[expose] public section

open ManySorted

namespace Interpreter

variable {B : Type} {D : B → Type}

namespace Ty

/-- The call-by-value translation of a type at partiality: every function is a partial
function. -/
@[reducible] def cbv : Ty B → Ty B
  | .fn a b => .fn a.cbv (.comp .M b.cbv)
  | .t => .t
  | .base b => .base b
  | .comp f a => .comp f a

@[simp] theorem cbv_fn (a b : Ty B) : (a ⇒ b).cbv = (a.cbv ⇒ .comp .M b.cbv) := rfl

@[simp] theorem cbv_t : (.t : Ty B).cbv = .t := rfl

@[simp] theorem cbv_base (b : B) : (.base b : Ty B).cbv = .base b := rfl

/-- A total value and the value of the translated type that is it: a function and a partial
function defined at every total argument, with the value that is the function's. -/
def CbvRel : (a : Ty B) → a.Dom D → a.cbv.Dom D → Prop
  | .fn a b, f, f' => ∀ x x', CbvRel a x x' → ∃ y, f' x' = .some y ∧ CbvRel b (f x) y
  | .t, p, p' => p = p'
  | .base _, x, x' => x = x'
  | .comp _ _, x, x' => x = x'

/-- A total value and the partial value that is it: defined, and it. -/
def PartRel (a : Ty B) (x : a.Dom D) (x' : Part (a.cbv.Dom D)) : Prop :=
  ∃ y, x' = .some y ∧ CbvRel a x y

theorem PartRel.dom {a : Ty B} {x : a.Dom D} {x' : Part (a.cbv.Dom D)} (h : PartRel a x x') :
    x'.Dom := by
  obtain ⟨y, rfl, -⟩ := h
  trivial

theorem cbvRel_fn_iff {a b : Ty B} {f : (a ⇒ b).Dom D} {f' : (a ⇒ b).cbv.Dom D} :
    CbvRel (a ⇒ b) f f' ↔ ∀ x x', CbvRel a x x' → PartRel b (f x) (f' x') :=
  Iff.rfl

@[simp] theorem cbvRel_t {p p' : Prop} : CbvRel (D := D) .t p p' ↔ p = p' := Iff.rfl

@[simp] theorem cbvRel_base {b : B} {x x' : D b} : CbvRel (D := D) (.base b) x x' ↔ x = x' :=
  Iff.rfl

end Ty

/-- Application of a partial value that is a partial function to a partial value: defined where
both are and the function is at the argument. -/
@[simp] def Application.evalCbv (D : B → Type) : {l r u : Ty B} → Application l r u →
    Part (l.cbv.Dom D) → Part (r.cbv.Dom D) → Part (u.cbv.Dom D)
  | _, _, _, .fa, f, x => f.bind fun g ↦ x.bind g
  | _, _, _, .ba, x, f => f.bind fun g ↦ x.bind g

/-- Predicate modification of two partial values that are partial predicates: defined where both
are, a predicate defined at what both are defined at. -/
@[simp] def PredicateModification.evalCbv (D : B → Type) : {l r u : Ty B} →
    PredicateModification l r u → Part (l.cbv.Dom D) → Part (r.cbv.Dom D) → Part (u.cbv.Dom D)
  | _, _, _, .pm, p, q => p.bind fun P ↦ q.map fun Q x ↦
      (P x).bind fun u ↦ (Q x).map fun v ↦ u ∧ v

/-- Application of a partial function is Structured App followed by Join. -/
theorem Application.evalCbv_fa {a b : Ty B} (f : Part ((a ⇒ b).cbv.Dom D))
    (x : Part (a.cbv.Dom D)) :
    Application.evalCbv D .fa f x =
      (.join (.ap (.basic .fa)) :
        Mode (application (B := B)).Binary (.comp .M (a.cbv ⇒ .comp .M b.cbv))
          (.comp .M a.cbv) (.comp .M b.cbv)).eval D f x := by
  change _ = Eff.join .M inferInstance (Eff.map .M id (Eff.seq .M inferInstance
    (Eff.map .M (fun g y ↦ Application.eval D .fa g y) f) x))
  simp [Application.evalCbv, Eff.join, Eff.seq, Eff.map, Application.eval, Part.bind_assoc,
    Part.bind_map]

/-- Application takes total values and the partial values that are them to a total value and the
partial value that is it. -/
theorem Application.partRel_evalCbv : ∀ {l r u : Ty B} (m : Application l r u) {x : l.Dom D}
    {x' : Part (l.cbv.Dom D)} {y : r.Dom D} {y' : Part (r.cbv.Dom D)},
    Ty.PartRel l x x' → Ty.PartRel r y y' →
      Ty.PartRel u (Application.eval D m x y) (Application.evalCbv D m x' y')
  | _, _, _, .fa, _, _, _, _, ⟨g, hg, hgr⟩, ⟨y, hy, hyr⟩ => by
    obtain ⟨z, hz, hzr⟩ := hgr _ _ hyr
    refine ⟨z, ?_, hzr⟩
    subst hg hy
    exact (Part.bind_some _ _).trans ((Part.bind_some _ _).trans hz)
  | _, _, _, .ba, _, _, _, _, ⟨y, hy, hyr⟩, ⟨g, hg, hgr⟩ => by
    obtain ⟨z, hz, hzr⟩ := hgr _ _ hyr
    refine ⟨z, ?_, hzr⟩
    subst hg hy
    exact (Part.bind_some _ _).trans ((Part.bind_some _ _).trans hz)

/-- Predicate modification takes total predicates and the partial values that are them to a
total predicate and the partial value that is it. -/
theorem PredicateModification.partRel_evalCbv : ∀ {l r u : Ty B}
    (m : PredicateModification l r u) {x : l.Dom D} {x' : Part (l.cbv.Dom D)} {y : r.Dom D}
    {y' : Part (r.cbv.Dom D)}, Ty.PartRel l x x' → Ty.PartRel r y y' →
      Ty.PartRel u (PredicateModification.eval D m x y) (PredicateModification.evalCbv D m x' y')
  | _, _, _, .pm, _, _, _, _, ⟨P, hP, hPr⟩, ⟨Q, hQ, hQr⟩ => by
    subst hP hQ
    refine ⟨fun x ↦ (P x).bind fun u ↦ (Q x).map fun v ↦ u ∧ v,
      by rw [PredicateModification.evalCbv, Part.bind_some, Part.map_some], fun x x' hx ↦ ?_⟩
    obtain ⟨u, hu, hur⟩ := hPr _ _ hx
    obtain ⟨v, hv, hvr⟩ := hQr _ _ hx
    refine ⟨u ∧ v, ?_, ?_⟩
    · show ((P x').bind fun u ↦ (Q x').map fun v ↦ u ∧ v) = _
      rw [hu, Part.bind_some, hv]
      exact Part.map_some _ _
    · cases hur
      cases hvr
      rfl

/-- The partial values of a type whose functions are partial. -/
abbrev Ty.PDom (D : B → Type) (a : Ty B) : Type := Part (a.cbv.Dom D)

instance (D : B → Type) : (application (B := B)).Structure (Ty.PDom D) :=
  .mk₂ nofun (Application.evalCbv D)

instance (D : B → Type) : (predicateModification (B := B)).Structure (Ty.PDom D) :=
  .mk₂ nofun (PredicateModification.evalCbv D)

/-- Application and predicate modification on total values and on partial values of partial
functions are logically related: a constituent of words with total values has the partial value
that is its total one. -/
theorem isLogicalRel_partRel :
    (inferInstance : (application.sum predicateModification).Structure
      (Ty.Dom D)).IsLogicalRel
      (inferInstance : (application.sum predicateModification).Structure
        (Ty.PDom D)) Ty.PartRel :=
  .sum (.mk₂ nofun fun m _ _ _ _ h₁ h₂ ↦ m.partRel_evalCbv h₁ h₂)
    (.mk₂ nofun fun m _ _ _ _ h₁ h₂ ↦ m.partRel_evalCbv h₁ h₂)

/-- Partial assignments: an assignment may give an index no value, and an abstract always has a
value, a partial function defined where its body has one. -/
def Assignments.partial (D : B → Type) (Γ : ℕ → Ty B) :
    Assignments (∀ n, Ty.PDom D (Γ n)) (Ty.PDom D) Γ where
  get g n := g n
  set g n v := Function.update g n v
  lam F := .some fun x ↦ F (.some x)

/-! ### Partial values where a word has them

Where only some words are partial, their types say so, and constituents are partial values
combined by the rules of a grammar where both sisters are defined. -/

/-- The partial-valued interpreter: every constituent is a partial value, and sisters combine by
a rule of the grammar on their values where both are defined, a partial result of the rule
flattened. A function applied to an undefined argument is undefined. -/
def partialValued [DecidableEq B] (G : Language (Ty B)) [G.LocallyFinite] {N : Type} :
    Interpreter (effectGrammar G) N where
  unary _ _ := []
  binary
    | .comp .M l, .comp .M r =>
      (Language.LocallyFinite.binaryRules (L := G) l r).map fun
        | ⟨.comp .M u, p⟩ => ⟨.comp .M u, .join (.ap (.basic p))⟩
        | ⟨u, p⟩ => ⟨.comp .M u, .ap (.basic p)⟩
    | _, _ => []

section PartialValued

variable {G : Language (Ty B)} {D : B → Type} [M : G.Structure (Ty.Dom D)] {l r u : Ty B}

/-- A rule on two partial values: defined where both are. -/
theorem Mode.eval_ap_basic (p : G.Binary l r u) (x : Part (l.Dom D)) (y : Part (r.Dom D)) :
    (Mode.ap (.basic p) :
      Mode G.Binary (.comp .M l) (.comp .M r) (.comp .M u)).eval D x y =
      x.bind fun a ↦ y.map fun b ↦ M.funMap p (a, b) := by
  change Eff.seq .M inferInstance (Eff.map .M (fun a b ↦ M.funMap p (a, b)) x) y = _
  simp [Eff.seq, Eff.map, Part.bind_map]

/-- A rule with a partial result, on two partial values: defined where both are and the rule is
at their values. -/
theorem Mode.eval_join_ap_basic (p : G.Binary l r (.comp .M u)) (x : Part (l.Dom D))
    (y : Part (r.Dom D)) :
    (Mode.join (.ap (.basic p)) :
      Mode G.Binary (.comp .M l) (.comp .M r) (.comp .M u)).eval D x y =
      x.bind fun a ↦ y.bind fun b ↦ M.funMap p (a, b) := by
  change Eff.join .M inferInstance (Eff.map .M id (Eff.seq .M inferInstance
    (Eff.map .M (fun a b ↦ M.funMap p (a, b)) x) y)) = _
  simp [Eff.join, Eff.seq, Eff.map, Part.bind_assoc, Part.bind_map]

end PartialValued

end Interpreter
