module

public import Linglib.Semantics.Composition.Interpreter.Effect
public import Linglib.Semantics.Composition.Interpreter.Basic

/-!
# The effect-driven grammar

Bumford and Charlow's grammar takes whatever basic modes of combination a theory has and closes
them under meta-modes, each lifting a mode through an effect by the structure the effect has: Map
Left and Map Right by its map, Structured App and the Unit modes where it is applicative, Join
where it is a monad, Co-unit and Eject for the adjunction of storing and reading, and Lower for a
continuation at its own result type. The types of two daughters decide which modes combine them,
and `Ty.combine` lists them all.

## Main definitions

* `Interpreter.Grammar.application`, `Interpreter.Grammar.predicateModification`,
  `Interpreter.Grammar.eventIdentification`: the grammars of functional application, predicate
  modification and event identification, each with its structure and the list of its rules.
* `Interpreter.Grammar.length_binaryRules_application_sum_predicateModification_le_one`: at most
  one rule of application and predicate modification applies to two types.
* `Interpreter.Mode`: the basic modes closed under the meta-modes.
* `Interpreter.Mode.eval`: the meaning of a mode, by the operations of the effects.
* `Interpreter.Ty.combine`: every mode by which two types combine, the book's `combine`.
* `Interpreter.Abstraction`, `Interpreter.Assignments`: abstraction over an index, and how
  assignments give indices values and are modified.
* `Interpreter.Node`, `Interpreter.effectDriven`: what the semantics reads off a node, and the
  rules each kind of node admits.
* `Interpreter.partialValued`: constituents as partial values, undefined where a daughter is.
* `Interpreter.effectGrammar`: the grammar whose binary rules are the modes.

## Implementation notes

`Ty.combine` follows the book's interpreter rule for rule and in its order. Eject does not make
its types smaller, so the recursion is on a bound, three steps for each unit of size, which the
book's argument that no Eject feeds another justifies.

## TODO

That `Ty.combine` finds every mode, the book's claim that the interpreter finds every
interpretation, is not proved.

## References

* [bumford-charlow-2026]
* [heim-kratzer-1998]
* [kratzer-1996]
-/

@[expose] public section

namespace Interpreter

variable {B : Type}

mutual

/-- The size of a type. -/
def Ty.size : Ty B → ℕ
  | .t | .base _ => 1
  | .fn a b => a.size + b.size + 1
  | .comp f a => f.size + a.size + 1

/-- The size of an effect. -/
def Eff.size : Eff B → ℕ
  | .S | .M => 1
  | .R i | .W i | .C i => i.size + 1

end

/-- Functional application, forward and backward. -/
inductive Application : Ty B → Ty B → Ty B → Type
  /-- Forward application. -/
  | fa {a b : Ty B} : Application (a ⇒ b) a b
  /-- Backward application. -/
  | ba {a b : Ty B} : Application a (a ⇒ b) b

/-- Predicate modification, the conjunction of two predicates of one type. -/
inductive PredicateModification : Ty B → Ty B → Ty B → Type
  /-- Predicate modification. -/
  | pm {a : Ty B} : PredicateModification (a ⇒ .t) (a ⇒ .t) (a ⇒ .t)

/-- The meaning of application. -/
@[simp] def Application.eval (D : B → Type) :
    {l r u : Ty B} → Application l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .fa, f, x => f x
  | _, _, _, .ba, x, f => f x

/-- The meaning of predicate modification. -/
@[simp] def PredicateModification.eval (D : B → Type) :
    {l r u : Ty B} → PredicateModification l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .pm, p, q => fun x ↦ p x ∧ q x

/-- The grammar of functional application. -/
@[reducible] def Grammar.application : Grammar (Ty B) := ⟨fun _ _ ↦ Empty, Application⟩

instance (D : B → Type) : (Grammar.application (B := B)).language.Structure (Ty.Dom D) :=
  Grammar.structure nofun (Application.eval D)

/-- Whichever daughter is a function of the other's type applies to it. -/
instance [DecidableEq B] : (Grammar.application (B := B)).LocallyFinite where
  unaryRules _ := []
  binaryRules l r :=
    (match l with
      | .fn a b => if h : a = r then [⟨b, h ▸ .fa⟩] else []
      | _ => []) ++
    match r with
      | .fn a b => if h : a = l then [⟨b, h ▸ .ba⟩] else []
      | _ => []
  mem_unaryRules := nofun
  mem_binaryRules m := by cases m <;> simp

@[simp] theorem Grammar.application.funMap_fa {D : B → Type} {a b : Ty B} (f : (a ⇒ b).Dom D)
    (x : a.Dom D) :
    MSFirstOrder.Language.Structure.funMap (L := (Grammar.application (B := B)).language)
      (D := Ty.Dom D) (Grammar.Sym.binary .fa) (f, x) = f x :=
  rfl

@[simp] theorem Grammar.application.funMap_ba {D : B → Type} {a b : Ty B} (x : a.Dom D)
    (f : (a ⇒ b).Dom D) :
    MSFirstOrder.Language.Structure.funMap (L := (Grammar.application (B := B)).language)
      (D := Ty.Dom D) (Grammar.Sym.binary .ba) (x, f) = f x :=
  rfl

/-- The grammar of predicate modification. -/
@[reducible] def Grammar.predicateModification : Grammar (Ty B) :=
  ⟨fun _ _ ↦ Empty, PredicateModification⟩

instance (D : B → Type) :
    (Grammar.predicateModification (B := B)).language.Structure (Ty.Dom D) :=
  Grammar.structure nofun (PredicateModification.eval D)

/-- Two predicates of one type are conjoined. -/
instance [DecidableEq B] : (Grammar.predicateModification (B := B)).LocallyFinite where
  unaryRules _ := []
  binaryRules l r :=
    match l with
    | .fn a .t => if h : r = (a ⇒ .t) then [⟨a ⇒ .t, by subst h; exact .pm⟩] else []
    | _ => []
  mem_unaryRules := nofun
  mem_binaryRules m := by cases m; simp

@[simp] theorem Grammar.funMap_application_sum_predicateModification_inl {D : B → Type}
    {l r u : Ty B} (m : Application l r u) (p : l.Dom D × r.Dom D) :
    MSFirstOrder.Language.Structure.funMap
      (L := (Grammar.application.sum .predicateModification).language) (D := Ty.Dom D)
      (Grammar.Sym.binary
        (Sum.inl (α := Application l r u) (β := PredicateModification l r u) m)) p =
      Application.eval D m p.1 p.2 :=
  rfl

@[simp] theorem Grammar.funMap_application_sum_predicateModification_inr {D : B → Type}
    {l r u : Ty B} (m : PredicateModification l r u) (p : l.Dom D × r.Dom D) :
    MSFirstOrder.Language.Structure.funMap
      (L := (Grammar.application.sum .predicateModification).language) (D := Ty.Dom D)
      (Grammar.Sym.binary
        (Sum.inr (α := Application l r u) (β := PredicateModification l r u) m)) p =
      PredicateModification.eval D m p.1 p.2 :=
  rfl

theorem Ty.ne_fn_self (a b : Ty B) : a ≠ (a ⇒ b) := fun h ↦ by
  have := congrArg Ty.size h
  simp only [Ty.size] at this
  omega

theorem Ty.ne_fn_fn_self (a b c d : Ty B) (h : a = (c ⇒ d)) : c ≠ (a ⇒ b) := fun h' ↦ by
  have := congrArg Ty.size h
  have := congrArg Ty.size h'
  simp only [Ty.size] at *
  omega

/-- At most one rule of application and predicate modification applies to two types: a type is
not a function of itself, nor of a function of itself. -/
theorem Grammar.length_binaryRules_application_sum_predicateModification_le_one [DecidableEq B]
    (l r : Ty B) :
    (Grammar.LocallyFinite.binaryRules (G := Grammar.application.sum .predicateModification)
      l r).length ≤ 1 := by
  simp only [Grammar.LocallyFinite.binaryRules, List.length_append, List.length_map]
  rcases l with _ | _ | ⟨a, b⟩ | _ <;> rcases r with _ | _ | ⟨c, d⟩ | _ <;>
    (try rcases b with _ | _ | _ | _) <;> simp <;> split_ifs <;> (try simp) <;>
    first
    | exact Ty.ne_fn_fn_self _ _ _ _ (by assumption) (by assumption)
    | (obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›; exact Ty.ne_fn_self _ _ (by assumption))

/-- Event identification, for individuals of type `x` and events of type `s`: a relation of
individuals to events and a predicate of events are conjoined at the event. -/
inductive EventIdentification (x s : Ty B) : Ty B → Ty B → Ty B → Type
  /-- Event identification, the relation on the left. -/
  | left : EventIdentification x s (x ⇒ s ⇒ .t) (s ⇒ .t) (x ⇒ s ⇒ .t)
  /-- Event identification, the relation on the right. -/
  | right : EventIdentification x s (s ⇒ .t) (x ⇒ s ⇒ .t) (x ⇒ s ⇒ .t)

/-- The meaning of event identification. -/
def EventIdentification.eval (D : B → Type) {x s : Ty B} :
    {l r u : Ty B} → EventIdentification x s l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .left, f, g => fun y e ↦ f y e ∧ g e
  | _, _, _, .right, g, f => fun y e ↦ f y e ∧ g e

/-- The grammar of event identification. -/
@[reducible] def Grammar.eventIdentification (x s : Ty B) : Grammar (Ty B) :=
  ⟨fun _ _ ↦ Empty, EventIdentification x s⟩

instance (x s : Ty B) (D : B → Type) :
    (Grammar.eventIdentification x s).language.Structure (Ty.Dom D) :=
  Grammar.structure nofun (EventIdentification.eval D)

/-- A relation of individuals to events is identified with a predicate of events, in either
order. -/
instance [DecidableEq B] (x s : Ty B) : (Grammar.eventIdentification x s).LocallyFinite where
  unaryRules _ := []
  binaryRules l r :=
    (if h : l = (x ⇒ s ⇒ .t) ∧ r = (s ⇒ .t) then
      [⟨x ⇒ s ⇒ .t, by obtain ⟨rfl, rfl⟩ := h; exact .left⟩]
    else []) ++
    if h : l = (s ⇒ .t) ∧ r = (x ⇒ s ⇒ .t) then
      [⟨x ⇒ s ⇒ .t, by obtain ⟨rfl, rfl⟩ := h; exact .right⟩]
    else []
  mem_unaryRules := nofun
  mem_binaryRules m := by cases m <;> simp

/-- The modes of combination: a theory's basic modes closed under the meta-modes. -/
inductive Mode (Rule : Ty B → Ty B → Ty B → Type) : Ty B → Ty B → Ty B → Type
  /-- A basic mode. -/
  | basic {l r u : Ty B} (b : Rule l r u) : Mode Rule l r u
  /-- Map Right: a mode under the effect of the right daughter. -/
  | mapR {f : Eff B} {l r u : Ty B} (m : Mode Rule l r u) : Mode Rule l (.comp f r) (.comp f u)
  /-- Map Left: a mode under the effect of the left daughter. -/
  | mapL {f : Eff B} {l r u : Ty B} (m : Mode Rule l r u) : Mode Rule (.comp f l) r (.comp f u)
  /-- Structured App: a mode on the results of two daughters with one applicative effect. -/
  | ap {f : Eff B} {l r u : Ty B} (h : f.IsApplicative) (m : Mode Rule l r u) :
      Mode Rule (.comp f l) (.comp f r) (.comp f u)
  /-- Unit Right: a left daughter expecting a computation is given a pure one. -/
  | unitR {f : Eff B} {l l' r u : Ty B} (h : f.IsApplicative) (m : Mode Rule (l ⇒ l') r u) :
      Mode Rule (.comp f l ⇒ l') r u
  /-- Unit Left: a right daughter expecting a computation is given a pure one. -/
  | unitL {f : Eff B} {l r r' u : Ty B} (h : f.IsApplicative) (m : Mode Rule l (r ⇒ r') u) :
      Mode Rule l (.comp f r ⇒ r') u
  /-- Co-unit: what the left daughter stores is given to what the right daughter reads. -/
  | counit {i l r u : Ty B} (m : Mode Rule l r u) : Mode Rule (.comp (.W i) l) (.comp (.R i) r) u
  /-- Eject Right: reading is ejected from a right daughter that is a function into a reader. -/
  | ejectR {i l r r' u : Ty B} (m : Mode Rule l (.comp (.R i) (r ⇒ r')) u) :
      Mode Rule l (r ⇒ .comp (.R i) r') u
  /-- Eject Left: reading is ejected from a left daughter that is a function into a reader. -/
  | ejectL {i l l' r u : Ty B} (m : Mode Rule (.comp (.R i) (l ⇒ l')) r u) :
      Mode Rule (l ⇒ .comp (.R i) l') r u
  /-- Join: two layers of one monadic effect in the result are flattened. -/
  | join {f : Eff B} {l r u : Ty B} (h : f.IsApplicative)
      (m : Mode Rule l r (.comp f (.comp f u))) : Mode Rule l r (.comp f u)
  /-- Lower: a continuation at its own result type in the result is run at the identity. -/
  | lower {l r u : Ty B} (m : Mode Rule l r (.comp (.C u) u)) : Mode Rule l r u

namespace Mode

variable {Rule : Ty B → Ty B → Ty B → Type}

/-- The meaning of a mode over a grammar's rules, from a structure for the grammar: each
meta-mode is the operation of its effect. -/
def eval {G : Grammar (Ty B)} (D : B → Type) [M : G.language.Structure (Ty.Dom D)] :
    {l r u : Ty B} → Mode G.Binary l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .basic b, x, y => M.funMap (.binary b) (x, y)
  | _, _, _, .mapR (f := f) m, a, b => Eff.map f (fun y ↦ m.eval D a y) b
  | _, _, _, .mapL (f := f) m, a, b => Eff.map f (fun x ↦ m.eval D x b) a
  | _, _, _, .ap (f := f) h m, a, b =>
    Eff.seq f h (Eff.map f (fun x y ↦ m.eval D x y) a) b
  | _, _, _, .unitR (f := f) h m, a, b => m.eval D (fun x ↦ a (Eff.pure f h x)) b
  | _, _, _, .unitL (f := f) h m, a, b => m.eval D a fun y ↦ b (Eff.pure f h y)
  | _, _, _, .counit (i := i) m, a, b =>
    Eff.counit (Eff.map (.W i) (fun x ↦ Eff.map (.R i) (fun y ↦ m.eval D x y) b) a)
  | _, _, _, .ejectR m, a, b => m.eval D a (Eff.eject b)
  | _, _, _, .ejectL m, a, b => m.eval D (Eff.eject a) b
  | _, _, _, .join (f := f) h m, a, b => Eff.join f h (m.eval D a b)
  | _, _, _, .lower m, a, b => Eff.lower (m.eval D a b)

/-- The shape of a mode, forgetting its types. -/
inductive Shape (β : Type) where
  | basic (b : β)
  | mapR (m : Shape β)
  | mapL (m : Shape β)
  | ap (m : Shape β)
  | unitR (m : Shape β)
  | unitL (m : Shape β)
  | counit (m : Shape β)
  | ejectR (m : Shape β)
  | ejectL (m : Shape β)
  | join (m : Shape β)
  | lower (m : Shape β)
  deriving DecidableEq, Repr

/-- The shape of a mode, given the names of the basic modes. -/
def shape {β : Type} (name : ∀ {l r u : Ty B}, Rule l r u → β) :
    {l r u : Ty B} → Mode Rule l r u → Shape β
  | _, _, _, .basic b => .basic (name b)
  | _, _, _, .mapR m => .mapR (m.shape name)
  | _, _, _, .mapL m => .mapL (m.shape name)
  | _, _, _, .ap _ m => .ap (m.shape name)
  | _, _, _, .unitR _ m => .unitR (m.shape name)
  | _, _, _, .unitL _ m => .unitL (m.shape name)
  | _, _, _, .counit m => .counit (m.shape name)
  | _, _, _, .ejectR m => .ejectR (m.shape name)
  | _, _, _, .ejectL m => .ejectL (m.shape name)
  | _, _, _, .join _ m => .join (m.shape name)
  | _, _, _, .lower m => .lower (m.shape name)

end Mode

section Combine

variable [DecidableEq B] {Rule : Ty B → Ty B → Ty B → Type}
  (find : (l r : Ty B) → List (Σ u, Rule l r u))

/-- The Join of a mode whose result has two layers of one monadic effect. -/
def Mode.join? {l r : Ty B} : (Σ u, Mode Rule l r u) → List (Σ u, Mode Rule l r u)
  | ⟨.comp f (.comp g a), m⟩ =>
    if h : g = f then
      if ha : f.IsApplicative then [⟨.comp f a, .join ha (h ▸ m)⟩] else []
    else []
  | _ => []

/-- The Lower of a mode whose result is a continuation at its own result type. -/
def Mode.lower? {l r : Ty B} : (Σ u, Mode Rule l r u) → List (Σ u, Mode Rule l r u)
  | ⟨.comp (.C o) a, m⟩ => if h : o = a then [⟨a, .lower (h ▸ m)⟩] else []
  | _ => []

/-- `Ty.combine` to a bound on the depth of its recursion. -/
def Ty.combineAux : ℕ → (l r : Ty B) → List (Σ u, Mode Rule l r u)
  | 0, _, _ => []
  | k + 1, l, r =>
    (((find l r).map fun p ↦ (⟨p.1, .basic p.2⟩ : Σ u, Mode Rule l r u)) ++
      (match r with
        | .comp f y => (Ty.combineAux k l y).map fun p ↦ ⟨.comp f p.1, .mapR p.2⟩
        | _ => []) ++
      (match l with
        | .comp f x => (Ty.combineAux k x r).map fun p ↦ ⟨.comp f p.1, .mapL p.2⟩
        | _ => []) ++
      (match l, r with
        | .comp f x, .comp g y =>
          if h : g = f then
            if ha : f.IsApplicative then
              (Ty.combineAux k x y).map fun p ↦ ⟨.comp f p.1, by subst h; exact .ap ha p.2⟩
            else []
          else []
        | _, _ => []) ++
      (match l with
        | .fn (.comp f x) x' =>
          if ha : f.IsApplicative then
            (Ty.combineAux k (x ⇒ x') r).map fun p ↦ ⟨p.1, .unitR ha p.2⟩
          else []
        | _ => []) ++
      (match r with
        | .fn (.comp f y) y' =>
          if ha : f.IsApplicative then
            (Ty.combineAux k l (y ⇒ y')).map fun p ↦ ⟨p.1, .unitL ha p.2⟩
          else []
        | _ => []) ++
      (match l, r with
        | .comp (.W i) x, .comp (.R j) y =>
          if h : j = i then (Ty.combineAux k x y).map fun p ↦ ⟨p.1, h ▸ .counit p.2⟩ else []
        | _, _ => []) ++
      (match r with
        | .fn x (.comp (.R i) y) =>
          (Ty.combineAux k l (.comp (.R i) (x ⇒ y))).map fun p ↦ ⟨p.1, .ejectR p.2⟩
        | _ => []) ++
      (match l with
        | .fn x (.comp (.R i) y) =>
          (Ty.combineAux k (.comp (.R i) (x ⇒ y)) r).map fun p ↦ ⟨p.1, .ejectL p.2⟩
        | _ => [])).flatMap fun p ↦ p :: (Mode.join? p ++ Mode.lower? p)

/-- Every mode by which a left daughter of type `l` and a right daughter of type `r` combine. -/
def Ty.combine (l r : Ty B) : List (Σ u, Mode Rule l r u) :=
  Ty.combineAux find (3 * (l.size + r.size) + 3) l r

end Combine

/-! ### Binding, islands and the interface with syntax

A trace reads an assignment, and the index a moved phrase leaves abstracts over the value the
assignment gives it, an operation on what reads assignments. An island keeps only the meanings
whose types hold no unclosed continuation. So the syntax owes the semantics a bare structure whose
nodes are plain, islands, or indices. -/

/-- Abstraction over an index: from a computation that reads an assignment of type `g`, the
function of the value of type `x` that the assignment gives the index. -/
inductive Abstraction (g x : Ty B) : Ty B → Ty B → Type
  /-- Abstraction over the index `n`. -/
  | index (n : ℕ) (b : Ty B) : Abstraction g x (.comp (.R g) b) (.comp (.R g) (x ⇒ b))

/-- Assignments `A` of values in the domains `D` to indices, of which the values of type `x` are
bound: the value an assignment gives an index, an assignment modified at an index, and the value
of function type that a function of the bound values is. -/
structure Assignments (A : Type) (D : Ty B → Type) (x : Ty B) where
  /-- The value an assignment gives an index. -/
  get : A → ℕ → D x
  /-- An assignment modified to give an index a value. -/
  set : A → ℕ → D x → A
  /-- The value of function type that a function of the bound values is. -/
  lam : {b : Ty B} → (D x → D b) → D (x ⇒ b)

variable {D : B → Type} {g x : Ty B}

/-- The meaning of abstraction: the function of the value the assignment is modified to give
the index. -/
def Abstraction.eval (A : Assignments (g.Dom D) (Ty.Dom D) x) : {a b : Ty B} →
    Abstraction g x a b → a.Dom D → b.Dom D
  | _, _, .index n _, body => fun i ↦ A.lam fun v ↦ body (A.set i n v)

/-- A trace of index `n` reads the value the assignment gives it. -/
def Assignments.trace (A : Assignments (g.Dom D) (Ty.Dom D) x) (n : ℕ) : Σ a : Ty B, a.Dom D :=
  ⟨.comp (.R g) x, fun i ↦ A.get i n⟩

/-- A type is evaluated when no continuation in it is still to be closed. -/
def Ty.Evaluated : Ty B → Bool
  | .comp (.C _) _ => false
  | .comp _ a => a.Evaluated
  | .fn _ b => b.Evaluated
  | _ => true

/-- What the semantics reads off a node of the syntax: a plain branching node, an island, or the
index a moved phrase leaves. -/
inductive Node where
  /-- A plain node. -/
  | branch
  /-- An island for continuations. -/
  | island
  /-- The index `n` of a moved phrase. -/
  | index (n : ℕ)
  deriving DecidableEq, Repr

/-- The effect-driven grammar over a theory's basic modes and type shifts: its binary rules are
the modes. -/
def effectGrammar (Rule : Ty B → Ty B → Ty B → Type) (Shift : Ty B → Ty B → Type) :
    Grammar (Ty B) where
  Unary := Shift
  Binary := Mode Rule

/-- The structure of the effect-driven grammar over a grammar's rules, from a structure for the
grammar and the meanings of the type shifts. -/
@[instance_reducible] def effectGrammar.structure {G : Grammar (Ty B)} {D : B → Type}
    [G.language.Structure (Ty.Dom D)] {Shift : Ty B → Ty B → Type}
    (shift : ∀ {a b : Ty B}, Shift a b → a.Dom D → b.Dom D) :
    (effectGrammar G.Binary Shift).language.Structure (Ty.Dom D) :=
  Grammar.structure shift fun m ↦ m.eval D

/-- The effect-driven interpreter over a grammar: a node admits every mode that combines its
daughters, kept at an island only if its result is evaluated, and abstraction at an index over
what reads assignments. -/
def effectDriven [DecidableEq B] (G : Grammar (Ty B)) [G.LocallyFinite] (g x : Ty B) :
    Interpreter (effectGrammar G.Binary (Abstraction g x)) Node where
  unary
    | .index n, .comp (.R i) b =>
      if h : i = g then [⟨.comp (.R g) (x ⇒ b), h ▸ .index n b⟩] else []
    | _, _ => []
  binary
    | .island, l, r =>
      (Ty.combine (Grammar.LocallyFinite.binaryRules (G := G)) l r).filter (·.1.Evaluated)
    | _, l, r => Ty.combine (Grammar.LocallyFinite.binaryRules (G := G)) l r

/-- The partial-valued interpreter: every constituent is a partial value, and sisters combine by
a rule of the grammar on their values where both are defined, a partial result of the rule
flattened. A function applied to an undefined argument is undefined. -/
def partialValued [DecidableEq B] (G : Grammar (Ty B)) [G.LocallyFinite]
    {Shift : Ty B → Ty B → Type} {N : Type} : Interpreter (effectGrammar G.Binary Shift) N where
  unary _ _ := []
  binary
    | _, .comp .M l, .comp .M r =>
      (Grammar.LocallyFinite.binaryRules (G := G) l r).map fun
        | ⟨.comp .M u, p⟩ => ⟨.comp .M u, .join trivial (.ap trivial (.basic p))⟩
        | ⟨u, p⟩ => ⟨.comp .M u, .ap trivial (.basic p)⟩
    | _, _, _ => []

section PartialValued

variable {G : Grammar (Ty B)} {D : B → Type} [M : G.language.Structure (Ty.Dom D)] {l r u : Ty B}

/-- A rule on two partial values: defined where both are. -/
theorem Mode.eval_ap_basic (p : G.Binary l r u) (x : Part (l.Dom D)) (y : Part (r.Dom D)) :
    (Mode.ap trivial (.basic p) :
      Mode G.Binary (.comp .M l) (.comp .M r) (.comp .M u)).eval D x y =
      x.bind fun a ↦ y.map fun b ↦ M.funMap (.binary p) (a, b) := by
  simp [Mode.eval, Eff.seq, Eff.map, Part.bind_map]

/-- A rule with a partial result, on two partial values: defined where both are and the rule is
at their values. -/
theorem Mode.eval_join_ap_basic (p : G.Binary l r (.comp .M u)) (x : Part (l.Dom D))
    (y : Part (r.Dom D)) :
    (Mode.join trivial (.ap trivial (.basic p)) :
      Mode G.Binary (.comp .M l) (.comp .M r) (.comp .M u)).eval D x y =
      x.bind fun a ↦ y.bind fun b ↦ M.funMap (.binary p) (a, b) := by
  simp [Mode.eval, Eff.join, Eff.seq, Eff.map, Part.bind_assoc, Part.bind_map]

end PartialValued

end Interpreter
