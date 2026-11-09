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

* `Interpreter.BasicModes`: a theory's basic modes of combination and their selection by type.
* `Interpreter.Standard`: forward and backward application and predicate modification.
* `Interpreter.Mode`: the basic modes closed under the meta-modes.
* `Interpreter.Mode.eval`: the meaning of a mode, by the operations of the effects.
* `Interpreter.Ty.combine`: every mode by which two types combine, the book's `combine`.
* `Interpreter.Abstraction`, `Interpreter.Assignments`: abstraction over an index, and traces.
* `Interpreter.Node`, `Interpreter.effectDriven`: what the semantics reads off a node, and the
  rules each kind of node admits.
* `Interpreter.envSensitive`: Heim and Kratzer's grammar as a selection of those rules.
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

/-- A theory's basic modes of combination: its rules, and those that apply to two types. -/
structure BasicModes (B : Type) where
  /-- The basic rules, typed by the daughters and the mother. -/
  Rule : Ty B → Ty B → Ty B → Type
  /-- The basic rules that apply to a left and a right daughter. -/
  find : (l r : Ty B) → List (Σ u, Rule l r u)

/-- Forward application, backward application and predicate modification. -/
inductive Standard : Ty B → Ty B → Ty B → Type
  /-- Forward application. -/
  | fa {a b : Ty B} : Standard (a ⇒ b) a b
  /-- Backward application. -/
  | ba {a b : Ty B} : Standard a (a ⇒ b) b
  /-- Predicate modification. -/
  | pm {a : Ty B} : Standard (a ⇒ .t) (a ⇒ .t) (a ⇒ .t)

namespace Standard

/-- The standard mode two types select: the first of forward application, backward application
and predicate modification that applies. -/
def find [DecidableEq B] (l r : Ty B) : List (Σ u, Standard l r u) :=
  match l, r with
  | .fn a b, r =>
    if h : a = r then [⟨b, h ▸ fa⟩]
    else match r with
      | .fn a' b' =>
        if h' : a' = .fn a b then [⟨b', h' ▸ ba⟩]
        else if h'' : b = .t ∧ b' = .t ∧ a = a' then
          [⟨a ⇒ .t, by obtain ⟨rfl, rfl, rfl⟩ := h''; exact pm⟩]
        else []
      | _ => []
  | l, .fn a b => if h : a = l then [⟨b, h ▸ ba⟩] else []
  | _, _ => []

/-- The meaning of a standard mode. -/
def eval (D : B → Type) : {l r u : Ty B} → Standard l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, fa, f, x => f x
  | _, _, _, ba, x, f => f x
  | _, _, _, pm, p, q => fun x ↦ p x ∧ q x

end Standard

/-- The standard basic modes. -/
def standard (B : Type) [DecidableEq B] : BasicModes B := ⟨Standard, Standard.find⟩

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

/-- The meaning of a mode, from the meanings of the basic modes: each meta-mode is the operation
of its effect. -/
def eval (D : B → Type) (basic : ∀ {l r u : Ty B}, Rule l r u → l.Dom D → r.Dom D → u.Dom D) :
    {l r u : Ty B} → Mode Rule l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .basic b, x, y => basic b x y
  | _, _, _, .mapR (f := f) m, a, b => Eff.map f (fun y ↦ m.eval D basic a y) b
  | _, _, _, .mapL (f := f) m, a, b => Eff.map f (fun x ↦ m.eval D basic x b) a
  | _, _, _, .ap (f := f) h m, a, b =>
    Eff.seq f h (Eff.map f (fun x y ↦ m.eval D basic x y) a) b
  | _, _, _, .unitR (f := f) h m, a, b => m.eval D basic (fun x ↦ a (Eff.pure f h x)) b
  | _, _, _, .unitL (f := f) h m, a, b => m.eval D basic a fun y ↦ b (Eff.pure f h y)
  | _, _, _, .counit (i := i) m, a, b =>
    Eff.counit (Eff.map (.W i) (fun x ↦ Eff.map (.R i) (fun y ↦ m.eval D basic x y) b) a)
  | _, _, _, .ejectR m, a, b => m.eval D basic a (Eff.eject b)
  | _, _, _, .ejectL m, a, b => m.eval D basic (Eff.eject a) b
  | _, _, _, .join (f := f) h m, a, b => Eff.join f h (m.eval D basic a b)
  | _, _, _, .lower m, a, b => Eff.lower (m.eval D basic a b)

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

variable [DecidableEq B] (basics : BasicModes B)

/-- The Join of a mode whose result has two layers of one monadic effect. -/
def Mode.join? {l r : Ty B} : (Σ u, Mode basics.Rule l r u) → List (Σ u, Mode basics.Rule l r u)
  | ⟨.comp f (.comp g a), m⟩ =>
    if h : g = f then
      if ha : f.IsApplicative then [⟨.comp f a, .join ha (h ▸ m)⟩] else []
    else []
  | _ => []

/-- The Lower of a mode whose result is a continuation at its own result type. -/
def Mode.lower? {l r : Ty B} : (Σ u, Mode basics.Rule l r u) → List (Σ u, Mode basics.Rule l r u)
  | ⟨.comp (.C o) a, m⟩ => if h : o = a then [⟨a, .lower (h ▸ m)⟩] else []
  | _ => []

/-- `Ty.combine` to a bound on the depth of its recursion. -/
def Ty.combineAux : ℕ → (l r : Ty B) → List (Σ u, Mode basics.Rule l r u)
  | 0, _, _ => []
  | n + 1, l, r =>
    (((basics.find l r).map fun p ↦ (⟨p.1, .basic p.2⟩ : Σ u, Mode basics.Rule l r u)) ++
      (match r with
        | .comp f y => (Ty.combineAux n l y).map fun p ↦ ⟨.comp f p.1, .mapR p.2⟩
        | _ => []) ++
      (match l with
        | .comp f x => (Ty.combineAux n x r).map fun p ↦ ⟨.comp f p.1, .mapL p.2⟩
        | _ => []) ++
      (match l, r with
        | .comp f x, .comp g y =>
          if h : g = f then
            if ha : f.IsApplicative then
              (Ty.combineAux n x y).map fun p ↦ ⟨.comp f p.1, by subst h; exact .ap ha p.2⟩
            else []
          else []
        | _, _ => []) ++
      (match l with
        | .fn (.comp f x) x' =>
          if ha : f.IsApplicative then
            (Ty.combineAux n (x ⇒ x') r).map fun p ↦ ⟨p.1, .unitR ha p.2⟩
          else []
        | _ => []) ++
      (match r with
        | .fn (.comp f y) y' =>
          if ha : f.IsApplicative then
            (Ty.combineAux n l (y ⇒ y')).map fun p ↦ ⟨p.1, .unitL ha p.2⟩
          else []
        | _ => []) ++
      (match l, r with
        | .comp (.W i) x, .comp (.R j) y =>
          if h : j = i then (Ty.combineAux n x y).map fun p ↦ ⟨p.1, h ▸ .counit p.2⟩ else []
        | _, _ => []) ++
      (match r with
        | .fn x (.comp (.R i) y) =>
          (Ty.combineAux n l (.comp (.R i) (x ⇒ y))).map fun p ↦ ⟨p.1, .ejectR p.2⟩
        | _ => []) ++
      (match l with
        | .fn x (.comp (.R i) y) =>
          (Ty.combineAux n (.comp (.R i) (x ⇒ y)) r).map fun p ↦ ⟨p.1, .ejectL p.2⟩
        | _ => [])).flatMap fun p ↦ p :: (Mode.join? basics p ++ Mode.lower? basics p)

/-- Every mode by which a left daughter of type `l` and a right daughter of type `r` combine. -/
def Ty.combine (l r : Ty B) : List (Σ u, Mode basics.Rule l r u) :=
  Ty.combineAux basics (3 * (l.size + r.size) + 3) l r

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

/-- How assignments of type `g` hold values of type `x`. -/
structure Assignments (D : B → Type) (g x : Ty B) where
  /-- The value an assignment gives an index. -/
  get : g.Dom D → ℕ → x.Dom D
  /-- An assignment modified at an index. -/
  set : g.Dom D → ℕ → x.Dom D → g.Dom D

variable {D : B → Type} {g x : Ty B}

/-- The meaning of abstraction: the body at the assignment modified at the index. -/
def Abstraction.eval (A : Assignments D g x) : {a b : Ty B} → Abstraction g x a b →
    a.Dom D → b.Dom D
  | _, _, .index n _, body => fun i v ↦ body (A.set i n v)

/-- A trace of index `n` reads the value the assignment gives it. -/
def Assignments.trace (A : Assignments D g x) (n : ℕ) : Σ a : Ty B, a.Dom D :=
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

/-- The structure of the effect-driven grammar, from the meanings of the basic modes and of the
type shifts. -/
def effectGrammar.structure (D : B → Type) {Rule : Ty B → Ty B → Ty B → Type}
    {Shift : Ty B → Ty B → Type}
    (basic : ∀ {l r u : Ty B}, Rule l r u → l.Dom D → r.Dom D → u.Dom D)
    (shift : ∀ {a b : Ty B}, Shift a b → a.Dom D → b.Dom D) :
    (effectGrammar Rule Shift).language.Structure (Ty.Dom D) :=
  Grammar.structure shift fun m ↦ m.eval D basic

/-- The effect-driven interpreter: a node admits every mode that combines its daughters, kept
at an island only if its result is evaluated, and abstraction at an index over what reads
assignments. -/
def effectDriven [DecidableEq B] (basics : BasicModes B) (g x : Ty B) :
    Interpreter (effectGrammar basics.Rule (Abstraction g x)) Node where
  unary
    | .index n, .comp (.R i) b =>
      if h : i = g then [⟨.comp (.R g) (x ⇒ b), h ▸ .index n b⟩] else []
    | _, _ => []
  binary
    | .island, l, r => (Ty.combine basics l r).filter (·.1.Evaluated)
    | _, l, r => Ty.combine basics l r

/-- The environment-sensitive interpreter of Heim and Kratzer, the book's Figure 5: every
constituent reads an assignment, sisters combine by a basic mode on their results at one
assignment, and an index abstracts. At most one rule applies to a node. -/
def envSensitive [DecidableEq B] (basics : BasicModes B) (g x : Ty B) :
    Interpreter (effectGrammar basics.Rule (Abstraction g x)) Node where
  unary := (effectDriven basics g x).unary
  binary
    | _, .comp (.R i) l, .comp (.R j) r =>
      if h : i = g ∧ j = g then
        (basics.find l r).map fun p ↦ ⟨.comp (.R g) p.1, by
          obtain ⟨rfl, rfl⟩ := h; exact .ap trivial (.basic p.2)⟩
      else []
    | _, _, _ => []

/-- A word that reads no assignment, as a constant reader. -/
def Assignments.const (_ : Assignments D g x) {a : Ty B} (m : a.Dom D) : Σ a : Ty B, a.Dom D :=
  ⟨.comp (.R g) a, fun _ ↦ m⟩

end Interpreter
