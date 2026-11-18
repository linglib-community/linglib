module

public import Linglib.Semantics.Composition.Effect
public import Linglib.Semantics.Composition.Basic

/-!
# The effect-driven grammar

Bumford and Charlow's grammar takes whatever basic modes of combination a theory has and closes
them under meta-modes, each lifting a mode through an effect by the structure the effect has: Map
Left and Map Right by its map, Structured App and the Unit modes where it is applicative, Join
where it is a monad, Co-unit and Eject for the adjunction of storing and reading, and Lower for a
continuation at its own result type.

## Main definitions

* `Interpreter.Mode`: the basic modes closed under the meta-modes.
* `Interpreter.Mode.eval`: the meaning of a mode, by the operations of the effects.
* `Interpreter.Ty.Evaluated`: the types with no continuation still to be closed.
* `Interpreter.effectGrammar`: the grammar whose binary rules are the modes over a grammar's
  rules, with its structure.

## References

* [bumford-charlow-2026]
-/

@[expose] public section

open ManySorted

namespace Interpreter

variable {B : Type}

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
def eval {G : Language (Ty B)} (D : B → Type) [M : G.Structure (Ty.Dom D)] :
    {l r u : Ty B} → Mode G.Binary l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .basic b, x, y => M.funMap b (x, y)
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

end Mode

/-- A type is evaluated when no continuation in it is still to be closed. -/
def Ty.Evaluated : Ty B → Prop
  | .comp (.C _) _ => False
  | .comp .S a | .comp (.R _) a | .comp (.W _) a | .comp .M a => a.Evaluated
  | .fn _ b => b.Evaluated
  | .t | .base _ => True

instance Ty.decidableEvaluated : (a : Ty B) → Decidable a.Evaluated
  | .comp (.C _) _ => isFalse id
  | .comp .S a | .comp (.R _) a | .comp (.W _) a | .comp .M a => decidableEvaluated a
  | .fn _ b => decidableEvaluated b
  | .t | .base _ => isTrue trivial

/-- The effect-driven grammar over a grammar: its type shifts, and the modes over its rules. -/
def effectGrammar (G : Language (Ty B)) : Language (Ty B) := .mk₂ G.Unary (Mode G.Binary)

/-- The structure of the effect-driven grammar over a grammar, from a structure for the
grammar: a type shift means what it does there, and a mode what the effects make of the rules. -/
instance effectGrammar.structure {G : Language (Ty B)} {D : B → Type}
    [M : G.Structure (Ty.Dom D)] : (effectGrammar G).Structure (Ty.Dom D) :=
  .mk₂ (fun s x ↦ M.funMap s x) fun m ↦ m.eval D

end Interpreter
