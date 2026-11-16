module

public import Linglib.Core.ModelTheory.ManySorted.Comap
public import Linglib.Semantics.Composition.Rules

/-!
# Continuized grammars

A continuized constituent is a computation at the effect of continuations: a function of its
context, which takes its value to an answer. A grammar of binary rules has a continuized grammar
over the same types. Its rule in order gives the second daughter a context that contains the
first, and gives the first a context whose answer still awaits the second, so the two daughters
are continuized at different answer types. Its symmetric rule is Structured App: each daughter is
in the context of the other, at one answer type. A derivation is continuized at an answer type
by continuizing its rules in order (`ManySorted.Language.Term.continuize`), and where its items
only return their values [it returns its value](##Interpreter.realize_continuize).

## Main definitions

* `Interpreter.Continuized`, `Interpreter.continuized`: the rules of the continuized grammar,
  and the grammar.
* `Interpreter.Ty.arrows`: the answer type that awaits arguments of given types.
* `ManySorted.Language.Term.continuize`: a derivation continuized at an answer that awaits
  arguments of given types.
* `Interpreter.saturations`: the answers a value gives, over the arguments it awaits.

## References

* [barker-2022]
* [barker-2002]
-/

@[expose] public section

open ManySorted ManySorted.Language

namespace Interpreter

variable {B : Type} {L : Language.{0, 0} (Ty B)} {D : B → Type}

/-- The rules of the continuized grammar of a grammar, one in order and one symmetric for each
of its binary rules, at each answer type. -/
inductive Continuized (L : Language.{0, 0} (Ty B)) : Ty B → Ty B → Ty B → Type
  /-- The rule in order: the answer of the first daughter awaits the second. -/
  | seq {a b c : Ty B} (f : L.Binary a b c) (r : Ty B) :
      Continuized L (.comp (.C (b ⇒ r)) a) (.comp (.C r) b) (.comp (.C r) c)
  /-- The symmetric rule: both daughters at one answer type. -/
  | sym {a b c : Ty B} (f : L.Binary a b c) (r : Ty B) :
      Continuized L (.comp (.C r) a) (.comp (.C r) b) (.comp (.C r) c)

/-- The meaning of a continuized rule. In order, the context of the second daughter contains the
first, and the context of the first is a function of the second's value. Symmetrically, the
context of each contains the other. -/
def Continuized.eval (D : B → Type) [M : L.Structure (Ty.Dom D)] :
    {l r u : Ty B} → Continuized L l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .seq f _, β, γ => fun κ ↦ γ (β fun x y ↦ κ (M.funMap f (x, y)))
  | _, _, _, .sym f _, β, γ => fun κ ↦ β fun x ↦ γ fun y ↦ κ (M.funMap f (x, y))

/-- The continuized grammar of a grammar, as a language over the types. -/
@[reducible] def continuized (L : Language.{0, 0} (Ty B)) : Language.{0, 0} (Ty B) :=
  .mk₂ (fun _ _ ↦ PEmpty) (Continuized L)

instance [L.Structure (Ty.Dom D)] : (continuized L).Structure (Ty.Dom D) :=
  .mk₂ nofun (Continuized.eval D)

/-- The answer type that awaits arguments of the types `l` before an answer of type `p`. -/
abbrev Ty.arrows : List (Ty B) → Ty B → Ty B
  | [], p => p
  | a :: l, p => a ⇒ Ty.arrows l p

/-- The answers of type `p` that a value gives, over the arguments it awaits. -/
def saturations (D : B → Type) (p : Ty B) :
    (l : List (Ty B)) → (Ty.arrows l p).Dom D → Set (p.Dom D)
  | [], f => {f}
  | _ :: l, f => ⋃ x, saturations D p l (f x)

/-- A lexical item of a grammar as an item of its continuized grammar, at an answer that awaits
arguments of the types `l`. -/
inductive Continuized.Item (p : Ty B) (W : Ty B → Type) : Ty B → Type
  /-- The item `x` at the answer type `Ty.arrows l p`. -/
  | at {a : Ty B} (x : W a) (l : List (Ty B)) : Item p W (.comp (.C (Ty.arrows l p)) a)

end Interpreter

namespace ManySorted

open Interpreter

variable {B : Type} {L : Language.{0, 0} (Ty B)} {D : B → Type} {W : Ty B → Type} (p : Ty B)

/-- The types of the arguments of a shape, in order. -/
def Signature.types : Signature (Ty B) → List (Ty B)
  | .nil => []
  | .of a => [a]
  | .prod σ τ => σ.types ++ τ.types

/-- The shape of continuized arguments, at an answer that awaits arguments of the types `l`:
each argument also awaits the arguments after it. -/
def Signature.continuize : Signature (Ty B) → List (Ty B) → Signature (Ty B)
  | .nil, _ => .nil
  | .of a, l => .of (.comp (.C (Ty.arrows l p)) a)
  | .prod σ τ, l => .prod (σ.continuize (τ.types ++ l)) (τ.continuize l)

/-- A derivation continuized at an answer that awaits arguments of the types `l`: each rule is
continuized in order, and each item is taken at the answer its position gives it. -/
def Language.Term.continuize [L.IsBinary] :
    {σ : Signature (Ty B)} → L.Term W σ → (l : List (Ty B)) →
      (continuized L).Term (Continuized.Item p W) (σ.continuize p l)
  | _, .var x, l => .var (.at x l)
  | _, .prod a b, l => .prod (a.continuize _) (b.continuize l)
  | _, .nil, _ => .nil
  | _, .func (σ := σ) (t := u) f d, l =>
    match σ, f, d with
    | .prod (.of _) (.of _), f, d => .func (Continuized.seq f (Ty.arrows l p)) (d.continuize l)
    | .nil, f, _ => (IsBinary.isEmpty_of_ne .nil u fun _ _ h ↦ nomatch h).elim f
    | .of a, f, _ => (IsBinary.isEmpty_of_ne (.of a) u fun _ _ h ↦ nomatch h).elim f
    | .prod .nil τ, f, _ => (IsBinary.isEmpty_of_ne (.prod .nil τ) u fun _ _ h ↦ nomatch h).elim f
    | .prod (.prod σ₁ σ₂) τ, f, _ =>
      (IsBinary.isEmpty_of_ne (.prod (.prod σ₁ σ₂) τ) u fun _ _ h ↦ nomatch h).elim f
    | .prod (.of a) .nil, f, _ =>
      (IsBinary.isEmpty_of_ne (.prod (.of a) .nil) u fun _ _ h ↦ nomatch h).elim f
    | .prod (.of a) (.prod τ₁ τ₂), f, _ =>
      (IsBinary.isEmpty_of_ne (.prod (.of a) (.prod τ₁ τ₂)) u fun _ _ h ↦ nomatch h).elim f

end ManySorted

namespace Interpreter

variable {B : Type} {L : Language.{0, 0} (Ty B)} {D : B → Type} {W : Ty B → Type} {p : Ty B}
  [L.IsBinary] [M : L.Structure (Ty.Dom D)]

/-- Continuized arguments that each only return the argument of a shape. -/
private def Returns : (σ : Signature (Ty B)) → (l : List (Ty B)) → σ.Interpret (Ty.Dom D) →
    (σ.continuize p l).Interpret (Ty.Dom D) → Prop
  | .nil, _, _, _ => True
  | .of _, _, x, m => m = fun κ ↦ κ x
  | .prod σ τ, l, x, m => Returns σ (τ.types ++ l) x.1 m.1 ∧ Returns τ l x.2 m.2

private theorem returns_realize_continuize (ρ : ∀ {a : Ty B}, W a → a.Dom D)
    (den : ∀ {a : Ty B}, Continuized.Item p W a → a.Dom D)
    (hden : ∀ {a : Ty B} (x : W a) (l : List (Ty B)), den (.at x l) = fun κ ↦ κ (ρ x)) :
    ∀ {σ : Signature (Ty B)} (t : L.Term W σ) (l : List (Ty B)),
      Returns σ l (t.realize M ρ) ((t.continuize p l).realize inferInstance den)
  | _, .var x, l => hden x l
  | _, .prod a b, l =>
    ⟨returns_realize_continuize ρ den hden a _, returns_realize_continuize ρ den hden b l⟩
  | _, .nil, _ => trivial
  | _, .func (σ := σ) (t := u) f d, l =>
    match σ, f, d with
    | .prod (.of _) (.of _), f, d => by
      obtain ⟨h₁, h₂⟩ := returns_realize_continuize ρ den hden d l
      exact congrArg₂ (Continuized.eval D (.seq f (Ty.arrows l p))) h₁ h₂
    | .nil, f, _ => (IsBinary.isEmpty_of_ne .nil u fun _ _ h ↦ nomatch h).elim f
    | .of a, f, _ => (IsBinary.isEmpty_of_ne (.of a) u fun _ _ h ↦ nomatch h).elim f
    | .prod .nil τ, f, _ => (IsBinary.isEmpty_of_ne (.prod .nil τ) u fun _ _ h ↦ nomatch h).elim f
    | .prod (.prod σ₁ σ₂) τ, f, _ =>
      (IsBinary.isEmpty_of_ne (.prod (.prod σ₁ σ₂) τ) u fun _ _ h ↦ nomatch h).elim f
    | .prod (.of a) .nil, f, _ =>
      (IsBinary.isEmpty_of_ne (.prod (.of a) .nil) u fun _ _ h ↦ nomatch h).elim f
    | .prod (.of a) (.prod τ₁ τ₂), f, _ =>
      (IsBinary.isEmpty_of_ne (.prod (.of a) (.prod τ₁ τ₂)) u fun _ _ h ↦ nomatch h).elim f

/-- A continuized derivation whose items only return their values returns the value of the
derivation: continuizing changes no meaning that does not consult its context. -/
theorem realize_continuize (ρ : ∀ {a : Ty B}, W a → a.Dom D)
    (den : ∀ {a : Ty B}, Continuized.Item p W a → a.Dom D)
    (hden : ∀ {a : Ty B} (x : W a) (l : List (Ty B)), den (.at x l) = fun κ ↦ κ (ρ x))
    {a : Ty B} (d : L.Deriv W a) (l : List (Ty B)) :
    (d.continuize p l).realize inferInstance den = fun κ ↦ κ (d.realize M ρ) :=
  returns_realize_continuize ρ den hden d l

end Interpreter
