module

public import Linglib.Core.ModelTheory.ManySorted.Traverse
public import Linglib.Semantics.Composition.Lawful
public import Linglib.Semantics.Composition.Mode.Pointwise

/-!
# Pointwise composition is interpretation of substitution

The pointwise grammar of an applicative effect is [the lifting of the effect-driven grammar along
the effect](##Interpreter.effectGrammar.pointwise_eq_applicative). So where each item is the
computation of the value of some item, the value of a derivation is [the computation of the values
of the derivations it traverses](##Interpreter.effectGrammar.realize_pointwise), each occurrence
of an item on its own.

At alternatives the traversal of a derivation by the substitutes of its items is Katzir's
recursive definition of the focus syntactic value: an unfocused terminal has itself, a focused
terminal its possible substitutions, and a nonterminal the combinations of its daughters' values.
Rooth's focus semantic value, composed pointwise from the values of the substitutes, is then [the
set of values of the focus syntactic
value](##Interpreter.effectGrammar.alternatives_realize_pointwise): the two definitions of the
formal alternatives agree on what a derivation's alternatives denote.

## Implementation notes

A substitute of an item is an item of its type. Katzir's possible substitutions for a terminal
also include the empty structure, by which the definition simulates deletion; a deleted terminal
has no value of the terminal's type, so those alternatives are outside the statement.

## References

* [bumford-charlow-2026]
* [rooth-1985]
* [katzir-2008]
* [fox-katzir-2011]
-/

@[expose] public section

namespace Interpreter

open ManySorted Language

variable {B : Type} {G : Language.{0, 0} (Ty B)} {D : B → Type} [M : G.Structure (Ty.Dom D)]
  {f : Eff B} [h : f.IsApplicative]

/-- The computation of the arguments of a shape is that of the applicative functor of the
effect. -/
theorem Eff.sequence_eq (σ : Signature (Ty B))
    (x : σ.Interpret fun a ↦ (Ty.comp f a).Dom D) :
    Eff.sequence f σ x = Signature.Interpret.sequence (A := Eff.Obj D f) σ x := by
  induction σ with
  | nil => rfl
  | of _ => rfl
  | prod σ τ ihσ ihτ =>
    change Eff.seq f h (Eff.map f Prod.mk (Eff.sequence f σ x.1)) (Eff.sequence f τ x.2) = _
    rw [ihσ, ihτ]
    rfl

/-- The structure of the effect-driven grammar on the computations of an applicative effect is
the lifting of its structure along the effect. -/
theorem effectGrammar.pointwise_eq_applicative :
    effectGrammar.pointwise (G := G) (D := D) f =
      (effectGrammar.structure (G := G) (D := D)).applicative (Eff.Obj D f) := by
  refine congrArg Language.Structure.mk ?_
  funext σ _ g x
  match σ, g with
  | .prod (.of _) (.of _), m =>
    change m.eval D <$> x.1 <*> x.2 = (fun p ↦ m.eval D p.1 p.2) <$> (Prod.mk <$> x.1 <*> x.2)
    simp only [map_seq, Functor.map_map]
    rfl
  | .nil, g | .of _, g | .prod .nil _, g | .prod (.prod _ _) _, g | .prod (.of _) .nil, g
  | .prod (.of _) (.prod _ _), g =>
    exact congrArg (Eff.map f (M.funMap g)) (Eff.sequence_eq _ x)

variable {W W' : Ty B → Type}

/-- In the pointwise grammar of an applicative effect, where each item is the computation of the
value of some item, the value of a derivation is the computation of the values of the derivations
it traverses. -/
theorem effectGrammar.realize_pointwise (ρ : ∀ {a : Ty B}, W' a → a.Dom D)
    (g : ∀ {a : Ty B}, W a → Eff.Obj D f (W' a)) {a : Ty B}
    (d : (effectGrammar G).Term W (.of a)) :
    d.realize (effectGrammar.pointwise f) (fun x ↦ ρ <$> g x) =
      (fun d' : (effectGrammar G).Term W' (.of a) ↦ d'.realize effectGrammar.structure ρ) <$>
        d.traverse g := by
  rw [effectGrammar.pointwise_eq_applicative]
  exact Term.realize_applicative _ ρ g d

omit M in
/-- Traversal at alternatives is the same by the effect's applicative and by that of
`WithAlternatives`. -/
private theorem traverse_F (g : ∀ {a : Ty B}, W a → WithAlternatives (W' a))
    {σ : Signature (Ty B)} (d : (effectGrammar G).Term W σ) :
    @Term.traverse _ _ _ _ (Eff.Obj D (.F : Eff B)) (Eff.monad (.F : Eff B)).toApplicative g σ d =
      d.traverse (A := WithAlternatives) g := by
  induction d with
  | var x => rfl
  | func f r ih => exact congrArg (Functor.map (f := WithAlternatives) (Term.func f)) ih
  | prod a b iha ihb =>
    exact congrArg₂ (fun x y ↦ (Term.prod <$> x <*> y : WithAlternatives _)) iha ihb
  | nil => rfl

/-- Rooth's composition is interpretation of substitution: where each item evokes the values of
its substitutes, the alternatives a derivation composes are the values of the derivations that
substituting at its leaves gives. -/
theorem effectGrammar.alternatives_realize_pointwise (ρ : ∀ {a : Ty B}, W' a → a.Dom D)
    (g : ∀ {a : Ty B}, W a → WithAlternatives (W' a)) {a : Ty B}
    (d : (effectGrammar G).Term W (.of a)) :
    WithAlternatives.alternatives
        (d.realize (effectGrammar.pointwise (.F : Eff B))
          fun x ↦ (ρ <$> g x : WithAlternatives _)) =
      (fun d' : (effectGrammar G).Term W' (.of a) ↦ d'.realize effectGrammar.structure ρ) ''
        (d.traverse (A := WithAlternatives) g).alternatives := by
  refine (congrArg WithAlternatives.alternatives
    (effectGrammar.realize_pointwise (f := (.F : Eff B)) ρ g d)).trans ?_
  rw [traverse_F (D := D)]
  exact Set.ext fun _ ↦ WithAlternatives.mem_alternatives_map

end Interpreter
