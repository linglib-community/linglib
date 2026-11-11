module

public import Linglib.Semantics.Composition.Mode.Basic
public import Mathlib.Control.Basic

/-!
# The effects as lawful monads

Each effect with a unit and an application is a monad, with its map, its unit, its application
and its join as the operations, and [the monad is lawful](##Interpreter.Eff.lawfulMonad). A
statement about the modes that follows from the functor, applicative or monad laws therefore
holds at every such effect at once: [Structured App is Join over the two maps, the left
daughter's effect first](##Interpreter.Mode.eval_join_mapL_mapR).

## Main definitions

* `Interpreter.Eff.monad`: the monad of an applicative effect.

## References

* [bumford-charlow-2026]
-/

@[expose] public section

/-! ### The monad laws with join after map for bind -/

section

universe u

variable {m : Type u → Type u} [Monad m] [LawfulMonad m] {α β γ : Type u}

private theorem join_map_pure (a : α) (k : α → m β) : (k <$> (pure a : m α)) >>= id = k a := by
  rw [bind_map_left]
  exact pure_bind a _

private theorem join_map_join_map (x : m α) (k : α → m β) (g : β → m γ) :
    (g <$> ((k <$> x) >>= id)) >>= id = ((fun a ↦ (g <$> k a) >>= id) <$> x) >>= id := by
  simp only [bind_map_left, id]
  exact bind_assoc x k g

private theorem join_map_pure_comp (g : α → β) (x : m α) :
    ((fun y ↦ (pure (g y) : m β)) <$> x) >>= id = g <$> x := by
  rw [bind_map_left]
  exact bind_pure_comp g x

private theorem join_map_map (g : m (α → β)) (x : m α) :
    ((fun k ↦ k <$> x) <$> g) >>= id = g <*> x := by
  rw [bind_map_left]
  exact bind_map g x

end

namespace Interpreter.Eff

variable {B : Type} {D : B → Type}

/-- The monad of an effect with a unit and an application: its map, its unit, its application,
and as bind its join after its map. -/
@[reducible] def monad (f : Eff B) (h : f.IsApplicative) : Monad (Obj D f) where
  map := map f
  pure := pure f h
  seq g x := seq f h g (x ())
  bind m k := join f h (map f k m)

/-- The monad of an effect with a unit and an application satisfies the monad laws. -/
theorem lawfulMonad (f : Eff B) (h : f.IsApplicative) :
    @LawfulMonad (Obj D f) (monad f h) := by
  let := monad (D := D) f h
  refine LawfulMonad.mk' (m := Obj D f) (id_map := fun x ↦ map_id f x) (pure_bind := ?_)
    (bind_assoc := ?_) (bind_pure_comp := ?_) (bind_map := ?_)
  · intro α β a k
    show join f h (map f k (pure f h a)) = k a
    cases f with
    | S => simp [join, map, pure]
    | W o => cases h; exact Prod.ext rfl (true_and _)
    | M => simp [join, map, pure]
    | F => clear this; exact join_map_pure (m := WithAlternatives) a k
    | _ => rfl
  · intro α β γ x k g
    show join f h (map f g (join f h (map f k x))) =
      join f h (map f (fun a ↦ join f h (map f g (k a))) x)
    cases f with
    | S => ext c; simp [join, map]
    | W o => cases h; exact Prod.ext rfl (propext and_assoc)
    | M => simp [join, map, Part.bind_assoc]
    | F => clear this; exact join_map_join_map (m := WithAlternatives) x k g
    | _ => rfl
  · intro α β g x
    show join f h (map f (fun y ↦ pure f h (g y)) x) = map f g x
    cases f with
    | S => ext c; simp [join, map, pure, eq_comm]
    | W o => cases h; exact Prod.ext rfl (and_true _)
    | M => exact Part.bind_some_eq_map g x
    | F => clear this; exact join_map_pure_comp (m := WithAlternatives) g x
    | _ => rfl
  · intro α β g x
    show join f h (map f (fun k ↦ map f k x) g) = seq f h g x
    cases f with
    | S => ext c; simp [join, map, seq, Set.mem_seq_iff]
    | W o => cases h; rfl
    | M => simp [join, map, seq]
    | F => clear this; exact join_map_map (m := WithAlternatives) g x
    | _ => rfl

end Interpreter.Eff

namespace Interpreter.Mode

open ManySorted

variable {B : Type} {D : B → Type} {G : Language (Ty B)} [M : G.Structure (Ty.Dom D)]
  {f : Eff B} {l r u : Ty B}

/-- At every effect with a unit and an application, mapping a mode over the right daughter, then
over the left, and joining, is Structured App of the mode: the two daughters' effects are merged
with the left daughter's first. -/
theorem eval_join_mapL_mapR (h : f.IsApplicative) (m : Mode G.Binary l r u)
    (a : (Ty.comp f l).Dom D) (b : (Ty.comp f r).Dom D) :
    (Mode.join h (.mapL (.mapR m))).eval D a b = (Mode.ap h m).eval D a b := by
  let := Eff.monad (D := D) f h
  have := Eff.lawfulMonad (D := D) f h
  show a >>= (fun x ↦ (fun y ↦ m.eval D x y) <$> b) = (fun x y ↦ m.eval D x y) <$> a <*> b
  simp only [seq_eq_bind_map, bind_map_left]

end Interpreter.Mode
