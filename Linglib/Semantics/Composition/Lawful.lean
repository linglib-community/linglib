module

public import Linglib.Semantics.Composition.Mode.Basic
public import Mathlib.Control.Basic
public import Mathlib.Basic.Nontrivial.Defs

/-!
# The effects as lawful monads

Each effect with a unit and an application is a monad, with its map, its unit, its application
and its join as the operations, and [the monad is lawful](##Interpreter.Eff.lawfulMonad). A
statement about the modes that follows from the functor, applicative or monad laws therefore
holds at every such effect at once: [Structured App is Join over the two maps, the left
daughter's effect first](##Interpreter.Mode.join_mapL_mapR).

Reading, indeterminacy, partiality, alternatives and the storing of truth values are
[commutative](##Interpreter.Eff.commApplicative): at these [the right daughter's effect may as
well come first](##Interpreter.Mode.join_mapR_mapL), and [the daughters may change
places](##Interpreter.Mode.eval_ap_comm). Quantifying over continuations
[is not](##Interpreter.Eff.not_commApplicative_C), and there [the order of the maps is a
difference of scope](##Interpreter.Mode.not_join_mapR_mapL_equiv_ap).

## Main definitions

* `Interpreter.Eff.monad`: the monad of an applicative effect.
* `Interpreter.Eff.IsCommutative`: the effects whose application is commutative.

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

/-- The effects whose application does not depend on the order of its two computations: those
with a unit and an application, but for quantifying over continuations. -/
def IsCommutative : Eff B → Prop
  | .C _ => False
  | f => f.IsApplicative

theorem IsCommutative.isApplicative : ∀ {f : Eff B}, f.IsCommutative → f.IsApplicative
  | .S, _ | .R _, _ | .M, _ | .F, _ => trivial
  | .W _, h => h

instance [DecidableEq B] : DecidablePred (IsCommutative (B := B))
  | .C _ => isFalse id
  | .W o => inferInstanceAs (Decidable (o = .t))
  | .S | .R _ | .M | .F => isTrue trivial

private theorem seq_map_prodMk_comm {f : Eff B} (hc : f.IsCommutative) {α β : Type}
    (a : Obj D f α) (b : Obj D f β) :
    seq f hc.isApplicative (map f Prod.mk a) b =
      seq f hc.isApplicative (map f (fun b a ↦ (a, b)) b) a := by
  cases f with
  | S => exact CommApplicative.commutative_prod (m := Set) a b
  | R i => rfl
  | W o => cases hc; exact Prod.ext rfl (propext and_comm)
  | C r => exact hc.elim
  | M =>
    ext p
    simp only [seq, map, Part.mem_bind_iff, Part.mem_map_iff, exists_exists_and_eq_and]
    exact ⟨fun ⟨x, hx, y, hy, h⟩ ↦ ⟨y, hy, x, hx, h⟩, fun ⟨y, hy, x, hx, h⟩ ↦ ⟨x, hx, y, hy, h⟩⟩
  | F => exact CommApplicative.commutative_prod (m := WithAlternatives) a b

/-- The application of a commutative effect is commutative: its two computations can be run in
either order. -/
theorem commApplicative {f : Eff B} (hc : f.IsCommutative) :
    @CommApplicative (Obj D f) (monad f hc.isApplicative).toApplicative :=
  let := monad (D := D) f hc.isApplicative
  have := lawfulMonad (D := D) f hc.isApplicative
  { commutative_prod := seq_map_prodMk_comm hc }

/-- Quantifying over continuations is not commutative where the result type has two values: of
two quantifiers that ignore their scopes, the application returns what the first does. -/
theorem not_commApplicative_C (r : Ty B) [Nontrivial (r.Dom D)] :
    ¬ @CommApplicative (Obj D (.C r)) (monad (.C r) trivial).toApplicative := fun h ↦ by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (r.Dom D)
  exact hxy (congrFun (@CommApplicative.commutative_prod _ _ h Unit Unit (fun _ ↦ x) fun _ ↦ y)
    fun _ ↦ x)

end Interpreter.Eff

namespace Interpreter.Mode

open ManySorted

variable {B : Type} {G : Language (Ty B)} {f : Eff B} {l r u : Ty B}

/-- At every effect with a unit and an application, mapping a mode over the right daughter, then
over the left, and joining, is Structured App of the mode: the two daughters' effects are merged
with the left daughter's first. -/
theorem join_mapL_mapR (h : f.IsApplicative) (m : Mode G.Binary l r u) :
    Mode.join h (.mapL (.mapR m)) ≈ .ap h m := fun D _ ↦ funext₂ fun a b ↦ by
  let := Eff.monad (D := D) f h
  have := Eff.lawfulMonad (D := D) f h
  show a >>= (fun x ↦ (fun y ↦ m.eval D x y) <$> b) = (fun x y ↦ m.eval D x y) <$> a <*> b
  simp only [seq_eq_bind_map, bind_map_left]

/-- At a commutative effect, mapping a mode over the left daughter, then over the right, and
joining, is Structured App of the mode too: the effects are merged with the right daughter's
first, and the order makes no difference. -/
theorem join_mapR_mapL (hc : f.IsCommutative) (m : Mode G.Binary l r u) :
    Mode.join hc.isApplicative (.mapR (.mapL m)) ≈ .ap hc.isApplicative m :=
  fun D _ ↦ funext₂ fun a b ↦ by
    let := Eff.monad (D := D) f hc.isApplicative
    have := Eff.lawfulMonad (D := D) f hc.isApplicative
    have := Eff.commApplicative (D := D) hc
    show b >>= (fun y ↦ (fun x ↦ m.eval D x y) <$> a) = (fun x y ↦ m.eval D x y) <$> a <*> b
    rw [CommApplicative.commutative_map]
    simp only [seq_eq_bind_map, bind_map_left]
    rfl

variable {D : B → Type} [M : G.Structure (Ty.Dom D)]

/-- At a commutative effect it does not matter which daughter is on the left: Structured App of
a mode is Structured App of its mirror image at the daughters in the other order. -/
theorem eval_ap_comm (hc : f.IsCommutative) {m : Mode G.Binary l r u} {m' : Mode G.Binary r l u}
    (hm : m.eval D = Function.swap (m'.eval D)) :
    (Mode.ap hc.isApplicative m).eval D = Function.swap ((Mode.ap hc.isApplicative m').eval D) :=
  funext₂ fun a b ↦ by
    let := Eff.monad (D := D) f hc.isApplicative
    have := Eff.commApplicative (D := D) hc
    show (fun x y ↦ m.eval D x y) <$> a <*> b = (fun y x ↦ m'.eval D y x) <$> b <*> a
    rw [CommApplicative.commutative_map]
    exact congrArg (fun k ↦ k <$> b <*> a) (funext₂ fun y x ↦ congrFun₂ hm x y)

/-- At quantification over continuations the order of the two effects matters: where the result
type has two values, merging the effects with the right daughter's first is not Structured App,
whatever the mode. -/
theorem not_join_mapR_mapL_equiv_ap {o : Ty B} [Nontrivial (o.Dom D)]
    (m : Mode G.Binary l r u) :
    ¬ Mode.join (f := .C o) trivial (.mapR (.mapL m)) ≈ .ap trivial m := fun h ↦ by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (o.Dom D)
  exact hxy (congrFun (congrFun₂ (h D) (fun _ ↦ x) fun _ ↦ y) fun _ ↦ x).symm

end Interpreter.Mode
