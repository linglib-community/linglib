module

public import Linglib.Semantics.Composition.Mode.Basic
public import Mathlib.Control.Basic
public import Mathlib.Basic.Nontrivial.Defs

/-!
# The effects as lawful monads

An applicative effect is [a lawful monad](##Interpreter.Eff.lawfulMonad), so a statement that
follows from the monad laws holds at every such effect: [`.join (.mapL (.mapR m))` is equivalent
to `.ap m`](##Interpreter.Mode.join_mapL_mapR_equiv_ap). Every applicative effect but
quantification over continuations is [commutative](##Interpreter.Eff.commApplicative), and at
these [so is `.join (.mapR (.mapL m))`](##Interpreter.Mode.join_mapR_mapL_equiv_ap) and [the
daughters may change places](##Interpreter.Mode.eval_ap_comm). At continuations [it is
not](##Interpreter.Mode.not_join_mapR_mapL_equiv_ap): the order of the two maps is a difference
of scope.

## Main definitions

* `Interpreter.Eff.lawfulMonad`: the monad of an applicative effect is lawful.
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

/-- The monad of an effect with a unit and an application satisfies the monad laws. -/
instance lawfulMonad (f : Eff B) [h : f.IsApplicative] : LawfulMonad (Obj D f) := by
  refine LawfulMonad.mk' (m := Obj D f) (id_map := fun x ↦ map_id f x) (pure_bind := ?_)
    (bind_assoc := ?_) (bind_pure_comp := ?_) (bind_map := ?_)
  · intro α β a k
    show join f h (map f k (pure f h a)) = k a
    cases f with
    | S => simp [join, map, pure]
    | W o => obtain ⟨rfl⟩ := h; exact Prod.ext rfl (true_and _)
    | M => simp [join, map, pure]
    | F => exact join_map_pure (m := WithAlternatives) a k
    | _ => rfl
  · intro α β γ x k g
    show join f h (map f g (join f h (map f k x))) =
      join f h (map f (fun a ↦ join f h (map f g (k a))) x)
    cases f with
    | S => ext c; simp [join, map]
    | W o => obtain ⟨rfl⟩ := h; exact Prod.ext rfl (propext and_assoc)
    | M => simp [join, map, Part.bind_assoc]
    | F => exact join_map_join_map (m := WithAlternatives) x k g
    | _ => rfl
  · intro α β g x
    show join f h (map f (fun y ↦ pure f h (g y)) x) = map f g x
    cases f with
    | S => ext c; simp [join, map, pure, eq_comm]
    | W o => obtain ⟨rfl⟩ := h; exact Prod.ext rfl (and_true _)
    | M => exact Part.bind_some_eq_map g x
    | F => exact join_map_pure_comp (m := WithAlternatives) g x
    | _ => rfl
  · intro α β g x
    show join f h (map f (fun k ↦ map f k x) g) = seq f h g x
    cases f with
    | S => ext c; simp [join, map, seq, Set.mem_seq_iff]
    | W o => obtain ⟨rfl⟩ := h; rfl
    | M => simp [join, map, seq]
    | F => exact join_map_map (m := WithAlternatives) g x
    | _ => rfl

/-- An effect is commutative if it is applicative and is not quantification over continuations
(`.C r`). The `seq` of a commutative effect does not depend on the order of its two computations
(`Eff.commApplicative`). -/
class IsCommutative (f : Eff B) : Prop extends IsApplicative f where
  /-- The effect is not quantification over continuations. -/
  ne_C : ∀ r : Ty B, f ≠ .C r

instance : IsCommutative (.S : Eff B) := ⟨nofun⟩

instance (i : Ty B) : IsCommutative (.R i) := ⟨nofun⟩

instance : IsCommutative (.W .t : Eff B) := ⟨nofun⟩

instance : IsCommutative (.M : Eff B) := ⟨nofun⟩

instance : IsCommutative (.F : Eff B) := ⟨nofun⟩

instance [DecidableEq B] : DecidablePred (IsCommutative (B := B))
  | .C _ => isFalse fun h ↦ h.ne_C _ rfl
  | .W o => decidable_of_iff (o = .t)
    ⟨fun h ↦ { out := h, ne_C := nofun }, fun h ↦ h.out⟩
  | .S | .R _ | .M | .F => isTrue { out := trivial, ne_C := nofun }

private theorem seq_map_prodMk_comm {f : Eff B} (hc : f.IsCommutative) {α β : Type}
    (a : Obj D f α) (b : Obj D f β) :
    seq f hc.toIsApplicative (map f Prod.mk a) b =
      seq f hc.toIsApplicative (map f (fun b a ↦ (a, b)) b) a := by
  cases f with
  | S => exact CommApplicative.commutative_prod (m := Set) a b
  | R i => rfl
  | W o => obtain ⟨rfl⟩ := hc.toIsApplicative; exact Prod.ext rfl (propext and_comm)
  | C r => exact (hc.ne_C r rfl).elim
  | M =>
    ext p
    simp only [seq, map, Part.mem_bind_iff, Part.mem_map_iff, exists_exists_and_eq_and]
    exact ⟨fun ⟨x, hx, y, hy, h⟩ ↦ ⟨y, hy, x, hx, h⟩, fun ⟨y, hy, x, hx, h⟩ ↦ ⟨x, hx, y, hy, h⟩⟩
  | F => exact CommApplicative.commutative_prod (m := WithAlternatives) a b

/-- The `seq` of a commutative effect does not depend on the order of its two computations. -/
instance commApplicative (f : Eff B) [hc : f.IsCommutative] : CommApplicative (Obj D f) where
  commutative_prod := seq_map_prodMk_comm hc

/-- Quantification over continuations with result type `r` is not commutative if `r.Dom D` has
two elements. -/
theorem not_commApplicative_C (r : Ty B) [Nontrivial (r.Dom D)] :
    ¬ @CommApplicative (Obj D (.C r)) (monad (.C r)).toApplicative := fun h ↦ by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (r.Dom D)
  exact hxy (congrFun (@CommApplicative.commutative_prod _ _ h Unit Unit (fun _ ↦ x) fun _ ↦ y)
    fun _ ↦ x)

end Interpreter.Eff

namespace Interpreter.Mode

open ManySorted

variable {B : Type} {G : Language (Ty B)} {f : Eff B} {l r u : Ty B}

/-- At an applicative effect, `.join (.mapL (.mapR m))` is equivalent to `.ap m`: both merge the
effects of the two daughters with the left daughter's outermost. -/
theorem join_mapL_mapR_equiv_ap [f.IsApplicative] (m : Mode G.Binary l r u) :
    Mode.join (f := f) (.mapL (.mapR m)) ≈ .ap m := fun D _ ↦ funext₂ fun a b ↦ by
  simp only [eval, MetaCombinator.join, MetaCombinator.mapL, MetaCombinator.mapR,
    MetaCombinator.ap, joinM, seq_eq_bind_map, bind_map_left]
  rfl

/-- At a commutative effect, `.join (.mapR (.mapL m))` is equivalent to `.ap m`. -/
theorem join_mapR_mapL_equiv_ap [f.IsCommutative] (m : Mode G.Binary l r u) :
    Mode.join (f := f) (.mapR (.mapL m)) ≈ .ap m :=
  fun D _ ↦ funext₂ fun a b ↦ by
    rw [eval, eval, ← MetaCombinator.ap_flip]
    simp only [eval, MetaCombinator.join, MetaCombinator.mapL, MetaCombinator.mapR,
      MetaCombinator.ap, joinM, seq_eq_bind_map, bind_map_left]
    rfl

variable {D : B → Type} [M : G.Structure (Ty.Dom D)]

theorem eval_join_mapL [f.IsApplicative] (m : Mode G.Binary l r (.comp f u))
    (a : (Ty.comp f l).Dom D) (b : r.Dom D) :
    (Mode.join (f := f) (.mapL m)).eval D a b = a >>= fun x ↦ m.eval D x b :=
  bind_map_left _ _ _

theorem eval_join_mapR [f.IsApplicative] (m : Mode G.Binary l r (.comp f u))
    (a : l.Dom D) (b : (Ty.comp f r).Dom D) :
    (Mode.join (f := f) (.mapR m)).eval D a b = b >>= fun y ↦ m.eval D a y :=
  bind_map_left _ _ _

/-- At a commutative effect, Structured App of a mode is Structured App of its mirror image with
the daughters exchanged. -/
theorem eval_ap_comm [f.IsCommutative] {m : Mode G.Binary l r u} {m' : Mode G.Binary r l u}
    (hm : m.eval D = flip (m'.eval D)) :
    (Mode.ap (f := f) m).eval D = flip ((Mode.ap (f := f) m').eval D) :=
  funext₂ fun a b ↦ by
    rw [eval, hm]
    exact MetaCombinator.ap_flip (m'.eval D) b a

/-- At quantification over continuations with result type `o`, `.join (.mapR (.mapL m))` is not
equivalent to `.ap m` if `o.Dom D` has two elements. -/
theorem not_join_mapR_mapL_equiv_ap {o : Ty B} [Nontrivial (o.Dom D)]
    (m : Mode G.Binary l r u) :
    ¬ Mode.join (f := .C o) (.mapR (.mapL m)) ≈ .ap m := fun h ↦ by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (o.Dom D)
  exact hxy (congrFun (congrFun₂ (h D) (fun _ ↦ x) fun _ ↦ y) fun _ ↦ x).symm

end Interpreter.Mode
