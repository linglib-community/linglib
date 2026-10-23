module

public import Mathlib.Control.Monad.Cont

/-!
# Evaluating continuation computations

`ContT.eval` finishes a continuation computation by handing it the
trivial continuation `pure` — [charlow-2014]'s Lowering, Haskell's
`evalCont`, the LOWER of [barker-shan-2014]. The `eval_*` simp lemmas
mirror `ContT`'s `run_*` set: a chain of binds evaluates in bind order
and the applicative combination left-to-right, which is what lets bind
order model quantifier scope. `ContT.reset` evaluates and re-lifts,
delimiting scope the way scope islands do. For the linguistic
applications see `Studies/Charlow2014.lean` and `Studies/Barker2002.lean`.

## References

- <https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html#v:evalCont>
-/

@[expose] public section

universe u v

namespace ContT

variable {r α β : Type u} {m : Type u → Type v}

/-- `eval c` runs `c` at the trivial continuation `pure`. -/
def eval [Pure m] (c : ContT r m r) : m r := c.run pure

/-! ### Interaction with the monad operations -/

@[simp] theorem eval_pure [Pure m] (a : r) :
    eval (pure a : ContT r m r) = pure a := rfl

@[simp] theorem eval_bind [Pure m] (c : ContT r m α) (f : α → ContT r m r) :
    eval (c >>= f) = c.run fun x ↦ eval (f x) := rfl

@[simp] theorem eval_map [Pure m] (f : α → r) (c : ContT r m α) :
    eval (f <$> c) = c.run fun x ↦ pure (f x) := rfl

@[simp] theorem eval_seq [Pure m] (mf : ContT r m (α → r)) (mx : ContT r m α) :
    eval (mf <*> mx) = mf.run fun f ↦ mx.run fun x ↦ pure (f x) := rfl

/-! ### Evaluating lifted computations -/

@[simp] theorem eval_monadLift [Monad m] [LawfulMonad m] (x : m r) :
    eval (monadLift x : ContT r m r) = x :=
  bind_pure x

/-- `reset c` evaluates `c` and lifts the result again, `reset c = monadLift (eval c)`, which is
[charlow-2014]'s Reset after [danvy-filinski-1990]; [barker-2002]'s scope-island rule is an
instance. -/
def reset {r' : Type u} [Monad m] (c : ContT r m r) : ContT r' m r :=
  monadLift (eval c)

theorem reset_monadLift {r' : Type u} [Monad m] [LawfulMonad m] (x : m r) :
    reset (monadLift x : ContT r m r) = (monadLift x : ContT r' m r) :=
  congrArg monadLift (eval_monadLift x)

@[simp] theorem eval_reset [Monad m] [LawfulMonad m] (c : ContT r m r) :
    eval (reset c : ContT r m r) = eval c :=
  eval_monadLift _

@[simp] theorem reset_pure {r' : Type u} [Monad m] [LawfulMonad m] (a : r) :
    reset (pure a : ContT r m r) = (pure a : ContT r' m r) := by
  ext k
  simp only [reset, eval_pure, run_monadLift, pure_bind, run_pure]

theorem eval_seq_monadLift [Monad m] [LawfulMonad m]
    (f : α → β → r) (x : m α) (y : m β) :
    eval (f <$> (monadLift x : ContT r m α) <*> monadLift y) =
    f <$> x <*> y := by
  simp only [eval, seq_eq_bind_map, bind_map_left, run_bind, run_map,
    run_monadLift, Function.comp_def, bind_pure_comp]

theorem eval_map_monadLift [Monad m] [LawfulMonad m] (f : α → r) (x : m α) :
    eval (f <$> (monadLift x : ContT r m α)) = f <$> x := by
  simp only [eval_map, run_monadLift, bind_pure_comp]

/-- Resetting a lifted computation changes nothing ([charlow-2014]'s Fact 4.1). -/
theorem reset_map_monadLift {r' : Type u} [Monad m] [LawfulMonad m] (f : α → r) (x : m α) :
    reset (f <$> (monadLift x : ContT r m α)) = (monadLift (f <$> x) : ContT r' m r) :=
  congrArg monadLift (eval_map_monadLift f x)

theorem reset_seq_monadLift {r' : Type u} [Monad m] [LawfulMonad m]
    (f : α → β → r) (x : m α) (y : m β) :
    reset (f <$> (monadLift x : ContT r m α) <*> monadLift y) =
      (monadLift (f <$> x <*> y) : ContT r' m r) :=
  congrArg monadLift (eval_seq_monadLift f x y)

end ContT
