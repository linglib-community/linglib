module

public import Mathlib.Control.Basic
public import Mathlib.Control.Combinators
public import Mathlib.Control.Functor

/-!
# The meta-combinators over a functor, an applicative and a monad

Bumford and Charlow's meta-combinators take a basic combinator `(∗) : σ → τ → ω` and return one
for daughters that carry an effect, by the structure the effect has: the maps of a functor,
Structured App and the units of an applicative, and Join of a monad. They are stated here for
any functor, applicative and monad on types, and the effect-driven grammar's modes are defined
by them. Where the applicative is commutative, [Structured App does not depend on which daughter
is on the left](##Interpreter.MetaCombinator.ap_flip).

## Main definitions

* `Interpreter.MetaCombinator.mapL`, `mapR`, `ap`, `unitL`, `unitR`, `join`: the
  meta-combinators of a functor, an applicative and a monad.

## References

* [bumford-charlow-2026]
-/

@[expose] public section

namespace Interpreter

namespace MetaCombinator

universe u v

variable {σ τ ω α β : Type u}

/-- Forward application `(>)`. -/
def fa (f : α → β) (x : α) : β := f x

/-- Backward application `(<)`. -/
def ba (x : α) (f : α → β) : β := f x

section Functor

variable {F : Type u → Type v} [Functor F]

/-- Map Left: map the combinator over an effectful left daughter. -/
def mapL (star : σ → τ → ω) (e₁ : F σ) (e₂ : τ) : F ω := (fun a ↦ star a e₂) <$> e₁

/-- Map Right: map the combinator over an effectful right daughter. -/
def mapR (star : σ → τ → ω) (e₁ : σ) (e₂ : F τ) : F ω := (fun b ↦ star e₁ b) <$> e₂

theorem mapR_fa (f : α → β) (x : F α) : mapR fa f x = f <$> x := rfl

theorem mapL_ba (x : F α) (f : α → β) : mapL ba x f = f <$> x := rfl

theorem mapR_mapR_fa {G : Type u → Type u} [Functor G] (f : α → β) (x : F (G α)) :
    mapR (mapR fa) f x = (f <$> Functor.Comp.mk x).run := rfl

end Functor

section Applicative

variable {F : Type u → Type v} [Applicative F]

/-- Structured App: combine two daughters carrying the same applicative effect, merging the
effects with the left daughter's first. -/
def ap (star : σ → τ → ω) (e₁ : F σ) (e₂ : F τ) : F ω := star <$> e₁ <*> e₂

/-- Unit Left: a right daughter expecting a computation is given a pure one. -/
def unitL {τ' : Type u} (star : σ → (τ → τ') → ω) (e₁ : σ) (e₂ : F τ → τ') : ω :=
  star e₁ fun b ↦ e₂ (pure b)

/-- Unit Right: a left daughter expecting a computation is given a pure one. -/
def unitR {σ' : Type u} (star : (σ → σ') → τ → ω) (e₁ : F σ → σ') (e₂ : τ) : ω :=
  star (fun a ↦ e₁ (pure a)) e₂

theorem ap_fa [LawfulApplicative F] (f : F (α → β)) (x : F α) :
    ap fa f x = f <*> x :=
  congrArg (· <*> x) (id_map f)

/-- At a commutative applicative, Structured App of a combinator is Structured App of its mirror
image at the daughters in the other order. -/
theorem ap_flip [CommApplicative F] (star : σ → τ → ω) (e₁ : F σ) (e₂ : F τ) :
    ap (flip star) e₂ e₁ = ap star e₁ e₂ :=
  (CommApplicative.commutative_map e₁ e₂).symm

end Applicative

section Monad

variable {M : Type u → Type u} [Monad M]

/-- Join: flatten the doubled effect a combinator returns. -/
def join (star : σ → τ → M (M ω)) (e₁ : σ) (e₂ : τ) : M ω := joinM (star e₁ e₂)

variable [LawfulMonad M]

/-- Join over Map Left of backward application is bind. -/
theorem join_mapL_ba (m : M α) (k : α → M β) : join (mapL ba) m k = m >>= k :=
  bind_map_left _ _ _

/-- Join over Map Right of forward application is bind with its arguments flipped. -/
theorem join_mapR_fa (k : α → M β) (m : M α) : join (mapR fa) k m = m >>= k :=
  bind_map_left _ _ _

end Monad

end MetaCombinator

end Interpreter
