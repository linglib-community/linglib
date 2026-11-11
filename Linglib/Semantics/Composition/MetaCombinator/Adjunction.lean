module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Types.Basic
public import Linglib.Semantics.Composition.Mode.Basic

/-!
# The meta-combinators of an adjunction

Storing is left adjoint to reading, and an adjunction adds two meta-combinators to those of a
functor: the co-unit, which cancels the left adjoint of one daughter against the right adjoint
of the other, and the ejection of a right adjoint from a function. They are stated here for any
adjunction on types, and [the Co-unit](##Interpreter.Mode.eval_counit) and Eject modes of the
effect-driven grammar mean them at storing and reading. Every adjunction [induces a monad through
the grammar](##Interpreter.MetaCombinator.mapL_ejectR_counit).

## Main definitions

* `Interpreter.MetaCombinator.Output`, `outputInput`: the storing effect and its adjunction with
  reading.
* `Interpreter.MetaCombinator.counit`, `eject`, `ejectL`, `ejectR`: the meta-combinators of an
  adjunction.

## Implementation notes

The storing effect `Output ι α = α × ι` is a functor and not mathlib's `WriterT`, whose functor
comes only with a monad over a monoid of logs. An adjunction is mathlib's `Adjunction` between
the functors `ofTypeFunctor Ω ⊣ ofTypeFunctor Γ`, so the unit, co-unit and induced monad are
mathlib's.

## References

* [bumford-charlow-2026]
-/

@[expose] public section

namespace Interpreter

namespace MetaCombinator

open CategoryTheory

universe u

variable {σ τ ω α β : Type u}

/-! ### Storing and reading -/

/-- The storing effect, a value paired with a stored datum. -/
def Output (ι α : Type u) : Type u := α × ι

namespace Output

variable {ι : Type u}

/-- The map of the storing effect, on the value. -/
protected def map (f : α → β) (p : Output ι α) : Output ι β := (f p.1, p.2)

instance functor : Functor (Output ι) where map := Output.map

instance lawfulFunctor : LawfulFunctor (Output ι) := by constructor <;> intros <;> rfl

end Output

variable {ι : Type u}

/-- Storing is left adjoint to reading, with currying as the hom-equivalence. -/
def outputInput (ι : Type u) : ofTypeFunctor (Output ι) ⊣ ofTypeFunctor (ReaderM ι) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun α β ↦
        TypeCat.homEquiv.trans ((Equiv.curry α ι β).trans TypeCat.homEquiv.symm)
      homEquiv_naturality_left_symm := fun _ _ ↦ rfl
      homEquiv_naturality_right := fun _ _ ↦ rfl }

theorem outputInput_homEquiv_apply (f : Output ι α ⟶ β) (a : α) (x : ι) :
    (outputInput ι).homEquiv α β f a x = f (a, x) := rfl

theorem outputInput_unit_app (a : α) (x : ι) : (outputInput ι).unit.app α a x = (a, x) := rfl

theorem outputInput_counit_app (f : ReaderM ι α) (x : ι) :
    (outputInput ι).counit.app α (f, x) = f x := rfl

/-! ### The meta-combinators of an adjunction -/

section Adjunction

variable {Ω Γ : Type u → Type u} [Functor Ω] [LawfulFunctor Ω] [Functor Γ] [LawfulFunctor Γ]

/-- The Co-unit of a combinator maps it over both daughters and applies the co-unit of the
adjunction to the result. The left adjoint comes from the left daughter and the right adjoint
from the right. -/
def counit (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) (star : σ → τ → ω)
    (e₁ : Ω σ) (e₂ : Γ τ) : ω :=
  adj.counit.app ω ((fun l ↦ (fun r ↦ star l r) <$> e₂) <$> e₁ : Ω (Γ ω))

theorem counit_outputInput (star : σ → τ → ω) (p : Output ι σ) (r : ReaderM ι τ) :
    counit (outputInput ι) star p r = star p.1 (r p.2) := rfl

/-- For a right adjoint `Γ` on types, functions into `Γ β` are `Γ` of functions. -/
def eject (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) : (α → Γ β) ≃ Γ (α → β) where
  toFun k := (adj.homEquiv PUnit (α → β)
    (↾fun w a ↦ (adj.homEquiv PUnit β).symm (↾fun _ ↦ k a) w) PUnit.unit : Γ (α → β))
  invFun m a := (fun f ↦ f a) <$> m
  left_inv k := by
    funext a
    change ((ofTypeFunctor Γ).map (↾fun f : α → β ↦ f a)) (adj.homEquiv PUnit (α → β)
      (↾fun w a ↦ (adj.homEquiv PUnit β).symm (↾fun _ ↦ k a) w) PUnit.unit) = k a
    rw [← ConcreteCategory.comp_apply, ← adj.homEquiv_naturality_right]
    change adj.homEquiv PUnit β ((adj.homEquiv PUnit β).symm (↾fun _ ↦ k a)) PUnit.unit = _
    rw [Equiv.apply_symm_apply]
    rfl
  right_inv m := by
    have h (a : α) : (adj.homEquiv PUnit β).symm (↾fun _ ↦ ((fun f : α → β ↦ f a) <$> m : Γ β)) =
        (adj.homEquiv PUnit (α → β)).symm (↾fun _ ↦ m) ≫ ↾fun f : α → β ↦ f a :=
      adj.homEquiv_naturality_right_symm (↾fun _ ↦ m) (↾fun f : α → β ↦ f a)
    simp only [h]
    change adj.homEquiv PUnit (α → β) ((adj.homEquiv PUnit (α → β)).symm (↾fun _ ↦ m))
      PUnit.unit = m
    rw [Equiv.apply_symm_apply]
    rfl

theorem eject_outputInput (k : α → ReaderM ι β) : eject (outputInput ι) k = fun i a ↦ k a i :=
  rfl

/-- Eject Left of a combinator ejects the right adjoint from a left daughter that is a function
into it. -/
def ejectL (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) {σ' υ : Type u}
    (star : Γ (σ → σ') → τ → υ) (e₁ : σ → Γ σ') (e₂ : τ) : υ :=
  star (eject adj e₁) e₂

/-- Eject Right of a combinator ejects the right adjoint from a right daughter that is a function
into it. -/
def ejectR (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) {τ' υ : Type u}
    (star : σ → Γ (τ → τ') → υ) (e₁ : σ) (e₂ : τ → Γ τ') : υ :=
  star e₁ (eject adj e₂)

theorem counit_ba_eject (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) (a : Ω α)
    (k : α → Γ β) : counit adj ba a (eject adj k) = adj.counit.app β (k <$> a : Ω (Γ β)) := by
  have h : (fun l ↦ (fun r ↦ ba l r) <$> eject adj k) = k := (eject adj).left_inv k
  simp only [counit, h]

/-- Map Left over Eject Right over the Co-unit of backward application is the bind of the monad
`Γ Ω` that the adjunction induces. -/
theorem mapL_ejectR_counit (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) (m : Γ (Ω α))
    (k : α → Γ (Ω β)) :
    mapL (ejectR adj (counit adj ba)) m k = adj.toMonad.μ.app β (adj.toMonad.map (↾k) m) := by
  simp only [mapL, ejectR, counit_ba_eject]
  change _ = (fun x : Ω (Γ (Ω β)) ↦ adj.counit.app (Ω β) x) <$>
    ((fun a : Ω α ↦ (k <$> a : Ω (Γ (Ω β)))) <$> m)
  rw [← comp_map]
  rfl

end Adjunction

end MetaCombinator

namespace Mode

open ManySorted

variable {B : Type} {D : B → Type} {G : Language (Ty B)} [M : G.Structure (Ty.Dom D)]
  {i l l' r r' u : Ty B}

theorem eval_counit (m : Mode G.Binary l r u) :
    (Mode.counit (i := i) m).eval D =
      MetaCombinator.counit (MetaCombinator.outputInput (i.Dom D)) (m.eval D) := rfl

theorem eval_ejectR (m : Mode G.Binary l (.comp (.R i) (r ⇒ r')) u) :
    (Mode.ejectR m).eval D =
      MetaCombinator.ejectR (MetaCombinator.outputInput (i.Dom D)) (m.eval D) := rfl

theorem eval_ejectL (m : Mode G.Binary (.comp (.R i) (l ⇒ l')) r u) :
    (Mode.ejectL m).eval D =
      MetaCombinator.ejectL (MetaCombinator.outputInput (i.Dom D)) (m.eval D) := rfl

end Mode

end Interpreter
