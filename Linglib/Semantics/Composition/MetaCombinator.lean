module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Control.Basic
public import Mathlib.Control.Functor
public import Linglib.Semantics.Composition.Lawful

/-!
# The meta-combinators over a functor, an applicative, a monad and an adjunction

Bumford and Charlow's meta-combinators take a basic combinator `(∗) : σ → τ → ω` and return one
for daughters that carry an effect, by the structure the effect has: the maps of a functor,
Structured App and the units of an applicative, Join of a monad, and the co-unit and ejections
of an adjunction. They are stated here for any functor, applicative, monad and adjunction on
types, and [each meta-mode of the effect-driven grammar means its
meta-combinator](##Interpreter.Mode.eval_ap) at the effect it lifts through. Every adjunction
[induces a monad through the grammar](##Interpreter.MetaCombinator.mapL_ejectR_counit).

## Main definitions

* `Interpreter.MetaCombinator.mapL`, `mapR`, `ap`, `unitL`, `unitR`, `join`: the
  meta-combinators of a functor, an applicative and a monad.
* `Interpreter.MetaCombinator.Output`, `outputInput`: the storing effect and its adjunction with
  reading.
* `Interpreter.MetaCombinator.counit`, `eject`, `ejectL`, `ejectR`: the meta-combinators of
  an adjunction.
* `Interpreter.Eff.functor`: the functor of an effect.

## Implementation notes

The storing effect `Output ι α = α × ι` is a functor and not mathlib's `WriterT`, whose functor
comes only with a monad over a monoid of logs. An adjunction is mathlib's `Adjunction` between
the functors `ofTypeFunctor Ω ⊣ ofTypeFunctor Γ`, so the unit, co-unit and induced monad are
mathlib's. The flattening of a monad is `(· >>= id)`, which is the Join of an effect after its
map at the identity: [Join means the meta-combinator](##Interpreter.Mode.eval_join) by the
identity law of the functor, and Join over a map is bind with no law.

## References

* [bumford-charlow-2026]
-/

@[expose] public section

namespace Interpreter

namespace MetaCombinator

open CategoryTheory

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

/-! ### Storing and reading -/

/-- The storing effect: a value paired with a stored datum. -/
def Output (ι α : Type u) : Type u := α × ι

namespace Output

variable {ι : Type u}

/-- Map the value, keeping the stored datum. -/
protected def map (f : α → β) (p : Output ι α) : Output ι β := (f p.1, p.2)

instance functor : Functor (Output ι) where map := Output.map

instance lawfulFunctor : LawfulFunctor (Output ι) := by constructor <;> intros <;> rfl

end Output

variable {ι : Type u}

/-- Storing is left adjoint to reading: the hom-equivalence is currying. -/
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

/-- Co-unit: map the combinator over both daughters and apply the co-unit to the result. It
takes the left adjoint from the left daughter and the right adjoint from the right one. -/
def counit (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) (star : σ → τ → ω)
    (e₁ : Ω σ) (e₂ : Γ τ) : ω :=
  adj.counit.app ω ((fun l ↦ (fun r ↦ star l r) <$> e₂) <$> e₁ : Ω (Γ ω))

theorem counit_outputInput (star : σ → τ → ω) (p : Output ι σ) (r : ReaderM ι τ) :
    counit (outputInput ι) star p r = star p.1 (r p.2) := rfl

/-- Eject: for a right adjoint `Γ` on types, functions into `Γ β` are `Γ` of functions. -/
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

/-- Eject Left: eject the effect of a left daughter that is a function into a right adjoint. -/
def ejectL (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) {σ' υ : Type u}
    (star : Γ (σ → σ') → τ → υ) (e₁ : σ → Γ σ') (e₂ : τ) : υ :=
  star (eject adj e₁) e₂

/-- Eject Right: eject the effect of a right daughter that is a function into a right adjoint. -/
def ejectR (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) {τ' υ : Type u}
    (star : σ → Γ (τ → τ') → υ) (e₁ : σ) (e₂ : τ → Γ τ') : υ :=
  star e₁ (eject adj e₂)

theorem counit_ba_eject (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) (a : Ω α)
    (k : α → Γ β) : counit adj ba a (eject adj k) = adj.counit.app β (k <$> a : Ω (Γ β)) := by
  have h : (fun l ↦ (fun r ↦ ba l r) <$> eject adj k) = k := (eject adj).left_inv k
  simp only [counit, h]

/-- Every adjunction gives rise to a monad through the grammar: Map Left over Eject Right over
the Co-unit of backward application is the bind of the monad `Γ Ω` the adjunction induces. -/
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

/-! ### The meta-modes mean the meta-combinators -/

/-- The functor of an effect. -/
@[reducible] def Eff.functor {B : Type} {D : B → Type} (f : Eff B) : Functor (Eff.Obj D f) where
  map := Eff.map f

namespace Mode

open ManySorted

variable {B : Type} {D : B → Type} {G : Language (Ty B)} [M : G.Structure (Ty.Dom D)]
  {f : Eff B} {i l l' r r' u : Ty B}

theorem eval_mapR (m : Mode G.Binary l r u) :
    letI := Eff.functor (D := D) f
    (Mode.mapR (f := f) m).eval D = MetaCombinator.mapR (m.eval D) := rfl

theorem eval_mapL (m : Mode G.Binary l r u) :
    letI := Eff.functor (D := D) f
    (Mode.mapL (f := f) m).eval D = MetaCombinator.mapL (m.eval D) := rfl

theorem eval_ap (h : f.IsApplicative) (m : Mode G.Binary l r u) :
    letI := Eff.monad (D := D) f h
    (Mode.ap h m).eval D = MetaCombinator.ap (m.eval D) := rfl

theorem eval_unitR (h : f.IsApplicative) (m : Mode G.Binary (l ⇒ l') r u) :
    letI := Eff.monad (D := D) f h
    (Mode.unitR h m).eval D = MetaCombinator.unitR (m.eval D) := rfl

theorem eval_unitL (h : f.IsApplicative) (m : Mode G.Binary l (r ⇒ r') u) :
    letI := Eff.monad (D := D) f h
    (Mode.unitL h m).eval D = MetaCombinator.unitL (m.eval D) := rfl

/-- Join means the meta-combinator of the effect's monad, whose flattening is the effect's join
after its map at the identity. -/
theorem eval_join (h : f.IsApplicative) (m : Mode G.Binary l r (.comp f (.comp f u))) :
    letI := Eff.monad (D := D) f h
    (Mode.join h m).eval D = MetaCombinator.join (m.eval D) :=
  funext₂ fun a b ↦ congrArg (Eff.join f h) (Eff.map_id f (m.eval D a b)).symm

/-- Join over Map Left is the bind of the effect's monad. -/
theorem eval_join_mapL (h : f.IsApplicative) (m : Mode G.Binary l r (.comp f u))
    (a : (Ty.comp f l).Dom D) (b : r.Dom D) :
    letI := Eff.monad (D := D) f h
    (Mode.join h (.mapL m)).eval D a b = a >>= fun x ↦ m.eval D x b := rfl

/-- Join over Map Right is the bind of the effect's monad. -/
theorem eval_join_mapR (h : f.IsApplicative) (m : Mode G.Binary l r (.comp f u))
    (a : l.Dom D) (b : (Ty.comp f r).Dom D) :
    letI := Eff.monad (D := D) f h
    (Mode.join h (.mapR m)).eval D a b = b >>= fun y ↦ m.eval D a y := rfl

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
