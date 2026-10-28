module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Control.Basic
public import Mathlib.Control.Functor

/-!
# Bumford and Charlow 2026: effect-driven interpretation

[bumford-charlow-2026] treat pronouns, antecedents, indefinites and quantifiers as computations
with effects, and the modes of semantic combination as higher-order operations that lift a basic
combinator through the algebra of an effect: maps for functors (chapter 2), structured
application for applicatives (chapter 3), join for monads (chapter 4), and co-unit and eject for
adjunctions (chapter 5). This file states the modes over Lean's `Functor`, `Applicative` and
`Monad` classes and mathlib's adjunctions, and proves the results of chapter 5 about them.

A pronoun reads a referent and an antecedent stores one. Storing is left adjoint to reading,
with currying as the hom-equivalence, and the co-unit mode cancels the two effects, so a
sentence whose pronouns are bound denotes a pure value. The co-unit mode takes the left adjoint
from the left daughter, so an antecedent must precede the pronoun it binds however the scopes
are inverted: this is crossover, proved here over the book's type-driven grammar.

Every right adjoint on types distributes over function types, and the eject modes use this.
With them the grammar derives, with no new machinery, the bind of the reader transformer, the
bind of the monad that any adjunction induces, which for storing and reading is Lean's state
monad, and, with indeterminacy in between, the state transformer over sets that dynamic
semantics is built on.

## Main definitions

* `mapL`, `mapR`, `structuredApp`, `joinMode`: the map, structured application and join modes
* `Output`, `outputInput`: the storing effect `W` and the adjunction `W ⊣ R`
* `counitMode`, `eject`, `ejectL`, `ejectR`: the modes an adjunction adds
* `Ty`, `Eff`, `Combine`: the type-driven grammar of the book's Appendix B

## Implementation notes

The storing effect `Output ι α = α × ι` is a functor and not mathlib's `WriterT`, whose functor
comes only with a monad over a monoid of logs. A single stored referent cannot be merged with
another, which is the book's reason that this `W` is not a monad (section 5.3.4). The
supplement effect, whose log is a monoid, is `Composition/Writer.lean`.

The modes act on Lean's type constructors; an adjunction is mathlib's `Adjunction` between the
corresponding functors `ofTypeFunctor Ω ⊣ ofTypeFunctor Γ`, so the unit, co-unit and induced
monad are mathlib's. The grammar's `Ty` has computation types `comp f a` for all four effects.
`Montague.Ty` has them for the reader only, with the map and unit modes and every derivation of a
tree (`Montague.Ty.modes`, `PhraseStructure.Tree.translations`), so the grammar here keeps its own
types for the effects and modes the engine lacks. As in Appendix B, a writer is applicative exactly
when its datum is `t`, every applicative effect of the grammar is monadic, and the only
adjunction is `W i ⊣ R i`. Base types are `e` and `t`.

The Element is forthcoming; equation, section and appendix locators are to the arXiv version of
April 2025.

## TODO

* Islands (section 5.4): the book filters the results at an island node by a predicate on
  their types; the grammar here has no syntax trees.
* The denotations of derivations, the book's interpreter of section 5.5: `Combine` is a `Prop`,
  and the interpreter is `Montague.Mode` with `Montague.Ty.modes`, which has the reader with the
  map and unit modes so far. Moving this grammar onto it needs the indeterminacy, storing and
  quantification effects, and structured application, join, co-unit, eject and lowering.

## References

* [bumford-charlow-2026]
* [barker-shan-2014]
-/

@[expose] public section

namespace BumfordCharlow2026

open CategoryTheory

universe u v

/-! ### Modes of combination

A mode of combination takes a basic combinator `(∗) : σ → τ → ω` and returns one that works when
a daughter carries an effect. -/

section Modes

variable {σ τ ω α β : Type u}

/-- Forward application `(>)`. -/
def fa (f : α → β) (x : α) : β := f x

/-- Backward application `(<)`. -/
def ba (x : α) (f : α → β) : β := f x

section Functor

variable {F : Type u → Type v} [Functor F]

/-- Map Left `F̄` (2.17a): map the combinator over an effectful left daughter. -/
def mapL (star : σ → τ → ω) (e₁ : F σ) (e₂ : τ) : F ω := (fun a => star a e₂) <$> e₁

/-- Map Right `F̃` (2.17b): map the combinator over an effectful right daughter. -/
def mapR (star : σ → τ → ω) (e₁ : σ) (e₂ : F τ) : F ω := (fun b => star e₁ b) <$> e₂

-- (2.18)
theorem mapR_fa (f : α → β) (x : F α) : mapR fa f x = f <$> x := rfl

theorem mapL_ba (x : F α) (f : α → β) : mapL ba x f = f <$> x := rfl

-- (2.24)
theorem mapR_mapR_fa {G : Type u → Type u} [Functor G] (f : α → β) (x : F (G α)) :
    mapR (mapR fa) f x = (f <$> Functor.Comp.mk x).run := rfl

end Functor

/-- Structured Application `A` (3.10): combine two daughters carrying the same applicative
effect, merging the effects. -/
def structuredApp {F : Type u → Type v} [Applicative F] (star : σ → τ → ω) (e₁ : F σ)
    (e₂ : F τ) : F ω :=
  pure star <*> e₁ <*> e₂

theorem structuredApp_fa {F : Type u → Type v} [Applicative F] [LawfulApplicative F]
    (f : F (α → β)) (x : F α) : structuredApp fa f x = f <*> x := by
  rw [structuredApp, pure_seq]
  exact congrArg (· <*> x) (id_map f)

section Monad

variable {M : Type u → Type u} [Monad M]

/-- Join `J` (4.22): flatten the doubled effect a combinator returns, `J(∗) E₁ E₂ := μ(E₁ ∗ E₂)`.
-/
def joinMode (star : σ → τ → M (M ω)) (e₁ : σ) (e₂ : τ) : M ω := joinM (star e₁ e₂)

variable [LawfulMonad M]

/-- `J(F̄ <)` is bind (after (4.22)). -/
theorem joinMode_mapL_ba (m : M α) (k : α → M β) : joinMode (mapL ba) m k = m >>= k :=
  bind_map_left _ _ _

/-- `J(F̃ >)` is bind with its arguments flipped, the book's `(=>>)` (after (4.22)). -/
theorem joinMode_mapR_fa (k : α → M β) (m : M α) : joinMode (mapR fa) k m = m >>= k :=
  bind_map_left _ _ _

end Monad

/-- The order of the maps sets the priority of the effects (2.22): mapping over the left
daughter first gives its request the outer position. -/
example {E : Type} (saw : E → E → Prop) :
    mapL (F := ReaderM E) (mapR (F := ReaderM E) ba) (fun y => y) (fun x => saw x) =
      fun y x => saw x y := rfl

example {E : Type} (saw : E → E → Prop) :
    mapR (F := ReaderM E) (mapL (F := ReaderM E) ba) (fun y => y) (fun x => saw x) =
      fun x y => saw x y := rfl

end Modes

/-! ### Storing and reading

A pronoun reads a referent from its context, `R α = ι → α` (5.1a), and an antecedent stores its
referent alongside its value, `W α = α × ι` (5.1b). Functions out of `W α` are functions into
`R β` by currying (5.3), which makes `W` left adjoint to `R`. -/

/-- The storing effect `W`: a value paired with a stored datum. -/
def Output (ι α : Type u) : Type u := α × ι

namespace Output

variable {ι α β : Type u}

/-- Map the value, keeping the stored datum. -/
protected def map (f : α → β) (p : Output ι α) : Output ι β := (f p.1, p.2)

instance functor : Functor (Output ι) where map := Output.map

instance lawfulFunctor : LawfulFunctor (Output ι) := by constructor <;> intros <;> rfl

end Output

variable {ι α β : Type u}

/-- The antecedent operator `⊲` (5.1b): an entity stores itself. -/
def store (x : ι) : Output ι ι := (x, x)

/-- The pronoun (5.1a): read the referent. -/
def pronoun : ReaderM ι ι := fun i => i

/-- Storing is left adjoint to reading (5.3): the hom-equivalence `Φ` is currying. -/
def outputInput (ι : Type u) : ofTypeFunctor (Output ι) ⊣ ofTypeFunctor (ReaderM ι) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun α β =>
        TypeCat.homEquiv.trans ((Equiv.curry α ι β).trans TypeCat.homEquiv.symm)
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun _ _ => rfl }

theorem outputInput_homEquiv_apply (f : Output ι α ⟶ β) (a : α) (x : ι) :
    (outputInput ι).homEquiv α β f a x = f (a, x) := rfl

-- (5.4)
theorem outputInput_unit_app (a : α) (x : ι) : (outputInput ι).unit.app α a x = (a, x) := rfl

theorem outputInput_counit_app (f : ReaderM ι α) (x : ι) :
    (outputInput ι).counit.app α (f, x) = f x := rfl

/-! ### The co-unit mode

For any adjunction `Ω ⊣ Γ`, the co-unit mode maps the combinator over both daughters and applies
the co-unit to the result. -/

section Adjunction

variable {Ω Γ : Type u → Type u} [Functor Ω] [LawfulFunctor Ω] [Functor Γ] [LawfulFunctor Γ]

/-- The co-unit mode `C` (5.8): `C(∗) E₁ E₂ := ε((λl. (λr. l ∗ r) • E₂) • E₁)`. It takes the
left adjoint from the left daughter and the right adjoint from the right one. -/
def counitMode (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) {σ τ ω : Type u} (star : σ → τ → ω)
    (e₁ : Ω σ) (e₂ : Γ τ) : ω :=
  adj.counit.app ω ((fun l => (fun r => star l r) <$> e₂) <$> e₁ : Ω (Γ ω))

theorem counitMode_outputInput {σ τ ω : Type u} (star : σ → τ → ω) (p : Output ι σ)
    (r : ReaderM ι τ) : counitMode (outputInput ι) star p r = star p.1 (r p.2) := rfl

/-- The co-unit of `W ⊣ R` binds a pronoun to a preceding antecedent (5.5), and the same
daughters combined by maps alone keep both effects (5.2). -/
example {E : Type} (moon spot : E → E) (obscure : E → E → Prop) (j : E) :
    counitMode (outputInput E) ba (mapL ba (store j) moon)
      (mapR fa obscure (mapL ba pronoun spot)) = obscure (spot j) (moon j) := rfl

example {E : Type} (moon spot : E → E) (obscure : E → E → Prop) (j : E) :
    mapL (mapR ba) (mapL ba (store j) moon) (mapR fa obscure (mapL ba pronoun spot)) =
      ((fun x => obscure (spot x) (moon j), j) : Output E (ReaderM E Prop)) := rfl

/-- Eject `Υ` (5.24): for a right adjoint `Γ` on types, functions into `Γ β` are `Γ` of
functions. -/
def eject (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) : (α → Γ β) ≃ Γ (α → β) where
  toFun k := (adj.homEquiv PUnit (α → β)
    (↾fun w a => (adj.homEquiv PUnit β).symm (↾fun _ => k a) w) PUnit.unit : Γ (α → β))
  invFun m a := (fun f => f a) <$> m
  left_inv k := by
    funext a
    change ((ofTypeFunctor Γ).map (↾fun f : α → β => f a)) (adj.homEquiv PUnit (α → β)
      (↾fun w a => (adj.homEquiv PUnit β).symm (↾fun _ => k a) w) PUnit.unit) = k a
    rw [← ConcreteCategory.comp_apply, ← adj.homEquiv_naturality_right]
    change adj.homEquiv PUnit β ((adj.homEquiv PUnit β).symm (↾fun _ => k a)) PUnit.unit = _
    rw [Equiv.apply_symm_apply]
    rfl
  right_inv m := by
    have h (a : α) : (adj.homEquiv PUnit β).symm (↾fun _ => ((fun f : α → β => f a) <$> m : Γ β)) =
        (adj.homEquiv PUnit (α → β)).symm (↾fun _ => m) ≫ ↾fun f : α → β => f a :=
      adj.homEquiv_naturality_right_symm (↾fun _ => m) (↾fun f : α → β => f a)
    simp only [h]
    change adj.homEquiv PUnit (α → β) ((adj.homEquiv PUnit (α → β)).symm (↾fun _ => m))
      PUnit.unit = m
    rw [Equiv.apply_symm_apply]
    rfl

-- (5.22)
theorem eject_outputInput (k : α → ReaderM ι β) : eject (outputInput ι) k = fun i a => k a i :=
  rfl

/-- Eject Left (5.25a): eject the effect of a left daughter that is a function into a right
adjoint. -/
def ejectL (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) {σ σ' τ υ : Type u}
    (star : Γ (σ → σ') → τ → υ) (e₁ : σ → Γ σ') (e₂ : τ) : υ :=
  star (eject adj e₁) e₂

/-- Eject Right (5.25b). -/
def ejectR (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) {σ τ τ' υ : Type u}
    (star : σ → Γ (τ → τ') → υ) (e₁ : σ) (e₂ : τ → Γ τ') : υ :=
  star e₁ (eject adj e₂)

theorem counitMode_ba_eject (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) (a : Ω α)
    (k : α → Γ β) : counitMode adj ba a (eject adj k) = adj.counit.app β (k <$> a : Ω (Γ β)) := by
  have h : (fun l => (fun r => ba l r) <$> eject adj k) = k := (eject adj).left_inv k
  simp only [counitMode, h]

/-- Every adjunction gives rise to a monad through the grammar (section 5.3.4): the mode
`F̄ ® C <` is the bind of the monad `Γ Ω` the adjunction induces. -/
theorem mapL_ejectR_counitMode (adj : ofTypeFunctor Ω ⊣ ofTypeFunctor Γ) (m : Γ (Ω α))
    (k : α → Γ (Ω β)) :
    mapL (ejectR adj (counitMode adj ba)) m k = adj.toMonad.μ.app β (adj.toMonad.map (↾k) m) := by
  simp only [mapL, ejectR, counitMode_ba_eject]
  change _ = (fun x : Ω (Γ (Ω β)) => adj.counit.app (Ω β) x) <$>
    ((fun a : Ω α => (k <$> a : Ω (Γ (Ω β)))) <$> m)
  rw [← comp_map]
  rfl

end Adjunction

/-! ### Monads from storing and reading -/

/-- The state monad is the monad of `W ⊣ R`, and its bind is `F̄ ® C <` (5.37), (5.38). -/
theorem mapL_ejectR_counitMode_outputInput (m : StateM ι α) (k : α → StateM ι β) :
    mapL (F := ReaderM ι) (ejectR (outputInput ι) (counitMode (outputInput ι) ba)) m k =
      m >>= k := rfl

/-- With a monad in between, `F̄ J F̄ ® C <` is the bind of the state transformer (5.39). -/
theorem mapL_joinMode_mapL_ejectR_counitMode {M : Type u → Type u} [Monad M] [LawfulMonad M]
    (m : StateT ι M α) (k : α → StateT ι M β) :
    mapL (F := ReaderM ι)
      (joinMode (mapL (ejectR (outputInput ι) (counitMode (outputInput ι) ba)))) m k =
      m >>= k := by
  funext s
  exact bind_map_left
    (fun p : Output ι α => ejectR (outputInput ι) (counitMode (outputInput ι) ba) p k) (m s) id

/-- Ejecting the reader from a function into it, `® A J F̃ >` is the bind of the reader
transformer (5.28), (5.29). -/
theorem ejectL_structuredApp_joinMode_mapR {M : Type u → Type u} [Monad M] [LawfulMonad M]
    (m : ReaderT ι M α) (k : α → ReaderT ι M β) :
    ejectL (outputInput ι) (structuredApp (F := ReaderM ι) (joinMode (mapR fa))) k m =
      m >>= k := by
  funext s
  exact bind_map_left (fun b => k b s) (m s) id

/-! ### The type-driven grammar

Appendix B implements the grammar as a function from the types of two daughters to the modes
that combine them and the types they yield. `Combine l r u` says that some mode combines a left
daughter of type `l` with a right daughter of type `r` into a result of type `u`. -/

mutual

/-- The types of the grammar. -/
inductive Ty where
  | e
  | t
  | fn (a b : Ty)
  /-- A computation with effect `f` and value type `a`. -/
  | comp (f : Eff) (a : Ty)

/-- The effects of the grammar. -/
inductive Eff where
  /-- Indeterminacy. -/
  | S
  /-- Reading a datum of type `i`. -/
  | R (i : Ty)
  /-- Storing a datum of type `o`. -/
  | W (o : Ty)
  /-- Quantifying over contexts with result type `r`. -/
  | C (r : Ty)

end

namespace Eff

/-- An effect is applicative, and then also monadic, unless it stores something other than a
truth value, since only `t` is a monoid. -/
def IsApplicative : Eff → Prop
  | W o => o = .t
  | _ => True

/-- `f ⊣ g`: storing a datum is left adjoint to reading one of the same type, which is
`outputInput`. -/
def Adjoint : Eff → Eff → Prop
  | W o, R i => o = i
  | _, _ => False

/-- `g` has a left adjoint. -/
def IsRightAdjoint (g : Eff) : Prop := ∃ f, Adjoint f g

/-- The reading effects. -/
def IsReader : Eff → Prop
  | R _ => True
  | _ => False

theorem not_isReader_of_adjoint {f g : Eff} (h : Adjoint f g) : ¬ f.IsReader := by
  cases f <;> cases g <;> simp_all [Adjoint, IsReader]

end Eff

open Ty Eff

mutual

/-- The binary modes: the basic combinators and the higher-order modes of Figure 10. -/
inductive Binary : Ty → Ty → Ty → Prop
  | fa {a b} : Binary (fn a b) a b
  | ba {a b} : Binary a (fn a b) b
  | pm {a} : Binary (fn a t) (fn a t) (fn a t)
  | mapR {l r u f} : Combine l r u → Binary l (comp f r) (comp f u)
  | mapL {l r u f} : Combine l r u → Binary (comp f l) r (comp f u)
  | app {l r u f} : f.IsApplicative → Combine l r u → Binary (comp f l) (comp f r) (comp f u)
  | unitR {l l' r u f} : f.IsApplicative → Combine (fn l l') r u →
      Binary (fn (comp f l) l') r u
  | unitL {l r r' u f} : f.IsApplicative → Combine l (fn r r') u →
      Binary l (fn (comp f r) r') u
  | counit {l r u f g} : f.Adjoint g → Combine l r u → Binary (comp f l) (comp g r) u
  | ejectR {l r r' u g} : g.IsRightAdjoint → Combine l (comp g (fn r r')) u →
      Binary l (fn r (comp g r')) u
  | ejectL {l l' r u g} : g.IsRightAdjoint → Combine (comp g (fn l l')) r u →
      Binary (fn l (comp g l')) r u

/-- The book's `combine`: a binary mode, possibly followed by a join or a closure. -/
inductive Combine : Ty → Ty → Ty → Prop
  | bin {l r u} : Binary l r u → Combine l r u
  | join {l r a f} : f.IsApplicative → Binary l r (comp f (comp f a)) → Combine l r (comp f a)
  | lower {l r a} : Binary l r (comp (C a) a) → Combine l r a

end

/-- The type still requests a datum: a reading effect at a strictly positive position. -/
def Ty.Reads : Ty → Prop
  | fn _ b => b.Reads
  | comp f a => f.IsReader ∨ a.Reads
  | _ => False

/-- No reading effect anywhere in the type. -/
def Ty.InputFree : Ty → Prop
  | fn a b => a.InputFree ∧ b.InputFree
  | comp f a => ¬ f.IsReader ∧ a.InputFree
  | _ => True

theorem Ty.InputFree.not_reads : ∀ {a : Ty}, a.InputFree → ¬ a.Reads
  | fn _ b, h => not_reads (a := b) h.2
  | comp _ a, h => fun h' => h'.elim h.1 (not_reads (a := a) h.2)
  | e, _ => id
  | t, _ => id

mutual

theorem Binary.reads {l r u : Ty} : Binary l r u → l.Reads → r.InputFree → u.Reads
  | .fa, hl, _ => hl
  | .ba, hl, hr => absurd hl hr.1.not_reads
  | .pm, hl, _ => hl
  | .mapR h, hl, hr => .inr (h.reads hl hr.2)
  | .mapL h, hl, hr => hl.imp_right (h.reads · hr)
  | .app _ h, hl, hr => .inr (h.reads (hl.resolve_left hr.1) hr.2)
  | .unitR _ h, hl, hr => h.reads hl hr
  | .unitL _ h, hl, hr => h.reads hl ⟨hr.1.2, hr.2⟩
  | .counit hfg h, hl, hr => h.reads (hl.resolve_left (not_isReader_of_adjoint hfg)) hr.2
  | .ejectR _ h, hl, hr => h.reads hl ⟨hr.2.1, hr.1, hr.2.2⟩
  | .ejectL _ h, hl, hr => h.reads hl hr

/-- Crossover (section 5.2): a left daughter that reads, combined with a right daughter that
reads nothing, yields a type that still reads, whatever the modes. Only the co-unit mode removes
a reading effect, and it takes the reader from the right daughter. -/
theorem Combine.reads {l r u : Ty} : Combine l r u → l.Reads → r.InputFree → u.Reads
  | .bin h, hl, hr => h.reads hl hr
  | .join _ h, hl, hr => (h.reads hl hr).elim .inl id
  | .lower h, hl, hr => (h.reads hl hr).resolve_left id

end

/-- An antecedent followed by a pronoun combines into a pure truth value by `C <` (section 5.5). -/
example : Combine (comp (W e) e) (comp (R e) (fn e t)) t := .bin (.counit rfl (.bin .ba))

/-- An indefinite antecedent binds into an indefinite, `J F̄ C F̃ <` (5.12). -/
example : Combine (comp S (comp (W e) e)) (comp (R e) (comp S (fn e t))) (comp S t) :=
  .join trivial (.mapL (.bin (.counit rfl (.bin (.mapR (.bin .ba))))))

/-- A pronoun before its would-be antecedent stays unresolved (5.13), (5.14). -/
example {u : Ty} (h : Combine (comp (R e) e) (comp S (comp (W e) (fn e t))) u) : u.Reads :=
  h.reads (.inl trivial) ⟨id, id, trivial, trivial⟩

example {u : Ty} (h : Combine (comp (R e) (comp S e)) (comp (C t) (comp (W e) (fn e t))) u) :
    u.Reads :=
  h.reads (.inl trivial) ⟨id, id, trivial, trivial⟩

end BumfordCharlow2026
