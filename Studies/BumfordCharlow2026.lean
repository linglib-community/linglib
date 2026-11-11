module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Control.Basic
public import Mathlib.Control.Functor
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Mode.EffectFree
public import Linglib.Semantics.Composition.Mode.Pointwise
public import Linglib.Semantics.Composition.Mode.Normal

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
are inverted: this is crossover, proved here over the book's type-driven grammar for a pronoun
whose would-be antecedent is in a right daughter that reads nothing.

Every right adjoint on types distributes over function types, and the eject modes use this.
With them the grammar derives, with no new machinery, the bind of the reader transformer, the
bind of the monad that any adjunction induces, which for storing and reading is Lean's state
monad, and, with indeterminacy in between, the state transformer over sets that dynamic
semantics is built on.

A grammar need not have every meta-mode at every effect (section 3.4). With Structured App
alone, the pointwise grammar, [a closure operator captures the effect of its
prejacent](##BumfordCharlow2026.combineWithin_pointwise_closure), and without the Unit modes
[it has no prejacent that lacks the effect](##BumfordCharlow2026.combineWithin_ne_unit_closure).
Hamblin's grammar is the pointwise grammar of indeterminacy, and [its derivation of a multiple
question](##BumfordCharlow2026.values_whichDogChasedWhichCat) is application on sets.

A focused phrase evokes alternatives to its value, and an operator such as *only* associates
with that effect as existential closure does with indeterminacy: it captures the alternatives of
its prejacent, or [is given a prejacent with none](##BumfordCharlow2026.eval_unitR_only_iff).

## Main definitions

* `mapL`, `mapR`, `structuredApp`, `joinMode`: the map, structured application and join modes
* `Output`, `outputInput`: the storing effect `W` and the adjunction `W ⊣ R`
* `counitMode`, `eject`, `ejectL`, `ejectR`: the modes an adjunction adds
* `Reads`, `InputFree`: a type still requests a datum, or reads nothing anywhere

## Implementation notes

The storing effect `Output ι α = α × ι` is a functor and not mathlib's `WriterT`, whose functor
comes only with a monad over a monoid of logs. A single stored referent cannot be merged with
another, which is the book's reason that this `W` is not a monad (section 5.3.4). The
supplement effect, whose log is a monoid, is `Core/Control/Monad/Writer.lean`.

The modes act on Lean's type constructors; an adjunction is mathlib's `Adjunction` between the
corresponding functors `ofTypeFunctor Ω ⊣ ofTypeFunctor Γ`, so the unit, co-unit and induced
monad are mathlib's. The type-driven grammar is the library's `Interpreter.Mode` over application
and predicate modification. The book's final `combine` (Appendix B) is
`Interpreter.Ty.combineWith` with Join and Lower applied once to each result, and the
interpreters of its chapters 2 to 4 are that search kept to the meta-modes the chapter has. Each
list the book prints in full is checked here, and of the lists it abridges, the mode it singles
out. The library's `Interpreter.Ty.combine` stacks Join and Lower and so lists more modes: [one
that joins twice](##BumfordCharlow2026.combine_join_twice), and for two quantifiers [a Lower on
each Join](##BumfordCharlow2026.length_combine_quantifiers). The base sort is `e`.

The Element is forthcoming; equation, section and appendix locators are to the arXiv version of
April 2025.

## TODO

* Islands (section 5.4): the book keeps at an island the modes whose result is `Evaluated`,
  which [leaves a quantified clause its closed reading](##BumfordCharlow2026.combine_island). No
  tree here marks a category as an island.
* The modes over Lean's classes, `mapL`, `counitMode` and the rest, are not yet shown to be the
  meanings `Interpreter.Mode.eval` gives the grammar's modes at each effect.

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

/-- Map Left (2.17a): map the combinator over an effectful left daughter. -/
def mapL (star : σ → τ → ω) (e₁ : F σ) (e₂ : τ) : F ω := (fun a => star a e₂) <$> e₁

/-- Map Right (2.17b): map the combinator over an effectful right daughter. -/
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

/-- Join over Map Left of backward application is bind (after (4.22)). -/
theorem joinMode_mapL_ba (m : M α) (k : α → M β) : joinMode (mapL ba) m k = m >>= k :=
  bind_map_left _ _ _

/-- Join over Map Right of forward application is bind with its arguments flipped, the book's
`(=>>)` (after (4.22)). -/
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

A pronoun reads a referent from its context (5.1a), a computation of type `R α = ι → α`, and an
antecedent stores its referent alongside its value (5.1b), one of type `W α = α × ι`. Functions
out of `W α` are functions into `R β` by currying (5.3), which makes `W` left adjoint to `R`. -/

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

/-- Every adjunction gives rise to a monad through the grammar (section 5.3.4): Map Left over
Eject Right over the Co-unit of backward application is the bind of the monad `Γ Ω` the
adjunction induces. -/
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

/-- The state monad is the monad of `W ⊣ R`, and its bind is Map Left over Eject Right over the
Co-unit of backward application (5.37), (5.38). -/
theorem mapL_ejectR_counitMode_outputInput (m : StateM ι α) (k : α → StateM ι β) :
    mapL (F := ReaderM ι) (ejectR (outputInput ι) (counitMode (outputInput ι) ba)) m k =
      m >>= k := rfl

/-- With a monad in between, the same mode with a Join and a second Map Left around the
ejection is the bind of the state transformer (5.39). -/
theorem mapL_joinMode_mapL_ejectR_counitMode {M : Type u → Type u} [Monad M] [LawfulMonad M]
    (m : StateT ι M α) (k : α → StateT ι M β) :
    mapL (F := ReaderM ι)
      (joinMode (mapL (ejectR (outputInput ι) (counitMode (outputInput ι) ba)))) m k =
      m >>= k := by
  funext s
  exact bind_map_left
    (fun p : Output ι α => ejectR (outputInput ι) (counitMode (outputInput ι) ba) p k) (m s) id

/-- Eject Left over Structured App over the Join of Map Right of forward application is the
bind of the reader transformer (5.28), (5.29). -/
theorem ejectL_structuredApp_joinMode_mapR {M : Type u → Type u} [Monad M] [LawfulMonad M]
    (m : ReaderT ι M α) (k : α → ReaderT ι M β) :
    ejectL (outputInput ι) (structuredApp (F := ReaderM ι) (joinMode (mapR fa))) k m =
      m >>= k := by
  funext s
  exact bind_map_left (fun b => k b s) (m s) id

/-! ### The type-driven grammar

Appendix B implements the grammar as a function from the types of two daughters to the modes
that combine them and the types they yield, `combine` below. -/

open Interpreter

variable {B : Type}

/-- The reading effects. -/
def IsReader : Eff B → Prop
  | .R _ => True
  | _ => False

/-- The type still requests a datum: a reading effect at a strictly positive position. -/
def Reads : Ty B → Prop
  | .fn _ b => Reads b
  | .comp f a => IsReader f ∨ Reads a
  | _ => False

/-- No reading effect anywhere in the type. -/
def InputFree : Ty B → Prop
  | .fn a b => InputFree a ∧ InputFree b
  | .comp f a => ¬ IsReader f ∧ InputFree a
  | _ => True

theorem InputFree.not_reads : ∀ {a : Ty B}, InputFree a → ¬ Reads a
  | .fn _ b, h => not_reads (a := b) h.2
  | .comp _ a, h => fun h' ↦ h'.elim h.1 (not_reads (a := a) h.2)
  | .t, _ => id
  | .base _, _ => id

/-- The basic modes of the book's interpreter (Appendix B): forward and backward application and
predicate modification. -/
abbrev baseGrammar (B : Type) : ManySorted.Language (Ty B) := application.sum predicateModification

theorem baseGrammar_reads :
    ∀ {l r u : Ty B}, (baseGrammar B).Binary l r u → Reads l → InputFree r → Reads u
  | _, _, _, .inl .fa, hl, _ => hl
  | _, _, _, .inl .ba, hl, hr => absurd hl hr.1.not_reads
  | _, _, _, .inr .pm, hl, _ => hl

/-- Application and predicate modification keep to the types without effects. -/
theorem baseGrammar_effectFree : (baseGrammar B).EffectFree where
  unary r := nomatch r
  binary := @fun
    | _, _, _, .inl .fa, hl, _ => hl.2
    | _, _, _, .inl .ba, _, hr => hr.2
    | _, _, _, .inr .pm, hl, _ => hl

/-- Before any effect the effect-driven interpreter is the deterministic one it starts from:
over words with one item each, of types without effects, a tree has at most one value,
although interpretation is relational once a word has an effect. -/
theorem length_values_effectDriven_baseGrammar_le_one [DecidableEq B] {D : B → Type}
    {C Lx : Type} {W : Ty B → Type} (ρ : ∀ {a : Ty B}, W a → a.Dom D)
    {lex : Lx ⊕ ℕ → List (Σ a, W a)} (hlex : ∀ x, ∀ p ∈ lex x, p.1.EffectFree)
    (h₁ : ∀ x, (lex x).length ≤ 1) (t : PhraseStructure.Tree C Lx) :
    (t.values (effectDriven (baseGrammar B)) effectGrammar.structure ρ lex).length ≤ 1 := by
  rw [PhraseStructure.Tree.values_effectDriven_of_effectFree baseGrammar_effectFree ρ hlex]
  exact PhraseStructure.Tree.length_values_le_one (fun _ _ ↦ by simp [typeDriven])
    (fun l r ↦ length_binaryRules_application_sum_predicateModification_le_one l r) h₁ t

/-- Crossover (section 5.2): a left daughter that reads, combined with a right daughter that
reads nothing, yields a type that still reads, whatever the modes. Only the co-unit mode removes
a reading effect, and it takes the reader from the right daughter. -/
theorem Mode.reads {Rule : Ty B → Ty B → Ty B → Type}
    (hbasic : ∀ {l r u : Ty B}, Rule l r u → Reads l → InputFree r → Reads u) :
    ∀ {l r u : Ty B}, Mode Rule l r u → Reads l → InputFree r → Reads u
  | _, _, _, .basic b, hl, hr => hbasic b hl hr
  | _, _, _, .mapR m, hl, hr => .inr (Mode.reads hbasic m hl hr.2)
  | _, _, _, .mapL m, hl, hr => hl.imp_right (Mode.reads hbasic m · hr)
  | _, _, _, .ap _ m, hl, hr => .inr (Mode.reads hbasic m (hl.resolve_left hr.1) hr.2)
  | _, _, _, .unitR _ m, hl, hr => Mode.reads hbasic m hl hr
  | _, _, _, .unitL _ m, hl, hr => Mode.reads hbasic m hl ⟨hr.1.2, hr.2⟩
  | _, _, _, .counit _, _, hr => absurd trivial hr.1
  | _, _, _, .ejectR _, _, hr => absurd trivial hr.2.1
  | _, _, _, .ejectL m, hl, hr => Mode.reads hbasic m hl hr
  | _, _, _, .join _ m, hl, hr => (Mode.reads hbasic m hl hr).elim .inl id
  | _, _, _, .lower m, hl, hr => (Mode.reads hbasic m hl hr).resolve_left id

/-- The base sort of the book's interpreter. -/
abbrev e : Ty Unit := .base ()

/-- An antecedent followed by a pronoun combines into a pure truth value by `C <`
(section 5.5). -/
example : Mode (baseGrammar Unit).Binary (.comp (.W e) e) (.comp (.R e) (e ⇒ .t)) .t :=
  .counit (.basic (.inl .ba))

/-- An indefinite antecedent binds into an indefinite, by Join over Map Left over the Co-unit of
Map Right of backward application (5.12). -/
example : Mode (baseGrammar Unit).Binary (.comp .S (.comp (.W e) e))
    (.comp (.R e) (.comp .S (e ⇒ .t))) (.comp .S .t) :=
  .join trivial (.mapL (.counit (.mapR (.basic (.inl .ba)))))

/-- A pronoun before its would-be antecedent stays unresolved (5.13), (5.14). -/
example {u : Ty Unit}
    (m : Mode (baseGrammar Unit).Binary (.comp (.R e) e) (.comp .S (.comp (.W e) (e ⇒ .t))) u) :
    Reads u :=
  Mode.reads baseGrammar_reads m (.inl trivial) ⟨id, id, trivial, trivial⟩

example {u : Ty Unit}
    (m : Mode (baseGrammar Unit).Binary (.comp (.R e) (.comp .S e))
      (.comp (.C .t) (.comp (.W e) (e ⇒ .t))) u) :
    Reads u :=
  Mode.reads baseGrammar_reads m (.inl trivial) ⟨id, id, trivial, trivial⟩

/-- A type is evaluated when no continuation in it is still to be closed (section 5.5). -/
def Evaluated : Ty B → Prop
  | .comp (.C _) _ => False
  | .comp .S a | .comp (.R _) a | .comp (.W _) a | .comp .M a | .comp .F a => Evaluated a
  | .fn _ b => Evaluated b
  | .t | .base _ => True

instance decidableEvaluated : (a : Ty B) → Decidable (Evaluated a)
  | .comp (.C _) _ => isFalse id
  | .comp .S a | .comp (.R _) a | .comp (.W _) a | .comp .M a | .comp .F a =>
    decidableEvaluated a
  | .fn _ b => decidableEvaluated b
  | .t | .base _ => isTrue trivial

/-! ### The interpreter

The book's `combine` on the type combinations the book runs it on, with the modes named as the
book prints them. -/

/-- The names of the basic modes. -/
inductive Name
  | FA | BA | PM
  deriving DecidableEq, Repr

/-- The name of a basic mode. -/
def Name.of : {l r u : Ty Unit} → (baseGrammar Unit).Binary l r u → Name
  | _, _, _, .inl .fa => .FA
  | _, _, _, .inl .ba => .BA
  | _, _, _, .inr .pm => .PM

/-- The shape of a mode, forgetting its types. -/
inductive Shape (β : Type) where
  | basic (b : β)
  | mapR (m : Shape β)
  | mapL (m : Shape β)
  | ap (m : Shape β)
  | unitR (m : Shape β)
  | unitL (m : Shape β)
  | counit (m : Shape β)
  | ejectR (m : Shape β)
  | ejectL (m : Shape β)
  | join (m : Shape β)
  | lower (m : Shape β)
  deriving DecidableEq, Repr

/-- The shape of a mode, given the names of the basic modes. -/
def shape {B β : Type} {Rule : Ty B → Ty B → Ty B → Type}
    (name : ∀ {l r u : Ty B}, Rule l r u → β) : {l r u : Ty B} → Mode Rule l r u → Shape β
  | _, _, _, .basic b => .basic (name b)
  | _, _, _, .mapR m => .mapR (shape name m)
  | _, _, _, .mapL m => .mapL (shape name m)
  | _, _, _, .ap _ m => .ap (shape name m)
  | _, _, _, .unitR _ m => .unitR (shape name m)
  | _, _, _, .unitL _ m => .unitL (shape name m)
  | _, _, _, .counit m => .counit (shape name m)
  | _, _, _, .ejectR m => .ejectR (shape name m)
  | _, _, _, .ejectL m => .ejectL (shape name m)
  | _, _, _, .join _ m => .join (shape name m)
  | _, _, _, .lower m => .lower (shape name m)

/-- The modes the book's `combine` finds for two types, in its order. -/
def modes (l r : Ty Unit) : List (Sigma (Mode (baseGrammar Unit).Binary l r)) :=
  Ty.combineWith (fun _ _ ↦ True)
    (ManySorted.Language.LocallyFinite.binaryRules (L := baseGrammar Unit))
    (fun p ↦ p :: (Mode.joins p ++ Mode.lowers p)) l r

/-- The interpreter's output for two types: the modes that combine them, in the book's order,
each with the type it yields. -/
def combine (l r : Ty Unit) : List (Shape Name × Ty Unit) :=
  (modes l r).map fun p ↦ (shape Name.of p.2, p.1)

/-- The interpreter's output in a grammar with the inventory `inv` of meta-modes
(section 3.4). -/
def combineWithin (inv : MetaMode → Eff Unit → Prop) [∀ k f, Decidable (inv k f)]
    (l r : Ty Unit) : List (Shape Name × Ty Unit) :=
  ((modes l r).filter fun p ↦ p.2.Within inv).map fun p ↦ (shape Name.of p.2, p.1)

/-- The meta-modes of the grammar of Figure 4: the maps. -/
abbrev functorial : MetaMode → Eff Unit → Prop := fun k _ ↦ k = .map

/-- The meta-modes of the grammar of Figure 7: the maps, Structured App and the Unit modes. -/
abbrev applicative : MetaMode → Eff Unit → Prop := fun k _ ↦ k = .map ∨ k = .ap ∨ k = .unit

/-- The meta-modes of the grammar of Figure 8: those of Figure 7 and Join. -/
abbrev monadic : MetaMode → Eff Unit → Prop :=
  fun k _ ↦ k = .map ∨ k = .ap ∨ k = .unit ∨ k = .join

section Interpreter

local notation "FA" => Shape.basic Name.FA
local notation "BA" => Shape.basic Name.BA
local notation "S" => Ty.comp Eff.S
local notation "R" => Ty.comp (Eff.R e)
local notation "W" => Ty.comp (Eff.W e)
local notation "C" => Ty.comp (Eff.C Ty.t)
local notation "F" => Ty.comp Eff.F
local notation "T" => (Ty.t : Ty Unit)

-- section 3.6: a closure operator and its prejacent
theorem combine_closure : combine (S T ⇒ T) (S T) =
    [(FA, T), (.mapR (.unitR FA), S T), (.unitR (.mapR FA), S T)] := by decide

-- section 5.5: storing before reading binds
theorem combine_store_read : combine (W e) (R (e ⇒ T)) =
    [(.mapR (.mapL BA), R (W T)), (.mapL (.mapR BA), W (R T)), (.counit BA, T)] := by decide

-- section 5.5: reading before storing does not
theorem combine_read_store : combine (R e) (W (e ⇒ T)) =
    [(.mapR (.mapL BA), W (R T)), (.mapL (.mapR BA), R (W T))] := by decide

-- section 5.5: lowering
theorem combine_lower : combine (T ⇒ T) (C T) = [(.mapR FA, C T), (.lower (.mapR FA), T)] := by
  decide

/-- At an island the book keeps the modes whose result is evaluated: of the two ways a quantifier
and its predicate combine, the one that lowers it. -/
theorem combine_island :
    (combine (C e) (e ⇒ T)).filter (fun p ↦ Evaluated p.2) = [(.lower (.mapL BA), T)] := by decide

/-- The grammar has a mode that joins twice, flattening three layers of indeterminacy to one. -/
example : Mode (baseGrammar Unit).Binary (e ⇒ S (S (S T))) e (S T) :=
  .join trivial (.join trivial (.basic (.inl .fa)))

/-- The book's `combine` applies Join once to the result of application, and lists the modes that
give three layers and two. -/
theorem combine_join_twice :
    combine (e ⇒ S (S (S T))) e = [(FA, S (S (S T))), (.join FA, S (S T))] := by decide

/-- The search that stacks Join and Lower finds it. -/
example : (⟨S T, .join trivial (.join trivial (.basic (.inl .fa)))⟩ :
      Σ u, Mode (baseGrammar Unit).Binary (e ⇒ S (S (S T))) e u) ∈
    Ty.combine (ManySorted.Language.LocallyFinite.binaryRules (L := baseGrammar Unit)) _ _ :=
  Ty.mem_combine (find := ManySorted.Language.LocallyFinite.binaryRules (L := baseGrammar Unit))
    (fun b ↦ ManySorted.Language.LocallyFinite.mem_symbols b) _

-- section 5.3.4: the bind of the state monad is among the modes
theorem mem_combine_state :
    (.mapL (.ejectR (.counit BA)), R (W T)) ∈ combine (R (W e)) (e ⇒ R (W T)) := by decide

-- section 5.3.4: and so is the bind of dynamic state
theorem mem_combine_dynamic : (.mapL (.join (.mapL (.ejectR (.counit BA)))), R (S (W T))) ∈
    combine (R (S (W e))) (e ⇒ R (S (W T))) := by decide

-- section 5.5: an indefinite binding into an indefinite
theorem mem_combine_indefinites :
    (.join (.mapL (.counit (.mapR BA))), S T) ∈ combine (S (W e)) (R (S (e ⇒ T))) := by decide

-- two indefinites, neither moved, under the final `combine`: the alternatives of each mapped
-- inside the other's, each of these joined, and Structured App
theorem combine_alternatives : combine (S e) (S (e ⇒ T)) =
    [(.mapR (.mapL BA), S (S T)), (.join (.mapR (.mapL BA)), S T), (.mapL (.mapR BA), S (S T)),
      (.join (.mapL (.mapR BA)), S T), (.ap BA, S T)] := by decide

-- section 3.3: an operator that associates with focus and its prejacent, which it captures or,
-- given a pure one, lets through
theorem combine_focus_closure : combine (F T ⇒ T) (F T) =
    [(FA, T), (.mapR (.unitR FA), F T), (.unitR (.mapR FA), F T)] := by decide

-- section 2.5: the four outputs of the chapter's interpreter, which has the maps
theorem combineWithin_functorial_subject : combineWithin functorial (R e) (e ⇒ T) =
    [(.mapL BA, R T)] := by decide

theorem combineWithin_functorial_object : combineWithin functorial e (R (e ⇒ T)) =
    [(.mapR BA, R T)] := by decide

theorem combineWithin_functorial_pronouns : combineWithin functorial (R e) (R (e ⇒ T)) =
    [(.mapR (.mapL BA), R (R T)), (.mapL (.mapR BA), R (R T))] := by decide

theorem combineWithin_functorial_wh : combineWithin functorial (S e) (R (e ⇒ T)) =
    [(.mapR (.mapL BA), R (S T)), (.mapL (.mapR BA), S (R T))] := by decide

-- section 3.6: two indefinites under the chapter's interpreter, which adds Structured App and
-- the Unit modes
theorem combineWithin_applicative_alternatives : combineWithin applicative (S e) (S (e ⇒ T)) =
    [(.mapR (.mapL BA), S (S T)), (.mapL (.mapR BA), S (S T)), (.ap BA, S T)] := by decide

-- section 4.4: an indefinite and a function into indeterminacy, and two quantifiers, under the
-- chapter's interpreter, which adds Join
theorem combineWithin_monadic_kleisli : combineWithin monadic (S e) (e ⇒ S T) =
    [(.mapL BA, S (S T)), (.join (.mapL BA), S T)] := by decide

theorem combineWithin_monadic_quantifiers : combineWithin monadic (C e) (C (e ⇒ T)) =
    [(.mapR (.mapL BA), C (C T)), (.join (.mapR (.mapL BA)), C T),
      (.mapL (.mapR BA), C (C T)), (.join (.mapL (.mapR BA)), C T), (.ap BA, C T)] := by decide

/-- For two quantifiers the library's search lists twelve modes and the book's final `combine`
ten: the two more are a Lower on each Join of the maps. -/
theorem length_combine_quantifiers :
    (Ty.combine (ManySorted.Language.LocallyFinite.binaryRules (L := baseGrammar Unit))
      (C e) (C (e ⇒ T))).length = 12 ∧ (combine (C e) (C (e ⇒ T))).length = 10 := by decide

-- section 3.4: with Structured App alone, the pointwise grammars of Figures 5 and 6, two
-- indefinites combine in one way
theorem combineWithin_pointwise :
    combineWithin (MetaMode.pointwise fun _ ↦ True) (S e) (S (e ⇒ T)) = [(.ap BA, S T)] := by
  decide

-- section 3.4: and a closure operator captures the effect of its prejacent
theorem combineWithin_pointwise_closure :
    combineWithin (MetaMode.pointwise fun _ ↦ True) (S T ⇒ T) (S T) = [(FA, T)] := by decide

-- section 3.4: with the maps alone a closure operator associates with one layer, the inner
theorem combineWithin_map_closure : combineWithin (fun k _ ↦ k = .map) (S T ⇒ T) (S (S T)) =
    [(.mapR FA, S T)] := by decide

-- section 3.4: without the Unit modes a closure operator has no prejacent without the effect
theorem combineWithin_ne_unit_closure : combineWithin (fun k _ ↦ k ≠ .unit) (S T ⇒ T) T = [] ∧
    combine (S T ⇒ T) T = [(.unitR FA, T)] := by decide

-- two focused daughters: as with two indefinites, Structured App evokes their alternatives at once
theorem combine_foci : combine (F e) (F (e ⇒ T)) =
    [(.mapR (.mapL BA), F (F T)), (.join (.mapR (.mapL BA)), F T), (.mapL (.mapR BA), F (F T)),
      (.join (.mapL (.mapR BA)), F T), (.ap BA, F T)] := by decide

/-- The normal forms of the modes the book's `combine` finds for two types with a result of type
`u`. -/
def normalForms (l r u : Ty Unit) : List (Shape Name) :=
  ((modes l r).filter fun p ↦ p.1 = u).map fun p ↦ shape Name.of p.2.normalize

-- two indefinites: the three modes that give a set of truth values have one normal form, and so
-- one meaning
theorem normalForms_alternatives :
    normalForms (S e) (S (e ⇒ T)) (S T) = [.ap BA, .ap BA, .ap BA] := by decide

-- and so do those for two foci
theorem normalForms_foci : normalForms (F e) (F (e ⇒ T)) (F T) = [.ap BA, .ap BA, .ap BA] := by
  decide

-- two quantifiers: the Join that maps over the object last is its own normal form, the inverse
-- scope of (4.45b), beside Structured App and the two modes that lower one quantifier first
theorem normalForms_quantifiers : normalForms (C e) (C (e ⇒ T)) (C T) =
    [.join (.mapR (.mapL BA)), .mapR (.lower (.mapL BA)), .ap BA, .mapL (.lower (.mapR BA)),
      .ap BA] := by decide

end Interpreter

/-! ### A pointwise grammar

Hamblin's grammar (Figure 6) is the grammar with Structured App alone at indeterminacy, every
word a set. Its derivation of *which dog chased which cat* (3.2) puts the words together by
application in the structure on sets of values. -/

section Hamblin

open PhraseStructure

/-- The words of (3.2). -/
inductive Word
  | whichDog | chased | whichCat
  deriving DecidableEq

/-- The words by the type of their results. -/
inductive Item : Ty Unit → Type
  | whichDog : Item e
  | chased : Item (e ⇒ e ⇒ .t)
  | whichCat : Item e

/-- The words by type in Hamblin's grammar, where each is a set. -/
inductive SetItem : Ty Unit → Type
  | whichDog : SetItem (.comp .S e)
  | chased : SetItem (.comp .S (e ⇒ e ⇒ .t))
  | whichCat : SetItem (.comp .S e)

/-- The result of each word. -/
def results : Word ⊕ ℕ → List (Sigma Item)
  | .inl .whichDog => [⟨_, .whichDog⟩]
  | .inl .chased => [⟨_, .chased⟩]
  | .inl .whichCat => [⟨_, .whichCat⟩]
  | .inr _ => []

/-- Hamblin's lexicon. -/
def sets : Word ⊕ ℕ → List (Sigma SetItem)
  | .inl .whichDog => [⟨_, .whichDog⟩]
  | .inl .chased => [⟨_, .chased⟩]
  | .inl .whichCat => [⟨_, .whichCat⟩]
  | .inr _ => []

variable {E : Type} (dog cat : E → Prop) (chase : E → E → Prop)

local notation "D" => fun _ : Unit ↦ E

/-- The set each word denotes: a *wh*-phrase its restrictor, and the verb its one value. -/
def Item.val : {a : Ty Unit} → Item a → (Ty.comp .S a).Dom D
  | _, .whichDog => {d | dog d}
  | _, .chased => {chase}
  | _, .whichCat => {c | cat c}

/-- The same sets, of the words typed as Hamblin's grammar types them. -/
def SetItem.val : {a : Ty Unit} → SetItem a → a.Dom D
  | _, .whichDog => {d | dog d}
  | _, .chased => {chase}
  | _, .whichCat => {c | cat c}

/-- Hamblin's grammar: application, pointwise at indeterminacy. -/
def hamblin : Interpreter (effectGrammar (application (B := Unit))) ℕ :=
  effectDrivenWithin (MetaMode.pointwise (· = .S)) application

/-- (3.2): *which dog chased which cat*. -/
def whichDogChasedWhichCat : Tree Unit Word :=
  .bin (.leaf .whichDog) (.bin (.leaf .chased) (.leaf .whichCat))

private theorem binary_fa : hamblin.binary (e ⇒ e ⇒ .t) e = [⟨e ⇒ .t, .basic .fa⟩] := rfl

private theorem binary_ba : hamblin.binary e (e ⇒ .t) = [⟨.t, .basic .ba⟩] := rfl

/-- (3.2): the sentence denotes the set of propositions that a dog chased a cat, one for each dog
and each cat, by Structured App at each node. -/
theorem values_whichDogChasedWhichCat :
    whichDogChasedWhichCat.values hamblin effectGrammar.structure
        (fun {_} ↦ SetItem.val dog cat chase) sets =
      [⟨.comp .S .t, {p | ∃ c, cat c ∧ ∃ d, dog d ∧ p = chase c d}⟩] := by
  have h := Tree.values_effectDrivenWithin_pointwise (P := (· = .S)) (f := .S)
    (G := application (B := Unit)) rfl trivial (fun _ ↦ rfl) (fun b ↦ by cases b)
    (ρ := fun {_} ↦ Item.val dog cat chase) (ρ' := fun {_} ↦ SetItem.val dog cat chase)
    (lex := results) (lex' := sets) (fun x ↦ by rcases x with (_ | _ | _) | _ <;> rfl)
    whichDogChasedWhichCat
  refine h.trans ?_
  change (whichDogChasedWhichCat.values hamblin _ _ results).map _ = _
  simp only [whichDogChasedWhichCat, Tree.values_phrase_binary, Tree.values_terminal, results,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    binary_fa, binary_ba]
  refine congrArg (fun x ↦ [(⟨.comp .S .t, x⟩ : Sigma (Ty.Dom D))]) (Set.ext fun p ↦ ?_)
  change p ∈ Set.seq (_ '' {d | dog d}) (Set.seq (_ '' {chase}) {c | cat c}) ↔ _
  simp only [Set.mem_seq_iff, Set.mem_image, Set.mem_singleton_iff, Set.mem_ofPred_eq,
    exists_exists_and_eq_and, exists_eq_left]
  exact ⟨fun ⟨d, hd, _, ⟨_, rfl, c, hc, rfl⟩, h⟩ ↦ ⟨c, hc, d, hd, h.symm⟩,
    fun ⟨c, hc, d, hd, h⟩ ↦ ⟨d, hd, _, ⟨_, rfl, c, hc, rfl⟩, h.symm⟩⟩

end Hamblin

/-! ### Scope

Two quantifiers combine by Structured App, in their surface order, or by the two orders of the
maps followed by Join, of which the one that maps over the right daughter last gives the object
wide scope (4.45). -/

section Scope

variable {E : Type} (admires : E → E → Prop)

local notation "D" => fun _ : Unit ↦ E
local notation "C" => Ty.comp (Eff.C Ty.t)

/-- *Admires everyone*: application mapped over the object. -/
def admiresEveryone : (C (e ⇒ .t) : Ty Unit).Dom D :=
  (Mode.mapR (.basic (.inl .fa)) :
    Mode (baseGrammar Unit).Binary (e ⇒ e ⇒ .t) (C e) (C (e ⇒ .t))).eval D admires fun c ↦ ∀ x, c x

/-- The surface order: someone admires everyone. -/
theorem eval_ap_iff :
    ((Mode.ap trivial (.basic (.inl .ba)) :
      Mode (baseGrammar Unit).Binary (C e) (C (e ⇒ .t)) (C .t)).eval D
        (fun c ↦ ∃ y, c y) (admiresEveryone admires)) id ↔
      ∃ y, ∀ x, admires x y := Iff.rfl

/-- The inverse order: everyone is admired by someone. -/
theorem eval_join_mapR_mapL_iff :
    ((Mode.join trivial (.mapR (.mapL (.basic (.inl .ba)))) :
      Mode (baseGrammar Unit).Binary (C e) (C (e ⇒ .t)) (C .t)).eval D
        (fun c ↦ ∃ y, c y) (admiresEveryone admires)) id ↔ ∀ x, ∃ y, admires x y := Iff.rfl

/-- The two orders are two readings: where each of two people admires only themself, everyone
is admired by someone and no one admires everyone. -/
example :
    ((Mode.join trivial (.mapR (.mapL (.basic (.inl .ba)))) :
      Mode (baseGrammar Unit).Binary (C e) (C (e ⇒ .t)) (C .t)).eval (fun _ ↦ Bool)
        (fun c ↦ ∃ y, c y) (admiresEveryone (· = ·))) id ∧
    ¬ ((Mode.ap trivial (.basic (.inl .ba)) :
      Mode (baseGrammar Unit).Binary (C e) (C (e ⇒ .t)) (C .t)).eval (fun _ ↦ Bool)
        (fun c ↦ ∃ y, c y) (admiresEveryone (· = ·))) id :=
  ⟨fun x ↦ ⟨x, rfl⟩, fun ⟨_, hy⟩ ↦ Bool.noConfusion ((hy true).trans (hy false).symm)⟩

end Scope

/-! ### Commutative effects

At reading and at indeterminacy it does not matter to Structured App which daughter is on the
left (3.26), and so at every effect whose application is commutative. At quantification it
does: the function's quantifier takes scope over the argument's when the function is on the
left, and under it when the argument is (3.31). -/

section Commutative

variable {D : B → Type} {f : Eff B} {a b : Ty B}

-- (3.26)
theorem eval_ap_fa_eq_eval_ap_ba (hc : f.IsCommutative) (F : (Ty.comp f (a ⇒ b)).Dom D)
    (X : (Ty.comp f a).Dom D) :
    (Mode.ap hc.isApplicative (.basic (.inl .fa)) :
      Mode (baseGrammar B).Binary (.comp f (a ⇒ b)) (.comp f a) (.comp f b)).eval D F X =
    (Mode.ap hc.isApplicative (.basic (.inl .ba)) :
      Mode (baseGrammar B).Binary (.comp f a) (.comp f (a ⇒ b)) (.comp f b)).eval D X F :=
  Mode.eval_ap_comm hc _ _ (fun _ _ ↦ rfl) F X

variable {o : Ty B}

-- (3.31a)
theorem eval_ap_fa_C (F : (Ty.comp (.C o) (a ⇒ b)).Dom D) (X : (Ty.comp (.C o) a).Dom D) :
    (Mode.ap (f := .C o) trivial (.basic (.inl .fa)) :
      Mode (baseGrammar B).Binary (.comp (.C o) (a ⇒ b)) (.comp (.C o) a) (.comp (.C o) b)).eval
        D F X = fun c ↦ F fun g ↦ X fun x ↦ c (g x) := rfl

-- (3.31b)
theorem eval_ap_ba_C (X : (Ty.comp (.C o) a).Dom D) (F : (Ty.comp (.C o) (a ⇒ b)).Dom D) :
    (Mode.ap (f := .C o) trivial (.basic (.inl .ba)) :
      Mode (baseGrammar B).Binary (.comp (.C o) a) (.comp (.C o) (a ⇒ b)) (.comp (.C o) b)).eval
        D X F = fun c ↦ X fun x ↦ F fun g ↦ c (g x) := rfl

end Commutative

/-! ### Focus

A focused phrase names a value and evokes alternatives to it, and *only* associates with the
effect: it takes a proposition with its alternatives (3.15a). Given a prejacent with no focus
in it, Unit Right makes the proposition its own sole alternative, and *only* then says no more
than the prejacent does. -/

section Focus

variable {E : Type}

local notation "D" => fun _ : Unit ↦ E
local notation "F" => Ty.comp Eff.F

/-- *Only* (3.15a): of the alternatives to its prejacent, the prejacent alone is true. -/
def only : (F .t ⇒ .t : Ty Unit).Dom D := fun m ↦ {p ∈ m.alternatives | p} = {m.ordinary}

/-- *Only* over a prejacent with no focus in it is the prejacent. -/
theorem eval_unitR_only_iff (p : Prop) :
    (Mode.unitR trivial (.basic (.inl .fa)) :
      Mode (baseGrammar Unit).Binary (F .t ⇒ .t) .t .t).eval D (only (E := E)) p ↔ p := by
  change {q ∈ ({p} : Set Prop) | q} = {p} ↔ p
  refine ⟨fun h ↦ (h.ge rfl).2, fun hp ↦ Set.ext fun q ↦ ⟨And.left, fun hq ↦ ⟨hq, ?_⟩⟩⟩
  rwa [Set.mem_singleton_iff.1 hq]

end Focus

end BumfordCharlow2026
