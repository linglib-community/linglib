module

public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Mode.EffectFree
public import Linglib.Semantics.Composition.Mode.Pointwise
public import Linglib.Semantics.Composition.Interpret
public import Linglib.Semantics.Composition.Mode.Normal
public import Linglib.Semantics.Composition.MetaCombinator.Adjunction

/-!
# Bumford and Charlow 2026: effect-driven interpretation

[bumford-charlow-2026] treat pronouns, antecedents, indefinites and quantifiers as computations
with effects, and the modes of semantic combination as higher-order operations that lift a basic
combinator through the algebra of an effect: maps for functors (chapter 2), structured
application for applicatives (chapter 3), join for monads (chapter 4), and co-unit and eject for
adjunctions (chapter 5). This file proves the results of chapter 5 about those modes, over
Lean's `Functor`, `Applicative` and `Monad` classes and mathlib's adjunctions, and states the
outputs of the book's interpreter.

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

* `store`, `pronoun`: the antecedent operator and the pronoun
* `Reads`, `InputFree`: a type still requests a datum, or reads nothing anywhere
* `combine`, `combineWithin`: the book's interpreter on two types

## Implementation notes

The meta-combinators over Lean's `Functor`, `Applicative` and `Monad` classes and mathlib's
adjunctions are the library's `Interpreter.MetaCombinator`, and each mode of the type-driven
grammar means its meta-combinator. A single stored referent cannot be merged with another, which
is the book's reason that `W` is not a monad (section 5.3.4). The supplement effect, whose log is
a monoid, is `Core/Control/Monad/Writer.lean`.

The type-driven grammar is the library's `Interpreter.Mode` over application
and predicate modification. The book's final `combine` (Appendix B) is
`Interpreter.Ty.combineWith` with Join and Lower applied once to each result, and the
interpreters of its chapters 2 to 4 are that search kept to the meta-modes the chapter has. Each
list the book prints in full is checked here, and of the lists it abridges, the mode it singles
out. The first session of section 4.4 is run at an indefinite and a function from individuals
into sets of truth values, the Kleisli arrow of the text around it. The book's interpreter runs
at indeterminacy, reading, storing and continuations: the lists at alternatives, and *only* over
a prejacent without focus, are this file's. The library's `Interpreter.Ty.combine` stacks Join
and Lower and so lists more modes: [one that joins
twice](##BumfordCharlow2026.combine_join_twice), and for two quantifiers [a Lower on each
Join](##BumfordCharlow2026.length_combine_quantifiers). The base sort is `e`.

The Element is forthcoming; equation, section and appendix locators are to the arXiv version of
April 2025.

## TODO

* Islands (section 5.4): the book keeps at an island the modes whose result is `Evaluated`,
  which [leaves a quantified clause its closed reading](##BumfordCharlow2026.combine_island). No
  tree here marks a category as an island.

## References

* [bumford-charlow-2026]
* [barker-shan-2014]
-/

@[expose] public section

namespace BumfordCharlow2026

universe u v

open Interpreter.MetaCombinator

/-! ### Modes of combination

A mode of combination takes a basic combinator `(∗) : σ → τ → ω` and returns one that works when
a daughter carries an effect: Map Left and Map Right (2.17), Structured App (3.10), Join (4.22),
the Co-unit (5.8) and the ejections (5.25). They are the library's
`Interpreter.MetaCombinator`. -/

/-- The order of the maps sets the priority of the effects (2.22): mapping over the left
daughter first gives its request the outer position. -/
example {E : Type} (saw : E → E → Prop) :
    mapL (F := ReaderM E) (mapR (F := ReaderM E) ba) (fun y ↦ y) (fun x ↦ saw x) =
      fun y x ↦ saw x y := rfl

example {E : Type} (saw : E → E → Prop) :
    mapR (F := ReaderM E) (mapL (F := ReaderM E) ba) (fun y ↦ y) (fun x ↦ saw x) =
      fun x y ↦ saw x y := rfl

/-! ### Storing and reading

A pronoun reads a referent from its context (5.1a), a computation of type `R α = ι → α`, and an
antecedent stores its referent alongside its value (5.1b), one of type `W α = α × ι`. Functions
out of `W α` are functions into `R β` by currying (5.3), which makes `W` left adjoint to `R`,
with the unit and co-unit of (5.4). -/

variable {ι α β : Type u}

/-- The antecedent operator `⊲` (5.1b): an entity stores itself. -/
def store (x : ι) : Output ι ι := (x, x)

/-- The pronoun (5.1a): read the referent. -/
def pronoun : ReaderM ι ι := fun i ↦ i

/-- The co-unit of `W ⊣ R` binds a pronoun to a preceding antecedent (5.5), and the same
daughters combined by maps alone keep both effects (5.2). -/
example {E : Type} (moon spot : E → E) (obscure : E → E → Prop) (j : E) :
    counit (outputInput E) ba (mapL ba (store j) moon)
      (mapR fa obscure (mapL ba pronoun spot)) = obscure (spot j) (moon j) := rfl

example {E : Type} (moon spot : E → E) (obscure : E → E → Prop) (j : E) :
    mapL (mapR ba) (mapL ba (store j) moon) (mapR fa obscure (mapL ba pronoun spot)) =
      ((fun x ↦ obscure (spot x) (moon j), j) : Output E (ReaderM E Prop)) := rfl

/-! ### Monads from storing and reading -/

/-- The state monad is the monad of `W ⊣ R`, and its bind is Map Left over Eject Right over the
Co-unit of backward application (5.37), (5.38). -/
theorem mapL_ejectR_counit_outputInput (m : StateM ι α) (k : α → StateM ι β) :
    mapL (F := ReaderM ι) (ejectR (outputInput ι) (counit (outputInput ι) ba)) m k =
      m >>= k := rfl

/-- With a monad in between, the same mode with a Join and a second Map Left around the
ejection is the bind of the state transformer (5.39). -/
theorem mapL_join_mapL_ejectR_counit {M : Type u → Type u} [Monad M] [LawfulMonad M]
    (m : StateT ι M α) (k : α → StateT ι M β) :
    mapL (F := ReaderM ι)
      (join (mapL (ejectR (outputInput ι) (counit (outputInput ι) ba)))) m k =
      m >>= k := by
  funext s
  exact bind_map_left
    (fun p : Output ι α => ejectR (outputInput ι) (counit (outputInput ι) ba) p k) (m s) id

/-- Eject Left over Structured App over the Join of Map Right of forward application is the
bind of the reader transformer (5.28), (5.29). -/
theorem ejectL_ap_join_mapR {M : Type u → Type u} [Monad M] [LawfulMonad M]
    (m : ReaderT ι M α) (k : α → ReaderT ι M β) :
    ejectL (outputInput ι) (ap (F := ReaderM ι) (join (mapR fa))) k m =
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
  | _, _, _, .ap m _, hl, hr => .inr (Mode.reads hbasic m (hl.resolve_left hr.1) hr.2)
  | _, _, _, .unitR m _, hl, hr => Mode.reads hbasic m hl hr
  | _, _, _, .unitL m _, hl, hr => Mode.reads hbasic m hl ⟨hr.1.2, hr.2⟩
  | _, _, _, .counit _, _, hr => absurd trivial hr.1
  | _, _, _, .ejectR _, _, hr => absurd trivial hr.2.1
  | _, _, _, .ejectL m, hl, hr => Mode.reads hbasic m hl hr
  | _, _, _, .join m _, hl, hr => (Mode.reads hbasic m hl hr).elim .inl id
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
  .join (.mapL (.counit (.mapR (.basic (.inl .ba)))))

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
  | _, _, _, .ap m _ => .ap (shape name m)
  | _, _, _, .unitR m _ => .unitR (shape name m)
  | _, _, _, .unitL m _ => .unitL (shape name m)
  | _, _, _, .counit m => .counit (shape name m)
  | _, _, _, .ejectR m => .ejectR (shape name m)
  | _, _, _, .ejectL m => .ejectL (shape name m)
  | _, _, _, .join m _ => .join (shape name m)
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
def combineWithin (inv : MetaMode → Eff Unit → Prop) [DecidableRel inv]
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
  .join (.join (.basic (.inl .fa)))

/-- The book's `combine` applies Join once to the result of application, and lists the modes that
give three layers and two. -/
theorem combine_join_twice :
    combine (e ⇒ S (S (S T))) e = [(FA, S (S (S T))), (.join FA, S (S T))] := by decide

/-- The search that stacks Join and Lower finds it. -/
example : (⟨S T, .join (.join (.basic (.inl .fa)))⟩ :
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

-- an operator that associates with focus (3.15a) and its prejacent, which it captures or, given
-- a pure one, lets through: the list for a closure operator, at alternatives
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

-- two quantifiers: the Join with the object's map outermost is its own normal form, the inverse
-- scope of (4.45b), beside Structured App and the two modes that lower one quantifier inside
theorem normalForms_quantifiers : normalForms (C e) (C (e ⇒ T)) (C T) =
    [.join (.mapR (.mapL BA)), .mapR (.lower (.mapL BA)), .ap BA, .mapL (.lower (.mapR BA)),
      .ap BA] := by decide

end Interpreter

/-! ### The pointwise grammars

The environment-sensitive grammar (Figure 5) is the grammar with Structured App alone at reading
an environment, every word a function of the environment and a pronoun the coordinate of its
index. Its derivation of *she called her* (3.2) evaluates the words at one environment, and
Heim and Kratzer's rules give the sentence the same function of the assignment. Hamblin's
grammar (Figure 6) is the grammar with Structured App alone at indeterminacy, every word a set.
Its derivation of *which dog chased which cat* (3.2) puts the words together by application in
the structure on sets of values. -/

section Reading

open PhraseStructure

/-- The base sorts of the environment-sensitive grammar: individuals, and the sequences of
individuals that are environments. -/
inductive EnvSort
  | ind | env
  deriving DecidableEq

/-- The domains of the sorts over individuals `E`: an environment is a sequence of them. -/
abbrev EnvSort.Dom (E : Type) : EnvSort → Type
  | .ind => E
  | .env => ℕ → E

/-- The type of individuals. -/
abbrev ind : Ty EnvSort := .base .ind

/-- The type of environments. -/
abbrev env : Ty EnvSort := .base .env

/-- The verb of (3.2). Its pronouns are the indexed leaves of the tree. -/
inductive Verb
  | called
  deriving DecidableEq

/-- The verb and the pronouns by the type of their results. -/
inductive EnvItem : Ty EnvSort → Type
  | called : EnvItem (ind ⇒ ind ⇒ .t)
  | pro (n : ℕ) : EnvItem ind

/-- The verb and the pronouns by type in the environment-sensitive grammar, where each reads an
environment. -/
inductive ReaderItem : Ty EnvSort → Type
  | called : ReaderItem (.comp (.R env) (ind ⇒ ind ⇒ .t))
  | pro (n : ℕ) : ReaderItem (.comp (.R env) ind)

/-- The result of the verb and of the pronoun of each index. -/
def envResults : Verb ⊕ ℕ → List (Sigma EnvItem)
  | .inl .called => [⟨_, .called⟩]
  | .inr n => [⟨_, .pro n⟩]

/-- The lexicon of the environment-sensitive grammar. -/
def readers : Verb ⊕ ℕ → List (Sigma ReaderItem)
  | .inl .called => [⟨_, .called⟩]
  | .inr n => [⟨_, .pro n⟩]

variable {E : Type} (call : E → E → Prop)

local notation "D" => EnvSort.Dom E

/-- The function of the environment each item denotes: the verb ignores it, and a pronoun
returns the coordinate of its index. -/
def EnvItem.val : {a : Ty EnvSort} → EnvItem a → (Ty.comp (.R env) a).Dom D
  | _, .called => fun _ ↦ call
  | _, .pro n => fun i ↦ i n

/-- The same functions, of the items typed as the environment-sensitive grammar types them. -/
def ReaderItem.val : {a : Ty EnvSort} → ReaderItem a → a.Dom D
  | _, .called => fun _ ↦ call
  | _, .pro n => fun i ↦ i n

/-- The environment-sensitive grammar, application pointwise at reading an environment. -/
def environmentSensitive : Interpreter (effectGrammar (application (B := EnvSort))) ℕ :=
  effectDrivenWithin (MetaMode.pointwise (· = .R env)) application

/-- (3.2): *she called her*, the subject of index 0 and the object of index 1. -/
def sheCalledHer : Tree Unit Verb := .bin (.tr 0) (.bin (.leaf .called) (.tr 1))

private theorem environmentSensitive_fa :
    environmentSensitive.binary (ind ⇒ ind ⇒ .t) ind = [⟨ind ⇒ .t, .basic .fa⟩] := rfl

private theorem environmentSensitive_ba :
    environmentSensitive.binary ind (ind ⇒ .t) = [⟨.t, .basic .ba⟩] := rfl

/-- (3.2): *she called her* denotes the function of the environment `i` that is `call i₁ i₀`. -/
theorem values_sheCalledHer :
    sheCalledHer.values environmentSensitive effectGrammar.structure
        (fun {_} ↦ ReaderItem.val call) readers =
      [⟨.comp (.R env) .t, fun i ↦ call (i 1) (i 0)⟩] := by
  have h := Tree.values_effectDrivenWithin_pointwise (P := (· = .R env)) (f := .R env)
    (G := application (B := EnvSort)) rfl
    (ρ := fun {_} ↦ EnvItem.val call) (ρ' := fun {_} ↦ ReaderItem.val call)
    (lex := envResults) (lex' := readers) (fun x ↦ by rcases x with _ | _ <;> rfl)
    sheCalledHer
  refine h.trans ?_
  change (sheCalledHer.values environmentSensitive _ _ envResults).map _ = _
  simp only [sheCalledHer, Tree.values_phrase_binary, Tree.values_terminal, Tree.values_trace,
    envResults, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, environmentSensitive_fa, environmentSensitive_ba]
  rfl

/-- Heim and Kratzer's rules, application at one assignment with an indexed leaf the value the
assignment gives its index, give *she called her* the same function of the assignment. -/
theorem interpret_sheCalledHer :
    sheCalledHer.interpret application D (fun _ ↦ ind) (fun {_} ↦ EnvItem.val call)
        (fun | .called => [⟨_, .called⟩]) =
      [⟨.t, fun g ↦ call (g 1) (g 0)⟩] := by
  simp [sheCalledHer, EnvItem.val]

end Reading

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

/-- The set each word denotes, the restrictor of a *wh*-phrase and the singleton of the verb. -/
def Item.val : {a : Ty Unit} → Item a → (Ty.comp .S a).Dom D
  | _, .whichDog => {d | dog d}
  | _, .chased => {chase}
  | _, .whichCat => {c | cat c}

/-- The same sets, of the words typed as Hamblin's grammar types them. -/
def SetItem.val : {a : Ty Unit} → SetItem a → a.Dom D
  | _, .whichDog => {d | dog d}
  | _, .chased => {chase}
  | _, .whichCat => {c | cat c}

/-- Hamblin's grammar, application pointwise at indeterminacy. -/
def hamblin : Interpreter (effectGrammar (application (B := Unit))) ℕ :=
  effectDrivenWithin (MetaMode.pointwise (· = .S)) application

/-- (3.2): *which dog chased which cat*. -/
def whichDogChasedWhichCat : Tree Unit Word :=
  .bin (.leaf .whichDog) (.bin (.leaf .chased) (.leaf .whichCat))

private theorem binary_fa : hamblin.binary (e ⇒ e ⇒ .t) e = [⟨e ⇒ .t, .basic .fa⟩] := rfl

private theorem binary_ba : hamblin.binary e (e ⇒ .t) = [⟨.t, .basic .ba⟩] := rfl

/-- (3.2): *which dog chased which cat* denotes the set of the propositions `chase c d` for `c` a
cat and `d` a dog. -/
theorem values_whichDogChasedWhichCat :
    whichDogChasedWhichCat.values hamblin effectGrammar.structure
        (fun {_} ↦ SetItem.val dog cat chase) sets =
      [⟨.comp .S .t, {p | ∃ c, cat c ∧ ∃ d, dog d ∧ p = chase c d}⟩] := by
  have h := Tree.values_effectDrivenWithin_pointwise (P := (· = .S)) (f := .S)
    (G := application (B := Unit)) rfl
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
maps followed by Join, of which the one with the right daughter's map outermost gives the object
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
    ((Mode.ap (.basic (.inl .ba)) :
      Mode (baseGrammar Unit).Binary (C e) (C (e ⇒ .t)) (C .t)).eval D
        (fun c ↦ ∃ y, c y) (admiresEveryone admires)) id ↔
      ∃ y, ∀ x, admires x y := Iff.rfl

/-- The inverse order: everyone is admired by someone. -/
theorem eval_join_mapR_mapL_iff :
    ((Mode.join (.mapR (.mapL (.basic (.inl .ba)))) :
      Mode (baseGrammar Unit).Binary (C e) (C (e ⇒ .t)) (C .t)).eval D
        (fun c ↦ ∃ y, c y) (admiresEveryone admires)) id ↔ ∀ x, ∃ y, admires x y := Iff.rfl

/-- The two orders are two readings: where each of two people admires only themself, everyone
is admired by someone and no one admires everyone. -/
example :
    ((Mode.join (.mapR (.mapL (.basic (.inl .ba)))) :
      Mode (baseGrammar Unit).Binary (C e) (C (e ⇒ .t)) (C .t)).eval (fun _ ↦ Bool)
        (fun c ↦ ∃ y, c y) (admiresEveryone (· = ·))) id ∧
    ¬ ((Mode.ap (.basic (.inl .ba)) :
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
theorem eval_ap_fa_eq_eval_ap_ba [f.IsCommutative] (F : (Ty.comp f (a ⇒ b)).Dom D)
    (X : (Ty.comp f a).Dom D) :
    (Mode.ap (.basic (.inl .fa)) :
      Mode (baseGrammar B).Binary (.comp f (a ⇒ b)) (.comp f a) (.comp f b)).eval D F X =
    (Mode.ap (.basic (.inl .ba)) :
      Mode (baseGrammar B).Binary (.comp f a) (.comp f (a ⇒ b)) (.comp f b)).eval D X F :=
  congrFun₂ (Mode.eval_ap_comm rfl) F X

variable {o : Ty B}

-- (3.31a)
theorem eval_ap_fa_C (F : (Ty.comp (.C o) (a ⇒ b)).Dom D) (X : (Ty.comp (.C o) a).Dom D) :
    (Mode.ap (f := .C o) (.basic (.inl .fa)) :
      Mode (baseGrammar B).Binary (.comp (.C o) (a ⇒ b)) (.comp (.C o) a) (.comp (.C o) b)).eval
        D F X = fun c ↦ F fun g ↦ X fun x ↦ c (g x) := rfl

-- (3.31b)
theorem eval_ap_ba_C (X : (Ty.comp (.C o) a).Dom D) (F : (Ty.comp (.C o) (a ⇒ b)).Dom D) :
    (Mode.ap (f := .C o) (.basic (.inl .ba)) :
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
    (Mode.unitR (.basic (.inl .fa)) :
      Mode (baseGrammar Unit).Binary (F .t ⇒ .t) .t .t).eval D (only (E := E)) p ↔ p := by
  change {q ∈ ({p} : Set Prop) | q} = {p} ↔ p
  refine ⟨fun h ↦ (h.ge rfl).2, fun hp ↦ Set.ext fun q ↦ ⟨And.left, fun hq ↦ ⟨hq, ?_⟩⟩⟩
  rwa [Set.mem_singleton_iff.1 hq]

end Focus

end BumfordCharlow2026
