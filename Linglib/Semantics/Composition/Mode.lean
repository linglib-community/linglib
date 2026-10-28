module

public import Linglib.Semantics.Composition.Ty
public import Linglib.Semantics.Composition.EventIdentification
public import Linglib.Semantics.Modification.Basic
public import Linglib.Semantics.Composition.Extensional

/-!
# Composition modes

A *composition mode* is a rule by which the meanings of two sisters combine into the meaning of
their mother, selected by the daughters' types: functional application, predicate modification
and Kratzer's event identification. Over computation types, Bumford and Charlow's meta-modes lift a
mode through an effect: Map Left and Map Right apply it under the effect of a daughter, Structured
App applies it to the results of two daughters with one effect, merging their effects, and Unit
Left and Unit Right give a daughter that expects a computation the pure computation of a value. A
pair of types may then compose in several ways, and [the mode their types select is always
basic](##Ty.isBasic_of_mode?_eq_some). Under the reader of worlds, von Fintel and Heim's
intensional application is application mapped over the function's reader, which gives the function
its argument's whole intension, while Unit Right gives it the constant intension of the argument's
value; [the two agree on every argument exactly when the function is
extensional](##forall_eval_mapLeft_eq_eval_unitRight_iff).

## Main definitions

* `Montague.Mode`: the composition modes, typed by the two daughters and the mother.
* `Montague.Ty.mode?`, `Montague.Ty.combine?`: the mode two daughters' types select, and the type
  they compose to.
* `Montague.Mode.eval`: the mother's denotation from the daughters'.
* `Montague.Mode.evalM`: composition under an applicative effect.
* `Montague.Mode.combine?`: composition, by the mode their types select, in a family of values.
* `Montague.Ty.modes`: every mode by which two daughters' types compose.
* `Montague.Mode.IsBasic`: the modes that are not meta-modes.

## Implementation notes

The daughters' types select the first mode that applies among functional application, predicate
modification and event identification. In any family of
values indexed by types, [composing commutes with every map of families that commutes with the
modes](##combine?_map), and [the type of the result depends only on the daughters'
types](##combine?_map_fst). `Ty.mode?` selects among the basic modes only and is computed by
the kernel, so a tree's denotation reduces by `rfl`; `Ty.modes`, which also lifts modes through
effects, is defined by well-founded recursion and computed by `simp`.

## References

* [heim-kratzer-1998]
* [von-fintel-heim-2011]
* [kratzer-1996]
* [bumford-charlow-2026]
-/

@[expose] public section

namespace Montague

/-- The composition modes, typed by the two daughters and the mother, are functional application,
predicate modification of two predicates of one sort, event identification of a role head with a
predicate of eventualities, Kratzer's (23) ([kratzer-1996]), and the meta-modes lifting a mode
through an effect. All but predicate modification come in both orders. -/
inductive Mode : Ty → Ty → Ty → Type where
  /-- Functional application, the left daughter the function. -/
  | functionalLeft {σ τ : Ty} : Mode (σ ⇒ τ) σ τ
  /-- Functional application, the right daughter the function. -/
  | functionalRight {σ τ : Ty} : Mode σ (σ ⇒ τ) τ
  /-- Predicate modification, the intersection of two predicates of a sort. -/
  | predicateModification {σ : Ty} : Mode (σ ⇒ .t) (σ ⇒ .t) (σ ⇒ .t)
  /-- Event identification, the role head the left daughter. -/
  | eventIdentificationLeft : Mode (.e ⇒ .v ⇒ .t) (.v ⇒ .t) (.e ⇒ .v ⇒ .t)
  /-- Event identification, the role head the right daughter. -/
  | eventIdentificationRight : Mode (.v ⇒ .t) (.e ⇒ .v ⇒ .t) (.e ⇒ .v ⇒ .t)
  /-- Map Right ([bumford-charlow-2026]): a mode applied under the effect of the right
  daughter. -/
  | mapRight {f : Eff} {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) : Mode σ₁ (.comp f σ₂) (.comp f τ)
  /-- Map Left ([bumford-charlow-2026]): a mode applied under the effect of the left daughter. -/
  | mapLeft {f : Eff} {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) : Mode (.comp f σ₁) σ₂ (.comp f τ)
  /-- Structured App ([bumford-charlow-2026]): a mode applied to the results of two daughters with
  one effect, their effects merged. -/
  | ap {f : Eff} {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) : Mode (.comp f σ₁) (.comp f σ₂) (.comp f τ)
  /-- Unit Right ([bumford-charlow-2026]): a left daughter expecting a computation takes the pure
  computation of a value. -/
  | unitRight {f : Eff} {σ σ' τ ω : Ty} (m : Mode (σ ⇒ σ') τ ω) : Mode (.comp f σ ⇒ σ') τ ω
  /-- Unit Left ([bumford-charlow-2026]): a right daughter expecting a computation takes the pure
  computation of a value. -/
  | unitLeft {f : Eff} {σ τ τ' ω : Ty} (m : Mode σ (τ ⇒ τ') ω) : Mode σ (.comp f τ ⇒ τ') ω
  deriving DecidableEq

namespace Mode

/-! ### Selection by the daughters' types -/

/-- Forward functional application applies when the left daughter is a function on the right one. -/
def functionalLeft? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | .fn σ τ, σ₂ => if h : σ = σ₂ then some ⟨τ, h ▸ functionalLeft⟩ else none
  | _, _ => none

/-- Backward functional application applies when the right daughter is a function on the left. -/
def functionalRight? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | σ₁, .fn σ τ => if h : σ = σ₁ then some ⟨τ, h ▸ functionalRight⟩ else none
  | _, _ => none

/-- Predicate modification applies to two predicates of individuals or two predicates of
eventualities ([wellwood-2015]). -/
def predicateModification? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | .fn .e .t, .fn .e .t => some ⟨_, predicateModification⟩
  | .fn .v .t, .fn .v .t => some ⟨_, predicateModification⟩
  | _, _ => none

/-- Event identification applies to a role head and an eventuality predicate, in either order. -/
def eventIdentification? : (σ₁ σ₂ : Ty) → Option (Σ τ, Mode σ₁ σ₂ τ)
  | .fn .e (.fn .v .t), .fn .v .t => some ⟨_, eventIdentificationLeft⟩
  | .fn .v .t, .fn .e (.fn .v .t) => some ⟨_, eventIdentificationRight⟩
  | _, _ => none

end Mode

/-- The mode by which a left daughter of type `σ₁` and a right daughter of type `σ₂` compose is the
first that applies of functional application (with the left daughter as the function first),
predicate modification and event identification. -/
def Ty.mode? (σ₁ σ₂ : Ty) : Option (Σ τ, Mode σ₁ σ₂ τ) :=
  Mode.functionalLeft? σ₁ σ₂ <|> Mode.functionalRight? σ₁ σ₂ <|>
    Mode.predicateModification? σ₁ σ₂ <|> Mode.eventIdentification? σ₁ σ₂

/-- The type of the mother of a left daughter of type `σ₁` and a right daughter of type `σ₂`,
under the mode their types select. -/
def Ty.combine? (σ₁ σ₂ : Ty) : Option Ty := (σ₁.mode? σ₂).map (·.1)

/-- A basic mode is one of the composition principles proper, not a meta-mode that lifts one over
an effect. -/
def Mode.IsBasic {σ₁ σ₂ τ : Ty} : Mode σ₁ σ₂ τ → Prop
  | .mapRight _ | .mapLeft _ | .ap _ | .unitRight _ | .unitLeft _ => False
  | _ => True

/-- The mode two daughters' types select is basic. -/
theorem Ty.isBasic_of_mode?_eq_some {σ₁ σ₂ : Ty} {p : Σ τ, Mode σ₁ σ₂ τ}
    (h : σ₁.mode? σ₂ = some p) : p.2.IsBasic := by
  simp only [Ty.mode?, Option.orElse_eq_orElse, Option.orElse_eq_or, Option.or_eq_some_iff] at h
  rcases h with h | ⟨-, h | ⟨-, h | ⟨-, h⟩⟩⟩ <;>
    simp only [Mode.functionalLeft?, Mode.functionalRight?, Mode.predicateModification?,
      Mode.eventIdentification?] at h <;>
    split at h <;> (try split_ifs at h with hσ) <;> cases h <;> (try subst hσ) <;> trivial

/-- Every mode by which a left daughter of type `σ₁` and a right daughter of type `σ₂` compose,
[bumford-charlow-2026]'s `combine`: the basic mode their types select, Map Right and Map Left over
a daughter that is a computation, Structured App over two with one effect, and Unit Right and Unit
Left for a daughter that expects one, each over every way of composing the underlying types. -/
def Ty.modes (σ₁ σ₂ : Ty) : List (Σ τ, Mode σ₁ σ₂ τ) :=
  (σ₁.mode? σ₂).toList ++
    (match σ₂ with
      | .comp f b => (σ₁.modes b).map fun p ↦ ⟨.comp f p.1, .mapRight p.2⟩
      | _ => []) ++
    (match σ₁ with
      | .comp f a => (a.modes σ₂).map fun p ↦ ⟨.comp f p.1, .mapLeft p.2⟩
      | _ => []) ++
    (match σ₁, σ₂ with
      | .comp f a, .comp f' b =>
        if h : f = f' then h ▸ (a.modes b).map fun p ↦ ⟨.comp f p.1, .ap p.2⟩ else []
      | _, _ => []) ++
    (match σ₁ with
      | .fn (.comp _ a) b => ((a ⇒ b).modes σ₂).map fun p ↦ ⟨p.1, .unitRight p.2⟩
      | _ => []) ++
    (match σ₂ with
      | .fn (.comp _ a) b => (σ₁.modes (a ⇒ b)).map fun p ↦ ⟨p.1, .unitLeft p.2⟩
      | _ => [])
termination_by sizeOf σ₁ + sizeOf σ₂

namespace Mode

@[simp] theorem mode?_fn_left (σ τ : Ty) : (σ ⇒ τ).mode? σ = some ⟨τ, functionalLeft⟩ := by
  simp only [Ty.mode?, functionalLeft?, ↓reduceDIte, Option.orElse_eq_orElse, Option.orElse_eq_or,
    Option.some_or]

theorem functionalLeft?_self_fn (σ τ : Ty) : functionalLeft? σ (σ ⇒ τ) = none := by
  cases σ with
  | fn a b =>
    simp only [functionalLeft?]
    split_ifs with h
    · have := congrArg sizeOf h
      simp only [Ty.fn.sizeOf_spec] at this
      omega
    · rfl
  | _ => rfl

@[simp] theorem mode?_fn_right (σ τ : Ty) : σ.mode? (σ ⇒ τ) = some ⟨τ, functionalRight⟩ := by
  simp only [Ty.mode?, functionalLeft?_self_fn, functionalRight?, ↓reduceDIte,
    Option.orElse_eq_orElse, Option.orElse_eq_or, Option.none_or, Option.some_or]

@[simp] theorem mode?_predicateModification :
    (Ty.e ⇒ .t).mode? (.e ⇒ .t) = some ⟨_, predicateModification⟩ := by
  simp [Ty.mode?, functionalLeft?, functionalRight?, predicateModification?]

/-! ### Denotation -/

variable {E W : Type} {S : Sorts} {σ₁ σ₂ τ : Ty}

/-- The denotation of a mode is application, intersection of two predicates or event
identification, and for a meta-mode that of its mode under the effect of a daughter, on the
results of two daughters (`(λa b. a ∗ b) • E₁ ⊛ E₂`), or with the pure computation of a value
given to a daughter that expects one. -/
@[simp] def eval : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → Ty.Domain E W σ₁ S → Ty.Domain E W σ₂ S →
    Ty.Domain E W τ S
  | _, _, _, functionalLeft, f, a => f a
  | _, _, _, functionalRight, a, f => f a
  | _, _, _, predicateModification, p, q => Modifier.intersective p q
  | _, _, _, eventIdentificationLeft, f, p => ArgumentStructure.eventIdentification f p
  | _, _, _, eventIdentificationRight, p, f => ArgumentStructure.eventIdentification f p
  | _, _, _, mapRight (f := f) m, a, b => Eff.map f (fun y ↦ m.eval a y) b
  | _, _, _, mapLeft (f := f) m, a, b => Eff.map f (fun x ↦ m.eval x b) a
  | _, _, _, ap (f := f) m, a, b => Eff.seq f (Eff.map f (fun x y ↦ m.eval x y) a) b
  | _, _, _, unitRight (f := f) m, a, b => m.eval (fun x ↦ a (Eff.pure f x)) b
  | _, _, _, unitLeft (f := f) m, a, b => m.eval a (fun y ↦ b (Eff.pure f y))

/-- The denotation of a mode under an applicative effect, which runs the left daughter's
computation first. -/
def evalM {M : Type → Type} [Applicative M] (m : Mode σ₁ σ₂ τ) (a : M (Ty.Domain E W σ₁ S))
    (b : M (Ty.Domain E W σ₂ S)) : M (Ty.Domain E W τ S) :=
  m.eval <$> a <*> b

@[simp] theorem evalM_id (m : Mode σ₁ σ₂ τ) (a : Ty.Domain E W σ₁ S) (b : Ty.Domain E W σ₂ S) :
    m.evalM (M := Id) a b = m.eval a b := rfl

/-- Application mapped over the reader of worlds gives the function at `w` its argument's whole
intension ([von-fintel-heim-2011]'s Intensional Functional Application), and Unit Right gives it
the constant intension of the argument's value at `w`; the two agree at `w` on every argument
exactly when the function, read as an operator on intensions, is extensional at `w`. -/
theorem forall_eval_mapLeft_eq_eval_unitRight_iff {σ τ : Ty}
    {f : W → (W → Ty.Domain E W σ S) → Ty.Domain E W τ S} {w : W} :
    (∀ a, (mapLeft (f := .reader .s) (functionalLeft (σ := .comp (.reader .s) σ) (τ := τ))).eval
        f a w = (unitRight (f := .reader .s) (functionalLeft (σ := σ) (τ := τ))).eval (f w) (a w)) ↔
      IsExtensionalAt (fun a w' ↦ f w' a) w :=
  isExtensionalAt_iff_forall_const.symm

/-! ### Composition in a family of values -/

variable {V V' : Ty → Type*}

/-- Two values compose by the mode their types select, interpreted by `op`, and not at all when
no mode applies. -/
def combine? (op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ) (d₁ d₂ : Σ ty, V ty) :
    Option (Σ ty, V ty) :=
  (d₁.1.mode? d₂.1).map fun p ↦ ⟨p.1, op p.2 d₁.2 d₂.2⟩

/-- The type of a composed value depends only on the daughters' types. -/
@[simp] theorem combine?_map_fst (op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ)
    (d₁ d₂ : Σ ty, V ty) : (combine? op d₁ d₂).map (·.1) = d₁.1.combine? d₂.1 := by
  simp [combine?, Ty.combine?, Option.map_map, Function.comp_def]

/-- Composing commutes with every map of families that commutes with the modes. -/
theorem combine?_map {op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ}
    {op' : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V' σ₁ → V' σ₂ → V' τ} {h : ∀ {ty : Ty}, V ty → V' ty}
    (hh : ∀ {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) a b, h (op m a b) = op' m (h a) (h b))
    (d₁ d₂ : Σ ty, V ty) :
    (combine? op d₁ d₂).map (fun d ↦ ⟨d.1, h d.2⟩) =
      combine? op' ⟨d₁.1, h d₁.2⟩ ⟨d₂.1, h d₂.2⟩ := by
  simp [combine?, Option.map_map, Function.comp_def, hh]

@[simp] theorem combine?_fn_left (op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ)
    {σ τ : Ty} (f : V (σ ⇒ τ)) (a : V σ) :
    combine? op ⟨σ ⇒ τ, f⟩ ⟨σ, a⟩ = some ⟨τ, op functionalLeft f a⟩ := by
  simp [combine?]

@[simp] theorem combine?_fn_right (op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ)
    {σ τ : Ty} (a : V σ) (f : V (σ ⇒ τ)) :
    combine? op ⟨σ, a⟩ ⟨σ ⇒ τ, f⟩ = some ⟨τ, op functionalRight a f⟩ := by
  simp [combine?]

@[simp] theorem combine?_predicateModification
    (op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ) (p q : V (.e ⇒ .t)) :
    combine? op ⟨.e ⇒ .t, p⟩ ⟨.e ⇒ .t, q⟩ = some ⟨.e ⇒ .t, op predicateModification p q⟩ := by
  simp [combine?]

@[simp] theorem combine?_predicateModification_v
    (op : ∀ {σ₁ σ₂ τ : Ty}, Mode σ₁ σ₂ τ → V σ₁ → V σ₂ → V τ) (p q : V (.v ⇒ .t)) :
    combine? op ⟨.v ⇒ .t, p⟩ ⟨.v ⇒ .t, q⟩ = some ⟨.v ⇒ .t, op predicateModification p q⟩ := by
  simp [combine?, Ty.mode?, functionalLeft?, functionalRight?, predicateModification?]

end Mode

end Montague
