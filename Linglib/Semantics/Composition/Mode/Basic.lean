module

public import Linglib.Semantics.Composition.Effect
public import Linglib.Semantics.Composition.Basic
public import Linglib.Core.ModelTheory.ManySorted.LanguageMap

/-!
# The effect-driven grammar

Bumford and Charlow's grammar takes whatever basic modes of combination a theory has and closes
them under meta-modes, each lifting a mode through an effect by the structure the effect has: Map
Left and Map Right by its map, Structured App and the Unit modes where it is applicative, Join
where it is a monad, Co-unit and Eject for the adjunction of storing and reading, and Lower for a
continuation at its own result type.

## Main definitions

* `Interpreter.Mode`: the basic modes closed under the meta-modes.
* `Interpreter.Mode.eval`: the meaning of a mode, by the operations of the effects.
* `Interpreter.Mode.Equiv`: two modes mean the same in every structure, the relation of the
  setoid of modes, `m ≈ m'`; each meta-mode respects it.
* `Interpreter.MetaMode`, `Interpreter.Mode.Within`: the meta-modes, and the modes that keep to
  an inventory of them at each effect.
* `Interpreter.effectGrammar`: the grammar whose binary rules are the modes over a grammar's
  rules, with its structure, and `Interpreter.effectGrammar.basic`, the map of the grammar into
  it.

## References

* [bumford-charlow-2026]
-/

@[expose] public section

open ManySorted

namespace Interpreter

variable {B : Type}

/-- The modes of combination: a theory's basic modes closed under the meta-modes. -/
inductive Mode (Rule : Ty B → Ty B → Ty B → Type) : Ty B → Ty B → Ty B → Type
  /-- A basic mode. -/
  | basic {l r u : Ty B} (b : Rule l r u) : Mode Rule l r u
  /-- Map Right: a mode under the effect of the right daughter. -/
  | mapR {f : Eff B} {l r u : Ty B} (m : Mode Rule l r u) : Mode Rule l (.comp f r) (.comp f u)
  /-- Map Left: a mode under the effect of the left daughter. -/
  | mapL {f : Eff B} {l r u : Ty B} (m : Mode Rule l r u) : Mode Rule (.comp f l) r (.comp f u)
  /-- Structured App: a mode on the results of two daughters with one applicative effect. -/
  | ap {f : Eff B} {l r u : Ty B} (h : f.IsApplicative) (m : Mode Rule l r u) :
      Mode Rule (.comp f l) (.comp f r) (.comp f u)
  /-- Unit Right: a left daughter expecting a computation is given a pure one. -/
  | unitR {f : Eff B} {l l' r u : Ty B} (h : f.IsApplicative) (m : Mode Rule (l ⇒ l') r u) :
      Mode Rule (.comp f l ⇒ l') r u
  /-- Unit Left: a right daughter expecting a computation is given a pure one. -/
  | unitL {f : Eff B} {l r r' u : Ty B} (h : f.IsApplicative) (m : Mode Rule l (r ⇒ r') u) :
      Mode Rule l (.comp f r ⇒ r') u
  /-- Co-unit: what the left daughter stores is given to what the right daughter reads. -/
  | counit {i l r u : Ty B} (m : Mode Rule l r u) : Mode Rule (.comp (.W i) l) (.comp (.R i) r) u
  /-- Eject Right: reading is ejected from a right daughter that is a function into a reader. -/
  | ejectR {i l r r' u : Ty B} (m : Mode Rule l (.comp (.R i) (r ⇒ r')) u) :
      Mode Rule l (r ⇒ .comp (.R i) r') u
  /-- Eject Left: reading is ejected from a left daughter that is a function into a reader. -/
  | ejectL {i l l' r u : Ty B} (m : Mode Rule (.comp (.R i) (l ⇒ l')) r u) :
      Mode Rule (l ⇒ .comp (.R i) l') r u
  /-- Join: two layers of one monadic effect in the result are flattened. -/
  | join {f : Eff B} {l r u : Ty B} (h : f.IsApplicative)
      (m : Mode Rule l r (.comp f (.comp f u))) : Mode Rule l r (.comp f u)
  /-- Lower: a continuation at its own result type in the result is run at the identity. -/
  | lower {l r u : Ty B} (m : Mode Rule l r (.comp (.C u) u)) : Mode Rule l r u

/-- The meta-modes, by the structure of an effect each one uses: its map, its application, its
unit, its join, and for storing and reading the co-unit and the ejection, and for a continuation
its lowering. -/
inductive MetaMode
  /-- Map Left and Map Right. -/
  | map
  /-- Structured App. -/
  | ap
  /-- Unit Left and Unit Right. -/
  | unit
  /-- Join. -/
  | join
  /-- Co-unit. -/
  | counit
  /-- Eject Left and Eject Right. -/
  | eject
  /-- Lower. -/
  | lower
  deriving DecidableEq, Repr

namespace Mode

variable {Rule : Ty B → Ty B → Ty B → Type}

/-- A mode keeps to an inventory of meta-modes when each meta-mode in it is one the inventory has
at the effect it lifts through. The co-unit and the ejections are asked of the reader, and the
lowering of the continuation. A grammar need not have every meta-mode at every effect: one with
only Structured App at an effect, and every lexical item carrying the effect, is the pointwise
grammar of that effect, in which an operator on the effect captures all of it in its prejacent. -/
def Within (inv : MetaMode → Eff B → Prop) : {l r u : Ty B} → Mode Rule l r u → Prop
  | _, _, _, .basic _ => True
  | _, _, _, .mapR (f := f) m => inv .map f ∧ m.Within inv
  | _, _, _, .mapL (f := f) m => inv .map f ∧ m.Within inv
  | _, _, _, .ap (f := f) _ m => inv .ap f ∧ m.Within inv
  | _, _, _, .unitR (f := f) _ m => inv .unit f ∧ m.Within inv
  | _, _, _, .unitL (f := f) _ m => inv .unit f ∧ m.Within inv
  | _, _, _, .counit (i := i) m => inv .counit (.R i) ∧ m.Within inv
  | _, _, _, .ejectR (i := i) m => inv .eject (.R i) ∧ m.Within inv
  | _, _, _, .ejectL (i := i) m => inv .eject (.R i) ∧ m.Within inv
  | _, _, _, .join (f := f) _ m => inv .join f ∧ m.Within inv
  | _, _, _, .lower (u := u) m => inv .lower (.C u) ∧ m.Within inv

instance decidableWithin (inv : MetaMode → Eff B → Prop) [∀ k f, Decidable (inv k f)] :
    {l r u : Ty B} → (m : Mode Rule l r u) → Decidable (m.Within inv)
  | _, _, _, .basic _ => isTrue trivial
  | _, _, _, .mapR m | _, _, _, .mapL m | _, _, _, .ap _ m | _, _, _, .unitR _ m
  | _, _, _, .unitL _ m | _, _, _, .counit m | _, _, _, .ejectR m | _, _, _, .ejectL m
  | _, _, _, .join _ m | _, _, _, .lower m =>
    haveI := decidableWithin inv m
    inferInstanceAs (Decidable (_ ∧ _))

/-- Every mode keeps to the inventory with every meta-mode at every effect. -/
theorem within_of_forall {inv : MetaMode → Eff B → Prop} (h : ∀ k f, inv k f) :
    ∀ {l r u : Ty B} (m : Mode Rule l r u), m.Within inv
  | _, _, _, .basic _ => trivial
  | _, _, _, .mapR m | _, _, _, .mapL m | _, _, _, .ap _ m | _, _, _, .unitR _ m
  | _, _, _, .unitL _ m | _, _, _, .counit m | _, _, _, .ejectR m | _, _, _, .ejectL m
  | _, _, _, .join _ m | _, _, _, .lower m => ⟨h _ _, within_of_forall h m⟩

/-- The meaning of a mode over a grammar's rules, from a structure for the grammar: each
meta-mode is the operation of its effect. -/
def eval {G : Language (Ty B)} (D : B → Type) [M : G.Structure (Ty.Dom D)] :
    {l r u : Ty B} → Mode G.Binary l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .basic b, x, y => M.funMap b (x, y)
  | _, _, _, .mapR (f := f) m, a, b => Eff.map f (fun y ↦ m.eval D a y) b
  | _, _, _, .mapL (f := f) m, a, b => Eff.map f (fun x ↦ m.eval D x b) a
  | _, _, _, .ap (f := f) h m, a, b =>
    Eff.seq f h (Eff.map f (fun x y ↦ m.eval D x y) a) b
  | _, _, _, .unitR (f := f) h m, a, b => m.eval D (fun x ↦ a (Eff.pure f h x)) b
  | _, _, _, .unitL (f := f) h m, a, b => m.eval D a fun y ↦ b (Eff.pure f h y)
  | _, _, _, .counit (i := i) m, a, b =>
    Eff.counit (Eff.map (.W i) (fun x ↦ Eff.map (.R i) (fun y ↦ m.eval D x y) b) a)
  | _, _, _, .ejectR m, a, b => m.eval D a (Eff.eject b)
  | _, _, _, .ejectL m, a, b => m.eval D (Eff.eject a) b
  | _, _, _, .join (f := f) h m, a, b => Eff.join f h (m.eval D a b)
  | _, _, _, .lower m, a, b => Eff.lower (m.eval D a b)

/-- Two modes mean the same when they combine their daughters alike in every structure for the
grammar. -/
protected def Equiv {G : Language (Ty B)} {l r u : Ty B} (m m' : Mode G.Binary l r u) : Prop :=
  ∀ (D : B → Type) [G.Structure (Ty.Dom D)], m.eval D = m'.eval D

namespace Equiv

variable {G : Language (Ty B)} {l r u : Ty B} {m m' m'' : Mode G.Binary l r u}

@[refl] protected theorem refl (m : Mode G.Binary l r u) : m.Equiv m := fun _ _ ↦ rfl

@[symm] protected theorem symm (h : m.Equiv m') : m'.Equiv m := fun D _ ↦ (h D).symm

@[trans] protected theorem trans (h : m.Equiv m') (h' : m'.Equiv m'') : m.Equiv m'' :=
  fun D _ ↦ (h D).trans (h' D)

end Equiv

/-- Modes up to sameness of meaning. -/
instance setoid {G : Language (Ty B)} {l r u : Ty B} : Setoid (Mode G.Binary l r u) where
  r := Mode.Equiv
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

theorem equiv_def {G : Language (Ty B)} {l r u : Ty B} {m m' : Mode G.Binary l r u} :
    m ≈ m' ↔ ∀ (D : B → Type) [G.Structure (Ty.Dom D)], m.eval D = m'.eval D := Iff.rfl

end Mode

namespace Mode.Equiv

variable {G : Language (Ty B)} {f : Eff B} {i l l' r r' u : Ty B}

/-! Each meta-mode respects sameness of meaning. -/

protected theorem mapR {m m' : Mode G.Binary l r u} (h : m ≈ m') :
    (.mapR m : Mode G.Binary l (.comp f r) (.comp f u)) ≈ .mapR m' :=
  fun D _ ↦ funext₂ fun a b ↦ by simp only [eval, h D]

protected theorem mapL {m m' : Mode G.Binary l r u} (h : m ≈ m') :
    (.mapL m : Mode G.Binary (.comp f l) r (.comp f u)) ≈ .mapL m' :=
  fun D _ ↦ funext₂ fun a b ↦ by simp only [eval, h D]

protected theorem ap (hf : f.IsApplicative) {m m' : Mode G.Binary l r u} (h : m ≈ m') :
    Mode.ap hf m ≈ .ap hf m' :=
  fun D _ ↦ funext₂ fun a b ↦ by simp only [eval, h D]

protected theorem unitR (hf : f.IsApplicative) {m m' : Mode G.Binary (l ⇒ l') r u}
    (h : m ≈ m') : Mode.unitR hf m ≈ .unitR hf m' :=
  fun D _ ↦ funext₂ fun a b ↦ by simp only [eval, h D]

protected theorem unitL (hf : f.IsApplicative) {m m' : Mode G.Binary l (r ⇒ r') u}
    (h : m ≈ m') : Mode.unitL hf m ≈ .unitL hf m' :=
  fun D _ ↦ funext₂ fun a b ↦ by simp only [eval, h D]

protected theorem counit {m m' : Mode G.Binary l r u} (h : m ≈ m') :
    (.counit m : Mode G.Binary (.comp (.W i) l) (.comp (.R i) r) u) ≈ .counit m' :=
  fun D _ ↦ funext₂ fun a b ↦ by simp only [eval, h D]

protected theorem ejectR {m m' : Mode G.Binary l (.comp (.R i) (r ⇒ r')) u} (h : m ≈ m') :
    Mode.ejectR m ≈ .ejectR m' :=
  fun D _ ↦ funext₂ fun a b ↦ by simp only [eval, h D]

protected theorem ejectL {m m' : Mode G.Binary (.comp (.R i) (l ⇒ l')) r u} (h : m ≈ m') :
    Mode.ejectL m ≈ .ejectL m' :=
  fun D _ ↦ funext₂ fun a b ↦ by simp only [eval, h D]

protected theorem join (hf : f.IsApplicative) {m m' : Mode G.Binary l r (.comp f (.comp f u))}
    (h : m ≈ m') : Mode.join hf m ≈ .join hf m' :=
  fun D _ ↦ funext₂ fun a b ↦ by simp only [eval, h D]

protected theorem lower {m m' : Mode G.Binary l r (.comp (.C u) u)} (h : m ≈ m') :
    Mode.lower m ≈ .lower m' :=
  fun D _ ↦ funext₂ fun a b ↦ by simp only [eval, h D]

end Mode.Equiv

/-- The effect-driven grammar over a grammar: its binary rules are replaced by the modes over
them, and its other symbols are kept. -/
def effectGrammar (G : Language (Ty B)) : Language (Ty B) := G.withBinary (Mode G.Binary)

/-- The structure of the effect-driven grammar over a grammar, from a structure for the
grammar: a mode means what the effects make of the rules, and any other symbol what it does
there. -/
instance effectGrammar.structure {G : Language (Ty B)} {D : B → Type}
    [M : G.Structure (Ty.Dom D)] : (effectGrammar G).Structure (Ty.Dom D) :=
  M.withBinary fun m ↦ m.eval D

/-- The map of a grammar into its effect-driven grammar: a rule is its basic mode. -/
def effectGrammar.basic (G : Language (Ty B)) : G →ᴸ effectGrammar G := .withBinary .basic

/-- A basic mode means what its rule means: the structure of the effect-driven grammar expands
that of the grammar. -/
theorem effectGrammar.basic_isExpansionOn {G : Language (Ty B)} {D : B → Type}
    [M : G.Structure (Ty.Dom D)] :
    (effectGrammar.basic G).IsExpansionOn M effectGrammar.structure where
  map_onFunction σ _ f _ :=
    match σ, f with
    | .prod (.of _) (.of _), _ => rfl
    | .nil, _ => rfl
    | .of _, _ => rfl
    | .prod .nil _, _ => rfl
    | .prod (.prod _ _) _, _ => rfl
    | .prod (.of _) .nil, _ => rfl
    | .prod (.of _) (.prod _ _), _ => rfl

end Interpreter
