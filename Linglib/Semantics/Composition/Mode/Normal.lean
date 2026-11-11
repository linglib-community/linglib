module

public import Linglib.Semantics.Composition.Lawful

/-!
# Derivations that differ in the order of commuting effects

Two daughters carrying one effect combine by Structured App, or by the two maps in either order
followed by Join. Mapped right first, the Join is Structured App, and at a commutative effect so
is the other: the effect-driven grammar gives one meaning several derivations. The normal form of
a mode has Structured App for each such Join, and [means what the mode
does](##Interpreter.Mode.normalize_equiv), so [derivations with one normal form have one
value](##Interpreter.effectGrammar.normalize_isExpansionOn).

## Main definitions

* `Interpreter.Mode.normalize`: the normal form of a mode.
* `Interpreter.effectGrammar.normalize`: the map of the effect-driven grammar into itself that
  takes each mode to its normal form.

## Implementation notes

Bumford and Charlow's implementation is said to avoid spurious ambiguity by a notion of
normal-form derivation, which the book does not define. The normal form here removes the two
Joins that the applicative and commutative laws identify with Structured App, and no other
redundancy among derivations.

## References

* [bumford-charlow-2026]
-/

@[expose] public section

open ManySorted

namespace Interpreter

variable {B : Type}

namespace Mode

variable {Rule : Ty B → Ty B → Ty B → Type} {G : Language (Ty B)} {f : Eff B} {l r u : Ty B}

/-- Join over Map Left of a mode: Structured App, where the mode is a Map Right. -/
def joinMapL (h : f.IsApplicative) :
    {l r u : Ty B} → Mode Rule l r (.comp f u) → Mode Rule (.comp f l) r (.comp f u)
  | _, _, _, .mapR m => .ap h m
  | _, _, _, m => .join h (.mapL m)

theorem joinMapL_equiv (h : f.IsApplicative) (m : Mode G.Binary l r (.comp f u)) :
    joinMapL h m ≈ Mode.join h (.mapL m) := by
  cases m with
  | mapR m => exact (join_mapL_mapR h m).symm
  | _ => exact .refl _

variable [DecidableEq B]

/-- Join over Map Right of a mode: Structured App, where the mode is a Map Left and the effect
is commutative. -/
def joinMapR (h : f.IsApplicative) :
    {l r u : Ty B} → Mode Rule l r (.comp f u) → Mode Rule l (.comp f r) (.comp f u)
  | _, _, _, .mapL m => if f.IsCommutative then .ap h m else .join h (.mapR (.mapL m))
  | _, _, _, m => .join h (.mapR m)

/-- Join of a mode: Structured App, where the mode is the two maps in an order that merges the
effects as Structured App does. -/
def joinNormal (h : f.IsApplicative) :
    {l r u : Ty B} → Mode Rule l r (.comp f (.comp f u)) → Mode Rule l r (.comp f u)
  | _, _, _, .mapL m => joinMapL h m
  | _, _, _, .mapR m => joinMapR h m
  | _, _, _, m => .join h m

/-- The normal form of a mode: Structured App for each Join over Map Left over Map Right, and at
a commutative effect for each Join over Map Right over Map Left. -/
def normalize : {l r u : Ty B} → Mode Rule l r u → Mode Rule l r u
  | _, _, _, .basic b => .basic b
  | _, _, _, .mapR m => .mapR m.normalize
  | _, _, _, .mapL m => .mapL m.normalize
  | _, _, _, .ap h m => .ap h m.normalize
  | _, _, _, .unitR h m => .unitR h m.normalize
  | _, _, _, .unitL h m => .unitL h m.normalize
  | _, _, _, .counit m => .counit m.normalize
  | _, _, _, .ejectR m => .ejectR m.normalize
  | _, _, _, .ejectL m => .ejectL m.normalize
  | _, _, _, .join h m => joinNormal h m.normalize
  | _, _, _, .lower m => .lower m.normalize

theorem joinMapR_equiv (h : f.IsApplicative) (m : Mode G.Binary l r (.comp f u)) :
    joinMapR h m ≈ Mode.join h (.mapR m) := by
  cases m with
  | mapL m =>
    show (if f.IsCommutative then Mode.ap h m else .join h (.mapR (.mapL m))) ≈ _
    split_ifs with hc
    · exact (join_mapR_mapL hc m).symm
    · exact .refl _
  | _ => exact .refl _

theorem joinNormal_equiv (h : f.IsApplicative) (m : Mode G.Binary l r (.comp f (.comp f u))) :
    joinNormal h m ≈ Mode.join h m := by
  cases m with
  | mapL m => exact joinMapL_equiv h m
  | mapR m => exact joinMapR_equiv h m
  | _ => exact .refl _

/-- A mode and its normal form mean the same. -/
theorem normalize_equiv : ∀ {l r u : Ty B} (m : Mode G.Binary l r u), m.normalize ≈ m
  | _, _, _, .basic _ => .refl _
  | _, _, _, .mapR m => (normalize_equiv m).mapR
  | _, _, _, .mapL m => (normalize_equiv m).mapL
  | _, _, _, .ap h m => (normalize_equiv m).ap h
  | _, _, _, .unitR h m => (normalize_equiv m).unitR h
  | _, _, _, .unitL h m => (normalize_equiv m).unitL h
  | _, _, _, .counit m => (normalize_equiv m).counit
  | _, _, _, .ejectR m => (normalize_equiv m).ejectR
  | _, _, _, .ejectL m => (normalize_equiv m).ejectL
  | _, _, _, .join h m => (joinNormal_equiv h _).trans ((normalize_equiv m).join h)
  | _, _, _, .lower m => (normalize_equiv m).lower

end Mode

namespace effectGrammar

variable [DecidableEq B] {G : Language (Ty B)} {D : B → Type}

/-- The map of the effect-driven grammar into itself that takes each mode to its normal form. -/
def normalize (G : Language (Ty B)) : effectGrammar G →ᴸ effectGrammar G where
  onFunction σ _ g :=
    match σ, g with
    | .prod (.of _) (.of _), g => Mode.normalize g
    | .nil, g => g
    | .of _, g => g
    | .prod .nil _, g => g
    | .prod (.prod _ _) _, g => g
    | .prod (.of _) .nil, g => g
    | .prod (.of _) (.prod _ _), g => g

/-- **Equal meanings.** Taking normal forms keeps the meaning of every symbol of the
effect-driven grammar, so a derivation and its normal form have one value, and so do two
derivations with one normal form: they differ, at some of their nodes, in the order in which
commuting effects are merged. -/
theorem normalize_isExpansionOn [M : G.Structure (Ty.Dom D)] :
    (normalize G).IsExpansionOn (effectGrammar.structure (M := M)) effectGrammar.structure where
  map_onFunction σ _ g x :=
    match σ, g with
    | .prod (.of _) (.of _), g => congrFun₂ (Mode.normalize_equiv g D) x.1 x.2
    | .nil, _ => rfl
    | .of _, _ => rfl
    | .prod .nil _, _ => rfl
    | .prod (.prod _ _) _, _ => rfl
    | .prod (.of _) .nil, _ => rfl
    | .prod (.of _) (.prod _ _), _ => rfl

end effectGrammar

end Interpreter
