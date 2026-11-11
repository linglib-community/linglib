module

public import Linglib.Semantics.Composition.Lawful

/-!
# Derivations that differ in the order of commuting effects

Two daughters carrying one effect combine by Structured App, or by the two maps in either order
followed by Join. Mapped right first, the Join is Structured App, and at a commutative effect so
is the other: the effect-driven grammar gives one meaning several derivations. The normal form of
a mode has Structured App for each such Join, and [means what the mode
does](##Interpreter.Mode.eval_normalize), so [derivations with one normal form have one
value](##Interpreter.effectGrammar.realize_eq_of_onTerm_normalize_eq).

## Main definitions

* `Interpreter.Mode.normalize`: the normal form of a mode.
* `Interpreter.effectGrammar.normalize`: the map of the effect-driven grammar into itself that
  takes each mode to its normal form, [which keeps the meaning of every
  symbol](##Interpreter.effectGrammar.normalize_isExpansionOn).

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

variable {Rule : Ty B → Ty B → Ty B → Type} {f : Eff B} {D : B → Type} {G : Language (Ty B)}
  [M : G.Structure (Ty.Dom D)] {l r u : Ty B}

/-- Join over Map Left of a mode: Structured App, where the mode is a Map Right. -/
def joinMapL (h : f.IsApplicative) :
    {l r u : Ty B} → Mode Rule l r (.comp f u) → Mode Rule (.comp f l) r (.comp f u)
  | _, _, _, .mapR m => .ap h m
  | _, _, _, m => .join h (.mapL m)

theorem eval_joinMapL (h : f.IsApplicative) (m : Mode G.Binary l r (.comp f u))
    (a : (Ty.comp f l).Dom D) (b : r.Dom D) :
    (joinMapL h m).eval D a b = (Mode.join h (.mapL m)).eval D a b := by
  cases m with
  | mapR m => exact (eval_join_mapL_mapR h m a b).symm
  | _ => rfl

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

theorem eval_joinMapR (h : f.IsApplicative) (m : Mode G.Binary l r (.comp f u))
    (a : l.Dom D) (b : (Ty.comp f r).Dom D) :
    (joinMapR h m).eval D a b = (Mode.join h (.mapR m)).eval D a b := by
  cases m with
  | mapL m =>
    show (if f.IsCommutative then Mode.ap h m else .join h (.mapR (.mapL m))).eval D a b = _
    split_ifs with hc
    · exact (eval_join_mapR_mapL hc m a b).symm
    · rfl
  | _ => rfl

theorem eval_joinNormal (h : f.IsApplicative) (m : Mode G.Binary l r (.comp f (.comp f u)))
    (a : l.Dom D) (b : r.Dom D) :
    (joinNormal h m).eval D a b = Eff.join f h (m.eval D a b) := by
  cases m with
  | mapL m => exact eval_joinMapL h m a b
  | mapR m => exact eval_joinMapR h m a b
  | _ => rfl

/-- A mode and its normal form mean the same. -/
@[simp] theorem eval_normalize : ∀ {l r u : Ty B} (m : Mode G.Binary l r u) (a : l.Dom D)
    (b : r.Dom D), m.normalize.eval D a b = m.eval D a b
  | _, _, _, .basic _, _, _ => rfl
  | _, _, _, .mapR m, a, b | _, _, _, .mapL m, a, b | _, _, _, .ap _ m, a, b
  | _, _, _, .unitR _ m, a, b | _, _, _, .unitL _ m, a, b | _, _, _, .counit m, a, b
  | _, _, _, .ejectR m, a, b | _, _, _, .ejectL m, a, b | _, _, _, .lower m, a, b => by
    simp only [normalize, eval, eval_normalize m]
  | _, _, _, .join h m, a, b => by
    simp only [normalize, eval, eval_joinNormal, eval_normalize m]

/-- Modes with one normal form mean the same: they differ in the order in which commuting
effects are merged. -/
theorem eval_eq_of_normalize_eq {m m' : Mode G.Binary l r u} (h : m.normalize = m'.normalize)
    (a : l.Dom D) (b : r.Dom D) : m.eval D a b = m'.eval D a b := by
  rw [← eval_normalize m, h, eval_normalize]

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

/-- Taking normal forms keeps the meaning of every symbol of the effect-driven grammar. -/
theorem normalize_isExpansionOn [M : G.Structure (Ty.Dom D)] :
    (normalize G).IsExpansionOn (effectGrammar.structure (M := M)) effectGrammar.structure where
  map_onFunction σ _ g x :=
    match σ, g with
    | .prod (.of _) (.of _), g => Mode.eval_normalize g x.1 x.2
    | .nil, _ => rfl
    | .of _, _ => rfl
    | .prod .nil _, _ => rfl
    | .prod (.prod _ _) _, _ => rfl
    | .prod (.of _) .nil, _ => rfl
    | .prod (.of _) (.prod _ _), _ => rfl

/-- **Equal meanings.** Derivations of the effect-driven grammar with one normal form have one
value: they differ, at some of their nodes, in the order in which commuting effects are
merged. -/
theorem realize_eq_of_onTerm_normalize_eq [M : G.Structure (Ty.Dom D)] {W : Ty B → Type}
    (ρ : ∀ {a : Ty B}, W a → a.Dom D) {a : Ty B} {d d' : (effectGrammar G).Deriv W a}
    (h : (normalize G).onTerm d = (normalize G).onTerm d') :
    d.realize effectGrammar.structure ρ = d'.realize effectGrammar.structure ρ := by
  rw [← Language.LHom.realize_onTerm normalize_isExpansionOn ρ d, h,
    Language.LHom.realize_onTerm normalize_isExpansionOn]

end effectGrammar

end Interpreter
