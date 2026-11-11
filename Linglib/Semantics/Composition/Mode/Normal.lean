module

public import Linglib.Semantics.Composition.Lawful

/-!
# Derivations that differ in the order of commuting effects

Two daughters carrying one effect combine by Structured App, or by the two maps in either order
followed by Join. With the left daughter's map outermost the Join is Structured App, and at a
commutative effect so is the other: the effect-driven grammar gives one meaning several
derivations. The normal form of a mode has Structured App for each such Join, and [means what
the mode does](##Interpreter.Mode.normalize_equiv), so [derivations with one normal form have one
value](##Interpreter.effectGrammar.normalize_isExpansionOn).

## Main definitions

* `Interpreter.Mode.normalize`: the normal form of a mode.
* `Interpreter.effectGrammar.normalize`: the map of the effect-driven grammar into itself that
  takes each mode to its normal form.

## Implementation notes

Bumford and Charlow's implementation is said to avoid spurious ambiguity by a notion of
normal-form derivation, which the book does not define. The normal form here removes the two
Joins that the applicative and commutative laws identify with Structured App, and no other
redundancy among derivations: the two layerings of Map Right and Unit Right over a closure
operator, which the book notes are equivalent, keep two normal forms.

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
def joinMapL [f.IsApplicative] :
    {l r u : Ty B} → Mode Rule l r (.comp f u) → Mode Rule (.comp f l) r (.comp f u)
  | _, _, _, .mapR m => .ap m
  | _, _, _, m => .join (.mapL m)

theorem joinMapL_equiv [f.IsApplicative] (m : Mode G.Binary l r (.comp f u)) :
    joinMapL m ≈ Mode.join (f := f) (.mapL m) := by
  cases m with
  | mapR m => exact (join_mapL_mapR_equiv_ap m).symm
  | _ => exact .refl _

variable [DecidableEq B]

/-- Join over Map Right of a mode: Structured App, where the mode is a Map Left and the effect
is commutative. -/
def joinMapR [f.IsApplicative] :
    {l r u : Ty B} → Mode Rule l r (.comp f u) → Mode Rule l (.comp f r) (.comp f u)
  | _, _, _, .mapL m => if f.IsCommutative then .ap m else .join (.mapR (.mapL m))
  | _, _, _, m => .join (.mapR m)

/-- Join of a mode: Structured App, where the mode is the two maps in an order that merges the
effects as Structured App does. -/
def joinNormal [f.IsApplicative] :
    {l r u : Ty B} → Mode Rule l r (.comp f (.comp f u)) → Mode Rule l r (.comp f u)
  | _, _, _, .mapL m => joinMapL m
  | _, _, _, .mapR m => joinMapR m
  | _, _, _, m => .join m

/-- The normal form of a mode: Structured App for each Join over Map Left over Map Right, and at
a commutative effect for each Join over Map Right over Map Left. -/
def normalize : {l r u : Ty B} → Mode Rule l r u → Mode Rule l r u
  | _, _, _, .basic b => .basic b
  | _, _, _, .mapR m => .mapR m.normalize
  | _, _, _, .mapL m => .mapL m.normalize
  | _, _, _, .ap m h => .ap m.normalize h
  | _, _, _, .unitR m h => .unitR m.normalize h
  | _, _, _, .unitL m h => .unitL m.normalize h
  | _, _, _, .counit m => .counit m.normalize
  | _, _, _, .ejectR m => .ejectR m.normalize
  | _, _, _, .ejectL m => .ejectL m.normalize
  | _, _, _, .join m _ => joinNormal m.normalize
  | _, _, _, .lower m => .lower m.normalize

theorem joinMapR_equiv [f.IsApplicative] (m : Mode G.Binary l r (.comp f u)) :
    joinMapR m ≈ Mode.join (f := f) (.mapR m) := by
  cases m with
  | mapL m =>
    show (if f.IsCommutative then Mode.ap m else .join (.mapR (.mapL m))) ≈ _
    split_ifs with hc
    · exact (join_mapR_mapL_equiv_ap m).symm
    · exact .refl _
  | _ => exact .refl _

theorem joinNormal_equiv [f.IsApplicative] (m : Mode G.Binary l r (.comp f (.comp f u))) :
    joinNormal m ≈ Mode.join (f := f) m := by
  cases m with
  | mapL m => exact joinMapL_equiv m
  | mapR m => exact joinMapR_equiv m
  | _ => exact .refl _

/-- A mode and its normal form mean the same. -/
theorem normalize_equiv : ∀ {l r u : Ty B} (m : Mode G.Binary l r u), m.normalize ≈ m
  | _, _, _, .basic _ => .refl _
  | _, _, _, .mapR m => (normalize_equiv m).mapR
  | _, _, _, .mapL m => (normalize_equiv m).mapL
  | _, _, _, .ap m _ => (normalize_equiv m).ap
  | _, _, _, .unitR m _ => (normalize_equiv m).unitR
  | _, _, _, .unitL m _ => (normalize_equiv m).unitL
  | _, _, _, .counit m => (normalize_equiv m).counit
  | _, _, _, .ejectR m => (normalize_equiv m).ejectR
  | _, _, _, .ejectL m => (normalize_equiv m).ejectL
  | _, _, _, .join m _ => (joinNormal_equiv _).trans (normalize_equiv m).join
  | _, _, _, .lower m => (normalize_equiv m).lower

end Mode

namespace effectGrammar

variable [DecidableEq B] {G : Language (Ty B)} {D : B → Type}

/-- The map of the effect-driven grammar into itself that takes each mode to its normal form. -/
def normalize (G : Language (Ty B)) : effectGrammar G →ᴸ effectGrammar G :=
  .mapBinary Mode.normalize

/-- **Equal meanings.** Taking normal forms keeps the meaning of every symbol of the
effect-driven grammar, so a derivation and its normal form have one value, and so do two
derivations with one normal form: they differ, at some of their nodes, in the order in which
commuting effects are merged. -/
theorem normalize_isExpansionOn [M : G.Structure (Ty.Dom D)] :
    (normalize G).IsExpansionOn (effectGrammar.structure (M := M)) effectGrammar.structure :=
  Language.LHom.mapBinary_isExpansionOn fun g ↦ Mode.normalize_equiv g D

end effectGrammar

end Interpreter
