module

public import Linglib.Semantics.Composition.Mode.Combine

/-!
# The effect-driven grammar without effects

A meta-mode needs an effect in a daughter, or a basic mode whose result has one. Daughters of
types with no effect in them therefore [combine by a basic mode
only](##Interpreter.Mode.exists_eq_basic), and the search lists for them [the basic rules and
nothing else](##Interpreter.Ty.combine_of_effectFree), [whatever the
inventory](##Interpreter.Ty.combineWithin_of_effectFree).

## Main definitions

* `Interpreter.Ty.EffectFree`: the types with no effect in them.
* `ManySorted.Language.EffectFree`: the grammars whose rules keep to those types.

## References

* [bumford-charlow-2026]
-/

@[expose] public section

open ManySorted

namespace Interpreter

variable {B : Type}

/-! ### Conservativity over the types without effects -/

/-- A type with no effect anywhere in it. -/
def Ty.EffectFree : Ty B → Prop
  | .t | .base _ => True
  | .fn a b => a.EffectFree ∧ b.EffectFree
  | .comp _ _ => False

/-- A grammar keeps to the types without effects when its rules give daughters of such types a
mother of one. -/
structure _root_.ManySorted.Language.EffectFree (G : Language (Ty B)) : Prop where
  /-- The type shifts. -/
  unary {a b : Ty B} : G.Unary a b → a.EffectFree → b.EffectFree
  /-- The modes of combination. -/
  binary {l r u : Ty B} : G.Binary l r u → l.EffectFree → r.EffectFree → u.EffectFree

/-- Daughters of types without effects combine by a basic mode only: every meta-mode needs an
effect in a daughter, or a basic mode whose result has one. -/
theorem Mode.exists_eq_basic {Rule : Ty B → Ty B → Ty B → Type}
    (hR : ∀ {l r u : Ty B}, Rule l r u → l.EffectFree → r.EffectFree → u.EffectFree) :
    ∀ {l r u : Ty B} (m : Mode Rule l r u), l.EffectFree → r.EffectFree → ∃ b, m = .basic b
  | _, _, _, .basic b, _, _ => ⟨b, rfl⟩
  | _, _, _, .mapR _, _, hr => hr.elim
  | _, _, _, .mapL _, hl, _ => hl.elim
  | _, _, _, .ap _ _, hl, _ => hl.elim
  | _, _, _, .unitR _ _, hl, _ => hl.1.elim
  | _, _, _, .unitL _ _, _, hr => hr.1.elim
  | _, _, _, .counit _, hl, _ => hl.elim
  | _, _, _, .ejectR _, _, hr => hr.2.elim
  | _, _, _, .ejectL _, hl, _ => hl.2.elim
  | _, _, _, .join m _, hl, hr => by
    obtain ⟨b, rfl⟩ := Mode.exists_eq_basic hR m hl hr
    exact (hR b hl hr).elim
  | _, _, _, .lower m, hl, hr => by
    obtain ⟨b, rfl⟩ := Mode.exists_eq_basic hR m hl hr
    exact (hR b hl hr).elim

/-- A basic mode whose result has no effect has no Join and no Lower. -/
private theorem Mode.closure_basic [DecidableEq B] {Rule : Ty B → Ty B → Ty B → Type}
    {l r u : Ty B}
    (b : Rule l r u) (hu : u.EffectFree) :
    Mode.closure (⟨u, .basic b⟩ : Sigma (Mode Rule l r)) = [⟨u, .basic b⟩] := by
  rcases u with _ | _ | _ | _
  · rfl
  · rfl
  · simp [Mode.closure, Ty.size, Mode.closureAux, Mode.joins, Mode.lowers]
  · exact hu.elim

/-- For daughters of types without effects, a search that closes each basic mode to itself finds
the basic rules and nothing else: no meta-mode applies to a type without effects. -/
private theorem Ty.combineWith_of_effectFree [DecidableEq B]
    {Rule : Ty B → Ty B → Ty B → Type} (inv : MetaMode → Eff B → Prop) [DecidableRel inv]
    {find : (l r : Ty B) → List (Sigma (Rule l r))}
    {close : {l r : Ty B} → Sigma (Mode Rule l r) → List (Sigma (Mode Rule l r))} {l r : Ty B}
    (hclose : ∀ p : Sigma (Rule l r), close ⟨p.1, .basic p.2⟩ = [⟨p.1, .basic p.2⟩])
    (hl : l.EffectFree) (hr : r.EffectFree) :
    Ty.combineWith inv find close l r = (find l r).map fun p ↦ ⟨p.1, .basic p.2⟩ := by
  have hbasic : ((find l r).map fun p ↦ (⟨p.1, .basic p.2⟩ : Sigma (Mode Rule l r))).flatMap
      close = (find l r).map fun p ↦ ⟨p.1, .basic p.2⟩ := by
    rw [List.flatMap_map]
    simp only [hclose]
    exact List.map_eq_flatMap.symm
  rw [← hbasic, Ty.combineWith_eq_combineStep, Ty.combineStep]
  congr 1
  all_goals simp_all
  all_goals
    intros; intro h; subst h
    first
    | exact hl.elim | exact hr.elim | exact hl.1.elim | exact hl.2.elim
    | exact hr.1.elim | exact hr.2.elim

/-- For daughters of types without effects `Ty.combine` finds the basic rules and nothing
else. -/
theorem Ty.combine_of_effectFree [DecidableEq B] {Rule : Ty B → Ty B → Ty B → Type}
    {find : (l r : Ty B) → List (Sigma (Rule l r))}
    (hR : ∀ {l r u : Ty B}, Rule l r u → l.EffectFree → r.EffectFree → u.EffectFree)
    {l r : Ty B} (hl : l.EffectFree) (hr : r.EffectFree) :
    Ty.combine find l r = (find l r).map fun p ↦ ⟨p.1, .basic p.2⟩ :=
  Ty.combineWith_of_effectFree _ (fun p ↦ Mode.closure_basic p.2 (hR p.2 hl hr)) hl hr

/-- For daughters of types without effects the search of any inventory finds the basic rules
and nothing else. -/
theorem Ty.combineWithin_of_effectFree [DecidableEq B] {Rule : Ty B → Ty B → Ty B → Type}
    (inv : MetaMode → Eff B → Prop) [DecidableRel inv]
    {find : (l r : Ty B) → List (Sigma (Rule l r))}
    (hR : ∀ {l r u : Ty B}, Rule l r u → l.EffectFree → r.EffectFree → u.EffectFree)
    {l r : Ty B} (hl : l.EffectFree) (hr : r.EffectFree) :
    Ty.combineWithin inv find l r = (find l r).map fun p ↦ ⟨p.1, .basic p.2⟩ :=
  Ty.combineWith_of_effectFree inv
    (fun p ↦ by simp [Mode.closure_basic p.2 (hR p.2 hl hr), Mode.Within]) hl hr

end Interpreter
