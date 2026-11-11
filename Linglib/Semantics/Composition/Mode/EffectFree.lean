module

public import Linglib.Semantics.Composition.Mode.Combine

/-!
# The effect-driven grammar without effects

A meta-mode needs an effect in a daughter, or a basic mode whose result has one. Daughters of
types with no effect in them therefore [combine by a basic mode
only](##Interpreter.Mode.exists_eq_basic), and over a lexicon of such types [the effect-driven
interpreter gives the values of the grammar it was built
over](##Interpreter.values_effectDriven_of_effectFree).

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

/-- A type without effects has no continuation to close. -/
theorem Ty.EffectFree.evaluated : ∀ {a : Ty B}, a.EffectFree → a.Evaluated
  | .t, _ | .base _, _ => trivial
  | .fn _ _, h => h.2.evaluated

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
  | _, _, _, .join _ m, hl, hr => by
    obtain ⟨b, rfl⟩ := Mode.exists_eq_basic hR m hl hr
    exact (hR b hl hr).elim
  | _, _, _, .lower m, hl, hr => by
    obtain ⟨b, rfl⟩ := Mode.exists_eq_basic hR m hl hr
    exact (hR b hl hr).elim

/-- For daughters of types without effects `Ty.combine` finds the basic rules and nothing
else. -/
theorem Ty.combine_of_effectFree [DecidableEq B] {Rule : Ty B → Ty B → Ty B → Type}
    {find : (l r : Ty B) → List (Σ u, Rule l r u)}
    (hR : ∀ {l r u : Ty B}, Rule l r u → l.EffectFree → r.EffectFree → u.EffectFree)
    {l r : Ty B} (hl : l.EffectFree) (hr : r.EffectFree) :
    Ty.combine find l r = (find l r).map fun p ↦ ⟨p.1, .basic p.2⟩ := by
  have hj (p : Σ u, Rule l r u) :
      Mode.closure (⟨p.1, .basic p.2⟩ : Σ u, Mode Rule l r u) = [⟨p.1, .basic p.2⟩] := by
    obtain ⟨u, b⟩ := p
    have hu := hR b hl hr
    rcases u with _ | _ | _ | _
    · rfl
    · rfl
    · simp [Mode.closure, Ty.size, Mode.closureAux, Mode.joins, Mode.lowers]
    · exact hu.elim
  have hbasic : ((find l r).map fun p ↦ (⟨p.1, .basic p.2⟩ : Σ u, Mode Rule l r u)).flatMap
      Mode.closure = (find l r).map fun p ↦ ⟨p.1, .basic p.2⟩ := by
    rw [List.flatMap_map]
    simp only [hj]
    exact List.map_eq_flatMap.symm
  rw [← hbasic]
  unfold Ty.combine Ty.combineWith
  rw [show 3 * (l.size + r.size) + 3 = (3 * (l.size + r.size) + 2) + 1 from rfl]
  generalize 3 * (l.size + r.size) + 2 = k
  rw [Ty.combineAux]
  congr 1
  all_goals simp_all
  all_goals
    intros; intro h; subst h
    first
    | exact hl.elim | exact hr.elim | exact hl.1.elim | exact hl.2.elim
    | exact hr.1.elim | exact hr.2.elim

/-- Over a lexicon whose items have types without effects, the values a grammar that keeps to
such types gives a bare structure have types without effects. -/
theorem EffectFree.of_mem_values {G : Language (Ty B)} [G.LocallyFinite] (hG : G.EffectFree)
    {D : Ty B → Type} (M : G.Structure D) {Lx : Type} {W : Ty B → Type}
    (ρ : ∀ {a : Ty B}, W a → D a) {lex : Lx → List (Σ a, W a)}
    (hlex : ∀ x, ∀ p ∈ lex x, p.1.EffectFree) :
    ∀ (s : Skeleton Node Lx), ∀ d ∈ (typeDriven G).values M ρ lex s, d.1.EffectFree
  | .leaf x, d, hd => by
    rw [values_leaf] at hd
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hd
    exact hlex x p hp
  | .unary n s, d, hd => by
    rw [values_unary] at hd
    obtain ⟨e, he, hd⟩ := List.mem_flatMap.1 hd
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hd
    exact hG.unary r.2 (EffectFree.of_mem_values hG M ρ hlex s e he)
  | .binary n s₁ s₂, d, hd => by
    rw [values_binary] at hd
    obtain ⟨e₁, he₁, hd⟩ := List.mem_flatMap.1 hd
    obtain ⟨e₂, he₂, hd⟩ := List.mem_flatMap.1 hd
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hd
    exact hG.binary m.2 (EffectFree.of_mem_values hG M ρ hlex s₁ e₁ he₁)
      (EffectFree.of_mem_values hG M ρ hlex s₂ e₂ he₂)

/-- **The effect-driven grammar is conservative.** Over a lexicon whose items have types without
effects, the effect-driven interpreter over a grammar that keeps to such types gives each bare
structure the values the grammar's own type-driven interpreter gives it, in the same order: the
meta-modes add no reading, and remove none. -/
theorem values_effectDriven_of_effectFree [DecidableEq B] {G : Language (Ty B)}
    [G.LocallyFinite] (hG : G.EffectFree) {D : B → Type} [M : G.Structure (Ty.Dom D)]
    {Lx : Type} {W : Ty B → Type} (ρ : ∀ {a : Ty B}, W a → a.Dom D)
    {lex : Lx → List (Σ a, W a)} (hlex : ∀ x, ∀ p ∈ lex x, p.1.EffectFree) :
    ∀ s : Skeleton Node Lx, (effectDriven G).values effectGrammar.structure ρ lex s =
      (typeDriven G).values M ρ lex s
  | .leaf x => by rw [values_leaf, values_leaf]
  | .unary n s => by
    rw [values_unary, values_unary, values_effectDriven_of_effectFree hG ρ hlex s]
    rfl
  | .binary n s₁ s₂ => by
    rw [values_binary, values_binary, values_effectDriven_of_effectFree hG ρ hlex s₁,
      values_effectDriven_of_effectFree hG ρ hlex s₂]
    refine List.flatMap_congr fun d₁ h₁ ↦ List.flatMap_congr fun d₂ h₂ ↦ ?_
    have hl := EffectFree.of_mem_values hG M ρ hlex s₁ d₁ h₁
    have hr := EffectFree.of_mem_values hG M ρ hlex s₂ d₂ h₂
    have hc : (effectDriven G).binary n d₁.1 d₂.1 =
        (Language.LocallyFinite.binaryRules (L := G) d₁.1 d₂.1).map
          fun p ↦ ⟨p.1, .basic p.2⟩ := by
      cases n with
      | island =>
        simp only [effectDriven, Ty.combine_of_effectFree hG.binary hl hr]
        refine List.filter_eq_self.2 fun p hp ↦ ?_
        obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
        exact decide_eq_true (hG.binary q.2 hl hr).evaluated
      | branch => simp only [effectDriven, Ty.combine_of_effectFree hG.binary hl hr]
      | index k => simp only [effectDriven, Ty.combine_of_effectFree hG.binary hl hr]
    rw [hc, List.map_map]
    rfl

end Interpreter
