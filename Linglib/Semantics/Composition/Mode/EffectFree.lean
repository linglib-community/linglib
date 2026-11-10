module

public import Linglib.Semantics.Composition.Mode.Combine
public import Linglib.Semantics.Composition.Constituency

/-!
# The effect-driven grammar without effects

A meta-mode needs an effect in a daughter, or a basic mode whose result has one. Daughters of
types with no effect in them therefore [combine by a basic mode
only](##Interpreter.Mode.exists_eq_basic), and over a lexicon of such types [the effect-driven
interpreter gives the values of the grammar it was built
over](##PhraseStructure.Tree.values_effectDriven_of_effectFree).

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

end Interpreter

namespace PhraseStructure.Tree

open ManySorted Interpreter

variable {B : Type} {C Lx : Type}

/-- **The effect-driven grammar is conservative.** Over a lexicon whose items have types without
effects, the effect-driven interpreter over a grammar that keeps to such types gives each tree
the values the grammar's own type-driven interpreter gives it, in the same order: the meta-modes
add no reading, and remove none. -/
theorem values_effectDriven_of_effectFree [DecidableEq B] {G : Language (Ty B)}
    [G.LocallyFinite] (hG : G.EffectFree) {D : B → Type} [M : G.Structure (Ty.Dom D)]
    {W : Ty B → Type} (ρ : ∀ {a : Ty B}, W a → a.Dom D)
    {lex : Lx ⊕ ℕ → List (Σ a, W a)} (hlex : ∀ x, ∀ p ∈ lex x, p.1.EffectFree)
    (t : Tree C Lx) (island : C → Bool) :
    t.values (effectDriven G) effectGrammar.structure ρ lex island =
      t.values (typeDriven G) M ρ lex island := by
  refine (RoseTree.rel_fold
    (fun (X Y : List (Σ a, Ty.Dom D a)) ↦ X = Y ∧ ∀ d ∈ Y, d.1.EffectFree)
    (fun l Xs Ys h ↦ ?_) t).1
  match l, Xs, Ys, h with
  | .terminal _ w, [], [], _ =>
    refine ⟨rfl, fun d hd ↦ ?_⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hd
    exact hlex _ p hp
  | .trace n _, [], [], _ =>
    refine ⟨rfl, fun d hd ↦ ?_⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hd
    exact hlex _ p hp
  | .bind n _, [_], [Y], .cons ⟨rfl, hY⟩ .nil =>
    refine ⟨rfl, fun d hd ↦ ?_⟩
    obtain ⟨d₁, h₁, r, -, rfl⟩ := mem_unaryValues.1 hd
    exact hG.unary r.2 (hY d₁ h₁)
  | .phrase _ _, [_], [Y], .cons h .nil => exact h
  | .phrase c _, [_, _], [Y₁, Y₂], .cons ⟨rfl, h₁⟩ (.cons ⟨rfl, h₂⟩ .nil) =>
    refine ⟨?_, fun d hd ↦ ?_⟩
    · refine List.flatMap_congr fun ⟨a, x⟩ hd₁ ↦ List.flatMap_congr fun ⟨b, y⟩ hd₂ ↦ ?_
      have hl : a.EffectFree := h₁ _ hd₁
      have hr : b.EffectFree := h₂ _ hd₂
      have hc : (effectDriven G).binary (if island c then .island else .branch) a b =
          (Language.LocallyFinite.binaryRules (L := G) a b).map
            fun p ↦ ⟨p.1, .basic p.2⟩ := by
        split
        · simp only [effectDriven, Ty.combine_of_effectFree hG.binary hl hr]
          refine List.filter_eq_self.2 fun p hp ↦ ?_
          obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
          exact decide_eq_true (hG.binary q.2 hl hr).evaluated
        · simp only [effectDriven, Ty.combine_of_effectFree hG.binary hl hr]
      dsimp only
      rw [hc, List.map_map]
      rfl
    · obtain ⟨d₁, hd₁, d₂, hd₂, m, -, rfl⟩ := mem_binaryValues.1 hd
      exact hG.binary m.2 (h₁ d₁ hd₁) (h₂ d₂ hd₂)
  | .terminal _ _, _ :: _, _ :: _, _ | .trace _ _, _ :: _, _ :: _, _ | .bind _ _, [], [], _
  | .bind _ _, _ :: _ :: _, _ :: _ :: _, _ | .phrase _ _, [], [], _
  | .phrase _ _, _ :: _ :: _ :: _, _ :: _ :: _ :: _, _ => exact ⟨rfl, fun _ hd ↦ nomatch hd⟩

end PhraseStructure.Tree
