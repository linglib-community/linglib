module

public import Linglib.Semantics.Composition.Mode.Combine
public import Linglib.Semantics.Composition.Constituency

/-!
# The effect-driven grammar without effects

A meta-mode needs an effect in a daughter, or a basic mode whose result has one. Daughters of
types with no effect in them therefore [combine by a basic mode
only](##Interpreter.Mode.exists_eq_basic), and over a lexicon of such types [the effect-driven
interpreter admits the derivations of the grammar it was built
over](##PhraseStructure.Tree.derivs_effectDriven_of_effectFree), so that [a tree has the same
values in any structure](##PhraseStructure.Tree.values_effectDriven_of_effectFree).

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
  | _, _, _, .join _ m, hl, hr => by
    obtain ⟨b, rfl⟩ := Mode.exists_eq_basic hR m hl hr
    exact (hR b hl hr).elim
  | _, _, _, .lower m, hl, hr => by
    obtain ⟨b, rfl⟩ := Mode.exists_eq_basic hR m hl hr
    exact (hR b hl hr).elim

/-- For daughters of types without effects `Ty.combine` finds the basic rules and nothing
else. -/
theorem Ty.combine_of_effectFree [DecidableEq B] {Rule : Ty B → Ty B → Ty B → Type}
    {find : (l r : Ty B) → List (Sigma (Rule l r))}
    (hR : ∀ {l r u : Ty B}, Rule l r u → l.EffectFree → r.EffectFree → u.EffectFree)
    {l r : Ty B} (hl : l.EffectFree) (hr : r.EffectFree) :
    Ty.combine find l r = (find l r).map fun p ↦ ⟨p.1, .basic p.2⟩ := by
  have hj (p : Sigma (Rule l r)) :
      Mode.closure (⟨p.1, .basic p.2⟩ : Sigma (Mode Rule l r)) = [⟨p.1, .basic p.2⟩] := by
    obtain ⟨u, b⟩ := p
    have hu := hR b hl hr
    rcases u with _ | _ | _ | _
    · rfl
    · rfl
    · simp [Mode.closure, Ty.size, Mode.closureAux, Mode.joins, Mode.lowers]
    · exact hu.elim
  have hbasic : ((find l r).map fun p ↦ (⟨p.1, .basic p.2⟩ : Sigma (Mode Rule l r))).flatMap
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

section

variable [DecidableEq B] {G : Language (Ty B)} [G.LocallyFinite] {D : B → Type}
  [M : G.Structure (Ty.Dom D)] {N : Type}

/-- On daughters of types without effects the effect-driven interpreter admits the basic rules
of the grammar and nothing else. -/
theorem binary_effectDriven_of_effectFree (hG : G.EffectFree) {l r : Ty B}
    (hl : l.EffectFree) (hr : r.EffectFree) :
    (effectDriven G : Interpreter (effectGrammar G) N).binary l r =
      (Language.LocallyFinite.binaryRules (L := G) l r).map fun p ↦ ⟨p.1, .basic p.2⟩ :=
  Ty.combine_of_effectFree hG.binary hl hr

end

end Interpreter

namespace PhraseStructure.Tree

open ManySorted ManySorted.Language Interpreter

variable {B : Type} {C Lx : Type} [DecidableEq B] {G : Language (Ty B)} [G.LocallyFinite]
  {D : B → Type} [M : G.Structure (Ty.Dom D)] {W : Ty B → Type} {lex : Lx ⊕ ℕ → List (Sigma W)}

/-- **The effect-driven grammar is conservative.** Over a lexicon whose items have types without
effects, the derivations the effect-driven interpreter admits over a tree are those of the
grammar's own type-driven interpreter, each rule read as its basic mode, in the same order: the
meta-modes add no derivation, and remove none. -/
theorem derivs_effectDriven_of_effectFree (hG : G.EffectFree)
    (hlex : ∀ x, ∀ p ∈ lex x, p.1.EffectFree) (t : Tree C Lx) :
    t.derivs (effectDriven G) lex =
      (t.derivs (typeDriven G) lex).map fun d ↦ ⟨d.1, (effectGrammar.basic G).onTerm d.2⟩ := by
  have ha : (t.derivs (typeDriven G) lex).map (fun d ↦
        (⟨d.1, (effectGrammar.basic G).onTerm d.2⟩ : Sigma (Deriv (effectGrammar G) W))) =
      t.values (typeDriven G)
        ((effectGrammar.basic G).reduct (Term.structure (effectGrammar G) W)) Deriv.leaf lex := by
    rw [values_eq_fold]
    exact RoseTree.fold_hom _ (fun l Xs ↦ map_nodeValues (typeDriven G) (Term.structure G W)
      Deriv.leaf lex (fun _ d ↦ (effectGrammar.basic G).onTerm d) (fun _ _ ↦ rfl)
      (fun _ _ _ ↦ rfl) (fun _ ↦ rfl) l Xs) t
  rw [ha, derivs_eq_values]
  refine values_congr (I := effectDriven G) (J := typeDriven G) Ty.EffectFree hlex
    (fun n X hX ↦ ⟨rfl, fun d hd ↦ ?_⟩) (fun {X Y} hX hY ↦ ⟨?_, fun d hd ↦ ?_⟩) t
  · obtain ⟨d₁, h₁, r, -, rfl⟩ := mem_unaryValues.1 hd
    exact hG.unary r.2 (hX d₁ h₁)
  · refine List.flatMap_congr fun ⟨a, x⟩ h₁ ↦ List.flatMap_congr fun ⟨b, y⟩ h₂ ↦ ?_
    dsimp only
    rw [binary_effectDriven_of_effectFree hG (hX _ h₁) (hY _ h₂), List.map_map]
    rfl
  · obtain ⟨d₁, h₁, d₂, h₂, m, -, rfl⟩ := mem_binaryValues.1 hd
    exact hG.binary m.2 (hX d₁ h₁) (hY d₂ h₂)

/-- Over a lexicon whose items have types without effects, the effect-driven interpreter gives
each tree, in any structure, the values the grammar's type-driven interpreter gives it. -/
theorem values_effectDriven_of_effectFree (hG : G.EffectFree)
    (ρ : ∀ {a : Ty B}, W a → a.Dom D) (hlex : ∀ x, ∀ p ∈ lex x, p.1.EffectFree)
    (t : Tree C Lx) :
    t.values (effectDriven G) effectGrammar.structure ρ lex =
      t.values (typeDriven G) M ρ lex := by
  rw [values_eq_map_derivs, derivs_effectDriven_of_effectFree hG hlex, List.map_map,
    values_eq_map_derivs]
  exact List.map_congr_left fun d _ ↦ congrArg (Sigma.mk d.1)
    (LHom.realize_onTerm effectGrammar.basic_isExpansionOn ρ d.2)

end PhraseStructure.Tree
