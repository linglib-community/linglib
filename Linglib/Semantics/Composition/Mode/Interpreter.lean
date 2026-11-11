module

public import Linglib.Semantics.Composition.Mode.EffectFree
public import Linglib.Semantics.Composition.Mode.Pointwise
public import Linglib.Semantics.Composition.Mode.Binder
public import Linglib.Semantics.Composition.CallByValue
public import Linglib.Semantics.Composition.Interpret

/-!
# The effect-driven interpreter

The effect-driven grammar read off a tree: a binary node admits the modes the search finds for
its daughters, all of them or those of an inventory, and a binder node the binder of its index.
What the grammar's theorems say of types and derivations they say here of the values of a tree.
Over a lexicon without effects [the interpreter admits the derivations of the grammar it was built
over](##PhraseStructure.Tree.derivs_effectDriven_of_effectFree); in a grammar pointwise at an
effect [a tree has its values in the structure on
computations](##PhraseStructure.Tree.values_effectDrivenWithin_pointwise); and with the binder
[its values are those relative to assignments](##PhraseStructure.Tree.values_withBinder), which
over words without effects are [the values of Heim and Kratzer's
rules](##PhraseStructure.Tree.values_withBinder_of_effectFree).

## Main definitions

* `Interpreter.effectDriven`, `Interpreter.effectDrivenWithin`: the interpreters of the
  effect-driven grammar and of its inventories.
* `Interpreter.withBinder`: an interpreter that admits the binder at an index.
* `Interpreter.partialValued`: the interpreter in which every constituent is a partial value.

## References

* [bumford-charlow-2026]
* [heim-kratzer-1998]
-/

@[expose] public section

open ManySorted

namespace Interpreter

variable {B : Type}

/-- The interpreter of Bumford and Charlow's effect-driven grammar over a grammar: a binary node
admits every mode that `Ty.combine` finds for its daughters, which are all the modes of the
grammar. -/
def effectDriven [DecidableEq B] (G : Language (Ty B)) [G.LocallyFinite] {N : Type} :
    Interpreter (effectGrammar G) N where
  bind _ _ := []
  binary := Ty.combine (Language.LocallyFinite.binaryRules (L := G))

/-- A node admits every mode of the grammar that combines its daughters. -/
theorem mem_binary_effectDriven [DecidableEq B] {G : Language (Ty B)} [G.LocallyFinite]
    {N : Type} {l r : Ty B} (m : Sigma (Mode G.Binary l r)) :
    m ∈ (effectDriven G : Interpreter (effectGrammar G) N).binary l r :=
  Ty.mem_combine (find := Language.LocallyFinite.binaryRules (L := G))
    (fun b ↦ Language.LocallyFinite.mem_symbols b) m.2

/-- The effect-driven interpreter of a grammar with an inventory of meta-modes: a node admits the
modes for its daughters that keep to the inventory. -/
def effectDrivenWithin [DecidableEq B] (inv : MetaMode → Eff B → Prop)
    [DecidableRel inv] (G : Language (Ty B)) [G.LocallyFinite] {N : Type} :
    Interpreter (effectGrammar G) N where
  bind _ _ := []
  binary := Ty.combineWithin inv (Language.LocallyFinite.binaryRules (L := G))

/-- A node admits exactly the modes that keep to the inventory. -/
theorem mem_binary_effectDrivenWithin [DecidableEq B] {G : Language (Ty B)} [G.LocallyFinite]
    {N : Type} {inv : MetaMode → Eff B → Prop} [DecidableRel inv] {l r : Ty B}
    {m : Sigma (Mode G.Binary l r)} :
    m ∈ (effectDrivenWithin inv G : Interpreter (effectGrammar G) N).binary l r ↔
      m.2.Within inv :=
  Ty.mem_combineWithin (find := Language.LocallyFinite.binaryRules (L := G))
    fun b ↦ Language.LocallyFinite.mem_symbols b

section

variable [DecidableEq B] {G : Language (Ty B)} [G.LocallyFinite] {D : B → Type}
  [M : G.Structure (Ty.Dom D)] {N : Type}

/-- On daughters of types without effects the effect-driven interpreter of any inventory admits
the basic rules of the grammar and nothing else. -/
theorem binary_effectDrivenWithin_of_effectFree (inv : MetaMode → Eff B → Prop)
    [DecidableRel inv] (hG : G.EffectFree) {l r : Ty B} (hl : l.EffectFree)
    (hr : r.EffectFree) :
    (effectDrivenWithin inv G : Interpreter (effectGrammar G) N).binary l r =
      (Language.LocallyFinite.binaryRules (L := G) l r).map fun p ↦ ⟨p.1, .basic p.2⟩ :=
  Ty.combineWithin_of_effectFree inv hG.binary hl hr

/-- On daughters of types without effects the effect-driven interpreter admits the basic rules
of the grammar and nothing else. -/
theorem binary_effectDriven_of_effectFree (hG : G.EffectFree) {l r : Ty B}
    (hl : l.EffectFree) (hr : r.EffectFree) :
    (effectDriven G : Interpreter (effectGrammar G) N).binary l r =
      (Language.LocallyFinite.binaryRules (L := G) l r).map fun p ↦ ⟨p.1, .basic p.2⟩ :=
  Ty.combine_of_effectFree hG.binary hl hr

end

theorem binary_effectDrivenWithin_pointwise [DecidableEq B] {P : Eff B → Prop} [DecidablePred P]
    {G : Language (Ty B)} [G.LocallyFinite] {N : Type} {f : Eff B} (hf : P f)
    [ha : f.IsApplicative] {l r : Ty B}
    [∀ u : Ty B, IsEmpty (G.Binary (.comp f l) (.comp f r) u)] :
    (effectDrivenWithin (MetaMode.pointwise P) G : Interpreter (effectGrammar G) N).binary
        (.comp f l) (.comp f r) =
      ((effectDrivenWithin (MetaMode.pointwise P) G : Interpreter (effectGrammar G) N).binary
        l r).map fun p ↦ ⟨.comp f p.1, .ap p.2 ha⟩ :=
  Ty.combineWithin_pointwise hf (List.eq_nil_iff_forall_not_mem.2 fun p _ ↦ isEmptyElim p.2)

/-- An interpreter with the binder: a binder node admits the binder of its index,
and a binary node admits what the interpreter admits. -/
def withBinder [DecidableEq B] {L : Language.{0, 0} (Ty B)} (I : Interpreter L ℕ) (g : Ty B)
    (Γ : ℕ → Ty B) : Interpreter (L.sum (binding g Γ)) ℕ where
  bind n a := (Binder.rules g Γ n a).map fun r ↦ ⟨r.1, Language.Sum.inr r.2⟩
  binary l r := (I.binary l r).map fun m ↦ ⟨m.1, .inl m.2⟩

/-- The partial-valued interpreter: every constituent is a partial value, and sisters combine by
a rule of the grammar on their values where both are defined, a partial result of the rule
flattened. A function applied to an undefined argument is undefined. -/
def partialValued [DecidableEq B] (G : Language (Ty B)) [G.LocallyFinite] {N : Type} :
    Interpreter (effectGrammar G) N where
  bind _ _ := []
  binary
    | .comp .M l, .comp .M r =>
      (Language.LocallyFinite.binaryRules (L := G) l r).map fun
        | ⟨.comp .M u, p⟩ => ⟨.comp .M u, .join (.ap (.basic p))⟩
        | ⟨u, p⟩ => ⟨.comp .M u, .ap (.basic p)⟩
    | _, _ => []

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
  rw [derivs_eq_values, derivs_eq_values]
  refine (values_rel
    (fun (X : List (Sigma (Deriv (effectGrammar G) W))) (Y : List (Sigma (Deriv G W))) ↦
      X = Y.map (fun d ↦ ⟨d.1, (effectGrammar.basic G).onTerm d.2⟩) ∧ ∀ d ∈ Y, d.1.EffectFree)
    ⟨rfl, fun _ hd ↦ nomatch hd⟩ (fun x ↦ ⟨by rw [List.map_map]; rfl, fun d hd ↦ ?_⟩) ?_ ?_ t).1
  -- a word and a trace: the items they may be
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hd
    exact hlex x p hp
  -- a binder: neither interpreter admits a rule at one
  · rintro n _ Y ⟨rfl, -⟩
    rw [bindValues_eq_nil fun _ ↦ rfl, bindValues_eq_nil fun _ ↦ rfl]
    exact ⟨rfl, fun _ hd ↦ nomatch hd⟩
  -- a binary node: its daughters' types have no effects, so only basic modes combine them
  · rintro _ Y₁ _ Y₂ ⟨rfl, h₁⟩ ⟨rfl, h₂⟩
    refine ⟨?_, fun d hd ↦ ?_⟩
    · rw [map_binaryValues (I := typeDriven G)
        (M' := (effectGrammar.basic G).reduct (Term.structure (effectGrammar G) W))
        (fun _ d ↦ (effectGrammar.basic G).onTerm d) (fun _ _ _ ↦ rfl)]
      refine List.flatMap_congr fun ⟨a, x⟩ hx ↦ List.flatMap_congr fun ⟨b, y⟩ hy ↦ ?_
      have ha : a.EffectFree := by
        obtain ⟨d, hd, hde⟩ := List.mem_map.1 hx
        cases hde
        exact h₁ d hd
      have hb : b.EffectFree := by
        obtain ⟨d, hd, hde⟩ := List.mem_map.1 hy
        cases hde
        exact h₂ d hd
      dsimp only
      rw [binary_effectDriven_of_effectFree hG ha hb, List.map_map]
      rfl
    · obtain ⟨d₁, hd₁, d₂, hd₂, m, -, rfl⟩ := mem_binaryValues.1 hd
      exact hG.binary m.2 (h₁ d₁ hd₁) (h₂ d₂ hd₂)

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

namespace PhraseStructure.Tree

open ManySorted.Language Interpreter

variable {B : Type} [DecidableEq B] {P : Eff B → Prop} [DecidablePred P] {G : Language (Ty B)}
  [G.LocallyFinite] {D : B → Type} [M : G.Structure (Ty.Dom D)] {C Lx : Type}
  {W W' : Ty B → Type} {f : Eff B}

/-- In a grammar pointwise at `f`, with no basic rule for two daughters that
carry `f`, the values of a tree over a lexicon whose items all carry `f` are its values in
`effectGrammar.pointwise f` over the results of the items. -/
theorem values_effectDrivenWithin_pointwise
    [∀ l r u : Ty B, IsEmpty (G.Binary (.comp f l) (.comp f r) u)] (hf : P f)
    [ha : f.IsApplicative]
    {ρ : ∀ {a : Ty B}, W a → (Ty.comp f a).Dom D} {ρ' : ∀ {a : Ty B}, W' a → a.Dom D}
    {lex : Lx ⊕ ℕ → List (Sigma W)} {lex' : Lx ⊕ ℕ → List (Sigma W')}
    (hlex : ∀ x, (lex' x).map (fun p ↦ (⟨p.1, ρ' p.2⟩ : Sigma (Ty.Dom D))) =
      (lex x).map fun p ↦ ⟨.comp f p.1, ρ p.2⟩)
    (t : Tree C Lx) :
    t.values (effectDrivenWithin (MetaMode.pointwise P) G) effectGrammar.structure ρ' lex' =
      (t.values (effectDrivenWithin (MetaMode.pointwise P) G) (effectGrammar.pointwise f)
        ρ lex).map fun d ↦ ⟨.comp f d.1, d.2⟩ := by
  refine values_eq_map_of_types (Ty.comp f) (fun _ ↦ True) hlex (fun _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ ?_) (fun _ _ _ _ _ _ ↦ trivial) t
  rw [binary_effectDrivenWithin_pointwise hf, List.map_map]
  rfl

end PhraseStructure.Tree

namespace PhraseStructure.Tree

open ManySorted.Language Interpreter

variable {B : Type} [DecidableEq B] {P : Eff B → Prop} [DecidablePred P]
  {L : Language.{0, 0} (Ty B)} [L.LocallyFinite] {D : B → Type} [M : L.Structure (Ty.Dom D)]
  {C Lx : Type} {W W' : Ty B → Type} {g : Ty B} {Γ : ℕ → Ty B}
  [∀ l r u : Ty B, IsEmpty (L.Binary (.comp (.R g) l) (.comp (.R g) r) u)]
  {ρ : ∀ {a : Ty B}, W a → (Ty.comp (.R g) a).Dom D} {ρ' : ∀ {a : Ty B}, W' a → a.Dom D}
  {lex : Lx ⊕ ℕ → List (Sigma W)} {lex' : Lx ⊕ ℕ → List (Sigma W')}

/-- **Assignments are an effect.** In a grammar pointwise at reading an assignment, over a
lexicon whose every item reads one, the values of a tree with the binder at its indices are its
values relative to assignments, with abstraction over its indices: the assignment may be a
parameter of the interpretation or a datum in the types. -/
theorem values_withBinder (hf : P (.R g)) (E : Assignments (g.Dom D) (Ty.Dom D) Γ)
    (hlex : ∀ x, (lex' x).map (fun p ↦ (⟨p.1, ρ' p.2⟩ : Sigma (Ty.Dom D))) =
      (lex x).map fun p ↦ ⟨.comp (.R g) p.1, ρ p.2⟩)
    (t : Tree C Lx) :
    t.values ((effectDrivenWithin (MetaMode.pointwise P) L).withBinder g Γ)
        (effectGrammar.structure.sum (binding.structure E)) ρ' lex' =
      (t.values ((effectDrivenWithin (MetaMode.pointwise P) L).withAbstraction Γ)
        (withAbstraction.structure (M := effectGrammar.structure) E) ρ lex).map
          fun d ↦ ⟨.comp (.R g) d.1, d.2⟩ := by
  refine values_eq_map_of_types (Ty.comp (.R g)) (fun _ ↦ True) hlex (fun _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ by simp [withBinder, Interpreter.withAbstraction])
    (fun _ _ _ _ _ ↦ trivial) (fun _ _ _ _ _ _ ↦ ?_) (fun _ _ _ _ _ _ ↦ trivial) t
  simp only [withBinder, Interpreter.withAbstraction, binary_effectDrivenWithin_pointwise hf,
    List.map_map]
  rfl

/-- **Rules at one assignment are the pointwise grammar of reading an assignment.** For a grammar
that keeps to the types without effects and has no rule for two readers, over words and indices of
such types, each word read as the computation that ignores or consults the assignment, the values
of a tree in the effect-driven grammar pointwise at reading, with the binder at its indices, are
its values by the rules of the grammar at one assignment, with abstraction over its indices. The
domains are total: a grammar of partial denotations is not an instance. -/
theorem values_withBinder_of_effectFree [L.IsBinary] (hf : P (.R g)) (hL : L.EffectFree)
    (hΓ : ∀ n, (Γ n).EffectFree) (E : Assignments (g.Dom D) (Ty.Dom D) Γ)
    (hlex : ∀ x, (lex' x).map (fun p ↦ (⟨p.1, ρ' p.2⟩ : Sigma (Ty.Dom D))) =
      (lex x).map fun p ↦ ⟨.comp (.R g) p.1, ρ p.2⟩)
    (hfree : ∀ x, ∀ p ∈ lex x, p.1.EffectFree) (t : Tree C Lx) :
    t.values ((effectDrivenWithin (MetaMode.pointwise P) L).withBinder g Γ)
        (effectGrammar.structure.sum (binding.structure E)) ρ' lex' =
      (t.values ((typeDriven L).withAbstraction Γ) (withAbstraction.structure E) ρ lex).map
        fun d ↦ ⟨.comp (.R g) d.1, d.2⟩ := by
  refine values_eq_map_values (withAbstraction.toBinding_isExpansionOn E)
    (Q := Ty.EffectFree) ⟨fun n a ha r hr ↦ ?_, fun a b ha hb m hm ↦ ?_⟩ hlex hfree
    (fun _ _ _ ↦ by simp [withBinder, Interpreter.withAbstraction, withAbstraction.toBinding,
      LHom.ofMk₂])
    (fun a b ha hb ↦ ?_) t
  · obtain rfl := List.mem_singleton.1 hr
    exact ⟨hΓ n, ha⟩
  · obtain ⟨m, -, rfl⟩ := List.mem_map.1 hm
    exact hL.binary m.2 ha hb
  · simp only [withBinder, Interpreter.withAbstraction, typeDriven,
      binary_effectDrivenWithin_pointwise hf,
      binary_effectDrivenWithin_of_effectFree _ hL ha hb, List.map_map]
    rfl

end PhraseStructure.Tree
