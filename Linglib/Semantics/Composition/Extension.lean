module

public import Linglib.Core.ModelTheory.ManySorted.LanguageMap
public import Linglib.Semantics.Composition.Interpret

/-!
# Extending a system of rules

A system of rules is extended by a map of languages: the rules of one are among the rules of
another, which may have more. Where an interpreter of the larger system admits at a node what an
interpreter of the smaller admits there, and a larger lexicon has the items of a smaller, [every
derivation of the smaller is one of the larger](##Interpreter.mem_derivs_of_le), and in a
structure that expands the smaller one [it has the same
value](##Interpreter.mem_values_of_le). A claim that a structure has a reading therefore holds in
every extension. A claim that it has no other reading, or none, does not, and those are the claims
an extension tests.

## Main definitions

* `Interpreter.Extends`: an interpreter admits at each node the images of the rules another
  admits there.
-/

@[expose] public section

universe u v w x

open ManySorted ManySorted.Language

namespace Interpreter

variable {T : Type u} {L L' : Language.{u, v} T} {N : Type v} {Lx : Type w} {W : T → Type w}
  {D : T → Type x} {I : Interpreter L N} {J : Interpreter L' N} {φ : L →ᴸ L'}
  {lex lex' : Lx → List (Σ a, W a)}

/-- An interpreter extends another along a map of languages when it admits at each node the
images of the rules the other admits there. -/
structure Extends (J : Interpreter L' N) (I : Interpreter L N) (φ : L →ᴸ L') : Prop where
  /-- The unary rules. -/
  unary {n : N} {a : T} {r : Σ b, L.Unary a b} :
    r ∈ I.unary n a → ⟨r.1, φ.onFunction r.2⟩ ∈ J.unary n a
  /-- The binary rules. -/
  binary {n : N} {l r : T} {m : Σ u, L.Binary l r u} :
    m ∈ I.binary n l r → ⟨m.1, φ.onFunction m.2⟩ ∈ J.binary n l r

/-- A derivation survives an extension of the rules and of the lexicon: its image along the map
is a derivation the extending interpreter finds. -/
theorem mem_derivs_of_le (h : J.Extends I φ) (hl : ∀ x, lex x ⊆ lex' x) :
    ∀ {s : Skeleton N Lx} {d : Σ a, Deriv L W a}, d ∈ I.derivs lex s →
      (⟨d.1, φ.onTerm d.2⟩ : Σ a, Deriv L' W a) ∈ J.derivs lex' s
  | .leaf x, d, hd => by
    obtain ⟨⟨a, w⟩, hw, rfl⟩ := List.mem_map.1 hd
    exact List.mem_map.2 ⟨⟨a, w⟩, hl x hw, rfl⟩
  | .unary n s, d, hd => by
    obtain ⟨⟨a, e⟩, he, hd⟩ := List.mem_flatMap.1 hd
    obtain ⟨⟨b, r⟩, hr, rfl⟩ := List.mem_map.1 hd
    exact List.mem_flatMap.2 ⟨_, mem_derivs_of_le h hl he, List.mem_map.2 ⟨_, h.unary hr, rfl⟩⟩
  | .binary n s₁ s₂, d, hd => by
    obtain ⟨⟨a, e₁⟩, he₁, hd⟩ := List.mem_flatMap.1 hd
    obtain ⟨⟨b, e₂⟩, he₂, hd⟩ := List.mem_flatMap.1 hd
    obtain ⟨⟨c, m⟩, hm, rfl⟩ := List.mem_map.1 hd
    exact List.mem_flatMap.2 ⟨_, mem_derivs_of_le h hl he₁, List.mem_flatMap.2
      ⟨_, mem_derivs_of_le h hl he₂, List.mem_map.2 ⟨_, h.binary hm, rfl⟩⟩⟩

/-- A value survives an extension of the rules and of the lexicon, in a structure that expands
the one it was computed in. -/
theorem mem_values_of_le {M : L.Structure D} {M' : L'.Structure D} (h : J.Extends I φ)
    (hM : φ.IsExpansionOn M M') (hl : ∀ x, lex x ⊆ lex' x) (ρ : ∀ {a : T}, W a → D a)
    {s : Skeleton N Lx} {d : Σ a, D a} (hd : d ∈ I.values M ρ lex s) :
    d ∈ J.values M' ρ lex' s := by
  obtain ⟨⟨a, e⟩, he, rfl⟩ := List.mem_map.1 hd
  exact List.mem_map.2 ⟨_, mem_derivs_of_le h hl he,
    congrArg (Sigma.mk a) (LHom.realize_onTerm hM ρ e)⟩

/-- The type-driven interpreter of the sum of two languages extends that of the first. -/
theorem typeDriven_sum_extends [L.LocallyFinite] [L'.LocallyFinite] :
    (typeDriven (L.sum L') : Interpreter (L.sum L') N).Extends (typeDriven L) LHom.sumInl where
  unary {_ _ r} hr := by
    obtain ⟨b, r⟩ := r
    exact List.mem_append_left _ (List.mem_map.2 ⟨⟨b, r⟩, hr, rfl⟩)
  binary {_ _ _ m} hm := by
    obtain ⟨u, m⟩ := m
    exact List.mem_append_left _ (List.mem_map.2 ⟨⟨u, m⟩, hm, rfl⟩)

/-- The values the type-driven interpreter of a language finds are found by that of its sum with
another language, whatever rules the other adds. -/
theorem mem_values_typeDriven_sum [L.LocallyFinite] [L'.LocallyFinite] (M : L.Structure D)
    (M' : L'.Structure D) (ρ : ∀ {a : T}, W a → D a) {s : Skeleton N Lx} {d : Σ a, D a}
    (hd : d ∈ (typeDriven L).values M ρ lex s) :
    d ∈ (typeDriven (L.sum L')).values (M.sum M') ρ lex s :=
  mem_values_of_le typeDriven_sum_extends (LHom.sumInl_isExpansionOn M M')
    (fun _ ↦ List.Subset.refl _) ρ hd

/-- An extension is one of the interpreters with predicate abstraction, which the map leaves in
place. -/
theorem Extends.withAbstraction {B : Type} {L L' : Language.{0, 0} (Ty B)}
    {I : Interpreter L Node} {J : Interpreter L' Node} {φ : L →ᴸ L'} (h : J.Extends I φ)
    (Γ : ℕ → Ty B) :
    (J.withAbstraction Γ).Extends (I.withAbstraction Γ) (φ.sumMap (LHom.id _)) where
  unary {n _ r} hr := by
    cases n with
    | index k =>
      obtain rfl := List.mem_singleton.1 hr
      exact List.mem_singleton.2 rfl
    | branch =>
      obtain ⟨⟨c, s⟩, hs, rfl⟩ := List.mem_map.1 hr
      exact List.mem_map.2 ⟨⟨c, φ.onFunction s⟩, h.unary (r := ⟨c, s⟩) hs, rfl⟩
    | island =>
      obtain ⟨⟨c, s⟩, hs, rfl⟩ := List.mem_map.1 hr
      exact List.mem_map.2 ⟨⟨c, φ.onFunction s⟩, h.unary (r := ⟨c, s⟩) hs, rfl⟩
  binary {_ _ _ _} h₀ := by
    obtain ⟨⟨u, m⟩, hm, rfl⟩ := List.mem_map.1 h₀
    exact List.mem_map.2 ⟨⟨u, φ.onFunction m⟩, h.binary (m := ⟨u, m⟩) hm, rfl⟩

end Interpreter

namespace PhraseStructure.Tree

open Interpreter

variable {C Lx : Type} {T : Type} {G G' : Language T} {W D : T → Type}
  {I : Interpreter G Node} {J : Interpreter G' Node} {φ : G →ᴸ G'}
  {lex lex' : Lx ⊕ ℕ → List (Σ a, W a)}

/-- A value of a tree survives an extension of the rules and of the lexicon. -/
theorem mem_values_of_le {M : G.Structure D} {M' : G'.Structure D} (h : J.Extends I φ)
    (hM : φ.IsExpansionOn M M') (hl : ∀ x, lex x ⊆ lex' x) (ρ : ∀ {a : T}, W a → D a)
    {t : Tree C Lx} {island : C → Bool} {d : Σ a, D a} (hd : d ∈ t.values I M ρ lex island) :
    d ∈ t.values J M' ρ lex' island := by
  unfold values derivs at hd ⊢
  cases hs : t.skeleton island with
  | none => simp [hs] at hd
  | some s =>
    rw [hs] at hd
    exact Interpreter.mem_values_of_le h hM hl ρ hd

/-- The meanings of a tree by Heim and Kratzer's procedure over a language of rules are among its
meanings over the sum of the language with another: adding rules loses no reading. -/
theorem mem_interpret_sum {B : Type} {D : B → Type} {W : Ty B → Type}
    {L L' : Language.{0, 0} (Ty B)} [L.LocallyFinite] [L'.LocallyFinite]
    [M : L.Structure (Ty.Dom D)] [M' : L'.Structure (Ty.Dom D)] (Γ : ℕ → Ty B)
    (ρ : ∀ {a : Ty B}, W a → (∀ n, (Γ n).Dom D) → a.Dom D) (lex : Lx → List (Σ a, W a))
    {t : Tree C Lx} {d : Σ a : Ty B, (∀ n, (Γ n).Dom D) → a.Dom D}
    (hd : d ∈ t.interpret L D Γ ρ lex) : d ∈ t.interpret (L.sum L') D Γ ρ lex :=
  mem_values_of_le (typeDriven_sum_extends.withAbstraction Γ)
    (LHom.sumMap_isExpansionOn (LHom.pi_isExpansionOn (LHom.sumInl_isExpansionOn M M') _)
      (LHom.id_isExpansionOn _))
    (fun _ ↦ List.Subset.refl _) (Leaf.val ρ) hd

end PhraseStructure.Tree
