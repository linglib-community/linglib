module

public import Linglib.Core.ModelTheory.ManySorted.LanguageMap
public import Linglib.Semantics.Composition.Interpret

/-!
# Extending a system of rules

A system of rules is extended by a map of languages: the rules of one are among the rules of
another, which may have more. Where an interpreter of the larger system admits at a node what an
interpreter of the smaller admits there, and a larger lexicon has the items of a smaller, [every
derivation of the smaller is one of the larger](##PhraseStructure.Tree.mem_derivs_of_le), and in
a structure that expands the smaller one [it has the same
value](##PhraseStructure.Tree.mem_values_of_le). A claim that a tree has a reading therefore
holds in every extension. A claim that it has no other reading, or none, does not, and those are
the claims an extension tests.

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
  {lex lex' : Lx → List (Sigma W)}

/-- An interpreter extends another along a map of languages when it admits at each node the
images of the rules the other admits there. -/
structure Extends (J : Interpreter L' N) (I : Interpreter L N) (φ : L →ᴸ L') : Prop where
  /-- The rules of a binder. -/
  bind {n : N} {a : T} {r : Sigma (L.Unary a)} :
    r ∈ I.bind n a → ⟨r.1, φ.onFunction r.2⟩ ∈ J.bind n a
  /-- The binary rules. -/
  binary {l r : T} {m : Sigma (L.Binary l r)} :
    m ∈ I.binary l r → ⟨m.1, φ.onFunction m.2⟩ ∈ J.binary l r

section Values

variable {D' : T → Type x} {M : L.Structure D} {M' : L'.Structure D'} (h : ∀ a, D a → D' a)
  {n : N}

/-- A value of a binder survives an extension of the rules, along a map of domains that
commutes with them. -/
theorem map_mem_bindValues (hJ : J.Extends I φ)
    (hh : ∀ {a b : T} (r : L.Unary a b) (x : D a),
      h b (M.funMap r x) = M'.funMap (φ.onFunction r) (h a x))
    {X : List (Sigma D)} {Y : List (Sigma D')}
    (hXY : ∀ d ∈ X, (⟨d.1, h d.1 d.2⟩ : Sigma D') ∈ Y) {d : Sigma D}
    (hd : d ∈ I.bindValues M n X) : (⟨d.1, h d.1 d.2⟩ : Sigma D') ∈ J.bindValues M' n Y := by
  obtain ⟨d₁, h₁, r, hr, rfl⟩ := mem_bindValues.1 hd
  exact mem_bindValues.2 ⟨_, hXY d₁ h₁, ⟨r.1, φ.onFunction r.2⟩, hJ.bind hr,
    congrArg (Sigma.mk r.1) (hh r.2 d₁.2)⟩

/-- A value of a binary node survives an extension of the rules, along a map of domains that
commutes with them. -/
theorem map_mem_binaryValues (hJ : J.Extends I φ)
    (hh : ∀ {a b c : T} (m : L.Binary a b c) (x : D a) (y : D b),
      h c (M.funMap m (x, y)) = M'.funMap (φ.onFunction m) (h a x, h b y))
    {X₁ X₂ : List (Sigma D)} {Y₁ Y₂ : List (Sigma D')}
    (h₁ : ∀ d ∈ X₁, (⟨d.1, h d.1 d.2⟩ : Sigma D') ∈ Y₁)
    (h₂ : ∀ d ∈ X₂, (⟨d.1, h d.1 d.2⟩ : Sigma D') ∈ Y₂) {d : Sigma D}
    (hd : d ∈ I.binaryValues M X₁ X₂) :
    (⟨d.1, h d.1 d.2⟩ : Sigma D') ∈ J.binaryValues M' Y₁ Y₂ := by
  obtain ⟨d₁, hd₁, d₂, hd₂, m, hm, rfl⟩ := mem_binaryValues.1 hd
  exact mem_binaryValues.2 ⟨_, h₁ d₁ hd₁, _, h₂ d₂ hd₂, ⟨m.1, φ.onFunction m.2⟩, hJ.binary hm,
    congrArg (Sigma.mk m.1) (hh m.2 d₁.2 d₂.2)⟩

end Values

/-- The type-driven interpreter of the sum of two languages extends that of the first. -/
theorem typeDriven_sum_extends [L.LocallyFinite] [L'.LocallyFinite] :
    (typeDriven (L.sum L') : Interpreter (L.sum L') N).Extends (typeDriven L) LHom.sumInl where
  bind hr := nomatch hr
  binary {_ _ m} hm := by
    obtain ⟨u, m⟩ := m
    exact List.mem_append_left _ (List.mem_map.2 ⟨⟨u, m⟩, hm, rfl⟩)

/-- An extension is one of the interpreters with predicate abstraction, which the map leaves in
place. -/
theorem Extends.withAbstraction {B : Type} {L L' : Language.{0, 0} (Ty B)}
    {I : Interpreter L ℕ} {J : Interpreter L' ℕ} {φ : L →ᴸ L'} (h : J.Extends I φ)
    (Γ : ℕ → Ty B) :
    (J.withAbstraction Γ).Extends (I.withAbstraction Γ) (φ.sumMap (LHom.id _)) where
  bind {n _ r} hr := by
    obtain rfl := List.mem_singleton.1 hr
    exact List.mem_singleton.2 rfl
  binary {_ _ _} h₀ := by
    obtain ⟨⟨u, m⟩, hm, rfl⟩ := List.mem_map.1 h₀
    exact List.mem_map.2 ⟨⟨u, φ.onFunction m⟩, h.binary (m := ⟨u, m⟩) hm, rfl⟩

end Interpreter

namespace PhraseStructure.Tree

open Interpreter

variable {C Lx : Type} {T : Type} {G G' : Language T} {W D : T → Type}
  {I : Interpreter G ℕ} {J : Interpreter G' ℕ} {φ : G →ᴸ G'}
  {lex lex' : Lx ⊕ ℕ → List (Sigma W)}

/-- A value of a tree survives an extension of the rules and of the lexicon, along a map of
domains that commutes with the rules and takes the values of the items to their values. -/
theorem map_mem_values_of_le {D' : T → Type} {M : G.Structure D} {M' : G'.Structure D'}
    (hJ : J.Extends I φ) (h : ∀ a, D a → D' a)
    (hu : ∀ {a b : T} (r : G.Unary a b) (x : D a),
      h b (M.funMap r x) = M'.funMap (φ.onFunction r) (h a x))
    (hb : ∀ {a b c : T} (m : G.Binary a b c) (x : D a) (y : D b),
      h c (M.funMap m (x, y)) = M'.funMap (φ.onFunction m) (h a x, h b y))
    {ρ : ∀ {a : T}, W a → D a} {ρ' : ∀ {a : T}, W a → D' a}
    (hρ : ∀ {a : T} (x : W a), h a (ρ x) = ρ' x) (hl : ∀ x, lex x ⊆ lex' x)
    (t : Tree C Lx) {d : Sigma D} (hd : d ∈ t.values I M ρ lex) :
    (⟨d.1, h d.1 d.2⟩ : Sigma D') ∈ t.values J M' ρ' lex' := by
  refine values_rel
    (fun (X : List (Sigma D)) (Y : List (Sigma D')) ↦ ∀ d ∈ X, (⟨d.1, h d.1 d.2⟩ : Sigma D') ∈ Y)
    (fun _ hd ↦ nomatch hd) (fun x d hd ↦ ?_) (fun _ _ _ hX d hd ↦ map_mem_bindValues h hJ hu hX hd)
    (fun _ _ _ _ h₁ h₂ d hd ↦ map_mem_binaryValues h hJ hb h₁ h₂ hd) t d hd
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hd
  exact List.mem_map.2 ⟨p, hl _ hp, congrArg (Sigma.mk p.1) (hρ p.2).symm⟩

/-- A value of a tree survives an extension of the rules and of the lexicon, in a structure that
expands the one it was computed in. -/
theorem mem_values_of_le {M : G.Structure D} {M' : G'.Structure D} (h : J.Extends I φ)
    (hM : φ.IsExpansionOn M M') (hl : ∀ x, lex x ⊆ lex' x) (ρ : ∀ {a : T}, W a → D a)
    {t : Tree C Lx} {d : Sigma D} (hd : d ∈ t.values I M ρ lex) :
    d ∈ t.values J M' ρ lex' :=
  map_mem_values_of_le h (fun _ x ↦ x) (fun r x ↦ (hM.map_onFunction r x).symm)
    (fun m x y ↦ (hM.map_onFunction m (x, y)).symm) (fun _ ↦ rfl) hl t hd

/-- A derivation of a tree survives an extension of the rules and of the lexicon: its image
along the map is a derivation the extending interpreter admits. -/
theorem mem_derivs_of_le (h : J.Extends I φ) (hl : ∀ x, lex x ⊆ lex' x) {t : Tree C Lx}
    {d : Sigma (Deriv G W)} (hd : d ∈ t.derivs I lex) :
    (⟨d.1, φ.onTerm d.2⟩ : Sigma (Deriv G' W)) ∈ t.derivs J lex' := by
  rw [derivs_eq_values] at hd ⊢
  exact map_mem_values_of_le h (fun _ d ↦ φ.onTerm d) (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun _ ↦ rfl) hl t hd

/-- The meanings of a tree by Heim and Kratzer's procedure over a language of rules are among its
meanings over the sum of the language with another: adding rules loses no reading. -/
theorem mem_interpret_sum {B : Type} {D : B → Type} {W : Ty B → Type}
    {L L' : Language.{0, 0} (Ty B)} [L.LocallyFinite] [L'.LocallyFinite]
    [M : L.Structure (Ty.Dom D)] [M' : L'.Structure (Ty.Dom D)] (Γ : ℕ → Ty B)
    (ρ : ∀ {a : Ty B}, W a → (∀ n, (Γ n).Dom D) → a.Dom D) (lex : Lx → List (Sigma W))
    {t : Tree C Lx} {d : Σ a : Ty B, (∀ n, (Γ n).Dom D) → a.Dom D}
    (hd : d ∈ t.interpret L D Γ ρ lex) : d ∈ t.interpret (L.sum L') D Γ ρ lex :=
  mem_values_of_le (typeDriven_sum_extends.withAbstraction Γ)
    (LHom.sumMap_isExpansionOn (LHom.pi_isExpansionOn (LHom.sumInl_isExpansionOn M M') _)
      (LHom.id_isExpansionOn _))
    (fun _ ↦ List.Subset.refl _) (Leaf.val ρ) hd

end PhraseStructure.Tree
