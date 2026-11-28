/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Negation.Strength.ProjectivitySignature
public import Linglib.Semantics.Alternatives.WithAlternatives
public import Linglib.Semantics.PolarityItem.Basic
public import Linglib.Semantics.PolarityItem.Licenser
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Group.Action.Defs

/-!
# Environments of a polarity item

A *domain* of a polarity item is a constituent in which its acceptability is evaluated. The
*environment* of the item in a domain is the meaning of the domain as a function of the meaning of
the item, together with a signature whose function class contains that function. Environments
compose as constituents nest: the environment of a position in a larger constituent is the
environment of the smaller constituent in the larger one after the environment of the position in
the smaller one, and the signatures multiply. The environments from a lattice to itself are the
*layers* of meaning between successive domains. They form a monoid, and they act on the
environments into that lattice.

Along the chain of domains from the item to the sentence, each environment is the environment
below it under a layer, and its sign is the product of the signs below it. An environment of
negative sign carries the monotone decreasing strength, and an environment of positive sign carries
no strength. A domain can therefore admit an item where the next domain does not and the one
after that does again.

## Main definitions

* `PolarityItem.Environment`: a map between bounded lattices with a signature that holds of it.
* `PolarityItem.Environment.comp`, `PolarityItem.Environment.id`: composition and the identity.
* `PolarityItem.Environment.signatureHom`: the signature of a layer, as a monoid homomorphism.
* `PolarityItem.Path`: the environment of the minimal domain of an item and the layers above it.
* `PolarityItem.Path.Licenses`: some domain of the path admits a distribution.

## Main results

* `PolarityItem.Path.environment_cons`: the environment of each domain is the environment of the
  domain below it under a layer.
* `PolarityItem.Environment.carries_monotoneDecreasing_of_sign_eq_neg_one`: a non-constant
  environment of negative sign carries the monotone decreasing strength.
* `PolarityItem.Environment.not_carries_of_sign_eq_one`: an environment of positive sign carries
  no strength.

## Implementation notes

* An environment is not determined by its map: a constant map is in every monotone and every
  antitone class, so a map has no least signature. The signature is therefore a field, two
  environments with the same map can differ, and there is no `FunLike` instance.
* A signature whose class contains an environment can understate the strength of the
  environment. A proof that a domain does not carry a strength therefore requires meanings of the
  item at which the environment fails that strength.
* The licenser of an environment is the classical licenser of a single operator. Its operators
  are between lattices in `Type`, so carrying and licensing are stated at that universe.
* The layers of a path are maps of one lattice to itself, so every domain of a path has the same
  type of meaning.

## References

* [gajewski-2005]
* [homer-2021]
* [icard-2012]
* [zwarts-1998]
-/

@[expose] public section

namespace PolarityItem

open NaturalLogic

/-- The environment of a position in a constituent. It consists of the meaning of the constituent
as a function of the meaning at the position, together with a signature whose function class
contains that function. -/
@[ext]
structure Environment (α β : Type*) [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] where
  /-- The meaning of the constituent as a function of the meaning at the position. -/
  toFun : α → β
  /-- A signature whose function class contains the environment. -/
  signature : ProjectivitySignature
  holdsFor : signature.HoldsFor toFun

namespace Environment

section Comp

variable {α β γ δ : Type*} [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β]
  [Lattice γ] [BoundedOrder γ] [Lattice δ] [BoundedOrder δ]

instance : CoeFun (Environment α β) fun _ ↦ α → β := ⟨toFun⟩

attribute [coe] toFun

@[simp]
theorem coe_mk (f : α → β) (φ : ProjectivitySignature) (h : φ.HoldsFor f) :
    ⇑(⟨f, φ, h⟩ : Environment α β) = f :=
  rfl

variable (α) in
/-- The environment of a position in itself. -/
protected def id : Environment α α :=
  ⟨id, 1, ProjectivitySignature.holdsFor_addMult_id⟩

/-- The environment of a position in a larger constituent: the environment `g` of a smaller
constituent in the larger one, after the environment `f` of the position in the smaller one. -/
def comp (g : Environment β γ) (f : Environment α β) : Environment α γ :=
  ⟨g ∘ f, g.signature * f.signature, g.holdsFor.comp f.holdsFor⟩

/-- Complementation on a Boolean algebra, the environment of the scope of negation. -/
protected def compl {P : Type*} [BooleanAlgebra P] : Environment P P :=
  ⟨compl, .antiAddMult, ProjectivitySignature.holdsFor_antiAddMult_compl⟩

@[simp]
theorem coe_id : ⇑(Environment.id α) = id :=
  rfl

@[simp]
theorem signature_id : (Environment.id α).signature = 1 :=
  rfl

@[simp]
theorem coe_comp (g : Environment β γ) (f : Environment α β) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
theorem signature_comp (g : Environment β γ) (f : Environment α β) :
    (g.comp f).signature = g.signature * f.signature :=
  rfl

@[simp]
theorem coe_compl {P : Type*} [BooleanAlgebra P] : ⇑(Environment.compl : Environment P P) = compl :=
  rfl

@[simp]
theorem signature_compl {P : Type*} [BooleanAlgebra P] :
    (Environment.compl : Environment P P).signature = .antiAddMult :=
  rfl

theorem comp_assoc (h : Environment γ δ) (g : Environment β γ) (f : Environment α β) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  Environment.ext rfl (mul_assoc _ _ _)

@[simp]
theorem id_comp (f : Environment α β) : (Environment.id β).comp f = f :=
  Environment.ext rfl (one_mul _)

@[simp]
theorem comp_id (f : Environment α β) : f.comp (Environment.id α) = f :=
  Environment.ext rfl (mul_one _)

/-- The layers of meaning on a lattice form a monoid under composition. -/
instance : Monoid (Environment α α) where
  mul := comp
  one := Environment.id α
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]
theorem coe_one : ⇑(1 : Environment α α) = id :=
  rfl

@[simp]
theorem signature_one : (1 : Environment α α).signature = 1 :=
  rfl

@[simp]
theorem coe_mul (g f : Environment α α) : ⇑(g * f) = g ∘ f :=
  rfl

@[simp]
theorem signature_mul (g f : Environment α α) : (g * f).signature = g.signature * f.signature :=
  rfl

variable (α) in
/-- The signature of a layer, as a monoid homomorphism. -/
def signatureHom : Environment α α →* ProjectivitySignature where
  toFun := signature
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem signatureHom_apply (l : Environment α α) : signatureHom α l = l.signature :=
  rfl

/-- A layer acts on the environment of the domain below it by composition. -/
instance : MulAction (Environment β β) (Environment α β) where
  smul := comp
  one_smul := id_comp
  mul_smul := comp_assoc

@[simp]
theorem coe_smul (l : Environment β β) (e : Environment α β) : ⇑(l • e) = l ∘ e :=
  rfl

@[simp]
theorem signature_smul (l : Environment β β) (e : Environment α β) :
    (l • e).signature = l.signature * e.signature :=
  rfl

variable (e : Environment α β)

theorem monotone_of_sign_eq_one (h : e.signature.sign = 1) : Monotone e :=
  e.holdsFor.monotone_of_sign_eq_one h

/-- An environment of negative sign is downward entailing. -/
theorem antitone_of_sign_eq_neg_one (h : e.signature.sign = -1) : Antitone e :=
  e.holdsFor.antitone_of_sign_eq_neg_one h

end Comp

/-! ### Carrying a strength of negation -/

section Carries

variable {σ P : Type} [BooleanAlgebra σ] [BooleanAlgebra P]
  (e : Environment σ P) {s : Negation.Strength}

/-- An environment of positive sign carries no strength of negation. -/
theorem not_carries_of_sign_eq_one (h : e.signature.sign = 1) :
    ¬(Licenser.ofOperator e).Carries s := fun hc ↦
  (Licenser.carries_ofOperator_iff.1 hc).2 (e.monotone_of_sign_eq_one h)

/-- A non-constant environment carries every strength that its signature realizes. -/
theorem carries_of_le_negationStrength
    (hs : (s : WithBot Negation.Strength) ≤ e.signature.negationStrength) (hne : e ⊥ ≠ e ⊤) :
    (Licenser.ofOperator e).Carries s := by
  have hf := e.holdsFor.of_le (ProjectivitySignature.coe_le_negationStrength_iff.1 hs)
  refine Licenser.carries_ofOperator_iff.2
    ⟨.of_toProjectivitySignature hf, fun hm ↦ hne (le_antisymm (hm bot_le) ?_)⟩
  exact ProjectivitySignature.holdsFor_anti_iff.1
    (hf.of_le (Negation.Strength.toProjectivitySignature_antitone bot_le))
    bot_le

/-- A non-constant environment of negative sign carries the monotone decreasing strength. -/
theorem carries_monotoneDecreasing_of_sign_eq_neg_one (h : e.signature.sign = -1)
    (hne : e ⊥ ≠ e ⊤) :
    (Licenser.ofOperator e).Carries .monotoneDecreasing := by
  obtain ⟨s', hs'⟩ :=
    WithBot.ne_bot_iff_exists.1 ((ProjectivitySignature.negationStrength_ne_bot_iff _).2 h)
  exact e.carries_of_le_negationStrength (hs' ▸ WithBot.coe_le_coe.2 bot_le) hne

end Carries

end Environment

/-! ### Paths -/

/-- The path of a polarity item from its minimal domain to the sentence. It consists of the
environment of the minimal domain and the layers between successive domains, outermost first. -/
structure Path (σ P : Type*) [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P] where
  /-- The environment of the minimal domain. -/
  minimal : Environment σ P
  /-- The layers between successive domains, outermost first. -/
  layers : List (Environment P P)

namespace Path

variable {σ P : Type*} [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P] (p : Path σ P)

/-- The environment of the domain reached through the layers `t`, which act together on the
minimal environment. -/
def environment (t : List (Environment P P)) : Environment σ P :=
  t.prod • p.minimal

@[simp]
theorem environment_nil : p.environment [] = p.minimal :=
  one_smul _ _

/-- The environment of each domain is the environment of the domain below it under a layer. -/
@[simp]
theorem environment_cons (l : Environment P P)
    (t : List (Environment P P)) :
    p.environment (l :: t) = l • p.environment t := by
  rw [environment, environment, List.prod_cons, mul_smul]

section WithAlternatives

/-- The meaning of the domain reached through the layers `t`, together with its alternatives, when
`A` gives the alternatives of the minimal domain. The layers apply to each alternative. -/
def withAlternatives (A : σ → Set P) (t : List (Environment P P)) (x : σ) :
    WithAlternatives P :=
  ⇑t.prod <$> ⟨p.minimal x, A x⟩

@[simp]
theorem ordinary_withAlternatives (A : σ → Set P)
    (t : List (Environment P P)) (x : σ) :
    (p.withAlternatives A t x).ordinary = p.environment t x :=
  rfl

@[simp]
theorem withAlternatives_nil (A : σ → Set P) (x : σ) :
    p.withAlternatives A [] x = ⟨p.minimal x, A x⟩ :=
  id_map _

@[simp]
theorem withAlternatives_cons (A : σ → Set P) (l : Environment P P)
    (t : List (Environment P P)) (x : σ) :
    p.withAlternatives A (l :: t) x = ⇑l <$> p.withAlternatives A t x := by
  simp only [withAlternatives, List.prod_cons, Environment.coe_mul]
  exact comp_map _ _ _

end WithAlternatives

end Path

/-! ### Licensing -/

namespace Environment

variable {σ P : Type} [BooleanAlgebra σ] [BooleanAlgebra P]
  (e : Environment σ P) {s : Negation.Strength}

/-- An environment of negative sign holds the monotone decreasing strength outright. -/
theorem holds_monotoneDecreasing_of_sign_eq_neg_one (h : e.signature.sign = -1) :
    (Licenser.ofOperator e).Holds .monotoneDecreasing :=
  fun _ ↦ e.antitone_of_sign_eq_neg_one h

/-- A non-constant environment of positive sign holds no strength outright. -/
theorem not_holds_of_sign_eq_one (h : e.signature.sign = 1) (hne : e ⊥ ≠ e ⊤) :
    ¬ (Licenser.ofOperator e).Holds s :=
  Licenser.not_holds_of_not_holds_monotoneDecreasing fun ha ↦ hne <| le_antisymm
    (e.monotone_of_sign_eq_one h bot_le) (ha ⟨⟩ bot_le)

end Environment

namespace Path

variable {σ P : Type} [BooleanAlgebra σ] [BooleanAlgebra P] (p : Path σ P)
  {s : Negation.Strength} {d : Distribution}

/-- The licensing condition, which requires that some domain admit the item. -/
def Licenses (d : Distribution) : Prop :=
  ∃ t ∈ p.layers.tails, (Licenser.ofOperator (p.environment t)).Admits d

/-- A negative polarity item is not licensed on a path along which every domain has positive
sign. -/
theorem not_licenses_npi
    (h : ∀ t ∈ p.layers.tails, (p.environment t).signature.sign = 1) :
    ¬p.Licenses (.npi s) := fun ⟨t, ht, ha⟩ ↦
  (p.environment t).not_carries_of_sign_eq_one (h t ht) (Licenser.admits_npi_iff.1 ha)

/-- A positive polarity item is not licensed on a path along which every domain holds the strength
that blocks it. -/
theorem not_licenses_ppi
    (h : ∀ t ∈ p.layers.tails,
      (Licenser.ofOperator (p.environment t)).Holds s) :
    ¬p.Licenses (.ppi s) := fun ⟨t, ht, ha⟩ ↦ Licenser.admits_ppi_iff.1 ha (h t ht)

end Path

end PolarityItem
