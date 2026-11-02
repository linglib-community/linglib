/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.Composition
public import Linglib.Semantics.Composition.WithAlternatives
public import Linglib.Semantics.PolarityItem.Basic
public import Linglib.Semantics.PolarityItem.Licenser

/-!
# Environments of a polarity item

This file defines the environment of a polarity item in a domain, a constituent in which its
acceptability is evaluated: the meaning of the domain as a function of the meaning of the item,
together with a signature whose function class contains it. A layer of meaning acts on the
environment of the domain below it, composing the maps and multiplying the signatures, so along the
chain of domains from the item to the sentence [each environment is the one below under a
layer](##PolarityItem.Path.environment_cons), and its sign is the product of the signs below it. An
environment of negative sign [carries weak
strength](##PolarityItem.Environment.carries_weak_of_sign_eq_neg_one) and one of positive sign
[carries none](##PolarityItem.Environment.not_carries_of_sign_eq_one), so an item licensed in one
domain can be anti-licensed in the next, and licensed again in the one after.

## Implementation notes

* The licenser of an environment is the classical licenser of a single operator, whose operators
  are between lattices in `Type`, so carrying and licensing are stated there.
* A signature in whose class an environment lies can understate its strength, so showing that a
  domain does not carry a strength takes meanings of the item on which the environment fails the
  strength.

## References

* [gajewski-2005]
* [homer-2021]
* [icard-2012]
* [zwarts-1998]
-/

@[expose] public section

namespace PolarityItem

open NaturalLogic

/-- Sentential negation as a layer: complementation, anti-morphic. -/
def negation {P : Type*} [BooleanAlgebra P] : Signature.classPairs P :=
  ⟨(compl, .antiAddMult), Signature.holdsFor_antiAddMult_compl⟩

/-- The environment of a polarity item in a domain: the meaning of the domain as a function of the
meaning of the item, with a signature whose function class contains it. -/
@[ext]
structure Environment (σ P : Type*) [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P] where
  /-- The meaning of the domain as a function of the meaning of the item. -/
  toFun : σ → P
  /-- A signature whose function class contains the environment. -/
  signature : Signature
  holdsFor : signature.HoldsFor toFun

namespace Environment

section Action

variable {σ P : Type*} [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P]

instance : CoeFun (Environment σ P) fun _ ↦ σ → P := ⟨toFun⟩

attribute [coe] toFun

@[simp]
theorem coe_mk (f : σ → P) (φ : Signature) (h : φ.HoldsFor f) :
    ⇑(⟨f, φ, h⟩ : Environment σ P) = f :=
  rfl

/-- A layer acts on the environment of the domain below it, composing its map with the
environment and multiplying its signature with the environment's. -/
instance : MulAction (Signature.classPairs P) (Environment σ P) where
  smul l e := ⟨l.1.1 ∘ e, l.1.2 * e.signature, (Signature.mem_classPairs.1 l.2).comp e.holdsFor⟩
  one_smul e := Environment.ext rfl (one_mul e.signature)
  mul_smul a b e := Environment.ext rfl (mul_assoc a.1.2 b.1.2 e.signature)

@[simp]
theorem coe_smul (l : Signature.classPairs P) (e : Environment σ P) : ⇑(l • e) = l.1.1 ∘ e :=
  rfl

@[simp]
theorem signature_smul (l : Signature.classPairs P) (e : Environment σ P) :
    (l • e).signature = l.1.2 * e.signature :=
  rfl

variable (e : Environment σ P)

theorem monotone_of_sign_eq_one (h : e.signature.sign = 1) : Monotone e :=
  (Signature.soundFor_of_holdsFor e.holdsFor).monotone_of_sign_eq_one h

/-- An environment of negative sign is downward entailing. -/
theorem antitone_of_sign_eq_neg_one (h : e.signature.sign = -1) : Antitone e :=
  (Signature.soundFor_of_holdsFor e.holdsFor).antitone_of_sign_eq_neg_one h

end Action

/-! ### Carrying a strength of negation -/

section Carries

variable {σ P : Type} [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P]
  (e : Environment σ P) {s : Negation.Strength}

/-- An environment carries the strength `s` of negation when its licenser does. -/
def Carries (s : Negation.Strength) : Prop :=
  (Licenser.ofOperator e).Carries s

theorem carries_iff : e.Carries s ↔ s.toSignature.HoldsFor e ∧ ¬Monotone e :=
  Licenser.carries_ofOperator_iff

/-- An environment of positive sign carries no strength of negation. -/
theorem not_carries_of_sign_eq_one (h : e.signature.sign = 1) : ¬e.Carries s := fun hc ↦
  (e.carries_iff.1 hc).2 (e.monotone_of_sign_eq_one h)

/-- An environment carries the strengths its signature realizes, once it is not constant. -/
theorem carries_of_le_negationStrength
    (hs : (s : WithBot Negation.Strength) ≤ e.signature.negationStrength) (hne : e ⊥ ≠ e ⊤) :
    e.Carries s := by
  have hf := e.holdsFor.of_le (Signature.coe_le_negationStrength_iff.1 hs)
  refine e.carries_iff.2 ⟨hf, fun hm ↦ hne (le_antisymm (hm bot_le) ?_)⟩
  exact Signature.holdsFor_anti_iff.1 (hf.of_le (Negation.Strength.toSignature_antitone bot_le))
    bot_le

/-- An environment of negative sign carries weak strength, once it is not constant. -/
theorem carries_weak_of_sign_eq_neg_one (h : e.signature.sign = -1) (hne : e ⊥ ≠ e ⊤) :
    e.Carries .weak := by
  obtain ⟨s', hs'⟩ :=
    WithBot.ne_bot_iff_exists.1 ((Signature.negationStrength_ne_bot_iff _).2 h)
  exact e.carries_of_le_negationStrength (hs' ▸ WithBot.coe_le_coe.2 bot_le) hne

end Carries

end Environment

/-! ### Paths -/

/-- The path of a polarity item from its minimal domain to the sentence: the environment of the
minimal domain and the layers between successive domains, outermost first. -/
structure Path (σ P : Type*) [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P] where
  /-- The environment of the minimal domain. -/
  minimal : Environment σ P
  /-- The layers between successive domains, outermost first, each in the function class of its
  signature. -/
  layers : List (Signature.classPairs P)

namespace Path

variable {σ P : Type*} [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P] (p : Path σ P)

/-- The environment of the domain reached through the layers `t`, on which they act together. -/
def environment (t : List (Signature.classPairs P)) : Environment σ P :=
  t.prod • p.minimal

@[simp]
theorem environment_nil : p.environment [] = p.minimal :=
  one_smul _ _

/-- The environment of each domain is that of the one below under a layer. -/
@[simp]
theorem environment_cons (l : Signature.classPairs P) (t : List (Signature.classPairs P)) :
    p.environment (l :: t) = l • p.environment t := by
  rw [environment, environment, List.prod_cons, mul_smul]

section WithAlternatives

/-- The meaning of the domain reached through the layers `t` with its alternatives, when `A` gives
the alternatives of the minimal domain: the layers apply to each alternative. -/
def withAlternatives (A : σ → Set P) (t : List (Signature.classPairs P)) (x : σ) :
    WithAlternatives P :=
  (t.prod : Function.End P × Signature).1 <$> ⟨p.minimal x, A x⟩

@[simp]
theorem ordinary_withAlternatives (A : σ → Set P) (t : List (Signature.classPairs P)) (x : σ) :
    (p.withAlternatives A t x).ordinary = p.environment t x :=
  rfl

@[simp]
theorem withAlternatives_nil (A : σ → Set P) (x : σ) :
    p.withAlternatives A [] x = ⟨p.minimal x, A x⟩ :=
  id_map _

@[simp]
theorem withAlternatives_cons (A : σ → Set P) (l : Signature.classPairs P)
    (t : List (Signature.classPairs P)) (x : σ) :
    p.withAlternatives A (l :: t) x = l.1.1 <$> p.withAlternatives A t x := by
  simp only [withAlternatives, List.prod_cons, Submonoid.coe_mul, Prod.fst_mul]
  exact comp_map _ _ _

end WithAlternatives

end Path

/-! ### Licensing -/

section Acceptable

variable {σ P : Type} [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P]

/-- An item is acceptable under an operator over its position when the operator carries the
strength of negation that licenses the item and does not carry the strength that blocks it. -/
def Acceptable (π : PolarityItem) (f : σ → P) : Prop :=
  (∀ s ∈ π.licensor, (Licenser.ofOperator f).Carries s) ∧
    ∀ s ∈ π.antiLicensor, ¬(Licenser.ofOperator f).Carries s

variable {π : PolarityItem} {f : σ → P} {s : Negation.Strength}

theorem acceptable_of_licensor (hl : π.licensor = some s) (ha : π.antiLicensor = none)
    (h : (Licenser.ofOperator f).Carries s) : π.Acceptable f :=
  ⟨fun _ h' ↦ Option.mem_some_iff.1 (hl ▸ h') ▸ h, fun _ h' ↦ absurd (ha ▸ h') nofun⟩

theorem acceptable_of_antiLicensor (hl : π.licensor = none) (ha : π.antiLicensor = some s)
    (h : ¬(Licenser.ofOperator f).Carries s) : π.Acceptable f :=
  ⟨fun _ h' ↦ absurd (hl ▸ h') nofun, fun _ h' ↦ Option.mem_some_iff.1 (ha ▸ h') ▸ h⟩

end Acceptable

namespace Path

variable {σ P : Type} [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P] (p : Path σ P)
  {s : Negation.Strength} {π : PolarityItem}

/-- The licensing condition: the item is acceptable in some domain. -/
def Licenses (π : PolarityItem) : Prop :=
  ∃ t ∈ p.layers.tails, π.Acceptable (p.environment t)

/-- An item that a strength licenses is anti-licensed when every domain has positive sign. -/
theorem not_licenses_of_mem_licensor (hs : s ∈ π.licensor)
    (h : ∀ t ∈ p.layers.tails, (p.environment t).signature.sign = 1) : ¬p.Licenses π :=
  fun ⟨t, ht, ha⟩ ↦ (p.environment t).not_carries_of_sign_eq_one (h t ht) (ha.1 s hs)

/-- An item that a strength blocks is anti-licensed when every domain carries it. -/
theorem not_licenses_of_mem_antiLicensor (hs : s ∈ π.antiLicensor)
    (h : ∀ t ∈ p.layers.tails, (p.environment t).Carries s) : ¬p.Licenses π := fun ⟨t, ht, ha⟩ ↦
  ha.2 s hs (h t ht)

end Path

end PolarityItem
