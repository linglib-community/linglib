/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.Composition
public import Linglib.Semantics.Composition.WithAlternatives
public import Linglib.Semantics.Polarity.Item
public import Linglib.Semantics.Polarity.Licenser

/-!
# Environments of a polarity item

The environment of a polarity item in a constituent is the meaning of the constituent as a function
of the meaning of the item. The constituents in which the acceptability of an item is evaluated,
its domains, form a chain from its minimal domain to the sentence (`PolarityItem.Path`): each
domain is the one below under a layer, so the environment of a domain composes the layers below it
with the environment of the minimal domain. A domain carries a strength of negation when its
environment, as the operator over the position of the item, does (`PolarityItem.Licenser.Carries`).
The licensing condition asks of an item that some domain carry the strength that licenses it, and
that some domain not carry the strength that blocks it (`PolarityItem.Path.Licenses`).

Each layer is in the function class of a signature, so the sign of a domain is the product of the
signs below it, and [it fixes the direction of the domain's
environment](##PolarityItem.Path.antitone_environment). A layer of negative sign, a
downward-entailing expression, therefore [reverses the sign of every domain above
it](##PolarityItem.Path.sign_cons): a domain of positive sign [carries no
strength](##PolarityItem.Path.not_carries_of_sign_eq_one), so an item licensed in a domain can be
anti-licensed in the next, and licensed again in the one after. The strength the signature of a
domain realizes [is carried by it](##PolarityItem.Path.carries_of_le_strength) once its
environment is not constant. When the minimal domain comes with scalar alternatives, the layers
apply to each of them, so every domain has [its meaning with its
alternatives](##PolarityItem.Path.withAlternatives), as in alternative semantics.

## Implementation notes

* The licenser of a domain is a classical licenser, whose operators are between lattices in
  `Type`, so carrying and licensing are stated for paths there.
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

/-- The path of a polarity item from its minimal domain to the sentence: the environment of the
minimal domain with a signature whose function class contains it, and the layers between
successive domains, outermost first, each in the class of its signature. -/
structure Path (σ P : Type*) [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P] where
  /-- The environment of the minimal domain, as a function of the meaning of the item. -/
  minimal : σ → P
  /-- A signature whose function class contains the environment of the minimal domain. -/
  signature : Signature
  holdsFor : signature.HoldsFor minimal
  /-- The layers between successive domains, outermost first, each in the function class of its
  signature. -/
  layers : List (Signature.classPairs P)

namespace Path

variable {σ P : Type*} [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P] (p : Path σ P)
  {t : List (Signature.classPairs P)}

/-- The environment of the domain reached through the layers `t`. -/
def environment (t : List (Signature.classPairs P)) : σ → P :=
  (t.prod : Function.End P × Signature).1 ∘ p.minimal

/-- The sign of the domain reached through the layers `t`: the product of their signs with the
sign of the minimal domain. -/
def sign (t : List (Signature.classPairs P)) : SignType :=
  (t.map fun l ↦ l.1.2.sign).prod * p.signature.sign

/-- The strength of negation that the signature of the domain reached through `t` realizes. -/
def strength (t : List (Signature.classPairs P)) : WithBot Negation.Strength :=
  ((t.prod : Function.End P × Signature).2 * p.signature).negationStrength

@[simp]
theorem environment_nil : p.environment [] = p.minimal :=
  rfl

@[simp]
theorem environment_cons (l : Signature.classPairs P) (t : List (Signature.classPairs P)) :
    p.environment (l :: t) = l.1.1 ∘ p.environment t := by
  simp only [environment, List.prod_cons, Submonoid.coe_mul, Prod.fst_mul]
  rfl

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

/-- Adding a layer multiplies the sign of a domain by the sign of the layer. -/
@[simp]
theorem sign_cons (l : Signature.classPairs P) (t : List (Signature.classPairs P)) :
    p.sign (l :: t) = l.1.2.sign * p.sign t := by
  simp [sign, mul_assoc]

@[simp]
theorem sign_nil : p.sign [] = p.signature.sign := by
  simp [sign]

theorem holdsFor_environment (t : List (Signature.classPairs P)) :
    ((t.prod : Function.End P × Signature).2 * p.signature).HoldsFor (p.environment t) :=
  Signature.HoldsFor.comp t.prod.2 p.holdsFor

theorem sign_eq (t : List (Signature.classPairs P)) :
    ((t.prod : Function.End P × Signature).2 * p.signature).sign = p.sign t := by
  show _ = (t.map fun l ↦ l.1.2.sign).prod * p.signature.sign
  rw [Signature.sign_mul, Submonoid.coe_list_prod, Signature.sign_list_prod, List.map_map]
  rfl

theorem strength_ne_bot_iff : p.strength t ≠ ⊥ ↔ p.sign t = -1 :=
  (Signature.negationStrength_ne_bot_iff _).trans (by rw [p.sign_eq])

theorem monotone_environment (h : p.sign t = 1) : Monotone (p.environment t) :=
  (Signature.soundFor_of_holdsFor (p.holdsFor_environment t)).monotone_of_sign_eq_one
    ((p.sign_eq t).trans h)

/-- A domain of negative sign is downward entailing with respect to the item. -/
theorem antitone_environment (h : p.sign t = -1) : Antitone (p.environment t) :=
  (Signature.soundFor_of_holdsFor (p.holdsFor_environment t)).antitone_of_sign_eq_neg_one
    ((p.sign_eq t).trans h)

end Path

/-! ### Carrying a strength and licensing -/

namespace Path

variable {σ P : Type} [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P] (p : Path σ P)
  {t : List (Signature.classPairs P)} {s : Negation.Strength} {π : PolarityItem}

/-- The licenser of the domain reached through `t`: its environment, as the operator over the
position of the item. -/
def licenser (t : List (Signature.classPairs P)) : Licenser :=
  .classical { Param := PUnit, Dom := fun _ ↦ σ, Cod := fun _ ↦ P, op := fun _ ↦ p.environment t }

/-- The domain reached through `t` carries the strength `s` of negation. -/
def Carries (t : List (Signature.classPairs P)) (s : Negation.Strength) : Prop :=
  (p.licenser t).Carries s

/-- The licensing condition: some domain carries the strength of negation that licenses the
item, and some domain does not carry the strength that blocks it. -/
def Licenses (π : PolarityItem) : Prop :=
  (∀ s ∈ π.licensor, ∃ t ∈ p.layers.tails, p.Carries t s) ∧
    ∀ s ∈ π.antiLicensor, ∃ t ∈ p.layers.tails, ¬p.Carries t s

theorem carries_iff :
    p.Carries t s ↔ s.toSignature.HoldsFor (p.environment t) ∧ ¬Monotone (p.environment t) := by
  have ha (h : s.toSignature.HoldsFor (p.environment t)) : Antitone (p.environment t) :=
    Signature.holdsFor_anti_iff.1 (h.of_le (by cases s <;> decide))
  cases s <;>
    simp only [Carries, licenser, Licenser.Carries, Licenser.IsStrawsonDE, Licenser.IsStrawsonUE,
      Licenser.exhaustified, Licenser.Holds]
  · exact ⟨fun h ↦ ⟨Signature.holdsFor_anti_iff.2 (h.1 ⟨⟩), fun hm ↦ h.2 fun _ ↦ hm⟩,
      fun h ↦ ⟨fun _ ↦ Signature.holdsFor_anti_iff.1 h.1, fun hm ↦ h.2 (hm ⟨⟩)⟩⟩
  all_goals exact ⟨fun h ↦ ⟨h.2 ⟨⟩, fun hm ↦ h.1.2 fun _ ↦ hm⟩,
    fun h ↦ ⟨⟨fun _ ↦ ha h.1, fun hm ↦ h.2 (hm ⟨⟩)⟩, fun _ ↦ h.1⟩⟩

/-- A domain of positive sign carries no strength of negation. -/
theorem not_carries_of_sign_eq_one (h : p.sign t = 1) : ¬p.Carries t s := fun hc ↦
  (p.carries_iff.1 hc).2 (p.monotone_environment h)

/-- A domain carries the strengths its signature realizes, once its environment is not
constant. -/
theorem carries_of_le_strength (hs : (s : WithBot Negation.Strength) ≤ p.strength t)
    (hne : p.environment t ⊥ ≠ p.environment t ⊤) : p.Carries t s := by
  have hf := (p.holdsFor_environment t).of_le (Signature.le_toSignature_of_le_negationStrength hs)
  refine p.carries_iff.2 ⟨hf, fun hm ↦ hne (le_antisymm (hm bot_le) ?_)⟩
  exact Signature.holdsFor_anti_iff.1 (hf.of_le (by cases s <;> decide)) bot_le

/-- A domain of negative sign carries weak strength, once its environment is not constant. -/
theorem carries_weak_of_sign_eq_neg_one (h : p.sign t = -1)
    (hne : p.environment t ⊥ ≠ p.environment t ⊤) : p.Carries t .weak := by
  obtain ⟨s', hs'⟩ := WithBot.ne_bot_iff_exists.1 (p.strength_ne_bot_iff.2 h)
  exact p.carries_of_le_strength (hs' ▸ WithBot.coe_le_coe.2 (by cases s' <;> decide)) hne

/-- An item that a strength licenses is anti-licensed when every domain has positive sign. -/
theorem not_licenses_of_mem_licensor (hs : s ∈ π.licensor)
    (h : ∀ t ∈ p.layers.tails, p.sign t = 1) : ¬p.Licenses π := fun hl ↦
  let ⟨t, ht, hc⟩ := hl.1 s hs
  p.not_carries_of_sign_eq_one (h t ht) hc

/-- An item that a strength blocks is anti-licensed when every domain carries it. -/
theorem not_licenses_of_mem_antiLicensor (hs : s ∈ π.antiLicensor)
    (h : ∀ t ∈ p.layers.tails, p.Carries t s) : ¬p.Licenses π := fun hl ↦
  let ⟨t, ht, hc⟩ := hl.2 s hs
  hc (h t ht)

end Path

end PolarityItem
