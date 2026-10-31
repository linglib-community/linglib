/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.Composition
public import Linglib.Semantics.Composition.WithAlternatives
public import Linglib.Semantics.Polarity.Basic

/-!
# Environments of a polarity item

The environment of a polarity item in a constituent is the meaning of the constituent as a function
of the meaning of the item, and the constituent is downward entailing with respect to the item when
its environment is antitone. The constituents in which the acceptability of an item is evaluated,
its domains, form a chain from its minimal domain to the sentence (`PolarityItem.Path`): each
domain is the one below under a layer, so the environment of a domain composes the layers below it
with the environment of the minimal domain. The licensing condition asks of a negative polarity item
that some domain be downward entailing with respect to it, and of a positive one that some domain
not be (`PolarityItem.Path.Licenses`).

Each layer carries a signature sound for it, so the sign of a domain is the product of the signs
below it, and [it fixes the direction of the domain's
environment](##PolarityItem.Path.antitone_environment). A layer of negative sign, a
downward-entailing expression, therefore [reverses the sign of every domain above
it](##PolarityItem.Path.sign_cons): an item licensed in a domain can be anti-licensed in the
next, and licensed again in the one after. When the minimal domain comes with scalar alternatives,
the layers apply to each of them, so every domain has [its meaning with its
alternatives](##PolarityItem.Path.withAlternatives), as in alternative semantics.

## Implementation notes

* A sign fixes only a non-strict direction, and a constant environment is both monotone and
  antitone, so anti-licensing a negative polarity item in a domain of positive sign also takes two
  meanings of the item that the environment separates (`PolarityItem.Path.not_licenses_negative`).

## References

* [gajewski-2005]
* [homer-2021]
* [icard-2012]
-/

@[expose] public section

namespace PolarityItem

open NaturalLogic

/-- Sentential negation as a layer: complementation, anti-morphic. -/
def negation {P : Type*} [BooleanAlgebra P] : Signature.soundPairs P :=
  ⟨(compl, .antiAddMult), compl_soundFor_antiAddMult⟩

/-- The path of a polarity item from its minimal domain to the sentence: the environment of the
minimal domain with a signature sound for it, and the layers between successive domains, outermost
first, each with a signature sound for it. -/
structure Path (σ P : Type*) [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P] where
  /-- The environment of the minimal domain, as a function of the meaning of the item. -/
  minimal : σ → P
  /-- A signature sound for the environment of the minimal domain. -/
  signature : Signature
  sound : signature.SoundFor minimal
  /-- The layers between successive domains, outermost first, each with a signature sound for
  it. -/
  layers : List (Signature.soundPairs P)

namespace Path

variable {σ P : Type*} [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P] (p : Path σ P)
  {t : List (Signature.soundPairs P)}

/-- The environment of the domain reached through the layers `t`. -/
def environment (t : List (Signature.soundPairs P)) : σ → P :=
  (t.prod : Function.End P × Signature).1 ∘ p.minimal

/-- The sign of the domain reached through the layers `t`: the product of their signs with the
sign of the minimal domain. -/
def sign (t : List (Signature.soundPairs P)) : SignType :=
  (t.map fun l ↦ l.1.2.sign).prod * p.signature.sign

/-- The licensing condition: some domain is downward entailing with respect to a negative polarity
item, and some domain is not downward entailing with respect to a positive one. -/
def Licenses : Polarity → Prop
  | .negative => ∃ t ∈ p.layers.tails, Antitone (p.environment t)
  | .positive => ∃ t ∈ p.layers.tails, ¬Antitone (p.environment t)

@[simp]
theorem environment_nil : p.environment [] = p.minimal :=
  rfl

@[simp]
theorem environment_cons (l : Signature.soundPairs P) (t : List (Signature.soundPairs P)) :
    p.environment (l :: t) = l.1.1 ∘ p.environment t := by
  simp only [environment, List.prod_cons, Submonoid.coe_mul, Prod.fst_mul]
  rfl

section WithAlternatives

/-- The meaning of the domain reached through the layers `t` with its alternatives, when `A` gives
the alternatives of the minimal domain: the layers apply to each alternative. -/
def withAlternatives (A : σ → Set P) (t : List (Signature.soundPairs P)) (x : σ) :
    WithAlternatives P :=
  (t.prod : Function.End P × Signature).1 <$> ⟨p.minimal x, A x⟩

@[simp]
theorem ordinary_withAlternatives (A : σ → Set P) (t : List (Signature.soundPairs P)) (x : σ) :
    (p.withAlternatives A t x).ordinary = p.environment t x :=
  rfl

@[simp]
theorem withAlternatives_nil (A : σ → Set P) (x : σ) :
    p.withAlternatives A [] x = ⟨p.minimal x, A x⟩ :=
  id_map _

@[simp]
theorem withAlternatives_cons (A : σ → Set P) (l : Signature.soundPairs P)
    (t : List (Signature.soundPairs P)) (x : σ) :
    p.withAlternatives A (l :: t) x = l.1.1 <$> p.withAlternatives A t x := by
  simp only [withAlternatives, List.prod_cons, Submonoid.coe_mul, Prod.fst_mul]
  exact comp_map _ _ _

end WithAlternatives

/-- Adding a layer multiplies the sign of a domain by the sign of the layer. -/
@[simp]
theorem sign_cons (l : Signature.soundPairs P) (t : List (Signature.soundPairs P)) :
    p.sign (l :: t) = l.1.2.sign * p.sign t := by
  simp [sign, mul_assoc]

@[simp]
theorem sign_nil : p.sign [] = p.signature.sign := by
  simp [sign]

theorem soundFor_environment (t : List (Signature.soundPairs P)) :
    ((t.prod : Function.End P × Signature).2 * p.signature).SoundFor (p.environment t) :=
  Signature.SoundFor.comp t.prod.2 p.sound

theorem sign_eq (t : List (Signature.soundPairs P)) :
    ((t.prod : Function.End P × Signature).2 * p.signature).sign = p.sign t := by
  show _ = (t.map fun l ↦ l.1.2.sign).prod * p.signature.sign
  rw [Signature.sign_mul, Submonoid.coe_list_prod, Signature.sign_list_prod, List.map_map]
  rfl

theorem monotone_environment (h : p.sign t = 1) :
    Monotone (p.environment t) :=
  (p.soundFor_environment t).monotone_of_sign_eq_one ((p.sign_eq t).trans h)

/-- A domain of negative sign is downward entailing with respect to the item. -/
theorem antitone_environment (h : p.sign t = -1) :
    Antitone (p.environment t) :=
  (p.soundFor_environment t).antitone_of_sign_eq_neg_one ((p.sign_eq t).trans h)

theorem licenses_negative (ht : t ∈ p.layers.tails) (h : p.sign t = -1) :
    p.Licenses .negative :=
  ⟨t, ht, p.antitone_environment h⟩

theorem not_antitone_environment (h : p.sign t = 1) {a b : σ} (hab : a ≤ b)
    (hne : p.environment t a ≠ p.environment t b) : ¬Antitone (p.environment t) := fun ha ↦
  hne (le_antisymm (p.monotone_environment h hab) (ha hab))

theorem licenses_positive (ht : t ∈ p.layers.tails) (h : p.sign t = 1) {a b : σ} (hab : a ≤ b)
    (hne : p.environment t a ≠ p.environment t b) : p.Licenses .positive :=
  ⟨t, ht, p.not_antitone_environment h hab hne⟩

/-- A positive polarity item is anti-licensed when every domain has negative sign. -/
theorem not_licenses_positive (h : ∀ t ∈ p.layers.tails, p.sign t = -1) :
    ¬p.Licenses .positive := fun ⟨t, ht, hn⟩ ↦ hn (p.antitone_environment (h t ht))

/-- A negative polarity item is anti-licensed when every domain has positive sign and its
environment is not constant. -/
theorem not_licenses_negative
    (h : ∀ t ∈ p.layers.tails, p.sign t = 1 ∧
      ∃ a b, a ≤ b ∧ p.environment t a ≠ p.environment t b) :
    ¬p.Licenses .negative := fun ⟨t, ht, ha⟩ ↦
  let ⟨hs, _, _, hab, hne⟩ := h t ht
  p.not_antitone_environment hs hab hne ha

end Path

end PolarityItem
