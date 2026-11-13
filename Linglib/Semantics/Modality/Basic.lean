module

public import Linglib.Core.Order.UpperLower.Principal
public import Linglib.Semantics.Degree.PositiveStandard
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Tactic.DeriveFintype

/-!
# Modal force and flavor

This file defines the vocabulary of modal typology. A modal force is a quantificational
strength, necessity, weak necessity or possibility, ordered by strength. On a degree semantics of
modality a force is a standard on one scale of propositions, and the strength order is the order
of the standards (`ModalForce.monotone_standard`). A modal flavor is a
source of modality, epistemic, deontic, bouletic or circumstantial, after Kratzer, and a
force-flavor pair is one point of the space of modal meanings. Condoravdi's temporal perspective
and orientation locate a modal claim in time.

## Main definitions

* `Modality.QuantificationalForce`, existential or universal, with its dual and the action of
  `Polarity`; `Modality.ModalForce.quantificational` reads a force's.
* `Modality.ModalForce`, with the strength order `possibility < weakNecessity < necessity`.
* `Modality.ModalForce.standard`: the standard a force sets on a scale of propositions.
* `Modality.ModalFlavor` and the pair type `Modality.ForceFlavor`.
* `Modality.TemporalPerspective`, `Modality.TemporalOrientation`.

## Main statements

* `Modality.ModalForce.monotone_standard`, `Modality.ModalForce.strictMono_standard`: a stronger
  force sets a stronger standard, so the strength order is the order of the standards.
* `Modality.ModalForce.standard_possibility_mem`, `Modality.ModalForce.standard_weakNecessity_mem`:
  possibility's standard is a minimum standard, which the scale fixes, and weak necessity's a
  threshold, which it does not.

## References

* [kratzer-1981]
* [lassiter-2017]
* [grano-2026]
* [von-fintel-iatridou-2008]
* [rubinstein-2014]
* [agha-jeretic-2022]
* [agha-jeretic-2026]
* [imel-guo-steinert-threlkeld-2026]
* [zeijlstra-2007]
* [nauze-2008]
* [matthewson-2016]
* [condoravdi-2002]
-/

@[expose] public section

namespace Modality

/-! ### Modal force -/

/-- The quantificational force of a modal: existential or universal quantification over its
domain of worlds. -/
inductive QuantificationalForce where
  | existential
  | universal
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace QuantificationalForce

/-- The strength of a quantificational force, existential the weaker. -/
def rank : QuantificationalForce → ℕ
  | existential => 0
  | universal => 1

/-- Quantificational forces are ordered by strength: over a nonempty domain a universal claim
entails the existential one. -/
instance : LinearOrder QuantificationalForce := LinearOrder.lift' rank (by decide)

instance : BoundedOrder QuantificationalForce where
  top := universal
  le_top := by decide
  bot := existential
  bot_le := by decide

/-- The dual exchanges the two forces, as negation does: what is not possible is necessarily
not. -/
def dual : QuantificationalForce → QuantificationalForce
  | existential => universal
  | universal => existential

theorem dual_involutive : Function.Involutive dual := by rintro (_ | _) <;> rfl

@[simp] theorem dual_dual (q : QuantificationalForce) : q.dual.dual = q := dual_involutive q

theorem dual_ne (q : QuantificationalForce) : q.dual ≠ q := by cases q <;> decide

/-- A polarity acts on quantificational forces, the negative polarity taking the dual. -/
instance : MulAction Polarity QuantificationalForce :=
  .ofEndHom (Polarity.lift ⟨dual, dual_involutive.comp_self⟩)

@[simp] theorem negative_smul (q : QuantificationalForce) : Polarity.negative • q = q.dual := rfl

end QuantificationalForce

/-- A modal force is a quantificational strength. Weak necessity, *ought* and *should*, lies
between necessity and possibility ([von-fintel-iatridou-2008]); whether it quantifies
universally over a narrower domain ([von-fintel-iatridou-2008]), compares alternatives
([rubinstein-2014]) or predicates of a plurality of worlds ([agha-jeretic-2022]) is open
([agha-jeretic-2026]). -/
inductive ModalForce where
  | necessity
  | weakNecessity
  | possibility
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace ModalForce

/-- The strength of a force, possibility the weakest. -/
def rank : ModalForce → ℕ
  | possibility => 0
  | weakNecessity => 1
  | necessity => 2

/-- Forces are ordered by strength: a necessity claim entails the weak necessity claim, which
entails the possibility claim. -/
instance : LinearOrder ModalForce := LinearOrder.lift' rank (by decide)

instance : BoundedOrder ModalForce where
  top := necessity
  le_top := by decide
  bot := possibility
  bot_le := by decide

/-- The quantificational force of a force, weak necessity quantifying universally
([von-fintel-iatridou-2008]). -/
def quantificational : ModalForce → QuantificationalForce
  | possibility => .existential
  | weakNecessity | necessity => .universal

theorem monotone_quantificational : Monotone quantificational := by
  intro f g h
  cases f <;> cases g <;> first | exact absurd h (by decide) | decide

/-! ### Forces as standards -/

section Standard
variable {D : Type*} [LinearOrder D] [OrderBot D] {θ θ' : D}

/-- On a degree semantics of modality, the standard a force sets on a scale of propositions:
possibility asks for a degree above the least, and weak necessity and necessity for degrees
from their thresholds `θ` and `θ'` ([lassiter-2017], [grano-2026]). -/
def standard (θ θ' : D) : ModalForce → UpperSet D
  | possibility => .Ioi ⊥
  | weakNecessity => .Ici θ
  | necessity => .Ici θ'

/-- With thresholds in order above the least degree, a stronger force sets a stronger standard,
so a necessity claim entails the weak necessity claim, which entails the possibility claim. -/
theorem monotone_standard (hθ : ⊥ < θ) (hθθ' : θ ≤ θ') : Monotone (standard θ θ') := by
  intro f g hfg
  cases f <;> cases g <;> first
    | exact le_rfl
    | exact absurd hfg (by decide)
    | exact UpperSet.Ioi_le_Ici hθ
    | exact UpperSet.Ioi_le_Ici (hθ.trans_le hθθ')
    | exact (UpperSet.Ici_strictMono D).monotone hθθ'

/-- On a dense scale with thresholds strictly in order, the strength order of the forces is
exactly the order of their standards. -/
theorem strictMono_standard [DenselyOrdered D] (hθ : ⊥ < θ) (hθθ' : θ < θ') :
    StrictMono (standard θ θ') := by
  obtain ⟨x, hx, hxθ⟩ := exists_between hθ
  refine (monotone_standard hθ hθθ'.le).strictMono_of_injective fun f g h ↦ ?_
  have hx' := SetLike.ext_iff.1 h x
  have hθ'' := SetLike.ext_iff.1 h θ
  cases f <;> cases g <;>
    simp [standard, hx, hxθ.not_ge, (hxθ.trans hθθ').not_ge, hθθ'.not_ge] at hx' hθ'' ⊢

/-- Possibility's standard is a minimum standard, the one existential closure above the least
degree gives ([grano-2026]), and so one the scale fixes. -/
theorem standard_possibility_mem :
    standard θ θ' .possibility ∈ PositiveStandard.minEndpoint.standards D :=
  ⟨⊥, isBot_bot, rfl⟩

/-- Weak necessity's standard is a threshold, which the scale does not fix, so that weak
necessity, like a relative adjective, needs a comparison class ([grano-2026] §7). -/
theorem standard_weakNecessity_mem :
    standard θ θ' .weakNecessity ∈ PositiveStandard.contextual.standards D :=
  ⟨θ, .inr rfl⟩

end Standard

end ModalForce

/-! ### Modal flavor -/

/-- A modal flavor is the source of a modal claim: an epistemic or a circumstantial modal base,
or a circumstantial base ordered by what the law requires or what someone wants
([kratzer-1981]); teleological modality, ordered by goals, counts as circumstantial. -/
inductive ModalFlavor where
  | epistemic
  | deontic
  | bouletic
  | circumstantial
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- A force-flavor pair is one point of the modal semantic space of
[imel-guo-steinert-threlkeld-2026], which has two forces and three flavors; weak necessity
([agha-jeretic-2026]) and bouletic flavor ([kratzer-1981]) extend the space to twelve points. -/
abbrev ForceFlavor := ModalForce × ModalFlavor

/-- The force of a force-flavor pair. -/
abbrev ForceFlavor.force : ForceFlavor → ModalForce := Prod.fst

/-- The flavor of a force-flavor pair. -/
abbrev ForceFlavor.flavor : ForceFlavor → ModalFlavor := Prod.snd

/-! ### Modal-temporal axes

The two temporal axes of modal interpretation ([condoravdi-2002] §2): the perspective is the
time at which the modal base and ordering source are evaluated, the orientation the relation
between the perspective time and the prejacent's time. [condoravdi-2002] uses only the future
and past orientations. -/

/-- The time at which a modal base and ordering source are evaluated. -/
inductive TemporalPerspective where
  /-- Evaluation at the utterance time. -/
  | present
  /-- Evaluation at a prior time, as under a perfect. -/
  | past
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The relation between the perspective time and the prejacent's instantiation time. -/
inductive TemporalOrientation where
  /-- The prejacent is instantiated before the perspective time. -/
  | past
  /-- The prejacent coincides with the perspective time. -/
  | present
  /-- The prejacent is instantiated at or after the perspective time. -/
  | future
  deriving DecidableEq, Repr, Inhabited, Fintype

end Modality
