module

public import Mathlib.Order.Basic
public import Mathlib.Order.Birkhoff
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Affectedness

This file defines Beavers's affectedness hierarchy. A predicate affects a theme to one of four
degrees according to how specific it is about the theme's change along a scale. It may entail that
the theme reaches a goal the predicate fixes (a quantized change), that the theme reaches some goal
(a non-quantized change), that the theme is related to a scale without necessarily changing
(potential for change), or nothing about change at all. Each degree is an existential
generalization of the one above it, over the goal, over the result and over the scalar relation, so
the degrees form a chain of weakening truth conditions. The three degrees above the bottom are the
entailments, and each degree is the set of entailments at most as strong as it. The role a predicate
assigns its theme is the set of entailments it has, closed under entailment, and every such set is
the role of some predicate, so exactly four roles are contentful.

## Main definitions

* `AffectednessDegree`: the four degrees, ordered by strength.
* `AffectednessEntailment`: the three degrees above the bottom, the affectedness entailments.
* `AffectednessDegree.entailments`: a degree as the set of entailments it comprises.
* `QuantizedChange`: the predicate entails that the theme reaches a goal it fixes.
* `NonQuantizedChange`: the predicate entails that the theme reaches some goal.
* `PotentialChange`: the predicate relates the theme to a scale.
* `AffectednessDegree.Holds`: the condition each degree names.
* `affectednessRole`: the entailments a predicate has, as a lower set.

## Main results

* `AffectednessDegree.holds_antitone`: each degree entails every weaker one.
* `affectednessRole_antitone`: a predicate that entails another has at least its entailments.
* `exists_affectednessRole_eq`: every lower set of entailments is the role of some predicate.

## Implementation notes

* A predicate `φ x e` comes with its scalar θ-relation `θ x s e`, relating its theme to a scale in
  an event, and a result relation `R x s g e`, the theme reaching the state `g` on the scale `s`.
  Beavers defines the result only together with the predicate's scalar relation, so the result
  conditions conjoin the two, and every step of the hierarchy is then existential generalization.
* Potential for change is lexical data, not a consequence of the predicate's truth conditions.
  Beavers's existential over θ-relations is trivial unless it ranges over the predicate's own roles,
  so the scalar relation `θ` is a parameter, and any predicate has potential for change under
  `θ := fun _ _ _ ↦ True`. For the same reason the unspecified degree holds of every predicate.
* A quantized change fixes one goal for every event of the predicate, and a non-quantized change
  one goal for each event, `∃ g, ∀ x e` against `∀ x e, ∃ g`.
* The paper binds the event existentially and states the degrees of a sentence; here they are
  stated of a relation between themes and events.

## References

* [J. Beavers, *On Affectedness* (2011)][beavers-2011]
* [J. Beavers, *The structure of lexical meaning: Why semantics really matters*
  (2010)][beavers-2010]
-/

@[expose] public section

namespace ArgumentStructure

/-! ### The degrees -/

/-- The degrees of affectedness, weakest first ([beavers-2011] (62)). -/
inductive AffectednessDegree where
  /-- Nothing is entailed about change, as for the object of *see* or *ponder*. -/
  | unspecified
  /-- The theme is related to a scale without necessarily changing, as for *hit* or *wipe*. -/
  | potential
  /-- The theme reaches some goal on a scale, as for *widen* or *cool*. -/
  | nonquantized
  /-- The theme reaches a goal the predicate fixes, as for *break* or *destroy*. -/
  | quantized
  deriving DecidableEq, Fintype, Repr, Inhabited

namespace AffectednessDegree

/-- The strength of a degree is its position in the chain. -/
def strength : AffectednessDegree → ℕ
  | .unspecified => 0
  | .potential => 1
  | .nonquantized => 2
  | .quantized => 3

instance : LinearOrder AffectednessDegree :=
  .lift' strength fun a b ↦ by cases a <;> cases b <;> simp [strength]

theorem le_iff_strength_le {a b : AffectednessDegree} : a ≤ b ↔ a.strength ≤ b.strength :=
  Iff.rfl

instance : OrderBot AffectednessDegree where
  bot := .unspecified
  bot_le a := by cases a <;> decide

theorem supIrred_iff_ne_bot {d : AffectednessDegree} : SupIrred d ↔ d ≠ ⊥ := by
  rw [supIrred_iff_not_isMin, isMin_iff_eq_bot]

instance : DecidablePred (SupIrred : AffectednessDegree → Prop) :=
  fun _ ↦ decidable_of_iff _ supIrred_iff_ne_bot.symm

end AffectednessDegree

/-- An affectedness entailment is a degree that is not the join of weaker ones, one of the three
degrees above `unspecified`, entailing a quantized change, a non-quantized change or potential for
change. -/
abbrev AffectednessEntailment := {d : AffectednessDegree // SupIrred d}

/-- A degree is the set of entailments at most as strong as it, and every set of entailments closed
under entailment is a degree, by Birkhoff's representation of the chain of degrees. -/
noncomputable def AffectednessDegree.entailments :
    AffectednessDegree ≃o LowerSet AffectednessEntailment :=
  OrderIso.lowerSetSupIrred

theorem AffectednessDegree.coe_entailments (d : AffectednessDegree) :
    (d.entailments : Set AffectednessEntailment) = {e | e.1 ≤ d} :=
  rfl

/-! ### The affectedness conditions -/

section Conditions

variable {α S G β : Type*} (θ : α → S → β → Prop) (R : α → S → G → β → Prop)
  (φ : α → β → Prop)

/-- A predicate effects a **quantized change** to the goal `g` when every event of it relates its
theme to a scale on which the theme reaches `g` ([beavers-2011] (60a)). -/
def QuantizedChange (g : G) : Prop := ∀ x e, φ x e → ∃ s, θ x s e ∧ R x s g e

/-- A predicate effects a **non-quantized change** when every event of it relates its theme to a
scale on which the theme reaches some goal ([beavers-2011] (60b)). -/
def NonQuantizedChange : Prop := ∀ x e, φ x e → ∃ s, θ x s e ∧ ∃ g, R x s g e

/-- A predicate gives its theme **potential for change** when every event of it relates the theme
to a scale ([beavers-2011] (60c)). -/
def PotentialChange : Prop := ∀ x e, φ x e → ∃ s, θ x s e

variable {θ R φ}

theorem QuantizedChange.nonQuantizedChange {g : G} (h : QuantizedChange θ R φ g) :
    NonQuantizedChange θ R φ :=
  fun x e hx ↦ let ⟨s, hs, hg⟩ := h x e hx; ⟨s, hs, g, hg⟩

theorem NonQuantizedChange.potentialChange (h : NonQuantizedChange θ R φ) :
    PotentialChange θ φ :=
  fun x e hx ↦ let ⟨s, hs, _⟩ := h x e hx; ⟨s, hs⟩

variable (θ R φ)

/-- The condition an affectedness degree names is a quantized change to some goal, a non-quantized
change, potential for change, or nothing ([beavers-2011] (60)). -/
def AffectednessDegree.Holds : AffectednessDegree → Prop
  | .unspecified => True
  | .potential => PotentialChange θ φ
  | .nonquantized => NonQuantizedChange θ R φ
  | .quantized => ∃ g, QuantizedChange θ R φ g

/-- Each degree entails every weaker one, the Affectedness Hierarchy ([beavers-2011] (62)). -/
theorem AffectednessDegree.holds_antitone : Antitone (AffectednessDegree.Holds θ R φ) := by
  intro d d' h
  cases d <;> cases d' <;> first
    | exact absurd h (by decide)
    | exact fun _ ↦ trivial
    | exact id
    | exact fun ⟨_, hq⟩ ↦ hq.nonQuantizedChange
    | exact NonQuantizedChange.potentialChange
    | exact fun ⟨_, hq⟩ ↦ hq.nonQuantizedChange.potentialChange

variable {θ R φ} in
theorem AffectednessDegree.Holds.of_le {ψ : α → β → Prop} (h : φ ≤ ψ) :
    ∀ {d}, AffectednessDegree.Holds θ R ψ d → AffectednessDegree.Holds θ R φ d
  | .unspecified, hd => hd
  | .potential, hd => fun x e hx ↦ hd x e (h x e hx)
  | .nonquantized, hd => fun x e hx ↦ hd x e (h x e hx)
  | .quantized, ⟨g, hd⟩ => ⟨g, fun x e hx ↦ hd x e (h x e hx)⟩

end Conditions

/-! ### The role of a predicate -/

section Role

variable {α S G β : Type*} (θ : α → S → β → Prop) (R : α → S → G → β → Prop)
  (φ : α → β → Prop)

/-- The role a predicate assigns its theme is the set of affectedness entailments it has
([beavers-2010] (65)), closed under entailment by the Affectedness Hierarchy. -/
def affectednessRole : LowerSet AffectednessEntailment :=
  ⟨{e | AffectednessDegree.Holds θ R φ e.1},
    fun _ _ h ↦ AffectednessDegree.holds_antitone θ R φ h⟩

variable {θ R φ}

@[simp] theorem mem_affectednessRole {e : AffectednessEntailment} :
    e ∈ affectednessRole θ R φ ↔ AffectednessDegree.Holds θ R φ e.1 :=
  .rfl

variable (θ R) in
/-- A predicate that entails another has at least its entailments. -/
theorem affectednessRole_antitone : Antitone (affectednessRole θ R) :=
  fun _ _ h _ ↦ AffectednessDegree.Holds.of_le h

theorem affectednessRole_eq_entailments_iff {d : AffectednessDegree} :
    affectednessRole θ R φ = d.entailments ↔
      ∀ e : AffectednessEntailment, AffectednessDegree.Holds θ R φ e.1 ↔ e.1 ≤ d := by
  rw [← SetLike.coe_set_eq, AffectednessDegree.coe_entailments, Set.ext_iff]
  rfl

/-- Every lower set of affectedness entailments is the role of some predicate, so each of the four
roles of [beavers-2010] (66) is contentful. -/
theorem exists_affectednessRole_eq (s : LowerSet AffectednessEntailment) :
    ∃ (θ : Unit → Unit → Bool → Prop) (R : Unit → Unit → Bool → Bool → Prop)
      (φ : Unit → Bool → Prop), affectednessRole θ R φ = s := by
  obtain ⟨d, rfl⟩ := AffectednessDegree.entailments.surjective s
  cases d
  on_goal 1 => refine ⟨fun _ _ _ ↦ False, fun _ _ _ _ ↦ False, fun _ _ ↦ True, ?_⟩
  on_goal 2 => refine ⟨fun _ _ _ ↦ True, fun _ _ _ _ ↦ False, fun _ _ ↦ True, ?_⟩
  on_goal 3 => refine ⟨fun _ _ _ ↦ True, fun _ _ g e ↦ g = e, fun _ _ ↦ True, ?_⟩
  on_goal 4 => refine ⟨fun _ _ _ ↦ True, fun _ _ _ _ ↦ True, fun _ _ ↦ True, ?_⟩
  all_goals
    refine affectednessRole_eq_entailments_iff.2 fun ⟨e, he⟩ ↦ ?_
    cases e <;> simp_all [AffectednessDegree.Holds,
      QuantizedChange, NonQuantizedChange, PotentialChange,
      AffectednessDegree.le_iff_strength_le, AffectednessDegree.strength]

end Role

end ArgumentStructure
