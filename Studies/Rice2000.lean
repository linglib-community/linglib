module

public import Linglib.Morphology.Morphotactics.Template.Precedence
public import Linglib.Morphology.Morphotactics.RelevanceHierarchy
public import Mathlib.Logic.Relation
public import Mathlib.Order.Hom.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Rice 2000: morpheme order and semantic scope

[rice-2000] takes the positions of the Slave verb, traditionally listed as a template, and
orders them by semantic scope. `Below a b` holds when one of her ordering principles places `b`
structurally above `a`, and the scope order `≤` on positions is the reflexive transitive closure
of `Below`. It is a partial order on some positions only: the quantifiers and the incorporates
are not ordered with each other, and the qualifiers are ordered with nothing.

The Athapaskan verb puts a position of greater scope to the right. `position` is the place of a
position in the template, counted from the left, as a monotone map from the scope order to `ℕ`;
since it is injective, the template is a linear extension of the scope order. In the vocabulary
of `Morphotactics.Template`, the prefixes of `template` ascend away from the stem along the dual
of the scope order (`prefixesAscend_toDual`). As languages, the strings the template admits are
among those in which no position stands before one in its scope
(`language_le_pairwise_scope`), and scope alone also admits the orders the template excludes
among unordered positions (`incorporate_quantifier`).

They do not ascend along [bybee-1985]'s relevance hierarchy (`not_prefixesAscend_relevance`):
the first and second person subject stands between the aspect positions and the stem.

## Implementation notes

`Below` has one constructor for each pair of positions that the summary of ordering principles
orders by a stated principle. The order of first and second person subjects after the aspect
positions is described there as fixed without a principle of its own, so the two are left
unordered; `position_strictMono` holds of any further pair that respects the template. The
voice and valence position, the root and the aspect suffix enter no principle.

## TODO

The principles that order preverbs among themselves and subsituation aspects among themselves,
the override of subject over object by definiteness, and the comparison of the templates of the
other languages of the family are not formalized.

## References

* [rice-2000]
* [bybee-1985]
-/

@[expose] public section

namespace Rice2000

open Morphology

/-- The positions of the Slave verb, from the left; the root is not a position. -/
inductive Slot where
  /-- Preverbs. -/
  | preverb
  /-- Quantificational elements. -/
  | quantifier
  /-- Incorporates. -/
  | incorporate
  /-- Object pronominals. -/
  | object
  /-- Third person subjects, the number subjects. -/
  | thirdSubject
  /-- Qualifiers. -/
  | qualifier
  /-- Subsituation aspect. -/
  | subsituation
  /-- Situation aspect. -/
  | situation
  /-- Viewpoint aspect. -/
  | viewpoint
  /-- First and second person subjects. -/
  | participantSubject
  /-- Voice and valence. -/
  | voice
  /-- The aspect suffix. -/
  | aspectSuffix
  deriving DecidableEq, Repr, Fintype

/-- (1): the template of the Slave verb. -/
def template : Morphotactics.Template Slot where
  prefixSlots := [.preverb, .quantifier, .incorporate, .object, .thirdSubject, .qualifier,
    .subsituation, .situation, .viewpoint, .participantSubject, .voice]
  suffixSlots := [.aspectSuffix]

/-! ### The scope order -/

/-- `Below a b`: an ordering principle places `b` structurally above `a`. -/
inductive Below : Slot → Slot → Prop
  /-- Quantifying above quantified. -/
  | quantified : Below .preverb .quantifier
  /-- Selector above selected: an incorporate selects the preverb. -/
  | selectedPreverb : Below .preverb .incorporate
  /-- Inherently referential above noninherently referential, among subjects. -/
  | referentialSubject : Below .thirdSubject .participantSubject
  /-- Inherently referential above noninherently referential: situation aspect. -/
  | referentialSituation : Below .thirdSubject .situation
  /-- Inherently referential above noninherently referential: viewpoint aspect. -/
  | referentialViewpoint : Below .thirdSubject .viewpoint
  /-- Selector above selected: viewpoint selects situation aspect. -/
  | selectedSituation : Below .situation .viewpoint
  /-- Limiter above limited: situation aspect limits the reading of the object. -/
  | limited : Below .object .situation
  /-- Subsituation aspects are defined within situation aspects. -/
  | within : Below .subsituation .situation
  /-- Subject above object, for third person subjects. -/
  | objectThird : Below .object .thirdSubject
  /-- Subject above object, for first and second person subjects. -/
  | objectParticipant : Below .object .participantSubject

instance : DecidableRel Below := fun a b ↦ by
  cases a <;> cases b <;> first | exact isTrue (by constructor) | exact isFalse nofun

/-- The scope order: the reflexive transitive closure of `Below`. -/
instance : Preorder Slot where
  le := Relation.ReflTransGen Below
  le_refl _ := .refl
  le_trans _ _ _ := .trans

theorem le_iff {a b : Slot} : a ≤ b ↔ Relation.ReflTransGen Below a b := .rfl

theorem Below.le {a b : Slot} (h : Below a b) : a ≤ b := .single h

/-! ### The template as a linear extension -/

/-- The place of a position in the template, counted from the left, as a monotone map from the
scope order. -/
def position : Slot →o ℕ where
  toFun := template.slots.idxOf
  monotone' a b h := by
    have step : ∀ a b, Below a b → template.slots.idxOf a ≤ template.slots.idxOf b := by decide
    induction h with
    | refl => exact le_rfl
    | tail _ hbc ih => exact ih.trans (step _ _ hbc)

@[simp] theorem position_apply (a : Slot) : position a = template.slots.idxOf a := rfl

theorem position_injective : Function.Injective position := by
  have : ∀ a b : Slot, template.slots.idxOf a = template.slots.idxOf b → a = b := by decide
  exact fun a b ↦ this a b

/-- A position of greater scope stands further right. -/
theorem position_strictMono : StrictMono position :=
  position.monotone.strictMono_of_injective position_injective

theorem not_quantifier_le_incorporate :
    ¬ Slot.quantifier ≤ Slot.incorporate ∧ ¬ Slot.incorporate ≤ Slot.quantifier := by
  constructor <;> intro h <;> rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, -⟩ <;>
    first | exact absurd h (by decide) | cases hc

/-- The prefixes of the Slave verb ascend away from the stem along the dual of the scope order:
no position stands outside one that has it in its scope. -/
theorem prefixesAscend_toDual :
    template.PrefixesAscend fun a ↦ some (OrderDual.toDual a) := by
  rw [Morphotactics.Template.prefixesAscend_iff_pairwise]
  have h : template.prefixSlots.Pairwise fun a b ↦ position a < position b := by decide
  refine h.imp fun {a b} hab x hx y hy hlt ↦ ?_
  obtain rfl := Option.some.inj hx
  obtain rfl := Option.some.inj hy
  exact (position_strictMono (OrderDual.toDual_lt_toDual.1 hlt)).not_gt hab

/-- Every string of positions the template admits is admitted by scope: no position stands
before one in its scope. -/
theorem language_le_pairwise_scope :
    template.language ≤ Language.pairwise fun a b : Slot ↦ ¬ b < a := fun _ hv ↦
  (Morphotactics.Template.mem_language_iff_pairwise.1 hv).2.imp fun hab hba ↦
    (hab.resolve_right (by simp [template])).not_gt (position_strictMono hba)

/-- Scope admits the incorporate before the quantifier, an order the template excludes. -/
theorem incorporate_quantifier :
    [Slot.incorporate, .quantifier] ∈ Language.pairwise (fun a b : Slot ↦ ¬ b < a) ∧
      [Slot.incorporate, .quantifier] ∉ template.language :=
  ⟨Language.pair_mem_pairwise.2 fun h ↦ not_quantifier_le_incorporate.1 h.le, by decide⟩

/-! ### Relevance -/

/-- The relevance category of a position: the pronominals are agreement, the three aspect
positions aspect, and voice and valence voice. -/
def relevance? : Slot → Option RelevanceHierarchy
  | .object | .thirdSubject | .participantSubject => some .agreement
  | .subsituation | .situation | .viewpoint => some .aspect
  | .voice => some .voice
  | .preverb | .quantifier | .incorporate | .qualifier | .aspectSuffix => none

/-- The prefixes of the Slave verb do not ascend along the relevance hierarchy. -/
theorem not_prefixesAscend_relevance : ¬ template.PrefixesAscend relevance? := by decide

end Rice2000
