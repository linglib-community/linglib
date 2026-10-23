module

public import Linglib.Semantics.Homogeneity.Plural
public import Linglib.Data.Examples.HaslingerEtAl2025
public import Mathlib.Order.UpperLower.Closure

/-!
# Haslinger, Rosina, Schmitt and Wurm (2025): On the relation between distributivity and maximality

Haslinger, Rosina, Schmitt and Wurm ask whether every obligatorily distributive operator blocks
non-maximal construals of its associate plural, and answer no. German *jed-* is distributive and
exception-intolerant in both its determiner and its distance use, *alle* and numeral indefinites
are exception-intolerant but not distributive, and definite plurals are neither (5); the
distance distributor *jeweils* fills the remaining cell, since some speakers accept it in
scenarios whose question under discussion makes an exception irrelevant, where DP-*jeder* is
rejected and distance *jeder* mostly rejected (§3). `Item.class` is the classification of (5),
which the paper's truth-value judgments in the scenarios of (3) confirm (`class_of_rows`), and
`jeweils_answers_Q` is their answer.

The semantics of §2 relativizes a predicate to a tolerance relation, (14), which relates a
plurality to the parts of it that are similar enough to it (`tolerant`). Varying the tolerance
yields exactly Križ and Spector's readings of the plural predication
(`exists_isTolerance_iff_mem_readings`), which is why footnote 3 can call the difference between
the two ways of modelling the parameter irrelevant. *all*, which quantifies over tolerances,
forces the maximal reading (`all_maximal`), and so does *each*, (21c), since an atom has no part
short of itself (`each_maximal`). An exception-tolerant distributor has to depend on the
tolerance itself, as *jeweils* does in (25): in the magnets scenario of (23) it is true under the
tolerance the explosion question induces (`jeweils_accepts_magnets`) and false for the speakers
whose tolerance is the identity (`jeweils_identity_rejects_magnets`). The hypothetical determiner
*jeder\** of (27) is (25) applied to the sum of its restrictor, so the framework does not predict
the absence of exception-tolerant distributive determiners; the paper relates *jeweils*'s
permissiveness to its lacking a determiner use instead (`determiner_maximal`).

## Implementation notes

The questionnaire's ratings are prose: DP-*jeder* was overwhelmingly rejected, *jeweils* judged
bimodally, distance *jeder* mostly rejected, and 15 of 18 participants rated the *jeweils* member
of a minimal pair above its distance-*jeder* counterpart. The paper's examples and scenarios are
the rows of `Data/Examples/HaslingerEtAl2025.json`; the (3) judgments classify an item as
distributive when it is false in the cumulative scenario (3b) and as maximal when it is false in
the exception scenario (3c), which for *jeweils* out of the blue gives the maximal cell, the
non-maximal construal needing the questionnaire's contexts. Pluralities are finite sets of
individuals, whose empty set is excluded from the parts of a plurality as the paper's domain has
no empty individual. The tolerance of the magnets scenario tolerates every part of the boxes,
since one box with two magnets already answers the explosion question.

## References

* [haslinger-etal-2025]
* [kriz-spector-2021]
-/

@[expose] public section

namespace HaslingerEtAl2025

open Homogeneity

/-! ### Tolerance relations (§2.2) -/

section Tolerance

variable {α W : Type*} [PartialOrder α] {r : α → α → Prop} {Q : α → Set W} {y : α} {w : W}

/-- A tolerance relation (14) relates a part `z` of `y` to `y` when `z` is similar enough to
`y`. It is reflexive and contained in parthood, and whatever lies between a tolerated part and
the whole is tolerated too. -/
structure IsTolerance (r : α → α → Prop) : Prop where
  refl (x : α) : r x x
  le_of_rel {x y : α} : r x y → x ≤ y
  rel_of_le_of_le {x y z : α} : r x y → x ≤ z → z ≤ y → r z y

/-- The identity relation of (16a), under which no proper part is similar enough. -/
theorem isTolerance_eq : IsTolerance (α := α) (· = ·) :=
  ⟨fun _ ↦ rfl, fun h ↦ h ▸ le_rfl, fun h hxz hzy ↦ le_antisymm hzy (h ▸ hxz)⟩

/-- Parthood itself, (16b), under which every part is similar enough. -/
theorem isTolerance_le : IsTolerance (α := α) (· ≤ ·) :=
  ⟨fun _ ↦ le_rfl, id, fun _ _ hzy ↦ hzy⟩

/-- A predicate relativized to a tolerance (15a) holds of `y` where it holds of a non-bottom
part of `y` that is similar enough to `y`. -/
def tolerant (r : α → α → Prop) (Q : α → Set W) (y : α) : Set W :=
  {w | ∃ z, r z y ∧ ¬ IsBot z ∧ w ∈ Q z}

/-- Under the identity relation, (16a), the predication is maximal. -/
theorem tolerant_eq (hy : ¬ IsBot y) : tolerant (· = ·) Q y = Q y := by
  ext
  simp only [tolerant]
  grind

/-- Every tolerance yields one of [kriz-spector-2021]'s readings and every reading comes from a
tolerance, which is why footnote 3 can set the difference aside. -/
theorem exists_isTolerance_iff_mem_readings {p : Set W} :
    (∃ r, IsTolerance r ∧ p = tolerant r Q y) ↔ p ∈ readings Q y := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨upperClosure {z | r z y}, subset_upperClosure (hr.refl y), Set.ext fun w ↦
      ⟨fun ⟨z, hz, hzb, hw⟩ ↦ ⟨z, subset_upperClosure hz, hr.le_of_rel hz, hzb, hw⟩, ?_⟩⟩
    rintro ⟨z, ⟨a, ha, haz⟩, hzy, hzb, hw⟩
    exact ⟨z, hr.rel_of_le_of_le ha haz hzy, hzb, hw⟩
  · rintro ⟨U, hyU, rfl⟩
    refine ⟨fun z x ↦ z = x ∨ (z ≤ x ∧ z ∈ U), ⟨fun _ ↦ .inl rfl, ?_, ?_⟩, Set.ext fun w ↦ ?_⟩
    · rintro z x (rfl | ⟨hzx, -⟩)
      exacts [le_rfl, hzx]
    · rintro z x u (rfl | ⟨-, hz⟩) hzu hux
      exacts [.inl (le_antisymm hux hzu), .inr ⟨hux, U.upper hzu hz⟩]
    · refine ⟨fun ⟨z, hz, hzy, hzb, hw⟩ ↦ ⟨z, .inr ⟨hzy, hz⟩, hzb, hw⟩, ?_⟩
      rintro ⟨z, rfl | ⟨hzy, hz⟩, hzb, hw⟩
      exacts [⟨z, hyU, le_rfl, hzb, hw⟩, ⟨z, hz, hzy, hzb, hw⟩]

/-- *all*, which quantifies over tolerances (20), forces the maximal reading. -/
theorem all_maximal (hy : ¬ IsBot y) :
    (∀ r, IsTolerance r → w ∈ tolerant r Q y) ↔ w ∈ Q y := by
  refine ⟨fun h ↦ ?_, fun h r hr ↦ ⟨y, hr.refl y, hy, h⟩⟩
  obtain ⟨z, rfl, -, hw⟩ := h _ isTolerance_eq
  exact hw

end Tolerance

/-! ### *each* (§2.3) -/

section Distributivity

variable {Atom W : Type*} {r : Finset Atom → Finset Atom → Prop}

private theorem minimal_singleton (a : Atom) : Minimal (¬ IsBot ·) ({a} : Finset Atom) := by
  refine ⟨fun h ↦ Finset.singleton_ne_empty a (isBot_iff_eq_bot.1 h), fun z hz hza ↦ ?_⟩
  grind [isBot_iff_eq_bot]

/-- *each* (21c) is maximal even over a predicate relativized to a tolerance (§2.3, (21d)). -/
theorem each_maximal (hr : IsTolerance r) (Q : Finset Atom → Set W) (x : Finset Atom) :
    {w | ∀ a ∈ x, w ∈ tolerant r Q {a}} = {w | ∀ a ∈ x, w ∈ Q {a}} := by
  have h (a : Atom) : tolerant r Q {a} = Q {a} := by
    have := (exists_isTolerance_iff_mem_readings (Q := Q) (y := {a})).1 ⟨r, hr, rfl⟩
    rwa [readings_of_minimal (minimal_singleton a), Set.mem_singleton_iff] at this
  simp only [h]

end Distributivity

/-! ### The classification of (5) -/

/-- The four cells of (5) cross obligatory distributivity with exception intolerance. -/
inductive DistMaxClass where
  | distMax
  | distNonMax
  | nonDistMax
  | nonDistNonMax
  deriving DecidableEq, Repr

/-- The item applies its predicate to each atom separately. -/
def DistMaxClass.isDistributive : DistMaxClass → Prop
  | .distMax | .distNonMax => True
  | .nonDistMax | .nonDistNonMax => False

instance : DecidablePred DistMaxClass.isDistributive
  | .distMax | .distNonMax => isTrue trivial
  | .nonDistMax | .nonDistNonMax => isFalse not_false

/-- The item tolerates no exceptions. -/
def DistMaxClass.isMaximal : DistMaxClass → Prop
  | .distMax | .nonDistMax => True
  | .distNonMax | .nonDistNonMax => False

instance : DecidablePred DistMaxClass.isMaximal
  | .distMax | .nonDistMax => isTrue trivial
  | .distNonMax | .nonDistNonMax => isFalse not_false

/-- The expressions of (5) and (22) are the distance distributor *jeweils* and the determiner and
distance uses of *jed-*, beside *alle*, numeral indefinites and definite plurals. -/
inductive Item where
  | definitePlural
  | numeralIndefinite
  | alle
  | jederDP
  | jederDistance
  | jeweils
  deriving DecidableEq, Repr, Fintype

/-- Whether the item is a determiner. -/
def Item.IsDeterminer : Item → Prop
  | .jederDP | .alle | .numeralIndefinite => True
  | .definitePlural | .jederDistance | .jeweils => False

instance : DecidablePred Item.IsDeterminer
  | .jederDP | .alle | .numeralIndefinite => isTrue trivial
  | .definitePlural | .jederDistance | .jeweils => isFalse not_false

/-- The classification of (5), obligatory distributivity crossed with exception intolerance. -/
def Item.class : Item → DistMaxClass
  | .definitePlural => .nonDistNonMax
  | .numeralIndefinite | .alle => .nonDistMax
  | .jederDP | .jederDistance => .distMax
  | .jeweils => .distNonMax

theorem jeweils_answers_Q :
    Item.jeweils.class.isDistributive ∧ ¬ Item.jeweils.class.isMaximal := by decide

theorem four_cells : ∀ c : DistMaxClass, ∃ i : Item, i.class = c
  | .distMax => ⟨.jederDP, rfl⟩
  | .distNonMax => ⟨.jeweils, rfl⟩
  | .nonDistMax => ⟨.alle, rfl⟩
  | .nonDistNonMax => ⟨.definitePlural, rfl⟩

/-- §4 observation: among the attested items, every determiner is exception-intolerant. -/
theorem determiner_maximal : ∀ i : Item, i.IsDeterminer → i.class.isMaximal := by decide

/-! ### The scenarios of (3) -/

/-- The classification an example row's judgments in (3) determine: distributive if false
in the cumulative scenario (3b), maximal if false in the exception scenario (3c). -/
def classOfDatum (ex : Datum) : Option DistMaxClass := do
  let b ← ex.feature? "trueIn3b"
  let c ← ex.feature? "trueIn3c"
  pure <| match b == "no", c == "no" with
    | true, true => .distMax
    | true, false => .distNonMax
    | false, true => .nonDistMax
    | false, false => .nonDistNonMax

/-- The rows of (1), (2), (4) and (22a) classify the items as (5) does, *jeweils* out
of the blue included. -/
theorem class_of_rows :
    ∀ p ∈ [(Item.jederDP, Examples.ex1), (.jederDistance, Examples.ex2), (.alle, Examples.ex4a),
      (.numeralIndefinite, Examples.ex4b), (.definitePlural, Examples.ex4c)],
      classOfDatum p.2 = some p.1.class := by
  decide

theorem jeweils_maximal_out_of_the_blue : classOfDatum Examples.ex22a = some .distMax := by
  decide

/-! ### The magnets scenario of (23) -/

/-- The five boxes of (23a). -/
abbrev Box := Fin 5

/-- Every box but the fifth contains two magnets. -/
def hasTwoMagnets (b : Box) : Prop := b < 4

instance : DecidablePred hasTwoMagnets := fun b ↦ inferInstanceAs (Decidable (b < 4))

/-- *jeder* in either use, (21c), is false in the scenario, since one box has one magnet. -/
theorem jeder_rejects_magnets : ¬ ∀ b ∈ (Finset.univ : Finset Box), hasTwoMagnets b := by
  decide

/-- *jeweils* (25) is true under the tolerance the explosion question induces, and so is the
determiner of (27). -/
theorem jeweils_accepts_magnets :
    () ∈ tolerant (· ≤ ·) (fun z ↦ {_u | ∀ b ∈ z, hasTwoMagnets b}) (Finset.univ : Finset Box) :=
  ⟨{0, 1, 2, 3}, Finset.subset_univ _, isBot_iff_eq_bot.not.2 (by decide), by decide⟩

theorem jeweils_identity_rejects_magnets :
    () ∉ tolerant (· = ·) (fun z ↦ {_u | ∀ b ∈ z, hasTwoMagnets b}) (Finset.univ : Finset Box) := by
  rw [tolerant_eq (isBot_iff_eq_bot.not.2 (by decide))]
  exact jeder_rejects_magnets

end HaslingerEtAl2025
