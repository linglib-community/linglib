module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Semantics.Degree.MeasurePhrase
public import Linglib.Semantics.Degree.Scale
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.English.Adjectives
public import Linglib.Data.Examples.HayKennedyLevin1999

/-!
# Hay, Kennedy and Levin (1999): Scalar Structure Underlies Telicity in "Degree Achievements"

This file formalizes Hay, Kennedy and Levin's analysis of degree achievements. The morpheme that
forms the verb contributes an increase, true of an event when the affected argument's degree on
the base adjective's scale at the end of the event is its degree at the start plus a difference
value, and the predicate is telic exactly when the difference value is bounded, specifying a
positive lower bound on the change. A bound can come from a measure phrase or *completely*, from
*significantly* as against *slightly*, from the maximal value of a closed-range base adjective, or
from a conventional value supplied by context. A bound that is only implicated can be cancelled and
one supplied by overt material cannot, which is why an unmodified degree achievement takes both
adverbials and one modified by *completely* only the in-adverbial. The paper's closed-range and
open-range adjectives are checked against the scales of the English fragment.

## Implementation notes

* Degrees form a densely ordered abelian group, whose addition extends the paper's degree addition
  (15), defined only when a summand is positive. The maximal scale value is a degree `top` rather
  than a top element, and density makes "some amount" and *slightly* unbounded.
* In a group, INCREASE (16) is the differential comparative of the argument at the end of the
  event with itself at the start (`increase_iff_differentialComparative`).
* A modifier's difference values are the degrees that stand in a `Degree.Comparison` to its
  degree: exactly a measure phrase's, at least *significantly*'s standard, and among the positive
  ones at most *slightly*'s. A monotone decreasing modifier is one whose comparison gives a lower
  set.
* The readings of a description are its admissible difference values. Overt material fixes one;
  with none there is the literal "some amount" and, when a maximal or conventional value is
  salient, the bounded value it implicates. The in-adverbial and for-adverbial tests are read as
  the existence of a bounded and of an unbounded reading.
* The *almost* test and the causative component of transitive degree achievements are not
  modelled.

## TODO

* The parallel with the mass–count distinction and the redefinition of the incremental theme as
  the difference value (§4.2), which want a shared substrate with Krifka's cumulativity.

## References

* [J. Hay, C. Kennedy and B. Levin, *Scalar Structure Underlies Telicity in “Degree
  Achievements”* (1999)][hay-kennedy-levin-1999]
* [C. Kennedy and L. McNally, *Scale Structure, Degree Modification, and the Semantics of Gradable
  Predicates* (2005)][kennedy-mcnally-2005]
* [D. R. Dowty, *Word Meaning and Montague Grammar* (1979)][dowty-1979]
* [M. Krifka, *Nominal Reference, Temporal Constitution and Quantification in Event Semantics*
  (1989)][krifka-1989]
-/

@[expose] public section

namespace HayKennedyLevin1999

open Degree Set
open English
open English.Verbs hiding Verb

/-! ### The difference value (§2) -/

section Semantics

variable {α δ T : Type*}

/-- `Increase φ x d t₀ t₁` holds when `x` increases in `φ`-ness by the difference value `d`
    over an event that begins at `t₀` and ends at `t₁` ((16)). -/
def Increase [Add δ] (φ : α → T → δ) (x : α) (d : δ) (t₀ t₁ : T) : Prop :=
  φ x t₀ + d = φ x t₁

/-- A description holds when `x` increases by some difference value in `D`, the positive
    degrees for (17a) and `{5 inches}` for (17b). -/
def Describes [Add δ] (φ : α → T → δ) (x : α) (D : Set δ) (t₀ t₁ : T) :
    Prop :=
  ∃ d ∈ D, Increase φ x d t₀ t₁

/-- In a group an increase by `d` is the differential comparative of `x` at the end of the event
    with `x` at its start: `x` ends up `d` more `φ` than it began. -/
theorem increase_iff_differentialComparative [AddCommGroup δ] {φ : α → T → δ} {x : α} {d : δ}
    {t₀ t₁ : T} : Increase φ x d t₀ t₁ ↔ DifferentialComparative (φ x) t₁ t₀ d := by
  rw [Increase, DifferentialComparative, sub_eq_iff_eq_add', eq_comm]

/-- Given the difference value, an event's end degree is determined by its start degree (§3). -/
theorem Increase.end_unique [Add δ] {φ : α → T → δ} {x : α} {d : δ}
    {t₀ t₁ t₂ : T} (h₁ : Increase φ x d t₀ t₁) (h₂ : Increase φ x d t₀ t₂) :
    φ x t₁ = φ x t₂ :=
  h₁.symm.trans h₂

/-- In a group a description holds exactly when the difference between the final and the
    initial degree is one of its difference values. -/
theorem describes_iff_sub_mem [AddCommGroup δ] {φ : α → T → δ} {x : α} {D : Set δ}
    {t₀ t₁ : T} : Describes φ x D t₀ t₁ ↔ φ x t₁ - φ x t₀ ∈ D :=
  ⟨fun ⟨_, hd, h⟩ ↦ by rwa [← h, add_sub_cancel_left], fun h ↦ ⟨_, h, add_sub_cancel _ _⟩⟩

variable [AddCommGroup δ] [LinearOrder δ]

/-- A set of difference values is **bounded** when it has a positive lower bound. Once that
    much change has happened the truth conditions are met, so the event has an endpoint and the
    predicate is telic (§3.1). -/
def IsBounded (D : Set δ) : Prop := ∃ b, 0 < b ∧ b ∈ lowerBounds D

/-- The implicit difference value "some amount" is any positive degree ((9a)). -/
def someAmount : Set δ := Comparison.gt.interval 0

/-- A measure phrase fixes the difference value at exactly its degree `m` ((18)). -/
def measurePhrase (m : δ) : Set δ := Comparison.eq.interval m

/-- *Completely* fixes the difference value at the change that takes the initial degree `i`
    to the scale's maximal value `top` ((21)). -/
def completely (top i : δ) : Set δ := measurePhrase (top - i)

/-- *Significantly*, a monotone increasing modifier, admits the difference values of at
    least the contextual standard `s` ((23)). -/
def significantly (s : δ) : Set δ := Comparison.ge.interval s

/-- *Slightly*, a monotone decreasing modifier, admits the positive difference values of at
    most `s` ((24)). -/
def slightly (s : δ) : Set δ := Comparison.le.interval s ∩ someAmount

theorem isBounded_measurePhrase {m : δ} (hm : 0 < m) : IsBounded (measurePhrase m) :=
  ⟨m, hm, fun _ hd ↦ (Set.mem_singleton_iff.1 hd).ge⟩

theorem isBounded_completely [IsOrderedAddMonoid δ] {top i : δ} (hi : i < top) :
    IsBounded (completely top i) :=
  ⟨top - i, sub_pos.2 hi, fun _ hd ↦ (Set.mem_singleton_iff.1 hd).ge⟩

theorem isBounded_significantly {s : δ} (hs : 0 < s) : IsBounded (significantly s) :=
  ⟨s, hs, fun _ hd ↦ hd⟩

/-- A lower set of difference values, like *slightly*'s, sets no bound on positive increases (§3.1).
-/
theorem not_isBounded_inter_someAmount [DenselyOrdered δ] {D : Set δ} (hD : IsLowerSet D)
    {d : δ} (hd : d ∈ D) (hd₀ : 0 < d) : ¬ IsBounded (D ∩ someAmount) := by
  rintro ⟨b, hb, hlow⟩
  obtain ⟨c, hc₀, hc⟩ := exists_between (lt_min hb hd₀)
  exact (hlow (mem_inter (hD (lt_min_iff.1 hc).2.le hd) hc₀)).not_gt (lt_min_iff.1 hc).1

theorem not_isBounded_slightly [DenselyOrdered δ] {s : δ} (hs : 0 < s) :
    ¬ IsBounded (slightly s) :=
  not_isBounded_inter_someAmount (isLowerSet_Iic s) (mem_Iic.2 le_rfl) hs

theorem not_isBounded_someAmount [DenselyOrdered δ] : ¬ IsBounded (someAmount (δ := δ)) :=
  fun h ↦ h.elim fun b hb ↦
    not_isBounded_inter_someAmount isLowerSet_univ (mem_univ b) hb.1 (by rwa [univ_inter])

/-! ### Readings (§3.2–§3.4) -/

/-- A modifier is the overt material that can fix a difference value. -/
inductive Modifier (δ : Type*)
  | none
  | measure (m : δ)
  | completely
  | significantly (s : δ)
  | slightly (s : δ)

/-- A context supplies what can bound the difference value when nothing overt does, the
    maximal value of a closed-range base adjective's scale (§3.2) or a conventional maximum for the
    affected object (§3.3). -/
structure Context (δ : Type*) where
  scaleMax : Option δ
  conventionalMax : Option δ

/-- The salient bound of a context is its scale maximum if there is one, and otherwise its
    conventional maximum. -/
def Context.bound (c : Context δ) : Option δ := c.scaleMax <|> c.conventionalMax

/-- The admissible difference values of a description whose argument starts at degree `i`
    are the one that overt material fixes or, with none, the literal "some amount" and, when a bound
    is salient, the value the most informative interpretation implicates. -/
def readings (c : Context δ) (i : δ) : Modifier δ → Set (Set δ)
  | .none => {someAmount} ∪ (c.bound.map fun m ↦ {completely m i}).getD ∅
  | .measure m => {measurePhrase m}
  | .completely => (c.scaleMax.map fun m ↦ {completely m i}).getD ∅
  | .significantly s => {significantly s}
  | .slightly s => {slightly s}

/-- A description has a telic reading, which an in-adverbial needs, when one of its
    admissible difference values is bounded. -/
def HasTelic (c : Context δ) (i : δ) (m : Modifier δ) : Prop :=
  ∃ D ∈ readings c i m, IsBounded D

/-- A description has an atelic reading, which a for-adverbial needs, when one of its
    admissible difference values is unbounded. -/
def HasAtelic (c : Context δ) (i : δ) (m : Modifier δ) : Prop :=
  ∃ D ∈ readings c i m, ¬ IsBounded D

variable {c : Context δ} {i : δ}

/-- A measure phrase makes the predicate telic, whatever the base adjective ((18)–(20)). -/
theorem hasTelic_measure {m : δ} (hm : 0 < m) : HasTelic c i (.measure m) :=
  ⟨_, rfl, isBounded_measurePhrase hm⟩

theorem not_hasAtelic_measure {m : δ} (hm : 0 < m) : ¬ HasAtelic c i (.measure m) :=
  fun ⟨_, hD, h⟩ ↦ h (Set.mem_singleton_iff.1 hD ▸ isBounded_measurePhrase hm)

/-- *Completely* makes the predicate telic and leaves no atelic reading ((21)–(22), (35)). -/
theorem hasTelic_completely [IsOrderedAddMonoid δ] {top : δ} (hc : c.scaleMax = some top)
    (hi : i < top) :
    HasTelic c i .completely :=
  ⟨_, by simp [readings, hc], isBounded_completely hi⟩

theorem not_hasAtelic_completely [IsOrderedAddMonoid δ] {top : δ} (hc : c.scaleMax = some top)
    (hi : i < top) :
    ¬ HasAtelic c i .completely := by
  rintro ⟨D, hD, h⟩
  simp only [readings, hc, Option.map_some, Option.getD_some, Set.mem_singleton_iff] at hD
  exact h (hD ▸ isBounded_completely hi)

/-- *Completely* has no reading on an open-range base ((25b)). -/
theorem readings_completely_open (hc : c.scaleMax = none) : readings c i .completely = ∅ := by
  simp [readings, hc]

/-- *Significantly* makes the predicate telic ((23)). -/
theorem hasTelic_significantly {s : δ} (hs : 0 < s) : HasTelic c i (.significantly s) :=
  ⟨_, rfl, isBounded_significantly hs⟩

/-- *Slightly* leaves the predicate atelic ((24)). -/
theorem hasAtelic_slightly [DenselyOrdered δ] {s : δ} (hs : 0 < s) :
    HasAtelic c i (.slightly s) :=
  ⟨_, rfl, not_isBounded_slightly hs⟩

theorem not_hasTelic_slightly [DenselyOrdered δ] {s : δ} (hs : 0 < s) :
    ¬ HasTelic c i (.slightly s) :=
  fun ⟨_, hD, h⟩ ↦ not_isBounded_slightly hs (Set.mem_singleton_iff.1 hD ▸ h)

/-- With a salient bound, from a closed-range base or from convention, an unmodified degree
    achievement has a telic reading ((26), (28), (34a)). -/
theorem hasTelic_of_bound [IsOrderedAddMonoid δ] {b : δ} (hb : c.bound = some b) (hi : i < b) :
    HasTelic c i .none :=
  ⟨completely b i, by simp [readings, hb], isBounded_completely hi⟩

/-- The literal reading is always available, so the implicated bound can be cancelled and the
    for-adverbial is felicitous ((32), (34b)). -/
theorem hasAtelic_none [DenselyOrdered δ] : HasAtelic c i .none :=
  ⟨someAmount, by simp [readings], not_isBounded_someAmount⟩

/-- Without a salient bound an unmodified degree achievement has only the atelic reading
    ((27), (30), (31)). -/
theorem not_hasTelic_none [DenselyOrdered δ] (hb : c.bound = none) : ¬ HasTelic c i .none := by
  rintro ⟨D, hD, h⟩
  simp only [readings, hb, Option.map_none, Option.getD_none, Set.union_empty,
    Set.mem_singleton_iff] at hD
  exact not_isBounded_someAmount (hD ▸ h)

/-! ### Cancellability (§3.3, (32)–(33)) -/

/-- A bound supplied by overt material cannot be cancelled, so a rope straightened
    completely is completely straight ((33)). -/
theorem completely_not_cancellable {φ : α → T → δ} {x : α} {top : δ}
    {t₀ t₁ : T} (h : Describes φ x (completely top (φ x t₀)) t₀ t₁) :
    ¬ φ x t₁ < top := by
  obtain ⟨d, hd, hinc⟩ := h
  rw [Set.mem_singleton_iff.1 hd, Increase, add_sub_cancel] at hinc
  intro hlt
  rw [← hinc] at hlt
  exact lt_irrefl _ hlt

/-- A bound that is only implicated can be cancelled, the literal "some amount" being
    consistent with the maximal value not having been reached ((32)). -/
theorem someAmount_cancellable [IsOrderedAddMonoid δ] [DenselyOrdered δ] {i top : δ}
    (hi : i < top) :
    ∃ φ : Unit → Bool → δ,
      Describes φ () someAmount false true ∧ φ () true < top := by
  obtain ⟨j, hij, hjt⟩ := exists_between hi
  exact ⟨fun _ t ↦ if t then j else i, ⟨j - i, sub_pos.2 hij, by simp [Increase]⟩, by simpa⟩

end Semantics

/-! ### The English degree achievements (§3.2, (25)) -/

/-- The closed-range adjectives the paper names are *straight*, *empty* and *dry* ((25a)), and
    *flat*. -/
def closedRange : List GradableAdjective :=
  open English.Adjectives in [straight, empty, dry, flat]

/-- The open-range adjectives the paper names are *long*, *wide* and *short* ((25b)). -/
def openRange : List GradableAdjective :=
  open English.Adjectives in [long, wide, short]

/-- The fragment's adjectives agree with the paper's classification, a closed-range adjective
    having a scale with a maximum and an open-range one a scale without. -/
theorem fragment_range :
    (∀ a ∈ closedRange, a.boundedness.HasMax) ∧ ∀ a ∈ openRange, ¬ a.boundedness.HasMax := by
  decide

/-- The fragment's degree achievements measure change on scales of the same kind as their base
    adjectives, *straighten*, *dry* and *flatten* on a scale with a maximum and *lengthen* and
    *widen* on one without. -/
theorem fragment_verbs :
    (∀ v ∈ [Verbs.straighten, Verbs.dry, Verbs.flatten], ∃ b ∈ v.changeScale, b.HasMax) ∧
    ∀ v ∈ [Verbs.lengthen, Verbs.widen], ∃ b ∈ v.changeScale, ¬ b.HasMax := by
  decide

/-- The default telicity the fragment derives for a degree achievement is the telicity of the
    unmodified reading in a context whose only salient bound is the scale's maximum, when it
    has one. -/
theorem defaultTelicity_iff (d : ScalarDimension) (i top : ℚ) (hi : i < top) :
    d.defaultTelicity = .telic ↔
      HasTelic ⟨if d.boundedness.HasMax then some top else none, none⟩ i .none := by
  rw [ScalarDimension.defaultTelicity_telic_iff_hasGreatest,
    ScalarDimension.hasGreatest_scale_iff]
  by_cases hmax : d.boundedness.HasMax
  · rw [ite_eq_left hmax]
    exact iff_of_true hmax (hasTelic_of_bound rfl hi)
  · rw [ite_eq_right hmax]
    exact iff_of_false hmax (not_hasTelic_none rfl)

end HayKennedyLevin1999
