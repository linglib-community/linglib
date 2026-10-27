module

public import Linglib.Fragments.English.PolarityItems
public import Mathlib.Order.Monotone.Basic

/-!
# Israel (2001): Minimizers, Maximizers and the Rhetoric of Scalar Reasoning

This file formalizes Israel's Scalar Model of polarity sensitivity. A scalar model, after
Fillmore, Kay and O'Connor, is a propositional function over an ordered scale whose values
pragmatically entail one another; a polarity item encodes a quantity relative to the scalar norm
and a rhetorical force, emphatic when the proposition it expresses entails the norm's and
attenuating when it is entailed by it (`Emphatic`, `Attenuating`). Scale preserving contexts are
the strictly monotone maps on propositions and scale reversing ones the strictly antitone maps,
the positive and negative directions of `Polarity.StrictMonoBy`, and the direction of the
expressed propositional function decides which quantities are emphatic
(`felicitous_iff_of_strictMonoBy`). The four cells of Figure 1 follow: emphatic items with low
values and attenuating items with high values need reversing contexts, the negative polarity
items, the other two cells preserving contexts. The inverted items of Section 4, maximizing NPIs
like *wild horses* and minimizing PPIs like *for peanuts*, follow from the thematic logic of
Section 5: a propositional role either impedes the eventuality, so that the function is antitone
in quantity, or facilitates it, so that it is monotone (`Role`). Directions compose as
polarities multiply, so that the licensing context of any item is the product of the signs of
its force, quantity and role (`licensingContext`, `felicitous_iff`). The pecuniary paradox
dissolves because a resource is impeding and a reward facilitating, and the ambiguous
superlatives of Section 7 are the same composition with an existential and a
perceptual-ability scale.

## Implementation notes

* Pragmatic entailment between the propositions of a scalar model is modelled as inclusion of
  sets of worlds; the paper's point that the relevant inferences may be pragmatic rather than
  logical is not represented.
* The paper's classifications of the English items of `Fragments/English/PolarityItems.lean`
  by force, quantity and role live here (`classified`), and the derived licensing context is
  checked against the fragment's record of each item as an NPI or PPI.

## References

* [israel-2001]
* [israel-1996]
* [fillmore-kay-oconnor-1988]
* [fauconnier-1975]
* [ladusaw-1979]
-/

@[expose] public section

namespace Israel2001

open PolarityItem English.PolarityItems

variable {α W : Type*} [LinearOrder α]

/-- Rhetorical force: the expressed proposition is more informative than the scalar norm, or
less. -/
inductive Force
  | emphatic
  | attenuating
  deriving DecidableEq

/-- The sign of a force: emphatic items are negative, attenuating ones positive. -/
def Force.sign : Force → Polarity
  | .emphatic => .negative
  | .attenuating => .positive

/-- Quantity relative to the norm: the size, amount or degree the item denotes. -/
inductive Quantity
  | small
  | large
  deriving DecidableEq

/-- The sign of a quantity relative to the norm: small is negative, large positive. -/
def Quantity.sign : Quantity → Polarity
  | .small => .negative
  | .large => .positive

/-- A quantity `x` stands to the norm `n` as the item's quantity says. -/
def Quantity.Rel : Quantity → α → α → Prop
  | .small, x, n => x < n
  | .large, x, n => n < x

/-- The effect of a propositional role on the likelihood of the eventuality (Section 5): a
patient, theme, increment, expense or duration impedes it, the bigger the less likely, and an
agent, stimulus, reward, instrument or interval facilitates it. -/
inductive Role
  | impeding
  | facilitating
  deriving DecidableEq

/-- The direction of the propositional function of a role: strictly antitone in quantity for an
impeding role, so that bigger values entail smaller ones, strictly monotone for a facilitating
one. -/
def Role.sign : Role → Polarity
  | .impeding => .negative
  | .facilitating => .positive

/-- The proposition expressed with quantity `x` is emphatic when it pragmatically entails the
proposition at the norm. -/
def Emphatic (Q : α → Set W) (n x : α) : Prop := Q x < Q n

/-- It is attenuating when the proposition at the norm entails it. -/
def Attenuating (Q : α → Set W) (n x : α) : Prop := Q n < Q x

/-- An item of a given force is felicitous when the proposition expressed has that force. -/
def Felicitous : Force → (α → Set W) → α → α → Prop
  | .emphatic, Q, n, x => Emphatic Q n x
  | .attenuating, Q, n, x => Attenuating Q n x

variable {Q : α → Set W} {n x : α}

theorem emphatic_iff_of_strictMono (h : StrictMono Q) (hx : x ≠ n) : Emphatic Q n x ↔ x < n :=
  ⟨λ hE => (lt_or_gt_of_ne hx).resolve_right λ hn => lt_asymm (h hn) hE, λ hxn => h hxn⟩

theorem emphatic_iff_of_strictAnti (h : StrictAnti Q) (hx : x ≠ n) : Emphatic Q n x ↔ n < x :=
  ⟨λ hE => (lt_or_gt_of_ne hx).resolve_left λ hn => lt_asymm (h hn) hE, λ hxn => h hxn⟩

theorem attenuating_iff_of_strictMono (h : StrictMono Q) (hx : x ≠ n) :
    Attenuating Q n x ↔ n < x :=
  ⟨λ hA => (lt_or_gt_of_ne hx).resolve_left λ hn => lt_asymm (h hn) hA, λ hxn => h hxn⟩

theorem attenuating_iff_of_strictAnti (h : StrictAnti Q) (hx : x ≠ n) :
    Attenuating Q n x ↔ x < n :=
  ⟨λ hA => (lt_or_gt_of_ne hx).resolve_right λ hn => lt_asymm (h hn) hA, λ hxn => h hxn⟩

theorem felicitous_iff_of_strictMono (h : StrictMono Q) (hx : x ≠ n) (d : Force) :
    Felicitous d Q n x ↔ (d = .emphatic ↔ x < n) := by
  cases d
  · simp [Felicitous, emphatic_iff_of_strictMono h hx]
  · rw [Felicitous, attenuating_iff_of_strictMono h hx]
    simp only [reduceCtorEq, false_iff, not_lt]
    exact ⟨le_of_lt, λ h => lt_of_le_of_ne h hx.symm⟩

theorem felicitous_iff_of_strictAnti (h : StrictAnti Q) (hx : x ≠ n) (d : Force) :
    Felicitous d Q n x ↔ (d = .emphatic ↔ n < x) := by
  cases d
  · simp [Felicitous, emphatic_iff_of_strictAnti h hx]
  · rw [Felicitous, attenuating_iff_of_strictAnti h hx]
    simp only [reduceCtorEq, false_iff, not_lt]
    exact ⟨le_of_lt, λ h => lt_of_le_of_ne h hx⟩

/-- The direction of the context in which an item of a given force, quantity and role is
felicitous, scale preserving (positive) or scale reversing (negative), the scalar logic of
Sections 2 and 5: the product of the three signs. Emphatic small items in impeding roles and
emphatic large items in facilitating roles are NPIs, needing scale reversal, as are attenuating
items of the opposite quantities; the remaining cells are PPIs. -/
def licensingContext (d : Force) (q : Quantity) (r : Role) : Polarity := d.sign * q.sign * r.sign

theorem Quantity.lt_iff_of_rel {q : Quantity} (hq : q.Rel x n) : x < n ↔ q = .small := by
  cases q
  · exact iff_of_true hq rfl
  · exact iff_of_false (lt_asymm hq) (by decide)

theorem Quantity.gt_iff_of_rel {q : Quantity} (hq : q.Rel x n) : n < x ↔ q = .large := by
  cases q
  · exact iff_of_false (lt_asymm hq) (by decide)
  · exact iff_of_true hq rfl

theorem felicitous_iff_of_strictMonoBy {δ : Polarity} {q : Quantity} (h : δ.StrictMonoBy Q)
    (hq : q.Rel x n) (d : Force) : Felicitous d Q n x ↔ d.sign = δ * q.sign := by
  have hx : x ≠ n := by
    cases q
    · exact ne_of_lt (hq : x < n)
    · exact (ne_of_lt (hq : n < x)).symm
  cases δ
  · rw [felicitous_iff_of_strictMono h hx, Quantity.lt_iff_of_rel hq]
    cases d <;> cases q <;> decide
  · rw [felicitous_iff_of_strictAnti h hx, Quantity.gt_iff_of_rel hq]
    cases d <;> cases q <;> decide

/-- An item is felicitous exactly in contexts of its licensing direction, for any scalar model of
its role (Figures 1 and 3). -/
theorem felicitous_iff {P : α → Set W} {f : Set W → Set W} {r : Role} {c : Polarity}
    {d : Force} {q : Quantity} (hr : r.sign.StrictMonoBy P) (hc : c.StrictMonoBy f)
    (hq : q.Rel x n) : Felicitous d (f ∘ P) n x ↔ c = licensingContext d q r := by
  rw [felicitous_iff_of_strictMonoBy (hc.comp hr) hq, licensingContext]
  cases c <;> cases d <;> cases q <;> cases r <;> decide

-- (15), (16)
theorem pecuniary_paradox {res rew : α → Set W} {f : Set W → Set W} (hres : StrictAnti res)
    (hrew : StrictMono rew) (hf : StrictAnti f) (hx : x < n) :
    Emphatic (f ∘ res) n x ∧ ¬ Emphatic (f ∘ rew) n x ∧ Emphatic rew n x ∧ ¬ Emphatic res n x :=
  ⟨(emphatic_iff_of_strictMono (hf.comp hres) (ne_of_lt hx)).2 hx,
    λ h => lt_asymm hx ((emphatic_iff_of_strictAnti (hf.comp_strictMono hrew) (ne_of_lt hx)).1 h),
    (emphatic_iff_of_strictMono hrew (ne_of_lt hx)).2 hx,
    λ h => lt_asymm hx ((emphatic_iff_of_strictAnti hres (ne_of_lt hx)).1 h)⟩

-- (22)
theorem superlative_ambiguity {exist ability : α → Set W} {f : Set W → Set W}
    (hex : StrictAnti exist) (hab : StrictMono ability) (hf : StrictAnti f) {lo hi : α}
    (hlo : lo < n) (hhi : n < hi) : Emphatic (f ∘ exist) n lo ∧ Emphatic (f ∘ ability) n hi :=
  ⟨(emphatic_iff_of_strictMono (hf.comp hex) (ne_of_lt hlo)).2 hlo,
    (emphatic_iff_of_strictAnti (hf.comp_strictMono hab) (ne_of_lt hhi).symm).2 hhi⟩

/-! ### The classified lexicon -/

/-- A fragment entry with the paper's classification by force, quantity and role. -/
structure Classified where
  item : PolarityItem
  force : Force
  quantity : Quantity
  role : Role

/-- The paper's classifications of the fragment's items: the canonical minimizers and the degree
items of Figure 1 in impeding roles, the maximizing NPIs and minimizing PPIs of Section 4 in
facilitating roles. -/
def classified : List Classified :=
  [⟨atAll, .emphatic, .small, .impeding⟩, ⟨liftAFinger, .emphatic, .small, .impeding⟩,
   ⟨budgeAnInch, .emphatic, .small, .impeding⟩, ⟨somewhat, .attenuating, .small, .impeding⟩,
   ⟨rather, .attenuating, .small, .impeding⟩, ⟨tonsOf, .emphatic, .large, .impeding⟩,
   ⟨awfully, .emphatic, .large, .impeding⟩, ⟨wildHorses, .emphatic, .large, .facilitating⟩,
   ⟨allTheTeaInChina, .emphatic, .large, .facilitating⟩,
   ⟨aTenFootPole, .emphatic, .large, .facilitating⟩,
   ⟨inAMillionYears, .emphatic, .large, .facilitating⟩,
   ⟨atTheDropOfAHat, .emphatic, .small, .facilitating⟩,
   ⟨inAJiffy, .emphatic, .small, .facilitating⟩, ⟨forAPittance, .emphatic, .small, .facilitating⟩,
   ⟨forASong, .emphatic, .small, .facilitating⟩]

/-- The direction of the context the fragment records an item as sensitive to: preserving for a
PPI, reversing for an NPI. -/
def PolarityItem.contextType (e : PolarityItem) : Option Polarity :=
  if e.antiLicensor.isSome then some .positive else if e.licensor.isSome then some .negative
  else none

theorem classified_licensingContext :
    ∀ c ∈ classified,
      PolarityItem.contextType c.item = some (licensingContext c.force c.quantity c.role) := by
  decide

end Israel2001
