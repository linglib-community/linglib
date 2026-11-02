module

public import Mathlib.Order.Sigma
public import Linglib.Semantics.Degree.Quotient
public import Linglib.Semantics.Negation.Polarity
public import Linglib.Semantics.Conditionals.SelectionFunction
public import Linglib.Data.Examples.Cresswell1976
public import Linglib.Data.Examples.Readers

/-!
# The semantics of degree

Cresswell's degree of comparison is a point paired with the ordering of its scale, and
*er than* holds of two degree properties when both are instantiated and every degree of the
first exceeds every degree of the second on their common scale, so a comparative across
scales is anomalous and a disjoined standard is compared universally. Mass nouns and plurals
carry degrees of volume and of number through the totality operator, degrees need no units
since any comparison relation yields a scale by quotienting, and the counterfactual *shorter
than he is* compares heights across worlds.

We take degrees on a family of scales to be mathlib's disjoint sum of the scales' orders and
prove the same-scale restriction, the universal reading of disjoined standards, the reduction
of the totality comparatives to volumes and cardinalities, the synonymy of *all* and *every*
given that there are men, the comparative on constructed degrees, and the counterfactual
through a Stalnaker selection function.

## Implementation notes

* The plural is read as in (49), a nonempty set of things satisfying the noun with its
  cardinality; as printed, (3.6) fixes the set to all of them, on which (54) would require
  the set of all men to walk.

## References

* [M. J. Cresswell, *The semantics of degree* (1976)][cresswell-1976]
* [R. C. Stalnaker, *A theory of conditionals* (1968)][stalnaker-1968]
-/

@[expose] public section

namespace Cresswell1976

open Degree OrderDual

/-! ### Comparison of degree properties (2.3), (2.7) -/

section Comparative

variable {D : Type*} [LT D] {ω ω' ω₁ ω₂ : Set D} {a b : D}

/-- *Er than* holds of two properties of degrees when both are instantiated and every degree of the
first exceeds every degree of the second (2.3). -/
def ErThan (ω ω' : Set D) : Prop := ω.Nonempty ∧ ω'.Nonempty ∧ ∀ a ∈ ω, ∀ b ∈ ω', b < a

/-- *As as* holds when every degree of the first exceeds or equals every degree of the second (2.7).
-/
def AsAs (ω ω' : Set D) : Prop := ω.Nonempty ∧ ω'.Nonempty ∧ ∀ a ∈ ω, ∀ b ∈ ω', b < a ∨ b = a

/-- *Exactly as as* holds when the degrees coincide (2.7). -/
def Exactly (ω ω' : Set D) : Prop := ω.Nonempty ∧ ω'.Nonempty ∧ ∀ a ∈ ω, ∀ b ∈ ω', a = b

theorem ErThan.asAs (h : ErThan ω ω') : AsAs ω ω' :=
  ⟨h.1, h.2.1, fun a ha b hb ↦ .inl (h.2.2 a ha b hb)⟩

theorem Exactly.asAs (h : Exactly ω ω') : AsAs ω ω' :=
  ⟨h.1, h.2.1, fun a ha b hb ↦ .inr (h.2.2 a ha b hb).symm⟩

-- (13), (18)
@[simp] theorem erThan_singleton : ErThan {a} {b} ↔ b < a := by simp [ErThan]

theorem erThan_singleton_toDual : ErThan {toDual a} {toDual b} ↔ a < b :=
  erThan_singleton.trans toDual_lt_toDual

@[simp] theorem asAs_singleton : AsAs {a} {b} ↔ b < a ∨ b = a := by simp [AsAs]

omit [LT D] in
@[simp] theorem exactly_singleton : Exactly {a} {b} ↔ a = b := by simp [Exactly]

-- footnote 10
theorem erThan_union (h₁ : ω₁.Nonempty) (h₂ : ω₂.Nonempty) :
    ErThan ω (ω₁ ∪ ω₂) ↔ ErThan ω ω₁ ∧ ErThan ω ω₂ :=
  ⟨fun ⟨h, _, hlt⟩ ↦ ⟨⟨h, h₁, fun a ha b hb ↦ hlt a ha b (.inl hb)⟩,
    ⟨h, h₂, fun a ha b hb ↦ hlt a ha b (.inr hb)⟩⟩,
   fun ⟨⟨h, _, hlt₁⟩, ⟨_, _, hlt₂⟩⟩ ↦
    ⟨h, h₁.inl, fun a ha b hb ↦ hb.elim (hlt₁ a ha b) (hlt₂ a ha b)⟩⟩

-- (39), (72)
theorem erThan_image_toDual : ErThan (toDual '' ω) (toDual '' ω') ↔ ErThan ω' ω := by
  simp only [ErThan, Set.image_nonempty, Set.forall_mem_image, toDual_lt_toDual, and_left_comm]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall₂_comm

end Comparative

section Substrate

variable {E α : Type*} {μ : E → α} {x y : E}

-- (2.7)
theorem asAs_singleton_iff_le [PartialOrder α] : AsAs {μ x} {μ y} ↔ μ y ≤ μ x :=
  asAs_singleton.trans le_iff_lt_or_eq.symm

end Substrate

/-! ### Degrees on a family of scales (2.1) -/

section Scales

variable {ι : Type*} {P : ι → Type*} [∀ i, LT (P i)] {ω ω' : Set (Σ i, P i)}

-- (2.3)
theorem ErThan.fst_eq (h : ErThan ω ω') {a b : Σ i, P i} (ha : a ∈ ω) (hb : b ∈ ω') :
    a.1 = b.1 :=
  (Sigma.lt_def.1 (h.2.2 a ha b hb)).1.symm

-- (23), (65), (69)
theorem not_erThan_of_fst_ne (h : ∀ a ∈ ω, ∀ b ∈ ω', a.1 ≠ b.1) : ¬ ErThan ω ω' :=
  fun he ↦ let ⟨a, ha⟩ := he.1; let ⟨b, hb⟩ := he.2.1; h a ha b hb (he.fst_eq ha hb)

theorem erThan_image_sigmaMk {i : ι} {ω ω' : Set (P i)} :
    ErThan (Sigma.mk i '' ω) (Sigma.mk i '' ω') ↔ ErThan ω ω' := by
  simp only [ErThan, Set.image_nonempty, Set.forall_mem_image, Sigma.mk_lt_mk_iff]

end Scales

/-! ### The scales of the paper's comparatives -/

/-- The examples compare on spatial and temporal distances, volumes, the numbers of (3.6), and the
unit-free scales of §4. -/
inductive Scale where
  | distance
  | time
  | volume
  | number
  | cleverness
  | beauty
  deriving DecidableEq

/-- A directed scale is the relation of a degree read upward or, for *short*, downward (2.1). -/
abbrev DirectedScale := Scale × Polarity

/-- The scale a `paperFeatures` label names. -/
def DirectedScale.ofLabel : String → Option DirectedScale
  | "distance" => some (.distance, .positive)
  | "distanceDownward" => some (.distance, .negative)
  | "time" => some (.time, .positive)
  | "volume" => some (.volume, .positive)
  | "number" => some (.number, .positive)
  | "cleverness" => some (.cleverness, .positive)
  | "beauty" => some (.beauty, .positive)
  | _ => none

/-- The scales of an example's two terms and its judgment. -/
def datum (e : Datum) :
    Option (DirectedScale × DirectedScale × Judgment) := do
  let l ← DirectedScale.ofLabel (← e.feature? "leftScale")
  let r ← DirectedScale.ofLabel (← e.feature? "rightScale")
  pure (l, r, e.judgment)

/-- The comparatives whose scales the paper records. -/
def data : List (DirectedScale × DirectedScale × Judgment) :=
  Examples.all.filterMap datum

theorem scale_ne_of_unacceptable : ∀ d ∈ data, d.2.2 = .unacceptable → d.1 ≠ d.2.1 := by
  decide

theorem not_erThan_of_unacceptable {P : DirectedScale → Type*} [∀ s, LT (P s)] {d}
    (hd : d ∈ data) (hj : d.2.2 = .unacceptable) {ω ω' : Set (Σ s, P s)}
    (hω : ∀ a ∈ ω, a.1 = d.1) (hω' : ∀ b ∈ ω', b.1 = d.2.1) : ¬ ErThan ω ω' :=
  not_erThan_of_fst_ne fun a ha b hb ↦ by
    rw [hω a ha, hω' b hb]; exact scale_ne_of_unacceptable d hd hj

/-! ### Superlatives, mass nouns and plurals ((2.6), §3) -/

section Totality

variable {E D : Type*} [LE D] (ω : E → D → Prop) (ω' : E → Prop)

/-- *Tot* gives the degree of the greatest part of whatever satisfies both predicates (3.2). -/
def tot : Set D := {u | IsGreatest {d | ∃ c, ω' c ∧ ω c d} u}

/-- *Est* holds when `a` bears a unique degree at or above every degree of anything (2.6). -/
def Est (a : E) : Prop := ∃! b, ω a b ∧ b ∈ upperBounds {d | ∃ c, ω c d}

-- (2.6), (27)
theorem est_iff (μ : E → D) (a : E) : Est (fun c d ↦ μ c = d) a ↔ ∀ c, μ c ≤ μ a := by
  simp [Est, upperBounds, ExistsUnique]

end Totality

section TotalityOrder

variable {E D : Type*} [PartialOrder D] {ω : E → D → Prop} {ω' : E → Prop}

theorem tot_eq_singleton {u : D} (h : IsGreatest {d | ∃ c, ω' c ∧ ω c d} u) : tot ω ω' = {u} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨h, fun _ h' ↦ h'.unique h⟩

-- (42), (44)
theorem erThan_tot_tot {E' : Type*} {ω₁ : E' → D → Prop} {ω₁' : E' → Prop} {u u₁ : D}
    (h : IsGreatest {d | ∃ c, ω' c ∧ ω c d} u) (h₁ : IsGreatest {d | ∃ c, ω₁' c ∧ ω₁ c d} u₁) :
    ErThan (tot ω ω') (tot ω₁ ω₁') ↔ u₁ < u := by
  rw [tot_eq_singleton h, tot_eq_singleton h₁, erThan_singleton]

end TotalityOrder

section Plural

variable {E : Type*} (noun : Finset E) (pred : E → Prop)

/-- *Pl* gives a nonempty set of things satisfying the noun, with its cardinality, a positive
integer, as degree ((3.6), (49)). -/
def Pl (a : Finset E) (n : ℕ) : Prop := a ⊆ noun ∧ a.Nonempty ∧ a.card = n

/-- *All* holds when something satisfies the plural and everything that does satisfies the predicate
(3.7). -/
def All {A B : Type*} (ω : A → B → Prop) (ω' : A → Prop) : Prop :=
  (∃ a b, ω a b) ∧ ∀ a, (∃ b, ω a b) → ω' a

-- (54), (55)
theorem tot_pl [DecidablePred pred] (h : (noun.filter pred).Nonempty) :
    tot (Pl noun) (fun a ↦ ∀ x ∈ a, pred x) = {(noun.filter pred).card} := by
  refine tot_eq_singleton ⟨⟨noun.filter pred, fun _ hx ↦ (Finset.mem_filter.1 hx).2,
    Finset.filter_subset _ _, h, rfl⟩, ?_⟩
  rintro _ ⟨a, ha, hsub, -, rfl⟩
  exact Finset.card_le_card fun x hx ↦ Finset.mem_filter.2 ⟨hsub hx, ha x hx⟩

-- (52), (55)
theorem erThan_tot_pl (man bird : Finset E) (walk fly : E → Prop) [DecidablePred walk]
    [DecidablePred fly] (hw : (man.filter walk).Nonempty) (hf : (bird.filter fly).Nonempty) :
    ErThan (tot (Pl man) (fun a ↦ ∀ x ∈ a, walk x)) (tot (Pl bird) (fun a ↦ ∀ x ∈ a, fly x)) ↔
      (bird.filter fly).card < (man.filter walk).card := by
  rw [tot_pl _ _ hw, tot_pl _ _ hf, erThan_singleton]

-- (3.8), (56), (57)
theorem all_pl_iff_forall :
    All (Pl noun) (fun a ↦ ∀ x ∈ a, pred x) ↔ noun.Nonempty ∧ ∀ x ∈ noun, pred x :=
  ⟨fun ⟨⟨_, _, hsub, hne, _⟩, h⟩ ↦
    ⟨hne.mono hsub, fun x hx ↦ h noun ⟨_, Finset.Subset.refl _, hne.mono hsub, rfl⟩ x hx⟩,
   fun ⟨hne, h⟩ ↦ ⟨⟨noun, _, Finset.Subset.refl _, hne, rfl⟩,
    fun _ ⟨_, hsub, _, _⟩ x hx ↦ h x (hsub hx)⟩⟩

end Plural

/-! ### Degrees from comparisons (§4) -/

-- (62), (4.2)
theorem erThan_singleton_mk {E : Type*} (φ : E → E → Prop) (a b : E) :
    ErThan ({⟦a⟧} : Set (CresswellDegree φ)) {⟦b⟧} ↔ φ a b :=
  erThan_singleton.trans CresswellDegree.mk_lt_mk

/-! ### Comparison across worlds ((70)–(73)) -/

section Counterfactual

variable {W D : Type*} [Preorder D] (s : Conditional.SelectionFunction W) (height : W → D)
  (smokes : Set W) (w : W)

-- (71)
theorem erThan_sel :
    ErThan {toDual (height (s.sel w smokes))} {toDual (height w)} ↔
      height (s.sel w smokes) < height w :=
  erThan_singleton_toDual

theorem not_erThan_sel_of_mem (hw : w ∈ smokes) :
    ¬ ErThan {toDual (height (s.sel w smokes))} {toDual (height w)} := by
  rw [erThan_sel, s.centering w smokes hw]
  exact lt_irrefl _

end Counterfactual

end Cresswell1976
