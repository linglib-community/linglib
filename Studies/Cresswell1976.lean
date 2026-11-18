module

public import Mathlib.Order.Sigma
public import Linglib.Semantics.Degree.CresswellDegree
public import Linglib.Semantics.Negation.Polarity
public import Linglib.Semantics.Conditionals.SelectionFunction
public import Linglib.Data.Examples.Cresswell1976
public import Linglib.Fragments.English.Adjectives
public import Linglib.Fragments.English.MeasurePhrases
public import Linglib.Fragments.English.Nouns

/-!
# The semantics of degree

Cresswell's degree of comparison is a point paired with the ordering of its scale, and
*er than* holds of two degree properties when both are instantiated and every degree of the
first exceeds every degree of the second on their common scale, so a comparative across
scales is anomalous and a disjoined standard is compared universally. Mass nouns and plurals
carry degrees of volume and of number through the totality operator, degrees need no units
since a comparison relation yields its own degrees by quotienting, and the counterfactual
*shorter than he is* compares heights across worlds.

We take degrees on a family of scales to be mathlib's disjoint sum of the scales' orders and
prove the same-scale restriction, on which [the judgments follow from the scales of the
fragment's words](##scale_eq_iff_acceptable), the universal reading of disjoined standards, the
reduction of the totality comparatives to volumes and cardinalities, the synonymy of *all* and
*every* given that there are men, the [comparative](##erThan_singleton_mk) and the
[*exactly*](##exactly_singleton_mk) on constructed degrees, and the counterfactual through a
Stalnaker selection function.

## Implementation notes

* The plural is read as in (49), a nonempty set of things satisfying the noun with its
  cardinality; as printed, (3.6) fixes the set to all of them, on which (54) would require
  the set of all men to walk.
* A degree of (2.1) is a point of a scale in a family. That the point lie in the field of the
  scale's relation is not imposed on the family; for constructed degrees the field of the induced
  comparison is [the set of classes of the field of the comparison](##field_lt), and everything
  outside that field [falls into one class](##mk_eq_mk_of_notMem_field).
* The scale of an example is read from `English.Adjectives`, `English.Nouns` and
  `English.MeasurePhrases` (`ScalarDimension.comparisonScale`), and *six feet* is the
  paper's degree on the relation ordering lengths: if it is the name of $⟨u, >⟩$ it cannot also be
  the name of $⟨u, <⟩$ (p. 274). The fragment's *long* is the spatial clause of (4.3); the temporal
  clause is the paper's and stays here.
* (66) lies outside the prediction. Cresswell takes it to use the words as if they produced a
  common scale, and says that he does not know how this should be represented.

## TODO

* The relation $>_d$ between pairs of points on a scale with a natural metric (§4), on which *twice
  as tall* would rest.

## References

* [M. J. Cresswell, *The semantics of degree* (1976)][cresswell-1976]
* [R. C. Stalnaker, *A theory of conditionals* (1968)][stalnaker-1968]
-/

@[expose] public section

namespace Cresswell1976

open OrderDual

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

-- (2.7)
theorem asAs_singleton_iff_le {D : Type*} [PartialOrder D] {a b : D} : AsAs {a} {b} ↔ b ≤ a :=
  asAs_singleton.trans le_iff_lt_or_eq.symm

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

/-- Spatial distance read upward, the scale of *tall* (2.2). -/
def spatial : DirectedScale := (.inl (.of .length), .positive)

/-- Temporal distance read upward, the scale of *long* of an event (4.3). -/
def temporal : DirectedScale := (.inl (.of .time), .positive)

/-- A mass noun carries degrees of volume (40) and a count noun, through the plural, a number
(3.6). -/
def nounScale (n : English.Nouns.Noun) : DirectedScale :=
  (.inl (if n.IsCount then 1 else .volume), .positive)

section Scales

variable {P : DirectedScale → Type*} [∀ s, LT (P s)] {ω ω' : Set (Σ s, P s)}

/-- *Er than* "works only when its terms have the same scale": across two scales it fails in every
model (p. 271). -/
theorem not_erThan_of_scale_ne {l r : Option DirectedScale} (h : l ≠ r)
    (hω : ∀ a ∈ ω, some a.1 = l) (hω' : ∀ b ∈ ω', some b.1 = r) : ¬ ErThan ω ω' :=
  not_erThan_of_fst_ne fun a ha b hb hab ↦ h <| by rw [← hω a ha, ← hω' b hb, hab]

end Scales

section Long

variable {E : Type*} {P : DirectedScale → Type*} (ω object event : Set E) (extent : E → P spatial)
  (duration : E → P temporal) {a b : E}

/-- *Long* gives a physical object the distance between its extremities and an event the temporal
distance between its beginning and end (4.3). -/
def long (a : E) : Set (Σ s, P s) :=
  {d | a ∈ ω ∧ (a ∈ object ∧ d = ⟨spatial, extent a⟩ ∨ a ∈ event ∧ d = ⟨temporal, duration a⟩)}

-- The fragment's *long* is the spatial clause.
example : English.Adjectives.long.directedScale? = some spatial := rfl

variable {ω object event extent duration}

theorem long_of_object (ha : a ∈ ω) (ho : a ∈ object) (he : a ∉ event) :
    long ω object event extent duration a = {⟨spatial, extent a⟩} := by
  ext d; simp [long, ha, ho, he]

theorem long_of_event (ha : a ∈ ω) (ho : a ∉ object) (he : a ∈ event) :
    long ω object event extent duration a = {⟨temporal, duration a⟩} := by
  ext d; simp [long, ha, ho, he]

variable [∀ s, LT (P s)]

-- (68)
theorem erThan_long_of_object (ha : a ∈ ω) (hao : a ∈ object) (hae : a ∉ event) (hb : b ∈ ω)
    (hbo : b ∈ object) (hbe : b ∉ event) :
    ErThan (long ω object event extent duration a) (long ω object event extent duration b) ↔
      extent b < extent a := by
  rw [long_of_object ha hao hae, long_of_object hb hbo hbe, erThan_singleton, Sigma.mk_lt_mk_iff]

-- (67)
theorem erThan_long_of_event (ha : a ∈ ω) (hao : a ∉ object) (hae : a ∈ event) (hb : b ∈ ω)
    (hbo : b ∉ object) (hbe : b ∈ event) :
    ErThan (long ω object event extent duration a) (long ω object event extent duration b) ↔
      duration b < duration a := by
  rw [long_of_event ha hao hae, long_of_event hb hbo hbe, erThan_singleton, Sigma.mk_lt_mk_iff]

/-- *Long* puts an event and a physical object on different scales, which "explains the semantic
anomaly of (69)". -/
theorem not_erThan_long_event_object (ha : a ∈ ω) (hao : a ∉ object) (hae : a ∈ event)
    (hb : b ∈ ω) (hbo : b ∈ object) (hbe : b ∉ event) :
    ¬ ErThan (long ω object event extent duration a) (long ω object event extent duration b) := by
  rw [long_of_event ha hao hae, long_of_object hb hbo hbe]
  exact not_erThan_of_fst_ne fun _ h₁ _ h₂ ↦ by
    rw [Set.mem_singleton_iff.1 h₁, Set.mem_singleton_iff.1 h₂]
    exact show temporal ≠ spatial by decide

end Long

/-- An example comparing two terms: their scales and its row. -/
structure Compared where
  /-- The scale of the first term. -/
  left : Option DirectedScale
  /-- The scale of the second term. -/
  right : Option DirectedScale
  /-- The example. -/
  row : Datum

section Rows

open English.Adjectives English.MeasurePhrases English.Nouns Examples

/-- The examples whose judgments follow from their scales. (56) and (57) compare nothing, and
(50) and (66) are `crossScale`. -/
def comparisons : List Compared :=
  [⟨tall.directedScale?, tall.directedScale?, ex_13⟩,
   ⟨tall.directedScale?, English.Adjectives.long.directedScale?, ex_15⟩,
   ⟨tall.directedScale?, clever.directedScale?, ex_23⟩,
   ⟨tall.directedScale?, some foot.directedScale, ex_35⟩,
   ⟨tall.directedScale?, some foot.directedScale, ex_37⟩,
   ⟨short.directedScale?, some foot.directedScale, ex_39⟩,
   ⟨some (nounScale water), some (nounScale mud), ex_41⟩,
   ⟨some (nounScale man), some (nounScale bird), ex_52⟩,
   ⟨beautiful.directedScale?, beautiful.directedScale?, ex_62⟩,
   ⟨tall.directedScale?, beautiful.directedScale?, ex_65⟩,
   ⟨some temporal, English.Adjectives.long.directedScale?, ex_69⟩,
   ⟨short.directedScale?, short.directedScale?, ex_70⟩,
   ⟨tall.directedScale?, tall.directedScale?, fn10_iii⟩]

/-- An example is acceptable exactly when its terms lie on the same scale, *short* and *six feet*
being opposed in direction. -/
theorem scale_eq_iff_acceptable :
    ∀ c ∈ comparisons, c.left = c.right ↔ c.row.judgment = .acceptable := by
  decide

/-- The examples printed without an asterisk although their terms lie on different scales. -/
def crossScale : List Compared :=
  [⟨beautiful.directedScale?, clever.directedScale?, ex_50⟩,
   ⟨old.directedScale?, wise.directedScale?, ex_66⟩]

theorem scale_ne_of_mem_crossScale :
    ∀ c ∈ crossScale, c.left ≠ c.right ∧ c.row.judgment = .acceptable := by
  decide

/-- (50) has no asterisk and (65) has one, yet the two compare across scales alike, so the account
gives them no different verdict. -/
theorem unstarred_crosses_scales :
    beautiful.directedScale? ≠ clever.directedScale? ∧
      tall.directedScale? ≠ beautiful.directedScale? ∧ ex_50.judgment ≠ ex_65.judgment := by
  decide

end Rows

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

section Constructed

variable {E : Type*} (φ : E → E → Prop) {a b : E}

-- (62), (4.2)
theorem erThan_singleton_mk (a b : E) :
    ErThan ({⟦a⟧} : Set (CresswellDegree φ)) {⟦b⟧} ↔ φ a b :=
  erThan_singleton.trans CresswellDegree.mk_lt_mk

-- p. 274, (4.1)
theorem exactly_singleton_mk (a b : E) :
    Exactly ({⟦a⟧} : Set (CresswellDegree φ)) {⟦b⟧} ↔ cresswellSetoid φ a b :=
  exactly_singleton.trans Quotient.eq

/-- The field of a relation is the set of things it relates to something in one direction or the
other (2.1). -/
def field : Set E := {a | ∃ c, φ a c ∨ φ c a}

-- p. 281
theorem field_lt :
    field ((· < ·) : CresswellDegree φ → CresswellDegree φ → Prop) =
      Quotient.mk (cresswellSetoid φ) '' field φ := by
  ext x
  induction x using Quotient.inductionOn with | _ a
  constructor
  · rintro ⟨c, hc⟩
    induction c using Quotient.inductionOn with | _ c
    exact ⟨a, ⟨c, hc.symm⟩, rfl⟩
  · rintro ⟨b, ⟨c, hc⟩, hb⟩
    exact ⟨⟦c⟧, by rw [← hb]; exact hc.symm⟩

variable {φ} in
theorem mk_eq_mk_of_notMem_field (ha : a ∉ field φ) (hb : b ∉ field φ) :
    (⟦a⟧ : CresswellDegree φ) = ⟦b⟧ := by
  simp only [field, Set.mem_ofPred_eq, not_exists, not_or] at ha hb
  exact Quotient.sound ⟨fun c ↦ iff_of_false (ha c).1 (hb c).1,
    fun c ↦ iff_of_false (ha c).2 (hb c).2⟩

/-- A partial order and its strict part need not give the same degrees: of two dimensions, the
points high on one and low on the other have the same strictly greater and lesser points, but
neither is at most the other (p. 266). -/
theorem cresswellSetoid_lt_ne_le :
    cresswellSetoid ((· < ·) : Bool × Bool → Bool × Bool → Prop) ≠ cresswellSetoid (· ≤ ·) := by
  intro h
  have hlt : cresswellSetoid ((· < ·) : Bool × Bool → Bool × Bool → Prop) (true, false)
      (false, true) := by
    refine ⟨fun c ↦ ?_, fun c ↦ ?_⟩ <;> obtain ⟨_ | _, _ | _⟩ := c <;> simp [Prod.lt_iff]
  rw [h] at hlt
  exact absurd ((hlt.1 (true, false)).1 le_rfl) (by decide)

end Constructed

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
