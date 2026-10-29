/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Quantification.Numerals.Basic
public import Linglib.Semantics.Exhaustification.DomainAlternatives
public import Linglib.Semantics.Exhaustification.Excluder
public import Linglib.Semantics.Exhaustification.Pointwise
public import Mathlib.Data.Set.Card

/-!
# Mihoc (2019): Decomposing logic: Modified numerals, polarity, and exhaustification

Mihoc builds *more than n* and *less than n* from a comparative operator and *at least n* and
*at most n* from a superlative one, each applied to the extent indicator *much* or *little*; the
comparative places the maximum of the counted degrees outside the extent and the superlative
inside it. The truth conditions mention a domain, the set the maximum falls in, so the modified
numerals have subdomain alternatives besides their scalar ones. Exhaustifying against the
pre-exhaustified subdomain alternatives across the speaker's epistemic modal yields ignorance as
epistemic free choice, total for the superlative numerals, which keep every alternative, and
possibly partial for the comparative ones, which may prune. Under negation that exhaustification
is vacuous, so the superlative numerals, which require their exhaustification to strengthen the
prejacent, are deviant there.

## Implementation notes

* The maximum of the counted degrees is abstracted to its value, so a truth condition is a
  predicate on ℕ and an epistemic state is seen through the values it leaves possible.
* Scalar alternatives range over a contextual scale of numerals, which is all her granularity
  is; the full scale of naturals is her scale of granularity one.
* Ignorance is stated for a finite truth set, which her running examples *less than three* and
  *at most two* have; the infinite truth sets of *more than n* and *at least n* need a
  contextual bound for the same argument.
* Each subdomain alternative is pre-exhaustified against the others of its size, her choice for
  the parse that keeps alternatives of several sizes.

## References

* [mihoc-2019]
* [hackl-2000]
* [kennedy-2015]
* [horn-1972]
* [geurts-nouwen-2007]
* [nouwen-2010]
* [fox-hackl-2006]
* [spector-2014]
* [chierchia-2013]
-/

@[expose] public section

namespace Mihoc2019

open Degree ModalLogic Exhaustification Numerals

/-! ### Extent indicators and the two operators -/

/-- The positive extent ⟦much⟧(n) = {d | d ≤ n} (her (28a)). -/
def much (n : ℕ) : Set ℕ := Comparison.le.interval n

/-- The negative extent ⟦little⟧(n) = {d | d ≥ n} (her (28b)). -/
def little (n : ℕ) : Set ℕ := Comparison.ge.interval n

@[simp] theorem mem_much {d n : ℕ} : d ∈ much n ↔ d ≤ n := .rfl

@[simp] theorem mem_little {d n : ℕ} : d ∈ little n ↔ n ≤ d := .rfl

/-- The comparative operator puts the maximum of the degree predicate in the complement of the
extent `f n` (her (30)). -/
def compTC (f : ℕ → Set ℕ) (n maxD : ℕ) : Prop := maxD ∈ (f n)ᶜ

/-- The superlative operator puts the maximum of the degree predicate in the extent `f n` (her
(31)). -/
def atSupTC (f : ℕ → Set ℕ) (n maxD : ℕ) : Prop := maxD ∈ f n

/-! ### Assertion forms -/

/-- The two extent indicators. -/
inductive Extent where
  /-- The positive extent indicator *much*. -/
  | much
  /-- The negative extent indicator *little*. -/
  | little
  deriving DecidableEq, Repr

/-- The extent an extent indicator denotes. -/
def Extent.set : Extent → ℕ → Set ℕ
  | .much => Mihoc2019.much
  | .little => Mihoc2019.little

/-- The two modifier operators. -/
inductive Op where
  /-- The comparative operator of *more than* and *less than*. -/
  | comp
  /-- The superlative operator of *at least* and *at most*. -/
  | atSup
  deriving DecidableEq, Repr

/-- Bare and modified numerals. -/
inductive Form where
  /-- A bare numeral, with the lower-bounded meaning of [horn-1972]. -/
  | bare (n : ℕ)
  /-- An extent indicator and a numeral under one of the two operators. -/
  | modified (op : Op) (f : Extent) (n : ℕ)
  deriving DecidableEq, Repr

/-- *more than n* is the comparative operator with *much*. -/
abbrev Form.moreThan (n : ℕ) : Form := .modified .comp .much n

/-- *less than n* is the comparative operator with *little*. -/
abbrev Form.lessThan (n : ℕ) : Form := .modified .comp .little n

/-- *at least n* is the superlative operator with *little*. -/
abbrev Form.atLeast (n : ℕ) : Form := .modified .atSup .little n

/-- *at most n* is the superlative operator with *much*. -/
abbrev Form.atMost (n : ℕ) : Form := .modified .atSup .much n

/-- The truth conditions of a form, as a predicate on the maximum of the degree predicate. -/
def Form.tc : Form → ℕ → Prop
  | .bare n, maxD => maxD ∈ Comparison.ge.interval n
  | .modified .comp f n, maxD => compTC f.set n maxD
  | .modified .atSup f n, maxD => atSupTC f.set n maxD

/-- The comparison a form's truth conditions instantiate. -/
def Form.toComparison : Form → Comparison
  | .bare _ => .ge
  | .modified .comp .much _ => .gt
  | .modified .comp .little _ => .lt
  | .modified .atSup .little _ => .ge
  | .modified .atSup .much _ => .le

/-- The numeral of a form. -/
def Form.arg : Form → ℕ
  | .bare n => n
  | .modified _ _ n => n

/-- Every form's truth conditions compare the maximum with its numeral, which recovers the
truth conditions of [hackl-2000] and [kennedy-2015] (her (32)–(33)). -/
theorem Form.tc_iff_rel (φ : Form) (maxD : ℕ) :
    φ.tc maxD ↔ φ.toComparison.Rel maxD φ.arg := by
  obtain ⟨n⟩ | ⟨_ | _, _ | _, n⟩ := φ <;>
    simp [Form.tc, Form.toComparison, Form.arg, compTC, atSupTC, Extent.set]

instance (φ : Form) (maxD : ℕ) : Decidable (φ.tc maxD) :=
  decidable_of_iff _ (φ.tc_iff_rel maxD).symm

@[simp] theorem tc_bare (n maxD : ℕ) : (Form.bare n).tc maxD ↔ n ≤ maxD := .rfl

@[simp] theorem tc_moreThan (n maxD : ℕ) : (Form.moreThan n).tc maxD ↔ n < maxD := by
  simp [Form.tc, compTC, Extent.set]

@[simp] theorem tc_lessThan (n maxD : ℕ) : (Form.lessThan n).tc maxD ↔ maxD < n := by
  simp [Form.tc, compTC, Extent.set]

@[simp] theorem tc_atLeast (n maxD : ℕ) : (Form.atLeast n).tc maxD ↔ n ≤ maxD := .rfl

@[simp] theorem tc_atMost (n maxD : ℕ) : (Form.atMost n).tc maxD ↔ maxD ≤ n := .rfl

/-! ### Strictness

The comparative forms exclude the numeral and the superlative ones include it, the split of
[geurts-nouwen-2007] and [nouwen-2010] into Class A and Class B modifiers, here derived from the
operator through `Comparison.boundary_mem`. -/

theorem comp_excludes_boundary (f : Extent) (n : ℕ) : ¬ (Form.modified .comp f n).tc n := by
  rw [Form.tc_iff_rel, Form.arg, ← Comparison.mem_interval, Comparison.boundary_mem]
  cases f <;> simp [Form.toComparison, Comparison.IsStrict]

theorem atSup_includes_boundary (f : Extent) (n : ℕ) : (Form.modified .atSup f n).tc n := by
  rw [Form.tc_iff_rel, Form.arg, ← Comparison.mem_interval, Comparison.boundary_mem]
  cases f <;> simp [Form.toComparison, Comparison.IsStrict]

/-! ### Subdomain alternatives

A modified form's subdomain alternatives replace the set its maximum is asserted to fall in,
the complement of the extent or the extent itself, by its proper subsets (her (38c), (39c)). A
bare numeral mentions no such set and has none (her (37c)). -/

/-- The subdomain alternatives of a form. -/
def Form.domainAlts : Form → Set (Set ℕ)
  | .bare _ => ∅
  | φ@(.modified _ _ _) => {D' | D' ⊂ {d | φ.tc d}}

theorem Form.tc_of_mem_domainAlts {φ : Form} {D' : Set ℕ} (h : D' ∈ φ.domainAlts) {maxD : ℕ}
    (hm : maxD ∈ D') : φ.tc maxD := by
  obtain ⟨n⟩ | ⟨op, f, n⟩ := φ
  · exact absurd h (Set.notMem_empty _)
  · simp only [Form.domainAlts, Set.mem_ofPred_eq] at h
    exact h.subset hm

theorem coe_mem_domainAlts {op : Op} {f : Extent} {n k : ℕ} {T S : Finset ℕ}
    (hT : ∀ d, (Form.modified op f n).tc d ↔ d ∈ T) (hS : S ∈ T.powersetCard k)
    (hk : k < T.card) : (S : Set ℕ) ∈ (Form.modified op f n).domainAlts := by
  rw [Finset.mem_powersetCard] at hS
  have : {d | (Form.modified op f n).tc d} = T := Set.ext hT
  simp only [Form.domainAlts, this, Set.mem_ofPred_eq, Finset.coe_ssubset]
  exact Finset.ssubset_iff_subset_ne.2 ⟨hS.1, by rintro rfl; omega⟩

/-! ### Scalar implicatures

A form's scalar alternatives replace its numeral by the other points of a contextual scale `S`
(her (37b)–(39b)), and exhaustifying denies those the form does not entail, the stronger ones.
On the full scale of naturals every form comes out exact, the bare numeral and the superlatives
at their numeral and the comparatives at the adjacent number
(`Numerals.mem_exh_range_interval_gt_iff`), the bare numeral's reading after [horn-1972] and an
unattested one for the modified forms. A scale with gaps instead leaves an interval up to the next
point (`mem_exh_moreThan_iff`), and on a dense scale the comparatives' exhaustification is
contradictory, the prediction of [fox-hackl-2006]; the scale is contextual rather than universally
dense (her fn. 8). -/

/-- The form with its numeral replaced by `m`. -/
def Form.withArg : Form → ℕ → Form
  | .bare _, m => .bare m
  | .modified op f _, m => .modified op f m

/-- The scalar alternatives of a form on the scale `S`. -/
def Form.scalarAlts (S : Set ℕ) (φ : Form) : Set (Set ℕ) :=
  (fun m ↦ {d | (φ.withArg m).tc d}) '' S

theorem Form.setOf_tc (φ : Form) : {d | φ.tc d} = φ.toComparison.interval φ.arg :=
  Set.ext fun d ↦ (φ.tc_iff_rel d).trans (Comparison.mem_interval _ _ _).symm

/-- On the full scale a form's scalar alternatives are the intervals of its comparison at every
number. -/
theorem Form.scalarAlts_univ (φ : Form) :
    φ.scalarAlts .univ = Set.range φ.toComparison.interval := by
  rw [Form.scalarAlts, Set.image_univ]
  congr 1
  funext m
  rw [Form.setOf_tc]
  obtain ⟨n⟩ | ⟨_ | _, _ | _, n⟩ := φ <;> rfl

theorem mem_exh_moreThan_iff {S : Set ℕ} {n s : ℕ} (hs : s ∈ S) (hns : n < s)
    (hnext : ∀ m ∈ S, n < m → s ≤ m) (maxD : ℕ) :
    maxD ∈ exh ((Form.moreThan n).scalarAlts S) {d | (Form.moreThan n).tc d} ↔
      n < maxD ∧ maxD ≤ s := by
  simp only [mem_exh, Form.scalarAlts, Set.forall_mem_image, Form.withArg, Set.mem_ofPred_eq,
    Set.ofPred_subset_ofPred, tc_moreThan]
  refine ⟨fun ⟨h, hS⟩ ↦ ⟨h, ?_⟩, fun ⟨h, hd⟩ ↦ ⟨h, fun m hm hmd x hx ↦ ?_⟩⟩
  · by_contra! hsd
    have := hS hs hsd (n + 1) (by omega)
    omega
  · have := hnext m hm
    omega

-- Ch. 3, (24)
theorem mem_exh_moreThan_univ (n maxD : ℕ) :
    maxD ∈ exh ((Form.moreThan n).scalarAlts .univ) {d | (Form.moreThan n).tc d} ↔
      maxD = n + 1 := by
  rw [Form.scalarAlts_univ, Form.setOf_tc]
  exact mem_exh_range_interval_gt_iff.trans (Nat.covBy_iff_add_one_eq.trans eq_comm)

-- Ch. 3, (33) [spector-2014]
theorem mem_exh_moreThan_five {S : Set ℕ} (h9 : 9 ∈ S) (hgap : ∀ m ∈ S, 5 < m → 9 ≤ m)
    (maxD : ℕ) :
    maxD ∈ exh ((Form.moreThan 5).scalarAlts S) {d | (Form.moreThan 5).tc d} ↔
      5 < maxD ∧ maxD ≤ 9 :=
  mem_exh_moreThan_iff h9 (by omega) hgap maxD

-- Ch. 3, (2)
theorem mem_exh_bare_univ (n maxD : ℕ) :
    maxD ∈ exh ((Form.bare n).scalarAlts .univ) {d | (Form.bare n).tc d} ↔
      maxD ∈ Comparison.eq.interval n := by
  rw [Form.scalarAlts_univ, Form.setOf_tc]
  exact mem_exh_range_interval_iff_of_not_isStrict (c := .ge) nofun

-- Ch. 3, (25)
theorem mem_exh_lessThan_univ {n : ℕ} (hn : 1 ≤ n) (maxD : ℕ) :
    maxD ∈ exh ((Form.lessThan n).scalarAlts .univ) {d | (Form.lessThan n).tc d} ↔
      maxD = n - 1 := by
  rw [Form.scalarAlts_univ, Form.setOf_tc]
  exact mem_exh_range_interval_lt_iff.trans <| Nat.covBy_iff_add_one_eq.trans <| by
    simp only [Form.arg]; omega

-- Ch. 3, (26)
theorem mem_exh_atLeast_univ (n maxD : ℕ) :
    maxD ∈ exh ((Form.atLeast n).scalarAlts .univ) {d | (Form.atLeast n).tc d} ↔ maxD = n := by
  rw [Form.scalarAlts_univ, Form.setOf_tc]
  exact mem_exh_range_interval_iff_of_not_isStrict (c := .ge) nofun

-- Ch. 3, (27)
theorem mem_exh_atMost_univ (n maxD : ℕ) :
    maxD ∈ exh ((Form.atMost n).scalarAlts .univ) {d | (Form.atMost n).tc d} ↔ maxD = n := by
  rw [Form.scalarAlts_univ, Form.setOf_tc]
  exact mem_exh_range_interval_iff_of_not_isStrict (c := .le) nofun

-- [fox-hackl-2006]: on a dense scale exhaustified *more than n* is contradictory.
theorem exh_moreThan_eq_empty_of_dense {D : Type*} [LinearOrder D] [DenselyOrdered D] (n : D) :
    exh (Set.range Comparison.gt.interval) (Comparison.gt.interval n) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h ↦
    not_covBy_of_denselyOrdered (mem_exh_range_interval_gt_iff.1 h)

/-! ### Ignorance

An assertion carries a null epistemic necessity modal `□_S`, and exhaustification applies above
it, negating each pre-exhaustified subdomain alternative `□_S (max ∈ S)` and the stronger scalar
alternatives. A state settles `□_S (max ∈ S)` just when every value it leaves possible lies in `S`
(`box_mem_iff`), so of the subdomains of one size exactly one is settled iff the possible values
number exactly that size, and the implicatures from the subdomain alternatives of a size hold iff
they do not (`domainImplicatures_iff`). Her three parses of *less than three* follow: keeping the
singletons rules out settling a value, a 'winner' state (her Table 4.1); keeping the larger
alternatives rules out excluding a value without settling one, a 'loser' state (her Table 4.2);
keeping all leaves only total ignorance (her Table 4.3), the only parse open to the superlative
forms, which cannot prune their subdomain alternatives. -/

namespace Ignorance

variable {W : Type*} (R : SetRel W W) (μ : W → ℕ) (w : W)

/-- The values of the maximum that the speaker considers possible at `w`. -/
def possibleValues : Set ℕ := {x | ◇[R] (μ · = x) w}

/-- The speaker knows the value of the maximum, a 'winner' state. -/
def Winner : Prop := ∃ x, □[R] (μ · = x) w

/-- The implicatures from the size-`k` subdomain alternatives of `T` deny each `□_S (max ∈ S)`
pre-exhaustified against the others of its size. -/
def DomainImplicatures (T : Finset ℕ) (k : ℕ) : Prop :=
  ∀ S : T.powersetCard k,
    ¬ exhAgainst (· ≠ ·) (fun S : T.powersetCard k ↦ □[R] (μ · ∈ (S : Finset ℕ)) w) S

variable {R μ w} {T : Finset ℕ} {k : ℕ}

theorem box_mem_iff {s : Set ℕ} : □[R] (μ · ∈ s) w ↔ possibleValues R μ w ⊆ s :=
  ⟨fun h _ ⟨v, hv, hx⟩ ↦ hx ▸ h v hv, fun h v hv ↦ h ⟨v, hv, rfl⟩⟩

theorem nonempty_possibleValues [IsSerial R] : (possibleValues R μ w).Nonempty :=
  let ⟨v, hv⟩ := IsSerial.serial (R := R) w
  ⟨μ v, v, hv, rfl⟩

theorem existsUnique_subset_iff (hT : possibleValues R μ w ⊆ T) (hk : k < T.card) :
    (∃! S : T.powersetCard k, possibleValues R μ w ⊆ (S : Finset ℕ)) ↔
      (possibleValues R μ w).ncard = k := by
  set V := possibleValues R μ w
  have hV : V.Finite := T.finite_toSet.subset hT
  constructor
  · rintro ⟨⟨S, hS⟩, hVS, huniq⟩
    rw [Finset.mem_powersetCard] at hS
    by_contra hne
    have hle : V.ncard ≤ k := by simpa [hS.2] using Set.ncard_le_ncard hVS
    obtain ⟨a, haS, haV⟩ : ∃ a ∈ S, a ∉ V := by
      by_contra! h
      have := Set.ncard_le_ncard (s := (S : Set ℕ)) h hV
      simp only [Set.ncard_coe_finset] at this
      omega
    obtain ⟨b, hbT, hbS⟩ : ∃ b ∈ T, b ∉ S :=
      Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.2 ⟨hS.1, by rintro rfl; omega⟩)
    have hS' : insert b (S.erase a) ∈ T.powersetCard k := by
      rw [Finset.mem_powersetCard, Finset.card_insert_of_notMem (fun h ↦ hbS
        (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem haS]
      exact ⟨Finset.insert_subset hbT ((Finset.erase_subset a S).trans hS.1), by omega⟩
    have := Subtype.mk.inj (huniq ⟨_, hS'⟩ fun x hx ↦ Finset.mem_insert_of_mem
      (Finset.mem_erase.2 ⟨fun h ↦ haV (h ▸ hx), hVS hx⟩))
    exact hbS (this ▸ Finset.mem_insert_self b _)
  · intro hcard
    refine ⟨⟨hV.toFinset, Finset.mem_powersetCard.2 ⟨fun x hx ↦ hT (hV.mem_toFinset.1 hx),
      by rw [← Set.ncard_eq_toFinset_card V hV, hcard]⟩⟩, by simp, ?_⟩
    rintro ⟨S', hS'⟩ hVS'
    rw [Finset.mem_powersetCard] at hS'
    refine Subtype.ext (Finset.eq_of_subset_of_card_le (fun x hx ↦ ?_) ?_).symm
    · exact hVS' (hV.mem_toFinset.1 hx)
    · rw [hS'.2, ← Set.ncard_eq_toFinset_card V hV, hcard]

/-- The implicatures from the subdomain alternatives of size `k` hold iff the speaker does not
consider exactly `k` values possible. -/
theorem domainImplicatures_iff (hT : □[R] (μ · ∈ (T : Set ℕ)) w) (hk : k < T.card) :
    DomainImplicatures R μ w T k ↔ (possibleValues R μ w).ncard ≠ k := by
  simp only [DomainImplicatures, forall_not_exhAgainst_ne_iff, Finset.mem_coe.symm, box_mem_iff]
  rw [existsUnique_subset_iff (box_mem_iff.1 hT) hk]

theorem winner_iff [IsSerial R] : Winner R μ w ↔ (possibleValues R μ w).ncard = 1 := by
  simp only [Winner, Set.ncard_eq_one]
  refine exists_congr fun x ↦ ?_
  rw [← Set.subset_singleton_iff_eq.trans (or_iff_right nonempty_possibleValues.ne_empty)]
  exact box_mem_iff (s := {x})

theorem freeChoice_iff (hT : □[R] (μ · ∈ (T : Set ℕ)) w) :
    FreeChoice R w T (μ · = ·) ↔ (possibleValues R μ w).ncard = T.card := by
  have hVT := box_mem_iff.1 hT
  refine ⟨fun h ↦ ?_, fun h x hx ↦ ?_⟩
  · rw [Set.Subset.antisymm hVT fun x hx ↦ h x hx, Set.ncard_coe_finset]
  · rw [← Set.ncard_coe_finset] at h
    change x ∈ possibleValues R μ w
    rw [Set.eq_of_subset_of_ncard_le hVT h.ge]
    exact hx

private theorem ncard_possibleValues_bounds [IsSerial R] (hT : □[R] (μ · ∈ (T : Set ℕ)) w) :
    0 < (possibleValues R μ w).ncard ∧ (possibleValues R μ w).ncard ≤ T.card :=
  ⟨(Set.ncard_pos (T.finite_toSet.subset (box_mem_iff.1 hT))).2 nonempty_possibleValues,
    by simpa using Set.ncard_le_ncard (box_mem_iff.1 hT)⟩

-- Table 4.1
theorem domainImplicatures_one_iff [IsSerial R] (hT : □[R] (μ · ∈ (T : Set ℕ)) w)
    (h : 1 < T.card) : DomainImplicatures R μ w T 1 ↔ ¬ Winner R μ w := by
  rw [domainImplicatures_iff hT h, winner_iff]

-- Table 4.2
theorem forall_two_le_domainImplicatures_iff [IsSerial R] (hT : □[R] (μ · ∈ (T : Set ℕ)) w) :
    (∀ k, 2 ≤ k → k < T.card → DomainImplicatures R μ w T k) ↔
      Winner R μ w ∨ FreeChoice R w T (μ · = ·) := by
  obtain ⟨hpos, hle⟩ := ncard_possibleValues_bounds hT
  rw [winner_iff, freeChoice_iff hT]
  refine ⟨fun h ↦ ?_, fun h k hk hkT ↦ (domainImplicatures_iff hT hkT).2 (by omega)⟩
  by_contra! hne
  exact (domainImplicatures_iff hT (by omega)).1 (h _ (by omega) (by omega)) rfl

/-- Keeping every subdomain alternative, as the superlative forms must, leaves only total
ignorance (her Table 4.3). -/
theorem forall_domainImplicatures_iff [IsSerial R] (hT : □[R] (μ · ∈ (T : Set ℕ)) w) :
    (∀ k, 0 < k → k < T.card → DomainImplicatures R μ w T k) ↔
      FreeChoice R w T (μ · = ·) := by
  obtain ⟨hpos, hle⟩ := ncard_possibleValues_bounds hT
  rw [freeChoice_iff hT]
  refine ⟨fun h ↦ ?_, fun h k hk hkT ↦ (domainImplicatures_iff hT hkT).2 (by omega)⟩
  by_contra hne
  exact (domainImplicatures_iff hT (by omega)).1 (h _ hpos (by omega)) rfl

-- Tables 4.1 and 4.2
theorem not_box_lessThan_pred_iff {n : ℕ} (hT : possibleValues R μ w ⊆ Finset.range n) :
    ¬ □[R] (fun v ↦ (Form.lessThan (n - 1)).tc (μ v)) w ↔ n - 1 ∈ possibleValues R μ w := by
  simp only [tc_lessThan]
  change ¬ □[R] (μ · ∈ Set.Iio (n - 1)) w ↔ _
  rw [box_mem_iff, Set.not_subset]
  refine ⟨fun ⟨x, hx, hxn⟩ ↦ ?_, fun h ↦ ⟨_, h, by simp⟩⟩
  have := Finset.mem_range.1 (hT hx)
  grind

/-- Her 'loser' state for *less than three* rules out zero, with each world the value of the
maximum and the speaker's accessible worlds one and two. -/
def zeroRuledOut : SetRel ℕ ℕ := {p | p.2 = 1 ∨ p.2 = 2}

instance : IsSerial zeroRuledOut := ⟨fun _ ↦ ⟨1, .inl rfl⟩⟩

theorem zeroRuledOut_domainImplicatures :
    DomainImplicatures zeroRuledOut id 0 (Finset.range 3) 1 ∧
      ¬ DomainImplicatures zeroRuledOut id 0 (Finset.range 3) 2 := by
  have hV : possibleValues zeroRuledOut id 0 = {1, 2} := by
    ext x
    simp [possibleValues, Diamond, zeroRuledOut]
  have hT : □[zeroRuledOut] (id · ∈ (Finset.range 3 : Set ℕ)) 0 := by
    rintro v (rfl | rfl) <;> simp
  rw [domainImplicatures_iff hT (by simp), domainImplicatures_iff hT (by simp), hV]
  constructor <;> simp

end Ignorance

/-! ### Anti-negativity

Under clausemate negation the subdomain alternatives are negated too, and each pre-exhaustified
negated alternative `¬ (max ∈ D i) ∧ max ∈ D j` contradicts the negated prejacent, so negating
them adds nothing (her Ch. 5 (9)) and exhaustification fails to strengthen the prejacent
(`not_negExh_lt`). The superlative forms require their exhaustification to
strengthen the prejacent, so they are deviant under negation, while the comparative forms, without
the requirement, are not. -/

namespace AntiNegativity

variable {ι : Type*} {φ : Form} {D : ι → Set ℕ}

/-- Exhaustifying a negated form against its negated subdomain alternatives `D`, each
pre-exhaustified against the others (her Ch. 5 (8)–(9)). -/
def negExh (φ : Form) (D : ι → Set ℕ) (maxD : ℕ) : Prop :=
  ¬ φ.tc maxD ∧ ∀ i, ¬ exhAgainst (· ≠ ·) (fun j ↦ maxD ∉ D j) i

theorem negExh_iff [Nontrivial ι] (hD : ∀ i, D i ∈ φ.domainAlts) (maxD : ℕ) :
    negExh φ D maxD ↔ ¬ φ.tc maxD := by
  refine ⟨And.left, fun h ↦ ⟨h, fun i hi ↦ ?_⟩⟩
  obtain ⟨j, hj⟩ := exists_ne i
  exact h (Form.tc_of_mem_domainAlts (hD j) (not_not.1 (hi.2 j hj.symm)))

/-- Exhaustifying the negated form is not strictly stronger than the negated form. -/
theorem not_negExh_lt [Nontrivial ι] (hD : ∀ i, D i ∈ φ.domainAlts) :
    ¬ negExh φ D < fun maxD ↦ ¬ φ.tc maxD := by
  rw [show negExh φ D = _ from funext fun maxD ↦ propext (negExh_iff hD maxD)]
  exact lt_irrefl _

end AntiNegativity

end Mihoc2019
