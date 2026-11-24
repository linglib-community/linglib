module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Tactic.IntervalCases
public import Linglib.Semantics.Plurality.NumberFeatures
public import Linglib.Syntax.Feature.Number.System
public import Linglib.Core.Order.Concept
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Studies.Corbett2000
public import Linglib.Data.Examples.Readers

/-!
# Harbour (2014): Paucity, Abundance, and the Theory of Number

Harbour characterizes the approximative numbers, paucal and greater plural, by a feature
`[±additive]` of additive closure, beside the `[±atomic]` and `[±minimal]` that give the exact
numbers. Each feature acts on a lattice of atoms and their sums, and the same two parameters
govern all three: whether a feature is active on Number⁰ (22) and whether its two values may
cooccur (23). A sociosemantic convention fixes the height of the cut `[±additive]` induces (14).
A parameter setting generates a number system, the feature bundles with nonempty denotation, and
the typology of Table 3 and the implications `Number.universals` are claims about these systems.
Without `[±additive]`, a setting with `[±atomic]` gives a referent of `k` individuals [the value
`Number.ofCard` gives](##Harbour2014.Setting.number_eq_ofCard), so conjoined noun phrases
resolve to the value of the sum of their cardinalities; [an approximative value rules such
resolution out](##Harbour2014.Setting.factorsThrough_number_iff).

## Main definitions

* `Setting`, `Convention`: parameter settings and the placement of the cuts.
* `Setting.number`: the value a setting gives a third-person referent of `k` individuals.
* `Setting.cell`: the region of a person lattice a bundle denotes in a setting.
* `Setting.system`: the number system a setting generates.
* `PlusAdditive`: the `[+additive]` elements of a region cut horizontally.
* `Generates`, `Requires`: the legitimate settings as a formal context, and the order of its
  attribute concepts that (34) reads off them, one number requiring another.

## Implementation notes

* A `Number.Bundle` is a `Finset` of signed features, so the axiom of extension (27) is built in,
  and it is interpreted in the order (28); its cell is its denotation less the more specific
  bundles', as the plural of Figure 7 is `Q+ \ Q′`.
* `card` carries the features from a person lattice to its strata, where `[±atomic]` and
  `[±minimal]` leave one stratum or every stratum from one up (`Strata`) and `[±additive]` cuts
  horizontally. The strata above four only matter through the cuts, so `collapse` reduces every
  placement of the cuts to the cuts at five and six, where `Setting.system` is computed. The
  labels (p. 201) follow Table 3 and its note b.

## TODO

* Banyun's greater and greatest plurals (Table 3, (18)) have no `Number` value, (24) omitting the
  greatest plural.

## References

* [harbour-2014]
* [corbett-2000]
* [gardenfors-2004]
-/

@[expose] public section

namespace Harbour2014

open Mereology
open Number (Bundle Feature additiveIn SatisfiesUniversals)

/-! ### Person lattices and their strata (§2, (12)) -/

section Region

variable {α : Type*}

/-- A region of the person lattice over `B` consists of the sums containing `B` whose number of
atoms lies in `S`, a union of strata (12). -/
def region (B : Finset α) (S : Set ℕ) : Set (Finset α) := {s | B ⊆ s ∧ s.card ∈ S}

variable {B : Finset α} {S : Set ℕ}

@[simp] theorem mem_region {s : Finset α} : s ∈ region B S ↔ B ⊆ s ∧ s.card ∈ S := Iff.rfl

theorem atomize_region (hS : ∀ k ∈ S, B.card ≤ k) :
    atomize (region B S) = region B (atomize S) := by
  ext s
  refine ⟨fun h ↦ ⟨h.1.1, h.1.2, fun j hj hle ↦ ?_⟩, fun h ↦ ⟨⟨h.1, h.2.1⟩, fun t ht hts ↦ ?_⟩⟩
  · obtain ⟨t, hBt, hts, rfl⟩ := Finset.exists_subsuperset_card_eq h.1.1 (hS j hj) hle
    exact Finset.card_le_card (h.2 ⟨hBt, hj⟩ hts)
  · exact (Finset.eq_of_subset_of_card_le hts (h.2.2 ht.2 (Finset.card_le_card hts))).ge

theorem atom_iff_card {s : Finset α} : IsAtom s ↔ IsAtom s.card := by
  rw [isAtom_finset_iff_card_eq_one, Nat.isAtom_iff_eq_one]

variable [DecidableEq α]

omit [DecidableEq α] in
theorem restrict_region (f : Feature) (v : Bool) (hS : ∀ k ∈ S, B.card ≤ k) :
    f.restrict v (region B S) = region B (f.restrict v S) := by
  match f, v with
  | .atomic, true | .atomic, false =>
    ext s
    simp only [Feature.mem_restrict_atomic_true, Feature.mem_restrict_atomic_false, mem_region,
      atom_iff_card, and_assoc]
  | .minimal, true => exact atomize_region hS
  | .minimal, false =>
    ext s
    simp only [Feature.mem_restrict_minimal_false, atomize_region hS, mem_region]
    tauto
  | .additive, _ => rfl

end Region

/-! ### The successor-like function (§4.4) -/

section Successor

variable {α : Type*} [DecidableEq α]

private theorem restrict_minimal_false_iterate (n : ℕ) :
    (Feature.restrict .minimal false)^[n] (Set.Ici 2) = Set.Ici (n + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    ext j
    simp only [Feature.mem_restrict_minimal_false, atomize_Ici, Set.mem_Ici,
      Set.mem_singleton_iff]
    omega

omit [DecidableEq α] in
private theorem restrict_minimal_false_iterate_region (n : ℕ) (S : Set ℕ) :
    (Feature.restrict .minimal false)^[n] (region (∅ : Finset α) S) =
      region ∅ ((Feature.restrict .minimal false)^[n] S) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      restrict_region _ _ fun _ _ ↦ Nat.zero_le _]

omit [DecidableEq α] in
private theorem nonempty_eq_region : {t : Finset α | t.Nonempty} = region ∅ (Set.Ici 1) := by
  ext t; simp [Finset.one_le_card]

omit [DecidableEq α] in
/-- `(+minimal(−minimalⁿ(−atomic(P))))` holds of exactly the sums of `n + 2` atoms (31), the dual of
(30) at `n = 0` and the trial at `n = 1`. -/
theorem atomize_restrict_iterate (n : ℕ) (s : Finset α) :
    s ∈ atomize ((Feature.restrict .minimal false)^[n]
      (Feature.restrict .atomic false {t | t.Nonempty})) ↔ s.card = n + 2 := by
  have hna : Feature.restrict .atomic false (Set.Ici 1) = Set.Ici 2 := by
    ext j; simp only [Feature.mem_restrict_atomic_false, Nat.isAtom_iff_eq_one, Set.mem_Ici]; omega
  rw [nonempty_eq_region, restrict_region _ _ fun _ _ ↦ Nat.zero_le _, hna,
    restrict_minimal_false_iterate_region, restrict_minimal_false_iterate,
    atomize_region fun _ _ ↦ Nat.zero_le _, atomize_Ici]
  simp

-- (30)
omit [DecidableEq α] in
theorem atomize_restrict_atomic_true (s : Finset α) :
    s ∈ atomize (Feature.restrict .atomic true {t | t.Nonempty}) ↔ s.card = 1 := by
  have ha : Feature.restrict .atomic true (Set.Ici 1) = ({1} : Set ℕ) := by
    ext j
    simp only [Feature.mem_restrict_atomic_true, Nat.isAtom_iff_eq_one, Set.mem_Ici,
      Set.mem_singleton_iff]
    omega
  rw [nonempty_eq_region, restrict_region _ _ fun _ _ ↦ Nat.zero_le _, ha,
    atomize_region fun _ _ ↦ Nat.zero_le _]
  simp only [mem_region, Finset.empty_subset, true_and]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ hj _ ↦ Set.mem_singleton_iff.1 hj ▸ h.le⟩⟩

end Successor

/-! ### Orders of composition (§§3.3, 4.1, 4.3) -/

section Orders

variable {D : Type*} [SemilatticeSup D] [OrderBot D]

-- §4.1, n. 15
theorem not_restrict_atomic_true_restrict_atomic_false (P : Set D) (x : D) :
    x ∉ Feature.restrict .atomic true (Feature.restrict .atomic false P) :=
  fun h ↦ h.1.2 h.2

-- §4.3
theorem not_restrict_atomic_true_restrict_minimal_false {P : Set D}
    (hP : ∀ y ∈ P, y ≠ ⊥) (x : D) :
    x ∉ Feature.restrict .atomic true (Feature.restrict .minimal false P) :=
  fun h ↦ h.1.2 (Number.singular_subset_minimal hP ⟨h.1.1, h.2⟩)

end Orders

/-! ### `[±additive]` and horizontal cuts (§3.1) -/

section Additive

variable {α : Type*} [DecidableEq α]

/-- A band consists of the sums of at least `lo` and fewer than `hi` atoms. -/
def Band (lo hi : ℕ) : Set (Finset α) := {s | lo ≤ s.card ∧ s.card < hi}

/-- Given infinitely many atoms, no element of a band above the null individual is additive in it
(10), so `(+additive(−additive(P)))` is unsatisfiable (§3.3). -/
theorem not_additiveIn_band [Infinite α] {lo hi : ℕ} (hlo : 1 ≤ lo) (s : Finset α) :
    s ∉ additiveIn (Band lo hi) := by
  rintro ⟨⟨hl, hh⟩, h⟩
  obtain ⟨u, hsu, hu⟩ :=
    Infinite.exists_superset_card_eq s (s.card + max lo (hi - s.card)) (by omega)
  have hcard : (u \ s).card = max lo (hi - s.card) := by
    rw [Finset.card_sdiff_of_subset hsu, hu]; omega
  have := (h (u \ s) ⟨by omega, by omega⟩).2
  rw [Finset.union_sdiff_of_subset hsu, hu] at this
  omega

-- (10), (11)
theorem additiveIn_le_card {c : ℕ} {s : Finset α} (hs : c ≤ s.card) :
    s ∈ additiveIn {t | c ≤ t.card} :=
  ⟨hs, fun _ _ ↦ hs.trans (Finset.card_le_card Finset.subset_union_left)⟩

theorem additiveIn_le_card' {i : α} {c : ℕ} {s : Finset α} (hi : i ∈ s) (hs : c ≤ s.card) :
    s ∈ additiveIn {t | i ∈ t ∧ c ≤ t.card} :=
  ⟨⟨hi, hs⟩, fun _ _ ↦ ⟨Finset.mem_union_left _ hi,
    hs.trans (Finset.card_le_card Finset.subset_union_left)⟩⟩

-- n. 23
theorem additiveIn_atomize_superset (B : Finset α) : B ∈ additiveIn (atomize {t | B ⊆ t}) := by
  have hB : B ∈ atomize {t | B ⊆ t} := ⟨Finset.Subset.refl B, fun _ hy _ ↦ hy⟩
  refine ⟨hB, fun y hy ↦ ?_⟩
  rw [le_antisymm (hy.2 (Finset.Subset.refl B) hy.1) hy.1, sup_idem]
  exact hB

-- n. 23
theorem not_additiveIn_atomize_nonempty [Nontrivial α] (s : Finset α) :
    s ∉ additiveIn (atomize {t | t.Nonempty}) := by
  have key : ∀ t : Finset α, t ∈ atomize {t | t.Nonempty} ↔ t.card = 1 := fun t ↦ by
    rw [nonempty_eq_region, atomize_region fun _ _ ↦ Nat.zero_le _, atomize_Ici]; simp
  rintro ⟨hs, h⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp ((key s).mp hs)
  obtain ⟨b, hb⟩ := exists_ne a
  have := (key _).mp (h {b} ((key _).mpr (Finset.card_singleton b)))
  rw [Finset.singleton_union, Finset.card_pair hb.symm] at this
  omega

end Additive

/-! ### Convexity (§4.5) -/

section Convexity

variable {α : Type*} [DecidableEq α]

/-- An element of a region `P` cut at `c` is `[+additive]` (10) when it is additive in the bounded
region below the cut or in the unbounded region above it. -/
def PlusAdditive (c : ℕ) (P : Set (Finset α)) : Set (Finset α) :=
  additiveIn {t | t ∈ P ∧ t.card < c} ∪ additiveIn {t | t ∈ P ∧ c ≤ t.card}

theorem plusAdditive_nonempty_iff [Infinite α] {c : ℕ} (hc : 1 ≤ c) (s : Finset α) :
    s ∈ PlusAdditive c {t | t.Nonempty} ↔ c ≤ s.card := by
  have hb : {t : Finset α | t ∈ {t : Finset α | t.Nonempty} ∧ t.card < c} = Band 1 c := by
    ext t; simp [Band, Finset.one_le_card]
  have ha : {t : Finset α | t ∈ {t : Finset α | t.Nonempty} ∧ c ≤ t.card} = {t | c ≤ t.card} := by
    ext t
    exact ⟨fun h ↦ h.2, fun (h : c ≤ t.card) ↦ ⟨Finset.card_pos.mp (by omega), h⟩⟩
  rw [PlusAdditive, hb, ha]
  exact ⟨fun h ↦ Or.elim h (fun h ↦ (not_additiveIn_band le_rfl s h).elim) (·.1),
    fun h ↦ Or.inr (additiveIn_le_card h)⟩

-- (33)
theorem ordConnected_plusAdditive_nonempty [Infinite α] {c : ℕ} (hc : 1 ≤ c) :
    (PlusAdditive c {t : Finset α | t.Nonempty}).OrdConnected := by
  rw [show PlusAdditive c {t : Finset α | t.Nonempty} = {s | c ≤ s.card} from
    Set.ext (plusAdditive_nonempty_iff hc)]
  exact IsUpperSet.ordConnected fun _ _ hst h ↦ h.trans (Finset.card_le_card hst)

/-- On the first-person exclusive lattice, only the speaker atom is additive below a cut (Figure 8).
-/
theorem additiveIn_firstPerson_iff [Infinite α] {i : α} {c : ℕ} (hc : 2 ≤ c) (s : Finset α) :
    s ∈ additiveIn {t | i ∈ t ∧ t.card < c} ↔ s = {i} := by
  refine ⟨fun ⟨⟨hi, hlt⟩, h⟩ ↦ ?_, ?_⟩
  · by_contra hne
    have h2 : 2 ≤ s.card := by
      by_contra h2
      exact hne (Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun x hx ↦
        Finset.card_le_one.mp (by omega) x hx i hi⟩)
    obtain ⟨u, hsu, hu⟩ := Infinite.exists_superset_card_eq s c hlt.le
    have hiu : i ∉ u \ s := fun h ↦ (Finset.mem_sdiff.mp h).2 hi
    have := (h (insert i (u \ s)) ⟨Finset.mem_insert_self i _, by
      rw [Finset.card_insert_of_notMem hiu, Finset.card_sdiff_of_subset hsu]; omega⟩).2
    rw [Finset.union_insert, Finset.union_sdiff_of_subset hsu,
      Finset.insert_eq_of_mem (hsu hi), hu] at this
    omega
  · rintro rfl
    refine ⟨⟨Finset.mem_singleton_self i, by simp; omega⟩, fun t ht ↦ ?_⟩
    rwa [Finset.singleton_union, Finset.insert_eq_of_mem ht.1]

/-- `{±additive}` cuts the first-person lattice nonconvexly (p. 212), so by (32), after
[gardenfors-2004], `[±additive]` is never a language's sole number feature. -/
theorem not_ordConnected_plusAdditive_firstPerson [Infinite α] (i : α) {c : ℕ} (hc : 3 ≤ c) :
    ¬ (PlusAdditive c {t | i ∈ t}).OrdConnected := by
  intro h
  obtain ⟨o, ho⟩ := exists_ne i
  obtain ⟨u, hu, huc⟩ := Infinite.exists_superset_card_eq {i, o} c
    (by rw [Finset.card_pair ho.symm]; omega)
  have hmid := h.out (x := {i}) (y := u)
    (Or.inl ((additiveIn_firstPerson_iff (by omega) _).mpr rfl))
    (Or.inr (additiveIn_le_card' (hu (by simp)) huc.ge))
    ⟨Finset.singleton_subset_iff.mpr (by simp), hu⟩
  rcases hmid with hl | hr
  · have := congrArg Finset.card ((additiveIn_firstPerson_iff (by omega) _).mp hl)
    rw [Finset.card_pair ho.symm, Finset.card_singleton] at this
    omega
  · have := hr.1.2
    rw [Finset.card_pair ho.symm] at this
    omega

end Convexity

/-! ### Parameters (§§4.1–4.3) -/

/-- A feature on Number⁰ is inactive, active (22), or recursive, its two values allowed to
cooccur (23), written `[±F]*`. -/
inductive Activation where
  | inactive
  | active
  | recursive
  deriving DecidableEq, Fintype, Repr

/-- Under an activation a bundle carries no value of `[±F]`, one, or under recursion both, and no
more by the axiom of extension (27). -/
def Activation.signs : Activation → List (Finset Bool)
  | .inactive => [∅]
  | .active => [{true}, {false}]
  | .recursive => [{true}, {false}, {true, false}]

/-- A parameter setting fixes the activation of each feature. -/
structure Setting where
  /-- The activation of `[±atomic]`. -/
  atomic : Activation
  /-- The activation of `[±minimal]`. -/
  minimal : Activation
  /-- The activation of `[±additive]`. -/
  additive : Activation
  deriving DecidableEq, Fintype, Repr

namespace Setting

/-- A bundle of a setting values every active feature once and a recursive one once or twice. -/
def bundles (σ : Setting) : List Bundle := do
  let a ← σ.atomic.signs
  let m ← σ.minimal.signs
  let d ← σ.additive.signs
  pure (a.image (.atomic, ·) ∪ m.image (.minimal, ·) ∪ d.image (.additive, ·))

/-- A setting is legitimate unless `[±additive]` is its sole feature, which the convexity
condition (32) rules out (§4.5, `not_ordConnected_plusAdditive_firstPerson`). -/
def Legitimate (σ : Setting) : Prop :=
  σ.additive ≠ .inactive → σ.atomic ≠ .inactive ∨ σ.minimal ≠ .inactive

instance (σ : Setting) : Decidable σ.Legitimate := by unfold Legitimate; infer_instance

end Setting

/-- A conventionalized cut (14) is low, bounding paucals, or high, bounding greater plurals. -/
inductive Height where
  | low
  | high
  deriving DecidableEq, Fintype, Repr

/-- The sociosemantic convention (14) places no cut without `[±additive]`, one cut with it, and
under recursion a low cut and a second cut above it (§3.3). Two high cuts, Banyun's greater and
greatest plurals, are left out. -/
inductive Convention where
  | none
  | one (h : Height)
  | two (h : Height)
  deriving DecidableEq, Fintype, Repr

/-- A convention fits an activation of `[±additive]` when it has as many cuts. -/
def Convention.Fits : Convention → Activation → Prop
  | .none, .inactive | .one _, .active | .two _, .recursive => True
  | _, _ => False

instance : ∀ c a, Decidable (Convention.Fits c a)
  | .none, .inactive | .one _, .active | .two _, .recursive => isTrue trivial
  | .none, .active | .none, .recursive | .one _, .inactive | .one _, .recursive
  | .two _, .inactive | .two _, .active => isFalse id

/-- A bundle is labelled with the descriptive name of its number (p. 201), after Table 3. -/
def Bundle.label (c : Convention) (b : Bundle) : Number :=
  if (.atomic, true) ∈ b then .singular
  else if b.CarriesBoth .minimal then (if (.atomic, false) ∈ b then .trial else .unitAugmented)
  else if (.minimal, true) ∈ b then (if (.atomic, false) ∈ b then .dual else .minimal)
  else if b.CarriesBoth .additive then (if c = .two .low then .greaterPaucal else .plural)
  else if (.additive, false) ∈ b then (if c = .one .high then .plural else .paucal)
  else if (.additive, true) ∈ b then
    (if c = .one .high ∨ c = .two .high then .greaterPlural else .plural)
  else if (.minimal, false) ∈ b ∧ (.atomic, false) ∉ b then .augmented
  else if b = ∅ then .general else .plural

/-- A bundle is labelled singular exactly when it carries `[+atomic]`. -/
theorem Bundle.label_eq_singular_iff {c : Convention} {b : Bundle} :
    Bundle.label c b = .singular ↔ (.atomic, true) ∈ b := by
  unfold Bundle.label
  split_ifs <;> simp_all

/-- Only `[+atomic]` restricts and only the singular carries it, so in every system a bundle is
defined where its label is. -/
theorem Bundle.dom_eq_dom_label {E : Type*} [PartialOrder E] [OrderBot E] (c : Convention)
    (b : Bundle) :
    Bundle.dom (E := E) b = Number.dom (some (Bundle.label c b)) := by
  rw [Bundle.dom_eq]
  split_ifs with h
  · rw [Bundle.label_eq_singular_iff.2 h]
  · exact (Number.dom_eq_univ_of_ne_singular fun e ↦
      h (Bundle.label_eq_singular_iff.1 (Option.some_injective _ e))).symm

/-! ### The strata of a bundle (§§2.2, 4.3) -/

/-- A region of strata is empty, the stratum `n`, or every positive stratum from `n` up. -/
inductive Strata where
  | empty
  | point (n : ℕ)
  | ray (n : ℕ)
  deriving DecidableEq, Repr

namespace Strata

/-- `s.toSet` is the set of the strata of `s`. -/
def toSet : Strata → Set ℕ
  | empty => ∅
  | point n => {n}
  | ray n => Set.Ici (max n 1)

instance : ∀ (s : Strata) (k : ℕ), Decidable (k ∈ s.toSet)
  | empty, _ => inferInstanceAs (Decidable False)
  | point n, k => inferInstanceAs (Decidable (k = n))
  | ray n, k => inferInstanceAs (Decidable (max n 1 ≤ k))

/-- The strata a valued feature selects: `[+atomic]` keeps the stratum one and `[−atomic]` drops
it, `[+minimal]` keeps the least stratum and `[−minimal]` drops it. -/
def restrict : Feature → Bool → Strata → Strata
  | .atomic, _, empty => empty
  | .atomic, true, point n => if n = 1 then point 1 else empty
  | .atomic, true, ray n => if n ≤ 1 then point 1 else empty
  | .atomic, false, point n => if n = 1 then empty else point n
  | .atomic, false, ray n => ray (max n 2)
  | .minimal, true, empty => empty
  | .minimal, true, point n => point n
  | .minimal, true, ray n => point (max n 1)
  | .minimal, false, empty => empty
  | .minimal, false, point _ => empty
  | .minimal, false, ray n => ray (max n 1 + 1)
  | .additive, _, s => s

/-- Membership in a region of strata is constant from its bound on. -/
def bound : Strata → ℕ
  | empty => 0
  | point n => n + 1
  | ray n => max n 1

theorem atomize_toSet (s : Strata) : atomize s.toSet = (s.restrict .minimal true).toSet := by
  cases s with
  | empty => exact (atomize_subset _).antisymm (Set.empty_subset _)
  | point n => exact Set.ext fun _ ↦ (Set.subsingleton_singleton.isAntichain _).minimal_mem_iff
  | ray n => exact atomize_Ici _

theorem restrict_toSet (f : Feature) (v : Bool) (s : Strata) :
    f.restrict v s.toSet = (s.restrict f v).toSet := by
  match f, v with
  | .atomic, true =>
    ext k
    cases s with
    | empty => simp [toSet, restrict]
    | point n =>
      by_cases h : n = 1 <;> simp [toSet, restrict, Nat.isAtom_iff_eq_one, h]
      omega
    | ray n =>
      by_cases h : n ≤ 1 <;> simp [toSet, restrict, Nat.isAtom_iff_eq_one, h]
      all_goals omega
  | .atomic, false =>
    ext k
    cases s with
    | empty => simp [toSet, restrict]
    | point n =>
      by_cases h : n = 1 <;> simp [toSet, restrict, Nat.isAtom_iff_eq_one, h]
      omega
    | ray n => simp [toSet, restrict, Nat.isAtom_iff_eq_one]; omega
  | .minimal, true => exact atomize_toSet s
  | .minimal, false =>
    ext k
    rw [Feature.mem_restrict_minimal_false, atomize_toSet]
    cases s <;> simp [toSet, restrict]
    omega
  | .additive, _ => cases s <;> rfl

theorem mem_of_restrict {f : Feature} {v : Bool} {s : Strata} {k : ℕ}
    (h : k ∈ (s.restrict f v).toSet) : k ∈ s.toSet :=
  Feature.restrict_le f v s.toSet (s.restrict_toSet f v ▸ h)

theorem mem_iff_of_bound_le {s : Strata} (hs : s.bound ≤ 4) {k : ℕ} (hk : 4 ≤ k) :
    k ∈ s.toSet ↔ 4 ∈ s.toSet := by
  cases s <;> simp only [bound] at hs <;>
    simp only [toSet, Set.mem_empty_iff_false, Set.mem_singleton_iff, Set.mem_Ici] <;> omega

end Strata

/-- The strata a bundle's `[±atomic]` and `[±minimal]` values select from `s`, in the order
(28). -/
def Bundle.strata (b : Bundle) (s : Strata) : Strata :=
  b.step (.minimal, true) (Strata.restrict .minimal true) <|
    b.step (.minimal, false) (Strata.restrict .minimal false) <|
    b.step (.atomic, true) (Strata.restrict .atomic true) <|
    b.step (.atomic, false) (Strata.restrict .atomic false) s

private theorem Bundle.step_map {X Y : Type*} (b : Bundle) (v : Feature × Bool) {f : X → X}
    {g : Y → Y} {φ : X → Y} (h : ∀ x, φ (f x) = g (φ x)) (x : X) :
    φ (b.step v f x) = b.step v g (φ x) := by
  unfold Bundle.step; split_ifs <;> simp [h]

theorem Bundle.exact_toSet (b : Bundle) (s : Strata) :
    b.exact s.toSet = (Bundle.strata b s).toSet := by
  simp only [Bundle.exact, Bundle.strata]
  rw [Bundle.step_map b _ fun s ↦ (Strata.atomize_toSet s).symm,
    Bundle.step_map b _ fun s ↦ (Strata.restrict_toSet .minimal false s).symm,
    Bundle.step_map b _ fun s ↦ (Strata.restrict_toSet .atomic true s).symm,
    Bundle.step_map b _ fun s ↦ (Strata.restrict_toSet .atomic false s).symm]

theorem bound_strata_le : ∀ b : Bundle, ∀ p ≤ 2, (Bundle.strata b (.ray p)).bound ≤ 4 := by decide

-- §4.2
theorem le_three_of_strata_eq_point (b : Bundle) {p : ℕ} (hp : p ≤ 2) {n : ℕ}
    (h : Bundle.strata b (.ray p) = .point n) : n ≤ 3 := by
  have := bound_strata_le b p hp
  rw [h, Strata.bound] at this
  omega

section Region

variable {α : Type*} [DecidableEq α] {B : Finset α}

omit [DecidableEq α] in
private theorem step_region (b : Bundle) (v : Feature × Bool)
    {f : Set (Finset α) → Set (Finset α)} {g : Strata → Strata} {s : Strata}
    (h : f (region B s.toSet) = region B (g s).toSet) :
    b.step v f (region B s.toSet) = region B (b.step v g s).toSet := by
  unfold Bundle.step; split_ifs <;> simp [h]

private theorem step_mem (b : Bundle) (v : Feature × Bool) {g : Strata → Strata}
    (hg : ∀ {t : Strata} {k : ℕ}, k ∈ (g t).toSet → k ∈ t.toSet) {s : Strata} {k : ℕ}
    (h : k ∈ (b.step v g s).toSet) : k ∈ s.toSet := by
  unfold Bundle.step at h; split_ifs at h; exacts [hg h, h]

omit [DecidableEq α] in
theorem Bundle.exact_region (b : Bundle) {s : Strata} (hs : ∀ k ∈ s.toSet, B.card ≤ k) :
    b.exact (region B s.toSet) = region B (Bundle.strata b s).toSet := by
  have h₁ : ∀ {k}, k ∈ (b.step (.atomic, false) (Strata.restrict .atomic false) s).toSet →
      k ∈ s.toSet :=
    step_mem b _ Strata.mem_of_restrict
  have h₂ : ∀ {t k}, k ∈ (b.step (.atomic, true) (Strata.restrict .atomic true) t).toSet →
      k ∈ t.toSet :=
    step_mem b _ Strata.mem_of_restrict
  have h₃ : ∀ {t k},
      k ∈ (b.step (.minimal, false) (Strata.restrict .minimal false) t).toSet → k ∈ t.toSet :=
    step_mem b _ Strata.mem_of_restrict
  simp only [Bundle.exact, Bundle.strata]
  rw [step_region b _ (by rw [restrict_region _ _ hs, Strata.restrict_toSet]),
    step_region b _ (by rw [restrict_region _ _ fun k hk ↦ hs k (h₁ hk), Strata.restrict_toSet]),
    step_region b _ (by rw [restrict_region _ _ fun k hk ↦ hs k (h₁ (h₂ hk)),
      Strata.restrict_toSet]),
    step_region b _ (by rw [atomize_region fun k hk ↦ hs k (h₁ (h₂ (h₃ hk))),
      Strata.atomize_toSet])]

end Region

/-! ### Cells and number systems (§5.1) -/

/-- `Bundle.Cut lo hi b k` holds when the stratum `k` survives the cuts the `[±additive]` values of
`b` make at `lo` and `hi`, lying below the first for `[−additive]`, at or above it for
`[+additive]`, and between the two for both (§3.3). -/
def Bundle.Cut (lo hi : ℕ) (b : Bundle) (k : ℕ) : Prop :=
  ((.additive, true) ∈ b → lo ≤ k) ∧
    ((.additive, false) ∈ b → k < if (.additive, true) ∈ b then hi else lo)

instance (lo hi : ℕ) (b : Bundle) : DecidablePred (Bundle.Cut lo hi b) := fun _ ↦ by
  unfold Bundle.Cut; infer_instance

/-- A bundle denotes the elements of its exact region that survive its cuts, graded by `g`. -/
def Bundle.denote {D : Type*} [SemilatticeSup D] [OrderBot D] (g : D → ℕ) (lo hi : ℕ) (b : Bundle)
    (P : Set D) (x : D) : Prop :=
  x ∈ b.exact P ∧ Bundle.Cut lo hi b (g x)

/-- The cell of a bundle in a setting is its denotation less those of the more specific bundles,
as the plural of Figure 7 is `Q+ \ Q′`. -/
def Setting.cell {D : Type*} [SemilatticeSup D] [OrderBot D] (σ : Setting) (g : D → ℕ) (lo hi : ℕ)
    (P : Set D) (b : Bundle) (x : D) : Prop :=
  Bundle.denote g lo hi b P x ∧ ∀ b' ∈ σ.bundles, b ⊂ b' → ¬ Bundle.denote g lo hi b' P x

theorem Setting.cell_strata_iff (σ : Setting) (lo hi : ℕ) (s : Strata) (b : Bundle) (k : ℕ) :
    σ.cell id lo hi s.toSet b k ↔ (k ∈ (Bundle.strata b s).toSet ∧ Bundle.Cut lo hi b k) ∧
      ∀ b' ∈ σ.bundles, b ⊂ b' → ¬ (k ∈ (Bundle.strata b' s).toSet ∧ Bundle.Cut lo hi b' k) := by
  simp only [Setting.cell, Bundle.denote, Bundle.exact_toSet, id]

instance (σ : Setting) (lo hi : ℕ) (s : Strata) (b : Bundle) :
    DecidablePred (σ.cell id lo hi s.toSet b) := fun k ↦
  decidable_of_iff _ (σ.cell_strata_iff lo hi s b k).symm

/-- `collapse lo hi` keeps the strata up to four and sends those below `lo`, those from `lo` below
`hi`, and those from `hi` up to four, five and six. -/
def collapse (lo hi k : ℕ) : ℕ :=
  if k ≤ 4 then k else if k < lo then 4 else if k < hi then 5 else 6

theorem cut_collapse {lo hi : ℕ} (h : 4 < lo) (b : Bundle) (k : ℕ) :
    Bundle.Cut lo hi b k ↔ Bundle.Cut 5 6 b (collapse lo hi k) := by
  unfold Bundle.Cut collapse
  by_cases ha : (.additive, true) ∈ b <;> by_cases hb : (.additive, false) ∈ b <;>
    simp only [ha, hb, ite_true, ite_false, forall_const, false_implies, and_true, true_and] <;>
    split_ifs <;> omega

theorem mem_strata_collapse {lo hi p : ℕ} (hp : p ≤ 2) (b : Bundle) (k : ℕ) :
    k ∈ (Bundle.strata b (.ray p)).toSet ↔ collapse lo hi k ∈ (Bundle.strata b (.ray p)).toSet := by
  have h4 := fun j (hj : 4 ≤ j) ↦ Strata.mem_iff_of_bound_le (bound_strata_le b p hp) hj
  unfold collapse
  split_ifs
  · rfl
  · exact h4 k (by omega)
  · rw [h4 k (by omega), h4 5 (by omega)]
  · rw [h4 k (by omega), h4 6 (by omega)]

theorem cell_collapse {lo hi p : ℕ} (h : 4 < lo) (hp : p ≤ 2) (σ : Setting) (b : Bundle)
    (k : ℕ) :
    σ.cell id lo hi (Strata.ray p).toSet b k ↔
      σ.cell id 5 6 (Strata.ray p).toSet b (collapse lo hi k) := by
  simp only [Setting.cell_strata_iff, mem_strata_collapse hp (lo := lo) (hi := hi) _ k,
    cut_collapse h _ k]

theorem exists_cell_iff {lo hi p : ℕ} (h₁ : 4 < lo) (h₂ : lo < hi) (hp : p ≤ 2) (σ : Setting)
    (b : Bundle) :
    (∃ k, σ.cell id lo hi (Strata.ray p).toSet b k) ↔
      ∃ k, k ≤ 6 ∧ σ.cell id 5 6 (Strata.ray p).toSet b k := by
  refine ⟨fun ⟨k, hk⟩ ↦ ⟨collapse lo hi k, by unfold collapse; split_ifs <;> omega,
    (cell_collapse h₁ hp σ b k).mp hk⟩, fun ⟨j, hj, hc⟩ ↦ ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, collapse lo hi k = j := by
    by_cases h4 : j ≤ 4
    · exact ⟨j, by simp [collapse, h4]⟩
    · by_cases h5 : j = 5
      · exact ⟨lo, by unfold collapse; split_ifs <;> omega⟩
      · exact ⟨hi, by unfold collapse; split_ifs <;> omega⟩
  exact ⟨k, (cell_collapse h₁ hp σ b k).mpr hc⟩

namespace Setting

/-- The number system of a setting on the person lattice over a base of `p` atoms consists of its
bundles with nonempty cells, computed with the cuts at five and six (`filter_cell_eq_system`). -/
def system (σ : Setting) (p : ℕ) : List Bundle :=
  σ.bundles.filter fun b ↦
    decide (∃ k : ℕ, k ≤ 6 ∧ σ.cell (D := ℕ) id 5 6 (Strata.ray p).toSet b k)

theorem mem_system {σ : Setting} {p : ℕ} {b : Bundle} :
    b ∈ σ.system p ↔ b ∈ σ.bundles ∧ ∃ k, k ≤ 6 ∧ σ.cell id 5 6 (Strata.ray p).toSet b k := by
  simp [system]

/-- The values of a setting's system are its bundles' labels. -/
def values (σ : Setting) (c : Convention) (p : ℕ) : List Number :=
  (σ.system p).map (Bundle.label c)

/-- A setting's third-person system, general number lying outside it. -/
def toSystem (σ : Setting) (c : Convention) : Finset Number :=
  ((σ.values c 0).filter (· ≠ .general)).toFinset

end Setting

section Lattice

variable {α : Type*} [DecidableEq α]

theorem cell_region {B : Finset α} {lo hi : ℕ} (σ : Setting) (b : Bundle) (x : Finset α) :
    σ.cell Finset.card lo hi (region B (Strata.ray B.card).toSet) b x ↔
      B ⊆ x ∧ σ.cell id lo hi (Strata.ray B.card).toSet b x.card := by
  have hs : ∀ k ∈ (Strata.ray B.card).toSet, B.card ≤ k := fun k hk ↦ le_of_max_le_left hk
  simp only [Setting.cell, Bundle.denote, Bundle.exact_region _ hs, Bundle.exact_toSet, mem_region,
    id]
  constructor
  · rintro ⟨⟨⟨hB, hE⟩, hb⟩, h⟩
    exact ⟨hB, ⟨hE, hb⟩, fun b' hb' hbb' ⟨hE', hb''⟩ ↦ h b' hb' hbb' ⟨⟨hB, hE'⟩, hb''⟩⟩
  · rintro ⟨hB, ⟨hE, hb⟩, h⟩
    exact ⟨⟨⟨hB, hE⟩, hb⟩, fun b' hb' hbb' ⟨⟨_, hE'⟩, hb''⟩ ↦ h b' hb' hbb' ⟨hE', hb''⟩⟩

open Classical in
/-- On the person lattice over any base of at most two atoms, given infinitely many atoms, and
for every placement of the cuts above four atoms, the bundles of a setting with nonempty cells
form its system. -/
theorem filter_cell_eq_system [Infinite α] {B : Finset α} (hB : B.card ≤ 2) {lo hi : ℕ}
    (h₁ : 4 < lo) (h₂ : lo < hi) (σ : Setting) :
    σ.bundles.filter (fun b ↦ ∃ x, σ.cell Finset.card lo hi
      (region B (Strata.ray B.card).toSet) b x) = σ.system B.card := by
  refine List.filter_congr fun b _ ↦ decide_eq_decide.mpr ?_
  rw [← exists_cell_iff h₁ h₂ hB]
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x.card, ((cell_region σ b x).mp hx).2⟩, fun ⟨k, hk⟩ ↦ ?_⟩
  have hBk : B.card ≤ k := le_of_max_le_left (Bundle.exact_le b _ hk.1.1)
  obtain ⟨x, hBx, rfl⟩ := Infinite.exists_superset_card_eq B k hBk
  exact ⟨x, (cell_region σ b x).mpr ⟨hBx, hk⟩⟩

end Lattice

/-! ### The typology (§5.1)

By `filter_cell_eq_system`, the following hold of every person lattice and every placement of
the cuts above four atoms. -/

theorem exists_mem_cell {lo hi p : ℕ} (h : 4 < lo) (hp : p ≤ 2) (σ : Setting) {k : ℕ}
    (hk : max p 1 ≤ k) : ∃ b ∈ σ.bundles, σ.cell id lo hi (Strata.ray p).toSet b k := by
  have ref : ∀ σ : Setting, ∀ p ≤ 2, ∀ j ≤ 6, max p 1 ≤ j →
      ∃ b ∈ σ.bundles, σ.cell (D := ℕ) id 5 6 (Strata.ray p).toSet b j := by
    decide +kernel
  obtain ⟨b, hb, hc⟩ := ref σ p hp (collapse lo hi k) (by unfold collapse; split_ifs <;> omega)
    (by unfold collapse; split_ifs <;> omega)
  exact ⟨b, hb, (cell_collapse h hp σ b k).mpr hc⟩

theorem disjoint_cell {lo hi p : ℕ} (h : 4 < lo) (hp : p ≤ 2) (σ : Setting) {b b' : Bundle}
    (hb : b ∈ σ.bundles) (hb' : b' ∈ σ.bundles) (hne : b ≠ b') :
    Disjoint (σ.cell id lo hi (Strata.ray p).toSet b)
      (σ.cell id lo hi (Strata.ray p).toSet b') := by
  rw [Pi.disjoint_iff]
  intro k
  rw [Prop.disjoint_iff]
  have ref : ∀ σ : Setting, ∀ p ∈ [0, 1, 2], ∀ b ∈ σ.system p, ∀ b' ∈ σ.system p, b ≠ b' →
      ∀ j ≤ 6, σ.cell (D := ℕ) id 5 6 (Strata.ray p).toSet b j →
        ¬ σ.cell (D := ℕ) id 5 6 (Strata.ray p).toSet b' j := by
    decide +kernel
  rw [cell_collapse h hp, cell_collapse h hp]
  have hj : collapse lo hi k ≤ 6 := by unfold collapse; split_ifs <;> omega
  exact fun ⟨h₁, h₂⟩ ↦ ref σ p (by interval_cases p <;> simp) b
    (Setting.mem_system.mpr ⟨hb, _, hj, h₁⟩) b' (Setting.mem_system.mpr ⟨hb', _, hj, h₂⟩) hne _
    hj h₁ h₂

theorem nodup_values : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive →
    (σ.values c 0).Nodup := by
  decide +kernel

-- §4.1
theorem values_atomic_recursive : ∀ m d : Activation, ∀ c : Convention,
    (Setting.mk .recursive m d).values c 0 = (Setting.mk .active m d).values c 0 := by
  decide +kernel

-- p. 203
theorem system_atomic_minimal :
    (⟨.active, .inactive, .inactive⟩ : Setting).system 0 = [{(.atomic, true)}, {(.atomic, false)}] ∧
      (⟨.inactive, .active, .inactive⟩ : Setting).system 0 =
        [{(.minimal, true)}, {(.minimal, false)}] ∧
      (⟨.active, .inactive, .inactive⟩ : Setting).system 2 = [{(.atomic, false)}] ∧
      (⟨.inactive, .active, .inactive⟩ : Setting).system 2 =
        [{(.minimal, true)}, {(.minimal, false)}] := by
  decide +kernel

/-- (26)'s quadral `[+minimal −minimal −minimal −atomic]` is the trial bundle. -/
example : ({(.minimal, true), (.minimal, false), (.minimal, false), (.atomic, false)} : Bundle) =
    {(.minimal, true), (.minimal, false), (.atomic, false)} := by
  decide

-- p. 205
theorem length_approximative_le_two : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive →
    ((σ.values c 0).filter (· ∈ [.paucal, .greaterPaucal, .greaterPlural])).length ≤ 2 := by
  decide +kernel

theorem length_values_le_six : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive →
    (σ.values c 0).length ≤ 6 := by
  decide +kernel

/-- Every legitimate setting satisfies Table 1 except `{±additive(*), ±minimal*}`, two lacunae of
Table 3 whose unit augmented has no augmented. -/
theorem satisfiesUniversals_toSystem_iff : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive →
    σ.Legitimate → (SatisfiesUniversals (σ.toSystem c) ↔
      ¬ (σ.atomic = .inactive ∧ σ.minimal = .recursive ∧ σ.additive ≠ .inactive)) := by
  decide +kernel

-- Table 1 [corbett-2000]
theorem satisfiesUniversals_corbett (c : Corbett2000.Choices) : SatisfiesUniversals c.toSystem := by
  obtain ⟨⟨d, p, gp⟩, g, f⟩ := c
  change SatisfiesUniversals (Corbett2000.Choices.mk ⟨d, p, gp⟩ .none 0).toSystem
  fin_cases d <;> fin_cases p <;> cases gp <;> decide


section Table3

/-- Table 3 pairs each setting and convention with the system of its example language, as
[corbett-2000] records it where it does, or of a lacuna; Banyun's row is left out. -/
def table3 : List (Setting × Convention × Finset Number) :=
  [(⟨.inactive, .inactive, .inactive⟩, .none, Corbett2000.piraha),
   (⟨.active, .inactive, .inactive⟩, .none, {.singular, .plural}),  -- Svan
   (⟨.inactive, .active, .inactive⟩, .none, {.minimal, .augmented}),  -- Winnebago
   (⟨.inactive, .recursive, .inactive⟩, .none, Corbett2000.rembarrnga),
   (⟨.active, .active, .inactive⟩, .none, {.singular, .dual, .plural}),  -- Kiowa
   (⟨.active, .inactive, .active⟩, .one .low, Corbett2000.bayso.toSystem),
   (⟨.active, .inactive, .active⟩, .one .high, {.singular, .plural, .greaterPlural}),  -- Fula
   (⟨.inactive, .active, .active⟩, .one .low, {.minimal, .paucal, .plural}),  -- Mebengokre
   (⟨.active, .recursive, .inactive⟩, .none, Corbett2000.larike.toSystem),
   (⟨.inactive, .recursive, .active⟩, .one .low, {.minimal, .unitAugmented, .paucal, .plural}),
   (⟨.inactive, .active, .recursive⟩, .two .low, {.minimal, .paucal, .greaterPaucal, .plural}),
   (⟨.inactive, .recursive, .recursive⟩, .two .low,
     {.minimal, .unitAugmented, .paucal, .greaterPaucal, .plural}),
   (⟨.active, .active, .active⟩, .one .low, Corbett2000.yimas.toSystem),
   (⟨.active, .active, .active⟩, .one .high, Corbett2000.mokilese.toSystem),
   (⟨.active, .recursive, .active⟩, .one .low, Corbett2000.marshallese.toSystem),
   (⟨.active, .active, .recursive⟩, .two .low, Corbett2000.sursurunga.toSystem),
   (⟨.active, .active, .recursive⟩, .two .high, Corbett2000.meleFila.toSystem),
   (⟨.active, .recursive, .recursive⟩, .two .low,
     {.singular, .dual, .trial, .paucal, .greaterPaucal, .plural})]

-- The rows carry `Finset Number`, itself finite, so `decide` would otherwise range over every
-- triple rather than the eighteen rows.
attribute [local instance high] List.decidableBAll

/-- Every row of Table 3 is generated. -/
theorem table3_generated : ∀ r ∈ table3, (r.1.toSystem r.2.1) = r.2.2 := by
  decide +kernel

-- Table 3
theorem table3_legitimate : ∀ r ∈ table3, r.2.1.Fits r.1.additive ∧ r.1.Legitimate := by
  decide

/-! ### The order the settings induce

By (34) a number requires another when the settings that generate the first generate the second.
With the legitimate settings as a formal context, requirement is the order of the numbers'
attribute concepts, the markedness order of number derived from the features. -/

/-- The legitimate settings, under the conventions that fit them, form a formal context in which
a setting generates the numbers of its system. -/
def Generates (p : {p : Setting × Convention // p.2.Fits p.1.additive ∧ p.1.Legitimate})
    (v : Number) : Prop :=
  v ∈ (p.1.1.toSystem p.1.2)

/-- A number requires another when its attribute concept lies below the other's, the implication
schema (34). -/
abbrev Requires (b a : Number) : Prop :=
  Concept.ofAttribute Generates b ≤ Concept.ofAttribute Generates a

theorem requires_iff {b a : Number} : Requires b a ↔ ∀ σ : Setting, ∀ c : Convention,
    c.Fits σ.additive → σ.Legitimate → b ∈ (σ.toSystem c) → a ∈ (σ.toSystem c) := by
  rw [Requires, Concept.ofAttribute_le_ofAttribute_iff]
  exact ⟨fun h σ c hc hσ ↦ h (x := ⟨(σ, c), hc, hσ⟩), fun h ⦃p⦄ ↦ h p.1.1 p.1.2 p.2.1 p.2.2⟩

/-- Implications with one consequent that the settings derive, Table 1's but the unit
augmented's, which requires the minimal instead, with the greater plural's strengthened to the
plural, since no setting generates the greater plural with the augmented. -/
def derivedImplications : List (Number × Number) :=
  [(.trial, .dual), (.dual, .singular), (.singular, .plural), (.unitAugmented, .minimal),
    (.augmented, .minimal), (.greaterPaucal, .paucal), (.paucal, .plural),
    (.greaterPlural, .plural)]

/-- The settings derive each implication of `derivedImplications`. -/
theorem requires_of_mem_derivedImplications : ∀ e ∈ derivedImplications, Requires e.1 e.2 := by
  have h : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive → σ.Legitimate →
      ∀ e ∈ derivedImplications, e.1 ∈ (σ.toSystem c) → e.2 ∈ (σ.toSystem c) := by
    decide +kernel
  exact fun e he ↦ requires_iff.2 fun σ c hc hσ ↦ h σ c hc hσ e he

/-- The unit augmented does not require the augmented, since `{±additive, ±minimal*}` generates
it without. -/
theorem not_requires_unitAugmented_augmented : ¬ Requires .unitAugmented .augmented := fun h ↦
  absurd (requires_iff.1 h ⟨.inactive, .recursive, .active⟩ (.one .low) trivial (by decide)
    (by decide)) (by decide)

-- Table 3
theorem mem_table3_of_requires {b a : Number} (h : Requires b a) {r} (hr : r ∈ table3)
    (hb : b ∈ r.2.2) : a ∈ r.2.2 := by
  rw [← table3_generated r hr] at hb ⊢
  exact requires_iff.1 h _ _ (table3_legitimate r hr).1 (table3_legitimate r hr).2 hb

/-- Every system of [corbett-2000]'s sequences of choices is a lower set of the order the settings
induce, having with a number every number that number requires. -/
theorem mem_of_requires_corbett (c : Corbett2000.Choices) {b a : Number} (h : Requires b a)
    (hb : b ∈ c.toSystem) : a ∈ c.toSystem := by
  have key : ∀ b a : Number, (∀ r ∈ table3, b ∈ r.2.2 → a ∈ r.2.2) →
      ∀ s : Corbett2000.Shape, b ∈ s.values → a ∈ s.values := by
    decide +kernel
  simp only [Corbett2000.Choices.toSystem, List.mem_toFinset] at hb ⊢
  exact key b a (fun _ hr ↦ mem_table3_of_requires h hr) c.toShape hb

theorem mem_of_requires_minimalAugmented {b a : Number} (h : Requires b a) :
    ∀ ns ∈ [Corbett2000.piraha, Corbett2000.rembarrnga, Corbett2000.ilocano],
      b ∈ ns → a ∈ ns := by
  have key : ∀ b a : Number, (∀ r ∈ table3, b ∈ r.2.2 → a ∈ r.2.2) →
      ∀ ns ∈ [Corbett2000.piraha, Corbett2000.rembarrnga, Corbett2000.ilocano],
        b ∈ ns → a ∈ ns := by
    decide +kernel
  exact key b a fun _ hr ↦ mem_table3_of_requires h hr

end Table3

/-! ### Composed number (§5.2) -/

-- (38), (40), (44), (45)
theorem yimas_system :
    (((⟨.active, .active, .active⟩ : Setting).system 0).map
      fun b ↦ (Bundle.label (.one .low) b, b)).Perm
    [(.singular, {(.atomic, true), (.minimal, true), (.additive, false)}),
     (.dual, {(.atomic, false), (.minimal, true), (.additive, false)}),
     (.paucal, {(.atomic, false), (.minimal, false), (.additive, false)}),
     (.plural, {(.atomic, false), (.minimal, false), (.additive, true)})] := by
  decide +kernel

/-- Mele-Fila's setting is `{±additive*, ±minimal, ±atomic}`, with a low and a high cut. -/
abbrev meleFila : Setting := ⟨.active, .active, .recursive⟩

-- Table 4
theorem meleFila_system :
    ((meleFila.system 0).map fun b ↦ (Bundle.label (.two .high) b, b)).Perm
    [(.singular, {(.atomic, true), (.minimal, true), (.additive, false)}),
     (.dual, {(.atomic, false), (.minimal, true), (.additive, false)}),
     (.paucal, {(.atomic, false), (.minimal, false), (.additive, false)}),
     (.plural, {(.atomic, false), (.minimal, false), (.additive, false), (.additive, true)}),
     (.greaterPlural, {(.atomic, false), (.minimal, false), (.additive, true)})] := by
  decide +kernel

/-- On every third-person lattice the plural holds of the sums from the lower cut up to the
upper, `[+additive]` relative to the one and `[−additive]` relative to the other. -/
theorem meleFila_cell_plural {α : Type*} [DecidableEq α] {lo hi : ℕ} (h₁ : 4 < lo)
    (x : Finset α) :
    meleFila.cell Finset.card lo hi {t | t.Nonempty}
      {(.atomic, false), (.minimal, false), (.additive, false), (.additive, true)} x ↔
        lo ≤ x.card ∧ x.card < hi := by
  have ref : ∀ j ≤ 6, meleFila.cell (D := ℕ) id 5 6 (Strata.ray 0).toSet
      {(.atomic, false), (.minimal, false), (.additive, false), (.additive, true)} j ↔ j = 5 := by
    decide +kernel
  have hP : {t : Finset α | t.Nonempty} = region ∅ (Strata.ray (∅ : Finset α).card).toSet := by
    ext t; simp [Strata.toSet, Finset.one_le_card]
  rw [hP, cell_region]
  simp only [Finset.empty_subset, true_and, Finset.card_empty]
  rw [cell_collapse h₁ (Nat.zero_le 2), ref _ (by unfold collapse; split_ifs <;> omega)]
  unfold collapse; split_ifs <;> omega

/-- The plural belongs to two natural classes, `[+additive]` with the greater plural and `[−minimal
−additive]` with the paucal (Table 4). -/
theorem meleFila_classes :
    (((meleFila.system 0).filter ((.additive, true) ∈ ·)).map
        (Bundle.label (.two .high))).Perm [.plural, .greaterPlural] ∧
      (((meleFila.system 0).filter
        fun b ↦ (.minimal, false) ∈ b ∧ (.additive, false) ∈ b).map
          (Bundle.label (.two .high))).Perm [.paucal, .plural] := by
  decide +kernel

/-! ### The value of a cardinality and resolution

The third-person cells partition the positive cardinalities, so a referent of `k` individuals
takes the label of the bundle whose cell holds it. -/

namespace Setting

/-- The value a setting gives a third-person referent of `k` individuals, the label of the bundle
whose cell holds `k`; the cells are disjoint (`disjoint_cell`). -/
def number (σ : Setting) (c : Convention) (lo hi : ℕ) (k : ℕ+) : Number :=
  ((σ.bundles.find? fun b ↦ decide (σ.cell id lo hi (Strata.ray 0).toSet b k)).map
    (Bundle.label c)).getD .general

theorem number_eq_of_collapse {lo hi : ℕ} (h : 4 < lo) (σ : Setting) (c : Convention)
    {k j : ℕ+} (hj : (j : ℕ) = collapse lo hi k) : σ.number c lo hi k = σ.number c 5 6 j := by
  have e : (fun b ↦ decide (σ.cell id lo hi (Strata.ray 0).toSet b k)) =
      fun b ↦ decide (σ.cell id 5 6 (Strata.ray 0).toSet b j) :=
    funext fun b ↦ decide_eq_decide.2 ((cell_collapse h (Nat.zero_le 2) σ b k).trans (by rw [hj]))
  simp only [number, e]

-- p. 213
/-- The settings derive Table 1's trial requiring the dual and dual the singular: the
determinate values of every system are an initial segment. -/
theorem toSystem_determinateInitial : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive →
    Number.DeterminateInitial (σ.toSystem c) := by
  decide +kernel

-- p. 213
/-- Without `[±additive]` and with `[±atomic]`, a setting gives a referent of `k` individuals the
determinate value of `k` if its system has one and the plural otherwise, the value
`Number.ofCard` gives. -/
theorem number_eq_ofCard (σ : Setting) (hd : σ.additive = .inactive)
    (ha : σ.atomic ≠ .inactive) {lo hi : ℕ} (h : 4 < lo) (k : ℕ+) :
    σ.number .none lo hi k = Number.ofCard (σ.toSystem .none) k := by
  have ref : ∀ σ : Setting, σ.additive = .inactive → σ.atomic ≠ .inactive → ∀ j < 6,
      σ.number .none 5 6 j.succPNat = Number.ofCard (σ.toSystem .none) j.succPNat := by
    decide +kernel
  have hk := k.pos
  have hc6 : collapse lo hi k ≤ 6 := by unfold collapse; split_ifs <;> omega
  have hc1 : 1 ≤ collapse lo hi k := by unfold collapse; split_ifs <;> omega
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j + 1 = collapse lo hi k := ⟨collapse lo hi k - 1, by omega⟩
  rw [number_eq_of_collapse h σ .none (j := j.succPNat) (by rw [Nat.succPNat_coe]; exact hj),
    ref σ hd ha j (by omega)]
  by_cases hk4 : (k : ℕ) ≤ 4
  · congr 1
    exact PNat.eq (by rw [Nat.succPNat_coe, Nat.succ_eq_add_one, hj, collapse, ite_eq_left hk4])
  · have : 4 ≤ collapse lo hi k := by unfold collapse; split_ifs <;> omega
    rw [Number.ofCard_of_three_lt (show 3 < (k : ℕ) by omega),
      Number.ofCard_of_three_lt (show 3 < j + 1 by omega)]

/-- With `[±additive]` and a cut above five, no function of the conjuncts' values gives a
coordination's: two cardinalities just below the cut share a cell, but adding one individual
to each puts one on either side of it. -/
theorem not_factorsThrough_number (σ : Setting) (c : Convention) (hc : c.Fits σ.additive)
    (hσ : σ.Legitimate) (hd : σ.additive ≠ .inactive) {lo hi : ℕ} (h₁ : 5 < lo) (h₂ : lo < hi) :
    ¬ (fun p : ℕ+ × ℕ+ ↦ σ.number c lo hi (p.1 + p.2)).FactorsThrough
      (Prod.map (σ.number c lo hi) (σ.number c lo hi)) := by
  have ref : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive → σ.Legitimate →
      σ.additive ≠ .inactive → σ.number c 5 6 4 ≠ σ.number c 5 6 5 := by
    decide +kernel
  have below (x : ℕ+) (hx : lo - 2 ≤ (x : ℕ)) (hx' : (x : ℕ) < lo) :
      σ.number c lo hi x = σ.number c 5 6 4 :=
    number_eq_of_collapse (by omega) σ c (show 4 = collapse lo hi x by
      unfold collapse; split_ifs <;> omega)
  have atLo : σ.number c lo hi ⟨lo, by omega⟩ = σ.number c 5 6 5 :=
    number_eq_of_collapse (by omega) σ c (show 5 = collapse lo hi lo by
      unfold collapse; split_ifs <;> omega)
  intro H
  have e := @H (⟨lo - 2, by omega⟩, 1) (⟨lo - 1, by omega⟩, 1) (by
    simp only [Prod.map, Prod.mk.injEq, and_true]
    rw [below ⟨lo - 2, by omega⟩ le_rfl (by simp; omega),
      below ⟨lo - 1, by omega⟩ (by simp; omega) (by simp; omega)])
  have e₁ : (⟨lo - 2, by omega⟩ : ℕ+) + 1 = ⟨lo - 1, by omega⟩ :=
    PNat.eq (show lo - 2 + 1 = lo - 1 by omega)
  have e₂ : (⟨lo - 1, by omega⟩ : ℕ+) + 1 = ⟨lo, by omega⟩ :=
    PNat.eq (show lo - 1 + 1 = lo by omega)
  dsimp only at e
  rw [e₁, e₂, below ⟨lo - 1, by omega⟩ (by simp; omega) (by simp; omega), atLo] at e
  exact ref σ c hc hσ hd e

/-- A setting with `[±atomic]` and its cuts above five gives a coordination a value that its
conjuncts' values determine exactly when it lacks `[±additive]`, approximative values
excluding it. -/
theorem factorsThrough_number_iff (σ : Setting) (c : Convention) (hc : c.Fits σ.additive)
    (hσ : σ.Legitimate) (ha : σ.atomic ≠ .inactive) {lo hi : ℕ} (h₁ : 5 < lo) (h₂ : lo < hi) :
    (fun p : ℕ+ × ℕ+ ↦ σ.number c lo hi (p.1 + p.2)).FactorsThrough
      (Prod.map (σ.number c lo hi) (σ.number c lo hi)) ↔ σ.additive = .inactive := by
  refine ⟨fun H ↦ ?_, fun hd ↦ ?_⟩
  · by_contra hd
    exact not_factorsThrough_number σ c hc hσ hd h₁ h₂ H
  · obtain rfl : c = .none := by
      rw [hd] at hc
      cases c
      · rfl
      all_goals exact hc.elim
    rw [funext (number_eq_ofCard σ hd ha (by omega))]
    exact Number.determinateInitial_iff_factorsThrough.1
      (toSystem_determinateInitial σ .none (hd ▸ trivial))

end Setting

end Harbour2014

end
