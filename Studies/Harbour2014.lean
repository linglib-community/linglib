module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Interval.Set.OrdConnected
public import Linglib.Semantics.Plurality.Number
public import Linglib.Core.Order.Concept
public import Studies.Corbett2000

/-!
# Harbour (2014): Paucity, Abundance, and the Theory of Number

Harbour characterizes the approximative numbers, paucal and greater plural, by a feature
`[±additive]` of additive closure, beside the `[±atomic]` and `[±minimal]` that give the exact
numbers. Each feature acts on a lattice of atoms and their sums, and the same two parameters
govern all three: whether a feature is active on Number⁰ (22) and whether its two values may
cooccur (23). A sociosemantic convention fixes the height of the cut `[±additive]` induces (14).
A parameter setting generates a number system, the feature bundles with nonempty denotation, and
the typology of Table 3 and the implications of Table 1 are claims about these systems.

## Main definitions

* `Setting`, `Bundle`, `Convention`: parameter settings, feature bundles, and the placement of
  the cuts.
* `Setting.cell`: the region of a person lattice a bundle denotes in a setting.
* `Setting.system`: the number system a setting generates.
* `PlusAdditive`: the `[+additive]` elements of a region cut horizontally.
* `table1`, `SatisfiesTable1`: the implicational universals of Table 1.
* `Generates`, `Requires`: the legitimate settings as a formal context, and the order of its
  attribute concepts that (34) reads off them, one number requiring another.

## Main results

* `atomize_nonMinimalOf_iterate`: the successor-like function (31).
* `not_additiveIn_band`, `additiveIn_firstPerson_iff`: below a cut no element of the
  third-person lattice is `[+additive]`, and on the first-person lattice only the speaker is.
* `not_ordConnected_plusAdditive_firstPerson`: `{±additive}` alone cuts the first-person lattice
  nonconvexly, against the convexity condition (32).
* `filter_cell_eq_system`: on every person lattice with infinitely many atoms and for every
  placement of the cuts above four atoms, the bundles with nonempty cells form `Setting.system`.
* `table3_generated`: the systems of Table 3, with Corbett's records of its example languages.
* `satisfiesTable1_toSystem_iff`: Table 1 holds of every legitimate setting but
  `{±additive(*), ±minimal*}`, two lacunae whose unit augmented has no augmented.
* `requires_of_mem_derivedImplications`, `not_requires_unitAugmented_augmented`: the order the
  settings induce by (34) has the single implications of Table 1 but the unit augmented's.
* `mem_of_requires_corbett`: every system of Corbett's choices is a lower set of that order.
* `meleFila_cell_plural`, `meleFila_classes`: Mele-Fila's plural lies between the two cuts and
  shares a form with each neighbour (Table 4).

## Implementation notes

* A bundle is a `Finset` of signed features, so the axiom of extension (27) is built in, and it
  is interpreted in the order (28); its cell is its denotation less the more specific bundles',
  as the plural of Figure 7 is `Q+ \ Q′`.
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
open Number (additiveIn atomsOf nonAtomsOf nonMinimalOf)

/-! ### Person lattices and their strata (§2, (12)) -/

section Region

variable {α : Type*}

theorem atom_iff_eq_one {k : ℕ} : Atom k ↔ k = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h0 : k ≠ 0 := fun h0 ↦ h.1 (h0 ▸ isBot_bot)
    have := h.2 (y := 1) (by simp [isBot_iff_eq_bot]) (by omega)
    omega
  · rintro rfl
    exact ⟨by simp [isBot_iff_eq_bot], fun y hy _ ↦ by
      have : y ≠ 0 := fun h0 ↦ hy (h0 ▸ isBot_bot); omega⟩

/-- A region of the person lattice over `B` holds of the sums containing `B` whose number of
atoms satisfies `S`, a union of strata (12). -/
def region (B : Finset α) (S : ℕ → Prop) (s : Finset α) : Prop := B ⊆ s ∧ S s.card

variable {B : Finset α} {S : ℕ → Prop}

theorem atomize_region (hS : ∀ k, S k → B.card ≤ k) :
    atomize (region B S) = region B (atomize S) := by
  ext s
  refine ⟨fun h ↦ ⟨h.1.1, h.1.2, fun j hj hle ↦ ?_⟩, fun h ↦ ⟨⟨h.1, h.2.1⟩, fun t ht hts ↦ ?_⟩⟩
  · obtain ⟨t, hBt, hts, rfl⟩ := Finset.exists_subsuperset_card_eq h.1.1 (hS j hj) hle
    exact Finset.card_le_card (h.2 ⟨hBt, hj⟩ hts)
  · exact (Finset.eq_of_subset_of_card_le hts (h.2.2 ht.2 (Finset.card_le_card hts))).ge

theorem atom_iff_card {s : Finset α} : Atom s ↔ Atom s.card := by
  have h : (fun t : Finset α ↦ ¬ IsBot t) = region ∅ (fun k ↦ ¬ IsBot k) := by
    ext t; simp [region, isBot_iff_eq_bot]
  show atomize (fun t : Finset α ↦ ¬ IsBot t) s ↔ atomize (fun k : ℕ ↦ ¬ IsBot k) s.card
  rw [h, atomize_region fun _ _ ↦ Nat.zero_le _]
  simp [region]

variable [DecidableEq α]

theorem atomsOf_region : atomsOf (region B S) = region B (atomsOf S) := by
  ext s; simp only [atomsOf, region, atom_iff_card, and_assoc]

theorem nonAtomsOf_region : nonAtomsOf (region B S) = region B (nonAtomsOf S) := by
  ext s; simp only [nonAtomsOf, region, atom_iff_card, and_assoc]

theorem nonMinimalOf_region (hS : ∀ k, S k → B.card ≤ k) :
    nonMinimalOf (region B S) = region B (nonMinimalOf S) := by
  ext s; simp only [nonMinimalOf, atomize_region hS, region]; tauto

end Region

/-! ### The successor-like function (§4.4) -/

section Successor

variable {α : Type*} [DecidableEq α]

private theorem atomize_le (k : ℕ) : atomize (k ≤ ·) = (· = k) := by
  ext j
  exact ⟨fun h ↦ le_antisymm (h.2 le_rfl h.1) h.1, by rintro rfl; exact ⟨le_rfl, fun _ h _ ↦ h⟩⟩

private theorem nonMinimalOf_iterate (n : ℕ) : nonMinimalOf^[n] (2 ≤ ·) = (n + 2 ≤ ·) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    ext j; simp only [nonMinimalOf, atomize_le]; omega

private theorem nonMinimalOf_iterate_region (n : ℕ) (S : ℕ → Prop) :
    nonMinimalOf^[n] (region (∅ : Finset α) S) = region ∅ (nonMinimalOf^[n] S) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      nonMinimalOf_region fun _ _ ↦ Nat.zero_le _]

omit [DecidableEq α] in
private theorem nonempty_eq_region : (Finset.Nonempty : Finset α → Prop) = region ∅ (1 ≤ ·) := by
  ext t; simp [region, Finset.one_le_card]

/-- `(+minimal(−minimalⁿ(−atomic(P))))` holds of exactly the sums of `n + 2` atoms (31), the dual of
(30) at `n = 0` and the trial at `n = 1`. -/
theorem atomize_nonMinimalOf_iterate (n : ℕ) (s : Finset α) :
    atomize (nonMinimalOf^[n] (nonAtomsOf Finset.Nonempty)) s ↔ s.card = n + 2 := by
  have hna : nonAtomsOf (1 ≤ ·) = (2 ≤ ·) := by
    ext j; simp only [nonAtomsOf, atom_iff_eq_one]; omega
  rw [nonempty_eq_region, nonAtomsOf_region, hna, nonMinimalOf_iterate_region,
    nonMinimalOf_iterate, atomize_region fun _ _ ↦ Nat.zero_le _, atomize_le]
  simp [region]

-- (30)
theorem atomize_atomsOf (s : Finset α) :
    atomize (atomsOf Finset.Nonempty) s ↔ s.card = 1 := by
  have ha : atomsOf (1 ≤ ·) = ((· = 1) : ℕ → Prop) := by
    ext j; simp only [atomsOf, atom_iff_eq_one]; omega
  rw [nonempty_eq_region, atomsOf_region, ha, atomize_region fun _ _ ↦ Nat.zero_le _]
  simp only [region, Finset.empty_subset, true_and]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ hj _ ↦ hj ▸ h.le⟩⟩

end Successor

/-! ### Orders of composition (§§3.3, 4.1, 4.3) -/

section Orders

variable {D : Type*} [SemilatticeSup D]

-- §4.1, n. 15
theorem not_atomsOf_nonAtomsOf (P : D → Prop) (x : D) : ¬ atomsOf (nonAtomsOf P) x :=
  fun h ↦ h.1.2 h.2

-- §4.3
theorem not_atomsOf_nonMinimalOf {P : D → Prop} (hP : ∀ y, P y → ¬ IsBot y) (x : D) :
    ¬ atomsOf (nonMinimalOf P) x :=
  fun h ↦ h.1.2 (Number.singular_subset_minimal hP ⟨h.1.1, h.2⟩)

end Orders

/-! ### `[±additive]` and horizontal cuts (§3.1) -/

section Additive

variable {α : Type*} [DecidableEq α]

/-- A band holds of the sums of at least `lo` and fewer than `hi` atoms. -/
def Band (lo hi : ℕ) (s : Finset α) : Prop := lo ≤ s.card ∧ s.card < hi

/-- Given infinitely many atoms, no element of a band above the null individual is additive in it
(10), so `(+additive(−additive(P)))` is unsatisfiable (§3.3). -/
theorem not_additiveIn_band [Infinite α] {lo hi : ℕ} (hlo : 1 ≤ lo) (s : Finset α) :
    ¬ additiveIn (Band lo hi) s := by
  rintro ⟨⟨hl, hh⟩, h⟩
  obtain ⟨u, hsu, hu⟩ :=
    Infinite.exists_superset_card_eq s (s.card + max lo (hi - s.card)) (by omega)
  have hcard : (u \ s).card = max lo (hi - s.card) := by
    rw [Finset.card_sdiff_of_subset hsu, hu]; omega
  have := (h (u \ s) ⟨by omega, by omega⟩).2
  rw [Finset.sup_eq_union, Finset.union_sdiff_of_subset hsu, hu] at this
  omega

-- (10), (11)
theorem additiveIn_le_card {c : ℕ} {s : Finset α} (hs : c ≤ s.card) :
    additiveIn (c ≤ ·.card) s :=
  ⟨hs, fun _ _ ↦ hs.trans (Finset.card_le_card Finset.subset_union_left)⟩

theorem additiveIn_le_card' {i : α} {c : ℕ} {s : Finset α} (hi : i ∈ s) (hs : c ≤ s.card) :
    additiveIn (fun t ↦ i ∈ t ∧ c ≤ t.card) s :=
  ⟨⟨hi, hs⟩, fun _ _ ↦ ⟨Finset.mem_union_left _ hi,
    hs.trans (Finset.card_le_card Finset.subset_union_left)⟩⟩

-- n. 23
theorem additiveIn_atomize_superset (B : Finset α) : additiveIn (atomize (B ⊆ ·)) B := by
  have hB : atomize (B ⊆ ·) B := ⟨subset_rfl, fun _ hy _ ↦ hy⟩
  refine ⟨hB, fun y hy ↦ ?_⟩
  rw [le_antisymm (hy.2 subset_rfl hy.1) hy.1, sup_idem]
  exact hB

-- n. 23
theorem not_additiveIn_atomize_nonempty [Nontrivial α] (s : Finset α) :
    ¬ additiveIn (atomize Finset.Nonempty) s := by
  have key : ∀ t : Finset α, atomize Finset.Nonempty t ↔ t.card = 1 := fun t ↦ by
    rw [nonempty_eq_region, atomize_region fun _ _ ↦ Nat.zero_le _, atomize_le]; simp [region]
  rintro ⟨hs, h⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp ((key s).mp hs)
  obtain ⟨b, hb⟩ := exists_ne a
  have := (key _).mp (h {b} ((key _).mpr (Finset.card_singleton b)))
  rw [Finset.sup_eq_union, Finset.singleton_union, Finset.card_pair hb.symm] at this
  omega

end Additive

/-! ### Convexity (§4.5) -/

section Convexity

variable {α : Type*} [DecidableEq α]

/-- An element of a region `P` cut at `c` is `[+additive]` (10) when it is additive in the bounded
region below the cut or in the unbounded region above it. -/
def PlusAdditive (c : ℕ) (P : Finset α → Prop) (s : Finset α) : Prop :=
  additiveIn (fun t ↦ P t ∧ t.card < c) s ∨ additiveIn (fun t ↦ P t ∧ c ≤ t.card) s

theorem plusAdditive_nonempty_iff [Infinite α] {c : ℕ} (hc : 1 ≤ c) (s : Finset α) :
    PlusAdditive c Finset.Nonempty s ↔ c ≤ s.card := by
  have hb : (fun t : Finset α ↦ t.Nonempty ∧ t.card < c) = Band 1 c := by
    ext t; simp [Band, Finset.one_le_card]
  have ha : (fun t : Finset α ↦ t.Nonempty ∧ c ≤ t.card) = (c ≤ ·.card) := by
    ext t; exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.card_pos.mp (by omega), h⟩⟩
  rw [PlusAdditive, hb, ha]
  exact ⟨fun h ↦ h.elim (fun h ↦ (not_additiveIn_band le_rfl s h).elim) (·.1),
    fun h ↦ .inr (additiveIn_le_card h)⟩

-- (33)
theorem ordConnected_plusAdditive_nonempty [Infinite α] {c : ℕ} (hc : 1 ≤ c) :
    {s : Finset α | PlusAdditive c Finset.Nonempty s}.OrdConnected := by
  simp only [plusAdditive_nonempty_iff hc]
  exact IsUpperSet.ordConnected fun _ _ hst h ↦ h.trans (Finset.card_le_card hst)

/-- On the first-person exclusive lattice, only the speaker atom is additive below a cut (Figure 8).
-/
theorem additiveIn_firstPerson_iff [Infinite α] {i : α} {c : ℕ} (hc : 2 ≤ c) (s : Finset α) :
    additiveIn (fun t ↦ i ∈ t ∧ t.card < c) s ↔ s = {i} := by
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
    rw [Finset.sup_eq_union, Finset.union_insert, Finset.union_sdiff_of_subset hsu,
      Finset.insert_eq_of_mem (hsu hi), hu] at this
    omega
  · rintro rfl
    refine ⟨⟨Finset.mem_singleton_self i, by simp; omega⟩, fun t ht ↦ ?_⟩
    rwa [Finset.sup_eq_union, Finset.singleton_union, Finset.insert_eq_of_mem ht.1]

/-- `{±additive}` cuts the first-person lattice nonconvexly (p. 212), so by (32), after
[gardenfors-2004], `[±additive]` is never a language's sole number feature. -/
theorem not_ordConnected_plusAdditive_firstPerson [Infinite α] (i : α) {c : ℕ} (hc : 3 ≤ c) :
    ¬ {s | PlusAdditive c (i ∈ ·) s}.OrdConnected := by
  intro h
  obtain ⟨o, ho⟩ := exists_ne i
  obtain ⟨u, hu, huc⟩ := Infinite.exists_superset_card_eq {i, o} c
    (by rw [Finset.card_pair ho.symm]; omega)
  have hmid := h.out (x := {i}) (y := u)
    (.inl ((additiveIn_firstPerson_iff (by omega) _).mpr rfl))
    (.inr (additiveIn_le_card' (hu (by simp)) huc.ge))
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

/-- Harbour's number features are `[±atomic]`, `[±minimal]` and `[±additive]`. -/
inductive Feature where
  | atomic
  | minimal
  | additive
  deriving DecidableEq, Fintype, Repr

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

/-- A feature bundle is the set of its signed features, `(F, true)` standing for `+F` (§2.3). -/
abbrev Bundle := Finset (Feature × Bool)

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
  else if (.minimal, true) ∈ b then
    if (.minimal, false) ∈ b then (if (.atomic, false) ∈ b then .trial else .unitAugmented)
    else if (.atomic, false) ∈ b then .dual else .minimal
  else if (.additive, false) ∈ b then
    if (.additive, true) ∈ b then (if c = .two .low then .greaterPaucal else .plural)
    else if c = .one .high then .plural else .paucal
  else if (.additive, true) ∈ b then
    (if c = .one .high ∨ c = .two .high then .greaterPlural else .plural)
  else if (.minimal, false) ∈ b ∧ (.atomic, false) ∉ b then .augmented
  else if b = ∅ then .general else .plural

/-! ### The strata of a bundle (§§2.2, 4.3) -/

/-- A region of strata is empty, the stratum `n`, or every positive stratum from `n` up. -/
inductive Strata where
  | empty
  | point (n : ℕ)
  | ray (n : ℕ)
  deriving DecidableEq, Repr

namespace Strata

/-- `s.Mem k` holds when `k` is a stratum of `s`. -/
def Mem : Strata → ℕ → Prop
  | empty, _ => False
  | point n, k => k = n
  | ray n, k => max n 1 ≤ k

instance : ∀ s : Strata, DecidablePred s.Mem
  | empty => fun _ ↦ instDecidableFalse
  | point n => fun k ↦ inferInstanceAs (Decidable (k = n))
  | ray n => fun k ↦ inferInstanceAs (Decidable (max n 1 ≤ k))

/-- `[+atomic]` keeps the stratum one. -/
def atomic : Strata → Strata
  | point n => if n = 1 then point 1 else empty
  | ray n => if n ≤ 1 then point 1 else empty
  | empty => empty

/-- `[−atomic]` drops the stratum one. -/
def nonAtomic : Strata → Strata
  | point n => if n = 1 then empty else point n
  | ray n => ray (max n 2)
  | empty => empty

/-- `[+minimal]` keeps the least stratum. -/
def minimal : Strata → Strata
  | ray n => point (max n 1)
  | s => s

/-- `[−minimal]` drops the least stratum. -/
def nonMinimal : Strata → Strata
  | ray n => ray (max n 1 + 1)
  | _ => empty

/-- Membership in a region of strata is constant from its bound on. -/
def bound : Strata → ℕ
  | empty => 0
  | point n => n + 1
  | ray n => max n 1

theorem atomsOf_mem (s : Strata) : atomsOf s.Mem = s.atomic.Mem := by
  ext k
  cases s with
  | empty => simp [atomsOf, Mem, atomic]
  | point n =>
    by_cases h : n = 1 <;> simp [atomsOf, Mem, atomic, atom_iff_eq_one, h]
    all_goals omega
  | ray n =>
    by_cases h : n ≤ 1 <;> simp [atomsOf, Mem, atomic, atom_iff_eq_one, h]
    all_goals omega

theorem nonAtomsOf_mem (s : Strata) : nonAtomsOf s.Mem = s.nonAtomic.Mem := by
  ext k
  cases s with
  | empty => simp [nonAtomsOf, Mem, nonAtomic]
  | point n =>
    by_cases h : n = 1 <;> simp [nonAtomsOf, Mem, nonAtomic, atom_iff_eq_one, h]
    all_goals omega
  | ray n => simp [nonAtomsOf, Mem, nonAtomic, atom_iff_eq_one]; omega

theorem atomize_mem (s : Strata) : atomize s.Mem = s.minimal.Mem := by
  ext k
  cases s with
  | empty => exact ⟨fun h ↦ h.1, fun h ↦ h.elim⟩
  | point n => exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ hj _ ↦ (h.trans hj.symm).le⟩⟩
  | ray n =>
    simp only [minimal, Mem]
    exact ⟨fun h ↦ le_antisymm (h.2 le_rfl h.1) h.1, fun h ↦ ⟨h.ge, fun _ hj _ ↦ h ▸ hj⟩⟩

theorem nonMinimalOf_mem (s : Strata) : nonMinimalOf s.Mem = s.nonMinimal.Mem := by
  ext k; rw [nonMinimalOf, atomize_mem]; cases s <;> simp [Mem, minimal, nonMinimal]; omega

theorem mem_iff_of_bound_le {s : Strata} (hs : s.bound ≤ 4) {k : ℕ} (hk : 4 ≤ k) :
    s.Mem k ↔ s.Mem 4 := by
  cases s <;> simp only [bound] at hs <;> simp only [Mem] <;> omega

end Strata

/-- `b.step v f` applies `f` when the bundle `b` carries the signed feature `v`. -/
def Bundle.step {X : Type*} (b : Bundle) (v : Feature × Bool) (f : X → X) (x : X) : X :=
  if v ∈ b then f x else x

/-- The region a bundle's `[±atomic]` and `[±minimal]` values select from `P`, in the order
(28). -/
def Bundle.exact {D : Type*} [SemilatticeSup D] (b : Bundle) (P : D → Prop) : D → Prop :=
  b.step (.minimal, true) atomize <| b.step (.minimal, false) nonMinimalOf <|
    b.step (.atomic, true) atomsOf <| b.step (.atomic, false) nonAtomsOf P

/-- The strata a bundle's `[±atomic]` and `[±minimal]` values select from `s`, in the order
(28). -/
def Bundle.strata (b : Bundle) (s : Strata) : Strata :=
  b.step (.minimal, true) Strata.minimal <| b.step (.minimal, false) Strata.nonMinimal <|
    b.step (.atomic, true) Strata.atomic <| b.step (.atomic, false) Strata.nonAtomic s

private theorem Bundle.step_map {X Y : Type*} (b : Bundle) (v : Feature × Bool) {f : X → X}
    {g : Y → Y} {φ : X → Y} (h : ∀ x, φ (f x) = g (φ x)) (x : X) :
    φ (b.step v f x) = b.step v g (φ x) := by
  unfold step; split_ifs <;> simp [h]

theorem Bundle.exact_mem (b : Bundle) (s : Strata) : b.exact s.Mem = (b.strata s).Mem := by
  simp only [exact, strata]
  rw [b.step_map _ fun s ↦ (Strata.atomize_mem s).symm,
    b.step_map _ fun s ↦ (Strata.nonMinimalOf_mem s).symm,
    b.step_map _ fun s ↦ (Strata.atomsOf_mem s).symm,
    b.step_map _ fun s ↦ (Strata.nonAtomsOf_mem s).symm]

theorem Bundle.exact_le {D : Type*} [SemilatticeSup D] (b : Bundle) (P : D → Prop) {x : D}
    (h : b.exact P x) : P x := by
  have step_le : ∀ v (f : (D → Prop) → D → Prop), (∀ P x, f P x → P x) →
      ∀ P x, b.step v f P x → P x := by
    intro v f hf P x h; unfold step at h; split_ifs at h; exacts [hf _ _ h, h]
  exact step_le _ _ (fun _ _ h ↦ h.1) _ _ <| step_le _ _ (fun _ _ h ↦ h.1) _ _ <|
    step_le _ _ (fun _ _ h ↦ h.1) _ _ <| step_le _ _ (fun _ _ h ↦ h.1) _ _ h

theorem bound_strata_le : ∀ b : Bundle, ∀ p ≤ 2, (b.strata (.ray p)).bound ≤ 4 := by decide

-- §4.2
theorem le_three_of_strata_eq_point (b : Bundle) {p : ℕ} (hp : p ≤ 2) {n : ℕ}
    (h : b.strata (.ray p) = .point n) : n ≤ 3 := by
  have := bound_strata_le b p hp
  rw [h, Strata.bound] at this
  omega

section Region

variable {α : Type*} [DecidableEq α] {B : Finset α}

omit [DecidableEq α] in
private theorem step_region (b : Bundle) (v : Feature × Bool)
    {f : (Finset α → Prop) → Finset α → Prop} {g : Strata → Strata} {s : Strata}
    (h : f (region B s.Mem) = region B (g s).Mem) :
    b.step v f (region B s.Mem) = region B (b.step v g s).Mem := by
  unfold Bundle.step; split_ifs <;> simp [h]

private theorem step_mem (b : Bundle) (v : Feature × Bool) {g : Strata → Strata}
    (hg : ∀ {t : Strata} {k : ℕ}, (g t).Mem k → t.Mem k) {s : Strata} {k : ℕ}
    (h : (b.step v g s).Mem k) : s.Mem k := by
  unfold Bundle.step at h; split_ifs at h; exacts [hg h, h]

theorem Bundle.exact_region (b : Bundle) {s : Strata} (hs : ∀ k, s.Mem k → B.card ≤ k) :
    b.exact (region B s.Mem) = region B (b.strata s).Mem := by
  have h₁ : ∀ {k}, (b.step (.atomic, false) Strata.nonAtomic s).Mem k → s.Mem k :=
    step_mem b _ fun {t k} h ↦ (t.nonAtomsOf_mem ▸ h : nonAtomsOf t.Mem k).1
  have h₂ : ∀ {t k}, (b.step (.atomic, true) Strata.atomic t).Mem k → t.Mem k :=
    step_mem b _ fun {t k} h ↦ (t.atomsOf_mem ▸ h : atomsOf t.Mem k).1
  have h₃ : ∀ {t k}, (b.step (.minimal, false) Strata.nonMinimal t).Mem k → t.Mem k :=
    step_mem b _ fun {t k} h ↦ (t.nonMinimalOf_mem ▸ h : nonMinimalOf t.Mem k).1
  simp only [Bundle.exact, Bundle.strata]
  rw [step_region b _ (by rw [nonAtomsOf_region, Strata.nonAtomsOf_mem]),
    step_region b _ (by rw [atomsOf_region, Strata.atomsOf_mem]),
    step_region b _ (by rw [nonMinimalOf_region fun k hk ↦ hs k (h₁ (h₂ hk)),
      Strata.nonMinimalOf_mem]),
    step_region b _ (by rw [atomize_region fun k hk ↦ hs k (h₁ (h₂ (h₃ hk))),
      Strata.atomize_mem])]

end Region

/-! ### Cells and number systems (§5.1) -/

/-- `b.Cut lo hi k` holds when the stratum `k` survives the cuts the `[±additive]` values of `b`
make at `lo` and `hi`, lying below the first for `[−additive]`, at or above it for `[+additive]`,
and between the two for both (§3.3). -/
def Bundle.Cut (lo hi : ℕ) (b : Bundle) (k : ℕ) : Prop :=
  ((.additive, true) ∈ b → lo ≤ k) ∧
    ((.additive, false) ∈ b → k < if (.additive, true) ∈ b then hi else lo)

instance (lo hi : ℕ) (b : Bundle) : DecidablePred (b.Cut lo hi) := fun _ ↦ by
  unfold Bundle.Cut; infer_instance

/-- A bundle denotes the elements of its exact region that survive its cuts, graded by `g`. -/
def Bundle.denote {D : Type*} [SemilatticeSup D] (g : D → ℕ) (lo hi : ℕ) (b : Bundle)
    (P : D → Prop) (x : D) : Prop :=
  b.exact P x ∧ b.Cut lo hi (g x)

/-- The cell of a bundle in a setting is its denotation less those of the more specific bundles,
as the plural of Figure 7 is `Q+ \ Q′`. -/
def Setting.cell {D : Type*} [SemilatticeSup D] (σ : Setting) (g : D → ℕ) (lo hi : ℕ)
    (P : D → Prop) (b : Bundle) (x : D) : Prop :=
  b.denote g lo hi P x ∧ ∀ b' ∈ σ.bundles, b ⊂ b' → ¬ b'.denote g lo hi P x

theorem Setting.cell_strata_iff (σ : Setting) (lo hi : ℕ) (s : Strata) (b : Bundle) (k : ℕ) :
    σ.cell id lo hi s.Mem b k ↔ ((b.strata s).Mem k ∧ b.Cut lo hi k) ∧
      ∀ b' ∈ σ.bundles, b ⊂ b' → ¬ ((b'.strata s).Mem k ∧ b'.Cut lo hi k) := by
  simp only [Setting.cell, Bundle.denote, Bundle.exact_mem, id]

instance (σ : Setting) (lo hi : ℕ) (s : Strata) (b : Bundle) :
    DecidablePred (σ.cell id lo hi s.Mem b) := fun k ↦
  decidable_of_iff _ (σ.cell_strata_iff lo hi s b k).symm

/-- `collapse lo hi` keeps the strata up to four and sends those below `lo`, those from `lo` below
`hi`, and those from `hi` up to four, five and six. -/
def collapse (lo hi k : ℕ) : ℕ :=
  if k ≤ 4 then k else if k < lo then 4 else if k < hi then 5 else 6

theorem cut_collapse {lo hi : ℕ} (h : 4 < lo) (b : Bundle) (k : ℕ) :
    b.Cut lo hi k ↔ b.Cut 5 6 (collapse lo hi k) := by
  unfold Bundle.Cut collapse
  by_cases ha : (.additive, true) ∈ b <;> by_cases hb : (.additive, false) ∈ b <;>
    simp only [ha, hb, ite_true, ite_false, forall_const, false_implies, and_true, true_and] <;>
    split_ifs <;> omega

theorem mem_strata_collapse {lo hi p : ℕ} (hp : p ≤ 2) (b : Bundle) (k : ℕ) :
    (b.strata (.ray p)).Mem k ↔ (b.strata (.ray p)).Mem (collapse lo hi k) := by
  have h4 := fun j (hj : 4 ≤ j) ↦ Strata.mem_iff_of_bound_le (bound_strata_le b p hp) hj
  unfold collapse
  split_ifs
  · rfl
  · exact h4 k (by omega)
  · rw [h4 k (by omega), h4 5 (by omega)]
  · rw [h4 k (by omega), h4 6 (by omega)]

theorem cell_collapse {lo hi p : ℕ} (h : 4 < lo) (hp : p ≤ 2) (σ : Setting) (b : Bundle)
    (k : ℕ) :
    σ.cell id lo hi (Strata.ray p).Mem b k ↔
      σ.cell id 5 6 (Strata.ray p).Mem b (collapse lo hi k) := by
  simp only [Setting.cell_strata_iff, mem_strata_collapse hp (lo := lo) (hi := hi) _ k,
    cut_collapse h _ k]

theorem exists_cell_iff {lo hi p : ℕ} (h₁ : 4 < lo) (h₂ : lo < hi) (hp : p ≤ 2) (σ : Setting)
    (b : Bundle) :
    (∃ k, σ.cell id lo hi (Strata.ray p).Mem b k) ↔
      ∃ k, k ≤ 6 ∧ σ.cell id 5 6 (Strata.ray p).Mem b k := by
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
    decide (∃ k : ℕ, k ≤ 6 ∧ σ.cell (D := ℕ) id 5 6 (Strata.ray p).Mem b k)

theorem mem_system {σ : Setting} {p : ℕ} {b : Bundle} :
    b ∈ σ.system p ↔ b ∈ σ.bundles ∧ ∃ k, k ≤ 6 ∧ σ.cell id 5 6 (Strata.ray p).Mem b k := by
  simp [system]

/-- The values of a setting's system are its bundles' labels. -/
def values (σ : Setting) (c : Convention) (p : ℕ) : List Number :=
  (σ.system p).map (Bundle.label c)

/-- A setting's third-person system as a `Number.System` sets general number apart. -/
def toSystem (σ : Setting) (c : Convention) : Number.System where
  values := ((σ.values c 0).filter (· ≠ .general)).toFinset
  hasGeneral := decide (.general ∈ σ.values c 0)

end Setting

section Lattice

variable {α : Type*} [DecidableEq α]

theorem cell_region {B : Finset α} {lo hi : ℕ} (σ : Setting) (b : Bundle) (x : Finset α) :
    σ.cell Finset.card lo hi (region B (Strata.ray B.card).Mem) b x ↔
      B ⊆ x ∧ σ.cell id lo hi (Strata.ray B.card).Mem b x.card := by
  have hs : ∀ k, (Strata.ray B.card).Mem k → B.card ≤ k := fun k hk ↦ le_of_max_le_left hk
  simp only [Setting.cell, Bundle.denote, Bundle.exact_region _ hs, Bundle.exact_mem, region,
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
      (region B (Strata.ray B.card).Mem) b x) = σ.system B.card := by
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
    (hk : max p 1 ≤ k) : ∃ b ∈ σ.bundles, σ.cell id lo hi (Strata.ray p).Mem b k := by
  have ref : ∀ σ : Setting, ∀ p ≤ 2, ∀ j ≤ 6, max p 1 ≤ j →
      ∃ b ∈ σ.bundles, σ.cell (D := ℕ) id 5 6 (Strata.ray p).Mem b j := by
    decide +kernel
  obtain ⟨b, hb, hc⟩ := ref σ p hp (collapse lo hi k) (by unfold collapse; split_ifs <;> omega)
    (by unfold collapse; split_ifs <;> omega)
  exact ⟨b, hb, (cell_collapse h hp σ b k).mpr hc⟩

theorem disjoint_cell {lo hi p : ℕ} (h : 4 < lo) (hp : p ≤ 2) (σ : Setting) {b b' : Bundle}
    (hb : b ∈ σ.bundles) (hb' : b' ∈ σ.bundles) (hne : b ≠ b') :
    Disjoint (σ.cell id lo hi (Strata.ray p).Mem b) (σ.cell id lo hi (Strata.ray p).Mem b') := by
  rw [Pi.disjoint_iff]
  intro k
  rw [Prop.disjoint_iff]
  have ref : ∀ σ : Setting, ∀ p ∈ [0, 1, 2], ∀ b ∈ σ.system p, ∀ b' ∈ σ.system p, b ≠ b' →
      ∀ j ≤ 6, σ.cell (D := ℕ) id 5 6 (Strata.ray p).Mem b j →
        ¬ σ.cell (D := ℕ) id 5 6 (Strata.ray p).Mem b' j := by
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

/-- An implication of Table 1 says that a system with its antecedent has one of its
consequents. -/
structure Implication where
  /-- The number that requires another. -/
  antecedent : Number
  /-- The numbers one of which it requires. -/
  consequents : Finset Number
  deriving DecidableEq

/-- A system satisfies an implication when, with its antecedent, it has one of its
consequents. -/
def Implication.Holds (u : Implication) (s : Finset Number) : Prop :=
  u.antecedent ∈ s → ∃ v ∈ u.consequents, v ∈ s

instance (u : Implication) (s : Finset Number) : Decidable (u.Holds s) := by
  unfold Implication.Holds; infer_instance

/-- Table 1, the implications the features are to derive, in the printed order; its last row,
for the greater and the global plural alike, is two implications. -/
def table1 : List Implication :=
  [⟨.trial, {.dual}⟩, ⟨.dual, {.singular}⟩, ⟨.singular, {.plural}⟩,
    ⟨.plural, {.singular, .minimal}⟩, ⟨.unitAugmented, {.augmented}⟩,
    ⟨.minimal, {.augmented, .plural}⟩, ⟨.augmented, {.minimal}⟩, ⟨.greaterPaucal, {.paucal}⟩,
    ⟨.paucal, {.plural}⟩, ⟨.greaterPlural, {.plural, .augmented}⟩,
    ⟨.globalPlural, {.plural, .augmented}⟩]

/-- A system satisfies Table 1 when it satisfies each of its implications. -/
def SatisfiesTable1 (s : Finset Number) : Prop := ∀ u ∈ table1, u.Holds s

instance (s : Finset Number) : Decidable (SatisfiesTable1 s) := by
  unfold SatisfiesTable1; infer_instance

/-- Every legitimate setting satisfies Table 1 except `{±additive(*), ±minimal*}`, two lacunae of
Table 3 whose unit augmented has no augmented. -/
theorem satisfiesTable1_toSystem_iff : ∀ σ : Setting, ∀ c : Convention, c.Fits σ.additive →
    σ.Legitimate → (SatisfiesTable1 (σ.toSystem c).values ↔
      ¬ (σ.atomic = .inactive ∧ σ.minimal = .recursive ∧ σ.additive ≠ .inactive)) := by
  decide +kernel

-- Table 1 [corbett-2000]
theorem satisfiesTable1_corbett (c : Corbett2000.Choices) : SatisfiesTable1 c.toSystem.values := by
  obtain ⟨⟨d, p, gp⟩, g, f⟩ := c
  change SatisfiesTable1 (Corbett2000.Choices.mk ⟨d, p, gp⟩ .none 0).toSystem.values
  fin_cases d <;> fin_cases p <;> cases gp <;> decide


section Table3

/-- Table 3 pairs each setting and convention with the system of its example language, as
[corbett-2000] records it where it does, or of a lacuna; Banyun's row is left out. -/
def table3 : List (Setting × Convention × Finset Number) :=
  [(⟨.inactive, .inactive, .inactive⟩, .none, Corbett2000.piraha.values),
   (⟨.active, .inactive, .inactive⟩, .none, {.singular, .plural}),  -- Svan
   (⟨.inactive, .active, .inactive⟩, .none, {.minimal, .augmented}),  -- Winnebago
   (⟨.inactive, .recursive, .inactive⟩, .none, Corbett2000.rembarrnga.values),
   (⟨.active, .active, .inactive⟩, .none, {.singular, .dual, .plural}),  -- Kiowa
   (⟨.active, .inactive, .active⟩, .one .low, Corbett2000.bayso.toSystem.values),
   (⟨.active, .inactive, .active⟩, .one .high, {.singular, .plural, .greaterPlural}),  -- Fula
   (⟨.inactive, .active, .active⟩, .one .low, {.minimal, .paucal, .plural}),  -- Mebengokre
   (⟨.active, .recursive, .inactive⟩, .none, Corbett2000.larike.toSystem.values),
   (⟨.inactive, .recursive, .active⟩, .one .low, {.minimal, .unitAugmented, .paucal, .plural}),
   (⟨.inactive, .active, .recursive⟩, .two .low, {.minimal, .paucal, .greaterPaucal, .plural}),
   (⟨.inactive, .recursive, .recursive⟩, .two .low,
     {.minimal, .unitAugmented, .paucal, .greaterPaucal, .plural}),
   (⟨.active, .active, .active⟩, .one .low, Corbett2000.yimas.toSystem.values),
   (⟨.active, .active, .active⟩, .one .high, Corbett2000.mokilese.toSystem.values),
   (⟨.active, .recursive, .active⟩, .one .low, Corbett2000.marshallese.toSystem.values),
   (⟨.active, .active, .recursive⟩, .two .low, Corbett2000.sursurunga.toSystem.values),
   (⟨.active, .active, .recursive⟩, .two .high, Corbett2000.meleFila.toSystem.values),
   (⟨.active, .recursive, .recursive⟩, .two .low,
     {.singular, .dual, .trial, .paucal, .greaterPaucal, .plural})]

-- The rows carry `Finset Number`, itself finite, so `decide` would otherwise range over every
-- triple rather than the eighteen rows.
attribute [local instance high] List.decidableBAll

/-- Every row of Table 3 is generated. -/
theorem table3_generated : ∀ r ∈ table3, (r.1.toSystem r.2.1).values = r.2.2 := by
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
  v ∈ (p.1.1.toSystem p.1.2).values

/-- A number requires another when its attribute concept lies below the other's, the implication
schema (34). -/
abbrev Requires (b a : Number) : Prop :=
  Concept.ofAttribute Generates b ≤ Concept.ofAttribute Generates a

theorem requires_iff {b a : Number} : Requires b a ↔ ∀ σ : Setting, ∀ c : Convention,
    c.Fits σ.additive → σ.Legitimate → b ∈ (σ.toSystem c).values → a ∈ (σ.toSystem c).values := by
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
      ∀ e ∈ derivedImplications, e.1 ∈ (σ.toSystem c).values → e.2 ∈ (σ.toSystem c).values := by
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
    (hb : b ∈ c.toSystem.values) : a ∈ c.toSystem.values := by
  have key : ∀ b a : Number, (∀ r ∈ table3, b ∈ r.2.2 → a ∈ r.2.2) →
      ∀ s : Corbett2000.Shape, b ∈ s.values → a ∈ s.values := by
    decide +kernel
  simp only [Corbett2000.Choices.toSystem, List.mem_toFinset] at hb ⊢
  exact key b a (fun _ hr ↦ mem_table3_of_requires h hr) c.toShape hb

theorem mem_of_requires_minimalAugmented {b a : Number} (h : Requires b a) :
    ∀ ns ∈ [Corbett2000.piraha, Corbett2000.rembarrnga, Corbett2000.ilocano],
      b ∈ ns.values → a ∈ ns.values := by
  have key : ∀ b a : Number, (∀ r ∈ table3, b ∈ r.2.2 → a ∈ r.2.2) →
      ∀ ns ∈ [Corbett2000.piraha, Corbett2000.rembarrnga, Corbett2000.ilocano],
        b ∈ ns.values → a ∈ ns.values := by
    decide +kernel
  exact key b a fun _ hr ↦ mem_table3_of_requires h hr

end Table3

/-! ### Composed number (§5.2) -/

-- (38), (40), (44), (45)
theorem yimas_system :
    (((⟨.active, .active, .active⟩ : Setting).system 0).map
      fun b ↦ (b.label (.one .low), b)).Perm
    [(.singular, {(.atomic, true), (.minimal, true), (.additive, false)}),
     (.dual, {(.atomic, false), (.minimal, true), (.additive, false)}),
     (.paucal, {(.atomic, false), (.minimal, false), (.additive, false)}),
     (.plural, {(.atomic, false), (.minimal, false), (.additive, true)})] := by
  decide +kernel

/-- Mele-Fila's setting is `{±additive*, ±minimal, ±atomic}`, with a low and a high cut. -/
abbrev meleFila : Setting := ⟨.active, .active, .recursive⟩

-- Table 4
theorem meleFila_system :
    ((meleFila.system 0).map fun b ↦ (b.label (.two .high), b)).Perm
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
    meleFila.cell Finset.card lo hi Finset.Nonempty
      {(.atomic, false), (.minimal, false), (.additive, false), (.additive, true)} x ↔
        lo ≤ x.card ∧ x.card < hi := by
  have ref : ∀ j ≤ 6, meleFila.cell (D := ℕ) id 5 6 (Strata.ray 0).Mem
      {(.atomic, false), (.minimal, false), (.additive, false), (.additive, true)} j ↔ j = 5 := by
    decide +kernel
  have hP : (Finset.Nonempty : Finset α → Prop) =
      region ∅ (Strata.ray (∅ : Finset α).card).Mem := by
    ext t; simp [region, Strata.Mem, Finset.one_le_card]
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

end Harbour2014

end
