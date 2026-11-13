module

public import Mathlib.Data.Set.Card
public import Mathlib.Order.Setoid.Partition
public import Linglib.Semantics.Degree.CresswellDegree
public import Linglib.Semantics.Reference.Iota

/-!
# Mendia (2020): Reference to ad hoc kinds

A kind-referring expression ranges over subkinds that share no realizations and jointly cover the
kind, Carlson's Disjointness Condition. Mendia restates the condition as a partition, so that the
subkinds are [the cells of an equivalence relation](##cover_and_noOverlap_iff_exists_classes) on
the realizations of the kind, which the context supplies. An ad hoc kind term such as *the lions
that eat people* is the definite over κ+, the cells that contain every instance of the restrictor.
It is [defined when any two instances are equivalent](##iota_kappaPlus_dom), it refers to the
instances themselves [when they are a cell](##self_mem_iota_kappaPlus_iff), and the coarsest
partition under which it does [divides the kind into the instances and the
rest](##isGreatest_ker_mem). Degrees are cells too, of mutual comparison on a preorder, so an
[amount reading](##amount_reading) of a relative clause is the same definite under the partition
into degrees.

## Implementation notes

* The model is extensional. The type `E` collects the realizations of the kind under
  discussion, a salient kind formation is a `Setoid E`, the partition Π of (28) is its
  `Setoid.classes`, and a subkind is identified with its cell, as the paper does for its tables
  (p. 616: the members of a partition "are always objects, not kinds").
* The definite of (36) picks the largest member of a set. The cells of a partition are an
  antichain, so the largest member is the only member (`iota_isGreatest_kappaPlus`) and the ι of
  (31) and (36) is `iota`, undefined when no cell or several qualify.
* κ+ in (33) asks that the cell contain the instances of the restrictor, and the second line of
  (36) names the instances themselves as the referent. The two agree when the instances are a
  cell. In the champagne partitions (64)–(66) the restrictor holds the one portion spilled and
  the referent is the whole cell of that portion.
* Dogs come in every combination of breed and role and lions in every combination of subspecies
  and diet, so there are people-eating lions of both subspecies. The restrictor *lions that eat
  people* is read as footnote 11's *lions that eat only people*, a value of the diet.

## TODO

* The partition of pluralities by cardinality (62)–(63), the distribution of ad hoc kind terms
  (§3.3), the singular–plural contrast (§3.4), and the amount readings without degrees of §5.

## References

* [mendia-2020]
* [carlson-1977a]
* [cresswell-1976]
-/

@[expose] public section

namespace Mendia2020

variable {E : Type*}

/-! ### Partitions and the Disjointness Condition (§3.1) -/

-- (16), (28)
theorem cover_and_noOverlap_iff {c : Set (Set E)} :
    ((∀ x, ∃ y ∈ c, x ∈ y) ∧ ∀ x, ∀ y ∈ c, x ∈ y → ¬ ∃ z ∈ c, y ≠ z ∧ x ∈ z) ↔
      ∀ x, ∃! y ∈ c, x ∈ y := by
  refine ⟨fun ⟨hc, hn⟩ x ↦ ?_, fun h ↦ ⟨fun x ↦ (h x).exists, fun x y hy hx ⟨z, hz, hne, hxz⟩ ↦
    hne ((h x).unique ⟨hy, hx⟩ ⟨hz, hxz⟩)⟩⟩
  obtain ⟨y, hy, hx⟩ := hc x
  exact ⟨y, ⟨hy, hx⟩, fun z ⟨hz, hxz⟩ ↦ by_contra fun hne ↦ hn x y hy hx ⟨z, hz, Ne.symm hne, hxz⟩⟩

/-- The families of nonempty sets that meet Cover and No overlap are the families of cells of an
equivalence relation ((28), p. 597). -/
theorem cover_and_noOverlap_iff_exists_classes {c : Set (Set E)} (h0 : ∅ ∉ c) :
    ((∀ x, ∃ y ∈ c, x ∈ y) ∧ ∀ x, ∀ y ∈ c, x ∈ y → ¬ ∃ z ∈ c, y ≠ z ∧ x ∈ z) ↔
      ∃ s : Setoid E, s.classes = c :=
  cover_and_noOverlap_iff.trans
    ⟨fun h ↦ ⟨_, Setoid.classes_mkClasses c ⟨h0, h⟩⟩, fun ⟨_, h⟩ ↦ h ▸ Setoid.classes_eqv_classes⟩

/-- The subkinds of a family realized among the individuals `X`, those that *n kinds of dog are
in the next room* counts. -/
def realized (c : Set (Set E)) (X : Set E) : Set (Set E) := {y ∈ c | (y ∩ X).Nonempty}

theorem realized_classes (s : Setoid E) (X : Set E) :
    realized s.classes X = (fun x ↦ {z | s z x}) '' X := by
  ext y
  refine ⟨?_, fun ⟨x, hx, hy⟩ ↦ hy ▸ ⟨s.mem_classes x, x, s.refl' x, hx⟩⟩
  rintro ⟨⟨a, rfl⟩, x, hxa, hx⟩
  exact ⟨x, hx, Set.ext fun z ↦ ⟨(s.trans' · hxa), (s.trans' · (s.symm' hxa))⟩⟩

theorem ncard_realized_classes_le (s : Setoid E) {X : Set E} (hX : X.Finite) :
    (realized s.classes X).ncard ≤ X.ncard := by
  rw [realized_classes]
  exact Set.ncard_image_le hX

-- (14b), `mendia2020_14b`
theorem ncard_realized_classes_singleton (s : Setoid E) (a : E) :
    (realized s.classes {a}).ncard = 1 := by
  rw [realized_classes, Set.image_singleton, Set.ncard_singleton]

/-! ### Fido, (14) -/

/-- Breeds of dog. -/
inductive Breed
  | borderCollie | bulldog | beagle

/-- Roles of dog. -/
inductive Role
  | watchDog | guideDog

/-- A dog has a breed, a role, and an index telling apart dogs alike in both. -/
structure Dog where
  breed : Breed
  role : Role
  idx : ℕ

/-- Fido, a border collie and a watch-dog, (14b). -/
def fido : Dog := ⟨.borderCollie, .watchDog, 0⟩

/-- The border collies. -/
def borderCollies : Set Dog := {d | d.breed = .borderCollie}

/-- The watch-dogs. -/
def watchDogs : Set Dog := {d | d.role = .watchDog}

private theorem borderCollies_ne_watchDogs : borderCollies ≠ watchDogs := fun h ↦ by
  have : (⟨.borderCollie, .guideDog, 0⟩ : Dog) ∈ watchDogs := h ▸ rfl
  simp [watchDogs] at this

-- (14), (14b)
theorem ncard_realized_borderCollies_watchDogs :
    (realized {borderCollies, watchDogs} {fido}).ncard = 2 := by
  have : realized {borderCollies, watchDogs} {fido} = {borderCollies, watchDogs} := by
    refine Set.sep_eq_self_iff_mem_true.2 ?_
    rintro y (rfl | rfl) <;> exact ⟨fido, rfl, rfl⟩
  rw [this, Set.ncard_pair borderCollies_ne_watchDogs]

-- (14b)
theorem not_partition_borderCollies_watchDogs :
    ¬ ∀ x, ∃! y ∈ ({borderCollies, watchDogs} : Set (Set Dog)), x ∈ y := fun h ↦
  borderCollies_ne_watchDogs ((h fido).unique ⟨by simp, rfl⟩ ⟨by simp, rfl⟩)

/-- The dogs of (14a) are three bulldogs and two beagles. -/
def room14a : Set Dog :=
  {⟨.bulldog, .guideDog, 0⟩, ⟨.bulldog, .guideDog, 1⟩, ⟨.bulldog, .guideDog, 2⟩,
    ⟨.beagle, .guideDog, 0⟩, ⟨.beagle, .guideDog, 1⟩}

-- (14a), `mendia2020_14a`
theorem ncard_realized_room14a : (realized (Setoid.ker Dog.breed).classes room14a).ncard = 2 := by
  have hne : {z : Dog | z.breed = .bulldog} ≠ {z | z.breed = .beagle} := fun h ↦ by
    have : (⟨.bulldog, .guideDog, 0⟩ : Dog) ∈ {z : Dog | z.breed = .beagle} := h ▸ rfl
    simp at this
  rw [realized_classes]
  simp only [room14a, Set.image_insert_eq, Set.image_singleton, Setoid.ker_def]
  simp only [Set.insert_eq_of_mem, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
  exact Set.ncard_pair hne

/-! ### Subkind reference (§3.2.2) -/

theorem isAntichain_classes (s : Setoid E) : IsAntichain (· ≤ ·) s.classes :=
  fun _ hb _ hb' hne hle ↦
    let ⟨_, hx⟩ := Setoid.nonempty_of_mem_partition s.isPartition_classes hb
    hne (Setoid.eq_of_mem_classes hb hx hb' (hle hx))

/-- The operator κ+ gives the cells of the partition that contain every instance of the
restrictor `P`, (33). -/
def kappaPlus (s : Setoid E) (P : Set E) : Set (Set E) := {y ∈ s.classes | P ⊆ y}

variable {s : Setoid E} {P c : Set E} {a b : E}

-- footnote 9
@[simp] theorem kappaPlus_empty (s : Setoid E) : kappaPlus s ∅ = s.classes := by
  simp [kappaPlus]

-- (31b), footnote 9
@[simp] theorem kappaPlus_singleton (s : Setoid E) (a : E) :
    kappaPlus s {a} = {y ∈ s.classes | a ∈ y} := by
  simp [kappaPlus]

theorem kappaPlus_subsingleton (s : Setoid E) (hP : P.Nonempty) : (kappaPlus s P).Subsingleton :=
  fun _ ⟨hy, hPy⟩ _ ⟨hz, hPz⟩ ↦
    let ⟨_, ha⟩ := hP
    Setoid.eq_of_mem_classes hy (hPy ha) hz (hPz ha)

theorem mem_iota_kappaPlus (hP : P.Nonempty) : c ∈ iota (kappaPlus s P) ↔ c ∈ s.classes ∧ P ⊆ c :=
  (kappaPlus_subsingleton s hP).mem_iota

/-- The definite over κ+ of a nonempty restrictor is defined exactly when any two instances of
the restrictor are equivalent (p. 604). -/
theorem iota_kappaPlus_dom (hP : P.Nonempty) :
    (iota (kappaPlus s P)).Dom ↔ ∀ x ∈ P, ∀ y ∈ P, s x y := by
  rw [(kappaPlus_subsingleton s hP).iota_dom]
  refine ⟨fun ⟨_, hy, hPy⟩ x hx y hy' ↦ s.rel_iff_exists_classes.2 ⟨_, hy, hPy hx, hPy hy'⟩,
    fun h ↦ ?_⟩
  obtain ⟨a, ha⟩ := hP
  exact ⟨_, s.mem_classes a, fun x hx ↦ h x hx a ha⟩

/-- The definite over κ+ refers to the instances of the restrictor themselves exactly when they
are a cell of the partition, (36). -/
theorem self_mem_iota_kappaPlus_iff : P ∈ iota (kappaPlus s P) ↔ P ∈ s.classes :=
  ⟨fun h ↦ (mem_iota.1 h).1.1, fun h ↦
    (mem_iota_kappaPlus (Setoid.nonempty_of_mem_partition s.isPartition_classes h)).2
      ⟨h, subset_rfl⟩⟩

-- The definite picks the largest member (p. 604), which among cells is the only member.
theorem iota_isGreatest_kappaPlus (s : Setoid E) (P : Set E) :
    iota {y | IsGreatest (kappaPlus s P) y} = iota (kappaPlus s P) :=
  ((isAntichain_classes s).subset (Set.sep_subset _ _)).iota_isGreatest

-- (31b), `mendia2020_32a`
theorem that_eq (s : Setoid E) (a : E) : {x | s x a} ∈ iota {y ∈ s.classes | a ∈ y} :=
  kappaPlus_singleton s a ▸ (mem_iota_kappaPlus (Set.singleton_nonempty a)).2
    ⟨s.mem_classes a, Set.singleton_subset_iff.2 (s.refl' a)⟩

-- (32b), `mendia2020_32b`
theorem the_kind_eq_none (s : Setoid E) (h : ¬ s a b) : iota s.classes = Part.none :=
  iota_eq_none_of_ne (s.mem_classes a) (s.mem_classes b) fun hab ↦
    h (hab ▸ s.refl' a : a ∈ {x | s x b})

-- p. 604
theorem the_kappaPlus_eq_none (ha : a ∈ P) (hb : b ∈ P) (h : ¬ s a b) :
    iota (kappaPlus s P) = Part.none :=
  Part.eq_none_iff'.2 fun hd ↦ h ((iota_kappaPlus_dom ⟨a, ha⟩).1 hd a ha b hb)

-- (36), (37), footnote 11
theorem the_kappaPlus_ker {β : Type*} (f : E → β) (a : E) :
    (f ⁻¹' {f a}) ∈ iota (kappaPlus (Setoid.ker f) (f ⁻¹' {f a})) :=
  self_mem_iota_kappaPlus_iff.2 ⟨a, rfl⟩

/-! ### The bipartition (§3.1.2) -/

theorem mem_classes_ker_mem (hP : P.Nonempty) : P ∈ (Setoid.ker (· ∈ P)).classes :=
  let ⟨a, ha⟩ := hP
  ⟨a, Set.ext fun _ ↦ ⟨fun hx ↦ (eq_true hx).trans (eq_true ha).symm, fun hx ↦ hx.mpr ha⟩⟩

/-- A nonempty restrictor is a cell of the partition into its instances and everything else,
the coarsest partition under which the definite over κ+ refers to it (p. 598). -/
theorem isGreatest_ker_mem (hP : P.Nonempty) :
    IsGreatest {s : Setoid E | P ∈ iota (kappaPlus s P)} (Setoid.ker (· ∈ P)) := by
  refine ⟨self_mem_iota_kappaPlus_iff.2 (mem_classes_ker_mem hP), fun s hs x y hxy ↦ ?_⟩
  obtain ⟨z, rfl⟩ := self_mem_iota_kappaPlus_iff.1 hs
  exact propext ⟨fun hx ↦ s.trans' (s.symm' hxy) hx, fun hy ↦ s.trans' hxy hy⟩

/-- Subspecies of lion. -/
inductive Subspecies
  | african | asiatic

/-- What a lion eats, read as footnote 11 requires, is only people, only zebras, or only
carrion. -/
inductive Diet
  | people | zebras | carrion

/-- A lion has a subspecies, a diet, and an index telling apart lions alike in both. -/
structure Lion where
  subspecies : Subspecies
  diet : Diet
  idx : ℕ

/-- *Lions that eat people*, (21b), sharpened as footnote 11 requires. -/
def eatPeople : Set Lion := Lion.diet ⁻¹' {.people}

-- p. 604
theorem the_kappaPlus_subspecies :
    iota (kappaPlus (Setoid.ker Lion.subspecies) eatPeople) = Part.none :=
  the_kappaPlus_eq_none (a := ⟨.african, .people, 0⟩) (b := ⟨.asiatic, .people, 0⟩) rfl rfl
    (by simp [Setoid.ker_def])

-- (37)
theorem the_kappaPlus_diet :
    eatPeople ∈ iota (kappaPlus (Setoid.ker Lion.diet) eatPeople) :=
  the_kappaPlus_ker Lion.diet ⟨.african, .people, 0⟩

/-! ### Amounts (§4.3) -/

section Amounts

variable {P : Set E} {a : E}

/-- Under the partition of a preorder into its degrees, the definite over κ+ refers to the
individuals exactly as A as the instances of the restrictor, (57)–(59). -/
theorem amount_reading [Preorder E] (ha : a ∈ P) (hP : ∀ x ∈ P, AntisymmRel (· ≤ ·) x a) :
    {y | AntisymmRel (· ≤ ·) y a} ∈ iota (kappaPlus (cresswellSetoid (· ≤ · : E → E → Prop)) P) :=
  cresswellSetoid_eq_antisymmRel (· ≤ · : E → E → Prop) ▸
    (mem_iota_kappaPlus ⟨a, ha⟩).2 ⟨(AntisymmRel.setoid E (· ≤ ·)).mem_classes a, hP⟩

-- (65), (66)
theorem the_kappaPlus_measure {D : Type*} [LinearOrder D] (μ : E → D) (ha : a ∈ P)
    (hP : ∀ x ∈ P, μ x = μ a) :
    μ ⁻¹' {μ a} ∈ iota (kappaPlus (cresswellSetoid fun x y ↦ μ y ≤ μ x) P) :=
  cresswellSetoid_le_measure μ ▸ (mem_iota_kappaPlus ⟨a, ha⟩).2 ⟨⟨a, rfl⟩, hP⟩

end Amounts

/-- Taxonomic kinds of champagne, (64). -/
inductive Cuvee
  | prestige | blancDeNoirs | blancDeBlancs | rose

/-- A portion of champagne has a taxonomic kind, a volume in litres, a sweetness in grams of
sugar per litre, and an index telling apart portions alike in all three. -/
structure Champagne where
  cuvee : Cuvee
  litres : ℕ
  sugar : ℕ
  idx : ℕ

/-- The champagne they spilled that evening, (48a): ten litres of a prestige cuvée with 21 grams
of sugar per litre. -/
def spilled : Champagne := ⟨.prestige, 10, 21, 0⟩

-- (64)
theorem the_spilled_cuvee :
    Champagne.cuvee ⁻¹' {.prestige} ∈ iota (kappaPlus (Setoid.ker Champagne.cuvee) {spilled}) :=
  (mem_iota_kappaPlus (Set.singleton_nonempty _)).2
    ⟨⟨spilled, rfl⟩, Set.singleton_subset_iff.2 rfl⟩

-- (65)
theorem the_spilled_litres :
    Champagne.litres ⁻¹' {10} ∈
      iota (kappaPlus (cresswellSetoid fun x y : Champagne ↦ y.litres ≤ x.litres) {spilled}) :=
  the_kappaPlus_measure Champagne.litres (Set.mem_singleton spilled) fun _ h ↦
    congrArg Champagne.litres (Set.mem_singleton_iff.1 h)

-- (66)
theorem the_spilled_sugar :
    Champagne.sugar ⁻¹' {21} ∈
      iota (kappaPlus (cresswellSetoid fun x y : Champagne ↦ y.sugar ≤ x.sugar) {spilled}) :=
  the_kappaPlus_measure Champagne.sugar (Set.mem_singleton spilled) fun _ h ↦
    congrArg Champagne.sugar (Set.mem_singleton_iff.1 h)

end Mendia2020
