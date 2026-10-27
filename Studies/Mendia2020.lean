module

public import Mathlib.Data.Set.Card
public import Mathlib.Order.Setoid.Partition
public import Linglib.Semantics.Degree.Quotient
public import Linglib.Semantics.Reference.Iota

/-!
# Mendia (2020): Reference to ad hoc kinds

Mendia analyzes kind reference through partitions. Carlson's Disjointness Condition, that a
kind-referring expression ranges over subkinds sharing no realizations and jointly covering the
kind, becomes the requirement that kind reference go through a partition of the kind's
realizations into the cells of a contextually salient equivalence relation. Subkinds are referred
to through the ι of the cells, and an ad hoc kind term such as *the lions that eat people* is the
ι of κ+, the cells that contain every instance of the restrictor. Mendia's indistinguishability
relation is Cresswell's degree construction, so an amount reading of a relative clause is the
same definite under the partition of a preorder into its degrees.

## Implementation notes

* The model is extensional. The type `E` collects the realizations of the kind under
  discussion, a salient kind formation is a `Setoid E`, the partition Π of (28) is its
  `Setoid.classes`, and a subkind is identified with its cell, as the paper does for its tables
  (p. 616: the members of a partition "are always objects, not kinds").
* (28b) as printed binds `y_k` in the antecedent and uses it in the consequent; it is read with
  `y_k` bound outside the implication. (33) prints `Π(x_y)` for `Π(x_k)`.
* The ι of (31) and (36) is `iota`, undefined when no cell or several qualify.
* Dogs come in every combination of breed and role and lions in every combination of subspecies
  and diet, so there are people-eating lions of both subspecies. The restrictor *lions that eat
  people* is read as footnote 11's *lions that eat only people*, a value of the diet.

## TODO

* The champagne partitions (64)–(66) of §4.3.2, the distribution of ad hoc kind terms (§3.3),
  the singular–plural contrast (§3.4), and the amount readings without degrees of §5.

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

/-- The subkinds of a family realized among the individuals `X`, those that *n kinds of dog are
in the next room* counts. -/
def realized (c : Set (Set E)) (X : Set E) : Set (Set E) := {y ∈ c | (y ∩ X).Nonempty}

theorem realized_classes (s : Setoid E) (X : Set E) :
    realized s.classes X = (fun x ↦ {z | s z x}) '' X := by
  ext y
  refine ⟨?_, fun ⟨x, hx, hy⟩ ↦ hy ▸ ⟨s.mem_classes x, x, s.refl' x, hx⟩⟩
  rintro ⟨⟨a, rfl⟩, x, hxa, hx⟩
  exact ⟨x, hx, Set.ext fun z ↦ ⟨(s.trans' · hxa), (s.trans' · (s.symm' hxa))⟩⟩

/-- Under any salient partition (14), finitely many individuals realize at most as many
subkinds as there are individuals. -/
theorem ncard_realized_classes_le (s : Setoid E) {X : Set E} (hX : X.Finite) :
    (realized s.classes X).ncard ≤ X.ncard := by
  rw [realized_classes]
  exact Set.ncard_image_le hX

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

-- (14b)
theorem ncard_realized_fido_le (s : Setoid Dog) : (realized s.classes {fido}).ncard ≤ 1 :=
  (ncard_realized_classes_le s (Set.finite_singleton fido)).trans (Set.ncard_singleton fido).le

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

-- (14a), (14)
theorem ncard_realized_room14a : (realized (Setoid.ker Dog.breed).classes room14a).ncard = 2 := by
  have hne : {z : Dog | z.breed = .bulldog} ≠ {z | z.breed = .beagle} := fun h ↦ by
    have : (⟨.bulldog, .guideDog, 0⟩ : Dog) ∈ {z : Dog | z.breed = .beagle} := h ▸ rfl
    simp at this
  rw [realized_classes]
  simp only [room14a, Set.image_insert_eq, Set.image_singleton, Setoid.ker_def]
  simp only [Set.insert_eq_of_mem, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
  exact Set.ncard_pair hne

/-! ### Subkind reference (§3.2.2) -/

-- (31b)
theorem that_eq (s : Setoid E) (a : E) :
    iota (fun y ↦ y ∈ s.classes ∧ a ∈ y) = some {x | s x a} :=
  (iota_eq_some_iff _).2 ⟨⟨s.mem_classes a, s.refl' a⟩,
    fun _ hy ↦ (Setoid.classes_eqv_classes a).unique hy ⟨s.mem_classes a, s.refl' a⟩⟩

-- (32b)
theorem the_kind_eq_none (s : Setoid E) {a b : E} (h : ¬ s a b) :
    iota (· ∈ s.classes) = none :=
  (iota_eq_none_iff _).2 fun ⟨y, hy, hu⟩ ↦ h <| s.rel_iff_exists_classes.2
    ⟨y, hy, hu _ (s.mem_classes a) ▸ s.refl' a, hu _ (s.mem_classes b) ▸ s.refl' b⟩

/-- The operator κ+ (33) gives the cells of the partition that contain every instance of the
restrictor `P`. -/
def kappaPlus (s : Setoid E) (P : Set E) : Set (Set E) := {y ∈ s.classes | P ⊆ y}

-- footnote 9
@[simp] theorem kappaPlus_empty (s : Setoid E) : kappaPlus s ∅ = s.classes := by
  simp [kappaPlus]

-- (31b), footnote 9
@[simp] theorem kappaPlus_singleton (s : Setoid E) (a : E) :
    kappaPlus s {a} = {y ∈ s.classes | a ∈ y} := by
  simp [kappaPlus]

/-- When every instance of the restrictor shares the cell of `a ∈ P`, the definite over
κ+ refers to that cell (36). -/
theorem the_kappaPlus_eq_some (s : Setoid E) {P : Set E} {a : E} (ha : a ∈ P)
    (hP : ∀ x ∈ P, s x a) : iota (· ∈ kappaPlus s P) = some {x | s x a} :=
  (iota_eq_some_iff _).2 ⟨⟨s.mem_classes a, hP⟩, fun _ ⟨hy, hPy⟩ ↦
    Setoid.eq_of_mem_classes hy (hPy ha) (s.mem_classes a) (s.refl' a)⟩

/-- When two instances of the restrictor lie in different cells, no cell contains them both and
the definite fails (p. 604). -/
theorem the_kappaPlus_eq_none (s : Setoid E) {P : Set E} {a b : E} (ha : a ∈ P) (hb : b ∈ P)
    (h : ¬ s a b) : iota (· ∈ kappaPlus s P) = none :=
  (iota_eq_none_iff _).2 fun ⟨y, ⟨hy, hPy⟩, _⟩ ↦
    h (s.rel_iff_exists_classes.2 ⟨y, hy, hPy ha, hPy hb⟩)

-- (36), (37), footnote 11
theorem the_kappaPlus_ker {β : Type*} (f : E → β) (a : E) :
    iota (· ∈ kappaPlus (Setoid.ker f) (f ⁻¹' {f a})) = some (f ⁻¹' {f a}) :=
  the_kappaPlus_eq_some _ rfl fun _ h ↦ h

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
    iota (· ∈ kappaPlus (Setoid.ker Lion.subspecies) eatPeople) = none :=
  the_kappaPlus_eq_none _ (a := ⟨.african, .people, 0⟩) (b := ⟨.asiatic, .people, 0⟩) rfl rfl
    (by simp [Setoid.ker_def])

-- (37)
theorem the_kappaPlus_diet :
    iota (· ∈ kappaPlus (Setoid.ker Lion.diet) eatPeople) = some eatPeople :=
  the_kappaPlus_ker Lion.diet ⟨.african, .people, 0⟩

/-! ### Amounts (§4.3) -/

/-- Under the partition of a preorder into degrees, the definite over κ+ refers to the individuals
exactly as A as `a` ((57)–(59), §4.3, p. 617). -/
theorem amount_reading [Preorder E] {P : Set E} {a : E} (ha : a ∈ P)
    (hP : ∀ x ∈ P, AntisymmRel (· ≤ ·) x a) :
    iota (· ∈ kappaPlus (Degree.cresswellSetoid (· ≤ ·)) P) =
      some {y | AntisymmRel (· ≤ ·) a y} := by
  simp_rw [← Degree.cresswellSetoid_le_iff] at hP
  rw [the_kappaPlus_eq_some _ ha hP]
  exact congrArg some (Set.ext fun y ↦ (Degree.cresswellSetoid_le_iff y a).trans antisymmRel_comm)

end Mendia2020
