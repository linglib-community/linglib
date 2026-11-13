module

public import Mathlib.Data.Set.Card
public import Mathlib.Order.Setoid.Partition
public import Linglib.Semantics.Degree.CresswellDegree
public import Linglib.Semantics.Questions.Partition.Basic
public import Linglib.Semantics.Reference.Iota

/-!
# Mendia (2020): Reference to ad hoc kinds

A kind-referring expression ranges over subkinds that share no realizations and jointly cover the
kind, Carlson's Disjointness Condition. Mendia restates the condition as a partition: the subkinds
are [the cells of an equivalence relation](##cover_and_noOverlap_iff_exists_classes) on the
realizations of the kind, which the context supplies. An ad hoc kind term such as *the lions that
eat people* is [the definite of the subkinds its instances realize](##iota_kappaPlus). Its referent
is realized by exactly the instances [when they are also a union of
cells](##cell_eq_iff_mem_iota_kappaPlus), and the coarsest partition under which that holds [divides
the kind into the instances and the rest](##isGreatest_polar). Degrees are subkinds too, the classes
of mutual comparison on a preorder, so an [amount reading](##amount_reading) of a relative clause is
the same definite under the partition into degrees.

## Implementation notes

* The model is extensional. The type `E` collects the realizations of the kind under
  discussion, a salient kind formation is a `Setoid E`, a subkind is a member of its quotient,
  and the realizations of the subkind of `a` are `Setoid.cell`, a member of the partition Π of
  (28), whose members the paper says "are always objects, not kinds" (p. 616). A kind formation
  is the same object as a partition question, the partition with the instances as one cell is
  the polar question `Setoid.polar`, and a restrictor that is a union of cells is one the
  partition determines, `Setoid.Determines`.
* The definite of (36) picks the largest member of a set. The subkinds of one partition are not
  ordered and at most one is realized by every instance of a nonempty restrictor
  (`kappaPlus_subsingleton`), so the ι of (31) and (36) is `iota`, undefined when no subkind or
  several qualify.
* κ+ in (33) collects the subkinds that every instance of the restrictor realizes. For a
  nonempty restrictor its definite is the definite of the image of the restrictor under
  `Quotient.mk`; on the empty restrictor κ+ is every subkind, the reading of (32b), where the
  image is empty.
* κ+ in (33) asks that every instance of the restrictor realize the subkind, and the second line
  of (36) names the instances themselves as its realizations. `cell_eq_iff_mem_iota_kappaPlus`
  says when the two
  agree. In the champagne partitions (64)–(66) the restrictor holds the one portion spilled and
  the referent is realized by the whole cell of that portion.
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

variable {E : Type*} {s : Setoid E} {P : Set E} {a b : E}

/-! ### Partitions and the Disjointness Condition (§3.1) -/

/-- Every realization of the kind instantiates a member of the family `c`, (28a). -/
def Cover (c : Set (Set E)) : Prop := ∀ x, ∃ y ∈ c, x ∈ y

/-- No realization of the kind instantiates two members of the family `c`, (28b). -/
def NoOverlap (c : Set (Set E)) : Prop := ∀ x, ∀ y ∈ c, x ∈ y → ¬ ∃ z ∈ c, y ≠ z ∧ x ∈ z

-- (16), (28)
theorem cover_and_noOverlap_iff {c : Set (Set E)} :
    Cover c ∧ NoOverlap c ↔ ∀ x, ∃! y ∈ c, x ∈ y := by
  refine ⟨fun ⟨hc, hn⟩ x ↦ ?_, fun h ↦ ⟨fun x ↦ (h x).exists, fun x y hy hx ⟨z, hz, hne, hxz⟩ ↦
    hne ((h x).unique ⟨hy, hx⟩ ⟨hz, hxz⟩)⟩⟩
  obtain ⟨y, hy, hx⟩ := hc x
  exact ⟨y, ⟨hy, hx⟩, fun z ⟨hz, hxz⟩ ↦ by_contra fun hne ↦ hn x y hy hx ⟨z, hz, Ne.symm hne, hxz⟩⟩

/-- The families of nonempty sets that meet Cover and No overlap are the families of cells of an
equivalence relation ((28), p. 597). -/
theorem cover_and_noOverlap_iff_exists_classes {c : Set (Set E)} (h0 : ∅ ∉ c) :
    Cover c ∧ NoOverlap c ↔ ∃ s : Setoid E, s.classes = c :=
  cover_and_noOverlap_iff.trans
    ⟨fun h ↦ ⟨_, Setoid.classes_mkClasses c ⟨h0, h⟩⟩, fun ⟨_, h⟩ ↦ h ▸ Setoid.classes_eqv_classes⟩

/-! ### Subkind reference (§3.2.2) -/

/-- The operator κ+ gives the subkinds that every instance of the restrictor `P` realizes,
(33). -/
def kappaPlus (s : Setoid E) (P : Set E) : Set (Quotient s) := {q | ∀ x ∈ P, Quotient.mk s x = q}

-- footnote 9
@[simp] theorem kappaPlus_empty (s : Setoid E) : kappaPlus s ∅ = Set.univ :=
  Set.eq_univ_of_forall fun _ _ h ↦ h.elim

-- (31b), footnote 9
@[simp] theorem kappaPlus_singleton (s : Setoid E) (a : E) :
    kappaPlus s {a} = {Quotient.mk s a} := by
  ext q
  simp [kappaPlus, eq_comm]

theorem kappaPlus_subsingleton (s : Setoid E) (hP : P.Nonempty) : (kappaPlus s P).Subsingleton :=
  fun _ hq _ hq' ↦
    let ⟨a, ha⟩ := hP
    (hq a ha).symm.trans (hq' a ha)

/-- The definite over κ+ of a nonempty restrictor is the definite of the subkinds its instances
realize, (33) and (36). -/
theorem iota_kappaPlus (hP : P.Nonempty) : iota (kappaPlus s P) = iota (Quotient.mk s '' P) := by
  obtain ⟨a, ha⟩ := hP
  refine Part.ext fun q ↦ ?_
  rw [(kappaPlus_subsingleton s ⟨a, ha⟩).mem_iota, mem_iota]
  exact ⟨fun h ↦ ⟨⟨a, ha, h a ha⟩, by rintro _ ⟨x, hx, rfl⟩; exact h x hx⟩,
    fun h x hx ↦ h.2 _ ⟨x, hx, rfl⟩⟩

theorem mk_mem_iota_kappaPlus (ha : a ∈ P) :
    Quotient.mk s a ∈ iota (kappaPlus s P) ↔ P ⊆ s.cell a := by
  rw [iota_kappaPlus ⟨a, ha⟩, apply_mem_iota_image ha]
  exact forall₂_congr fun _ _ ↦ Quotient.eq

-- p. 604
theorem iota_kappaPlus_dom (hP : P.Nonempty) :
    (iota (kappaPlus s P)).Dom ↔ ∀ x ∈ P, ∀ y ∈ P, s x y := by
  rw [iota_kappaPlus hP, iota_image_dom, and_iff_right hP]
  exact forall₂_congr fun _ _ ↦ forall₂_congr fun _ _ ↦ Quotient.eq

/-- The subkind the definite over κ+ refers to is realized by exactly the instances of the
restrictor when the definite is defined and the instances are a union of cells, (36). -/
theorem cell_eq_iff_mem_iota_kappaPlus (ha : a ∈ P) :
    s.cell a = P ↔ Quotient.mk s a ∈ iota (kappaPlus s P) ∧ s.Determines P := by
  rw [mk_mem_iota_kappaPlus ha, Setoid.cell_eq_iff ha]

/-- The coarsest partition under which the definite over κ+ refers to a subkind realized by
exactly the instances of the restrictor has the instances as one cell and everything else as
the other (p. 598). -/
theorem isGreatest_polar (ha : a ∈ P) :
    IsGreatest {s : Setoid E | Quotient.mk s a ∈ iota (kappaPlus s P) ∧ s.Determines P}
      (.polar P) := by
  simp_rw [← cell_eq_iff_mem_iota_kappaPlus ha]
  exact Setoid.isGreatest_polar ha

-- (31b), `mendia2020_32a`
theorem that_eq (s : Setoid E) (a : E) : iota (kappaPlus s {a}) = Part.some (Quotient.mk s a) := by
  rw [kappaPlus_singleton, iota_singleton]

-- (32b), `mendia2020_32b`
theorem the_kind_eq_none (h : ¬ s a b) : iota (kappaPlus s ∅) = Part.none :=
  iota_eq_none_of_ne (e := Quotient.mk s a) (e' := Quotient.mk s b) (by simp) (by simp)
    fun hab ↦ h (Quotient.eq.1 hab)

-- p. 604
theorem the_kappaPlus_eq_none (ha : a ∈ P) (hb : b ∈ P) (h : ¬ s a b) :
    iota (kappaPlus s P) = Part.none :=
  Part.eq_none_iff'.2 fun hd ↦ h ((iota_kappaPlus_dom ⟨a, ha⟩).1 hd a ha b hb)

-- (36), (37), footnote 11
theorem the_kappaPlus_ker {β : Type*} (f : E → β) (a : E) :
    Quotient.mk _ a ∈ iota (kappaPlus (Setoid.ker f) (f ⁻¹' {f a})) :=
  (mk_mem_iota_kappaPlus (P := f ⁻¹' {f a}) (a := a) rfl).2 subset_rfl

-- p. 604: independent classifications
theorem the_kappaPlus_ker_eq_none {α β : Type*} [Nontrivial β] (f : E → α) (g : E → β)
    (h : Function.Surjective fun x ↦ (f x, g x)) (a : E) :
    iota (kappaPlus (Setoid.ker g) (f ⁻¹' {f a})) = Part.none := by
  obtain ⟨b₁, b₂, hne⟩ := exists_pair_ne β
  obtain ⟨x₁, h₁⟩ := h (f a, b₁)
  obtain ⟨x₂, h₂⟩ := h (f a, b₂)
  rw [Prod.mk.injEq] at h₁ h₂
  exact the_kappaPlus_eq_none h₁.1 h₂.1 fun h' ↦ hne (h₁.2.symm.trans (h'.trans h₂.2))

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

-- (14b)
theorem not_exists_classes_eq_borderCollies_watchDogs :
    ¬ ∃ s : Setoid Dog, s.classes = {borderCollies, watchDogs} := fun ⟨s, h⟩ ↦ by
  have hb : borderCollies ∈ s.classes := by rw [h]; simp
  have hw : watchDogs ∈ s.classes := by rw [h]; simp
  have : (⟨.borderCollie, .guideDog, 0⟩ : Dog) ∈ watchDogs :=
    Setoid.eq_of_mem_classes hb (x := fido) rfl hw rfl ▸ rfl
  simp [watchDogs] at this

-- p. 601
theorem the_borderCollie_watchDogs :
    Quotient.mk _ fido ∈ iota (kappaPlus (Setoid.ker Dog.breed) (borderCollies ∩ watchDogs)) ∧
      (Setoid.ker Dog.breed).cell fido = borderCollies :=
  ⟨(mk_mem_iota_kappaPlus (P := borderCollies ∩ watchDogs) (a := fido) ⟨rfl, rfl⟩).2
    fun _ hx ↦ hx.1, rfl⟩

/-- The dogs of (14a) are three bulldogs and two beagles. -/
def room14a : Set Dog :=
  {⟨.bulldog, .guideDog, 0⟩, ⟨.bulldog, .guideDog, 1⟩, ⟨.bulldog, .guideDog, 2⟩,
    ⟨.beagle, .guideDog, 0⟩, ⟨.beagle, .guideDog, 1⟩}

-- (14a), `mendia2020_14a`
theorem ncard_image_breed_room14a : (Dog.breed '' room14a).ncard = 2 := by
  simp only [room14a, Set.image_insert_eq, Set.image_singleton]
  simp only [Set.insert_eq_of_mem, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
  exact Set.ncard_pair nofun

/-! ### The lions that eat people, (21b) -/

/-- Subspecies of lion. -/
inductive Subspecies
  | african | asiatic

/-- What a lion eats, read as footnote 11 requires, is only people, only zebras, or only
carrion. -/
inductive Diet
  | people | zebras | carrion

instance : Nontrivial Subspecies := ⟨⟨.african, .asiatic, nofun⟩⟩

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
  the_kappaPlus_ker_eq_none Lion.diet Lion.subspecies (fun ⟨d, s⟩ ↦ ⟨⟨s, d, 0⟩, rfl⟩)
    ⟨.african, .people, 0⟩

-- (36), (37)
theorem the_kappaPlus_diet :
    Quotient.mk _ (⟨.african, .people, 0⟩ : Lion) ∈
        iota (kappaPlus (Setoid.ker Lion.diet) eatPeople) ∧
      (Setoid.ker Lion.diet).cell ⟨.african, .people, 0⟩ = eatPeople :=
  ⟨the_kappaPlus_ker Lion.diet ⟨.african, .people, 0⟩, rfl⟩

/-! ### Amounts (§4.3) -/

/-- Under the partition of a preorder into its degrees, the definite over κ+ refers to the degree
of the instances of the restrictor, (57)–(59). -/
theorem amount_reading [Preorder E] (ha : a ∈ P) (hP : ∀ x ∈ P, AntisymmRel (· ≤ ·) x a) :
    (⟦a⟧ : CresswellDegree (· ≤ · : E → E → Prop)) ∈
      iota (kappaPlus (cresswellSetoid (· ≤ ·)) P) :=
  (mk_mem_iota_kappaPlus ha).2 fun x hx ↦ by
    rw [cresswellSetoid_eq_antisymmRel]
    exact hP x hx

-- (59), (65), (66)
theorem cell_cresswellSetoid_measure {D : Type*} [LinearOrder D] (μ : E → D) (a : E) :
    (cresswellSetoid fun x y ↦ μ y ≤ μ x).cell a = μ ⁻¹' {μ a} := by
  rw [cresswellSetoid_le_measure]
  rfl

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

/-- The champagne they spilled that evening, (48a), is ten litres of a prestige cuvée with 21
grams of sugar per litre. -/
def spilled : Champagne := ⟨.prestige, 10, 21, 0⟩

-- (64)
theorem cell_spilled_cuvee :
    (Setoid.ker Champagne.cuvee).cell spilled = Champagne.cuvee ⁻¹' {.prestige} :=
  rfl

-- (65)
theorem cell_spilled_litres :
    (cresswellSetoid fun x y : Champagne ↦ y.litres ≤ x.litres).cell spilled =
      Champagne.litres ⁻¹' {10} :=
  cell_cresswellSetoid_measure Champagne.litres spilled

-- (66)
theorem cell_spilled_sugar :
    (cresswellSetoid fun x y : Champagne ↦ y.sugar ≤ x.sugar).cell spilled =
      Champagne.sugar ⁻¹' {21} :=
  cell_cresswellSetoid_measure Champagne.sugar spilled

end Mendia2020
