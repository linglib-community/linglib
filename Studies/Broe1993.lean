module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Linglib.Core.Order.Concept
public import Linglib.Phonology.Segmental.Basic
public import Linglib.Phonology.Segmental.NaturalClass

/-!
# Broe 1993: structured specification

Broe replaces underspecified matrices and redundancy rules by a lattice. The descriptions a feature
set supports are ordered by inclusion of the classes they denote, which is the construction of
formal concept analysis for the relation between the segments of an inventory and the feature
values they bear: a node of the lattice of `Representations` is a class of segments together with
the feature values its members share. Its classes are
[the natural classes of the inventory and the empty class](##Broe1993.mem_classes_iff), and under
inclusion they [are the lattice](##Broe1993.classesOrderIso).

Redundancy is read off the order. The node of a feature value is the class of the segments that
bear it, and a redundancy rule $p \to q$ holds of the inventory exactly when
[the node of $p$ lies below the node of $q$](##Broe1993.ofAttribute_le_ofAttribute_iff_forall_mem).
Removing segments from an inventory keeps every description and shrinks its class, a map of
lattices that [reaches every node of the smaller lattice](##Broe1993.collapse_surjective) and
preserves meets, and descriptions with different classes
[may come to denote the same one](##Broe1993.quileute_collapse_not_injective). In the worked
example, the four vowels of Quileute bear every combination of [high] and [back] and
[no value predicts another](##Broe1993.quileute_no_redundancy); without the low front vowel
[[−back] lies below [+high] and [−high] below [+back]](##Broe1993.quileutePrime_redundancy).
[The join of two segments' nodes](##Broe1993.extent_ofObject_sup_ofObject) is the natural class
of what they share, so that
[/i/ and /u/ join lower than /i/ and /ɑ/](##Broe1993.quileutePrime_similarity).

## Implementation notes

The objects of the context are the members of a finite inventory and its attributes all the
feature values, so that the lattice is mathlib's `Concept` and its order, meets and joins are
those of formal concept analysis. `naturalClasses` lists the classes by meeting the classes of
the feature values, in any meet-semilattice, for computation.

## TODO

The reduced labelling of the lattice, in which each feature value labels one node, and the
distinctive features of a segment as the lowest feature nodes above it are not formalized.

## References

* [broe-1993]
-/

@[expose] public section

namespace Broe1993

open Phonology Segment Order Concept

/-! ### The lattice of representations -/

/-- A representation bears a feature value. -/
def Bears (x : Segment) (p : Feature × Bool) : Prop := x p.1 = p.2

instance (x : Segment) (p : Feature × Bool) : Decidable (Bears x p) :=
  inferInstanceAs (Decidable (x p.1 = p.2))

@[inherit_doc Bears]
local notation "bears[" I "]" => fun x : (I : Finset Segment) ↦ Bears (x : Segment)

section Representations

variable {I I' S : Finset Segment} {p q : Feature × Bool} {x d : Segment}

theorem bears_iff_setFeature_bot_le : Bears x p ↔ (⊥ : Segment).setFeature p.1 p.2 ≤ x := by
  rw [setFeature_le_iff (bot_apply _), and_iff_left bot_le, Bears]

theorem le_iff_forall_bears : d ≤ x ↔ ∀ p, Bears d p → Bears x p :=
  le_def.trans (Prod.forall (p := fun p ↦ Bears d p → Bears x p)).symm

/-- The lattice of representations of an inventory (§5.2.2, Stage 2): the formal concepts of the
relation between its segments and the feature values they bear. The extent of a node is a class
of segments and its intent the values they share. -/
abbrev Representations (I : Finset Segment) := Concept I (Feature × Bool) bears[I]

-- the class a description denotes is the extent of its feature values
theorem lowerPolar_bears (d : Segment) (I : Finset Segment) :
    lowerPolar bears[I] {p | Bears d p} = {x : I | ↑x ∈ naturalClass d I} := by
  ext x
  exact ⟨fun h ↦ mem_naturalClass.2 ⟨x.2, le_iff_forall_bears.2 fun p hp ↦ h hp⟩,
    fun h p hp ↦ le_iff_forall_bears.1 (mem_naturalClass.1 h).2 p hp⟩

-- no segment bears both values of a feature, so the least class is empty
theorem lowerPolar_univ (I : Finset Segment) :
    lowerPolar bears[I] Set.univ = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
  have h₁ : (x : Segment) .syllabic = some true := hx (b := (.syllabic, true)) trivial
  have h₂ : (x : Segment) .syllabic = some false := hx (b := (.syllabic, false)) trivial
  exact absurd (h₁.symm.trans h₂) (by decide)

-- the segments with a set of feature values are its lower polar
theorem lowerPolar_bears_coe (A : Finset (Feature × Bool)) (I : Finset Segment) :
    lowerPolar bears[I] ↑A = {x : I | ↑x ∈ extent A I} := by
  ext x
  exact ⟨fun h ↦ mem_extent.2 ⟨x.2, fun ⟨_, _⟩ hp ↦ mem_specs.2 (h (Finset.mem_coe.2 hp))⟩,
    fun h ⟨_, _⟩ hp ↦ mem_specs.1 ((mem_extent.1 h).2 (Finset.mem_coe.1 hp))⟩

-- what the members of a set of segments share is its upper polar
theorem upperPolar_bears (hS : S ⊆ I) :
    upperPolar bears[I] {x : I | (x : Segment) ∈ S} = ↑(sharedSpecs S) := by
  ext ⟨f, v⟩
  rw [Finset.mem_coe, mem_sharedSpecs]
  exact ⟨fun h y hy ↦ h (a := ⟨y, hS hy⟩) hy, fun h y hy ↦ h y hy⟩

theorem isExtent_iff (hS : S ⊆ I) :
    IsExtent bears[I] {x : I | (x : Segment) ∈ S} ↔ IsNaturalClass I S := by
  constructor
  · intro h
    have := h.eq
    rw [upperPolar_bears hS, lowerPolar_bears_coe] at this
    exact isNaturalClass_iff.2 <| Finset.ext fun x ↦
      ⟨fun hx ↦ (Set.ext_iff.1 this ⟨x, (mem_extent.1 hx).1⟩).1 hx,
        fun hx ↦ (Set.ext_iff.1 this ⟨x, hS hx⟩).2 hx⟩
  · rintro ⟨A, rfl⟩
    exact ⟨_, lowerPolar_bears_coe A I⟩

/-- The classes of an inventory: the extents of its lattice of representations. -/
def classes (I : Finset Segment) : Finset (Finset Segment) :=
  I.powerset.filter fun S ↦ IsExtent bears[I] {x : I | (x : Segment) ∈ S}

theorem mem_classes :
    S ∈ classes I ↔ S ⊆ I ∧ IsExtent bears[I] {x : I | (x : Segment) ∈ S} := by
  rw [classes, Finset.mem_filter, Finset.mem_powerset]

/-- The classes of the lattice of representations are the natural classes of the inventory,
the empty class among them. -/
theorem mem_classes_iff : S ∈ classes I ↔ IsNaturalClass I S := by
  rw [mem_classes]
  exact ⟨fun h ↦ (isExtent_iff h.1).1 h.2, fun h ↦ ⟨h.subset, (isExtent_iff h.subset).2 h⟩⟩

theorem classes_eq (I : Finset Segment) : classes I = I.powerset.filter (IsNaturalClass I) := by
  ext S
  simp only [mem_classes_iff, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h ↦ ⟨h.subset, h⟩, And.right⟩

/-- The lattice of descriptions (5) is the lattice of denotations (6) with its nodes relabelled:
the classes of an inventory under inclusion are its lattice of representations. -/
noncomputable def classesOrderIso (I : Finset Segment) : classes I ≃o Representations I :=
  RelIso.ofSurjective
    (OrderEmbedding.ofMapLEIff (fun S ↦ ofIsExtent _ _ (mem_classes.1 S.2).2) fun S _ ↦
      ⟨fun h x hx ↦ h (a := ⟨x, (mem_classes.1 S.2).1 hx⟩) hx, fun h _ hx ↦ h hx⟩)
    fun c ↦ by
      classical
      obtain ⟨T, hTI, hT⟩ : ∃ T : Finset Segment, T ⊆ I ∧ {x : I | (x : Segment) ∈ T} = c.extent :=
        ⟨(Finset.univ.filter (· ∈ c.extent)).map (.subtype _), fun x hx ↦ by
          obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
          exact y.2, by ext x; simp⟩
      exact ⟨⟨T, mem_classes.2 ⟨hTI, hT ▸ c.isExtent_extent⟩⟩, Concept.ext hT⟩

@[simp] theorem extent_classesOrderIso (S : classes I) :
    (classesOrderIso I S).extent = {x : I | (x : Segment) ∈ (S : Finset Segment)} := rfl

/-- A redundancy rule `p → q` holds of an inventory exactly when the node of `p` lies below the
node of `q`: the dominance relation of the lattice is the redundancy of its feature values. -/
theorem ofAttribute_le_ofAttribute_iff_forall_mem :
    ofAttribute bears[I] p ≤ ofAttribute bears[I] q ↔
      ∀ x ∈ I, Bears x p → Bears x q :=
  ofAttribute_le_ofAttribute_iff.trans Subtype.forall

-- descriptions that no segment satisfies together meet in the least node
theorem disjoint_ofAttribute_iff :
    Disjoint (ofAttribute bears[I] p) (ofAttribute bears[I] q) ↔
      ∀ x ∈ I, Bears x p → ¬Bears x q := by
  rw [disjoint_iff_inf_le, ← extent_subset_extent_iff, extent_inf, extent_bot, lowerPolar_univ,
    Set.subset_empty_iff, Set.eq_empty_iff_forall_notMem, Subtype.forall]
  simp [mem_lowerPolar_iff]

/-- The join of the nodes of two segments is the natural class of what they share (§6.4), so that
more similar segments join lower in the lattice. -/
theorem extent_ofObject_sup_ofObject {y : Segment} (hx : x ∈ I) (hy : y ∈ I) :
    (ofObject bears[I] ⟨x, hx⟩ ⊔ ofObject bears[I] ⟨y, hy⟩).extent =
      {z : I | (z : Segment) ∈ naturalClass (x ⊓ y) I} := by
  rw [ofObjects_sup_ofObjects, extent_ofObjects, ← lowerPolar_bears]
  congr 1
  ext p
  simp only [upperPolar_union, Set.mem_inter_iff, mem_upperPolar_singleton, Set.mem_ofPred_eq,
    bears_iff_setFeature_bot_le, le_inf_iff]

/-- Removing segments from an inventory collapses its lattice of representations: a node goes to
the node with the same feature values, whose class is what is left of its class. -/
def collapse (h : I' ⊆ I) : sInfHom (Representations I) (Representations I') :=
  comap (r := bears[I]) fun x : I' ↦ (⟨x, h x.2⟩ : I)

@[simp] theorem collapse_ofAttributes (h : I' ⊆ I) (t : Set (Feature × Bool)) :
    collapse h (ofAttributes _ t) = ofAttributes _ t :=
  comap_ofAttributes (r := bears[I]) t

-- every node of the lattice of a smaller inventory is the collapse of a node of the larger
theorem collapse_surjective (h : I' ⊆ I) : Function.Surjective (collapse h) :=
  comap_surjective bears[I] _

end Representations

/-! ### Enumerating the classes -/

section Construction

variable {α : Type*} [SemilatticeInf α] {base a c p s : α} {attrs l : List α}

private theorem foldr_inf_le {sub : List α} (ha : a ∈ sub) : sub.foldr (· ⊓ ·) base ≤ a := by
  induction sub with
  | nil => simp at ha
  | cons b rest ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact inf_le_left
    · exact inf_le_right.trans (ih ha)

private theorem foldr_inf_base (sub : List α) :
    sub.foldr (· ⊓ ·) (p ⊓ base) = p ⊓ sub.foldr (· ⊓ ·) base := by
  induction sub with
  | nil => rfl
  | cons b rest ih => simp only [List.foldr_cons, ih, inf_left_comm]

variable [DecidableEq α]

/-- A step of the construction adds the meets of the attribute extent `a` with the classes so
far, each once. -/
def addMeets (a : α) (acc : List α) : List α := acc.foldl (fun l s ↦ l.insert (a ⊓ s)) acc

section foldl

variable {β : Type*} [DecidableEq β] {x : β}

private theorem mem_foldl_insert (g : β → β) (l init : List β) :
    x ∈ l.foldl (fun l' t ↦ l'.insert (g t)) init ↔ x ∈ init ∨ ∃ t ∈ l, x = g t := by
  induction l generalizing init with
  | nil => simp
  | cons t l ih =>
    grind

private theorem nodup_foldl_insert (g : β → β) (l : List β) {init : List β} (h : init.Nodup) :
    (l.foldl (fun l' t ↦ l'.insert (g t)) init).Nodup := by
  induction l generalizing init with
  | nil => exact h
  | cons t l ih => exact ih h.insert

end foldl

theorem mem_addMeets : s ∈ addMeets a l ↔ s ∈ l ∨ ∃ t ∈ l, s = a ⊓ t :=
  mem_foldl_insert _ _ _

theorem nodup_addMeets (hl : l.Nodup) : (addMeets a l).Nodup := nodup_foldl_insert _ _ hl

/-- The meets of `base` with elements drawn from `attrs`, each listed once: the closure system
that `attrs` generates below `base`. -/
def naturalClasses (base : α) (attrs : List α) : List α := attrs.foldr addMeets [base]

theorem mem_naturalClasses_cons :
    s ∈ naturalClasses base (a :: attrs) ↔
      s ∈ naturalClasses base attrs ∨ ∃ t ∈ naturalClasses base attrs, s = a ⊓ t :=
  mem_addMeets

theorem nodup_naturalClasses (base : α) (attrs : List α) : (naturalClasses base attrs).Nodup := by
  induction attrs with
  | nil => exact List.nodup_singleton base
  | cons a rest ih => exact nodup_addMeets ih

theorem base_mem_naturalClasses (base : α) (attrs : List α) :
    base ∈ naturalClasses base attrs := by
  induction attrs with
  | nil => exact List.mem_singleton_self base
  | cons a rest ih => exact mem_naturalClasses_cons.2 (.inl ih)

theorem inf_mem_naturalClasses (ha : a ∈ attrs) (hs : s ∈ naturalClasses base attrs) :
    a ⊓ s ∈ naturalClasses base attrs := by
  induction attrs generalizing s with
  | nil => simp at ha
  | cons b rest ih =>
    rw [mem_naturalClasses_cons] at hs ⊢
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases hs with hs | ⟨t, ht, rfl⟩
      · exact .inr ⟨s, hs, rfl⟩
      · exact .inr ⟨t, ht, inf_left_idem _ _⟩
    · rcases hs with hs | ⟨t, ht, rfl⟩
      · exact .inl (ih ha' hs)
      · exact .inr ⟨a ⊓ t, ih ha' ht, inf_left_comm _ _ _⟩

theorem mem_naturalClasses :
    s ∈ naturalClasses base attrs ↔
      ∃ sub : List α, (∀ a ∈ sub, a ∈ attrs) ∧ s = sub.foldr (· ⊓ ·) base := by
  constructor
  · induction attrs generalizing s with
    | nil => intro hs; exact ⟨[], by simp, by simpa [naturalClasses] using hs⟩
    | cons a rest ih =>
      rw [mem_naturalClasses_cons]
      rintro (hs | ⟨t, ht, rfl⟩)
      · obtain ⟨sub, hmem, rfl⟩ := ih hs
        exact ⟨sub, fun c hc ↦ List.mem_cons_of_mem _ (hmem c hc), rfl⟩
      · obtain ⟨sub, hmem, rfl⟩ := ih ht
        exact ⟨a :: sub, by simpa using fun c hc ↦ List.mem_cons_of_mem _ (hmem c hc), rfl⟩
  · rintro ⟨sub, hmem, rfl⟩
    induction sub with
    | nil => exact base_mem_naturalClasses base attrs
    | cons a rest ih =>
      exact inf_mem_naturalClasses (hmem a List.mem_cons_self)
        (ih fun c hc ↦ hmem c (List.mem_cons_of_mem _ hc))

theorem naturalClasses_minimal {C : Set α} (hbase : base ∈ C)
    (hclosed : ∀ a ∈ attrs, ∀ s ∈ C, a ⊓ s ∈ C) : ∀ s ∈ naturalClasses base attrs, s ∈ C := by
  intro s hs
  obtain ⟨sub, hmem, rfl⟩ := mem_naturalClasses.mp hs
  clear hs
  induction sub with
  | nil => exact hbase
  | cons a rest ih =>
    exact hclosed a (hmem a List.mem_cons_self) _
      (ih fun c hc ↦ hmem c (List.mem_cons_of_mem _ hc))

theorem mem_naturalClasses_filter [DecidableLE α] :
    s ∈ naturalClasses base (attrs.filter (c ≤ ·)) ∧ c ≤ s ↔
      s ∈ naturalClasses base attrs ∧ c ≤ s := by
  refine ⟨fun ⟨hs, hc⟩ ↦ ⟨?_, hc⟩, fun ⟨hs, hc⟩ ↦ ⟨?_, hc⟩⟩ <;>
    obtain ⟨sub, hmem, rfl⟩ := mem_naturalClasses.mp hs <;>
    refine mem_naturalClasses.mpr ⟨sub, fun a ha ↦ ?_, rfl⟩
  · exact (List.mem_filter.mp (hmem a ha)).1
  · exact List.mem_filter.mpr ⟨hmem a ha, decide_eq_true (hc.trans (foldr_inf_le ha))⟩

theorem mem_naturalClasses_inf (hp : p ∈ attrs) :
    s ∈ naturalClasses (p ⊓ base) attrs ↔ s ∈ naturalClasses base attrs ∧ s ≤ p := by
  simp only [mem_naturalClasses, foldr_inf_base]
  constructor
  · rintro ⟨sub, hmem, rfl⟩
    exact ⟨⟨p :: sub, by simpa [hp] using hmem, rfl⟩, inf_le_left⟩
  · rintro ⟨⟨sub, hmem, rfl⟩, hle⟩
    exact ⟨sub, hmem, (inf_eq_right.mpr hle).symm⟩

end Construction

section Segment

open Phonology Segment

variable {I S : Finset Segment}

/-- The attribute extents of a segment inventory are, for each feature value, the members that
have it. -/
def attributeExtents (I : Finset Segment) : List (Finset Segment) :=
  (Feature.allFeatures ×ˢ [true, false]).map fun p ↦
    naturalClass ((⊥ : Segment).setFeature p.1 p.2) I

private theorem foldr_inf_naturalClass (l : List (Feature × Bool)) :
    (l.map fun p ↦ naturalClass ((⊥ : Segment).setFeature p.1 p.2) I).foldr (· ⊓ ·) I =
      I.filter fun x ↦ ∀ p ∈ l, x p.1 = some p.2 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    obtain ⟨f, v⟩ := p
    rw [List.map_cons, List.foldr_cons, ih]
    ext x
    simp only [Finset.inf_eq_inter, Finset.mem_inter, mem_naturalClass, Finset.mem_filter,
      List.forall_mem_cons, setFeature_le_iff (bot_apply _), and_iff_left bot_le]
    tauto

theorem mem_naturalClasses_attributeExtents :
    S ∈ naturalClasses I (attributeExtents I) ↔ IsNaturalClass I S := by
  rw [mem_naturalClasses]
  constructor
  · rintro ⟨sub, hsub, rfl⟩
    induction sub with
    | nil => exact isNaturalClass_self I
    | cons a rest ih =>
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 (hsub _ List.mem_cons_self)
      exact (isNaturalClass_naturalClass _ I).inter
        (ih fun b hb ↦ hsub b (List.mem_cons_of_mem _ hb))
  · have hmem (p : Feature × Bool) : p ∈ Feature.allFeatures ×ˢ [true, false] := by
      revert p; decide
    rintro ⟨A, rfl⟩
    refine ⟨((Feature.allFeatures ×ˢ [true, false]).filter (· ∈ A)).map
      fun p ↦ naturalClass ((⊥ : Segment).setFeature p.1 p.2) I, fun b hb ↦ ?_, ?_⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
      exact List.mem_map.2 ⟨p, List.mem_of_mem_filter hp, rfl⟩
    · rw [foldr_inf_naturalClass]
      ext x
      simp only [Finset.mem_filter, mem_extent, subset_specs_iff, List.mem_filter,
        decide_eq_true_eq, and_imp]
      exact and_congr_right fun _ ↦ ⟨fun h p _ hp ↦ h p hp, fun h p hp ↦ h p (hmem p) hp⟩

theorem toFinset_naturalClasses_attributeExtents (I : Finset Segment) :
    (naturalClasses I (attributeExtents I)).toFinset = classes I := by
  ext S
  rw [List.mem_toFinset, mem_naturalClasses_attributeExtents, mem_classes_iff]

/-! ### Quileute -/

namespace Quileute

/-- /i/, [+high, −back]. -/
def i : Segment := [+high, −back]

/-- /a/, [−high, −back]. -/
def a : Segment := [−high, −back]

/-- /ɑ/, [−high, +back]. -/
def «ɑ» : Segment := [−high, +back]

/-- /u/, [+high, +back]. -/
def u : Segment := [+high, +back]

/-- The four-vowel system of §5.2.2, exhaustively classified by [high] and [back]. -/
def vowels : Finset Segment := {i, a, «ɑ», u}

/-- Quileuteʹ, the system without the front low vowel. -/
def vowels' : Finset Segment := {i, «ɑ», u}

/-- The values of [high] and [back]. -/
def values : List (Feature × Bool) := [(.high, true), (.high, false), (.back, true), (.back, false)]

end Quileute

open Quileute

-- (6)
theorem quileute_classes :
    classes vowels = {vowels, {i, u}, {a, «ɑ»}, {«ɑ», u}, {i, a}, {i}, {a}, {«ɑ»}, {u}, ∅} := by
  rw [classes_eq]
  decide

-- every combination is attested, so no value of [high] or [back] predicts another
theorem quileute_no_redundancy : ∀ p ∈ values, ∀ q ∈ values,
    ofAttribute bears[vowels] p ≤ ofAttribute bears[vowels] q → p = q := by
  simp only [ofAttribute_le_ofAttribute_iff_forall_mem]
  decide +kernel

-- (9)
theorem quileutePrime_classes :
    classes vowels' = {vowels', {i, u}, {«ɑ», u}, {i}, {«ɑ»}, {u}, ∅} := by
  rw [classes_eq]
  decide

/-- Without the low front vowel the redundancy rules [−back] → [+high] and [−high] → [+back] hold
(p. 104): in the lattice (12) the node of [−back] lies below that of [+high] and the node of
[−high] below that of [+back]. -/
theorem quileutePrime_redundancy :
    ofAttribute bears[vowels'] (.back, false) < ofAttribute bears[vowels'] (.high, true) ∧
      ofAttribute bears[vowels'] (.high, false) < ofAttribute bears[vowels'] (.back, true) := by
  simp only [lt_iff_le_not_ge, ofAttribute_le_ofAttribute_iff_forall_mem]
  decide +kernel

-- (7): [−high, +back] is synonymous with [−high], and [−high, −back] denotes no vowel
theorem quileutePrime_synonymy :
    ofAttributes bears[vowels'] {(.high, false), (.back, true)} =
        ofAttribute bears[vowels'] (.high, false) ∧
      Disjoint (ofAttribute bears[vowels'] (.high, false))
        (ofAttribute bears[vowels'] (.back, false)) := by
  refine ⟨ofAttributes_pair_eq_left_iff.2 quileutePrime_redundancy.2.le, ?_⟩
  rw [disjoint_ofAttribute_iff]
  decide +kernel

-- (8): [−high, +back] and [−high] are distinct nodes of (5) that the collapse identifies
theorem quileute_collapse_not_injective (h : vowels' ⊆ vowels) :
    ¬Function.Injective (collapse h) := by
  intro hinj
  have := hinj (a₁ := ofAttributes bears[vowels] {(.high, false), (.back, true)})
    (a₂ := ofAttribute bears[vowels] (.high, false))
    (by rw [collapse_ofAttributes, collapse_ofAttributes]; exact quileutePrime_synonymy.1)
  rw [ofAttributes_pair_eq_left_iff, ofAttribute_le_ofAttribute_iff_forall_mem] at this
  revert this
  decide +kernel

/-- The lattice orders pairs of segments by similarity (§6.4): /i/ and /u/, which share [+high],
join strictly below /i/ and /ɑ/, which share nothing, and the joins of /u/ with /ɑ/ and with /i/
are unordered. -/
theorem quileutePrime_similarity :
    naturalClass (i ⊓ u) vowels' ⊂ naturalClass (i ⊓ «ɑ») vowels' ∧
      ¬naturalClass (u ⊓ «ɑ») vowels' ⊆ naturalClass (u ⊓ i) vowels' ∧
      ¬naturalClass (u ⊓ i) vowels' ⊆ naturalClass (u ⊓ «ɑ») vowels' := by
  decide +kernel

end Segment

end Broe1993
