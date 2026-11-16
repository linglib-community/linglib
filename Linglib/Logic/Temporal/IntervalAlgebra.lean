module

public import Linglib.Logic.Temporal.Allen
public import Linglib.Logic.Temporal.PointAlgebra
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Kleene

/-!
# The interval algebra

An element of the interval algebra is a set of the relations of [allen-1983] in which one interval
of a linear order may stand to another, read as their disjunction. Elements form a Boolean algebra
with a converse and a composition whose unit is equality; composition distributes over joins,
which the `IdemSemiring` instance records. Each element is a
[relation](##IntervalAlgebra.toSetRel) between intervals. On an order with four points the
relations [order as the elements do](##IntervalAlgebra.toSetRel_subset_toSetRel_iff), and on a
dense order without endpoints the relation of a product
[is the composite of the relations](##IntervalAlgebra.toSetRel_mul), so the laws of composition
are those of relations on the rationals. The point algebra
[embeds](##IntervalAlgebra.pure) as the relations between point intervals.

## Implementation notes

The sum of the semiring is the join. The composite of two elements is read off the intervals
among six points, placing a second interval only beside first intervals that stand to it in the
second element, which keeps it small enough for `decide +kernel`. The named elements are
irreducible, so that elaboration, which never needs their values, does not compute them, and are
built by `IntervalAlgebra.ofPred` from a predicate on relations.

## References

* [allen-1983]
* [vilain-kautz-1986]
-/

@[expose] public section

/-- An element of the interval algebra is a set of Allen relations, the ways in which one interval
may stand to another. -/
def IntervalAlgebra : Type := Finset Allen.Relation
deriving DecidableEq, BooleanAlgebra, Membership, Singleton, Insert

namespace IntervalAlgebra

open SetRel Allen

variable {C D : IntervalAlgebra} {r : Relation}

instance : DecidablePred (· ∈ C) := fun r ↦ Finset.decidableMem r C

instance : DecidableLE IntervalAlgebra := fun (C D : Finset Relation) ↦
  inferInstanceAs (Decidable (C ⊆ D))

instance : DecidableLT IntervalAlgebra := fun (C D : Finset Relation) ↦
  inferInstanceAs (Decidable (C ⊂ D))

@[ext] theorem ext (h : ∀ r, r ∈ C ↔ r ∈ D) : C = D := Finset.ext h

@[simp] theorem mem_sup : r ∈ C ⊔ D ↔ r ∈ C ∨ r ∈ D := Finset.mem_union

@[simp] theorem mem_inf : r ∈ C ⊓ D ↔ r ∈ C ∧ r ∈ D := Finset.mem_inter

/-- The relations that satisfy a predicate. -/
def ofPred (p : Relation → Prop) [DecidablePred p] : IntervalAlgebra := Finset.univ.filter p

@[simp] theorem mem_ofPred {p : Relation → Prop} [DecidablePred p] : r ∈ ofPred p ↔ p r :=
  Finset.mem_filter.trans (and_iff_right (Finset.mem_univ r))

theorem notMem_bot : r ∉ (⊥ : IntervalAlgebra) := Finset.notMem_empty r

theorem not_disjoint_iff : ¬ Disjoint C D ↔ ∃ r ∈ C, r ∈ D := Finset.not_disjoint_iff

/-! ### The relation of an element -/

section LinearOrder

variable {T : Type*} [LinearOrder T]

/-- The relation of an element relates an interval to the intervals that stand to it in one of
the element's relations. -/
def toSetRel (C : IntervalAlgebra) : SetRel (NonemptyInterval T) (NonemptyInterval T) :=
  {p | relation p.2 p.1 ∈ C}

variable {i j : NonemptyInterval T}

@[simp] theorem mem_toSetRel : (j, i) ∈ toSetRel C ↔ relation i j ∈ C := .rfl

instance : Decidable ((j, i) ∈ toSetRel C) := inferInstanceAs (Decidable (relation i j ∈ C))

@[simp] theorem toSetRel_bot : (toSetRel ⊥ : SetRel (NonemptyInterval T) _) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h ↦ notMem_bot h

theorem toSetRel_sup (C D : IntervalAlgebra) :
    (toSetRel (C ⊔ D) : SetRel (NonemptyInterval T) _) = toSetRel C ∪ toSetRel D := by
  ext ⟨j, i⟩
  simp

@[gcongr] theorem toSetRel_mono (h : C ≤ D) :
    (toSetRel C : SetRel (NonemptyInterval T) _) ⊆ toSetRel D :=
  fun _ hp ↦ h hp

/-- On an order with four points the relations of two elements are ordered as the elements
are. -/
theorem toSetRel_subset_toSetRel_iff (f : Fin 4 ↪o T) :
    (toSetRel C : SetRel (NonemptyInterval T) _) ⊆ toSetRel D ↔ C ≤ D := by
  refine ⟨fun h r hr ↦ ?_, toSetRel_mono⟩
  obtain ⟨i, j, rfl⟩ := exists_relation_eq r
  rw [← relation_map f] at hr ⊢
  exact h (a := (_, _)) hr

/-- One element's relation lies in another's on every linear order exactly when the element lies
in the other. -/
theorem forall_toSetRel_subset_iff :
    (∀ (T : Type) [LinearOrder T], (toSetRel C : SetRel (NonemptyInterval T) _) ⊆ toSetRel D) ↔
      C ≤ D :=
  ⟨fun h ↦ (toSetRel_subset_toSetRel_iff (RelEmbedding.refl _)).1 (h (Fin 4)),
    fun h _ _ ↦ toSetRel_mono h⟩

theorem toSetRel_injective (f : Fin 4 ↪o T) :
    Function.Injective (toSetRel : IntervalAlgebra → SetRel (NonemptyInterval T) _) :=
  fun _ _ h ↦ le_antisymm ((toSetRel_subset_toSetRel_iff f).1 h.subset)
    ((toSetRel_subset_toSetRel_iff f).1 h.superset)

end LinearOrder

/-! ### Converse -/

/-- The converse reads each relation from the second interval to the first. -/
instance : Inv IntervalAlgebra := ⟨fun C ↦ Finset.image Relation.inv C⟩

@[simp] theorem mem_inv : r ∈ C⁻¹ ↔ r.inv ∈ C := by
  change r ∈ Finset.image Relation.inv C ↔ _
  exact ⟨fun h ↦ by obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 h; simpa using hs,
    fun h ↦ Finset.mem_image.2 ⟨r.inv, h, r.inv_inv⟩⟩

instance : InvolutiveInv IntervalAlgebra where
  inv_inv C := by
    ext r
    simp

theorem toSetRel_inv {T : Type*} [LinearOrder T] (C : IntervalAlgebra) :
    (toSetRel C⁻¹ : SetRel (NonemptyInterval T) _) = (toSetRel C).inv := by
  ext ⟨i, j⟩
  simp

/-! ### Reversed time -/

/-- The element on reversed time. -/
def dual (C : IntervalAlgebra) : IntervalAlgebra := C.image Relation.dual

@[simp] theorem mem_dual {C : IntervalAlgebra} {r : Relation} : r ∈ dual C ↔ r.dual ∈ C :=
  ⟨fun h ↦ by obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 h; simpa using hs,
    fun h ↦ Finset.mem_image.2 ⟨r.dual, h, r.dual_dual⟩⟩

@[simp] theorem dual_dual (C : IntervalAlgebra) : dual (dual C) = C := by
  ext r; simp

/-- Two intervals stand in an element on reversed time exactly when they stand in its dual. -/
theorem mem_toSetRel_dual {T : Type*} [LinearOrder T] {i j : NonemptyInterval T} :
    (j.dual, i.dual) ∈ toSetRel C ↔ (j, i) ∈ toSetRel (dual C) := by
  simp

/-! ### Composition -/

/-- The unit is equality of intervals. -/
instance : One IntervalAlgebra :=
  ⟨ofPred fun r ↦ r.fstFst = .eq ∧ r.sndSnd = .eq⟩

/-- The product of two elements: the relations of an interval to a third compatible with its
standing in `D` to a second that stands in `C` to the third, read off the intervals among six
points. -/
@[irreducible] protected def mul (C D : IntervalAlgebra) : IntervalAlgebra :=
  ((Finset.univ : Finset (NonemptyInterval (Fin 6) × NonemptyInterval (Fin 6))).filter
      fun x ↦ relation x.1 x.2 ∈ D).biUnion fun x ↦
    ((Finset.univ : Finset (NonemptyInterval (Fin 6))).filter fun y ↦ relation x.2 y ∈ C).image
      (relation x.1)

/-- `C * D` holds of an interval and a third when the third stands to some second in `D` and the
second to the interval in `C`. -/
instance : Mul IntervalAlgebra := ⟨IntervalAlgebra.mul⟩

theorem mem_mul : r ∈ C * D ↔ ∃ i j k : NonemptyInterval (Fin 6),
    relation i j ∈ D ∧ relation j k ∈ C ∧ relation i k = r := by
  rw [show C * D = IntervalAlgebra.mul C D from rfl, IntervalAlgebra.mul]
  change r ∈ Finset.biUnion _ _ ↔ _
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Prod.exists]
  exact ⟨fun ⟨i, j, hC, k, hD, h⟩ ↦ ⟨i, j, k, hC, hD, h⟩,
    fun ⟨i, j, k, hC, hD, h⟩ ↦ ⟨i, j, hC, k, hD, h⟩⟩

section LinearOrder

variable {T : Type*} [LinearOrder T] 

theorem toSetRel_comp_subset (C D : IntervalAlgebra) :
    (toSetRel C ○ toSetRel D : SetRel (NonemptyInterval T) _) ⊆ toSetRel (C * D) := by
  rintro ⟨k, i⟩ ⟨j, hkj, hji⟩
  let f : Fin 6 → T := ![i.fst, i.snd, j.fst, j.snd, k.fst, k.snd]
  obtain ⟨g, hg⟩ := Ordering.exists_fin_compare_eq f
  have hle (a b : Fin 6) (h : f a ≤ f b) : g a ≤ g b :=
    compare_le_iff_le.1 (by rw [hg]; exact compare_le_iff_le.2 h)
  have hr (a b c d : Fin 6) (hab : f a ≤ f b) (hcd : f c ≤ f d) :
      relation ⟨(g a, g b), hle a b hab⟩ ⟨(g c, g d), hle c d hcd⟩ =
        relation ⟨(f a, f b), hab⟩ ⟨(f c, f d), hcd⟩ :=
    Relation.ext (ofEndpoints_eq hg a b c d)
  refine mem_toSetRel.2 <| mem_mul.2 ⟨⟨(g 0, g 1), hle 0 1 i.fst_le_snd⟩,
    ⟨(g 2, g 3), hle 2 3 j.fst_le_snd⟩, ⟨(g 4, g 5), hle 4 5 k.fst_le_snd⟩, ?_, ?_,
    hr 0 1 4 5 i.fst_le_snd k.fst_le_snd⟩
  · rw [hr 0 1 2 3 i.fst_le_snd j.fst_le_snd]; exact mem_toSetRel.1 hji
  · rw [hr 2 3 4 5 j.fst_le_snd k.fst_le_snd]; exact mem_toSetRel.1 hkj

/-- On dense time without endpoints the relation of a product is the composite of the relations:
the middle interval of a configuration of endpoints can be placed between any two intervals that
stand as its outer ones do. -/
theorem toSetRel_mul [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T] (C D : IntervalAlgebra) :
    (toSetRel (C * D) : SetRel (NonemptyInterval T) _) = toSetRel C ○ toSetRel D := by
  refine le_antisymm (fun ⟨k, i⟩ h ↦ ?_) (toSetRel_comp_subset C D)
  have : Nonempty T := ⟨i.fst⟩
  obtain ⟨I, J, K, hD, hC, hik⟩ := mem_mul.1 (mem_toSetRel.1 h)
  -- pair the endpoints of `I` and `K` with those of `i` and `k`, then extend to those of `J`
  obtain ⟨f, h₁, h₂, h₃, h₄⟩ := exists_partialIso_of_relation_eq hik
  obtain ⟨f₁, ⟨a, ha⟩, hf₁⟩ := (Order.PartialIso.definedAtLeft T J.fst).isCofinal f
  obtain ⟨f₂, ⟨b, hb⟩, hf₂⟩ := (Order.PartialIso.definedAtLeft T J.snd).isCofinal f₁
  have hab : a ≤ b := (le_iff_le_of_cmp_eq_cmp (f₂.prop _ (hf₂ ha) _ hb)).1 J.fst_le_snd
  refine ⟨⟨(a, b), hab⟩, mem_toSetRel.2 ?_, mem_toSetRel.2 ?_⟩
  · exact relation_eq_of_mem_partialIso f₂ (i := ⟨(a, b), hab⟩) (hf₂ ha) hb (hf₂ (hf₁ h₃))
      (hf₂ (hf₁ h₄)) ▸ hC
  · exact relation_eq_of_mem_partialIso f₂ (j := ⟨(a, b), hab⟩) (hf₂ (hf₁ h₁)) (hf₂ (hf₁ h₂))
      (hf₂ ha) hb ▸ hD

/-- The image under one element of the image under another lies in the image under their
product, so a complex aspect relates its outer interval to the run time as the product says. -/
theorem image_toSetRel_subset_mul (s : Set (NonemptyInterval T)) :
    (toSetRel C).image ((toSetRel D).image s) ⊆ (toSetRel (D * C)).image s := by
  rw [← SetRel.image_comp]
  exact fun _ ⟨k, hk, hik⟩ ↦ ⟨k, hk, toSetRel_comp_subset D C hik⟩

theorem image_toSetRel_mul [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T]
    (s : Set (NonemptyInterval T)) :
    (toSetRel C).image ((toSetRel D).image s) = (toSetRel (D * C)).image s := by
  rw [← SetRel.image_comp, toSetRel_mul]

end LinearOrder

/-! ### Named elements -/

/-- The first interval ends before the second starts. -/
@[irreducible]
def precedes : IntervalAlgebra := ofPred (·.sndFst = .lt)

/-- The first interval ends no later than the second starts. -/
@[irreducible]
def isBefore : IntervalAlgebra := ofPred (·.sndFst ≠ .gt)

/-- The first interval lies within the second. -/
@[irreducible]
def le : IntervalAlgebra := ofPred fun r ↦ r.fstFst ≠ .lt ∧ r.sndSnd ≠ .gt

/-- The first interval lies within the second and is not the whole of it. -/
@[irreducible]
def lt : IntervalAlgebra := le ⊓ ofPred fun r ↦ r.fstFst = .gt ∨ r.sndSnd = .lt

/-- The two intervals overlap. -/
@[irreducible]
def overlaps : IntervalAlgebra := ofPred fun r ↦ r.fstSnd ≠ .gt ∧ r.sndFst ≠ .lt

/-- The first interval starts within the second. -/
@[irreducible]
def startsWithin : IntervalAlgebra := ofPred fun r ↦ r.fstFst ≠ .lt ∧ r.fstSnd ≠ .gt

/-- The first interval lies within the second and ends with it. -/
@[irreducible]
def finalSubinterval : IntervalAlgebra := ofPred fun r ↦ r.fstFst ≠ .lt ∧ r.sndSnd = .eq

/-- The first interval lies within the second and ends before it. -/
@[irreducible]
def nonfinalSubinterval : IntervalAlgebra :=
  ofPred fun r ↦ r.fstFst ≠ .lt ∧ r.sndSnd = .lt

/-- The first interval starts no earlier than the second: no part of it precedes the second. -/
@[irreducible]
def startsNoEarlier : IntervalAlgebra := ofPred (·.fstFst ≠ .lt)

/-- The first interval ends no later than the second: no part of it follows the second. -/
@[irreducible]
def endsNoLater : IntervalAlgebra := ofPred (·.sndSnd ≠ .gt)

theorem precedes_mul_precedes : precedes * precedes = precedes := by decide +kernel

/-- Containment is starting no earlier and ending no later. -/
theorem le_eq_startsNoEarlier_inf_endsNoLater : le = startsNoEarlier ⊓ endsNoLater := by
  decide +kernel

/-- Ending no later is starting no earlier on reversed time. -/
theorem dual_startsNoEarlier : dual startsNoEarlier = endsNoLater := by decide +kernel

theorem dual_endsNoLater : dual endsNoLater = startsNoEarlier := by decide +kernel

/-- Containment is the same on reversed time. -/
theorem dual_le : dual le = le := by decide +kernel

/-- Precedence on reversed time is its converse. -/
theorem dual_precedes : dual precedes = precedes⁻¹ := by decide +kernel

theorem finalSubinterval_le_endsNoLater : finalSubinterval ≤ endsNoLater := by decide +kernel

/-- The relations whose position is one of `C`. -/
@[irreducible]
def ofPosition (C : PointAlgebra) : IntervalAlgebra := ofPred (·.position ∈ C)

theorem ofPosition_one : ofPosition 1 = overlaps := by decide +kernel

theorem ofPosition_lt : ofPosition {.lt} = precedes := by decide +kernel

section LinearOrder

variable {T : Type*} [LinearOrder T] {i j : NonemptyInterval T}

@[simp] theorem relation_mem_precedes : relation i j ∈ precedes ↔ i.Precedes j := by
  rw [precedes, mem_ofPred]
  simp [relation, ofEndpoints, NonemptyInterval.Precedes, compare_lt_iff_lt]

@[simp] theorem relation_mem_isBefore : relation i j ∈ isBefore ↔ i.IsBefore j := by
  rw [isBefore, mem_ofPred]
  simp [relation, ofEndpoints, NonemptyInterval.IsBefore, compare_le_iff_le]

@[simp] theorem relation_mem_le : relation i j ∈ le ↔ i ≤ j := by
  rw [le, mem_ofPred]
  simp [relation, ofEndpoints, NonemptyInterval.le_def, compare_le_iff_le, compare_ge_iff_ge]

@[simp] theorem relation_mem_lt : relation i j ∈ lt ↔ i < j := by
  rw [NonemptyInterval.lt_def, ← relation_mem_le, lt, mem_inf, mem_ofPred]
  simp [relation, ofEndpoints, compare_gt_iff_gt, compare_lt_iff_lt]

@[simp] theorem relation_mem_startsNoEarlier :
    relation i j ∈ startsNoEarlier ↔ j.fst ≤ i.fst := by
  rw [startsNoEarlier, mem_ofPred]
  simp [relation, ofEndpoints, compare_ge_iff_ge]

@[simp] theorem relation_mem_endsNoLater : relation i j ∈ endsNoLater ↔ i.snd ≤ j.snd := by
  rw [endsNoLater, mem_ofPred]
  simp [relation, ofEndpoints, compare_le_iff_le]

@[simp] theorem relation_mem_overlaps : relation i j ∈ overlaps ↔ i.Overlaps j := by
  rw [overlaps, mem_ofPred]
  simp [relation, ofEndpoints, NonemptyInterval.Overlaps, compare_le_iff_le, compare_ge_iff_ge]

@[simp] theorem relation_mem_startsWithin : relation i j ∈ startsWithin ↔ i.fst ∈ j := by
  rw [startsWithin, mem_ofPred]
  simp [relation, ofEndpoints, NonemptyInterval.mem_def, compare_le_iff_le, compare_ge_iff_ge]

@[simp] theorem relation_mem_finalSubinterval :
    relation i j ∈ finalSubinterval ↔ i.FinalSubinterval j := by
  rw [finalSubinterval, mem_ofPred]
  simp [relation, ofEndpoints, NonemptyInterval.FinalSubinterval, compare_lt_iff_lt]

@[simp] theorem relation_mem_nonfinalSubinterval :
    relation i j ∈ nonfinalSubinterval ↔ i.NonfinalSubinterval j := by
  rw [nonfinalSubinterval, mem_ofPred]
  simp [relation, ofEndpoints, NonemptyInterval.NonfinalSubinterval, compare_lt_iff_lt]

@[simp] theorem relation_mem_ofPosition {C : PointAlgebra} :
    relation i j ∈ ofPosition C ↔ i.position j ∈ C := by
  rw [ofPosition, mem_ofPred, position_relation]

theorem mem_toSetRel_precedes : (j, i) ∈ toSetRel precedes ↔ i.Precedes j :=
  relation_mem_precedes

theorem mem_toSetRel_overlaps : (j, i) ∈ toSetRel overlaps ↔ i.Overlaps j :=
  relation_mem_overlaps

theorem mem_toSetRel_le : (j, i) ∈ toSetRel le ↔ i ≤ j := relation_mem_le

theorem mem_toSetRel_ofPosition {C : PointAlgebra} :
    (j, i) ∈ toSetRel (ofPosition C) ↔ i.position j ∈ C :=
  relation_mem_ofPosition

instance : (toSetRel precedes : SetRel (NonemptyInterval T) _).IsTrans :=
  ⟨fun _ _ _ h₁ h₂ ↦ relation_mem_precedes.2
    (NonemptyInterval.precedes_trans (relation_mem_precedes.1 h₂) (relation_mem_precedes.1 h₁))⟩

/-- Precedence relates two intervals through a third exactly when time is dense. -/
theorem toSetRel_precedes_subset_comp_self_iff :
    (toSetRel precedes : SetRel (NonemptyInterval T) _) ⊆ toSetRel precedes ○ toSetRel precedes ↔
      DenselyOrdered T where
  mp h := ⟨fun a b hab ↦
    let ⟨c, h₁, h₂⟩ := @h (.pure b, .pure a) (relation_mem_precedes.2 hab)
    ⟨c.fst, relation_mem_precedes.1 h₂, c.fst_le_snd.trans_lt (relation_mem_precedes.1 h₁)⟩⟩
  mpr _ := fun _ h ↦ let ⟨u, hu, hu'⟩ := exists_between (relation_mem_precedes.1 h)
    ⟨.pure u, relation_mem_precedes.2 hu', relation_mem_precedes.2 hu⟩

/-- On dense time the composite of precedence with itself is precedence. -/
theorem toSetRel_precedes_comp_self [DenselyOrdered T] :
    (toSetRel precedes ○ toSetRel precedes : SetRel (NonemptyInterval T) _) =
      toSetRel precedes :=
  subset_antisymm SetRel.comp_subset_self (toSetRel_precedes_subset_comp_self_iff.2 ‹_›)

end LinearOrder

/-! ### Points

The point algebra embeds as the relations between point intervals. -/

/-- The relations between point intervals whose points compare as `C` allows. -/
@[irreducible]
def pure (C : PointAlgebra) : IntervalAlgebra :=
  ofPred fun r ↦ r.firstShape = .eq ∧ r.secondShape = .eq ∧ r.fstFst ∈ C

theorem mem_pure {C : PointAlgebra} :
    r ∈ pure C ↔ r.firstShape = .eq ∧ r.secondShape = .eq ∧ r.fstFst ∈ C := by
  rw [pure, mem_ofPred]

section LinearOrder

variable {T : Type*} [LinearOrder T] {i j : NonemptyInterval T}

@[simp] theorem relation_mem_one : relation i j ∈ (1 : IntervalAlgebra) ↔ i = j := by
  change relation i j ∈ ofPred _ ↔ _
  rw [mem_ofPred]
  simp [relation, ofEndpoints, NonemptyInterval.ext_iff, Prod.ext_iff]

@[simp] theorem relation_mem_pure {C : PointAlgebra} :
    relation i j ∈ pure C ↔ i.IsPoint ∧ j.IsPoint ∧ compare i.fst j.fst ∈ C := by
  simp [mem_pure, relation, ofEndpoints, NonemptyInterval.IsPoint]

end LinearOrder

private theorem exists_fin_of_mem_comp :
    ∀ r s o : Ordering, o ∈ r.comp s →
      ∃ x y z : Fin 6, compare x y = r ∧ compare y z = s ∧ compare x z = o := by
  decide

private theorem toComparisons_eq_of_shapes :
    ∀ t : Relation, t.firstShape = .eq → t.secondShape = .eq →
      t.toComparisons = ⟨t.fstFst, t.fstFst, t.fstFst, t.fstFst, .eq, .eq⟩ := by
  decide +kernel

/-- The embedding of the point algebra preserves products. -/
theorem pure_mul (R S : PointAlgebra) : pure (R * S) = pure R * pure S := by
  symm
  ext t
  simp only [mem_mul, mem_pure]
  constructor
  · rintro ⟨i, j, k, ⟨h1, -, hS⟩, ⟨-, h2, hR⟩, rfl⟩
    exact ⟨h1, h2, PointAlgebra.compare_mem_mul hS hR⟩
  · rintro ⟨h1, h2, hc⟩
    obtain ⟨s, hs, r, hr, ho⟩ := PointAlgebra.mem_mul.1 hc
    obtain ⟨x, y, z, hxy, hyz, hxz⟩ := exists_fin_of_mem_comp s r _ ho
    have hself (a : Fin 6) : compare a a = .eq := compare_eq_iff_eq.2 rfl
    refine ⟨.pure x, .pure y, .pure z, ⟨hself x, hself y, show compare x y ∈ S from hxy ▸ hs⟩,
      ⟨hself y, hself z, show compare y z ∈ R from hyz ▸ hr⟩, Relation.ext ?_⟩
    rw [toComparisons_eq_of_shapes t h1 h2]
    simp [ofEndpoints, hxz]

/-! ### The laws of composition

The relations of the elements on the rationals are faithful and exact, so each law of composition
is the law of relations it names. -/

@[simp] theorem toSetRel_one {T : Type*} [LinearOrder T] :
    (toSetRel 1 : SetRel (NonemptyInterval T) _) = SetRel.id := by
  ext ⟨j, i⟩
  rw [mem_toSetRel, relation_mem_one]
  exact eq_comm

private theorem eq_of_toSetRel_rat
    (h : (toSetRel C : SetRel (NonemptyInterval ℚ) _) = toSetRel D) : C = D :=
  toSetRel_injective ((Fin.valOrderEmb 4).trans Nat.castOrderEmbedding) h

private theorem comp_union {α : Type*} (R S S' : SetRel α α) :
    R ○ (S ∪ S') = (R ○ S) ∪ (R ○ S') := by
  ext ⟨a, c⟩
  simp only [SetRel.mem_comp, Set.mem_union, and_or_left, exists_or]

private theorem union_comp {α : Type*} (R R' S : SetRel α α) :
    (R ∪ R') ○ S = (R ○ S) ∪ (R' ○ S) := by
  ext ⟨a, c⟩
  simp only [SetRel.mem_comp, Set.mem_union, or_and_right, exists_or]

instance : Add IntervalAlgebra := ⟨(· ⊔ ·)⟩

instance : Zero IntervalAlgebra := ⟨⊥⟩

theorem add_eq_sup (C D : IntervalAlgebra) : C + D = C ⊔ D := rfl

theorem zero_eq_bot : (0 : IntervalAlgebra) = ⊥ := rfl

instance : IdemSemiring IntervalAlgebra where
  __ := (inferInstance : SemilatticeSup IntervalAlgebra)
  __ := (inferInstance : OrderBot IntervalAlgebra)
  nsmul := nsmulRec
  nsmul_zero := fun _ ↦ rfl
  nsmul_succ := fun _ _ ↦ rfl
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  mul_assoc _ _ _ := by
    apply eq_of_toSetRel_rat
    simp only [toSetRel_mul, SetRel.comp_assoc]
  one_mul _ := by
    apply eq_of_toSetRel_rat
    rw [toSetRel_mul, toSetRel_one, SetRel.id_comp]
  mul_one _ := by
    apply eq_of_toSetRel_rat
    rw [toSetRel_mul, toSetRel_one, SetRel.comp_id]
  left_distrib _ _ _ := by
    apply eq_of_toSetRel_rat
    simp only [add_eq_sup, toSetRel_mul, toSetRel_sup, comp_union]
  right_distrib _ _ _ := by
    apply eq_of_toSetRel_rat
    simp only [add_eq_sup, toSetRel_mul, toSetRel_sup, union_comp]
  zero_mul _ := by
    apply eq_of_toSetRel_rat
    rw [zero_eq_bot, toSetRel_mul, toSetRel_bot, SetRel.empty_comp]
  mul_zero _ := by
    apply eq_of_toSetRel_rat
    rw [zero_eq_bot, toSetRel_mul, toSetRel_bot, SetRel.comp_empty]

theorem mul_inv_rev (C D : IntervalAlgebra) : (C * D)⁻¹ = D⁻¹ * C⁻¹ := by
  apply eq_of_toSetRel_rat
  simp only [toSetRel_inv, toSetRel_mul, SetRel.inv_comp]

/-! ### Chains

A clause's times form a chain, each related to the one before it by a head's element. -/

section LinearOrder

variable {T : Type*} [LinearOrder T]

/-- The intervals `tos` stand along the elements `cs` from `b`: the first stands to `b` as the
first element says, and each later one to the one before it as the next element says. -/
def HoldsAlong : List (IntervalAlgebra) → NonemptyInterval T → List (NonemptyInterval T) → Prop
  | [], _, [] => True
  | C :: cs, y, x :: xs => (y, x) ∈ toSetRel C ∧ HoldsAlong cs x xs
  | _, _, _ => False

instance instDecidableHoldsAlong :
    ∀ (cs : List (IntervalAlgebra)) (b : NonemptyInterval T) tos,
      Decidable (HoldsAlong cs b tos)
  | [], _, [] => isTrue trivial
  | [], _, _ :: _ => isFalse id
  | _ :: _, _, [] => isFalse id
  | C :: cs, y, x :: xs =>
    have := instDecidableHoldsAlong cs x xs
    inferInstanceAs (Decidable ((y, x) ∈ toSetRel C ∧ HoldsAlong cs x xs))

end LinearOrder
section LinearOrder

variable {T : Type*} [LinearOrder T]

theorem HoldsAlong.mem_toSetRel_prod :
    ∀ {cs : List (IntervalAlgebra)} {b : NonemptyInterval T} {tos : List (NonemptyInterval T)},
      HoldsAlong cs b tos →
        (b, (b :: tos).getLast (List.cons_ne_nil _ _)) ∈ toSetRel cs.prod
  | [], b, [], _ => by simp
  | C :: cs, b, x :: xs, ⟨hx, h⟩ => by
    rw [List.prod_cons, List.getLast_cons (List.cons_ne_nil _ _)]
    exact toSetRel_comp_subset _ _ (SetRel.mem_comp.2 ⟨x, hx, h.mem_toSetRel_prod⟩)

/-- On dense time without endpoints, two times stand in a chain's composite exactly when the chain
can be realized from the first to the second. -/
theorem mem_toSetRel_prod_iff [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T] :
    ∀ {cs : List (IntervalAlgebra)} {b x : NonemptyInterval T},
      (b, x) ∈ toSetRel cs.prod ↔
        ∃ tos, HoldsAlong cs b tos ∧ (b :: tos).getLast (List.cons_ne_nil _ _) = x
  | [], b, x => by
    rw [List.prod_nil, mem_toSetRel, relation_mem_one]
    refine ⟨fun h ↦ ⟨[], trivial, h.symm⟩, ?_⟩
    rintro ⟨_ | _, h, rfl⟩
    · rfl
    · exact absurd h id
  | C :: cs, b, x => by
    refine ⟨fun h ↦ ?_, fun ⟨tos, h, hx⟩ ↦ hx ▸ h.mem_toSetRel_prod⟩
    rw [List.prod_cons, toSetRel_mul] at h
    obtain ⟨j, hbj, hjx⟩ := h
    obtain ⟨tos, htos, rfl⟩ := mem_toSetRel_prod_iff.1 hjx
    exact ⟨j :: tos, ⟨hbj, htos⟩, by simp⟩

end LinearOrder

end IntervalAlgebra
