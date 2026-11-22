module

public import Mathlib.Order.CompleteBooleanAlgebra
public import Linglib.Semantics.Mereology.Basic

/-!
# Mereology with a null element

In a part structure that may have a null element, one that is part of everything, the
mereological notions are stated with solid overlap: `x` and `y` overlap solidly if they share a
part that is not null. A sum of a set is an upper bound of it each of whose non-null parts
solidly overlaps a member, Strong Supplementation says that whatever is not part of `y` has a
non-null part that does not solidly overlap `y`, and a classical mereology,
`Mereology.IsClassicalMereology`, is Strong Supplementation with a sum of every nonempty set.

Under Strong Supplementation a sum is a least upper bound (`Mereology.IsSum.isLUB`). A complete
Boolean algebra is a classical mereology in this sense, and a classical mereology with a null
element is a complete Boolean algebra
(`Mereology.IsClassicalMereology.toCompleteBooleanAlgebra`). In it a proper part has a unique
remainder (`Mereology.IsClassicalMereology.existsUnique_remainder`) and two overlapping
individuals have a product.

## Implementation notes

On a part structure without a null element solid overlap is overlap, and these are the definitions
of `Mereology.Overlap`, `Mereology.IsFusion` and `Mereology.StrongSupplementation`. With a null
element the plain definitions degenerate: everything overlaps everything, and Strong
Supplementation fails. The axiom system [cotnoir-varzi-2021] give for mereology with a null
element, with Solid Remainder, is not formalized; the definitions here are the solid forms of
Strong Supplementation and Leśniewski's fusion. The statements are made with `IsBot`, so they
apply to a carrier with or without a least element.

## References

* [cotnoir-varzi-2021], [champollion-krifka-2016]
-/

@[expose] public section

namespace Mereology

variable {α : Type*}

/-! ### Overlap relative to a possible null individual

The axioms of classical mereology are stated for carriers with a null individual and without
one, so their overlap is relative to mathlib's `IsBot`; on an `OrderBot` carrier it is
`¬ Disjoint`. -/

section SolidOverlap

variable [PartialOrder α] {x y : α}

/-- Two elements overlap solidly if they share a part that is not null: the complement of the
solid disjointness of [cotnoir-varzi-2021], which is overlap where there is no null element and
`¬ Disjoint` where there is one. -/
def SolidOverlap (x y : α) : Prop := ∃ z, ¬ IsBot z ∧ z ≤ x ∧ z ≤ y

theorem SolidOverlap.refl (h : ¬ IsBot x) : SolidOverlap x x := ⟨x, h, le_rfl, le_rfl⟩

theorem SolidOverlap.symm (h : SolidOverlap x y) : SolidOverlap y x :=
  let ⟨z, hz, hzx, hzy⟩ := h; ⟨z, hz, hzy, hzx⟩

theorem SolidOverlap.not_isBot_left (h : SolidOverlap x y) : ¬ IsBot x :=
  let ⟨_, hz, hzx, _⟩ := h; fun hx ↦ hz (hx.mono hzx)

theorem SolidOverlap.not_isBot_right (h : SolidOverlap x y) : ¬ IsBot y := h.symm.not_isBot_left

theorem SolidOverlap.of_le (hx : ¬ IsBot x) (h : x ≤ y) : SolidOverlap x y := ⟨x, hx, le_rfl, h⟩

theorem SolidOverlap.mono {x' y' : α} (hx : x ≤ x') (hy : y ≤ y') (h : SolidOverlap x y) :
    SolidOverlap x' y' :=
  let ⟨z, hz, hzx, hzy⟩ := h; ⟨z, hz, hzx.trans hx, hzy.trans hy⟩

theorem overlap_iff_not_disjoint [OrderBot α] : SolidOverlap x y ↔ ¬ Disjoint x y :=
  (exists_congr fun _ ↦ and_congr_left' (not_congr isBot_iff_eq_bot)).trans
    not_disjoint_iff_exists.symm

end SolidOverlap

/-- Without a null individual, two elements overlap iff they share a part. -/
theorem overlap_iff_exists_le [PartialOrder α] [NoBotOrder α] {x y : α} :
    SolidOverlap x y ↔ ∃ z, z ≤ x ∧ z ≤ y :=
  ⟨fun ⟨z, _, hzx, hzy⟩ ↦ ⟨z, hzx, hzy⟩, fun ⟨z, hzx, hzy⟩ ↦ ⟨z, not_isBot z, hzx, hzy⟩⟩

/-! ### Sums -/

section Sum

variable [PartialOrder α] {P Q : Set α} {s t x y : α}

/-- `t` is a sum of the region `P` if it lies above each member and each of its non-null parts
overlaps one of them. Without a null element this is the sum of [champollion-krifka-2016]. -/
def IsSum (P : Set α) (t : α) : Prop :=
  (∀ x ∈ P, x ≤ t) ∧ ∀ y ≤ t, ¬ IsBot y → ∃ x ∈ P, SolidOverlap y x

/-- Every individual is the sum of itself. -/
theorem isSum_singleton (x : α) : IsSum {x} x :=
  ⟨fun _ h ↦ (Set.mem_singleton_iff.1 h).le, fun _ hy hy0 ↦ ⟨x, rfl, .of_le hy0 hy⟩⟩

/-- A sum overlaps exactly what its members overlap. -/
theorem IsSum.overlap_iff (h : IsSum P t) (w : α) : SolidOverlap w t ↔ ∃ x ∈ P, SolidOverlap w x :=
  ⟨fun ⟨p, hp, hpw, hpt⟩ ↦ let ⟨x, hx, ho⟩ := h.2 p hpt hp; ⟨x, hx, ho.mono hpw le_rfl⟩,
    fun ⟨x, hx, ho⟩ ↦ ho.mono le_rfl (h.1 x hx)⟩

/-- A sum of sums of subregions of `P` is a sum of a subregion of `P`. -/
theorem IsSum.bind {R : α → Set α} (ht : IsSum Q t) (hQ : ∀ q ∈ Q, IsSum (R q) q) :
    IsSum (⋃ q ∈ Q, R q) t :=
  ⟨fun _ hx ↦ let ⟨q, hq, hx⟩ := Set.mem_iUnion₂.1 hx; ((hQ q hq).1 _ hx).trans (ht.1 q hq),
    fun y hy hy0 ↦
      let ⟨q, hq, p, hp0, hpy, hpq⟩ := ht.2 y hy hy0
      let ⟨x, hx, ho⟩ := (hQ q hq).2 p hpq hp0
      ⟨x, Set.mem_iUnion₂.2 ⟨q, hq, hx⟩, ho.mono hpy le_rfl⟩⟩

end Sum

/-! ### Strong supplementation and products -/

/-- A part structure is strongly supplemented if whatever is not part of `y` has a non-null part
that does not overlap `y`. -/
class StronglySupplemented (α : Type*) [PartialOrder α] : Prop where
  exists_not_overlap ⦃x y : α⦄ : ¬ x ≤ y → ∃ z ≤ x, ¬ IsBot z ∧ ¬ SolidOverlap z y

/-- A part structure has products if two overlapping individuals have a greatest common part. -/
class HasProducts (α : Type*) [PartialOrder α] : Prop where
  exists_isGLB ⦃x y : α⦄ : SolidOverlap x y → ∃ p, IsGLB {x, y} p

/-- In a part structure with binary sums, the join of two individuals is their sum: each of its
non-null parts overlaps one of the two. Boolean algebras and classical mereologies satisfy this;
the lattice of three atoms any two of which join to the top does not. -/
class SupIsSum (α : Type*) [SemilatticeSup α] : Prop where
  isSum_sup (x y : α) : IsSum {x, y} (x ⊔ y)

export SupIsSum (isSum_sup)

section Principles

variable [PartialOrder α] {P : Set α} {s t x y : α}

/-- The product of two overlapping individuals is non-null. -/
theorem SolidOverlap.exists_isGLB [HasProducts α] (h : SolidOverlap x y) :
    ∃ p, ¬ IsBot p ∧ IsGLB {x, y} p :=
  let ⟨p, hp⟩ := HasProducts.exists_isGLB h
  let ⟨_, hq, hqx, hqy⟩ := h
  ⟨p, fun hb ↦ hq (hb.mono (hp.2 (by rintro _ (rfl | rfl) <;> assumption))), hp⟩

variable [StronglySupplemented α]

/-- In a strongly supplemented part structure, `x` is part of whatever all its non-null parts
overlap. -/
theorem le_of_forall_overlap (h : ∀ z ≤ x, ¬ IsBot z → SolidOverlap z y) : x ≤ y := by
  by_contra hxy
  obtain ⟨z, hzx, hz, hzy⟩ := StronglySupplemented.exists_not_overlap hxy
  exact hzy (h z hzx hz)

/-- A proper part of `y` leaves a non-null part of `y` that it does not overlap, weak
supplementation. -/
theorem exists_not_overlap_of_lt (h : x < y) : ∃ z ≤ y, ¬ IsBot z ∧ ¬ SolidOverlap z x :=
  StronglySupplemented.exists_not_overlap h.not_ge

/-- Two individuals that overlap the same things are identical. -/
theorem eq_of_forall_overlap_iff (h : ∀ w, SolidOverlap w x ↔ SolidOverlap w y) : x = y :=
  le_antisymm (le_of_forall_overlap fun z hz hz0 ↦ (h z).1 (.of_le hz0 hz))
    (le_of_forall_overlap fun z hz hz0 ↦ (h z).2 (.of_le hz0 hz))

/-- In a strongly supplemented part structure, a sum is what overlaps exactly what the members
overlap. -/
theorem isSum_iff_forall_overlap :
    IsSum P t ↔ ∀ w, SolidOverlap w t ↔ ∃ x ∈ P, SolidOverlap w x :=
  ⟨IsSum.overlap_iff, fun h ↦ ⟨fun x hx ↦ le_of_forall_overlap fun z hz hz0 ↦
    (h z).2 ⟨x, hx, .of_le hz0 hz⟩, fun y hy hy0 ↦ (h y).1 (.of_le hy0 hy)⟩⟩

/-- In a strongly supplemented part structure, a sum is a least upper bound. -/
theorem IsSum.isLUB (h : IsSum P t) : IsLUB P t :=
  ⟨fun _ hx ↦ h.1 _ hx, fun _ hw ↦ le_of_forall_overlap fun y hy hy0 ↦
    let ⟨_, hx, ho⟩ := h.2 y hy hy0
    ho.mono le_rfl (hw hx)⟩

/-- In a strongly supplemented part structure, a region has at most one sum. -/
theorem IsSum.unique (hs : IsSum P s) (ht : IsSum P t) : s = t := hs.isLUB.unique ht.isLUB

end Principles

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] {P : Set α} {t : α}

instance : StronglySupplemented α where
  exists_not_overlap x y h := ⟨x \ y, sdiff_le, by rwa [isBot_iff_eq_bot, sdiff_eq_bot_iff],
    overlap_iff_not_disjoint.not_left.2 disjoint_sdiff_self_left⟩

/-- In a Boolean algebra the sums are the least upper bounds. -/
theorem isSum_iff_isLUB : IsSum P t ↔ IsLUB P t := by
  refine ⟨IsSum.isLUB, fun h ↦ ⟨fun x hx ↦ h.1 hx, fun y hy hy0 ↦ ?_⟩⟩
  by_contra! hno
  refine hy0 (isBot_iff_eq_bot.2 ?_)
  have ht : t ≤ t \ y := h.2 fun x hx ↦
    le_sdiff.2 ⟨h.1 hx, (overlap_iff_not_disjoint.not_left.1 (hno x hx)).symm⟩
  exact (disjoint_sdiff_self_right.mono_right ht).eq_bot_of_le hy

instance : SupIsSum α where
  isSum_sup _ _ := isSum_iff_isLUB.2 isLUB_pair

end GeneralizedBooleanAlgebra

instance [SemilatticeInf α] : HasProducts α where
  exists_isGLB x y _ := ⟨x ⊓ y, isGLB_pair⟩

/-- A classical mereology that may have a null element: Strong Supplementation and a sum of
every nonempty region, both stated with solid overlap. Without a null element it is the
classical extensional mereology of [champollion-krifka-2016], whose axiom is uniqueness of sums
(`Mereology.isClassicalMereology_iff_existsUnique`). -/
class IsClassicalMereology (α : Type*) [PartialOrder α] : Prop
    extends StronglySupplemented α where
  exists_isSum (P : Set α) : P.Nonempty → ∃ t, IsSum P t

/-- A part structure is a classical mereology iff every nonempty region has exactly one sum,
the axiom of unique sums of [champollion-krifka-2016]. -/
theorem isClassicalMereology_iff_existsUnique [PartialOrder α] :
    IsClassicalMereology α ↔ ∀ P : Set α, P.Nonempty → ∃! t, IsSum P t := by
  refine ⟨fun h P hP ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨t, ht⟩ := h.exists_isSum P hP
    exact ⟨t, ht, fun s hs ↦ hs.unique ht⟩
  · have weak {x y : α} (hxy : x < y) : ∃ z ≤ y, ¬ IsBot z ∧ ¬ SolidOverlap z x := by
      by_contra! hall
      exact hxy.ne ((h {x} ⟨x, rfl⟩).unique (isSum_singleton x)
        ⟨fun _ e ↦ Set.mem_singleton_iff.1 e ▸ hxy.le, fun z hz hz0 ↦ ⟨x, rfl, hall z hz hz0⟩⟩)
    refine { exists_not_overlap := fun y u hyu ↦ ?_, exists_isSum := fun P hP ↦ (h P hP).exists }
    obtain ⟨s, hs⟩ := (h {y, u} ⟨y, .inl rfl⟩).exists
    have hus : u < s := lt_of_le_of_ne (hs.1 u (.inr rfl)) fun e ↦ hyu (e ▸ hs.1 y (.inl rfl))
    obtain ⟨w, hws, hw0, hwu⟩ := weak hus
    obtain ⟨_, rfl | rfl, v, hv, hvw, hvy⟩ := hs.2 w hws hw0
    · exact ⟨v, hvy, hv, fun ⟨q, hq, hqv, hqu⟩ ↦ hwu ⟨q, hq, hqv.trans hvw, hqu⟩⟩
    · exact absurd ⟨v, hv, hvw, hvy⟩ hwu

namespace IsClassicalMereology

section PartialOrder

variable [PartialOrder α] [IsClassicalMereology α] {P : Set α} {t x y z : α}

/-- In a classical mereology the sums of a nonempty region are its least upper bounds. -/
theorem isSum_iff_isLUB (hP : P.Nonempty) : IsSum P t ↔ IsLUB P t :=
  ⟨IsSum.isLUB, fun h ↦ let ⟨_, hs⟩ := exists_isSum P hP; hs.isLUB.unique h ▸ hs⟩

theorem isSum_pair (h : IsLUB {x, y} t) : IsSum {x, y} t :=
  (isSum_iff_isLUB (Set.insert_nonempty _ _)).2 h

theorem exists_remainder (h : x < y) : ∃ z, ¬ SolidOverlap z x ∧ IsLUB {x, z} y := by
  obtain ⟨w₀, hw₀y, -, hw₀x⟩ := exists_not_overlap_of_lt h
  obtain ⟨z, hz⟩ := exists_isSum {w | w ≤ y ∧ ¬ SolidOverlap w x} ⟨w₀, hw₀y, hw₀x⟩
  refine ⟨z, fun ⟨q, hq, hqz, hqx⟩ ↦ ?_, ⟨?_, fun u hu ↦ ?_⟩⟩
  · obtain ⟨r, ⟨_, hrx⟩, v, hv, hvq, hvr⟩ := hz.2 q hqz hq
    exact hrx ⟨v, hv, hvr, hvq.trans hqx⟩
  · rintro _ (rfl | rfl)
    exacts [h.le, hz.isLUB.2 fun _ hw ↦ hw.1]
  · refine le_of_forall_overlap fun v hv hv0 ↦ ?_
    by_cases hvx : SolidOverlap v x
    · exact hvx.mono le_rfl (hu (.inl rfl))
    · exact .of_le hv0 ((hz.1 v ⟨hv, hvx⟩).trans (hu (.inr rfl)))

theorem remainder_unique {z' : α} (hz : ¬ SolidOverlap z x) (hlub : IsLUB {x, z} y)
    (hz' : ¬ SolidOverlap z' x) (hlub' : IsLUB {x, z'} y) : z = z' := by
  have key {z z' : α} (hz : ¬ SolidOverlap z x) (hlub : IsLUB {x, z} y) (hlub' : IsLUB {x, z'} y) :
      z ≤ z' := le_of_forall_overlap fun v hv hv0 ↦ by
    obtain ⟨_, rfl | rfl, hov⟩ := (isSum_pair hlub').2 v (hv.trans (hlub.1 (.inr rfl))) hv0
    · exact absurd (hov.mono hv le_rfl) hz
    · exact hov
  exact le_antisymm (key hz hlub hlub') (key hz' hlub' hlub)

/-- A proper part of `y` has exactly one remainder in `y`, the unique separation of
[champollion-krifka-2016] and [champollion-2017]. -/
theorem existsUnique_remainder (h : x < y) : ∃! z, ¬ SolidOverlap z x ∧ IsLUB {x, z} y :=
  let ⟨z, hz, hlub⟩ := exists_remainder h
  ⟨z, ⟨hz, hlub⟩, fun _ ⟨hz', hlub'⟩ ↦ remainder_unique hz' hlub' hz hlub⟩

/-- The product of two overlapping individuals is the sum of their common parts. -/
instance : HasProducts α where
  exists_isGLB x y := fun ⟨q, _, hqx, hqy⟩ ↦ by
    obtain ⟨p, hp⟩ := exists_isSum {w | w ≤ x ∧ w ≤ y} ⟨q, hqx, hqy⟩
    refine ⟨p, ?_, fun w hw ↦ hp.1 w ⟨hw (.inl rfl), hw (.inr rfl)⟩⟩
    rintro _ (rfl | rfl)
    exacts [hp.isLUB.2 fun _ h ↦ h.1, hp.isLUB.2 fun _ h ↦ h.2]

/-! ### The generalized sum -/

/-- `sum P h` is the sum of the nonempty region `P`, the generalized sum `⊕P` of
[champollion-krifka-2016]. -/
noncomputable def sum (P : Set α) (h : P.Nonempty) : α := (exists_isSum P h).choose

variable (hP : P.Nonempty)

theorem isSum_sum : IsSum P (sum P hP) := (exists_isSum P hP).choose_spec

theorem isLUB_sum : IsLUB P (sum P hP) := (isSum_sum hP).isLUB

theorem _root_.Mereology.IsSum.eq_sum (h : IsSum P t) : t = sum P hP := h.unique (isSum_sum hP)

theorem le_sum (hx : x ∈ P) : x ≤ sum P hP := (isSum_sum hP).1 x hx

theorem sum_le_iff : sum P hP ≤ t ↔ ∀ x ∈ P, x ≤ t := isLUB_le_iff (isLUB_sum hP)

@[simp]
theorem sum_singleton (x : α) : sum {x} (Set.singleton_nonempty x) = x :=
  ((isSum_singleton x).eq_sum _).symm

/-- The binary sum `a ⊕ b` of a classical mereology is the sum of the pair `{a, b}`. -/
@[reducible] noncomputable def toSemilatticeSup : SemilatticeSup α :=
  { ‹PartialOrder α› with
    sup := fun a b ↦ sum {a, b} (Set.insert_nonempty _ _)
    le_sup_left := fun a b ↦ le_sum (P := {a, b}) (Set.insert_nonempty _ _) (.inl rfl)
    le_sup_right := fun a b ↦ le_sum (P := {a, b}) (Set.insert_nonempty _ _) (.inr rfl)
    sup_le := fun _ _ _ ha hb ↦ (sum_le_iff _).2 <| by
      rintro _ (rfl | rfl)
      exacts [ha, hb] }

end PartialOrder

instance [SemilatticeSup α] [IsClassicalMereology α] : SupIsSum α where
  isSum_sup _ _ := isSum_pair isLUB_pair

/-! ### Boolean algebras and non-null individuals -/

/-- A complete Boolean algebra is a classical mereology, its bottom the null individual and its
sums its suprema. -/
instance [CompleteBooleanAlgebra α] : IsClassicalMereology α where
  exists_isSum P _ := ⟨sSup P, Mereology.isSum_iff_isLUB.2 (isLUB_sSup _)⟩

theorem sum_eq_sSup [CompleteBooleanAlgebra α] (P : Set α) (hP : P.Nonempty) :
    sum P hP = sSup P :=
  (isLUB_sum hP).unique (isLUB_sSup _)

section Subtype

variable [PartialOrder α] {p : α → Prop} (hp : ∀ x, p x ↔ ¬ IsBot x)

include hp

private theorem overlap_of_overlap_subtype {x y : {x // p x}} (h : SolidOverlap x y) :
    SolidOverlap x.1 y.1 :=
  let ⟨z, _, hzx, hzy⟩ := h
  ⟨z, (hp z).1 z.2, hzx, hzy⟩

variable [IsClassicalMereology α]

private theorem eq_of_isBot_subtype {m : {x // p x}} (hm : IsBot m) (x : {x // p x}) :
    x = m := by
  refine le_antisymm (Subtype.coe_le_coe.1 ?_) (hm x)
  by_contra h
  obtain ⟨z, -, hz, hzm⟩ := StronglySupplemented.exists_not_overlap h
  exact hzm ⟨m, (hp m).1 m.2, hm ⟨z, (hp z).2 hz⟩, le_rfl⟩

/-- The non-null individuals of a classical mereology, picked out by any predicate, form a
classical mereology. -/
theorem subtype : IsClassicalMereology {x // p x} where
  exists_not_overlap x y h := by
    obtain ⟨z, hzx, hz, hzy⟩ := StronglySupplemented.exists_not_overlap
      (fun h' ↦ h (Subtype.coe_le_coe.1 h') : ¬ x.1 ≤ y.1)
    exact ⟨⟨z, (hp z).2 hz⟩, hzx, fun hb ↦ hzy ⟨z, hz, le_rfl, hb y⟩,
      fun ho ↦ hzy (overlap_of_overlap_subtype hp ho)⟩
  exists_isSum P := fun ⟨a, ha⟩ ↦ by
    obtain ⟨t, ht⟩ := exists_isSum {x : α | ∃ h, (⟨x, h⟩ : {x // p x}) ∈ P} ⟨a, a.2, ha⟩
    have ht0 : ¬ IsBot t := fun hb ↦ (hp a).1 a.2 (hb.mono (ht.1 a ⟨a.2, ha⟩))
    refine ⟨⟨t, (hp t).2 ht0⟩, fun x hx ↦ ht.1 x ⟨x.2, hx⟩, fun y hy hy0 ↦ ?_⟩
    obtain ⟨x, ⟨hx0, hx⟩, q, hq0, hqy, hqx⟩ := ht.2 y hy ((hp y).1 y.2)
    exact ⟨⟨x, hx0⟩, hx, ⟨q, (hp q).2 hq0⟩,
      fun hb ↦ hy0 (eq_of_isBot_subtype hp hb y ▸ hb), hqy, hqx⟩

omit hp in
/-- The non-null individuals of a classical mereology form a classical mereology, as the
nonempty subsets of a set do under inclusion ([champollion-krifka-2016]). -/
instance instSubtypeNotIsBot : IsClassicalMereology {x : α // ¬ IsBot x} :=
  subtype fun _ ↦ Iff.rfl

end Subtype

/-! ### The Boolean representation

A classical mereology with a null individual is a complete Boolean algebra, and adding a null
individual to a classical mereology without one gives a classical mereology, so the classical
mereologies without a null individual are the complete Boolean algebras with the bottom
removed. -/

section OrderBot
variable [PartialOrder α] [OrderBot α] [IsClassicalMereology α]

open Classical in
/-- A classical mereology with a null individual is a complete lattice. -/
@[reducible] noncomputable def toCompleteLattice : CompleteLattice α :=
  letI : SupSet α := ⟨fun s ↦ if h : s.Nonempty then sum s h else ⊥⟩
  completeLatticeOfSup α fun s ↦ by
    change IsLUB s (if h : s.Nonempty then sum s h else ⊥)
    split_ifs with h
    · exact isLUB_sum h
    · rw [Set.not_nonempty_iff_eq_empty.1 h]
      exact isLUB_empty

/-- A classical mereology with a null individual is a complete Boolean algebra. -/
@[reducible] noncomputable def toCompleteBooleanAlgebra : CompleteBooleanAlgebra α :=
  letI L : CompleteLattice α := toCompleteLattice
  have hc (x : α) : IsSum {w | ¬ SolidOverlap w x} (sSup {w | ¬ SolidOverlap w x}) :=
    (isSum_iff_isLUB ⟨⊥, fun h ↦ h.not_isBot_left isBot_bot⟩).2 (isLUB_sSup _)
  { L with
    le_sup_inf := fun x y z ↦ le_of_forall_overlap fun p hp hp0 ↦ by
      by_cases hpx : SolidOverlap p x
      · exact hpx.mono le_rfl le_sup_left
      · have key {u : α} (hu : p ≤ x ⊔ u) : p ≤ u := le_of_forall_overlap fun q hq hq0 ↦ by
          obtain ⟨_, rfl | rfl, ho⟩ := (isSum_pair isLUB_pair).2 q (hq.trans hu) hq0
          · exact absurd (ho.mono hq le_rfl) hpx
          · exact ho
        exact .of_le hp0 (le_sup_of_le_right
          (le_inf (key (hp.trans inf_le_left)) (key (hp.trans inf_le_right))))
    compl := fun x ↦ sSup {w | ¬ SolidOverlap w x}
    sdiff := fun x y ↦ x ⊓ sSup {w | ¬ SolidOverlap w y}
    himp := fun x y ↦ y ⊔ sSup {w | ¬ SolidOverlap w x}
    inf_compl_le_bot := fun x ↦ le_of_forall_overlap fun p hp hp0 ↦ by
      obtain ⟨w, hw, q, hq, hqp, hqw⟩ := (hc x).2 p (hp.trans inf_le_right) hp0
      exact absurd ⟨q, hq, hqw, hqp.trans (hp.trans inf_le_left)⟩ hw
    top_le_sup_compl := fun x ↦ le_of_forall_overlap fun p _ hp0 ↦ by
      by_cases hpx : SolidOverlap p x
      · exact hpx.mono le_rfl le_sup_left
      · exact .of_le hp0 (le_sup_of_le_right ((hc x).1 p hpx))
    sdiff_eq := fun _ _ ↦ rfl
    himp_eq := fun _ _ ↦ rfl }
end OrderBot

section WithBot
variable [PartialOrder α]

theorem _root_.Mereology.overlap_coe_withBot [NoBotOrder α] {a b : α} :
    SolidOverlap (a : WithBot α) b ↔ SolidOverlap a b := by
  constructor
  · rintro ⟨z, hz, hza, hzb⟩
    induction z with
    | bot => exact absurd isBot_bot hz
    | coe c => exact ⟨c, not_isBot c, WithBot.coe_le_coe.1 hza, WithBot.coe_le_coe.1 hzb⟩
  · rintro ⟨c, -, hca, hcb⟩
    exact ⟨c, fun h ↦ WithBot.not_coe_le_bot c (h ⊥), WithBot.coe_le_coe.2 hca,
      WithBot.coe_le_coe.2 hcb⟩

/-- Adding a null individual to a classical mereology without one gives a classical
mereology. -/
instance [NoBotOrder α] [IsClassicalMereology α] : IsClassicalMereology (WithBot α) where
  exists_not_overlap x y h := by
    induction x with
    | bot => exact absurd bot_le h
    | coe a =>
      have ha : ¬ IsBot (a : WithBot α) := fun hb ↦ WithBot.not_coe_le_bot a (hb ⊥)
      induction y with
      | bot => exact ⟨a, le_rfl, ha, fun ho ↦ ho.not_isBot_right isBot_bot⟩
      | coe b =>
        obtain ⟨z, hza, -, hzb⟩ := StronglySupplemented.exists_not_overlap
          (fun h' ↦ h (WithBot.coe_le_coe.2 h') : ¬ a ≤ b)
        exact ⟨z, WithBot.coe_le_coe.2 hza, fun hb ↦ WithBot.not_coe_le_bot z (hb ⊥),
          fun ho ↦ hzb (overlap_coe_withBot.1 ho)⟩
  exists_isSum P hP := by
    by_cases h : ∃ a : α, (a : WithBot α) ∈ P
    · obtain ⟨t, ht⟩ := exists_isSum {a : α | (a : WithBot α) ∈ P} h
      refine ⟨t, fun x hx ↦ ?_, fun y hy hy0 ↦ ?_⟩
      · induction x with
        | bot => exact bot_le
        | coe a => exact WithBot.coe_le_coe.2 (ht.1 a hx)
      · induction y with
        | bot => exact absurd isBot_bot hy0
        | coe c =>
          obtain ⟨a, ha, ho⟩ := ht.2 c (WithBot.coe_le_coe.1 hy) (not_isBot c)
          exact ⟨a, ha, overlap_coe_withBot.2 ho⟩
    · refine ⟨⊥, fun x hx ↦ ?_, fun y hy hy0 ↦ absurd (isBot_iff_eq_bot.2 (le_bot_iff.1 hy)) hy0⟩
      induction x with
      | bot => exact le_rfl
      | coe a => exact absurd ⟨a, hx⟩ h
end WithBot

end IsClassicalMereology

end Mereology
