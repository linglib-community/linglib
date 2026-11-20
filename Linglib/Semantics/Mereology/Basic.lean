module

public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Antichain
public import Mathlib.Order.Atoms
public import Mathlib.Order.SupClosed
public import Linglib.Core.Data.Fintype.Order
public import Linglib.Core.Order.SupClosed

/-!
# Algebraic mereology

Algebraic semantics models parthood as a partial order and mereological sum as join. The
reference properties of a region, a set of individuals, are then mathlib predicates: cumulativity
is `SupClosed`, divisiveness `IsLowerSet` and quantization `IsAntichain (· ≤ ·)`, and Link's
closure `*P` is `supClosure`, so a region is quantized and cumulative only if it has at most one
member (`Mereology.qua_and_cum_iff_subsingleton`).

Atoms and counting are stated here on a carrier with a least element `⊥`, as the sets of atoms
of a model are: an atom is `IsAtom`, two individuals overlap when they are not `Disjoint`
(`Mereology.not_disjoint_iff_exists`), and `⊥` is no individual. On a part structure without a
null element an atom is `IsMin` and overlap is `Mereology.Overlap`; `WithBot.isAtom_coe` and
`Mereology.overlap_iff_not_disjoint_coe` translate between the two.

## Implementation notes

`supClosure` closes under binary sums, which agrees with closure under sums of arbitrary
nonempty subsets only for finite sums.

## References

* [bylinina-nouwen-2018], [champollion-krifka-2016], [krifka-1989], [krifka-1998],
  [landman-2020], [link-1983]
-/

@[expose] public section

namespace Mereology

variable {α β : Type*}

/-! ### Reference properties

A region is a set of individuals. Cumulative, divisive and quantized reference are the mathlib
predicates `SupClosed`, `IsLowerSet` and `IsAntichain (· ≤ ·)` of a region, so hypotheses of
these forms are applied directly: `hC hx hy : x ⊔ y ∈ s`, `hD hle hx : y ∈ s`,
`hQ hx hy hne : ¬ x ≤ y`. -/

/-- A region has divisive reference if every part of a member is a member. -/
abbrev DIV [Preorder α] (s : Set α) : Prop := IsLowerSet s

section PartialOrder

variable [PartialOrder α] {s : Set α}

/-- A region has quantized reference ([krifka-1989]) if no proper part of a member is a
member. -/
abbrev QUA (s : Set α) : Prop := IsAntichain (· ≤ ·) s

theorem qua_of_forall (h : ∀ x y, x ∈ s → y < x → y ∉ s) : QUA s :=
  fun _ ha _ hb hne hle ↦ h _ _ hb (lt_of_le_of_ne hle hne) ha

theorem QUA.preimage [PartialOrder β] {d : α → β} (hd : StrictMono d) {t : Set β}
    (ht : QUA t) : QUA (d ⁻¹' t) :=
  fun _ ha _ hb hab hle ↦ ht ha hb (hd (hle.lt_of_ne hab)).ne (hd (hle.lt_of_ne hab)).le

/-- The `P`-atoms ([krifka-1989]) are the minimal `P`-elements. -/
def atomize (s : Set α) : Set α := {x | Minimal (· ∈ s) x}

@[simp] theorem mem_atomize {s : Set α} {x : α} : x ∈ atomize s ↔ Minimal (· ∈ s) x := Iff.rfl

theorem atomize_subset (s : Set α) : atomize s ⊆ s := fun _ h ↦ h.prop

theorem atomize_qua {s : Set α} : QUA (atomize s) := setOfPred_minimal_antichain (· ∈ s)

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup α] {s : Set α}

/-- A region has cumulative reference ([link-1983], [krifka-1989]) if it is closed under sum.
[krifka-1998] also requires two distinct members, and [champollion-krifka-2016] give a form
closed under sums of arbitrary nonempty subsets. -/
abbrev CUM (s : Set α) : Prop := SupClosed s

instance [Fintype α] [DecidablePred (· ∈ s)] : Decidable (CUM s) :=
  decidable_of_iff (∀ x, x ∈ s → ∀ y, y ∈ s → x ⊔ y ∈ s) Iff.rfl

/-- A region is both quantized and cumulative iff it has at most one member: the two parts of a
sum in the region are the sum itself. So a quantized region with two members is not cumulative
([krifka-1989] (T 3)). -/
theorem qua_and_cum_iff_subsingleton : QUA s ∧ CUM s ↔ s.Subsingleton :=
  ⟨fun ⟨hQ, hC⟩ _ hx _ hy ↦
      (hQ.eq hx (hC hx hy) le_sup_left).trans (hQ.eq hy (hC hx hy) le_sup_right).symm,
    fun h ↦ ⟨h.isAntichain _, fun x hx y hy ↦ by rw [h hx hy, sup_idem]; exact hy⟩⟩

theorem cum_maximal_iff_isGreatest (hCum : CUM s) {x : α} :
    Maximal (· ∈ s) x ↔ IsGreatest s x :=
  ⟨fun hx ↦ ⟨hx.1, fun _ hy ↦ le_sup_right.trans (hx.2 (hCum hx.1 hy) le_sup_left)⟩,
    fun hx ↦ ⟨hx.1, fun _ hy _ ↦ hx.2 hy⟩⟩

theorem cum_maximal_unique (hCum : CUM s) {x y : α} (hx : Maximal (· ∈ s) x)
    (hy : Maximal (· ∈ s) y) : x = y :=
  ((cum_maximal_iff_isGreatest hCum).1 hx).unique ((cum_maximal_iff_isGreatest hCum).1 hy)

/-! ### Algebraic closure

Link's `*P` ([link-1983]), the least region containing `P` and closed under binary sum, is
mathlib's `supClosure`. -/

theorem map_mem_supClosure {β : Type*} [SemilatticeSup β] {t : Set β} {f : α → β}
    (hf : ∀ x y, f (x ⊔ y) = f x ⊔ f y) (h : ∀ x ∈ s, f x ∈ t) {x : α}
    (hx : x ∈ supClosure s) : f x ∈ supClosure t := by
  induction hx using supClosure_induction with
  | mem a ha => exact subset_supClosure (h a ha)
  | sup a b _ _ iha ihb => exact hf a b ▸ supClosed_supClosure iha ihb

theorem exists_le_of_mem_supClosure {x : α} (h : x ∈ supClosure s) : ∃ a ∈ s, a ≤ x := by
  induction h using supClosure_induction with
  | mem a ha => exact ⟨a, ha, le_rfl⟩
  | sup a b _ _ iha _ => obtain ⟨c, hc, hle⟩ := iha; exact ⟨c, hc, hle.trans le_sup_left⟩

section OrderBot

variable [OrderBot α]

/-- The full algebraic closure `×P` adds the empty sum `⊥` to `*P`, closing `P` under the sums of
all finite families, the empty one included ([bylinina-nouwen-2018]'s (30)). -/
def fullSupClosure (s : Set α) : Set α := insert ⊥ (supClosure s)

theorem mem_fullSupClosure_iff_exists_sup (s : Set α) (x : α) :
    x ∈ fullSupClosure s ↔ ∃ t : Finset α, ↑t ⊆ s ∧ t.sup id = x := by
  rw [fullSupClosure, Set.mem_insert_iff]
  constructor
  · rintro (rfl | ⟨t, ht, hP, rfl⟩)
    · exact ⟨∅, by simp, Finset.sup_empty⟩
    · exact ⟨t, hP, (Finset.sup'_eq_sup ht id).symm⟩
  · rintro ⟨t, hP, rfl⟩
    rcases t.eq_empty_or_nonempty with rfl | ht
    · exact .inl Finset.sup_empty
    · exact .inr ⟨t, ht, hP, Finset.sup'_eq_sup ht id⟩

end OrderBot

end SemilatticeSup

/-! ### Atoms and overlap

The carrier has a null individual `⊥`, as a Boolean algebra does, and the individuals of the
sources are its elements other than `⊥`. An atom is then mathlib's `IsAtom`, and two individuals
overlap when they are not `Disjoint`. -/

section Atoms

variable [PartialOrder α] [OrderBot α] {x y : α}

/-- Two individuals are not disjoint iff they share a part that is not null. -/
theorem not_disjoint_iff_exists : ¬ Disjoint x y ↔ ∃ z, z ≠ ⊥ ∧ z ≤ x ∧ z ≤ y :=
  ⟨fun h ↦ by
      by_contra hz
      exact h fun z hx hy ↦ le_bot_iff.2 (by_contra fun h0 ↦ hz ⟨z, h0, hx, hy⟩),
    fun ⟨_, hz, hx, hy⟩ h ↦ hz (le_bot_iff.1 (h hx hy))⟩

instance (priority := low) [Fintype α] [DecidableEq α] [DecidableLT α] (x : α) :
    Decidable (IsAtom x) :=
  inferInstanceAs (Decidable (x ≠ ⊥ ∧ ∀ b < x, b = ⊥))

theorem not_disjoint_of_le (hx : x ≠ ⊥) (h : x ≤ y) : ¬ Disjoint x y :=
  fun hd ↦ hx (hd.eq_bot_of_le h)

theorem qua_of_isAtom {s : Set α} (h : ∀ ⦃x⦄, x ∈ s → IsAtom x) : QUA s :=
  fun _ ha _ hb hne hle ↦ hne (((h hb).le_iff_eq (h ha).1).1 hle)

/-- The atoms below `x`, its atomic parts. -/
def atomsBelow (x : α) : Set α := {a | IsAtom a ∧ a ≤ x}

@[simp] theorem mem_atomsBelow : y ∈ atomsBelow x ↔ IsAtom y ∧ y ≤ x := Iff.rfl

theorem atomsBelow_of_isAtom (h : IsAtom x) : atomsBelow x = {x} :=
  Set.ext fun _ ↦ ⟨fun hy ↦ (h.le_iff_eq hy.1.1).1 hy.2, by rintro rfl; exact ⟨h, le_rfl⟩⟩

/-- `count Z x` is the number of parts of `x` in `Z`, the cardinality of `x` relative to `Z`
([landman-2020]). -/
noncomputable def count (Z : Set α) (x : α) : ℕ := (Set.Iic x ∩ Z).ncard

variable (α) in
/-- `atomCount α x` is the number of atoms below `x` ([champollion-krifka-2016]). -/
noncomputable def atomCount (x : α) : ℕ := count {a | IsAtom a} x

theorem atomCount_eq_ncard (x : α) : atomCount α x = (atomsBelow x).ncard :=
  congrArg Set.ncard (Set.ext fun _ ↦ and_comm)

theorem atomize_ne_bot : atomize {x : α | x ≠ ⊥} = {x | IsAtom x} :=
  Set.ext fun _ ↦ isAtom_iff_le_of_ge.symm

end Atoms

theorem not_isAtom_sup_of_ne [SemilatticeSup α] [OrderBot α] {x y : α} (hx : IsAtom x)
    (hy : IsAtom y) (hne : x ≠ y) : ¬ IsAtom (x ⊔ y) :=
  fun h ↦ hne (((h.le_iff_eq hx.1).1 le_sup_left).trans ((h.le_iff_eq hy.1).1 le_sup_right).symm)

/-! ### Pluralities -/

section Plural

variable [SemilatticeSup α] {s : Set α} {x : α}

/-- A proper plurality of a region ([link-1983]) is a sum of its members with two distinct proper
parts in it. -/
def IsPlural (s : Set α) (x : α) : Prop :=
  x ∈ supClosure s ∧ ∃ a < x, ∃ b < x, a ∈ s ∧ b ∈ s ∧ a ≠ b

theorem not_isPlural_of_subsingleton (h : s.Subsingleton) (x : α) : ¬ IsPlural s x :=
  fun ⟨_, _, _, _, _, ha, hb, hne⟩ ↦ hne (h ha hb)

variable [OrderBot α]

theorem mem_of_mem_supClosure_of_isAtom (hx : x ∈ supClosure s) (h : IsAtom x) : x ∈ s := by
  induction hx using supClosure_induction with
  | mem a ha => exact ha
  | sup a b _ _ iha ihb =>
    by_cases ha : a = ⊥
    · rw [ha, bot_sup_eq] at h ⊢
      exact ihb h
    · have heq := (h.le_iff_eq ha).1 le_sup_left
      rw [← heq] at h ⊢
      exact iha h

theorem isPlural_iff_of_isAtom (hs : ∀ ⦃a⦄, a ∈ s → IsAtom a) :
    IsPlural s x ↔ x ∈ supClosure s ∧ ¬ IsAtom x := by
  constructor
  · rintro ⟨hx, a, ha, -, -, hPa, -, -⟩
    exact ⟨hx, fun h ↦ ha.ne ((h.le_iff_eq (hs hPa).1).1 ha.le)⟩
  · rintro ⟨hx, hne⟩
    refine ⟨hx, ?_⟩
    induction hx using supClosure_induction with
    | mem a h => exact absurd (hs h) hne
    | sup y z hy hz ihy ihz =>
      by_cases hay : IsAtom y
      · by_cases haz : IsAtom z
        · refine ⟨y, lt_of_le_of_ne le_sup_left fun h ↦ hne (by rw [← h]; exact hay),
            z, lt_of_le_of_ne le_sup_right fun h ↦ hne (by rw [← h]; exact haz),
            mem_of_mem_supClosure_of_isAtom hy hay, mem_of_mem_supClosure_of_isAtom hz haz,
            fun h ↦ hne ?_⟩
          subst h
          rwa [sup_idem]
        · obtain ⟨a, ha, b, hb, hPa, hPb, hab⟩ := ihz haz
          exact ⟨a, ha.trans_le le_sup_right, b, hb.trans_le le_sup_right, hPa, hPb, hab⟩
      · obtain ⟨a, ha, b, hb, hPa, hPb, hab⟩ := ihy hay
        exact ⟨a, ha.trans_le le_sup_left, b, hb.trans_le le_sup_left, hPa, hPb, hab⟩

theorem atomize_mem_supClosure (hs : ∀ ⦃a⦄, a ∈ s → IsAtom a) :
    atomize (supClosure s) = s := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ⟨subset_supClosure hx, fun y hy hyx ↦ ?_⟩⟩
  · obtain ⟨a, ha, hax⟩ := exists_le_of_mem_supClosure hx.prop
    exact hx.eq_of_le (subset_supClosure ha) hax ▸ ha
  · obtain ⟨b, hb, hby⟩ := exists_le_of_mem_supClosure hy
    rw [← ((hs hx).le_iff_eq (hs hb).1).1 (hby.trans hyx)]
    exact hby

end Plural

/-! ### Finite sets -/

instance {β : Type*} (s : Finset β) : Decidable (IsAtom s) :=
  decidable_of_iff (s.card = 1) (Finset.isAtom_iff.trans Finset.card_eq_one.symm).symm

theorem isAtom_finset_iff_card_eq_one {β : Type*} {s : Finset β} : IsAtom s ↔ s.card = 1 :=
  Finset.isAtom_iff.trans Finset.card_eq_one.symm

/-- The atomic parts of a finite set are its singletons. -/
theorem atomsBelow_finset {β : Type*} (s : Finset β) :
    atomsBelow s = (fun b ↦ ({b} : Finset β)) '' ↑s := by
  ext a
  simp only [mem_atomsBelow, Finset.isAtom_iff, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨⟨b, rfl⟩, h⟩
    exact ⟨b, Finset.singleton_subset_iff.1 h, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, rfl⟩, Finset.singleton_subset_iff.2 hb⟩

/-- A finite set has as many atomic parts as members. -/
theorem atomCount_finset {β : Type*} (s : Finset β) : atomCount (Finset β) s = s.card := by
  rw [atomCount_eq_ncard, atomsBelow_finset,
    Set.ncard_image_of_injective _ Finset.singleton_injective, Set.ncard_coe_finset]

end Mereology
