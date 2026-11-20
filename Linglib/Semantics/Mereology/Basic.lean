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
member (`Mereology.qua_and_cum_iff_subsingleton`). A carrier
may have a null individual, as a Boolean algebra does, or none, as a classical mereology does.
Atoms and overlap are stated relative to mathlib's `IsBot`, so on an `OrderBot` carrier they
are [`IsAtom`](##Mereology.atom_iff_isAtom) and
[`¬ Disjoint`](##Mereology.overlap_iff_not_disjoint).

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

The null individual of a carrier, if it has one, is its `IsBot` element: `⊥` on an
`OrderBot` carrier, and nothing on a `NoBotOrder` carrier or a classical mereology. -/

section Atoms

variable [PartialOrder α] {x y : α}

instance [OrderBot α] [DecidableEq α] (x : α) : Decidable (IsBot x) :=
  decidable_of_iff (x = ⊥) isBot_iff_eq_bot.symm

instance [Fintype α] [DecidableLE α] (x : α) : Decidable (IsBot x) :=
  inferInstanceAs (Decidable (∀ y, x ≤ y))

/-- An atom ([link-1983]) is a non-null element with no non-null proper part, that is, a minimal
non-null element. The `P`-relative notion is `atomize`. -/
abbrev Atom (x : α) : Prop := Minimal (¬ IsBot ·) x

theorem Atom.not_isBot (h : Atom x) : ¬ IsBot x := h.1

/-- An atom's only non-null part is itself. -/
theorem Atom.eq (h : Atom x) (hle : y ≤ x) (hy : ¬ IsBot y) : y = x :=
  le_antisymm hle (h.2 hy hle)

theorem qua_of_atom {s : Set α} (h : ∀ ⦃x⦄, x ∈ s → Atom x) : QUA s :=
  (atomize_qua (s := {x | ¬ IsBot x})).subset h

theorem exists_atom_le [WellFoundedLT α] (hy : ¬ IsBot y) : ∃ a, Atom a ∧ a ≤ y := by
  obtain ⟨a, ⟨ha, hay⟩, hmin⟩ :=
    WellFounded.has_min wellFounded_lt {z | ¬ IsBot z ∧ z ≤ y} ⟨y, hy, le_rfl⟩
  exact ⟨a, ⟨ha, fun z hz hza ↦ (eq_of_le_of_not_lt hza (hmin z ⟨hz, hza.trans hay⟩)).ge⟩, hay⟩

/-- The atoms below `x`, its atomic parts. -/
def atomsBelow (x : α) : Set α := {a | Atom a ∧ a ≤ x}

@[simp] theorem mem_atomsBelow : y ∈ atomsBelow x ↔ Atom y ∧ y ≤ x := Iff.rfl

theorem atomsBelow_of_atom (h : Atom x) : atomsBelow x = {x} :=
  Set.ext fun _ ↦ ⟨fun hy ↦ h.eq hy.2 hy.1.not_isBot, by rintro rfl; exact ⟨h, le_rfl⟩⟩

/-- `count Z x` is the number of parts of `x` in `Z`, the cardinality of `x` relative to `Z`
([landman-2020]). -/
noncomputable def count (Z : Set α) (x : α) : ℕ := (Set.Iic x ∩ Z).ncard

variable (α) in
/-- `atomCount α x` is the number of atoms below `x` ([champollion-krifka-2016]). -/
noncomputable def atomCount (x : α) : ℕ := count {a | Atom a} x

theorem atomCount_eq_ncard (x : α) : atomCount α x = (atomsBelow x).ncard :=
  congrArg Set.ncard (Set.ext fun _ ↦ and_comm)

/-- Two elements overlap ([krifka-1998]) if they share a non-null part. -/
def Overlap (x y : α) : Prop := ∃ z, ¬ IsBot z ∧ z ≤ x ∧ z ≤ y

theorem Overlap.refl (h : ¬ IsBot x) : Overlap x x := ⟨x, h, le_rfl, le_rfl⟩

theorem Overlap.symm (h : Overlap x y) : Overlap y x :=
  let ⟨z, hz, hzx, hzy⟩ := h; ⟨z, hz, hzy, hzx⟩

theorem Overlap.not_isBot_left (h : Overlap x y) : ¬ IsBot x :=
  let ⟨_, hz, hzx, _⟩ := h; fun hx ↦ hz (hx.mono hzx)

theorem Overlap.not_isBot_right (h : Overlap x y) : ¬ IsBot y := h.symm.not_isBot_left

theorem Overlap.of_le (hx : ¬ IsBot x) (h : x ≤ y) : Overlap x y := ⟨x, hx, le_rfl, h⟩

theorem Overlap.mono {x' y' : α} (hx : x ≤ x') (hy : y ≤ y') (h : Overlap x y) : Overlap x' y' :=
  let ⟨z, hz, hzx, hzy⟩ := h; ⟨z, hz, hzx.trans hx, hzy.trans hy⟩

end Atoms

theorem not_atom_sup_of_ne [SemilatticeSup α] {x y : α} (hx : Atom x) (hy : Atom y) (hne : x ≠ y) :
    ¬ Atom (x ⊔ y) :=
  fun h ↦ hne ((h.eq le_sup_left hx.not_isBot).trans (h.eq le_sup_right hy.not_isBot).symm)

/-! ### Pluralities -/

section Plural

variable [SemilatticeSup α] {s : Set α} {x : α}

/-- A proper plurality of a region ([link-1983]) is a sum of its members with two distinct proper
parts in it. -/
def IsPlural (s : Set α) (x : α) : Prop :=
  x ∈ supClosure s ∧ ∃ a < x, ∃ b < x, a ∈ s ∧ b ∈ s ∧ a ≠ b

theorem not_isPlural_of_subsingleton (h : s.Subsingleton) (x : α) : ¬ IsPlural s x :=
  fun ⟨_, _, _, _, _, ha, hb, hne⟩ ↦ hne (h ha hb)

theorem mem_of_mem_supClosure_of_atom (hx : x ∈ supClosure s) (h : Atom x) : x ∈ s := by
  induction hx using supClosure_induction with
  | mem a ha => exact ha
  | sup a b _ _ iha ihb =>
    by_cases ha : IsBot a
    · rw [sup_eq_right.mpr (ha _)] at h ⊢
      exact ihb h
    · have heq := h.eq le_sup_left ha
      rw [← heq] at h ⊢
      exact iha h

theorem isPlural_iff_of_atom (hs : ∀ ⦃a⦄, a ∈ s → Atom a) :
    IsPlural s x ↔ x ∈ supClosure s ∧ ¬ Atom x := by
  constructor
  · rintro ⟨hx, a, ha, -, -, hPa, -, -⟩
    exact ⟨hx, fun h ↦ ha.ne (h.eq ha.le (hs hPa).not_isBot)⟩
  · rintro ⟨hx, hne⟩
    refine ⟨hx, ?_⟩
    induction hx using supClosure_induction with
    | mem a h => exact absurd (hs h) hne
    | sup y z hy hz ihy ihz =>
      by_cases hay : Atom y
      · by_cases haz : Atom z
        · refine ⟨y, lt_of_le_of_ne le_sup_left fun h ↦ hne (by rw [← h]; exact hay),
            z, lt_of_le_of_ne le_sup_right fun h ↦ hne (by rw [← h]; exact haz),
            mem_of_mem_supClosure_of_atom hy hay, mem_of_mem_supClosure_of_atom hz haz,
            fun h ↦ hne ?_⟩
          subst h
          rwa [sup_idem]
        · obtain ⟨a, ha, b, hb, hPa, hPb, hab⟩ := ihz haz
          exact ⟨a, ha.trans_le le_sup_right, b, hb.trans_le le_sup_right, hPa, hPb, hab⟩
      · obtain ⟨a, ha, b, hb, hPa, hPb, hab⟩ := ihy hay
        exact ⟨a, ha.trans_le le_sup_left, b, hb.trans_le le_sup_left, hPa, hPb, hab⟩

theorem atomize_mem_supClosure (hs : ∀ ⦃a⦄, a ∈ s → Atom a) :
    atomize (supClosure s) = s := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ⟨subset_supClosure hx, fun y hy hyx ↦ ?_⟩⟩
  · obtain ⟨a, ha, hax⟩ := exists_le_of_mem_supClosure hx.prop
    exact hx.eq_of_le (subset_supClosure ha) hax ▸ ha
  · obtain ⟨b, hb, hby⟩ := exists_le_of_mem_supClosure hy
    rw [← (hs hx).eq (hby.trans hyx) (hs hb).not_isBot]
    exact hby

end Plural

/-! ### Bounded and bottomless carriers -/

section OrderBot

variable [PartialOrder α] [OrderBot α] {x y : α}

theorem atom_iff_isAtom : Atom x ↔ IsAtom x := by
  simp only [Atom, Minimal, isBot_iff_eq_bot, isAtom_iff_le_of_ge, ne_eq]

theorem overlap_iff_not_disjoint : Overlap x y ↔ ¬ Disjoint x y := by
  constructor
  · rintro ⟨z, hz, hzx, hzy⟩ hd
    exact hz (isBot_iff_eq_bot.2 (le_bot_iff.mp (hd hzx hzy)))
  · intro hd
    by_contra h
    exact hd fun z hzx hzy ↦ le_bot_iff.mpr
      (by_contra fun hz ↦ h ⟨z, mt isBot_iff_eq_bot.1 hz, hzx, hzy⟩)

theorem atomize_ne_bot : atomize {x : α | x ≠ ⊥} = {x | IsAtom x} :=
  Set.ext fun _ ↦ isAtom_iff_le_of_ge.symm

end OrderBot

theorem atom_singleton {β : Type*} (b : β) : Atom ({b} : Finset β) :=
  atom_iff_isAtom.2 (Finset.isAtom_singleton b)

theorem atom_finset_iff {β : Type*} {s : Finset β} : Atom s ↔ ∃ b, s = {b} := by
  rw [atom_iff_isAtom, Finset.isAtom_iff]

theorem atom_finset_iff_card_eq_one {β : Type*} {s : Finset β} : Atom s ↔ s.card = 1 :=
  atom_finset_iff.trans Finset.card_eq_one.symm

/-- The atomic parts of a finite set are its singletons. -/
theorem atomsBelow_finset {β : Type*} (s : Finset β) :
    atomsBelow s = (fun b ↦ ({b} : Finset β)) '' ↑s := by
  ext a
  simp only [mem_atomsBelow, atom_iff_isAtom, Finset.isAtom_iff, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨⟨b, rfl⟩, h⟩
    exact ⟨b, Finset.singleton_subset_iff.1 h, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, rfl⟩, Finset.singleton_subset_iff.2 hb⟩

/-- A finite set has as many atomic parts as members. -/
theorem atomCount_finset {β : Type*} (s : Finset β) : atomCount (Finset β) s = s.card := by
  rw [atomCount_eq_ncard, atomsBelow_finset,
    Set.ncard_image_of_injective _ Finset.singleton_injective, Set.ncard_coe_finset]

theorem atom_iff_isMin [PartialOrder α] [NoBotOrder α] {x : α} : Atom x ↔ IsMin x :=
  ⟨fun h _ hy ↦ h.2 (not_isBot _) hy, fun h ↦ ⟨not_isBot x, fun _ _ hy ↦ h hy⟩⟩

end Mereology
