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
reference properties of predicates are then mathlib set predicates: cumulativity is
`SupClosed`, divisiveness `IsLowerSet` and quantization `IsAntichain (· ≤ ·)`, and Link's
closure `*P` is `supClosure`, so a predicate is quantized and cumulative
[only if it holds of at most one element](##Mereology.qua_and_cum_iff_subsingleton). A carrier
may have a null individual, as a Boolean algebra does, or none, as a classical mereology does.
Atoms and overlap are stated relative to mathlib's `IsBot`, so on an `OrderBot` carrier they
are [`IsAtom`](##Mereology.atom_iff_isAtom) and
[`¬ Disjoint`](##Mereology.overlap_iff_not_disjoint).

## Implementation notes

`AlgClosure` closes under binary sums, which agrees with closure under sums of arbitrary
nonempty subsets only for finite sums.

## References

* [bylinina-nouwen-2018], [champollion-krifka-2016], [krifka-1989], [krifka-1998], [link-1983]
-/

@[expose] public section

namespace Mereology

variable {α β : Type*}

/-! ### Reference properties

Cumulative, divisive and quantized reference are the mathlib set predicates
`SupClosed`, `IsLowerSet` and `IsAntichain (· ≤ ·)` on the extension of a predicate,
so hypotheses of these forms are applied directly: `hC hx hy : P (x ⊔ y)`,
`hD hle hx : P y`, `hQ hx hy hne : ¬ x ≤ y`. -/

/-- A predicate has divisive reference if every part of a `P`-element is `P`. -/
abbrev DIV [Preorder α] (P : α → Prop) : Prop := IsLowerSet {x | P x}

section PartialOrder

variable [PartialOrder α] {P : α → Prop}

/-- A predicate has quantized reference ([krifka-1989]) if no proper part of a `P`-element is
`P`. -/
abbrev QUA (P : α → Prop) : Prop := IsAntichain (· ≤ ·) {x | P x}

theorem qua_of_forall (h : ∀ x y, P x → y < x → ¬ P y) : QUA P :=
  fun _ ha _ hb hne hle ↦ h _ _ hb (lt_of_le_of_ne hle hne) ha

theorem singleton_qua (n : α) : QUA (· = n) :=
  Set.Subsingleton.isAntichain (s := {x | x = n}) (fun _ ha _ hb ↦ ha.trans hb.symm) _

theorem qua_pullback [PartialOrder β] {d : α → β} (hd : StrictMono d) {P : β → Prop}
    (hP : QUA P) : QUA (P ∘ d) :=
  fun _ ha _ hb hab hle ↦ hP ha hb (hd (hle.lt_of_ne hab)).ne (hd (hle.lt_of_ne hab)).le

/-- The `P`-atoms ([krifka-1989]) are the minimal `P`-elements. -/
abbrev atomize (P : α → Prop) : α → Prop := Minimal P

theorem atomize_qua : QUA (atomize P) := setOfPred_minimal_antichain P

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup α] {P : α → Prop}

/-- A predicate has cumulative reference ([link-1983], [krifka-1989]) if it is closed under
sum. [krifka-1998] also requires two distinct members, and [champollion-krifka-2016] give a form
closed under sums of arbitrary nonempty subsets. -/
abbrev CUM (P : α → Prop) : Prop := SupClosed {x | P x}

instance [Fintype α] [DecidablePred P] : Decidable (CUM P) :=
  decidable_of_iff (∀ x, P x → ∀ y, P y → P (x ⊔ y)) Iff.rfl

/-- A predicate is both quantized and cumulative iff it holds of at most one element: the two
parts of a sum that the predicate holds of are the sum itself. So a quantized predicate with two
members is not cumulative ([krifka-1989] (T 3)). -/
theorem qua_and_cum_iff_subsingleton : QUA P ∧ CUM P ↔ {x | P x}.Subsingleton :=
  ⟨fun ⟨hQ, hC⟩ _ hx _ hy ↦
      (hQ.eq hx (hC hx hy) le_sup_left).trans (hQ.eq hy (hC hx hy) le_sup_right).symm,
    fun h ↦ ⟨h.isAntichain _, fun x hx y hy ↦ by rw [h hx hy, sup_idem]; exact hy⟩⟩

theorem cum_maximal_iff_isGreatest (hCum : CUM P) {x : α} :
    Maximal P x ↔ IsGreatest {y | P y} x :=
  ⟨fun hx ↦ ⟨hx.1, fun _ hy ↦ le_sup_right.trans (hx.2 (hCum hx.1 hy) le_sup_left)⟩,
    fun hx ↦ ⟨hx.1, fun _ hy _ ↦ hx.2 hy⟩⟩

theorem cum_maximal_unique (hCum : CUM P) {x y : α} (hx : Maximal P x) (hy : Maximal P y) :
    x = y :=
  ((cum_maximal_iff_isGreatest hCum).1 hx).unique ((cum_maximal_iff_isGreatest hCum).1 hy)

/-! ### Algebraic closure -/

/-- The algebraic closure `*P` of `P` ([link-1983]) is the least predicate containing `P` and
closed under binary sum, the predicate of mathlib's `supClosure`. -/
abbrev AlgClosure (P : α → Prop) : α → Prop := (· ∈ supClosure {x | P x})

/-- Every `P`-element is in `*P`. -/
theorem AlgClosure.base {x : α} (h : P x) : AlgClosure P x := subset_supClosure h

/-- `*P` is closed under sum. -/
theorem AlgClosure.sum {x y : α} (hx : AlgClosure P x) (hy : AlgClosure P y) :
    AlgClosure P (x ⊔ y) :=
  supClosed_supClosure hx hy

/-- Induction on sums: a property of the `P`-elements that sums preserve holds throughout
`*P`. -/
@[elab_as_elim]
theorem AlgClosure.induction {motive : (x : α) → AlgClosure P x → Prop}
    (base : ∀ {x} (h : P x), motive x (.base h))
    (sum : ∀ {x y} (hx : AlgClosure P x) (hy : AlgClosure P y), motive x hx → motive y hy →
      motive (x ⊔ y) (hx.sum hy))
    {x : α} (h : AlgClosure P x) : motive x h :=
  supClosure_induction (fun _ ha ↦ base ha) (fun _ _ ha hb ↦ sum ha hb) h

theorem algClosure_cum : CUM (AlgClosure P) := supClosed_supClosure

theorem algClosure_mono {Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∀ x, AlgClosure P x → AlgClosure Q x :=
  fun _ hx ↦ supClosure_mono (fun x hx ↦ h x hx) hx

theorem algClosure_finsetSup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → α}
    (hf : ∀ i ∈ s, AlgClosure P (f i)) : AlgClosure P (s.sup' hs f) :=
  SupClosed.finsetSup'_mem algClosure_cum hs hf

theorem AlgClosure.map {β : Type*} [SemilatticeSup β] {Q : β → Prop} {f : α → β}
    (hf : ∀ x y, f (x ⊔ y) = f x ⊔ f y) (h : ∀ x, P x → Q (f x)) {x : α}
    (hx : AlgClosure P x) : AlgClosure Q (f x) := by
  induction hx using AlgClosure.induction with
  | base hx => exact .base (h _ hx)
  | sum _ _ ih ih' => exact hf _ _ ▸ ih.sum ih'

theorem algClosure_has_base {x : α} (h : AlgClosure P x) : ∃ a, P a ∧ a ≤ x := by
  induction h using AlgClosure.induction with
  | base hp => exact ⟨_, hp, le_rfl⟩
  | sum _ _ ih₁ _ => obtain ⟨a, ha, hle⟩ := ih₁; exact ⟨a, ha, hle.trans le_sup_left⟩

theorem algClosure_of_cum (hCum : CUM P) {x : α} : AlgClosure P x ↔ P x :=
  Set.ext_iff.1 hCum.supClosure_eq x

theorem algClosure_iff_exists_sup' (P : α → Prop) (x : α) :
    AlgClosure P x ↔ ∃ (t : Finset α) (ht : t.Nonempty), (∀ y ∈ t, P y) ∧ t.sup' ht id = x :=
  Iff.rfl

section OrderBot

variable [OrderBot α]

/-- The full algebraic closure `×P` adds the empty sum `⊥` to `*P`, closing `P` under the sums of
all finite families, the empty one included ([bylinina-nouwen-2018]'s (30)). -/
def FullAlgClosure (P : α → Prop) (x : α) : Prop :=
  AlgClosure P x ∨ x = ⊥

theorem fullAlgClosure_bot (P : α → Prop) : FullAlgClosure P ⊥ := .inr rfl

theorem AlgClosure.fullAlgClosure {x : α} (h : AlgClosure P x) : FullAlgClosure P x := .inl h

theorem fullAlgClosure_iff_exists_sup (P : α → Prop) (x : α) :
    FullAlgClosure P x ↔ ∃ t : Finset α, (∀ y ∈ t, P y) ∧ t.sup id = x := by
  rw [FullAlgClosure, algClosure_iff_exists_sup']
  constructor
  · rintro (⟨t, ht, hP, rfl⟩ | rfl)
    · exact ⟨t, hP, (Finset.sup'_eq_sup ht id).symm⟩
    · exact ⟨∅, by simp, Finset.sup_empty⟩
  · rintro ⟨t, hP, rfl⟩
    rcases t.eq_empty_or_nonempty with rfl | ht
    · exact .inr Finset.sup_empty
    · exact .inl ⟨t, ht, hP, Finset.sup'_eq_sup ht id⟩

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

theorem qua_of_atom {P : α → Prop} (h : ∀ ⦃x⦄, P x → Atom x) : QUA P :=
  (atomize_qua (P := (¬ IsBot ·))).subset h

theorem exists_atom_le [WellFoundedLT α] (hy : ¬ IsBot y) : ∃ a, Atom a ∧ a ≤ y := by
  obtain ⟨a, ⟨ha, hay⟩, hmin⟩ :=
    WellFounded.has_min wellFounded_lt {z | ¬ IsBot z ∧ z ≤ y} ⟨y, hy, le_rfl⟩
  exact ⟨a, ⟨ha, fun z hz hza ↦ (eq_of_le_of_not_lt hza (hmin z ⟨hz, hza.trans hay⟩)).ge⟩, hay⟩

/-- The atoms below `x`, its atomic parts. -/
def atomsBelow (x : α) : Set α := {a | Atom a ∧ a ≤ x}

@[simp] theorem mem_atomsBelow : y ∈ atomsBelow x ↔ Atom y ∧ y ≤ x := Iff.rfl

theorem atomsBelow_of_atom (h : Atom x) : atomsBelow x = {x} :=
  Set.ext fun _ ↦ ⟨fun hy ↦ h.eq hy.2 hy.1.not_isBot, by rintro rfl; exact ⟨h, le_rfl⟩⟩

variable (α) in
/-- `atomCount α x` is the number of atoms below `x` ([champollion-krifka-2016]). -/
noncomputable def atomCount (x : α) : ℕ := (atomsBelow x).ncard

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

variable [SemilatticeSup α] {P : α → Prop} {x : α}

/-- A proper plurality of `P`s ([link-1983]) is a sum of `P`-elements with two distinct proper
`P`-parts. -/
def IsPlural (P : α → Prop) (x : α) : Prop :=
  AlgClosure P x ∧ ∃ a < x, ∃ b < x, P a ∧ P b ∧ a ≠ b

theorem not_isPlural_of_subsingleton (h : ∀ a b, P a → P b → a = b) (x : α) : ¬ IsPlural P x :=
  fun ⟨_, _, _, _, _, ha, hb, hne⟩ ↦ hne (h _ _ ha hb)

theorem of_algClosure_of_atom (hx : AlgClosure P x) (h : Atom x) : P x := by
  induction hx using AlgClosure.induction with
  | base hp => exact hp
  | @sum a b _ _ iha ihb =>
    by_cases ha : IsBot a
    · rw [sup_eq_right.mpr (ha _)] at h ⊢
      exact ihb h
    · have heq := h.eq le_sup_left ha
      rw [← heq] at h ⊢
      exact iha h

theorem isPlural_iff_of_atom (hP : ∀ ⦃a⦄, P a → Atom a) :
    IsPlural P x ↔ AlgClosure P x ∧ ¬ Atom x := by
  constructor
  · rintro ⟨hx, a, ha, -, -, hPa, -, -⟩
    exact ⟨hx, fun h ↦ ha.ne (h.eq ha.le (hP hPa).not_isBot)⟩
  · rintro ⟨hx, hne⟩
    refine ⟨hx, ?_⟩
    induction hx using AlgClosure.induction with
    | base h => exact absurd (hP h) hne
    | @sum y z hy hz ihy ihz =>
      by_cases hay : Atom y
      · by_cases haz : Atom z
        · refine ⟨y, lt_of_le_of_ne le_sup_left fun h ↦ hne (by rw [← h]; exact hay),
            z, lt_of_le_of_ne le_sup_right fun h ↦ hne (by rw [← h]; exact haz),
            of_algClosure_of_atom hy hay, of_algClosure_of_atom hz haz, fun h ↦ hne ?_⟩
          subst h
          rwa [sup_idem]
        · obtain ⟨a, ha, b, hb, hPa, hPb, hab⟩ := ihz haz
          exact ⟨a, ha.trans_le le_sup_right, b, hb.trans_le le_sup_right, hPa, hPb, hab⟩
      · obtain ⟨a, ha, b, hb, hPa, hPb, hab⟩ := ihy hay
        exact ⟨a, ha.trans_le le_sup_left, b, hb.trans_le le_sup_left, hPa, hPb, hab⟩

theorem atomize_algClosure (hP : ∀ ⦃a⦄, P a → Atom a) : atomize (AlgClosure P) = P := by
  funext x
  refine propext ⟨fun hx ↦ ?_, fun hx ↦ ⟨.base hx, fun y hy hyx ↦ ?_⟩⟩
  · obtain ⟨a, ha, hax⟩ := algClosure_has_base hx.prop
    exact hx.eq_of_le (.base ha) hax ▸ ha
  · obtain ⟨b, hb, hby⟩ := algClosure_has_base hy
    rw [← (hP hx).eq (hby.trans hyx) (hP hb).not_isBot]
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

theorem atomize_ne_bot : atomize (· ≠ (⊥ : α)) = IsAtom := by
  funext x; exact propext isAtom_iff_le_of_ge.symm

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
  rw [atomCount, atomsBelow_finset, Set.ncard_image_of_injective _ Finset.singleton_injective,
    Set.ncard_coe_finset]

theorem atom_iff_isMin [PartialOrder α] [NoBotOrder α] {x : α} : Atom x ↔ IsMin x :=
  ⟨fun h _ hy ↦ h.2 (not_isBot _) hy, fun h ↦ ⟨not_isBot x, fun _ _ hy ↦ h hy⟩⟩

end Mereology
