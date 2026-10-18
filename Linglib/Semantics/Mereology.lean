module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Atoms
public import Mathlib.Order.SupClosed
public import Mathlib.Order.Zorn
public import Linglib.Core.Data.Fintype.Order
public import Linglib.Core.Order.Antichain

/-!
# Algebraic mereology

Algebraic semantics models parthood as a partial order and mereological sum as join. The
reference properties of predicates are then mathlib set predicates: cumulativity is
`SupClosed`, divisiveness `IsLowerSet` and quantization `IsAntichain (· ≤ ·)`, and Link's
closure `*P` is `supClosure`. A carrier may have a null individual, as a Boolean algebra does,
or none, as a classical mereology does. Atoms and overlap are stated relative to mathlib's
`IsBot`, so on an `OrderBot` carrier they are `IsAtom` and `¬ Disjoint`.

## Main definitions

* `CUM`, `DIV`, `QUA`: cumulative, divisive and quantized reference.
* `AlgClosure P`: the closure of `P` under binary sum, and `FullAlgClosure P` with the empty sum.
* `Atom`, `Overlap`, `IsPlural`: atoms, overlap, and proper pluralities.
* `atomsBelow`, `atomCount`: the atomic parts of an element, and their number.
* `HasRemainders α`: every proper part is completed to the whole by a non-overlapping part.
* `IsClassicalMereology α`: classical extensional mereology, in which every inhabited predicate
  has a unique sum.
* `IsExtensiveMeasure μ`: extensive measure functions, and the measure phrases `QMOD` they build.
* `OverlapPred`, `DisjointPred`, `IsMaxDisjointIn`, `nullSchema`: individuation perspectives.

## Main results

* `qua_cum_incompatible`: a quantized predicate with two members is not cumulative.
* `IsClassicalMereology.existsUnique_remainder`: in a classical mereology a proper part has a
  unique remainder, so classical mereologies, like Boolean algebras, have remainders.
* `IsExtensiveMeasure.strictMono`: over a carrier with remainders an extensive measure is strictly
  monotone, so the measure phrases it builds are quantized (`qmod_qua`); the atom count is
  likewise extensive on sums of atoms (`qua_algClosure_atomCount`).
* `atomsBelow_finset`, `atomCount_finset`: the atomic parts of a finite set are its singletons,
  so its atom count is its cardinality.
* `nullSchema_eq`: every member of a predicate lies in some individuation perspective.

## Implementation notes

`AlgClosure` closes under binary sums, which agrees with closure under sums of arbitrary
nonempty subsets only for finite sums. Classical mereology is defined, as in Champollion's book,
by unique sums in Tarski's sense; Hovda compares the alternative axiomatizations. Since
`Overlap` excludes null parts, the element of a one-point carrier is null, so the trivial model
is not a classical mereology.

## References

* [bylinina-nouwen-2018], [champollion-krifka-2016], [champollion-2017], [hovda-2009],
  [krifka-1989], [krifka-1998], [landman-2011], [landman-2020], [link-1983], [sutton-filip-2021]
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

/-- Quantization in the paper's form holds if no `P`-element lies strictly below another. -/
theorem qua_of_forall (h : ∀ x y, P x → y < x → ¬ P y) : QUA P :=
  fun _ ha _ hb hne hle ↦ h _ _ hb (lt_of_le_of_ne hle hne) ha

/-- A singleton predicate is quantized ([krifka-1989] (T 1)). -/
theorem singleton_qua (n : α) : QUA (· = n) :=
  Set.Subsingleton.isAntichain (fun _ ha _ hb ↦ ha.trans hb.symm) _

/-- Quantization pulls back along strictly monotone maps. -/
theorem qua_pullback [PartialOrder β] {d : α → β} (hd : StrictMono d) {P : β → Prop}
    (hP : QUA P) : QUA (P ∘ d) :=
  hP.preimage_strictMono hd

/-- The `P`-atoms ([krifka-1989]) are the minimal `P`-elements. -/
abbrev atomize (P : α → Prop) : α → Prop := Minimal P

/-- The `P`-atoms are quantized. -/
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

/-- A quantized predicate with two members is not cumulative ([krifka-1989] (T 3)). -/
theorem qua_cum_incompatible (hQ : QUA P) {x y : α} (hx : P x) (hy : P y) (hne : x ≠ y) :
    ¬ CUM P := by
  intro hC
  have hxy : P (x ⊔ y) := hC hx hy
  rcases eq_or_lt_of_le (le_sup_left : x ≤ x ⊔ y) with hx_eq | hx_lt
  · rcases eq_or_lt_of_le (le_sup_right : y ≤ x ⊔ y) with hy_eq | hy_lt
    · exact hne (hx_eq.trans hy_eq.symm)
    · exact hQ hy hxy hy_lt.ne hy_lt.le
  · exact hQ hx hxy hx_lt.ne hx_lt.le

/-- A maximal element of a cumulative predicate is its greatest element, the supremum of
[champollion-krifka-2016]. -/
theorem cum_maximal_iff_isGreatest (hCum : CUM P) {x : α} :
    Maximal P x ↔ IsGreatest {y | P y} x :=
  ⟨fun hx ↦ ⟨hx.1, fun _ hy ↦ le_sup_right.trans (hx.2 (hCum hx.1 hy) le_sup_left)⟩,
    fun hx ↦ ⟨hx.1, fun _ hy _ ↦ hx.2 hy⟩⟩

/-- A cumulative predicate has at most one maximal element. -/
theorem cum_maximal_unique (hCum : CUM P) {x y : α} (hx : Maximal P x) (hy : Maximal P y) :
    x = y :=
  ((cum_maximal_iff_isGreatest hCum).1 hx).unique ((cum_maximal_iff_isGreatest hCum).1 hy)

/-! ### Algebraic closure -/

/-- The algebraic closure `*P` of `P` ([link-1983]) is the least predicate containing `P` and
closed under binary sum. The inductive presentation supports induction on sums;
`setOf_algClosure` identifies it with mathlib's `supClosure`. -/
inductive AlgClosure (P : α → Prop) : α → Prop where
  /-- Every `P`-element is in `*P`. -/
  | base {x : α} : P x → AlgClosure P x
  /-- `*P` is closed under sum. -/
  | sum {x y : α} : AlgClosure P x → AlgClosure P y → AlgClosure P (x ⊔ y)

theorem algClosure_cum : CUM (AlgClosure P) := fun _ hx _ hy ↦ .sum hx hy

theorem algClosure_mono {Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∀ x, AlgClosure P x → AlgClosure Q x := by
  intro x hx
  induction hx with
  | base hp => exact .base (h _ hp)
  | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂

/-- `*P` contains the sum of every nonempty finite family from `*P`. -/
theorem algClosure_finsetSup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → α}
    (hf : ∀ i ∈ s, AlgClosure P (f i)) : AlgClosure P (s.sup' hs f) :=
  SupClosed.finsetSup'_mem algClosure_cum hs hf

/-- Every element of `*P` has a `P`-element below it. -/
theorem algClosure_has_base {x : α} (h : AlgClosure P x) : ∃ a, P a ∧ a ≤ x := by
  induction h with
  | base hp => exact ⟨_, hp, le_rfl⟩
  | sum _ _ ih₁ _ => obtain ⟨a, ha, hle⟩ := ih₁; exact ⟨a, ha, hle.trans le_sup_left⟩

/-- A cumulative predicate is its own closure ([champollion-krifka-2016]). -/
theorem algClosure_of_cum (hCum : CUM P) {x : α} : AlgClosure P x ↔ P x :=
  ⟨fun h ↦ by induction h with
    | base h => exact h
    | sum _ _ ihx ihy => exact hCum ihx ihy,
   .base⟩

/-- `*P` is mathlib's `supClosure` of the extension of `P`. -/
theorem setOf_algClosure (P : α → Prop) : {x | AlgClosure P x} = supClosure {x | P x} :=
  Set.Subset.antisymm
    (fun _ h ↦ by
      induction (h : AlgClosure P _) with
      | base h => exact subset_supClosure h
      | sum _ _ ihx ihy => exact supClosed_supClosure ihx ihy)
    (supClosure_min (fun _ ↦ .base) algClosure_cum)

/-- `*P` holds of exactly the sums of nonempty finite families of `P`-elements, the finite case
of the closure of [champollion-krifka-2016] and [champollion-2017] under sums of nonempty
subsets. -/
theorem algClosure_iff_exists_sup' (P : α → Prop) (x : α) :
    AlgClosure P x ↔ ∃ (t : Finset α) (ht : t.Nonempty), (∀ y ∈ t, P y) ∧ t.sup' ht id = x := by
  rw [← Set.mem_ofPred_eq (p := AlgClosure P), setOf_algClosure]
  exact Iff.rfl

section OrderBot

variable [OrderBot α]

/-- The full algebraic closure `×P` adds the empty sum `⊥` to `*P`, closing `P` under the sums of
all finite families, the empty one included ([bylinina-nouwen-2018]'s (30)). -/
def FullAlgClosure (P : α → Prop) (x : α) : Prop :=
  AlgClosure P x ∨ x = ⊥

theorem fullAlgClosure_bot (P : α → Prop) : FullAlgClosure P ⊥ := .inr rfl

theorem AlgClosure.fullAlgClosure {x : α} (h : AlgClosure P x) : FullAlgClosure P x := .inl h

/-- `×P` holds of exactly the sums of finite families of `P`-elements. -/
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

/-- A predicate holding only of atoms is quantized. -/
theorem qua_of_atom {P : α → Prop} (h : ∀ ⦃x⦄, P x → Atom x) : QUA P :=
  (atomize_qua (P := (¬ IsBot ·))).subset h

/-- In a well-founded part order every non-null element has an atom below it, so finite
carriers are atomic ([champollion-krifka-2016]). -/
theorem exists_atom_le [WellFoundedLT α] (hy : ¬ IsBot y) : ∃ a, Atom a ∧ a ≤ y := by
  obtain ⟨a, ⟨ha, hay⟩, hmin⟩ :=
    WellFounded.has_min wellFounded_lt {z | ¬ IsBot z ∧ z ≤ y} ⟨y, hy, le_rfl⟩
  exact ⟨a, ⟨ha, fun z hz hza ↦ (eq_of_le_of_not_lt hza (hmin z ⟨hz, hza.trans hay⟩)).ge⟩, hay⟩

/-- The atoms below `x`, its atomic parts. -/
def atomsBelow (x : α) : Set α := {a | Atom a ∧ a ≤ x}

@[simp] theorem mem_atomsBelow : y ∈ atomsBelow x ↔ Atom y ∧ y ≤ x := Iff.rfl

/-- An atom is its own only atomic part. -/
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

/-- A non-null part of `y` overlaps `y`. -/
theorem Overlap.of_le (hx : ¬ IsBot x) (h : x ≤ y) : Overlap x y := ⟨x, hx, le_rfl, h⟩

theorem Overlap.mono {x' y' : α} (hx : x ≤ x') (hy : y ≤ y') (h : Overlap x y) : Overlap x' y' :=
  let ⟨z, hz, hzx, hzy⟩ := h; ⟨z, hz, hzx.trans hx, hzy.trans hy⟩

end Atoms

/-- The sum of two distinct atoms is not an atom. -/
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

/-- A predicate with at most one member has no plurality. -/
theorem not_isPlural_of_subsingleton (h : ∀ a b, P a → P b → a = b) (x : α) : ¬ IsPlural P x :=
  fun ⟨_, _, _, _, _, ha, hb, hne⟩ ↦ hne (h _ _ ha hb)

/-- An atom in the closure of a predicate is one of its members, since an atom is not a proper
sum. -/
theorem of_algClosure_of_atom (hx : AlgClosure P x) (h : Atom x) : P x := by
  induction hx with
  | base hp => exact hp
  | @sum a b _ _ iha ihb =>
    by_cases ha : IsBot a
    · rw [sup_eq_right.mpr (ha _)] at h ⊢
      exact ihb h
    · have heq := h.eq le_sup_left ha
      rw [← heq] at h ⊢
      exact iha h

/-- For a predicate holding only of atoms, a plurality is a non-atomic element of the closure. -/
theorem isPlural_iff_of_atom (hP : ∀ ⦃a⦄, P a → Atom a) :
    IsPlural P x ↔ AlgClosure P x ∧ ¬ Atom x := by
  constructor
  · rintro ⟨hx, a, ha, -, -, hPa, -, -⟩
    exact ⟨hx, fun h ↦ ha.ne (h.eq ha.le (hP hPa).not_isBot)⟩
  · rintro ⟨hx, hne⟩
    refine ⟨hx, ?_⟩
    induction hx with
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

/-- Atomizing the closure of a predicate holding only of atoms gives back the predicate. -/
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

/-- The atoms of the non-null predicate on a bounded carrier are its `IsAtom`s. -/
theorem atomize_ne_bot : atomize (· ≠ (⊥ : α)) = IsAtom := by
  funext x; exact propext isAtom_iff_le_of_ge.symm

end OrderBot

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

/-- Without a null individual, the atoms are the minimal elements. -/
theorem atom_iff_isMin [PartialOrder α] [NoBotOrder α] {x : α} : Atom x ↔ IsMin x :=
  ⟨fun h _ hy ↦ h.2 (not_isBot _) hy, fun h ↦ ⟨not_isBot x, fun _ _ hy ↦ h hy⟩⟩

/-! ### The remainder principle

A proper part of a whole is completed to the whole by a remainder that does not overlap it.
This is the remainder principle of [krifka-1998], the relative complementarity of
[krifka-1989], and the unique separation of [champollion-2017]. Boolean algebras satisfy it with
the difference `y \ x`, and so do classical mereologies (`IsClassicalMereology.exists_remainder`).
The sources also require the remainder to be unique; the results below need only existence. -/

/-- A part structure has remainders if every proper part `x` of `y` is completed to `y` by a
part that does not overlap `x`. -/
class HasRemainders (α : Type*) [SemilatticeSup α] : Prop where
  exists_remainder : ∀ ⦃x y : α⦄, x < y → ∃ z, ¬ Overlap z x ∧ x ⊔ z = y

instance [GeneralizedBooleanAlgebra α] : HasRemainders α where
  exists_remainder _ y h :=
    ⟨y \ _, overlap_iff_not_disjoint.not_left.2 disjoint_sdiff_self_left,
      sup_sdiff_cancel_right h.le⟩

/-! ### Classical mereology

Classical extensional mereology is the system of [champollion-krifka-2016] and
[champollion-2017]: a partial order in which every inhabited predicate has a unique sum in
Tarski's sense. Weak and strong supplementation, the remainder principle and the absence of a
null individual are theorems; [hovda-2009] compares this axiomatization with others. Binary sums
are fusions of pairs (`IsClassicalMereology.toSemilatticeSup`), and the nonempty subsets of a set
with two elements or more form a classical mereology. -/

section Classical

variable [PartialOrder α]

/-- `t` is a sum of the `P`-elements in Tarski's sense if it lies above each of them and each of
its parts overlaps one of them. -/
def IsFusion (P : α → Prop) (t : α) : Prop :=
  (∀ x, P x → x ≤ t) ∧ ∀ y, y ≤ t → ∃ x, P x ∧ Overlap y x

/-- A partial order is a classical extensional mereology if every inhabited predicate has a
unique sum. -/
class IsClassicalMereology (α : Type*) [PartialOrder α] : Prop where
  existsUnique_isFusion : ∀ P : α → Prop, (∃ x, P x) → ∃! t, IsFusion P t

namespace IsClassicalMereology

variable [IsClassicalMereology α] {x y u : α}

theorem exists_isFusion (P : α → Prop) (h : ∃ x, P x) : ∃ t, IsFusion P t :=
  (existsUnique_isFusion P h).exists

/-- A classical mereology has no null individual, since the predicate true of it alone would
have no sum. -/
theorem not_isBot (x : α) : ¬ IsBot x := fun hx ↦ by
  obtain ⟨t, ht⟩ := exists_isFusion (· = x) ⟨x, rfl⟩
  obtain ⟨_, rfl, w, hw, -, hwx⟩ := ht.2 t le_rfl
  exact hw (hx.mono hwx)

/-- In a classical mereology, overlap is sharing a part. -/
theorem overlap_iff : Overlap x y ↔ ∃ z, z ≤ x ∧ z ≤ y :=
  ⟨fun ⟨z, _, hzx, hzy⟩ ↦ ⟨z, hzx, hzy⟩, fun ⟨z, hzx, hzy⟩ ↦ ⟨z, not_isBot z, hzx, hzy⟩⟩

/-- Each element is the sum of itself. -/
theorem isFusion_eq (x : α) : IsFusion (· = x) x :=
  ⟨fun _ h ↦ h.le, fun z hz ↦ ⟨x, rfl, z, not_isBot z, le_rfl, hz⟩⟩

end IsClassicalMereology

variable [IsClassicalMereology α] {P : α → Prop} {s t x y u : α}

/-- Sums are unique. -/
theorem IsFusion.unique (hs : IsFusion P s) (ht : IsFusion P t) : s = t :=
  let ⟨x, hx, _⟩ := hs.2 s le_rfl
  (IsClassicalMereology.existsUnique_isFusion P ⟨x, hx⟩).unique hs ht

/-- A proper part of `y` leaves a part of `y` that does not overlap it (weak supplementation),
since otherwise `y` would be a second sum of the part alone. -/
theorem IsClassicalMereology.weak_supplementation (h : x < y) : ∃ z ≤ y, ¬ Overlap z x := by
  by_contra! hall
  exact h.ne ((IsClassicalMereology.isFusion_eq x).unique
    ⟨fun _ h' ↦ h' ▸ h.le, fun z hz ↦ ⟨x, rfl, hall z hz⟩⟩)

/-- A sum is a least upper bound, since weak supplementation forces the sum, an upper bound by
definition, to be the least one. -/
theorem IsFusion.isLUB (h : IsFusion P t) : IsLUB {x | P x} t := by
  refine ⟨fun a ha ↦ h.1 a ha, fun w hw ↦ ?_⟩
  obtain ⟨v, hv⟩ :=
    IsClassicalMereology.exists_isFusion (fun u ↦ u = w ∨ u = t) ⟨w, Or.inl rfl⟩
  have hwv : w ≤ v := hv.1 w (Or.inl rfl)
  have htv : t ≤ v := hv.1 t (Or.inr rfl)
  suffices hvw : v = w by rw [hvw] at htv; exact htv
  by_contra hne
  obtain ⟨s, hsv, hsw⟩ :=
    IsClassicalMereology.weak_supplementation (lt_of_le_of_ne hwv (Ne.symm hne))
  obtain ⟨u, hu, p, hp, hps, hpu⟩ := hv.2 s hsv
  rcases hu with rfl | rfl
  · exact hsw ⟨p, hp, hps, hpu⟩
  · obtain ⟨a, hPa, q, hq, hqp, hqa⟩ := h.2 p hpu
    exact hsw ⟨q, hq, hqp.trans hps, hqa.trans (hw hPa)⟩

namespace IsClassicalMereology

/-- If `y` is not part of `u`, some part of `y` does not overlap `u` (strong
supplementation). -/
theorem strong_supplementation (h : ¬ y ≤ u) : ∃ v ≤ y, ¬ Overlap v u := by
  obtain ⟨s, hs⟩ := exists_isFusion (fun w ↦ w = y ∨ w = u) ⟨y, .inl rfl⟩
  have hus : u < s := lt_of_le_of_ne (hs.1 u (.inr rfl)) fun he ↦ h (he ▸ hs.1 y (.inl rfl))
  obtain ⟨w, hws, hwu⟩ := weak_supplementation hus
  obtain ⟨p, rfl | rfl, hov⟩ := hs.2 w hws
  · obtain ⟨v, hv, hvw, hvy⟩ := hov
    exact ⟨v, hvy, fun ⟨q, hq, hqv, hqu⟩ ↦ hwu ⟨q, hq, hqv.trans hvw, hqu⟩⟩
  · exact absurd hov hwu

/-- A classical mereology satisfies the remainder principle, since the sum of the parts of `y`
that do not overlap `x` completes `x` to `y`. -/
theorem exists_remainder (h : x < y) : ∃ z, ¬ Overlap z x ∧ IsLUB {x, z} y := by
  obtain ⟨w₀, hw₀y, hw₀x⟩ := weak_supplementation h
  obtain ⟨z, hz⟩ := exists_isFusion (fun w ↦ w ≤ y ∧ ¬ Overlap w x) ⟨w₀, hw₀y, hw₀x⟩
  have hzy : z ≤ y := hz.isLUB.2 fun _ hw ↦ hw.1
  refine ⟨z, fun ⟨q, hq, hqz, hqx⟩ ↦ ?_, ⟨?_, fun u hu ↦ ?_⟩⟩
  · obtain ⟨r, ⟨_, hrx⟩, v, hv, hvq, hvr⟩ := hz.2 q hqz
    exact hrx ⟨v, hv, hvr, hvq.trans hqx⟩
  · rintro _ (rfl | rfl)
    exacts [h.le, hzy]
  · by_contra hyu
    obtain ⟨v, hvy, hvu⟩ := strong_supplementation hyu
    have hvz : v ≤ z := hz.isLUB.1
      ⟨hvy, fun ⟨q, hq, hqv, hqx⟩ ↦ hvu ⟨q, hq, hqv, hqx.trans (hu (.inl rfl))⟩⟩
    exact hvu ⟨v, not_isBot v, le_rfl, hvz.trans (hu (.inr rfl))⟩

/-- A classical mereology has no bottom element. -/
instance : NoBotOrder α := ⟨fun x ↦ not_forall.1 (not_isBot x)⟩

/-- An element all of whose parts overlap `u` is part of `u` (extensionality). -/
theorem le_of_forall_overlap (h : ∀ v ≤ y, Overlap v u) : y ≤ u := by
  by_contra hyu
  obtain ⟨v, hvy, hvu⟩ := strong_supplementation hyu
  exact hvu (h v hvy)

/-- The remainder of a proper part is unique, since each of two remainders lies in `y` and so
has every part overlapping `x` or the other remainder. -/
theorem remainder_unique {z z' : α} (hz : ¬ Overlap z x) (hlub : IsLUB {x, z} y)
    (hz' : ¬ Overlap z' x) (hlub' : IsLUB {x, z'} y) : z = z' := by
  have key : ∀ {z z' : α}, ¬ Overlap z x → IsLUB {x, z} y → IsLUB {x, z'} y → z ≤ z' := by
    intro z z' hz hlub hlub'
    obtain ⟨f, hf⟩ := exists_isFusion (fun u ↦ u = x ∨ u = z') ⟨x, .inl rfl⟩
    have hfy : f = y := hf.isLUB.unique
      (by rwa [show {u | u = x ∨ u = z'} = ({x, z'} : Set α) from by ext; simp])
    subst hfy
    refine le_of_forall_overlap fun v hv ↦ ?_
    obtain ⟨p, rfl | rfl, hov⟩ := hf.2 v (hv.trans (hlub.1 (by simp)))
    · exact absurd (hov.mono hv le_rfl) hz
    · exact hov
  exact le_antisymm (key hz hlub hlub') (key hz' hlub' hlub)

/-- A proper part of `y` has exactly one remainder in `y`, the unique separation of
[krifka-1998] and [champollion-2017]. -/
theorem existsUnique_remainder (h : x < y) : ∃! z, ¬ Overlap z x ∧ IsLUB {x, z} y :=
  let ⟨z, hz, hlub⟩ := exists_remainder h
  ⟨z, ⟨hz, hlub⟩, fun _ ⟨hz', hlub'⟩ ↦ remainder_unique hz' hlub' hz hlub⟩

/-- Every pair has a least upper bound, the sum of the pair. -/
theorem exists_isLUB_pair (a b : α) : ∃ s, IsLUB {a, b} s := by
  obtain ⟨t, ht⟩ := exists_isFusion (fun u ↦ u = a ∨ u = b) ⟨a, Or.inl rfl⟩
  refine ⟨t, ?_⟩
  have h := ht.isLUB
  rwa [show {x | x = a ∨ x = b} = ({a, b} : Set α) from by ext x; simp [Set.mem_insert_iff]] at h

/-- The binary sum `a ⊔ b` of a classical mereology is the sum of the pair `{a, b}`. -/
@[reducible] noncomputable def toSemilatticeSup : SemilatticeSup α :=
  { ‹PartialOrder α› with
    sup := fun a b ↦ Classical.choose (exists_isLUB_pair a b)
    le_sup_left := fun a b ↦ (Classical.choose_spec (exists_isLUB_pair a b)).1 (Set.mem_insert _ _)
    le_sup_right := fun a b ↦
      (Classical.choose_spec (exists_isLUB_pair a b)).1 (Set.mem_insert_of_mem _ rfl)
    sup_le := fun a b c ha hb ↦ (Classical.choose_spec (exists_isLUB_pair a b)).2 <| by
      rintro _ (rfl | rfl)
      exacts [ha, hb] }

end IsClassicalMereology

end Classical

instance [SemilatticeSup α] [IsClassicalMereology α] : HasRemainders α where
  exists_remainder _ _ h :=
    let ⟨z, hz, hlub⟩ := IsClassicalMereology.exists_remainder h
    ⟨z, hz, (hlub.unique isLUB_pair).symm⟩

section SetModel

variable {ι : Type*} [Nontrivial ι]

private theorem not_isBot_singleton (p : ι) :
    ¬ IsBot (⟨{p}, Set.singleton_nonempty p⟩ : {s : Set ι // s.Nonempty}) := fun h ↦ by
  obtain ⟨q, hq⟩ := exists_ne p
  exact hq (Set.singleton_subset_singleton.1 (h ⟨{q}, Set.singleton_nonempty q⟩)).symm

private theorem isFusion_iff_eq_iUnion {P : {s : Set ι // s.Nonempty} → Prop}
    {t : {s : Set ι // s.Nonempty}} : IsFusion P t ↔ t.1 = ⋃ (x) (_ : P x), x.1 := by
  constructor
  · rintro ⟨hub, hov⟩
    refine Set.Subset.antisymm (fun p hp ↦ ?_) (Set.iUnion₂_subset fun x hx ↦ hub x hx)
    obtain ⟨x, hx, w, -, hwp, hwx⟩ :=
      hov ⟨{p}, Set.singleton_nonempty p⟩ (Set.singleton_subset_iff.2 hp)
    obtain ⟨q, hq⟩ := w.2
    exact Set.mem_iUnion₂.2 ⟨x, hx, (hwp hq : q = p) ▸ hwx hq⟩
  · intro h
    refine ⟨fun x hx ↦ (Set.subset_iUnion₂ (s := fun x (_ : P x) ↦ x.1) x hx).trans h.ge,
      fun y hy ↦ ?_⟩
    obtain ⟨p, hp⟩ := y.2
    obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.1 (h ▸ hy hp : p ∈ ⋃ (x) (_ : P x), x.1)
    exact ⟨x, hx, ⟨{p}, Set.singleton_nonempty p⟩, not_isBot_singleton p,
      Set.singleton_subset_iff.2 hp, Set.singleton_subset_iff.2 hpx⟩

/-- The nonempty subsets of a set with two elements or more form a classical mereology whose
sums are unions ([champollion-2017]). -/
instance : IsClassicalMereology {s : Set ι // s.Nonempty} where
  existsUnique_isFusion P := by
    rintro ⟨x, hx⟩
    have hne : (⋃ (y) (_ : P y), y.1).Nonempty :=
      x.2.mono (Set.subset_iUnion₂ (s := fun y (_ : P y) ↦ y.1) x hx)
    exact ⟨⟨_, hne⟩, isFusion_iff_eq_iUnion.2 rfl,
      fun t ht ↦ Subtype.ext (isFusion_iff_eq_iUnion.1 ht)⟩

end SetModel

/-! ### Extensive measures

[krifka-1989] and [krifka-1998] define an extensive measure by additivity over non-overlapping
elements and positivity, and derive from the remainder principle that a proper part measures less
than the whole. [champollion-krifka-2016] call a measure extensive on a set when it has that
property there. Either way, the measure phrases such a measure builds are quantized. -/

/-- The measure phrase "`n` units of `R`" denotes the `R`-elements of measure `n`, as
[krifka-1989] analyses *five ounces of gold*. -/
def QMOD {M : Type*} (R : α → Prop) (μ : α → M) (n : M) : α → Prop := fun x ↦ R x ∧ μ x = n

/-- A measure phrase is quantized if its measure is strictly monotone on the predicate it
restricts. -/
theorem qmod_qua {M : Type*} [PartialOrder α] [Preorder M] {R : α → Prop} {μ : α → M}
    (hμ : StrictMonoOn μ {x | R x}) (n : M) : QUA (QMOD R μ n) :=
  fun _ hx _ hy hne hle ↦ (hμ hx.1 hy.1 (lt_of_le_of_ne hle hne)).ne (hx.2.trans hy.2.symm)

/-- On a finite carrier the atom count is strictly monotone on the closure of a predicate that
holds only of atoms. -/
theorem atomCount_strictMonoOn [SemilatticeSup α] [Fintype α] {P : α → Prop}
    (hP : ∀ ⦃a⦄, P a → Atom a) : StrictMonoOn (atomCount α) {x | AlgClosure P x} := by
  intro x _ y hy hxy
  obtain ⟨t, ht, hPt, rfl⟩ := (algClosure_iff_exists_sup' P y).1 hy
  have hsub : atomsBelow x ⊆ atomsBelow (t.sup' ht id) :=
    fun a ha ↦ ⟨ha.1, ha.2.trans hxy.le⟩
  obtain ⟨a, ha, hax⟩ : ∃ a ∈ t, ¬ a ≤ x := by
    by_contra! hno
    exact hxy.not_ge (Finset.sup'_le ht id hno)
  exact Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).2
    ⟨a, ⟨hP (hPt a ha), Finset.le_sup' id ha⟩, fun h ↦ hax h.2⟩) (Set.toFinite _)

/-- The sums of `P`-atoms with `n` atoms form an antichain, so *two cats* is quantized
([champollion-krifka-2016]). -/
theorem qua_algClosure_atomCount [SemilatticeSup α] [Fintype α] {P : α → Prop}
    (hP : ∀ ⦃a⦄, P a → Atom a) (n : ℕ) : QUA (QMOD (AlgClosure P) (atomCount α) n) :=
  qmod_qua (atomCount_strictMonoOn hP) n

section ExtensiveMeasure

variable {M : Type*} [SemilatticeSup α] [AddCommMonoid M] [PartialOrder M]

/-- An extensive measure function ([krifka-1989], [krifka-1998]) is additive over
non-overlapping elements and positive on non-null ones. -/
class IsExtensiveMeasure (μ : α → M) : Prop where
  additive : ∀ x y, ¬ Overlap x y → μ (x ⊔ y) = μ x + μ y
  positive : ∀ x, ¬ IsBot x → 0 < μ x

/-- Over a carrier with remainders, an extensive measure gives a proper part a smaller measure
than the whole, which adds a non-null remainder to it. -/
theorem IsExtensiveMeasure.strictMono [HasRemainders α] [AddLeftStrictMono M] (μ : α → M)
    [h : IsExtensiveMeasure μ] : StrictMono μ := fun x y hxy ↦ by
  obtain ⟨z, hz, rfl⟩ := HasRemainders.exists_remainder hxy
  rw [h.additive x z fun ho ↦ hz ho.symm]
  exact lt_add_of_pos_right _ (h.positive z fun hb ↦ hxy.ne (sup_eq_left.2 (hb x)).symm)

end ExtensiveMeasure

instance [DecidableEq β] : IsExtensiveMeasure (Finset.card : Finset β → ℕ) where
  additive _ _ h :=
    Finset.card_union_of_disjoint (not_not.mp (overlap_iff_not_disjoint.not.mp h))
  positive _ hx := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 (mt isBot_iff_eq_bot.2 hx))

/-! ### Individuation perspectives

A predicate is overlapping if two distinct members share a part, and disjoint otherwise; a
maximally disjoint subset is an individuation perspective ([landman-2011], [landman-2020]),
and the null schema of [sutton-filip-2021] unions all perspectives. The overlap relation
`ov` is a parameter (mereologically, `Overlap`). -/

section Individuation

variable (ov : α → α → Prop)

/-- A predicate overlaps if two distinct members share a part. -/
def OverlapPred (P : Set α) : Prop := ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ ov x y

/-- A predicate is disjoint if no two distinct members share a part. -/
def DisjointPred (P : Set α) : Prop := ¬ OverlapPred ov P

theorem disjointPred_iff_pairwise {P : Set α} : DisjointPred ov P ↔ P.Pairwise (¬ ov · ·) := by
  simp [DisjointPred, OverlapPred, Set.Pairwise]

theorem overlapPred_mono {P Q : Set α} (h : P ⊆ Q) (hP : OverlapPred ov P) : OverlapPred ov Q :=
  let ⟨x, hx, y, hy, hne, hov⟩ := hP; ⟨x, h hx, y, h hy, hne, hov⟩

theorem DisjointPred.anti {P Q : Set α} (h : P ⊆ Q) (hQ : DisjointPred ov Q) :
    DisjointPred ov P :=
  fun hP ↦ hQ (overlapPred_mono ov h hP)

/-- `D` is a maximally disjoint subset of `P` if it is disjoint and cannot be extended within `P`
without overlap. -/
def IsMaxDisjointIn (D P : Set α) : Prop :=
  D ⊆ P ∧ DisjointPred ov D ∧ ∀ x ∈ P, x ∉ D → OverlapPred ov (insert x D)

theorem isMaxDisjointIn_iff_maximal (D P : Set α) :
    IsMaxDisjointIn ov D P ↔ Maximal (fun D ↦ D ⊆ P ∧ DisjointPred ov D) D := by
  constructor
  · rintro ⟨hDP, hD, hmax⟩
    refine ⟨⟨hDP, hD⟩, fun D' ⟨hD'P, hD'⟩ hDD' x hx ↦ ?_⟩
    by_contra hxD
    exact hD' (overlapPred_mono ov (Set.insert_subset hx hDD') (hmax x (hD'P hx) hxD))
  · rintro ⟨⟨hDP, hD⟩, hmax⟩
    refine ⟨hDP, hD, fun x hxP hxD ↦ ?_⟩
    by_contra hno
    exact hxD (hmax ⟨Set.insert_subset hxP hDP, hno⟩ (Set.subset_insert x D) (Set.mem_insert x D))

/-- The null individuation schema of `P` is the union of its maximally disjoint subsets. -/
def nullSchema (P : Set α) : Set α := {x | ∃ D, IsMaxDisjointIn ov D P ∧ x ∈ D}

/-- The union of two distinct maximally disjoint subsets overlaps. -/
theorem overlapPred_union_of_maxDisjoint_ne {D₁ D₂ P : Set α} (h₁ : IsMaxDisjointIn ov D₁ P)
    (h₂ : IsMaxDisjointIn ov D₂ P) (hne : D₁ ≠ D₂) : OverlapPred ov (D₁ ∪ D₂) := by
  obtain ⟨x, hx₂, hx₁⟩ | ⟨x, hx₁, hx₂⟩ :
      (∃ x, x ∈ D₂ ∧ x ∉ D₁) ∨ (∃ x, x ∈ D₁ ∧ x ∉ D₂) := by
    by_contra hcon
    push Not at hcon
    exact hne (Set.Subset.antisymm hcon.2 hcon.1)
  · exact overlapPred_mono ov
      (Set.insert_subset_iff.mpr ⟨Or.inr hx₂, fun a ha ↦ Or.inl ha⟩)
      (h₁.2.2 x (h₂.1 hx₂) hx₁)
  · exact overlapPred_mono ov
      (Set.insert_subset_iff.mpr ⟨Or.inl hx₁, fun a ha ↦ Or.inr ha⟩)
      (h₂.2.2 x (h₁.1 hx₁) hx₂)

/-- The null schema of a predicate with two distinct perspectives overlaps. -/
theorem overlapPred_nullSchema {D₁ D₂ P : Set α} (h₁ : IsMaxDisjointIn ov D₁ P)
    (h₂ : IsMaxDisjointIn ov D₂ P) (hne : D₁ ≠ D₂) : OverlapPred ov (nullSchema ov P) :=
  overlapPred_mono ov
    (Set.union_subset (fun _ ha ↦ ⟨D₁, h₁, ha⟩) (fun _ ha ↦ ⟨D₂, h₂, ha⟩))
    (overlapPred_union_of_maxDisjoint_ne ov h₁ h₂ hne)

/-- A disjoint predicate is its own unique perspective. -/
theorem isMaxDisjointIn_self {P : Set α} (h : DisjointPred ov P) : IsMaxDisjointIn ov P P :=
  ⟨Set.Subset.rfl, h, fun _ hy hny ↦ absurd hy hny⟩

/-- Every member of a predicate lies in some perspective on it, since a disjoint subset
containing it extends to a maximal one. -/
theorem exists_isMaxDisjointIn_mem {P : Set α} {x : α} (hx : x ∈ P) :
    ∃ D, IsMaxDisjointIn ov D P ∧ x ∈ D := by
  obtain ⟨D, hxD, hD⟩ := zorn_subset_nonempty {D | D ⊆ P ∧ DisjointPred ov D}
    (fun c hc hchain _ ↦ ⟨⋃₀ c, ⟨Set.sUnion_subset fun D hD ↦ (hc hD).1,
      fun ⟨a, ⟨A, hA, haA⟩, b, ⟨B, hB, hbB⟩, hab, hov⟩ ↦
        (hchain.total hA hB).elim (fun hAB ↦ (hc hB).2 ⟨a, hAB haA, b, hbB, hab, hov⟩)
          (fun hBA ↦ (hc hA).2 ⟨a, haA, b, hBA hbB, hab, hov⟩)⟩,
      fun D hD ↦ Set.subset_sUnion_of_mem hD⟩)
    {x} ⟨Set.singleton_subset_iff.2 hx, fun ⟨a, ha, b, hb, hab, _⟩ ↦
      hab ((Set.mem_singleton_iff.1 ha).trans (Set.mem_singleton_iff.1 hb).symm)⟩
  refine ⟨D, ⟨hD.prop.1, hD.prop.2, fun y hy hyD ↦ ?_⟩, hxD rfl⟩
  by_contra hno
  exact hyD (hD.2 ⟨Set.insert_subset hy hD.prop.1, hno⟩ (Set.subset_insert _ _)
    (Set.mem_insert _ _))

/-- The null schema is the identity, since every member of a predicate is in some
perspective. -/
theorem nullSchema_eq (P : Set α) : nullSchema ov P = P :=
  Set.Subset.antisymm (fun _ ⟨_, hD, hx⟩ ↦ hD.1 hx)
    (fun _ hx ↦ let ⟨D, hD, hxD⟩ := exists_isMaxDisjointIn_mem ov hx; ⟨D, hD, hxD⟩)

end Individuation

/-- On a carrier with a null individual, a predicate is disjoint iff its members are pairwise
disjoint in the lattice sense. -/
theorem disjointPred_overlap_iff [PartialOrder α] [OrderBot α] {P : Set α} :
    DisjointPred Overlap P ↔ P.PairwiseDisjoint id := by
  simp only [disjointPred_iff_pairwise, overlap_iff_not_disjoint, not_not]
  rfl

end Mereology
