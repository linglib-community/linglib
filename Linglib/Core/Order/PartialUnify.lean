module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Bounds.Image
public import Mathlib.Order.WithBot

/-!
# Partial unification

`PartialUnify α` equips a partial order with a partial join: `unify a b` is the least upper
bound of `{a, b}` when the pair is bounded above, and `⊤` otherwise. This is the pairwise face of
bounded completeness, Carpenter's setting for unification domains, in which an inheritance
hierarchy is a finite bounded complete partial order and joins are unifications. Adjoining a top
element, the inconsistent description, makes the join total, as Aït-Kaci and Smolka do in
Carpenter's account: `WithTop α` is a join-semilattice whose join of two coerced elements is their
unification, and the laws of unification, idempotence, commutativity, associativity with failure
propagating, `⊥` as identity and monotonicity, are the semilattice laws read through the
coercion. A carrier supplies only `unify` and the two axioms. The semilattice is a scoped
instance, since a carrier that is already a semilattice would otherwise give `WithTop α` a second
join.

## Main declarations

* `PartialUnify`: the class.
* `PartialUnify.isLUB_unify`: `unify a b` is the join of `↑a` and `↑b` in `WithTop α`.
* `PartialUnify.semilatticeSup`: the scoped join-semilattice on `WithTop α`.
* `PartialUnify.unify_eq_coe_iff_isLUB`, `PartialUnify.unify_eq_top_iff`: success and failure,
  characterized.
* `PartialUnify.unify_comm`, `PartialUnify.unify_assoc`, `PartialUnify.unify_self`,
  `PartialUnify.bot_unify`, `PartialUnify.unify_mono`: the unification laws.
* `Compat`: the consistency relation, a common upper bound.
* The Pi instance: pointwise unification over a `Fintype` index.
* The `WithBot` instance: an adjoined `⊥` unifies with everything.
* The instance on nonempty finite sets ordered by reverse inclusion: unification is intersection.

## Implementation notes

`mem_upperBounds_pair`, `WithTop.decidableEqTop`, `WithTop.isLUB_image_coe_iff` and
`WithTop.isLUB_image_coe_top_iff` are rungs of mathlib's bounds and `WithTop` API that the class
needs and mathlib lacks. `[UPSTREAM]`

## References

* [carpenter-1992]
* [shieber-1986]
-/

@[expose] public section

/-! ### Bounds of pairs and of coerced sets -/

theorem mem_upperBounds_pair {α : Type*} [Preorder α] {u a b : α} :
    u ∈ upperBounds ({a, b} : Set α) ↔ a ≤ u ∧ b ≤ u := by
  simp [upperBounds_insert, upperBounds_singleton]

namespace WithTop

variable {α : Type*}

/-- Whether an element of `WithTop α` is `⊤` is decidable without decidable equality on `α`. -/
instance decidableEqTop (x : WithTop α) : Decidable (x = ⊤) :=
  recTopCoe (isTrue rfl) (fun _ ↦ isFalse coe_ne_top) x

variable [Preorder α] {s : Set α} {u : α}

theorem coe_mem_upperBounds_image_coe :
    (u : WithTop α) ∈ upperBounds ((↑) '' s) ↔ u ∈ upperBounds s := by
  simp only [mem_upperBounds, Set.forall_mem_image, coe_le_coe]

theorem isLUB_image_coe_iff : IsLUB ((↑) '' s : Set (WithTop α)) u ↔ IsLUB s u := by
  refine and_congr coe_mem_upperBounds_image_coe ⟨fun h v hv ↦ ?_, fun h x hx ↦ ?_⟩
  · exact coe_le_coe.mp (h (coe_mem_upperBounds_image_coe.mpr hv))
  · induction x using recTopCoe with
    | top => exact le_top
    | coe v => exact coe_le_coe.mpr (h (coe_mem_upperBounds_image_coe.mp hx))

theorem isLUB_image_coe_top_iff : IsLUB ((↑) '' s : Set (WithTop α)) ⊤ ↔ ¬ BddAbove s :=
  ⟨fun h ⟨v, hv⟩ ↦ absurd ((h.2 (coe_mem_upperBounds_image_coe.mpr hv)).trans_lt (coe_lt_top v))
    (lt_irrefl _),
   fun h ↦ ⟨fun _ _ ↦ le_top, fun x hx ↦ by
     induction x using recTopCoe with
     | top => exact le_rfl
     | coe v => exact absurd ⟨v, coe_mem_upperBounds_image_coe.mp hx⟩ h⟩⟩

end WithTop

/-! ### The class -/

/-- A partial join on a partial order, where `unify a b` is the least upper bound of `{a, b}`
when the pair is bounded above and `⊤` otherwise. -/
class PartialUnify (α : Type*) [PartialOrder α] where
  /-- The partial join, `⊤` on an unbounded pair. -/
  unify : α → α → WithTop α
  /-- A successful unification is a least upper bound. -/
  isLUB_of_unify_eq_coe : ∀ {a b c : α}, unify a b = c → IsLUB {a, b} c
  /-- Unification succeeds on bounded pairs. -/
  unify_ne_top_of_bddAbove : ∀ {a b : α}, BddAbove ({a, b} : Set α) → unify a b ≠ ⊤

namespace PartialUnify

variable {α : Type*} [PartialOrder α] [PartialUnify α] {a b c : α}

theorem isLUB_unify (a b : α) : IsLUB {(a : WithTop α), (b : WithTop α)} (unify a b) := by
  rw [← Set.image_pair]
  generalize h : unify a b = x
  induction x using WithTop.recTopCoe with
  | top => exact WithTop.isLUB_image_coe_top_iff.mpr fun hb ↦ unify_ne_top_of_bddAbove hb h
  | coe c => exact WithTop.isLUB_image_coe_iff.mpr (isLUB_of_unify_eq_coe h)

theorem unify_eq_coe_iff_isLUB : unify a b = c ↔ IsLUB {a, b} c := by
  rw [← WithTop.isLUB_image_coe_iff, Set.image_pair]
  exact ⟨fun h ↦ h ▸ isLUB_unify a b, (isLUB_unify a b).unique⟩

theorem unify_eq_top_iff : unify a b = ⊤ ↔ ¬ BddAbove ({a, b} : Set α) := by
  rw [← WithTop.isLUB_image_coe_top_iff, Set.image_pair]
  exact ⟨fun h ↦ h ▸ isLUB_unify a b, (isLUB_unify a b).unique⟩

theorem unify_ne_top_iff_bddAbove : unify a b ≠ ⊤ ↔ BddAbove ({a, b} : Set α) :=
  unify_eq_top_iff.not_left

/-! ### The join-semilattice with failure adjoined -/

/-- The join on `WithTop α` that unification computes, `⊤` absorbing. -/
protected def sup : WithTop α → WithTop α → WithTop α
  | (a : α), (b : α) => unify a b
  | _, _ => ⊤

theorem isLUB_sup (x y : WithTop α) : IsLUB {x, y} (PartialUnify.sup x y) := by
  induction x using WithTop.recTopCoe with
  | top => exact IsGreatest.isLUB ⟨Set.mem_insert _ _, fun _ _ ↦ le_top⟩
  | coe a =>
    induction y using WithTop.recTopCoe with
    | top =>
      exact IsGreatest.isLUB ⟨Set.mem_insert_of_mem _ (Set.mem_singleton _), fun _ _ ↦ le_top⟩
    | coe b => exact isLUB_unify a b

/-- Unification presents `WithTop α` as a join-semilattice with `⊤` as the failure of
unification. The instance is scoped: a carrier that is already a semilattice would otherwise
give `WithTop α` a second join. -/
scoped instance semilatticeSup : SemilatticeSup (WithTop α) :=
  .ofIsLUB PartialUnify.sup isLUB_sup

@[simp] theorem coe_sup_coe (a b : α) : (a : WithTop α) ⊔ b = unify a b := rfl

theorem unify_comm (a b : α) : unify a b = unify b a := sup_comm (a : WithTop α) b

@[simp] theorem unify_self (a : α) : unify a a = a := sup_idem (a : WithTop α)

theorem unify_assoc (a b c : α) : unify a b ⊔ ↑c = ↑a ⊔ unify b c :=
  sup_assoc (a : WithTop α) b c

theorem unify_le_coe_iff : unify a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  rw [← coe_sup_coe, sup_le_iff, WithTop.coe_le_coe, WithTop.coe_le_coe]

theorem unify_eq_left : unify a b = a ↔ b ≤ a := by
  rw [← coe_sup_coe, sup_eq_left, WithTop.coe_le_coe]

theorem unify_eq_right : unify a b = b ↔ a ≤ b := by
  rw [← coe_sup_coe, sup_eq_right, WithTop.coe_le_coe]

theorem sup_coe_eq_coe_iff {x : WithTop α} :
    x ⊔ ↑c = ↑a ↔ ∃ y : α, x = ↑y ∧ unify y c = ↑a := by
  induction x using WithTop.recTopCoe <;> simp

theorem coe_sup_eq_coe_iff {x : WithTop α} :
    ↑a ⊔ x = ↑c ↔ ∃ y : α, x = ↑y ∧ unify a y = ↑c := by
  induction x using WithTop.recTopCoe <;> simp

theorem unify_mono {a₁ a₂ b₁ b₂ u₂ : α} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (h₂ : unify a₂ b₂ = u₂) : ∃ u₁ : α, unify a₁ b₁ = u₁ ∧ u₁ ≤ u₂ :=
  WithTop.le_coe_iff.mp
    ((sup_le_sup (WithTop.coe_le_coe.mpr ha) (WithTop.coe_le_coe.mpr hb)).trans_eq
      ((coe_sup_coe a₂ b₂).trans h₂))

section OrderBot

variable [OrderBot α]

@[simp] theorem bot_unify (a : α) : unify ⊥ a = a := by
  rw [← coe_sup_coe, WithTop.coe_bot, bot_sup_eq]

@[simp] theorem unify_bot (a : α) : unify a ⊥ = a := by
  rw [← coe_sup_coe, WithTop.coe_bot, sup_bot_eq]

end OrderBot

/-! ### Pointwise unification on Pi types -/

section Pi

variable {F : Type*} {S : F → Type*} [∀ t, PartialOrder (S t)] [∀ t, PartialUnify (S t)]
  [Fintype F]

/-- Unification is pointwise, so a bundle unifies when every coordinate does. -/
instance : PartialUnify ((t : F) → S t) where
  unify f g :=
    if h : ∀ t, unify (f t) (g t) ≠ ⊤ then ↑(fun t ↦ (unify (f t) (g t)).untop (h t)) else ⊤
  isLUB_of_unify_eq_coe := by
    intro f g u hu
    by_cases h : ∀ t, unify (f t) (g t) ≠ ⊤
    · rw [dite_eq_left h, WithTop.coe_inj] at hu
      rw [isLUB_pi]
      intro t
      rw [Set.image_pair]
      exact isLUB_of_unify_eq_coe (by rw [← hu]; exact (WithTop.coe_untop _ (h t)).symm)
    · rw [dite_eq_right h] at hu
      exact absurd hu WithTop.top_ne_coe
  unify_ne_top_of_bddAbove := by
    intro f g ⟨w, hw⟩
    have h : ∀ t, unify (f t) (g t) ≠ ⊤ := fun t ↦ unify_ne_top_of_bddAbove
      ⟨w t, mem_upperBounds_pair.mpr
        ⟨hw (Set.mem_insert _ _) t, hw (Set.mem_insert_of_mem _ rfl) t⟩⟩
    rw [dite_eq_left h]
    exact WithTop.coe_ne_top

theorem unify_pi_eq_coe_iff {f g u : (t : F) → S t} :
    unify f g = ↑u ↔ ∀ t, unify (f t) (g t) = ↑(u t) := by
  rw [unify_eq_coe_iff_isLUB, isLUB_pi]
  exact forall_congr' fun t ↦ by rw [unify_eq_coe_iff_isLUB, Set.image_pair]

theorem unify_pi_eq_top_iff {f g : (t : F) → S t} :
    unify f g = ⊤ ↔ ∃ t, unify (f t) (g t) = ⊤ := by
  simp only [unify_eq_top_iff, bddAbove_pi, Set.image_pair, not_forall]

theorem unify_comp {G : Type*} [Fintype G] (σ : G → F) {f g u : (t : F) → S t}
    (h : unify f g = ↑u) :
    unify (fun i ↦ f (σ i)) (fun i ↦ g (σ i)) = ↑(fun i ↦ u (σ i)) :=
  unify_pi_eq_coe_iff.2 fun i ↦ unify_pi_eq_coe_iff.1 h (σ i)

theorem unify_update_bot [∀ t, OrderBot (S t)] [DecidableEq F] (f : (t : F) → S t) (t : F)
    (x : S t) :
    unify f (Function.update ⊥ t x) = (unify (f t) x).map (Function.update f t) := by
  cases h : unify (f t) x with
  | top =>
    rw [WithTop.map_top]
    exact unify_pi_eq_top_iff.2 ⟨t, by simpa using h⟩
  | coe u =>
    rw [WithTop.map_coe]
    refine unify_pi_eq_coe_iff.2 fun t' ↦ ?_
    rcases eq_or_ne t' t with rfl | ht
    · simpa using h
    · simp only [Function.update_of_ne ht, Pi.bot_apply]
      exact unify_eq_left.2 bot_le

end Pi

/-! ### Adjoining a bottom -/

section WithBot

/-- Unification on `WithBot α`, in which `⊥` unifies with everything and two elements of `α`
unify as in `α`. -/
protected def withBotUnify : WithBot α → WithBot α → WithTop (WithBot α)
  | ⊥, y => y
  | (a : α), ⊥ => (a : WithBot α)
  | (a : α), (b : α) => (unify a b).map WithBot.some

instance : PartialUnify (WithBot α) where
  unify := PartialUnify.withBotUnify
  isLUB_of_unify_eq_coe := by
    intro x y z h
    match x, y with
    | ⊥, y =>
      obtain rfl := WithTop.coe_inj.mp h
      exact ⟨mem_upperBounds_pair.mpr ⟨bot_le, le_rfl⟩,
        fun u hu ↦ (mem_upperBounds_pair.mp hu).2⟩
    | (a : α), ⊥ =>
      obtain rfl := WithTop.coe_inj.mp h
      exact ⟨mem_upperBounds_pair.mpr ⟨le_rfl, bot_le⟩,
        fun u hu ↦ (mem_upperBounds_pair.mp hu).1⟩
    | (a : α), (b : α) =>
      simp only [PartialUnify.withBotUnify, WithTop.map_eq_some_iff] at h
      obtain ⟨c, hc, rfl⟩ := h
      have hl := isLUB_of_unify_eq_coe hc
      obtain ⟨hac, hbc⟩ := mem_upperBounds_pair.mp hl.1
      refine ⟨mem_upperBounds_pair.mpr
        ⟨WithBot.coe_le_coe.mpr hac, WithBot.coe_le_coe.mpr hbc⟩, fun u hu ↦ ?_⟩
      obtain ⟨hau, hbu⟩ := mem_upperBounds_pair.mp hu
      obtain ⟨u', rfl, hau'⟩ := WithBot.coe_le_iff.mp hau
      exact WithBot.coe_le_coe.mpr (hl.2 (mem_upperBounds_pair.mpr
        ⟨hau', WithBot.coe_le_coe.mp hbu⟩))
  unify_ne_top_of_bddAbove := by
    intro x y ⟨u, hu⟩
    obtain ⟨hxu, hyu⟩ := mem_upperBounds_pair.mp hu
    match x, y with
    | ⊥, _ => exact WithTop.coe_ne_top
    | (a : α), ⊥ => exact WithTop.coe_ne_top
    | (a : α), (b : α) =>
      obtain ⟨u', rfl, hau'⟩ := WithBot.coe_le_iff.mp hxu
      obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp (unify_ne_top_of_bddAbove
        ⟨u', mem_upperBounds_pair.mpr ⟨hau', WithBot.coe_le_coe.mp hyu⟩⟩)
      simp [PartialUnify.withBotUnify, ← hc]

@[simp] theorem unify_bot_left (y : WithBot α) : unify (⊥ : WithBot α) y = ↑y := rfl

@[simp] theorem unify_coe_bot (a : α) : unify (a : WithBot α) ⊥ = ↑(a : WithBot α) := rfl

@[simp] theorem unify_coe_coe (a b : α) :
    unify (a : WithBot α) (b : WithBot α) = (unify a b).map (↑) := rfl

end WithBot

end PartialUnify

/-! ### Nonempty finite sets under reverse inclusion -/

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- Nonempty finite sets ordered by reverse inclusion, the smaller set the more specific, unify to
their intersection when it is nonempty. -/
instance : PartialUnify {s : Finset α // s.Nonempty}ᵒᵈ where
  unify a b :=
    if h : ((OrderDual.ofDual a).1 ∩ (OrderDual.ofDual b).1).Nonempty then
      ((OrderDual.toDual ⟨_, h⟩ : {s : Finset α // s.Nonempty}ᵒᵈ) : WithTop _)
    else ⊤
  isLUB_of_unify_eq_coe := by
    intro a b c h
    split at h
    · next hne =>
      obtain rfl := WithTop.coe_inj.mp h
      refine ⟨mem_upperBounds_pair.mpr ⟨inter_subset_left, inter_subset_right⟩, fun u hu ↦ ?_⟩
      obtain ⟨hau, hbu⟩ := mem_upperBounds_pair.mp hu
      exact subset_inter hau hbu
    · exact absurd h WithTop.top_ne_coe
  unify_ne_top_of_bddAbove := by
    intro a b ⟨u, hu⟩
    obtain ⟨hau, hbu⟩ := mem_upperBounds_pair.mp hu
    have hne : ((OrderDual.ofDual a).1 ∩ (OrderDual.ofDual b).1).Nonempty :=
      (OrderDual.ofDual u).2.mono (subset_inter hau hbu)
    simp [hne]

end Finset

/-! ### Compatibility

The consistency relation of unification: two elements are compatible when they have a common
upper bound, equivalently when they unify. On feature carriers this is the agreement relation of
Carpenter and Shieber. -/

section Compat

variable {α : Type*}

/-- Two elements are compatible when they are bounded above, the consistency relation of
unification. An `abbrev`, so the `BddAbove` API applies. -/
abbrev Compat [Preorder α] (a b : α) : Prop := BddAbove ({a, b} : Set α)

theorem Compat.of_le [Preorder α] {a b u : α} (ha : a ≤ u) (hb : b ≤ u) : Compat a b :=
  ⟨u, mem_upperBounds_pair.mpr ⟨ha, hb⟩⟩

theorem Compat.symm [Preorder α] {a b : α} (h : Compat a b) : Compat b a :=
  h.mono (Set.pair_comm b a).le

theorem Compat.mono [Preorder α] {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) (h : Compat b d) :
    Compat a c :=
  let ⟨_, hu⟩ := h
  let ⟨hb, hd⟩ := mem_upperBounds_pair.mp hu
  .of_le (h₁.trans hb) (h₂.trans hd)

theorem compat_self [Preorder α] (a : α) : Compat a a := .of_le le_rfl le_rfl

theorem compat_pi_iff {F : Type*} {S : F → Type*} [∀ t, Preorder (S t)] {f g : ∀ t, S t} :
    Compat f g ↔ ∀ t, Compat (f t) (g t) := by
  simp only [Compat, bddAbove_pi, Set.image_pair]

theorem compat_prod_iff {β : Type*} [Preorder α] [Preorder β] {a b : α × β} :
    Compat a b ↔ Compat a.1 b.1 ∧ Compat a.2 b.2 := by
  simp only [Compat, bddAbove_prod, Set.image_pair]

theorem Compat.apply {F : Type*} {S : F → Type*} [∀ t, Preorder (S t)] {f g : ∀ t, S t}
    (h : Compat f g) (t : F) : Compat (f t) (g t) :=
  compat_pi_iff.mp h t

theorem bot_compat [Preorder α] [OrderBot α] (a : α) : Compat (⊥ : α) a := .of_le bot_le le_rfl

theorem compat_bot [Preorder α] [OrderBot α] (a : α) : Compat a (⊥ : α) := .of_le le_rfl bot_le

theorem not_compat_iff_of_forall_isMax [PartialOrder α] [OrderBot α]
    (h : ∀ a : α, a ≠ ⊥ → IsMax a) {a b : α} : ¬ Compat a b ↔ a ≠ ⊥ ∧ b ≠ ⊥ ∧ a ≠ b := by
  constructor
  · intro hc
    exact ⟨fun ha ↦ hc (ha ▸ bot_compat b), fun hb ↦ hc (hb ▸ compat_bot a),
      fun hab ↦ hc (hab ▸ compat_self a)⟩
  · rintro ⟨ha, hb, hab⟩ ⟨u, hu⟩
    obtain ⟨hau, hbu⟩ := mem_upperBounds_pair.mp hu
    exact hab ((le_antisymm (h a ha hau) hau).symm.trans (le_antisymm (h b hb hbu) hbu))

instance [PartialOrder α] [PartialUnify α] (a b : α) : Decidable (Compat a b) :=
  decidable_of_iff _ PartialUnify.unify_ne_top_iff_bddAbove

end Compat
