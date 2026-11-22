module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Bounds.Image
public import Mathlib.Order.WithBot

/-!
# Compatibility and joins of pairs

Two elements of an order are compatible when they have a common upper bound, and their
unification is their least upper bound, `IsLUB {a, b} u`. These are the notions of Carpenter's
unification domains, the bounded complete partial orders, in which a compatible pair has a join
and an incompatible pair has none. Compatibility is `Compat`, mathlib's `BddAbove` at a pair, so
it is pointwise on functions and componentwise on products, and it is decidable wherever it is on
the components. Where every compatible pair has a join, [joins of pairs
reassociate](##IsLUB.pair_assoc). An order whose joins are computed presents them as the join of
`WithTop α`, with `⊤` the failure, through `WithTop.semilatticeSupOfIsLUB`.

## References

* [carpenter-1992]
* [shieber-1986]
-/

@[expose] public section

/-! ### Bounds of pairs -/

theorem mem_upperBounds_pair {α : Type*} [Preorder α] {u a b : α} :
    u ∈ upperBounds ({a, b} : Set α) ↔ a ≤ u ∧ b ≤ u := by
  simp [upperBounds_insert, upperBounds_singleton]

theorem isLUB_pair_iff_forall_le {α : Type*} [Preorder α] {a b c : α} :
    IsLUB {a, b} c ↔ a ≤ c ∧ b ≤ c ∧ ∀ u, a ≤ u → b ≤ u → c ≤ u :=
  ⟨fun h ↦ ⟨(mem_upperBounds_pair.1 h.1).1, (mem_upperBounds_pair.1 h.1).2,
    fun _ ha hb ↦ h.2 (mem_upperBounds_pair.2 ⟨ha, hb⟩)⟩,
   fun ⟨ha, hb, h⟩ ↦ ⟨mem_upperBounds_pair.2 ⟨ha, hb⟩,
    fun _ hu ↦ h _ (mem_upperBounds_pair.1 hu).1 (mem_upperBounds_pair.1 hu).2⟩⟩

theorem isLUB_pair_pi_iff {F : Type*} {S : F → Type*} [∀ t, Preorder (S t)] {f g u : ∀ t, S t} :
    IsLUB {f, g} u ↔ ∀ t, IsLUB {f t, g t} (u t) := by
  simp only [isLUB_pi, Set.image_pair]

theorem isLUB_pair_prod_iff {α β : Type*} [Preorder α] [Preorder β] {a b c : α × β} :
    IsLUB {a, b} c ↔ IsLUB {a.1, b.1} c.1 ∧ IsLUB {a.2, b.2} c.2 := by
  simp only [isLUB_prod, Set.image_pair]

instance {F : Type*} {S : F → Type*} [Fintype F] [∀ t, Preorder (S t)]
    [∀ t (a b c : S t), Decidable (IsLUB {a, b} c)] (f g u : ∀ t, S t) :
    Decidable (IsLUB {f, g} u) :=
  decidable_of_iff _ isLUB_pair_pi_iff.symm

instance {α β : Type*} [Preorder α] [Preorder β] [∀ a b c : α, Decidable (IsLUB {a, b} c)]
    [∀ a b c : β, Decidable (IsLUB {a, b} c)] (a b c : α × β) : Decidable (IsLUB {a, b} c) :=
  decidable_of_iff _ isLUB_pair_prod_iff.symm

/-- The join of a function with one that is `⊥` off one coordinate is the join at that
coordinate. -/
theorem isLUB_pair_update_bot_iff {F : Type*} {S : F → Type*} [DecidableEq F]
    [∀ t, PartialOrder (S t)] [∀ t, OrderBot (S t)] {f u : ∀ t, S t} {t : F} {x : S t} :
    IsLUB {f, Function.update ⊥ t x} u ↔ IsLUB {f t, x} (u t) ∧ u = Function.update f t (u t) := by
  rw [isLUB_pair_pi_iff]
  refine ⟨fun h ↦ ⟨by simpa using h t, funext fun t' ↦ ?_⟩, fun ⟨h₁, h₂⟩ t' ↦ ?_⟩
  · rcases eq_or_ne t' t with rfl | ht
    · simp
    · have := isLUB_pair_iff_forall_le.1 (h t')
      rw [Function.update_of_ne ht]
      exact le_antisymm (this.2.2 _ le_rfl (by simp [Function.update_of_ne ht])) this.1
  · rcases eq_or_ne t' t with rfl | ht
    · simpa using h₁
    · rw [h₂]
      simp only [Function.update_of_ne ht, Pi.bot_apply]
      exact isLUB_pair_iff_forall_le.2 ⟨le_rfl, bot_le, fun _ h _ ↦ h⟩

/-- Where every bounded pair has a join, joins of pairs reassociate. -/
theorem IsLUB.pair_assoc {α : Type*} [Preorder α]
    (hα : ∀ a b : α, BddAbove ({a, b} : Set α) → ∃ c, IsLUB {a, b} c) {p q w v r : α}
    (hv : IsLUB {p, q} v) (hr : IsLUB {v, w} r) : ∃ u, IsLUB {q, w} u ∧ IsLUB {p, u} r := by
  obtain ⟨hpv, hqv, hv'⟩ := isLUB_pair_iff_forall_le.1 hv
  obtain ⟨hvr, hwr, hr'⟩ := isLUB_pair_iff_forall_le.1 hr
  obtain ⟨u, hu⟩ := hα q w ⟨r, mem_upperBounds_pair.2 ⟨hqv.trans hvr, hwr⟩⟩
  obtain ⟨hqu, hwu, hu'⟩ := isLUB_pair_iff_forall_le.1 hu
  exact ⟨u, hu, isLUB_pair_iff_forall_le.2 ⟨hpv.trans hvr, hu' r (hqv.trans hvr) hwr,
    fun x hpx hux ↦ hr' x (hv' x hpx (hqu.trans hux)) (hwu.trans hux)⟩⟩

/-! ### Compatibility -/

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

/-- Compatible maximal elements coincide: a fully specified element has no proper extension. -/
theorem Compat.eq_of_isMax [PartialOrder α] {a b : α} (h : Compat a b) (ha : IsMax a)
    (hb : IsMax b) : a = b :=
  let ⟨_, hu⟩ := h
  let ⟨hau, hbu⟩ := mem_upperBounds_pair.mp hu
  (ha.eq_of_le hau).trans (hb.eq_of_ge hbu)

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
  · rintro ⟨ha, hb, hab⟩ hc
    exact hab (hc.eq_of_isMax (h a ha) (h b hb))

instance {F : Type*} {S : F → Type*} [Fintype F] [∀ t, Preorder (S t)]
    [∀ t (a b : S t), Decidable (Compat a b)] (f g : ∀ t, S t) : Decidable (Compat f g) :=
  decidable_of_iff _ compat_pi_iff.symm

instance {β : Type*} [Preorder α] [Preorder β] [∀ a b : α, Decidable (Compat a b)]
    [∀ a b : β, Decidable (Compat a b)] (a b : α × β) : Decidable (Compat a b) :=
  decidable_of_iff _ compat_prod_iff.symm

end Compat

/-! ### Joins with failure adjoined -/

namespace WithTop

variable {α : Type*}

/-- Whether an element of `WithTop α` is `⊤` is decidable without decidable equality on `α`. -/
instance decidableEqTop (x : WithTop α) : Decidable (x = ⊤) :=
  recTopCoe (isTrue rfl) (fun _ ↦ isFalse coe_ne_top) x

section Preorder

variable [Preorder α] {s : Set α} {u a b c : α}

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

theorem isLUB_pair_coe_iff :
    IsLUB ({↑a, ↑b} : Set (WithTop α)) (c : WithTop α) ↔ IsLUB {a, b} c := by
  simpa only [Set.image_pair] using isLUB_image_coe_iff (s := {a, b}) (u := c)

theorem isLUB_pair_coe_top_iff :
    IsLUB ({↑a, ↑b} : Set (WithTop α)) ⊤ ↔ ¬ BddAbove ({a, b} : Set α) := by
  simpa only [Set.image_pair] using isLUB_image_coe_top_iff (s := {a, b})

end Preorder

variable [PartialOrder α]

/-- A partial join extended to `WithTop α`, with `⊤` absorbing. -/
def supOfUnify (unify : α → α → WithTop α) : WithTop α → WithTop α → WithTop α
  | (a : α), (b : α) => unify a b
  | _, _ => ⊤

/-- A function computing the join of two elements of `α` in `WithTop α`, `⊤` when they have no
common upper bound, makes `WithTop α` a join-semilattice. -/
@[instance_reducible]
def semilatticeSupOfIsLUB (unify : α → α → WithTop α)
    (h : ∀ a b : α, IsLUB {(a : WithTop α), (b : WithTop α)} (unify a b)) :
    SemilatticeSup (WithTop α) :=
  .ofIsLUB (supOfUnify unify) fun x y ↦ by
    induction x using recTopCoe with
    | top => exact IsGreatest.isLUB ⟨Set.mem_insert _ _, fun _ _ ↦ le_top⟩
    | coe a =>
      induction y using recTopCoe with
      | top =>
        exact IsGreatest.isLUB ⟨Set.mem_insert_of_mem _ (Set.mem_singleton _), fun _ _ ↦ le_top⟩
      | coe b => exact h a b

theorem eq_coe_iff_of_isLUB {a b c : α} {v : WithTop α}
    (h : IsLUB ({↑a, ↑b} : Set (WithTop α)) v) : v = ↑c ↔ IsLUB {a, b} c :=
  ⟨fun e ↦ isLUB_pair_coe_iff.1 (e ▸ h), fun hc ↦ h.unique (isLUB_pair_coe_iff.2 hc)⟩

theorem eq_top_iff_of_isLUB {a b : α} {v : WithTop α}
    (h : IsLUB ({↑a, ↑b} : Set (WithTop α)) v) : v = ⊤ ↔ ¬ Compat a b :=
  ⟨fun e ↦ isLUB_pair_coe_top_iff.1 (e ▸ h), fun hc ↦ h.unique (isLUB_pair_coe_top_iff.2 hc)⟩

/-! ### Pointwise joins -/

section Pi

variable {F : Type*} {S : F → Type*} [∀ t, PartialOrder (S t)] [Fintype F]
  {u : ∀ t, S t → S t → WithTop (S t)}

/-- The join of two functions computed pointwise by `u`, `⊤` when some coordinate fails. -/
def piUnify (u : ∀ t, S t → S t → WithTop (S t)) (f g : ∀ t, S t) : WithTop (∀ t, S t) :=
  if h : ∀ t, u t (f t) (g t) ≠ ⊤ then ↑(fun t ↦ (u t (f t) (g t)).untop (h t)) else ⊤

theorem isLUB_piUnify
    (hu : ∀ t (a b : S t), IsLUB ({↑a, ↑b} : Set (WithTop (S t))) (u t a b)) (f g : ∀ t, S t) :
    IsLUB ({↑f, ↑g} : Set (WithTop (∀ t, S t))) (piUnify u f g) := by
  unfold piUnify
  split_ifs with h
  · exact isLUB_pair_coe_iff.2 (isLUB_pair_pi_iff.2 fun t ↦
      (eq_coe_iff_of_isLUB (hu t _ _)).1 (coe_untop _ (h t)).symm)
  · exact isLUB_pair_coe_top_iff.2 fun hc ↦ h fun t ↦
      (eq_top_iff_of_isLUB (hu t _ _)).not.2 (not_not.2 (compat_pi_iff.1 hc t))

/-- Unifying with a function that is `⊥` off one coordinate unifies at that coordinate. -/
theorem piUnify_update_bot [DecidableEq F] [∀ t, OrderBot (S t)]
    (hu : ∀ t (a b : S t), IsLUB ({↑a, ↑b} : Set (WithTop (S t))) (u t a b)) (f : ∀ t, S t)
    (t : F) (x : S t) :
    piUnify u f (Function.update ⊥ t x) = (u t (f t) x).map (Function.update f t) := by
  have H := isLUB_piUnify hu f (Function.update ⊥ t x)
  cases h : u t (f t) x with
  | top =>
    rw [map_top]
    exact (eq_top_iff_of_isLUB H).2 fun hc ↦
      (eq_top_iff_of_isLUB (hu t _ _)).1 h (by simpa using compat_pi_iff.1 hc t)
  | coe s =>
    rw [map_coe]
    exact (eq_coe_iff_of_isLUB H).2 (isLUB_pair_update_bot_iff.2
      ⟨by simpa using (eq_coe_iff_of_isLUB (hu t _ _)).1 h, by simp⟩)

end Pi

end WithTop


/-! ### Adjoining a bottom -/

namespace WithBot

variable {α : Type*} [Preorder α] {a b : α}

@[simp] theorem compat_coe_coe : Compat (a : WithBot α) (b : WithBot α) ↔ Compat a b :=
  ⟨fun ⟨u, hu⟩ ↦ by
    obtain ⟨ha, hb⟩ := mem_upperBounds_pair.1 hu
    obtain ⟨u', rfl, hau⟩ := coe_le_iff.1 ha
    exact .of_le hau (coe_le_coe.1 hb),
   fun ⟨u, hu⟩ ↦ .of_le (u := (u : WithBot α)) (coe_le_coe.2 (mem_upperBounds_pair.1 hu).1)
    (coe_le_coe.2 (mem_upperBounds_pair.1 hu).2)⟩

instance [∀ a b : α, Decidable (Compat a b)] : ∀ x y : WithBot α, Decidable (Compat x y)
  | ⊥, y => isTrue (bot_compat y)
  | (a : α), ⊥ => isTrue (compat_bot _)
  | (a : α), (b : α) => decidable_of_iff _ compat_coe_coe.symm

end WithBot

/-! ### Nonempty finite sets under reverse inclusion -/

namespace Finset

variable {α : Type*} [DecidableEq α] {a b c : {s : Finset α // s.Nonempty}ᵒᵈ}

/-- Nonempty finite sets ordered by reverse inclusion, the smaller set the more specific, are
compatible when they meet. -/
theorem compat_iff_inter_nonempty :
    Compat a b ↔ ((OrderDual.ofDual a).1 ∩ (OrderDual.ofDual b).1).Nonempty :=
  ⟨fun ⟨u, hu⟩ ↦ (OrderDual.ofDual u).2.mono
    (subset_inter (mem_upperBounds_pair.1 hu).1 (mem_upperBounds_pair.1 hu).2),
   fun h ↦ .of_le (u := OrderDual.toDual ⟨_, h⟩) inter_subset_left inter_subset_right⟩

/-- They unify to their intersection. -/
theorem isLUB_pair_iff_eq_inter :
    IsLUB {a, b} c ↔ (OrderDual.ofDual c).1 = (OrderDual.ofDual a).1 ∩ (OrderDual.ofDual b).1 := by
  rw [isLUB_pair_iff_forall_le]
  refine ⟨fun ⟨ha, hb, h⟩ ↦ (subset_inter ha hb).antisymm ?_, fun h ↦ ?_⟩
  · exact h (OrderDual.toDual ⟨_, (OrderDual.ofDual c).2.mono (subset_inter ha hb)⟩)
      inter_subset_left inter_subset_right
  · exact ⟨h.subset.trans inter_subset_left, h.subset.trans inter_subset_right, fun u hau hbu ↦
      show (OrderDual.ofDual u).1 ⊆ (OrderDual.ofDual c).1 from h ▸ subset_inter hau hbu⟩

/-- Unification of nonempty finite sets, their intersection when it is nonempty. -/
protected def unify (a b : {s : Finset α // s.Nonempty}ᵒᵈ) :
    WithTop {s : Finset α // s.Nonempty}ᵒᵈ :=
  if h : ((OrderDual.ofDual a).1 ∩ (OrderDual.ofDual b).1).Nonempty then
    ((OrderDual.toDual ⟨_, h⟩ : {s : Finset α // s.Nonempty}ᵒᵈ) : WithTop _)
  else ⊤

theorem isLUB_unify (a b : {s : Finset α // s.Nonempty}ᵒᵈ) :
    IsLUB ({↑a, ↑b} : Set (WithTop {s : Finset α // s.Nonempty}ᵒᵈ)) (Finset.unify a b) := by
  unfold Finset.unify
  split_ifs with h
  · exact WithTop.isLUB_pair_coe_iff.2 (isLUB_pair_iff_eq_inter.2 rfl)
  · exact WithTop.isLUB_pair_coe_top_iff.2 (compat_iff_inter_nonempty.not.2 h)

instance : Decidable (Compat a b) := decidable_of_iff _ compat_iff_inter_nonempty.symm

instance : Decidable (IsLUB {a, b} c) := decidable_of_iff _ isLUB_pair_iff_eq_inter.symm

end Finset
