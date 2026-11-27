module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Bounds.Image
public import Mathlib.Order.WithBot

/-!
# Bounded-complete orders

Two pieces of partial information can be combined when they do not conflict. Order them by how much
they say. Two elements are then **compatible** when some element lies above both, and their
**unification** is the least such element, their join. An order is **bounded complete** when every
compatible pair has a join; an incompatible pair has none. These are the notions of Carpenter's
unification domains. Partial assignments are the case at hand: two possibilities are compatible when
they share their world and never give a referent different values, and merging two information
states joins their compatible points.

## Implementation notes

Compatibility is `Compat`, mathlib's `BddAbove` at a pair, so it is pointwise on functions and
componentwise on products, and it is decidable wherever it is on the components; `Compat` is an
`abbrev`, so the `BddAbove` API applies. The unification of `a` and `b` is stated as `IsLUB {a, b}
u`. In an `IsBoundedComplete` order joins of pairs reassociate (`IsLUB.pair_assoc`). An order whose
joins are computed presents them as the join of `WithTop α`, with `⊤` the failure, through
`WithTop.semilatticeSupOfIsLUB`.

## References

* [carpenter-1992]
* [shieber-1986]
-/

@[expose] public section

/-!
### Bounds of pairs

An upper bound of a pair lies above both of its members, and their join is the least upper bound.
For functions the join is taken at each argument, and for pairs in each coordinate.
-/

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

/-- A function *u* is the join of a function *f* with the function that takes the value *x* at one
argument and the least value everywhere else exactly when *u* agrees with *f* away from that
argument, and its value there is the join of the value of *f* with *x*. -/
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

/-- An order is **bounded complete** when every pair of elements with an upper bound has a least
upper bound. -/
class IsBoundedComplete (α : Type*) [Preorder α] : Prop where
  /-- A pair that is bounded above has a least upper bound. -/
  exists_isLUB_of_bddAbove : ∀ a b : α, BddAbove ({a, b} : Set α) → ∃ c, IsLUB {a, b} c

/-- In a bounded-complete order, joins of pairs reassociate. If *r* is the join of *w* with the join
of *p* and *q*, then *q* and *w* have a join, and *r* is the join of *p* with it. -/
theorem IsLUB.pair_assoc {α : Type*} [Preorder α] [IsBoundedComplete α] {p q w v r : α}
    (hv : IsLUB {p, q} v) (hr : IsLUB {v, w} r) : ∃ u, IsLUB {q, w} u ∧ IsLUB {p, u} r := by
  obtain ⟨hpv, hqv, hv'⟩ := isLUB_pair_iff_forall_le.1 hv
  obtain ⟨hvr, hwr, hr'⟩ := isLUB_pair_iff_forall_le.1 hr
  obtain ⟨u, hu⟩ := IsBoundedComplete.exists_isLUB_of_bddAbove q w
    ⟨r, mem_upperBounds_pair.2 ⟨hqv.trans hvr, hwr⟩⟩
  obtain ⟨hqu, hwu, hu'⟩ := isLUB_pair_iff_forall_le.1 hu
  exact ⟨u, hu, isLUB_pair_iff_forall_le.2 ⟨hpv.trans hvr, hu' r (hqv.trans hvr) hwr,
    fun x hpx hux ↦ hr' x (hv' x hpx (hqu.trans hux)) (hwu.trans hux)⟩⟩

/-!
### Compatibility

Two elements are compatible when they have a common upper bound. Compatibility is symmetric, every
element is compatible with itself, and elements below a compatible pair are compatible.
-/

section Compat

variable {α : Type*}

/-- Two elements are **compatible** when some element lies above both. This is the consistency
relation of unification. -/
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

/-- Two compatible maximal elements are equal, since a fully specified element has no proper
extension. -/
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

/-- In the reverse of an order, two elements are compatible exactly when they have a common lower
bound in the original order. -/
theorem compat_toDual_iff [Preorder α] {a b : α} :
    Compat (OrderDual.toDual a) (OrderDual.toDual b) ↔ ∃ c, c ≤ a ∧ c ≤ b :=
  ⟨fun ⟨u, hu⟩ ↦ ⟨OrderDual.ofDual u, (mem_upperBounds_pair.1 hu).1, (mem_upperBounds_pair.1 hu).2⟩,
    fun ⟨c, ha, hb⟩ ↦ .of_le (u := OrderDual.toDual c) ha hb⟩

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

/-- Functions into bounded-complete orders, ordered argument by argument, form a bounded-complete
order. -/
instance {ι : Type*} {S : ι → Type*} [∀ i, Preorder (S i)] [∀ i, IsBoundedComplete (S i)] :
    IsBoundedComplete (∀ i, S i) where
  exists_isLUB_of_bddAbove a b h :=
    ⟨fun i ↦ (IsBoundedComplete.exists_isLUB_of_bddAbove (a i) (b i)
        (compat_pi_iff.mp h i)).choose,
      isLUB_pair_pi_iff.mpr fun i ↦ (IsBoundedComplete.exists_isLUB_of_bddAbove (a i) (b i)
        (compat_pi_iff.mp h i)).choose_spec⟩

/-!
### Joins with failure adjoined

A procedure that unifies two elements returns their join or fails. Adding one new element above all
the others, to stand for failure, makes unification defined everywhere: the join of two incompatible
elements is the failure element, and joining anything with failure gives failure.
-/

namespace WithTop

variable {α : Type*}

/-- Whether an element of an order with failure adjoined is the failure element can be decided
without deciding equality among the other elements. -/
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

/-- A unification procedure for the elements of an order extends to the order with failure adjoined,
where joining anything with failure gives failure. -/
def supOfUnify (unify : α → α → WithTop α) : WithTop α → WithTop α → WithTop α
  | (a : α), (b : α) => unify a b
  | _, _ => ⊤

/-- Suppose a procedure returns the join of any two elements in the order with failure adjoined, and
so returns failure when they have no common upper bound. Then every two elements of that order have
a join. -/
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

/-!
### Pointwise joins

Functions are unified one argument at a time. The unification of two functions succeeds when it
succeeds at every argument, and fails when it fails at one.
-/

section Pi

variable {F : Type*} {S : F → Type*} [∀ t, PartialOrder (S t)] [Fintype F]
  {u : ∀ t, S t → S t → WithTop (S t)}

/-- The **pointwise unification** of two functions unifies their values at each argument, and fails
when the values at some argument do not unify. -/
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

/-- Unifying a function with one that takes the value *x* at a single argument and the least value
everywhere else unifies the two values at that argument, and leaves the function as it is
elsewhere. -/
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

/-! ### Componentwise joins -/

section Prod

variable {β : Type*} [PartialOrder β] {u : α → α → WithTop α} {v : β → β → WithTop β}

/-- The join of two pairs computed componentwise by `u` and `v`, `⊤` when a component fails. -/
def prodUnify (u : α → α → WithTop α) (v : β → β → WithTop β) (a b : α × β) : WithTop (α × β) :=
  map₂ Prod.mk (u a.1 b.1) (v a.2 b.2)

theorem isLUB_prodUnify (hu : ∀ a b : α, IsLUB ({↑a, ↑b} : Set (WithTop α)) (u a b))
    (hv : ∀ a b : β, IsLUB ({↑a, ↑b} : Set (WithTop β)) (v a b)) (a b : α × β) :
    IsLUB ({↑a, ↑b} : Set (WithTop (α × β))) (prodUnify u v a b) := by
  unfold prodUnify
  cases h₁ : u a.1 b.1 with
  | top =>
    rw [map₂_top_left]
    exact isLUB_pair_coe_top_iff.2 fun hc ↦
      (eq_top_iff_of_isLUB (hu _ _)).1 h₁ (compat_prod_iff.1 hc).1
  | coe x =>
    cases h₂ : v a.2 b.2 with
    | top =>
      rw [map₂_top_right]
      exact isLUB_pair_coe_top_iff.2 fun hc ↦
        (eq_top_iff_of_isLUB (hv _ _)).1 h₂ (compat_prod_iff.1 hc).2
    | coe y =>
      rw [map₂_coe_coe]
      exact isLUB_pair_coe_iff.2 (isLUB_pair_prod_iff.2
        ⟨(eq_coe_iff_of_isLUB (hu _ _)).1 h₁, (eq_coe_iff_of_isLUB (hv _ _)).1 h₂⟩)

end Prod

end WithTop


/-!
### Adjoining a bottom

A new least element, for a value that is undefined, is compatible with everything, and it changes
nothing about which of the old elements are compatible with each other.
-/

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

/-!
### Nonempty finite sets under reverse inclusion

A nonempty finite set of alternatives says more the smaller it is, so these sets are ordered by
reverse inclusion. Two of them are compatible when they overlap, and they unify to their
intersection.
-/

namespace Finset

variable {α : Type*} [DecidableEq α] {a b c : {s : Finset α // s.Nonempty}ᵒᵈ}

/-- Two nonempty finite sets, ordered by reverse inclusion so that the smaller set says more, are
compatible exactly when they have an element in common. -/
theorem compat_iff_inter_nonempty :
    Compat a b ↔ ((OrderDual.ofDual a).1 ∩ (OrderDual.ofDual b).1).Nonempty :=
  ⟨fun ⟨u, hu⟩ ↦ (OrderDual.ofDual u).2.mono
    (subset_inter (mem_upperBounds_pair.1 hu).1 (mem_upperBounds_pair.1 hu).2),
   fun h ↦ .of_le (u := OrderDual.toDual ⟨_, h⟩) inter_subset_left inter_subset_right⟩

/-- In that order, a nonempty finite set is the join of two others exactly when it is their
intersection. -/
theorem isLUB_pair_iff_eq_inter :
    IsLUB {a, b} c ↔ (OrderDual.ofDual c).1 = (OrderDual.ofDual a).1 ∩ (OrderDual.ofDual b).1 := by
  rw [isLUB_pair_iff_forall_le]
  refine ⟨fun ⟨ha, hb, h⟩ ↦ (subset_inter ha hb).antisymm ?_, fun h ↦ ?_⟩
  · exact h (OrderDual.toDual ⟨_, (OrderDual.ofDual c).2.mono (subset_inter ha hb)⟩)
      inter_subset_left inter_subset_right
  · exact ⟨h.subset.trans inter_subset_left, h.subset.trans inter_subset_right, fun u hau hbu ↦
      show (OrderDual.ofDual u).1 ⊆ (OrderDual.ofDual c).1 from h ▸ subset_inter hau hbu⟩

/-- The **unification** of two nonempty finite sets is their intersection when it is nonempty, and
fails otherwise. -/
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
