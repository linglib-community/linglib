module

public import Linglib.Core.Computability.Edge
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.Forall2
public import Mathlib.Order.Cover
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Word order

This file defines the order of a head relative to one of its dependents (`HeadDirection`) and
the linear arrangement of a finite set of constituents (`WordOrder.Arrangement`), in particular of
the subject, object and verb of a clause. An arrangement of `α` over `n` ranks is a bijection
`α ≃ Fin n`; precedence, adjacency, the head direction of a pair, the ends and the mirror image are
all defined from the ranks. The six arrangements `Arrangement Constituent 3` are the basic word
orders of the typological literature, each labelled by its list of constituents ("SOV", …).

## Main declarations

* `HeadDirection`: head-initial or head-final.
* `HeadDirection.ofLT`, `dependentEdge`: the direction at given positions; the dependents' edge.
* `HeadDirection.nearest`: the dependent next to the head, such as the conjunct of a coordination
  that an adjacent selector or probe sees.
* `WordOrder.Arrangement`: a linear arrangement of a finite type over ranks.
* `Arrangement.Precedes`, `Adjacent`, `headDirection`, `mirror`: precedence, adjacency, the head
  direction of a pair, and the reversed arrangement.
* `Arrangement.IsInitial`, `Arrangement.IsFinal`, `Arrangement.IsMedial`: first, last, or neither.
* `Arrangement.sov` and its siblings, `Arrangement.label`: the six basic orders and their labels.

## Implementation notes

The WALS classification of a language's dominant orders, with its "no dominant order" value, is
data (WALS Feature 81A and its siblings). A fragment records the arrangements a language admits as
a `Finset (Arrangement Constituent 3)`; the pairwise orders the language fixes are those every
member agrees on, so no separate consistency invariant is needed. The rank count is a parameter
rather than `Fintype.card α`, so that numerals and `decide` reduce; the ends are defined by rank
for the same reason.

## References

* [dryer-1992]
* [dryer-2013-wals]
* [greenberg-1963]
-/

@[expose] public section

/-- The order of a head and one of its dependents is head-initial if the head precedes, as a verb
precedes its object in VO order and a preposition its noun phrase, and head-final otherwise. -/
inductive HeadDirection where
  | headInitial
  | headFinal
  deriving DecidableEq, Repr, Fintype

namespace HeadDirection

/-- The opposite direction. -/
def swap : HeadDirection → HeadDirection
  | headInitial => headFinal
  | headFinal => headInitial

@[simp] theorem swap_headInitial : headInitial.swap = headFinal := rfl

@[simp] theorem swap_headFinal : headFinal.swap = headInitial := rfl

@[simp] theorem swap_swap : ∀ d : HeadDirection, d.swap.swap = d := by decide

theorem swap_involutive : Function.Involutive swap := swap_swap

theorem swap_injective : Function.Injective swap := swap_involutive.injective

theorem swap_ne_self : ∀ d : HeadDirection, d.swap ≠ d := by decide

theorem swap_eq_iff_eq_swap {d e : HeadDirection} : d.swap = e ↔ d = e.swap :=
  swap_involutive.eq_iff

theorem eq_or_eq_swap : ∀ d e : HeadDirection, e = d ∨ e = d.swap := by decide

section ofLT

variable {α : Type*} [LT α] [DecidableLT α] {head dep : α}

/-- The direction of a head at position `head` with a dependent at position `dep`. -/
def ofLT (head dep : α) : HeadDirection := if head < dep then headInitial else headFinal

@[simp] theorem ofLT_eq_headInitial : ofLT head dep = headInitial ↔ head < dep := by
  unfold ofLT; split <;> simp [*]

@[simp] theorem ofLT_eq_headFinal : ofLT head dep = headFinal ↔ ¬ head < dep := by
  unfold ofLT; split <;> simp [*]

end ofLT

theorem ofLT_swap {α : Type*} [LinearOrder α] {head dep : α} (h : head ≠ dep) :
    ofLT dep head = (ofLT head dep).swap := by
  rcases lt_or_gt_of_ne h with hlt | hlt <;> simp [ofLT, hlt, lt_asymm hlt]

/-- The edge of a head on which its dependents lie, the right one for a head-initial head. -/
def dependentEdge : HeadDirection → Edge
  | headInitial => .right
  | headFinal => .left

@[simp] theorem dependentEdge_headInitial : headInitial.dependentEdge = .right := rfl

@[simp] theorem dependentEdge_headFinal : headFinal.dependentEdge = .left := rfl

@[simp] theorem dependentEdge_swap :
    ∀ d : HeadDirection, d.swap.dependentEdge = d.dependentEdge.swap := by
  decide

theorem dependentEdge_injective : Function.Injective dependentEdge := by decide

section Orders

variable {α : Type*} {d : HeadDirection} {head dep : α}

/-- `d.Orders head dep` holds when the dependent at `dep` lies in direction `d` of the head at
`head`, after it for a head-initial head and before it for a head-final one. Unlike `ofLT`, it
fails when the two positions coincide. -/
def Orders [LT α] : HeadDirection → α → α → Prop
  | headInitial, head, dep => head < dep
  | headFinal, head, dep => dep < head

instance [LT α] [DecidableLT α] :
    ∀ (d : HeadDirection) (head dep : α), Decidable (d.Orders head dep)
  | headInitial, _, _ => inferInstanceAs (Decidable (_ < _))
  | headFinal, _, _ => inferInstanceAs (Decidable (_ < _))

@[simp] theorem headInitial_orders [LT α] : headInitial.Orders head dep ↔ head < dep := Iff.rfl

@[simp] theorem headFinal_orders [LT α] : headFinal.Orders head dep ↔ dep < head := Iff.rfl

theorem orders_iff_ofLT [LinearOrder α] : d.Orders head dep ↔ head ≠ dep ∧ ofLT head dep = d := by
  cases d
  · exact ⟨fun h ↦ ⟨h.ne, ofLT_eq_headInitial.2 h⟩, fun h ↦ ofLT_eq_headInitial.1 h.2⟩
  · refine ⟨fun h ↦ ⟨h.ne', ofLT_eq_headFinal.2 (not_lt.2 h.le)⟩, fun ⟨hne, h⟩ ↦ ?_⟩
    exact lt_of_le_of_ne (not_lt.1 (ofLT_eq_headFinal.1 h)) hne.symm

end Orders

section nearest

variable {α β : Type*}

/-- Of the dependents `l` on one side of the head, in linear order, the one next to the head is the
first if the head precedes them and the last if it follows them. -/
def nearest : HeadDirection → List α → Option α
  | headInitial, l => l.head?
  | headFinal, l => l.getLast?

@[simp] theorem nearest_headInitial (l : List α) : headInitial.nearest l = l.head? := rfl

@[simp] theorem nearest_headFinal (l : List α) : headFinal.nearest l = l.getLast? := rfl

theorem mem_of_mem_nearest {d : HeadDirection} {l : List α} {a : α} (h : a ∈ d.nearest l) :
    a ∈ l := by
  cases d
  · exact List.mem_of_mem_head? h
  · exact List.mem_of_mem_getLast? h

theorem nearest_swap_reverse (d : HeadDirection) (l : List α) :
    d.swap.nearest l.reverse = d.nearest l := by
  cases d <;> simp [List.head?_reverse, List.getLast?_reverse]

theorem nearest_eq_head?_iff [Nontrivial α] {d : HeadDirection} :
    (∀ l : List α, d.nearest l = l.head?) ↔ d = headInitial := by
  refine ⟨fun h ↦ ?_, fun h l ↦ by simp [h]⟩
  cases d with
  | headInitial => rfl
  | headFinal =>
    obtain ⟨a, b, hab⟩ := exists_pair_ne α
    simpa [eq_comm, hab] using h [a, b]

private theorem rel_head? {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → Option.Rel R l₁.head? l₂.head?
  | _, _, .nil => .none
  | _, _, .cons h _ => .some h

theorem rel_nearest {R : α → β → Prop} {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂)
    (d : HeadDirection) : Option.Rel R (d.nearest l₁) (d.nearest l₂) := by
  cases d
  · exact rel_head? h
  · simpa [List.head?_reverse] using rel_head? (List.forall₂_reverse_iff.2 h)

end nearest

end HeadDirection

namespace WordOrder

/-- A linear arrangement of the elements of `α` over `n` ranks, each element sent to its
rank. -/
abbrev Arrangement (α : Type*) (n : ℕ) := α ≃ Fin n

namespace Arrangement

variable {α : Type*} {n : ℕ} (a : Arrangement α n) (x y : α)

/-- `x` precedes `y`. -/
def Precedes : Prop := a x < a y

instance : Decidable (a.Precedes x y) := inferInstanceAs (Decidable (_ < _))

/-- `x` and `y` stand next to each other, one rank covering the other. -/
def Adjacent : Prop := a x ⋖ a y ∨ a y ⋖ a x

/-- The direction of the head `x` with respect to its dependent `y`. -/
def headDirection : HeadDirection := .ofLT (a x) (a y)

/-- The mirror image, every rank reversed. -/
def mirror : Arrangement α n := a.trans Fin.revPerm

/-- `a.IsEnd x d` holds when `x` is a head in direction `d` of every other element, that is, when
`x` stands first if `d` is head-initial and last if it is head-final. -/
def IsEnd : HeadDirection → Prop
  | .headInitial => (a x : ℕ) = 0
  | .headFinal => (a x : ℕ) + 1 = n

/-- `x` stands first. -/
abbrev IsInitial : Prop := a.IsEnd x .headInitial

/-- `x` stands last. -/
abbrev IsFinal : Prop := a.IsEnd x .headFinal

/-- `x` stands neither first nor last. -/
def IsMedial : Prop := ¬ a.IsInitial x ∧ ¬ a.IsFinal x

instance : ∀ d, Decidable (a.IsEnd x d)
  | .headInitial => inferInstanceAs (Decidable ((a x : ℕ) = 0))
  | .headFinal => inferInstanceAs (Decidable ((a x : ℕ) + 1 = n))

instance : Decidable (a.IsMedial x) := inferInstanceAs (Decidable (_ ∧ _))

variable {a x y}

@[simp] theorem headDirection_eq_headInitial :
    a.headDirection x y = .headInitial ↔ a.Precedes x y :=
  HeadDirection.ofLT_eq_headInitial

@[simp] theorem headDirection_eq_headFinal :
    a.headDirection x y = .headFinal ↔ ¬ a.Precedes x y :=
  HeadDirection.ofLT_eq_headFinal

theorem Precedes.trans {z : α} (h₁ : a.Precedes x y) (h₂ : a.Precedes y z) : a.Precedes x z :=
  lt_trans h₁ h₂

theorem Precedes.asymm (h : a.Precedes x y) : ¬ a.Precedes y x := lt_asymm h

/-! ### The mirror image -/

@[simp] theorem mirror_apply : a.mirror x = (a x).rev := rfl

@[simp] theorem mirror_mirror (a : Arrangement α n) : a.mirror.mirror = a := by
  ext c; simp [mirror]

theorem mirror_involutive : Function.Involutive (mirror (α := α) (n := n)) := mirror_mirror

theorem precedes_mirror : a.mirror.Precedes x y ↔ a.Precedes y x := by
  simp [mirror, Precedes]

theorem headDirection_mirror (h : x ≠ y) :
    a.mirror.headDirection x y = (a.headDirection x y).swap := by
  unfold headDirection
  rw [← HeadDirection.ofLT_swap (a.injective.ne h)]
  simp [mirror, HeadDirection.ofLT]

/-! ### Adjacency -/

private theorem fin_covBy_iff {i j : Fin n} : i ⋖ j ↔ (i : ℕ) + 1 = j := by
  refine ⟨fun ⟨hlt, h⟩ ↦ ?_, fun h ↦ ⟨Fin.lt_def.2 (by omega), fun c hc hcj ↦ ?_⟩⟩
  · by_contra hne
    have : (i : ℕ) < j := hlt
    exact h (c := ⟨i + 1, by omega⟩) (Fin.lt_def.2 (by simp)) (Fin.lt_def.2 (by simp; omega))
  · simp only [Fin.lt_def] at hc hcj
    omega

theorem adjacent_iff_val : a.Adjacent x y ↔ (a x : ℕ) + 1 = a y ∨ (a y : ℕ) + 1 = a x := by
  simp only [Adjacent, fin_covBy_iff]

instance : Decidable (a.Adjacent x y) := decidable_of_iff _ adjacent_iff_val.symm

theorem adjacent_comm : a.Adjacent x y ↔ a.Adjacent y x := or_comm

theorem Adjacent.ne (h : a.Adjacent x y) : x ≠ y := by
  rintro rfl
  simp [adjacent_iff_val] at h

@[simp] theorem adjacent_mirror : a.mirror.Adjacent x y ↔ a.Adjacent x y := by
  have := (a x).isLt
  have := (a y).isLt
  simp only [adjacent_iff_val, mirror_apply, Fin.val_rev]
  omega

/-! ### Ends -/

theorem isInitial_iff_val : a.IsInitial x ↔ (a x : ℕ) = 0 := Iff.rfl

theorem isFinal_iff_val : a.IsFinal x ↔ (a x : ℕ) + 1 = n := Iff.rfl

theorem isInitial_iff : a.IsInitial x ↔ ∀ y, y ≠ x → a.Precedes x y := by
  rw [isInitial_iff_val]
  refine ⟨fun h y hy ↦ ?_, fun h ↦ ?_⟩
  · have := a.injective.ne hy
    simp only [Precedes, Fin.lt_def, h]
    exact Nat.pos_of_ne_zero fun h0 ↦ this (Fin.ext (h0.trans h.symm))
  · by_contra hx
    have := h (a.symm ⟨0, (a x).pos⟩) fun h0 ↦ hx (by rw [← h0]; simp)
    simp [Precedes, Fin.lt_def] at this

theorem isFinal_iff : a.IsFinal x ↔ ∀ y, y ≠ x → a.Precedes y x := by
  rw [isFinal_iff_val]
  have hx := (a x).isLt
  refine ⟨fun h y hy ↦ ?_, fun h ↦ ?_⟩
  · have hne : (a y : ℕ) ≠ a x := fun h' ↦ a.injective.ne hy (Fin.ext h')
    have := (a y).isLt
    simp only [Precedes, Fin.lt_def]
    omega
  · by_contra hn
    have := h (a.symm ⟨n - 1, by omega⟩) fun h0 ↦ hn (by rw [← h0]; simp; omega)
    simp only [Precedes, Fin.lt_def, Equiv.apply_symm_apply] at this
    omega

theorem isEnd_iff {d : HeadDirection} : a.IsEnd x d ↔ ∀ y, y ≠ x → a.headDirection x y = d := by
  cases d
  · simpa only [headDirection_eq_headInitial] using isInitial_iff
  · simp only [headDirection_eq_headFinal]
    refine isFinal_iff.trans (forall₂_congr fun y hy ↦ ?_)
    have : a y ≠ a x := a.injective.ne hy
    simp only [Precedes, not_lt]
    exact ⟨le_of_lt, fun h ↦ lt_of_le_of_ne h this⟩

theorem isEnd_mirror {d : HeadDirection} : a.mirror.IsEnd x d ↔ a.IsEnd x d.swap := by
  have := (a x).isLt
  cases d <;> simp only [IsEnd, mirror_apply, Fin.val_rev, HeadDirection.swap_headInitial,
    HeadDirection.swap_headFinal] <;> omega

theorem isInitial_mirror : a.mirror.IsInitial x ↔ a.IsFinal x := isEnd_mirror

theorem isFinal_mirror : a.mirror.IsFinal x ↔ a.IsInitial x := isEnd_mirror

theorem isMedial_mirror : a.mirror.IsMedial x ↔ a.IsMedial x := by
  simp only [IsMedial, isInitial_mirror, isFinal_mirror, and_comm]

/-- Of three elements over three ranks, two are adjacent exactly when the third is not
medial. -/
theorem adjacent_iff_not_isMedial {a : Arrangement α 3} {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : a.Adjacent x y ↔ ¬ a.IsMedial z := by
  have := a.injective.ne hxy
  have := a.injective.ne hxz
  have := a.injective.ne hyz
  have := (a x).isLt
  have := (a y).isLt
  have := (a z).isLt
  simp only [adjacent_iff_val, IsMedial, IsEnd, ne_eq, Fin.ext_iff] at *
  omega

/-! ### The elements before and after an element -/

section Fintype

variable [Fintype α] (a x)

/-- The elements after `x`. -/
def after : Finset α := {c | a.Precedes x c}

/-- The elements before `x`. -/
def before : Finset α := {c | a.Precedes c x}

variable {a x}

@[simp] theorem mem_after {c : α} : c ∈ a.after x ↔ a.Precedes x c := by simp [after]

@[simp] theorem mem_before {c : α} : c ∈ a.before x ↔ a.Precedes c x := by simp [before]

theorem notMem_after_self : x ∉ a.after x := by simp [Precedes]

theorem before_eq_after_mirror : a.before x = a.mirror.after x := by
  ext c
  simp [precedes_mirror]

end Fintype

/-! ### Lists -/

/-- The elements in their order. -/
def toList (a : Arrangement α n) : List α := (List.finRange n).map a.symm

@[simp] theorem length_toList (a : Arrangement α n) : a.toList.length = n := by simp [toList]

theorem toList_nodup (a : Arrangement α n) : a.toList.Nodup :=
  (List.nodup_finRange n).map a.symm.injective

theorem mem_toList (a : Arrangement α n) (x : α) : x ∈ a.toList := by
  simpa [toList] using ⟨a x, by simp⟩

end Arrangement

/-- The three constituents of a transitive clause. -/
inductive Constituent where
  | subject
  | object
  | verb
  deriving DecidableEq, Repr, Fintype

/-- The letter of a constituent in the labels "SOV", "SVO", … of the typological literature. -/
def Constituent.letter : Constituent → Char
  | .subject => 'S'
  | .object => 'O'
  | .verb => 'V'

namespace Arrangement

/-- Subject, object, verb. -/
def sov : Arrangement Constituent 3 :=
  ⟨fun | .subject => 0 | .object => 1 | .verb => 2,
    fun | 0 => .subject | 1 => .object | 2 => .verb, by decide, by decide⟩

/-- Subject, verb, object. -/
def svo : Arrangement Constituent 3 :=
  ⟨fun | .subject => 0 | .verb => 1 | .object => 2,
    fun | 0 => .subject | 1 => .verb | 2 => .object, by decide, by decide⟩

/-- Verb, subject, object. -/
def vso : Arrangement Constituent 3 :=
  ⟨fun | .verb => 0 | .subject => 1 | .object => 2,
    fun | 0 => .verb | 1 => .subject | 2 => .object, by decide, by decide⟩

/-- Verb, object, subject. -/
def vos : Arrangement Constituent 3 :=
  ⟨fun | .verb => 0 | .object => 1 | .subject => 2,
    fun | 0 => .verb | 1 => .object | 2 => .subject, by decide, by decide⟩

/-- Object, verb, subject. -/
def ovs : Arrangement Constituent 3 :=
  ⟨fun | .object => 0 | .verb => 1 | .subject => 2,
    fun | 0 => .object | 1 => .verb | 2 => .subject, by decide, by decide⟩

/-- Object, subject, verb. -/
def osv : Arrangement Constituent 3 :=
  ⟨fun | .object => 0 | .subject => 1 | .verb => 2,
    fun | 0 => .object | 1 => .subject | 2 => .verb, by decide, by decide⟩

/-- The six basic orders. -/
def basicOrders : List (Arrangement Constituent 3) := [sov, svo, vso, vos, ovs, osv]

theorem mem_basicOrders : ∀ a : Arrangement Constituent 3, a ∈ basicOrders := by decide

/-- The label of an arrangement of the three constituents, "SOV" for `sov`. -/
def label (a : Arrangement Constituent 3) : String := .ofList (a.toList.map Constituent.letter)

/-- The basic order with the label `s`, if any. -/
def ofLabel? (s : String) : Option (Arrangement Constituent 3) := basicOrders.find? (·.label = s)

@[simp] theorem ofLabel?_label : ∀ a : Arrangement Constituent 3, ofLabel? a.label = some a := by
  decide

end Arrangement

end WordOrder
