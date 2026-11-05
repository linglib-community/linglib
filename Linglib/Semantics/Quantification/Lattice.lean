module

public import Linglib.Core.Order.GenerateCompleteBoolean
public import Linglib.Semantics.Quantification.Properties
public import Mathlib.Order.Atoms
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Invariance classes of determiner denotations

Most classes of determiner denotations are defined by an invariance condition: the value of `d` at
a restrictor and a scope depends only on some function `f` of the two, on `A ∩ B` for the
intersective ones, on `A \ B` for the co-intersective ones, on the restrictor and `A ∩ B` for the
conservative ones. Such a class is [a Boolean subalgebra](##Quantifier.Det.invariants) of `Det α`,
and when `f` has a section it is [the power set of the codomain of
`f`](##Quantifier.Det.invariantsOrderIso), its atoms the fibres of `f`, so that the structure and
size of each class are read off that codomain. The closure of two classes under complements and
arbitrary joins is [the class of the pair of their
functions](##Quantifier.Det.generateCompleteBoolean_union_iff).

## References

* [keenan-stavi-1986]
-/

@[expose] public section

open Function

namespace Quantifier.Det

variable {α : Type*} {β γ : Type*} {f : Set α × Set α → β} {g : Set α × Set α → γ} {d : Det α}

/-! ### The class of a function -/

/-- The determiner denotations whose value at a restrictor and a scope depends only on `f` of them,
a Boolean subalgebra of `Det α`. -/
def invariants (f : Set α × Set α → β) : BooleanSubalgebra (Det α) where
  carrier := {d | ∀ A B A' B', f (A, B) = f (A', B') → (d A B ↔ d A' B')}
  supClosed' _ hd _ hd' A B A' B' h := or_congr (hd A B A' B' h) (hd' A B A' B' h)
  infClosed' _ hd _ hd' A B A' B' h := and_congr (hd A B A' B' h) (hd' A B A' B' h)
  compl_mem' hd A B A' B' h := not_congr (hd A B A' B' h)
  bot_mem' _ _ _ _ _ := .rfl

theorem mem_invariants :
    d ∈ invariants f ↔ ∀ A B A' B', f (A, B) = f (A', B') → (d A B ↔ d A' B') := .rfl

/-- When `f` has a section `s`, its class is the power set of its codomain, by evaluation along
`s`. -/
def invariantsOrderIso {s : β → Set α × Set α} (hs : RightInverse s f) : invariants f ≃o Set β :=
  Equiv.toOrderIso
    { toFun d := {b | d.1 (s b).1 (s b).2}
      invFun S := ⟨fun A B ↦ f (A, B) ∈ S, fun _ _ _ _ e ↦ iff_of_eq (congrArg (· ∈ S) e)⟩
      left_inv d := Subtype.ext <| funext₂ fun A B ↦ propext <| d.2 _ _ A B (hs (f (A, B)))
      right_inv S := Set.ext fun b ↦ iff_of_eq (congrArg (· ∈ S) (hs b)) }
    (fun _ _ h _ hb ↦ h _ _ hb) fun _ _ h _ _ hd ↦ h hd

/-- A class has two to the size of the codomain of its function as size. -/
theorem card_invariants [Finite β] (hf : Surjective f) :
    Nat.card (invariants f) = 2 ^ Nat.card β := by
  rw [Nat.card_congr (invariantsOrderIso (rightInverse_surjInv hf)).toEquiv]
  change Nat.card (β → Prop) = _
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop]

/-- The atoms of a class are the fibres of its function. -/
theorem isAtom_invariants_iff (hf : Surjective f) {d : invariants f} :
    IsAtom d ↔ ∃ b, d.1 = fun A B ↦ f (A, B) = b := by
  have hs := rightInverse_surjInv hf
  rw [← OrderIso.isAtom_iff (invariantsOrderIso hs) d, Set.isAtom_iff]
  refine exists_congr fun b ↦ ⟨fun h ↦ ?_, fun h ↦ Set.ext fun c ↦ ?_⟩
  · rw [← (invariantsOrderIso hs).symm_apply_eq.2 h.symm]
    rfl
  · change d.1 _ _ ↔ c = b
    rw [h]
    exact iff_of_eq (congrArg (· = b) (hs c))

/-! ### The closure of two classes -/

/-- The closure of a family of denotations consists of those whose value is a function of the
pattern of values of the family. -/
theorem generateCompleteBoolean_iff_forall {X : Set (Det α)} :
    GenerateCompleteBoolean X d ↔
      ∀ A B A' B', (∀ x ∈ X, x A B ↔ x A' B') → (d A B ↔ d A' B') := by
  rw [generateCompleteBoolean_iff_factorsThrough (B := Det α) (Set.curryOrderIso _ _)]
  refine ⟨fun h A B A' B' e ↦ iff_of_eq (h (a := (A, B)) (b := (A', B')) ?_),
    fun h ⟨A, B⟩ ⟨A', B'⟩ e ↦ propext (h A B A' B' fun x hx ↦ ?_)⟩
  · exact funext fun x ↦ propext (e x.1 x.2)
  · exact iff_of_eq (congrFun e ⟨x, hx⟩)

/-- The closure of the classes of `f` and `g` under complements and arbitrary joins is the class of
the pair of them, since each fibre of the pair is the meet of a fibre of `f` and a fibre of `g`. -/
theorem generateCompleteBoolean_union_iff :
    GenerateCompleteBoolean (↑(invariants f) ∪ ↑(invariants g)) d ↔
      d ∈ invariants fun p ↦ (f p, g p) := by
  rw [generateCompleteBoolean_iff_forall, mem_invariants]
  refine forall₄_congr fun A B A' B' ↦ imp_congr_left ?_
  constructor
  · intro h
    have hf := (h (fun X Y ↦ f (X, Y) = f (A, B)) (.inl fun _ _ _ _ e ↦ by simp [e])).1 rfl
    have hg := (h (fun X Y ↦ g (X, Y) = g (A, B)) (.inr fun _ _ _ _ e ↦ by simp [e])).1 rfl
    exact Prod.ext hf.symm hg.symm
  · intro e x hx
    obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
    exact hx.elim (· A B A' B' e₁) (· A B A' B' e₂)

/-! ### The conservative determiners -/

/-- The pairs of a restrictor and a scope inside it. -/
abbrev Nested (α : Type*) := {p : Set α × Set α // p.2 ⊆ p.1}

/-- A restrictor with the part of a scope inside it. -/
def nestedOf (p : Set α × Set α) : Nested α := ⟨(p.1, p.1 ∩ p.2), Set.inter_subset_left⟩

/-- The conservative determiner denotations are those whose value depends only on the restrictor
and the part of the scope inside it. -/
abbrev conservativeSubalgebra : BooleanSubalgebra (Det α) := invariants nestedOf

/-- The conservative determiner denotations as a Boolean algebra under the pointwise operations. -/
abbrev ConsDet (α : Type*) := conservativeSubalgebra (α := α)

@[simp] theorem mem_conservativeSubalgebra : d ∈ conservativeSubalgebra ↔ d.Conservative :=
  ⟨fun h A B ↦ h A B A (A ∩ B) (Subtype.ext (by simp [nestedOf])), fun h A B A' B' e ↦ by
    obtain ⟨rfl, hB⟩ := Prod.mk.inj (congrArg Subtype.val e)
    exact h.iff_of_inter_eq hB⟩

theorem rightInverse_nestedOf : RightInverse (Subtype.val : Nested α → _) nestedOf :=
  fun p ↦ Subtype.ext (Prod.ext rfl (Set.inter_eq_right.2 p.2))

/-- The conservative determiner denotations are the sets of nested pairs, [keenan-stavi-1986]'s
atoms being their singletons. -/
def conservativeOrderIso : ConsDet α ≃o Set (Nested α) :=
  invariantsOrderIso rightInverse_nestedOf

/-- Conservativity is intersectivity together with co-intersectivity: the pair of `A ∩ B` and
`A \ B` determines and is determined by `A` and `A ∩ B`. -/
theorem mem_invariants_inter_sdiff_iff :
    d ∈ invariants (fun p ↦ (p.1 ∩ p.2, p.1 \ p.2)) ↔ d.Conservative := by
  rw [← mem_conservativeSubalgebra]
  refine forall₄_congr fun A B A' B' ↦ imp_congr_left ?_
  simp only [nestedOf, Subtype.mk.injEq, Prod.mk.injEq]
  refine ⟨fun ⟨h, h'⟩ ↦ ?_, ?_⟩
  · refine ⟨?_, h⟩
    rw [← Set.inter_union_sdiff A B, ← Set.inter_union_sdiff A' B', h, h']
  · rintro ⟨rfl, h⟩
    exact ⟨h, by rw [← Set.sdiff_self_inter, h, Set.sdiff_self_inter]⟩

end Quantifier.Det
