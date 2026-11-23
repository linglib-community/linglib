module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Order.Antichain
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.Order.Lattice
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.Closure
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Basic.Finite.Prod

/-!
# Questions as inquisitive contents

A `Question W` is a nonempty downward-closed family of information states over `W`, the states
that resolve an inquisitive proposition ([ciardelli-groenendijk-roelofsen-2018],
[ciardelli-2022]). Its alternatives `alt P` are the maximal resolving states and its informative
content `info P` is their union. A question is informative when `info P` is not every world and
inquisitive when `info P` does not itself resolve it. The declarative `ofSet p` of a proposition
is the family of states included in `p`, the principal ideal below `p`.

## Implementation notes

`Question W` is a bundled structure with a `SetLike` instance rather than a `LowerSet (Set W)`
because the bottom elements differ: the bottom question is `{∅}`, resolved only by the
inconsistent state, while the bottom lower set is empty.

## References

* [ciardelli-2022]
* [ciardelli-groenendijk-roelofsen-2018]
* [puncochar-2019]
-/

@[expose] public section

universe u

/-- A question is a non-empty downward-closed family of information states over `W`, the states
that resolve it. -/
structure Question (W : Type u) where
  /-- The set of propositions resolving the issue. -/
  props : Set (Set W)
  /-- Contains the empty proposition (= the inconsistent information
  state). Equivalent to non-emptiness given downward closure. -/
  contains_empty : ∅ ∈ props
  /-- A state included in a resolving state resolves the question. -/
  downward_closed : ∀ p ∈ props, ∀ q : Set W, q ⊆ p → q ∈ props

namespace Question

variable {W : Type u}

/-- A question coerces to its set of resolving states. -/
instance : SetLike (Question W) (Set W) where
  coe := props
  coe_injective P Q h := by cases P; cases Q; congr

@[simp] theorem mem_props {P : Question W} {q : Set W} :
    q ∈ P.props ↔ q ∈ P := Iff.rfl

@[simp, norm_cast] theorem coe_mk (s : Set (Set W)) (h₁ h₂) :
    ((⟨s, h₁, h₂⟩ : Question W) : Set (Set W)) = s := rfl

@[ext]
theorem ext {P Q : Question W} (h : ∀ q, q ∈ P ↔ q ∈ Q) : P = Q :=
  SetLike.ext h

/-- The alternatives of a question are its maximal resolving states. -/
def alt (P : Question W) : Set (Set W) :=
  {p ∈ P.props | ∀ q ∈ P.props, p ⊆ q → p = q}

theorem mem_of_mem_alt {P : Question W} {p : Set W} (h : p ∈ alt P) : p ∈ P := h.1

/-- The informative content of a question is the union of its resolving states. -/
def info (P : Question W) : Set W :=
  ⋃₀ P.props

/-- A sentence is informative iff its informative content excludes
at least one possible world. -/
def IsInformative (P : Question W) : Prop :=
  info P ≠ Set.univ

/-- A sentence is inquisitive iff resolving the issue it raises
requires more than the information it provides — equivalently, iff
`info P` itself is not in `props` (so no single proposition in
`props` covers all of `info P`). -/
def IsInquisitive (P : Question W) : Prop :=
  info P ∉ P.props

/-- A content's own informative content resolves it iff it is not
inquisitive — the condition declarative sentences satisfy; `props`
is then a principal ideal ([puncochar-2019]), see
`info_mem_iff_eq_ofSet_info`. -/
theorem info_mem_iff_not_isInquisitive (P : Question W) :
    P.info ∈ P ↔ ¬ P.IsInquisitive :=
  not_not.symm

theorem mem_info_iff_singleton_mem (P : Question W) (w : W) :
    w ∈ P.info ↔ ({w} : Set W) ∈ P := by
  constructor
  · rintro ⟨q, hq, hwq⟩
    exact P.downward_closed q hq {w} (Set.singleton_subset_iff.mpr hwq)
  · intro h
    exact ⟨{w}, h, rfl⟩

theorem subset_info_of_mem {P : Question W} {q : Set W} (h : q ∈ P) : q ⊆ P.info :=
  Set.subset_sUnion_of_mem h

/-! ### Constructors -/

/-- Smart constructor from a lower (downward-closed) family of
information states containing `∅`. Packages the two `Question`
obligations in mathlib's `IsLowerSet` vocabulary, so a caller holding
a persistence proof (`IsLowerSet`) and an empty-state witness builds
the `Question` directly instead of re-deriving `downward_closed`
inline. -/
def ofLowerSet (s : Set (Set W)) (empty_mem : ∅ ∈ s) (lower : IsLowerSet s) :
    Question W where
  props := s
  contains_empty := empty_mem
  downward_closed := fun _p hp _q hq => lower hq hp

@[simp] theorem props_ofLowerSet (s : Set (Set W)) (empty_mem : ∅ ∈ s)
    (lower : IsLowerSet s) : (ofLowerSet s empty_mem lower).props = s := rfl

@[simp] theorem mem_ofLowerSet {s : Set (Set W)} {empty_mem : ∅ ∈ s}
    {lower : IsLowerSet s} {q : Set W} :
    q ∈ ofLowerSet s empty_mem lower ↔ q ∈ s := Iff.rfl

protected theorem isLowerSet (P : Question W) : IsLowerSet (P : Set (Set W)) :=
  fun _ _ hba ha ↦ P.downward_closed _ ha _ hba

/-- The declarative of `p` is resolved by the states included in `p`, the principal ideal below
`p`, as `Filter.principal` is the principal filter. -/
def ofSet (p : Set W) : Question W where
  props := {q | q ⊆ p}
  contains_empty := Set.empty_subset p
  downward_closed := fun _ hq _ hr => hr.trans hq

/-! ### Basic theorems on ofSet -/

@[simp] theorem mem_ofSet {p q : Set W} :
    q ∈ ofSet p ↔ q ⊆ p := Iff.rfl

@[simp] theorem info_ofSet (p : Set W) : (ofSet p).info = p := by
  ext w
  simp only [info, ofSet, Set.mem_sUnion, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨q, hq, hwq⟩; exact hq hwq
  · intro hw; exact ⟨p, Set.Subset.refl p, hw⟩

theorem info_mem_ofSet (p : Set W) :
    (ofSet p).info ∈ ofSet p := by
  show (ofSet p).info ∈ ofSet p
  rw [info_ofSet]
  exact Set.Subset.refl p

theorem not_isInquisitive_ofSet (p : Set W) :
    ¬ (ofSet p).IsInquisitive :=
  fun h => h (info_mem_ofSet p)

end Question
