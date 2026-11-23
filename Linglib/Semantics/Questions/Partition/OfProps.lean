module

public import Linglib.Semantics.Questions.Partition.Basic
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.Order.Hom.CompleteLattice

/-!
# The question raised by a family of propositions

Given a family `A` of propositions, we define the question `Setoid.ofProps A` that asks, of each
member of `A`, whether it holds. Two worlds are equivalent for it when they make the same members of
`A` true. It is the meet of the polar questions of the members, `⨅ p ∈ A, polar p`.

In the other direction, the propositions that a question `Q` determines form a Boolean subalgebra,
`Q.determined`.

These two constructions are adjoint: a question `Q` determines every member of `A` if and only if
`Q` refines `ofProps A`. See `Setoid.gc_ofProps_determined`. Every question is raised by the
propositions it determines, so the adjunction is a Galois insertion.

## References

* [groenendijk-stokhof-1984]
* [lewis-1988]
* [ciardelli-2022]
-/

@[expose] public section

namespace Setoid

variable {W : Type*} {Q : Setoid W} {p q : Set W} {w v : W}

/-- Two worlds are equivalent for the question raised by a family of propositions when every
member treats them alike. -/
theorem iInf_mem_polar_iff {A : Set (Set W)} :
    (⨅ a ∈ A, polar a) w v ↔ ∀ a ∈ A, (w ∈ a ↔ v ∈ a) := by
  simp only [Setoid.iInf_iff, polar_iff]

variable (A B : Set (Set W))

/-- The question raised by a family of propositions is the meet of their polar questions, the
coarsest question deciding each of them. -/
def ofProps : Setoid W := ⨅ p ∈ A, polar p

variable {A B}

theorem ofProps_iff : ofProps A w v ↔ ∀ p ∈ A, (w ∈ p ↔ v ∈ p) := iInf_mem_polar_iff

theorem ofProps_determines (hp : p ∈ A) : (ofProps A).Determines p := iInf₂_le p hp

theorem le_ofProps_iff : Q ≤ ofProps A ↔ ∀ p ∈ A, Q.Determines p := le_iInf₂_iff

variable (Q) in
/-- The propositions a question determines form a Boolean subalgebra of the propositions. -/
def determined : BooleanSubalgebra (Set W) where
  carrier := {p | Q.Determines p}
  supClosed' _ hp _ hq := hp.union hq
  infClosed' _ hp _ hq := hp.inter hq
  compl_mem' hp := hp.compl
  bot_mem' := determines_iff.2 fun _ _ _ ↦ Iff.rfl

@[simp] theorem mem_determined : p ∈ Q.determined ↔ Q.Determines p := Iff.rfl

theorem le_ofProps_iff_subset : Q ≤ ofProps A ↔ A ⊆ Q.determined := le_ofProps_iff

/-- The question a family of propositions raises and the propositions a question determines are
adjoint: a question determines every member of `A` exactly when it refines the question `A`
raises. -/
theorem gc_ofProps_determined :
    GaloisConnection (OrderDual.toDual ∘ ofProps : Set (Set W) → (Setoid W)ᵒᵈ)
      (fun Q ↦ (determined (OrderDual.ofDual Q) : Set (Set W))) :=
  fun _ _ ↦ le_ofProps_iff_subset

/-- Every question is raised by the propositions it determines. -/
@[simp] theorem ofProps_determined (Q : Setoid W) : ofProps (Q.determined : Set (Set W)) = Q :=
  le_antisymm
    ((le_iInf fun w ↦ ofProps_determines (determines_cell w)).trans_eq (iInf_polar_cell Q))
    (le_ofProps_iff_subset.2 subset_rfl)

/-- The adjunction is a Galois insertion, since every question is raised by the propositions it
determines. -/
def gi_ofProps_determined :
    GaloisInsertion (OrderDual.toDual ∘ ofProps : Set (Set W) → (Setoid W)ᵒᵈ)
      (fun Q ↦ (determined (OrderDual.ofDual Q) : Set (Set W))) :=
  gc_ofProps_determined.toGaloisInsertion fun Q ↦ (ofProps_determined (OrderDual.ofDual Q)).le

theorem ofProps_surjective : Function.Surjective (ofProps : Set (Set W) → Setoid W) :=
  fun Q ↦ ⟨_, ofProps_determined Q⟩

/-- A larger family of propositions raises a finer question. -/
theorem ofProps_anti : Antitone (ofProps : Set (Set W) → Setoid W) :=
  fun _ _ h ↦ gc_ofProps_determined.monotone_l h

@[simp] theorem ofProps_empty : ofProps (∅ : Set (Set W)) = ⊤ :=
  congrArg OrderDual.ofDual gc_ofProps_determined.l_bot

theorem ofProps_union : ofProps (A ∪ B) = ofProps A ⊓ ofProps B :=
  congrArg OrderDual.ofDual gc_ofProps_determined.l_sup

theorem ofProps_sUnion (S : Set (Set (Set W))) : ofProps (⋃₀ S) = ⨅ A ∈ S, ofProps A :=
  congrArg OrderDual.ofDual gc_ofProps_determined.l_sSup

@[simp] theorem ofProps_singleton : ofProps {p} = polar p :=
  Setoid.ext fun _ _ ↦ by simp only [ofProps_iff, Set.mem_singleton_iff, forall_eq, polar_iff]

theorem ofProps_insert : ofProps (insert p A) = polar p ⊓ ofProps A := by
  rw [Set.insert_eq, ofProps_union, ofProps_singleton]

/-- The question raised by a family of propositions as a map into the dual of the lattice of
questions, sending unions to meets. -/
def ofPropsHom : sSupHom (Set (Set W)) (Setoid W)ᵒᵈ where
  toFun A := OrderDual.toDual (ofProps A)
  map_sSup' _ := gc_ofProps_determined.l_sSup.trans sSup_image.symm

@[simp] theorem ofPropsHom_apply (A : Set (Set W)) :
    ofPropsHom A = OrderDual.toDual (ofProps A) := rfl

instance [DecidablePred (· ∈ p)] : DecidableRel (ofProps {p}) :=
  fun w v ↦ decidable_of_iff (polar p w v) (by rw [ofProps_singleton])

instance [DecidablePred (· ∈ p)] [DecidableRel (ofProps A)] :
    DecidableRel (ofProps (insert p A)) :=
  fun w v ↦ decidable_of_iff (polar p w v ∧ ofProps A w v) (by
    rw [ofProps_insert]; exact Setoid.inf_iff_and.symm)

end Setoid
