module

public import Linglib.Core.Order.SupClosed
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Set.NAry
public import Mathlib.Tactic.DeriveFintype

/-!
# Sauerland's alternatives

The scale of disjunction of [sauerland-2004] has four members: *or*, *and*, and the operators
`L` and `R` that keep the left and the right disjunct. A sentence is built from elementary
sentences by these connectives, and its alternatives are the sentences obtained by replacing each
connective by a member of the scale. The alternatives of a sentence need not be closed under
conjunction, but they express [every conjunction of its elementary
sentences](##Sauerland.Sentence.infClosure_image_atoms_subset), and [only propositions built from
them by conjunction and disjunction](##Sauerland.Sentence.eval_image_alternatives_subset).

## Implementation notes

Every connective of a sentence may be replaced, `L` and `R` included, which for a sentence built
from *or* and *and* is the definition of the alternatives in [spector-2016].

## References

* [sauerland-2004]
* [spector-2016]
-/

@[expose] public section

namespace Sauerland

open Set

/-- The scale of disjunction. -/
inductive Connective where
  | or
  /-- The operator `L`, which keeps the left disjunct. -/
  | L
  /-- The operator `R`, which keeps the right disjunct. -/
  | R
  | and
  deriving DecidableEq, Fintype

/-- The proposition a connective forms from two propositions. -/
def Connective.apply {W : Type*} : Connective → Set W → Set W → Set W
  | .or, A, B => A ∪ B
  | .L, A, _ => A
  | .R, _, B => B
  | .and, A, B => A ∩ B

instance {W : Type*} (c : Connective) (A B : Set W) [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ B)] : DecidablePred (· ∈ c.apply A B) := by
  cases c <;> unfold Connective.apply <;> infer_instance

/-- A sentence built from elementary sentences by the connectives of the scale. -/
inductive Sentence (ι : Type*) where
  | atom (i : ι)
  | conn (c : Connective) (x y : Sentence ι)

namespace Sentence

variable {ι W : Type*} (p : ι → Set W)

/-- The elementary sentences occurring in a sentence. -/
def atoms : Sentence ι → Set ι
  | atom i => {i}
  | conn _ x y => x.atoms ∪ y.atoms

/-- The proposition a sentence expresses, given those its elementary sentences express. -/
def eval : Sentence ι → Set W
  | atom i => p i
  | conn c x y => c.apply x.eval y.eval

/-- The alternatives of a sentence replace each of its connectives by a member of the scale. -/
def alternatives : Sentence ι → Set (Sentence ι)
  | atom i => {atom i}
  | conn _ x y => ⋃ c, image2 (conn c) x.alternatives y.alternatives

@[simp] theorem alternatives_atom (i : ι) : (atom i).alternatives = {atom i} := rfl

@[simp] theorem mem_alternatives_conn {c : Connective} {x y z : Sentence ι} :
    z ∈ (conn c x y).alternatives ↔
      ∃ c', ∃ x' ∈ x.alternatives, ∃ y' ∈ y.alternatives, conn c' x' y' = z := by
  simp [alternatives]

theorem self_mem_alternatives : ∀ S : Sentence ι, S ∈ S.alternatives
  | atom _ => rfl
  | conn c x y =>
    mem_alternatives_conn.2 ⟨c, x, x.self_mem_alternatives, y, y.self_mem_alternatives, rfl⟩

theorem finite_atoms : ∀ S : Sentence ι, S.atoms.Finite
  | atom _ => finite_singleton _
  | conn _ x y => x.finite_atoms.union y.finite_atoms

theorem eval_image_alternatives_subset : ∀ S : Sentence ι,
    eval p '' S.alternatives ⊆ latticeClosure (p '' S.atoms)
  | atom i => by simp [atoms, eval]
  | conn c x y => by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨c', x', hx', y', hy', rfl⟩ := mem_alternatives_conn.1 hz
    have hx := latticeClosure_mono (image_mono (subset_union_left (t := y.atoms)))
      (x.eval_image_alternatives_subset ⟨x', hx', rfl⟩)
    have hy := latticeClosure_mono (image_mono (subset_union_right (s := x.atoms)))
      (y.eval_image_alternatives_subset ⟨y', hy', rfl⟩)
    cases c'
    exacts [isSublattice_latticeClosure.supClosed hx hy, hx, hy,
      isSublattice_latticeClosure.infClosed hx hy]

/-- Every conjunction of elementary sentences of a sentence is expressed by an alternative: keep
with `L` or `R` the side holding the conjuncts, and conjoin where both sides hold some. -/
theorem infClosure_image_atoms_subset : ∀ S : Sentence ι,
    infClosure (p '' S.atoms) ⊆ eval p '' S.alternatives
  | atom i => by simp [atoms, eval]
  | conn c x y => by
    rw [atoms, image_union, infClosure_union]
    rintro _ ((ha | hb) | ⟨a, ha, b, hb, rfl⟩)
    · obtain ⟨x', hx', rfl⟩ := x.infClosure_image_atoms_subset ha
      exact ⟨conn .L x' y,
        mem_alternatives_conn.2 ⟨_, x', hx', y, y.self_mem_alternatives, rfl⟩, rfl⟩
    · obtain ⟨y', hy', rfl⟩ := y.infClosure_image_atoms_subset hb
      exact ⟨conn .R x y',
        mem_alternatives_conn.2 ⟨_, x, x.self_mem_alternatives, y', hy', rfl⟩, rfl⟩
    · obtain ⟨x', hx', rfl⟩ := x.infClosure_image_atoms_subset ha
      obtain ⟨y', hy', rfl⟩ := y.infClosure_image_atoms_subset hb
      exact ⟨conn .and x' y', mem_alternatives_conn.2 ⟨_, x', hx', y', hy', rfl⟩, rfl⟩

end Sentence

end Sauerland
