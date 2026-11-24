module

public import Linglib.Semantics.Questions.Partition.OfProps
public import Mathlib.Order.Concept

/-!
# Hamblin sets

A Hamblin set is a set `H : Set (Set W)` of propositions, the possible answers to a question. Unlike
the cells of a partition, the members of a Hamblin set may overlap, and several of them may be true
in the same world.

This file defines three ways to say what the answer is at a world `w`.

* `karttunen H w`: the Karttunen denotation, the members of `H` that are true at `w`.
* `weakAnswer H w`: the intersection of the true answers. It says that each of them holds.
* `strongAnswer H w`: the set of worlds that agree with `w` on every member of `H`. It says which
  members hold and which do not.

Two worlds have the same true answers if and only if every member of `H` treats them alike. So the
true answers determine a partition question, `Setoid.ofProps H`, and its cells are the strong
answers. See `Question.ker_karttunen` and `Question.strongAnswer_eq_cell`.

## References

* [karttunen-1977]
* [groenendijk-stokhof-1984]
* [heim-1994]
* [beck-rullmann-1999]
-/

@[expose] public section

namespace Question

variable {W : Type*} (H : Set (Set W)) (w : W)

/-! ### The Karttunen denotation and the weak and strong answers -/

/-- The Karttunen denotation at `w` of a question with Hamblin set `H` is the set of its true
answers, the members of `H` true at `w` ([karttunen-1977]; the term is [beck-rullmann-1999]'s). As
a function of the world it is the Karttunen intension. -/
def karttunen : Set (Set W) := {p ∈ H | w ∈ p}

@[simp] theorem mem_karttunen {p : Set W} :
    p ∈ karttunen H w ↔ p ∈ H ∧ w ∈ p := Iff.rfl

theorem karttunen_subset : karttunen H w ⊆ H := fun _ h => h.1

/-- A question intension, a set of answers at each world, is veridical when each answer it gives at
`w` holds at `w`. -/
def IsVeridical (q : W → Set (Set W)) : Prop := ∀ w, ∀ p ∈ q w, w ∈ p

theorem isVeridical_karttunen : IsVeridical (karttunen H) := fun _ _ hp ↦ hp.2

theorem iUnion_karttunen : ⋃ w, karttunen H w = {p ∈ H | p.Nonempty} := by
  ext p
  simp only [Set.mem_iUnion, mem_karttunen, Set.mem_ofPred_eq, Set.Nonempty]
  exact ⟨fun ⟨w, hp, hw⟩ ↦ ⟨hp, w, hw⟩, fun ⟨hp, w, hw⟩ ↦ ⟨w, hp, hw⟩⟩

/-- The weakly exhaustive answer is the intersection of the true members ([heim-1994]'s Ans₁,
[beck-rullmann-1999]'s Ans-BR). -/
def weakAnswer : Set W := ⋂₀ karttunen H w

@[simp] theorem mem_weakAnswer {v : W} :
    v ∈ weakAnswer H w ↔ ∀ p ∈ H, w ∈ p → v ∈ p := by
  simp [weakAnswer, and_imp]

theorem self_mem_weakAnswer : w ∈ weakAnswer H w := by simp

/-! Truth relates worlds to propositions, and a relation induces a Galois connection between
sets on its two sides, mathlib's `upperPolar` and `lowerPolar`. The Karttunen denotation and the
weak answer are the two polars at a world. -/

/-- The Karttunen denotation at `w` is the members of `H` among the propositions true at `w`. -/
theorem karttunen_eq_inter_upperPolar : karttunen H w = H ∩ upperPolar (· ∈ ·) {w} := by
  ext q
  simp [upperPolar]

/-- The weak answer at `w` is the lower polar of the Karttunen denotation, the worlds at which
every true member holds. -/
theorem weakAnswer_eq_lowerPolar : weakAnswer H w = lowerPolar (· ∈ ·) (karttunen H w) := by
  ext v
  simp [lowerPolar, and_imp]

theorem weakAnswer_subset {p : Set W} (hp : p ∈ H) (hw : w ∈ p) :
    weakAnswer H w ⊆ p :=
  Set.sInter_subset_of_mem ⟨hp, hw⟩

/-- The strongly exhaustive answer at `w` is the set of worlds that decide every member of `H` as
`w` does ([groenendijk-stokhof-1984], [heim-1994]'s Ans₂). -/
def strongAnswer : Set W := {v | ∀ p ∈ H, (w ∈ p ↔ v ∈ p)}

@[simp] theorem mem_strongAnswer {v : W} :
    v ∈ strongAnswer H w ↔ ∀ p ∈ H, (w ∈ p ↔ v ∈ p) := Iff.rfl

theorem strongAnswer_subset_weakAnswer : strongAnswer H w ⊆ weakAnswer H w :=
  fun _ hv => (mem_weakAnswer H w).2 fun p hp hwp => (hv p hp).1 hwp

@[simp] theorem self_mem_strongAnswer : w ∈ strongAnswer H w := fun _ _ => Iff.rfl

/-- Adding the negation of every member makes the weak answer the strong one. -/
theorem weakAnswer_union_image_compl : weakAnswer (H ∪ compl '' H) w = strongAnswer H w := by
  ext v
  rw [mem_weakAnswer, mem_strongAnswer]
  constructor
  · exact fun h p hp ↦ ⟨h p (.inl hp), fun hv ↦
      Classical.byContradiction fun hw ↦ h pᶜ (.inr ⟨p, hp, rfl⟩) hw hv⟩
  · rintro h p (hp | ⟨q, hq, rfl⟩) hw
    · exact (h p hp).1 hw
    · exact fun hv ↦ hw ((h q hq).2 hv)

/-- Two worlds have the same true answers exactly when every member decides them alike: the
kernel of the [karttunen-1977] denotation is the partition of [groenendijk-stokhof-1984], the
question the members raise, whose cell [heim-1994]'s generalized analysis has the agent
believe. -/
theorem ker_karttunen : Setoid.ker (karttunen H) = Setoid.ofProps H := by
  ext v w
  simp only [Setoid.ker_def, Setoid.ofProps_iff, Set.ext_iff, mem_karttunen,
    and_congr_right_iff]

theorem ker_weakAnswer : Setoid.ker (weakAnswer H) = Setoid.ofProps H := by
  ext v w
  rw [Setoid.ker_def, Setoid.ofProps_iff]
  constructor
  · intro h p hp
    have hw : w ∈ weakAnswer H v := h ▸ self_mem_weakAnswer H w
    have hv : v ∈ weakAnswer H w := h ▸ self_mem_weakAnswer H v
    exact ⟨fun hvp ↦ weakAnswer_subset H v hp hvp hw, fun hwp ↦ weakAnswer_subset H w hp hwp hv⟩
  · intro h
    ext u
    simp only [mem_weakAnswer]
    exact ⟨fun hu p hp hw ↦ hu p hp ((h p hp).2 hw), fun hu p hp hv ↦ hu p hp ((h p hp).1 hv)⟩

theorem strongAnswer_eq_cell : strongAnswer H w = (Setoid.ofProps H).cell w := by
  ext v
  simp only [mem_strongAnswer, Setoid.mem_cell, Setoid.ofProps_iff]
  exact forall₂_congr fun _ _ ↦ Iff.comm

theorem classes_ofProps : (Setoid.ofProps H).classes = Set.range (strongAnswer H) := by
  ext C
  simp only [Setoid.classes, Set.mem_ofPred_eq, Set.mem_range, strongAnswer_eq_cell, eq_comm]
  rfl

theorem strongAnswer_eq_or_disjoint (w v : W) :
    strongAnswer H w = strongAnswer H v ∨ Disjoint (strongAnswer H w) (strongAnswer H v) := by
  simpa only [strongAnswer_eq_cell] using (Setoid.ofProps H).cell_eq_or_disjoint w v

end Question
