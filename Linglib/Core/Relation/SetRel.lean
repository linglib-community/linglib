module

public import Mathlib.Basic.Rel
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.SetNotation

/-!
# Complements and transitive closure of relations as sets of pairs

`[UPSTREAM]` supplements to `Mathlib/Basic/Rel.lean`. The core and the preimage of a relation
are dual under complement (`SetRel.core_compl`, `SetRel.preimage_compl`), the core is antitone
in the relation (`SetRel.core_subset_core_left`) and sends unions to intersections
(`SetRel.core_iUnion`), and the transitive closure of a relation
(`SetRel.transGen`) has as core the intersection of the iterated cores
(`SetRel.core_transGen`).

## Main definitions

* `SetRel.ofSuccessors`: a set-valued function `α → Set β` as a relation, whose core at `a` is
  inclusion of `f a` (`SetRel.mem_core_ofSuccessors`) and whose image is the union of the values
  (`SetRel.image_ofSuccessors`).
* `SetRel.transGen`: the transitive closure of `R : SetRel α α`, `Relation.TransGen` of its
  pointwise relation.
-/

@[expose] public section

namespace SetRel

variable {α β : Type*} {R R₁ R₂ : SetRel α β} {t : Set β} {a b c : α}

/-! ### Complements -/

theorem core_compl (R : SetRel α β) (t : Set β) : R.core tᶜ = (R.preimage t)ᶜ := by
  ext; grind

theorem preimage_compl (R : SetRel α β) (t : Set β) : R.preimage tᶜ = (R.core t)ᶜ := by
  rw [← compl_compl (R.preimage _), ← core_compl, compl_compl]

/-- The core along a union of relations is the intersection of the cores. -/
theorem core_iUnion {ι : Sort*} (R : ι → SetRel α β) (t : Set β) :
    core (⋃ i, R i) t = ⋂ i, (R i).core t := by
  ext; simp only [mem_core, Set.mem_iUnion, Set.mem_iInter]; grind

/-- Restricting the relation enlarges the core. -/
@[gcongr]
theorem core_subset_core_left (h : R₁ ⊆ R₂) : R₂.core t ⊆ R₁.core t :=
  fun _ ha _ hb ↦ ha (h hb)

instance isRefl_id : (SetRel.id : SetRel α α).IsRefl := ⟨fun _ ↦ rfl⟩

/-! ### Decidability over finite codomains -/

instance [Fintype β] (R : SetRel α β) (t : Set β) (a : α) [∀ b, Decidable (a ~[R] b)]
    [DecidablePred (· ∈ t)] : Decidable (a ∈ R.core t) :=
  decidable_of_iff (∀ b, a ~[R] b → b ∈ t) mem_core.symm

instance [Fintype β] (R : SetRel α β) (t : Set β) (a : α) [∀ b, Decidable (a ~[R] b)]
    [DecidablePred (· ∈ t)] : Decidable (a ∈ R.preimage t) :=
  decidable_of_iff (∃ b ∈ t, a ~[R] b) mem_preimage.symm

instance [Fintype β] (R : SetRel α β) (a : α) [∀ b, Decidable (a ~[R] b)] : Decidable (a ∈ R.dom) :=
  decidable_of_iff (∃ b, a ~[R] b) mem_dom.symm

instance [Fintype α] (R : SetRel α β) (b : β) [∀ a, Decidable (a ~[R] b)] : Decidable (b ∈ R.cod) :=
  decidable_of_iff (∃ a, a ~[R] b) mem_cod.symm

/-! ### Relations from set-valued functions -/

/-- A set-valued function as a relation, relating `a` to every member of `f a`. -/
def ofSuccessors (f : α → Set β) : SetRel α β := {p | p.2 ∈ f p.1}

variable {f : α → Set β} {y : β}

@[simp] theorem mem_ofSuccessors : a ~[ofSuccessors f] y ↔ y ∈ f a := .rfl

theorem mem_core_ofSuccessors : a ∈ (ofSuccessors f).core t ↔ f a ⊆ t := .rfl

theorem image_ofSuccessors (f : α → Set β) (s : Set α) :
    (ofSuccessors f).image s = ⋃ a ∈ s, f a := by
  ext; simp [image]

theorem mem_preimage_ofSuccessors : a ∈ (ofSuccessors f).preimage t ↔ (f a ∩ t).Nonempty :=
  ⟨fun ⟨b, ht, hb⟩ ↦ ⟨b, hb, ht⟩, fun ⟨b, hb, ht⟩ ↦ ⟨b, ht, hb⟩⟩

/-! ### Transitive closure -/

/-- The transitive closure of a relation. -/
def transGen (R : SetRel α α) : SetRel α α := {p | Relation.TransGen (· ~[R] ·) p.1 p.2}

variable {R : SetRel α α} {s : Set α}

@[simp] theorem mem_transGen : a ~[R.transGen] b ↔ Relation.TransGen (· ~[R] ·) a b := .rfl

theorem subset_transGen : R ⊆ R.transGen := fun _ h ↦ .single h

instance : R.transGen.IsTrans where
  trans _ _ _ := Relation.TransGen.trans

theorem core_transGen_subset_core : R.transGen.core s ⊆ R.core s :=
  core_subset_core_left subset_transGen

/-- The core of the transitive closure is the intersection of the iterated cores. -/
theorem core_transGen : R.transGen.core s = ⋂ n, R.core^[n + 1] s := by
  ext a
  simp only [Set.mem_iInter]
  refine ⟨fun h n ↦ ?_, fun h b hab ↦ ?_⟩
  · induction n generalizing s with
    | zero => exact fun b hab ↦ h (.single hab)
    | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih fun b hab c hbc ↦ h (Relation.TransGen.tail hab hbc)
  · suffices ∀ {b}, Relation.TransGen (· ~[R] ·) a b → ∃ n, ∀ t, a ∈ R.core^[n + 1] t → b ∈ t by
      obtain ⟨n, hn⟩ := this hab
      exact hn s (h n)
    intro b hab
    induction hab with
    | single h => exact ⟨0, fun _ ht ↦ ht h⟩
    | tail _ hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, fun t ht ↦ hn (R.core t)
        (by rwa [Function.iterate_succ_apply] at ht) hbc⟩

end SetRel
