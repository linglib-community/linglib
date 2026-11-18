module

public import Mathlib.Basic.Rel
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.SetNotation

/-!
# Complements, asymmetric parts and transitive closure of relations as sets of pairs

`[UPSTREAM]` supplements to `Mathlib/Basic/Rel.lean`. The core and the preimage of a relation
are dual under complement (`SetRel.core_compl`, `SetRel.preimage_compl`), and the core is
antitone in the relation (`SetRel.core_subset_core_left`). The transitive closure of a relation
(`SetRel.transGen`) has as core the intersection of the iterated cores
(`SetRel.core_transGen`). The asymmetric part of a relation (`SetRel.asymmetrize`) complements
mathlib's symmetric part `SetRel.symmetrize`, and a set-valued function is a relation
(`SetRel.ofSuccessors`).
-/

@[expose] public section

namespace SetRel

variable {α β : Type*} {R R₁ R₂ : SetRel α β} {t : Set β} {a b c : α}

/-! ### Complements -/

theorem core_compl (R : SetRel α β) (t : Set β) : R.core tᶜ = (R.preimage t)ᶜ := by
  ext; grind

theorem preimage_compl (R : SetRel α β) (t : Set β) : R.preimage tᶜ = (R.core t)ᶜ := by
  rw [← compl_compl (R.preimage _), ← core_compl, compl_compl]

theorem core_iInter {ι : Sort*} (R : SetRel α β) (t : ι → Set β) :
    R.core (⋂ i, t i) = ⋂ i, R.core (t i) :=
  Set.ext fun _ ↦ by
    simp only [mem_core, Set.mem_iInter]
    exact ⟨fun h i _ hb ↦ h hb i, fun h _ hb i ↦ h i hb⟩

@[gcongr]
theorem core_subset_core_left (h : R₁ ⊆ R₂) : R₂.core t ⊆ R₁.core t :=
  fun _ ha _ hb ↦ ha (h hb)

instance isRefl_id : (SetRel.id : SetRel α α).IsRefl := ⟨fun _ ↦ rfl⟩

/-! ### The image as an order embedding -/

/-- Relations are ordered as their images are. -/
theorem image_le_image_iff : R₁.image ≤ R₂.image ↔ R₁ ⊆ R₂ :=
  ⟨fun h ⟨a, _⟩ r ↦ by
      obtain ⟨_, rfl, r'⟩ := h {a} ⟨a, rfl, r⟩
      exact r',
    fun h _ ↦ image_subset_image_left h⟩

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

/-! ### The asymmetric part -/

section Asymmetrize

variable {R R₁ R₂ : SetRel α α} {a b : α}

variable (R) in
/-- The pairs a relation relates in one direction only, the complement of its symmetric part
`SetRel.symmetrize` within it. -/
def asymmetrize : SetRel α α := R \ R.inv

@[simp] theorem mem_asymmetrize : a ~[R.asymmetrize] b ↔ a ~[R] b ∧ ¬ b ~[R] a := .rfl

instance isIrrefl_asymmetrize : R.asymmetrize.IsIrrefl := ⟨fun _ h ↦ h.2 h.1⟩

instance [DecidablePred (· ∈ R)] : DecidablePred (· ∈ R.asymmetrize) := fun p ↦
  inferInstanceAs (Decidable (p ∈ R ∧ ¬ (p.2, p.1) ∈ R))

theorem asymmetrize_image_prodMap {β : Type*} {f : α → β} (hf : Function.Injective f) :
    asymmetrize (Prod.map f f '' R) = Prod.map f f '' R.asymmetrize := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨⟨a, b⟩, h, he⟩, hn⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨(a, b), ⟨h, fun h' ↦ hn ⟨(b, a), h', rfl⟩⟩, rfl⟩
  · rintro ⟨⟨a, b⟩, ⟨h, hn⟩, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    refine ⟨⟨(a, b), h, rfl⟩, fun ⟨⟨b', a'⟩, h', he'⟩ ↦ hn ?_⟩
    obtain ⟨hb, ha⟩ := Prod.mk.inj he'
    exact hf ha ▸ hf hb ▸ h'

end Asymmetrize

/-! ### Relations from set-valued functions -/

/-- A set-valued function as a relation, relating `a` to every member of `f a`. -/
def ofSuccessors (f : α → Set β) : SetRel α β := {p | p.2 ∈ f p.1}

variable {f : α → Set β} {y : β}

@[simp] theorem mem_ofSuccessors : a ~[ofSuccessors f] y ↔ y ∈ f a := .rfl

theorem mem_core_ofSuccessors : a ∈ (ofSuccessors f).core t ↔ f a ⊆ t := .rfl

theorem image_ofSuccessors (f : α → Set β) (s : Set α) :
    (ofSuccessors f).image s = ⋃ a ∈ s, f a := by
  ext; simp [image]

@[simp] theorem image_ofSuccessors_singleton (f : α → Set β) (a : α) :
    (ofSuccessors f).image {a} = f a := by
  ext; simp [image]

/-- A relation is irreflexive exactly when no point lies in the image of its own singleton. -/
theorem forall_disjoint_image_singleton_iff {R : SetRel α α} :
    (∀ a, Disjoint (R.image {a}) {a}) ↔ R.IsIrrefl := by
  simp only [Set.disjoint_singleton_right, mem_image, Set.mem_singleton_iff, exists_eq_left]
  exact ⟨fun h ↦ ⟨h⟩, fun h ↦ h.irrefl⟩

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
