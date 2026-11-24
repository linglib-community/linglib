module

public import Mathlib.Logic.Relation

/-!
# Reading a word along a labelled relation

A labelled relation `R : σ → α → σ → Prop` relates a state to the states a step labelled `a` may
lead to. We define `Relation.Reads R s w t`: the word `w : List α` leads from `s` to `t`, one
label at a time. Reading the empty word is equality, and reading a concatenation is the
composition of the two readings, so `Reads R` sends the free monoid on `α` to relations on `σ`
under composition.

## Main definitions

* `Relation.Reads`: reading a word along a labelled relation.

## Main results

* `Relation.reads_append_iff`: reading `v ++ w` is reading `v` and then `w`.
* `Relation.Reads.mono`: a larger labelled relation reads every word a smaller one does.
* `Relation.Reads.reflTransGen`: states related by reading a word are related by the reflexive
  transitive closure of the steps.
-/

@[expose] public section

namespace Relation

variable {σ α : Type*} {R R' : σ → α → σ → Prop} {s t u : σ} {a : α} {v w : List α}

/-- `Reads R s w t`: the word `w` leads from `s` to `t` along the labelled relation `R`. -/
inductive Reads (R : σ → α → σ → Prop) : σ → List α → σ → Prop
  | nil {s : σ} : Reads R s [] s
  | cons {s t u : σ} {a : α} {w : List α} : R s a t → Reads R t w u → Reads R s (a :: w) u

@[simp] theorem reads_nil_iff : Reads R s [] t ↔ s = t :=
  ⟨fun h ↦ by cases h; rfl, fun h ↦ h ▸ .nil⟩

theorem reads_cons_iff : Reads R s (a :: w) u ↔ ∃ t, R s a t ∧ Reads R t w u :=
  ⟨fun h ↦ by cases h with | cons h₁ h₂ => exact ⟨_, h₁, h₂⟩, fun ⟨_, h₁, h₂⟩ ↦ .cons h₁ h₂⟩

@[simp] theorem reads_singleton_iff : Reads R s [a] t ↔ R s a t := by
  simp [reads_cons_iff]

theorem Reads.append (h₁ : Reads R s v t) (h₂ : Reads R t w u) : Reads R s (v ++ w) u := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h (ih h₂)

/-- Reading `v ++ w` is reading `v` and then `w`. -/
theorem reads_append_iff : Reads R s (v ++ w) u ↔ ∃ t, Reads R s v t ∧ Reads R t w u := by
  refine ⟨fun h ↦ ?_, fun ⟨_, h₁, h₂⟩ ↦ h₁.append h₂⟩
  induction v generalizing s with
  | nil => exact ⟨s, .nil, h⟩
  | cons a v ih =>
    obtain ⟨t, h₁, h₂⟩ := reads_cons_iff.mp h
    obtain ⟨t', h₃, h₄⟩ := ih h₂
    exact ⟨t', .cons h₁ h₃, h₄⟩

theorem Reads.mono (h : ∀ s a t, R s a t → R' s a t) (hr : Reads R s w t) : Reads R' s w t := by
  induction hr with
  | nil => exact .nil
  | cons h₁ _ ih => exact .cons (h _ _ _ h₁) ih

/-- States related by reading a word are related by the reflexive transitive closure of the
steps. -/
theorem Reads.reflTransGen (h : Reads R s w t) : ReflTransGen (fun s t ↦ ∃ a, R s a t) s t := by
  induction h with
  | nil => exact .refl
  | cons h₁ _ ih => exact .head ⟨_, h₁⟩ ih

end Relation
