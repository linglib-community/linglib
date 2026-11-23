/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Basic

/-!
# Adding and erasing association lines

`X.addLines i j L` is the representation `X` with the lines of `L` added between tiers `i` and
`j`, and `X.filterLines i j P` keeps the lines between those tiers that satisfy `P`. Both keep
the words of `X`, and `link_addLines` and `link_filterLines` say which lines the results have.
`X.addLine i j p q` adds the one line from position `p` of tier `i` to position `q` of tier `j`,
and `X.eraseLine i j p q` erases it (`link_addLine`, `link_eraseLine`). Spreading an autosegment
is an `addLine`, delinking an `eraseLine`.
-/

@[expose] public section

namespace Autosegmental.AR

variable {ι : Type*} {τ : ι → Type*} {X : AR τ}

section Edit

variable [DecidableEq ι] (X) (i j : ι)

/-- `X.addLines i j L` adds the lines of `L` between tiers `i` and `j`, each a position of `i`
and a position of `j`; pairs out of range are not added, and nothing is added within a tier. -/
def addLines (L : Finset (ℕ × ℕ)) : AR τ where
  word := X.word
  lines i' j' :=
    if i' = i ∧ j' = j ∧ i ≠ j then
      X.lines i' j' ∪ L.filter fun l ↦ l.1 < (X.word i).length ∧ l.2 < (X.word j).length
    else if i' = j ∧ j' = i ∧ i ≠ j then
      X.lines i' j' ∪ (L.filter fun l ↦ l.1 < (X.word i).length ∧ l.2 < (X.word j).length).map
        (Equiv.prodComm ℕ ℕ).toEmbedding
    else X.lines i' j'
  lines_self i' := by
    have h₁ : ¬ (i' = i ∧ i' = j ∧ i ≠ j) := fun h ↦ h.2.2 (h.1.symm.trans h.2.1)
    have h₂ : ¬ (i' = j ∧ i' = i ∧ i ≠ j) := fun h ↦ h.2.2 (h.2.1.symm.trans h.1)
    rw [ite_eq_right h₁, ite_eq_right h₂]
    exact X.lines_self i'
  swap_mem_lines i' j' p q h := by
    by_cases h₁ : i' = i ∧ j' = j ∧ i ≠ j
    · have h₂ : ¬ (j' = i ∧ i' = j ∧ i ≠ j) := fun h' ↦ h₁.2.2 (h₁.1.symm.trans h'.2.1)
      have h₃ : j' = j ∧ i' = i ∧ i ≠ j := ⟨h₁.2.1, h₁.1, h₁.2.2⟩
      rw [ite_eq_left h₁] at h
      rw [ite_eq_right h₂, ite_eq_left h₃]
      rcases Finset.mem_union.1 h with h | h
      · exact Finset.mem_union_left _ (X.swap_mem_lines h)
      · exact Finset.mem_union_right _ (by simpa using h)
    · rw [ite_eq_right h₁] at h
      by_cases h₂ : i' = j ∧ j' = i ∧ i ≠ j
      · have h₃ : j' = i ∧ i' = j ∧ i ≠ j := ⟨h₂.2.1, h₂.1, h₂.2.2⟩
        rw [ite_eq_left h₂] at h
        rw [ite_eq_left h₃]
        rcases Finset.mem_union.1 h with h | h
        · exact Finset.mem_union_left _ (X.swap_mem_lines h)
        · exact Finset.mem_union_right _ (by simpa using h)
      · have h₃ : ¬ (j' = i ∧ i' = j ∧ i ≠ j) := fun h' ↦ h₂ ⟨h'.2.1, h'.1, h'.2.2⟩
        have h₄ : ¬ (j' = j ∧ i' = i ∧ i ≠ j) := fun h' ↦ h₁ ⟨h'.2.1, h'.1, h'.2.2⟩
        rw [ite_eq_right h₂] at h
        rw [ite_eq_right h₃, ite_eq_right h₄]
        exact X.swap_mem_lines h
  fst_lt_of_mem_lines i' j' p q h := by
    split_ifs at h with h₁ h₂
    · rcases Finset.mem_union.1 h with h | h
      · exact X.fst_lt_of_mem_lines h
      · exact h₁.1 ▸ (Finset.mem_filter.1 h).2.1
    · rcases Finset.mem_union.1 h with h | h
      · exact X.fst_lt_of_mem_lines h
      · have h' : (q, p) ∈ L.filter fun l ↦
            l.1 < (X.word i).length ∧ l.2 < (X.word j).length := by simpa using h
        exact h₂.1 ▸ (Finset.mem_filter.1 h').2.2
    · exact X.fst_lt_of_mem_lines h

/-- `X.filterLines i j P` keeps the lines between tiers `i` and `j` that satisfy `P`, each read
as a position of `i` and a position of `j`. -/
def filterLines (P : ℕ × ℕ → Prop) [DecidablePred P] : AR τ where
  word := X.word
  lines i' j' :=
    if i' = i ∧ j' = j then (X.lines i' j').filter P
    else if i' = j ∧ j' = i then (X.lines i' j').filter fun l ↦ P l.swap
    else X.lines i' j'
  lines_self i' := by split_ifs <;> simp [X.lines_self]
  swap_mem_lines i' j' p q h := by
    by_cases h₁ : i' = i ∧ j' = j
    · obtain ⟨rfl, rfl⟩ := h₁
      rw [ite_eq_left ⟨rfl, rfl⟩] at h
      have hm := Finset.mem_filter.1 h
      by_cases h₂ : j' = i' ∧ i' = j'
      · obtain ⟨rfl, -⟩ := h₂
        exact absurd (X.lines_self _ ▸ hm.1) (Finset.notMem_empty _)
      · rw [ite_eq_right h₂, ite_eq_left ⟨rfl, rfl⟩]
        exact Finset.mem_filter.2 ⟨X.swap_mem_lines hm.1, hm.2⟩
    · rw [ite_eq_right h₁] at h
      by_cases h₂ : i' = j ∧ j' = i
      · obtain ⟨rfl, rfl⟩ := h₂
        rw [ite_eq_left ⟨rfl, rfl⟩] at h
        have hm := Finset.mem_filter.1 h
        rw [ite_eq_left ⟨rfl, rfl⟩]
        exact Finset.mem_filter.2 ⟨X.swap_mem_lines hm.1, hm.2⟩
      · rw [ite_eq_right h₂] at h
        have h₃ : ¬ (j' = i ∧ i' = j) := fun h' ↦ h₂ ⟨h'.2, h'.1⟩
        have h₄ : ¬ (j' = j ∧ i' = i) := fun h' ↦ h₁ ⟨h'.2, h'.1⟩
        rw [ite_eq_right h₃, ite_eq_right h₄]
        exact X.swap_mem_lines h
  fst_lt_of_mem_lines i' j' p q h := by
    split_ifs at h
    · exact X.fst_lt_of_mem_lines (Finset.mem_filter.1 h).1
    · exact X.fst_lt_of_mem_lines (Finset.mem_filter.1 h).1
    · exact X.fst_lt_of_mem_lines h

@[simp] theorem word_addLines (L : Finset (ℕ × ℕ)) : (X.addLines i j L).word = X.word := rfl

@[simp] theorem word_filterLines (P : ℕ × ℕ → Prop) [DecidablePred P] :
    (X.filterLines i j P).word = X.word := rfl

variable {X i j} {i' j' : ι} {p q : ℕ}

theorem link_addLines {L : Finset (ℕ × ℕ)} :
    (X.addLines i j L).Link i' j' p q ↔ X.Link i' j' p q ∨ i ≠ j ∧
      (i' = i ∧ j' = j ∧ (p, q) ∈ L ∧ p < (X.word i).length ∧ q < (X.word j).length ∨
        i' = j ∧ j' = i ∧ (q, p) ∈ L ∧ q < (X.word i).length ∧ p < (X.word j).length) := by
  simp only [Link, addLines]
  by_cases h₁ : i' = i ∧ j' = j ∧ i ≠ j
  · rw [ite_eq_left h₁]
    obtain ⟨rfl, rfl, hne⟩ := h₁
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h)
      exacts [.inl h, .inr ⟨hne, .inl ⟨trivial, trivial, h⟩⟩]
    · rintro (h | ⟨-, ⟨-, -, h⟩ | ⟨h, -⟩⟩)
      exacts [.inl h, .inr h, absurd h hne]
  · rw [ite_eq_right h₁]
    by_cases h₂ : i' = j ∧ j' = i ∧ i ≠ j
    · rw [ite_eq_left h₂]
      obtain ⟨rfl, rfl, hne⟩ := h₂
      simp only [Finset.mem_union, Finset.mem_map_equiv, Equiv.prodComm_symm,
        Equiv.prodComm_apply, Prod.swap_prod_mk, Finset.mem_filter]
      constructor
      · rintro (h | h)
        exacts [.inl h, .inr ⟨hne, .inr ⟨trivial, trivial, h⟩⟩]
      · rintro (h | ⟨-, ⟨h, -⟩ | ⟨-, -, h⟩⟩)
        exacts [.inl h, absurd h.symm hne, .inr h]
    · rw [ite_eq_right h₂]
      exact ⟨.inl, fun h ↦ h.elim id fun ⟨hne, h'⟩ ↦ h'.elim
        (fun h'' ↦ absurd ⟨h''.1, h''.2.1, hne⟩ h₁) fun h'' ↦ absurd ⟨h''.1, h''.2.1, hne⟩ h₂⟩

/-- Adding no lines changes nothing. -/
@[simp] theorem addLines_empty : X.addLines i j ∅ = X :=
  ext rfl fun i' j' p q ↦ by simp [link_addLines]

theorem link_filterLines {P : ℕ × ℕ → Prop} [DecidablePred P] :
    (X.filterLines i j P).Link i' j' p q ↔ X.Link i' j' p q ∧
      (i' = i → j' = j → P (p, q)) ∧ (i' = j → j' = i → P (q, p)) := by
  simp only [Link, filterLines]
  by_cases h₁ : i' = i ∧ j' = j
  · obtain ⟨rfl, rfl⟩ := h₁
    rw [ite_eq_left ⟨rfl, rfl⟩, Finset.mem_filter]
    refine and_congr_right fun hl ↦ ⟨fun h ↦ ⟨fun _ _ ↦ h, fun h₁ _ ↦ ?_⟩, fun h ↦ h.1 rfl rfl⟩
    subst h₁
    exact absurd (X.lines_self _ ▸ hl) (Finset.notMem_empty _)
  · rw [ite_eq_right h₁]
    by_cases h₂ : i' = j ∧ j' = i
    · obtain ⟨rfl, rfl⟩ := h₂
      rw [ite_eq_left ⟨rfl, rfl⟩, Finset.mem_filter]
      exact and_congr_right fun _ ↦
        ⟨fun h ↦ ⟨fun a b ↦ absurd ⟨a, b⟩ h₁, fun _ _ ↦ h⟩, fun h ↦ h.2 rfl rfl⟩
    · rw [ite_eq_right h₂]
      exact ⟨fun h ↦ ⟨h, fun a b ↦ absurd ⟨a, b⟩ h₁, fun a b ↦ absurd ⟨a, b⟩ h₂⟩, fun h ↦ h.1⟩

/-! ### One line -/

variable (X i j) (p q : ℕ)

/-- The representation with one more line, from position `p` of tier `i` to position `q` of tier
`j`; a line out of range or within a tier is not added. -/
def addLine : AR τ := X.addLines i j {(p, q)}

/-- The representation without the line from position `p` of tier `i` to position `q` of tier
`j`. -/
def eraseLine : AR τ := X.filterLines i j (· ≠ (p, q))

@[simp] theorem word_addLine : (X.addLine i j p q).word = X.word := rfl

@[simp] theorem word_eraseLine : (X.eraseLine i j p q).word = X.word := rfl

variable {X i j p q} {p' q' : ℕ}

theorem link_addLine : (X.addLine i j p q).Link i' j' p' q' ↔ X.Link i' j' p' q' ∨
    i ≠ j ∧ p < (X.word i).length ∧ q < (X.word j).length ∧
      (i' = i ∧ j' = j ∧ p' = p ∧ q' = q ∨ i' = j ∧ j' = i ∧ p' = q ∧ q' = p) := by
  simp only [addLine, link_addLines, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro (h | ⟨hne, ⟨rfl, rfl, ⟨rfl, rfl⟩, hp, hq⟩ | ⟨rfl, rfl, ⟨rfl, rfl⟩, hp, hq⟩⟩)
    · exact .inl h
    · exact .inr ⟨hne, hp, hq, .inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · exact .inr ⟨hne, hp, hq, .inr ⟨rfl, rfl, rfl, rfl⟩⟩
  · rintro (h | ⟨hne, hp, hq, ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩⟩)
    · exact .inl h
    · exact .inr ⟨hne, .inl ⟨rfl, rfl, ⟨rfl, rfl⟩, hp, hq⟩⟩
    · exact .inr ⟨hne, .inr ⟨rfl, rfl, ⟨rfl, rfl⟩, hp, hq⟩⟩

theorem link_eraseLine : (X.eraseLine i j p q).Link i' j' p' q' ↔ X.Link i' j' p' q' ∧
    ¬ (i' = i ∧ j' = j ∧ p' = p ∧ q' = q) ∧ ¬ (i' = j ∧ j' = i ∧ p' = q ∧ q' = p) := by
  simp only [eraseLine, link_filterLines, ne_eq, Prod.mk.injEq]
  tauto

end Edit

end Autosegmental.AR
