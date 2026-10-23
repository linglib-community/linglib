/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar.Pumping
public import Linglib.Core.Data.List.Infix
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The language `{aⁿbⁿcⁿ | n ∈ ℕ}`

For letters `a`, `b` and `c`, `Language.anbncn a b c` is the language of the words consisting of
`n` copies of `a`, then `n` copies of `b`, then `n` copies of `c`. For distinct letters it is not
context-free, the standard application of the pumping lemma: a window of the pumped word
`aᵖbᵖcᵖ` no longer than `p` cannot meet both the `a` block and the `c` block, so pumping it out
leaves the count of `a` or of `c` at `p` while removing letters.

The argument shows more: a language that contains `aⁿbⁿcⁿ` for infinitely many `n`, and whose
words all have as many `a` as `b` as `c`, is not context-free.

## Main definitions

* `Language.anbncn a b c`: the language `{aⁿbⁿcⁿ | n ∈ ℕ}`.

## Main results

* `Language.not_isContextFree_of_replicate_mem_of_count_eq`: a language containing infinitely
  many of the words `aⁿbⁿcⁿ`, whose words have as many `a` as `b` as `c`, is not context-free.
* `Language.not_isContextFree_anbncn`: for distinct letters, `{aⁿbⁿcⁿ}` is not context-free.

## References

* [J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation* (2000)][hopcroft-motwani-ullman-2000]
-/

@[expose] public section

open List

variable {α : Type*} {a b c : α}

namespace Language

/-- The language `{aⁿbⁿcⁿ | n ∈ ℕ}` of the words consisting of `n` copies of the letter `a`, then
`n` copies of `b`, then `n` copies of `c`. -/
def anbncn (a b c : α) : Language α :=
  {w | ∃ n, replicate n a ++ replicate n b ++ replicate n c = w}

theorem mem_anbncn {w : List α} :
    w ∈ anbncn a b c ↔ ∃ n, replicate n a ++ replicate n b ++ replicate n c = w :=
  Iff.rfl

theorem replicate_append_replicate_append_replicate_mem_anbncn (n : ℕ) :
    replicate n a ++ replicate n b ++ replicate n c ∈ anbncn a b c :=
  ⟨n, rfl⟩

variable [DecidableEq α] {X : Language α}

/-- A language containing `aⁿbⁿcⁿ` for infinitely many `n`, whose words have as many `a` as `b`
as `c`, is not context-free. Pumping out a window of `aⁿbⁿcⁿ` no longer than the pumping length
leaves `a` or `c` untouched, so by the counts no letter is removed at all. -/
theorem not_isContextFree_of_replicate_mem_of_count_eq (h : [a, b, c].Nodup)
    (hmem : ∃ᶠ n in Filter.atTop, replicate n a ++ replicate n b ++ replicate n c ∈ X)
    (hcount : ∀ w ∈ X, w.count a = w.count b ∧ w.count b = w.count c) : ¬ X.IsContextFree := by
  obtain ⟨⟨hab, hac⟩, hbc⟩ : (a ≠ b ∧ a ≠ c) ∧ b ≠ c := by simpa using h
  refine mt IsContextFree.hasCFLPumpingProperty ?_
  rintro ⟨p, hp, hpump⟩
  obtain ⟨n, hpn, hn⟩ := Filter.frequently_atTop.1 hmem p
  obtain ⟨u, v, x, y, z, hw, hvxy, hvy, hall⟩ := hpump _ hn (by simp; omega)
  have hwin : v ++ x ++ y <:+: replicate n a ++ replicate n b ++ replicate n c :=
    ⟨u, z, by simp [hw]⟩
  have hout : a ∉ v ++ x ++ y ∨ c ∉ v ++ x ++ y :=
    hwin.notMem_or_notMem_of_length_le (by rw [length_replicate]; omega)
      (by simp [mem_replicate, hab, hac]) (by simp [mem_replicate, hac.symm, hbc.symm])
  have h0 := hcount _ (hall 0)
  have hca := congr(count a $hw)
  have hcb := congr(count b $hw)
  have hcc := congr(count c $hw)
  simp [count_replicate, hab, hac, hbc, hab.symm, hac.symm, hbc.symm] at h0 hca hcb hcc
  have hz : ∀ s, s ∉ v ++ x ++ y → v.count s = 0 ∧ x.count s = 0 ∧ y.count s = 0 := fun s hs ↦
    ⟨count_eq_zero.mpr fun h ↦ hs (by simp [h]), count_eq_zero.mpr fun h ↦ hs (by simp [h]),
      count_eq_zero.mpr fun h ↦ hs (by simp [h])⟩
  have key : v.count a + y.count a = 0 ∧ v.count b + y.count b = 0 ∧
      v.count c + y.count c = 0 := by
    rcases hout.imp (hz _) (hz _) with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
  have hsub : ∀ e ∈ v ++ y, e = a ∨ e = b ∨ e = c := fun e he ↦ by
    have := hwin.subset (by simp at he ⊢; tauto)
    simp only [mem_append, mem_replicate] at this
    tauto
  have hnil : v ++ y = [] := eq_nil_iff_forall_not_mem.2 fun e he ↦
    count_eq_zero.1
      (by rcases hsub e he with rfl | rfl | rfl <;> simp only [count_append] <;> omega) he
  obtain ⟨rfl, rfl⟩ := append_eq_nil_iff.1 hnil
  simp at hvy

/-- For distinct letters, `{aⁿbⁿcⁿ}` is not context-free. -/
theorem not_isContextFree_anbncn (h : [a, b, c].Nodup) : ¬ (anbncn a b c).IsContextFree := by
  obtain ⟨⟨hab, hac⟩, hbc⟩ : (a ≠ b ∧ a ≠ c) ∧ b ≠ c := by simpa using h
  refine not_isContextFree_of_replicate_mem_of_count_eq h
    (.of_forall replicate_append_replicate_append_replicate_mem_anbncn) ?_
  rintro _ ⟨n, rfl⟩
  simp [count_replicate, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]

end Language
