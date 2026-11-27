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

This file defines `Language.anbncn a b c`, the language of the words consisting of `n` copies of
`a`, then `n` copies of `b`, then `n` copies of `c`. For distinct letters it is
[not context-free](##Language.not_isContextFree_anbncn), the standard application of the pumping
lemma, and the argument shows more: [a language containing `aⁿbⁿcⁿ` for infinitely many `n`, whose
words have as many `a` as `b` as `c`, is not
context-free](##Language.not_isContextFree_of_replicate_mem_of_count_eq).

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
  intro hX
  obtain ⟨p, hp, hpump⟩ := hX.exists_pump_multiset
  obtain ⟨n, hpn, hn⟩ := Filter.frequently_atTop.1 hmem p
  obtain ⟨s, t, hs, hsp, ht, hts, hall⟩ := hpump _ hn (by simp; omega)
  have hout : a ∉ s ∨ c ∉ s := hs.notMem_or_notMem_of_length_le (by rw [length_replicate]; omega)
    (by simp [mem_replicate, hab, hac]) (by simp [mem_replicate, hac.symm, hbc.symm])
  obtain ⟨w, hw, h0⟩ := hall 0
  have hw := hcount w hw
  have ha := congr(Multiset.count a $h0)
  have hb := congr(Multiset.count b $h0)
  have hc := congr(Multiset.count c $h0)
  simp [count_replicate, hab, hac, hbc, Ne.symm] at ha hb hc
  have hz : ∀ e, e ∉ s → t.count e = 0 := fun e he ↦ count_eq_zero.2 fun h ↦ he (hts.subset h)
  obtain ⟨e, he⟩ := exists_mem_of_ne_nil t ht
  have hpos := count_pos_iff.2 he
  have he' := hs.subset (hts.subset he)
  simp only [mem_append, mem_replicate] at he'
  rcases hout.imp (hz _) (hz _) with _ | _ <;>
    rcases he' with (⟨-, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩ <;> omega

/-- For distinct letters, `{aⁿbⁿcⁿ}` is not context-free. -/
theorem not_isContextFree_anbncn (h : [a, b, c].Nodup) : ¬ (anbncn a b c).IsContextFree := by
  obtain ⟨⟨hab, hac⟩, hbc⟩ : (a ≠ b ∧ a ≠ c) ∧ b ≠ c := by simpa using h
  refine not_isContextFree_of_replicate_mem_of_count_eq h
    (.of_forall replicate_append_replicate_append_replicate_mem_anbncn) ?_
  rintro _ ⟨n, rfl⟩
  simp [count_replicate, hab, hac, hbc, Ne.symm]

end Language
