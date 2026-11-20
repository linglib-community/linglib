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
# The language `{aᵐbⁿcᵐdⁿ | m, n ∈ ℕ}`

This file defines `Language.ambncmdn a b c d`, the language of the words `aᵐbⁿcᵐdⁿ`, in which
the `a` block is matched by the `c` block and the `b` block by the `d` block, so that the two
dependencies cross. For distinct letters it is
[not context-free](##Language.not_isContextFree_ambncmdn), and the pumping argument shows more:
[a language containing `aⁿbⁿcⁿdⁿ` for infinitely many `n`, whose words have no more `a` than `c`
and no more `b` than `d`, is not
context-free](##Language.not_isContextFree_of_replicate_mem_of_count_le).

## References

* [J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation* (2000)][hopcroft-motwani-ullman-2000]
-/

@[expose] public section

open List

variable {α : Type*} {a b c d : α}

namespace Language

/-- The language `{aᵐbⁿcᵐdⁿ | m, n ∈ ℕ}` of the words consisting of `m` copies of the letter `a`,
`n` copies of `b`, `m` copies of `c` and `n` copies of `d`. -/
def ambncmdn (a b c d : α) : Language α :=
  {w | ∃ m n, replicate m a ++ replicate n b ++ replicate m c ++ replicate n d = w}

theorem mem_ambncmdn {w : List α} : w ∈ ambncmdn a b c d ↔
    ∃ m n, replicate m a ++ replicate n b ++ replicate m c ++ replicate n d = w :=
  Iff.rfl

variable [DecidableEq α] {X : Language α}

/-- A language containing `aⁿbⁿcⁿdⁿ` for infinitely many `n`, whose words have no more `a` than
`c` and no more `b` than `d`, is not context-free. Pumping `aⁿbⁿcⁿdⁿ` down and up shows that the
pumped pieces carry as many `a` as `c` and as many `b` as `d`, while a window no longer than `n`
lacks `a` or `c`, and `b` or `d`; so the pumped pieces are empty. -/
theorem not_isContextFree_of_replicate_mem_of_count_le (h : [a, b, c, d].Nodup)
    (hmem : ∃ᶠ n in Filter.atTop,
      replicate n a ++ replicate n b ++ replicate n c ++ replicate n d ∈ X)
    (hcount : ∀ w ∈ X, w.count a ≤ w.count c ∧ w.count b ≤ w.count d) : ¬ X.IsContextFree := by
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ :
      (a ≠ b ∧ a ≠ c ∧ a ≠ d) ∧ (b ≠ c ∧ b ≠ d) ∧ c ≠ d := by simpa using h
  intro hX
  obtain ⟨p, hp, hpump⟩ := hX.exists_pump_multiset
  obtain ⟨n, hpn, hn⟩ := Filter.frequently_atTop.1 hmem p
  obtain ⟨s, t, hs, hsp, ht, hts, hall⟩ := hpump _ hn (by simp; omega)
  have hac' : a ∉ s ∨ c ∉ s :=
    (show s <:+: replicate n a ++ replicate n b ++ (replicate n c ++ replicate n d) by
      simpa only [append_assoc] using hs).notMem_or_notMem_of_length_le
      (by rw [length_replicate]; omega) (by simp [mem_replicate, hab, hac, had])
      (by simp [mem_replicate, hac.symm, hbc.symm])
  have hbd' : b ∉ s ∨ d ∉ s :=
    hs.notMem_or_notMem_of_length_le (by rw [length_replicate]; omega)
      (by simp [mem_replicate, hbc, hbd]) (by simp [mem_replicate, had.symm, hbd.symm, hcd.symm])
  obtain ⟨w₀, hw₀, h0⟩ := hall 0
  obtain ⟨w₂, hw₂, h2⟩ := hall 2
  have hw₀ := hcount w₀ hw₀
  have hw₂ := hcount w₂ hw₂
  have ha0 := congr(Multiset.count a $h0); have hb0 := congr(Multiset.count b $h0)
  have hc0 := congr(Multiset.count c $h0); have hd0 := congr(Multiset.count d $h0)
  have ha2 := congr(Multiset.count a $h2); have hb2 := congr(Multiset.count b $h2)
  have hc2 := congr(Multiset.count c $h2); have hd2 := congr(Multiset.count d $h2)
  simp [count_replicate, hab, hac, had, hbc, hbd, hcd, Ne.symm] at ha0 hb0 hc0 hd0 ha2 hb2 hc2 hd2
  have hz : ∀ e, e ∉ s → t.count e = 0 := fun e he ↦ count_eq_zero.2 fun h ↦ he (hts.subset h)
  obtain ⟨e, he⟩ := exists_mem_of_ne_nil t ht
  have hpos := count_pos_iff.2 he
  have he' := hs.subset (hts.subset he)
  simp only [mem_append, mem_replicate] at he'
  rcases hac'.imp (hz _) (hz _) with _ | _ <;> rcases hbd'.imp (hz _) (hz _) with _ | _ <;>
    rcases he' with ((⟨-, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩) | ⟨-, rfl⟩ <;> omega

/-- For distinct letters, `{aᵐbⁿcᵐdⁿ}` is not context-free. -/
theorem not_isContextFree_ambncmdn (h : [a, b, c, d].Nodup) :
    ¬ (ambncmdn a b c d).IsContextFree := by
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ :
      (a ≠ b ∧ a ≠ c ∧ a ≠ d) ∧ (b ≠ c ∧ b ≠ d) ∧ c ≠ d := by simpa using h
  refine not_isContextFree_of_replicate_mem_of_count_le h (.of_forall fun n ↦ ⟨n, n, rfl⟩) ?_
  rintro _ ⟨m, n, rfl⟩
  simp [count_replicate, hab, hac, had, hbc, hbd, hcd, Ne.symm]

end Language
