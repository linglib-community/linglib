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
  refine mt IsContextFree.hasCFLPumpingProperty ?_
  rintro ⟨p, hp, hpump⟩
  obtain ⟨n, hpn, hn⟩ := Filter.frequently_atTop.1 hmem p
  obtain ⟨u, v, x, y, z, hw, hvxy, hvy, hall⟩ := hpump _ hn (by simp; omega)
  have hwin : v ++ x ++ y <:+: replicate n a ++ replicate n b ++ replicate n c ++ replicate n d :=
    ⟨u, z, by rw [hw]; simp⟩
  have hac' : a ∉ v ++ x ++ y ∨ c ∉ v ++ x ++ y :=
    (show v ++ x ++ y <:+: replicate n a ++ replicate n b ++ (replicate n c ++ replicate n d) by
      simpa only [append_assoc] using hwin).notMem_or_notMem_of_length_le
      (by rw [length_replicate]; omega) (by simp [mem_replicate, hab, hac, had])
      (by simp [mem_replicate, hac.symm, hbc.symm])
  have hbd' : b ∉ v ++ x ++ y ∨ d ∉ v ++ x ++ y :=
    hwin.notMem_or_notMem_of_length_le (by rw [length_replicate]; omega)
      (by simp [mem_replicate, hbc, hbd]) (by simp [mem_replicate, had.symm, hbd.symm, hcd.symm])
  have h0 := hcount _ (hall 0)
  have h2 := hcount _ (hall 2)
  simp only [replicate_zero, replicate_succ, flatten_nil, flatten_cons, append_nil,
    count_append] at h0 h2
  have ha := congr(count a $hw); have hb := congr(count b $hw)
  have hc := congr(count c $hw); have hd := congr(count d $hw)
  simp [count_replicate, hab, hac, had, hbc, hbd, hcd, Ne.symm] at ha hb hc hd
  have hz : ∀ s, s ∉ v ++ x ++ y → v.count s = 0 ∧ y.count s = 0 := fun s hs ↦
    ⟨count_eq_zero.mpr fun h ↦ hs (by simp [h]), count_eq_zero.mpr fun h ↦ hs (by simp [h])⟩
  obtain ⟨e, he⟩ := exists_mem_of_ne_nil (v ++ y) hvy
  have hpos := count_pos_iff.2 he
  have he' := hwin.subset (show e ∈ v ++ x ++ y by simp at he ⊢; tauto)
  simp only [count_append, mem_append, mem_replicate] at hpos he'
  rcases hac'.imp (hz _) (hz _) with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases hbd'.imp (hz _) (hz _) with ⟨_, _⟩ | ⟨_, _⟩ <;>
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
