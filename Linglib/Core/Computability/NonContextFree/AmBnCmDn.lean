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

For letters `a`, `b`, `c` and `d`, `Language.ambncmdn a b c d` is the language of the words
`aᵐbⁿcᵐdⁿ`, in which the `a` block is matched by the `c` block and the `b` block by the `d` block,
so that the two dependencies cross. For distinct letters it is not context-free; it is the
language to which the argument of [shieber-1985] that Swiss German is not weakly context-free
reduces.

The pumping argument shows more: a language that contains `aⁿbⁿcⁿdⁿ` for infinitely many `n`, and
whose words have no more `a` than `c` and no more `b` than `d`, is not context-free. Pumping
`aⁿbⁿcⁿdⁿ` down and up forces the pumped window to carry as many `a` as `c` and as many `b` as
`d`, and a window no longer than the pumping length meets neither pair.

## Main definitions

* `Language.ambncmdn a b c d`: the language `{aᵐbⁿcᵐdⁿ | m, n ∈ ℕ}`.

## Main results

* `Language.not_isContextFree_of_replicate_mem_of_count_le`: a language containing infinitely
  many of the words `aⁿbⁿcⁿdⁿ`, whose words have no more `a` than `c` and no more `b` than `d`, is
  not context-free.
* `Language.not_isContextFree_ambncmdn`: for distinct letters, `{aᵐbⁿcᵐdⁿ}` is not context-free.

## References

* [S. M. Shieber, *Evidence against the Context-Freeness of Natural Language* (1985)][shieber-1985]
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
`c` and no more `b` than `d`, is not context-free. -/
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
  simp [count_replicate, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm,
    hbd.symm, hcd.symm] at ha hb hc hd
  have hz : ∀ s, s ∉ v ++ x ++ y → v.count s = 0 ∧ y.count s = 0 := fun s hs ↦
    ⟨count_eq_zero.mpr fun h ↦ hs (by simp [h]), count_eq_zero.mpr fun h ↦ hs (by simp [h])⟩
  have key : v.count a + y.count a = 0 ∧ v.count b + y.count b = 0 ∧
      v.count c + y.count c = 0 ∧ v.count d + y.count d = 0 := by
    rcases hac'.imp (hz _) (hz _) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases hbd'.imp (hz _) (hz _) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have hsub : ∀ e ∈ v ++ y, e = a ∨ e = b ∨ e = c ∨ e = d := fun e he ↦ by
    have := hwin.subset (by simp at he ⊢; tauto)
    simp only [mem_append, mem_replicate] at this
    tauto
  have hnil : v ++ y = [] := eq_nil_iff_forall_not_mem.2 fun e he ↦
    count_eq_zero.1
      (by rcases hsub e he with rfl | rfl | rfl | rfl <;> simp only [count_append] <;> omega) he
  obtain ⟨rfl, rfl⟩ := append_eq_nil_iff.1 hnil
  simp at hvy

/-- For distinct letters, `{aᵐbⁿcᵐdⁿ}` is not context-free. -/
theorem not_isContextFree_ambncmdn (h : [a, b, c, d].Nodup) :
    ¬ (ambncmdn a b c d).IsContextFree := by
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ :
      (a ≠ b ∧ a ≠ c ∧ a ≠ d) ∧ (b ≠ c ∧ b ≠ d) ∧ c ≠ d := by simpa using h
  refine not_isContextFree_of_replicate_mem_of_count_le h (.of_forall fun n ↦ ⟨n, n, rfl⟩) ?_
  rintro _ ⟨m, n, rfl⟩
  simp [count_replicate, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm,
    hbd.symm, hcd.symm]

end Language
