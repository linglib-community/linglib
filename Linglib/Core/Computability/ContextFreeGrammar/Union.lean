/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar

/-!
# Context-free languages are closed under finite unions

The union `ContextFreeGrammar.iUnion g` of a finite family of grammars has the nonterminals of
every `g i`, tagged by `i`, and a fresh start symbol that rewrites to the start nonterminal of each
`g i`. Tagging is a relabelling of nonterminals that sends the rules of `g i` to rules of the union
and accounts for every rule of the union at a tagged nonterminal, so the union [generates the union
of the languages](##ContextFreeGrammar.language_iUnion). The context-free languages are therefore
[closed under finite unions](##Language.IsContextFree.iSup).

## References

* [hopcroft-motwani-ullman-2000]
-/

@[expose] public section

namespace ContextFreeGrammar

variable {T : Type*} {ι : Type} [Finite ι] {g : ι → ContextFreeGrammar T}

/-- The union of a finite family of grammars: the nonterminals of each `g i` tagged by `i`, with
the rules of `g i`, and a fresh start symbol `none` that rewrites to the start nonterminal of each
`g i`. -/
noncomputable def iUnion (g : ι → ContextFreeGrammar T) : ContextFreeGrammar T where
  NT := Option (Σ i, (g i).NT)
  initial := none
  rules := Set.Finite.toFinset
    (s := Set.range (fun i ↦ ⟨none, [.nonterminal (some ⟨i, (g i).initial⟩)]⟩) ∪
      ⋃ i, ContextFreeRule.mapNonterminal (fun A ↦ some ⟨i, A⟩) '' (g i).rules)
    ((Set.finite_range _).union (Set.finite_iUnion fun i ↦ (g i).rules.finite_toSet.image _))

theorem mem_iUnion_rules {r' : ContextFreeRule T (Option (Σ i, (g i).NT))} :
    r' ∈ (iUnion g).rules ↔ (∃ i, ⟨none, [.nonterminal (some ⟨i, (g i).initial⟩)]⟩ = r') ∨
      ∃ i, ∃ r ∈ (g i).rules, r.mapNonterminal (fun A ↦ some ⟨i, A⟩) = r' := by
  simp [iUnion]

/-- The union of a family of grammars generates the union of their languages. -/
@[simp] theorem language_iUnion (g : ι → ContextFreeGrammar T) :
    (iUnion g).language = ⨆ i, (g i).language := by
  ext w
  rw [Language.mem_iSup, mem_language_iff]
  constructor
  · intro h
    rcases h.eq_or_head with heq | ⟨v, hstep, hd⟩
    · cases w <;> simp at heq
    obtain ⟨r', hr', hin, rfl⟩ := produces_singleton_iff.mp hstep
    rcases mem_iUnion_rules.mp hr' with ⟨i, rfl⟩ | ⟨i, r, -, rfl⟩
    · obtain ⟨v, hv, hvw⟩ := Derives.of_mapNonterminal (g := g i) (g' := iUnion g)
        (f := fun A ↦ some ⟨i, A⟩) (u := [.nonterminal (g i).initial]) (fun r' hr' A hA ↦ by
          rcases mem_iUnion_rules.mp hr' with ⟨j, rfl⟩ | ⟨j, r, hr, rfl⟩
          · cases hA
          · cases hA
            exact ⟨r, hr, rfl, rfl⟩) hd
      rw [Symbol.map_mapNonterminal_eq_map_terminal_iff] at hvw
      subst hvw
      exact ⟨i, hv⟩
    · cases hin
  · rintro ⟨i, hi⟩
    refine (produces_singleton_iff.mpr ⟨_, mem_iUnion_rules.mpr (.inl ⟨i, rfl⟩), rfl, rfl⟩
      ).trans_derives ?_
    simpa using Derives.mapNonterminal (g' := iUnion g) (f := fun A ↦ some ⟨i, A⟩)
      (fun r hr ↦ mem_iUnion_rules.mpr (.inr ⟨i, r, hr, rfl⟩)) ((mem_language_iff _ _).mp hi)

end ContextFreeGrammar

namespace Language

variable {T : Type*}

/-- Context-free languages are closed under finite unions. -/
protected theorem IsContextFree.iSup {ι : Type*} [Finite ι] {L : ι → Language T}
    (h : ∀ i, (L i).IsContextFree) : (⨆ i, L i).IsContextFree := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  choose g hg using h
  exact ⟨.iUnion fun k ↦ g (e.symm k), by simpa [hg] using e.symm.iSup_comp (g := L)⟩

/-- Context-free languages are closed under union. -/
protected theorem IsContextFree.add {L₁ L₂ : Language T} (h₁ : L₁.IsContextFree)
    (h₂ : L₂.IsContextFree) : (L₁ + L₂).IsContextFree := by
  have := IsContextFree.iSup (L := fun b : Bool ↦ bif b then L₁ else L₂)
    (by rintro (_ | _) <;> assumption)
  rwa [iSup_bool_eq] at this

end Language
