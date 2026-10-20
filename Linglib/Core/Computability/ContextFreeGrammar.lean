/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.DFA
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Symbols, rules and derivations of a context-free grammar

Lemmas on mathlib's `Symbol`, `ContextFreeRule` and `ContextFreeGrammar` that the derivation
trees, the closure properties and the weighted grammars share. `[UPSTREAM]` candidate for
`Mathlib/Computability/ContextFreeGrammar.lean`.

## Main definitions

* `Symbol.terminal?`, `Symbol.IsNonterminal`, `Symbol.mapNonterminal`: the terminal at a symbol,
  the nonterminal predicate, and relabelling of nonterminals.
* `ContextFreeRule.NonterminalPos`: the positions of a right-hand side holding a nonterminal.
* `ContextFreeGrammar.RulesWithLHS`: the rules of a grammar with a given left-hand side.
* `DFA.toContextFreeGrammar M`: the right-linear grammar of a finite automaton over a finite
  alphabet.

## Main results

* `ContextFreeGrammar.Derives.append_split`: a derivation from a concatenation splits into
  derivations from the two halves.
* `ContextFreeGrammar.produces_map_terminal_append_singleton_append_iff`: the one-step
  productions of a word with a single nonterminal, the step of linear grammars.
* `ContextFreeGrammar.Derives.terminal_mem`: a derivation introduces only terminals that occur in
  the output of a rule.
* `DFA.language_toContextFreeGrammar`: the right-linear grammar of `M` generates the language of
  `M`, so over a finite alphabet regular languages are context-free
  (`Language.IsRegular.isContextFree`).
* `Language.isContextFree_top_iff`: the language of all words is context-free exactly when the
  alphabet is finite.

## Implementation notes

The right-linear grammar of a finite automaton `M` has a nonterminal for each state, a rule
`q → a q'` for each transition from `q` to `q'` on the letter `a`, and a rule `q → ε` for each
accepting state `q`; its sentential forms are a word `w` followed by the state `M.eval w`, or an
accepted word. The alphabet must be finite, because a grammar has finitely many rules and so uses
finitely many letters: over an infinite alphabet the language of all words is regular, by a
one-state automaton, but not context-free.

## References

* [J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation* (2000)][hopcroft-motwani-ullman-2000]
-/

@[expose] public section

namespace Symbol

variable {T N N' : Type*}

/-- The terminal at a symbol, if it is one. -/
def terminal? : Symbol T N → Option T
  | .terminal a => some a
  | .nonterminal _ => none

@[simp] theorem terminal?_terminal (a : T) : (terminal a : Symbol T N).terminal? = some a := rfl

@[simp] theorem terminal?_nonterminal (A : N) :
    (nonterminal A : Symbol T N).terminal? = none := rfl

/-- The nonterminal symbols. -/
def IsNonterminal : Symbol T N → Prop
  | terminal _ => False
  | nonterminal _ => True

instance : DecidablePred (IsNonterminal : Symbol T N → Prop)
  | terminal _ => isFalse id
  | nonterminal _ => isTrue trivial

@[simp] theorem isNonterminal_nonterminal (A : N) : (nonterminal A : Symbol T N).IsNonterminal :=
  trivial

@[simp] theorem not_isNonterminal_terminal (a : T) : ¬ (terminal a : Symbol T N).IsNonterminal :=
  id

theorem isNonterminal_iff_terminal?_eq_none (s : Symbol T N) :
    s.IsNonterminal ↔ s.terminal? = none := by
  cases s <;> simp

/-- Relabel the nonterminals of a symbol. -/
def mapNonterminal (f : N → N') : Symbol T N → Symbol T N'
  | .terminal a => .terminal a
  | .nonterminal A => .nonterminal (f A)

@[simp] theorem mapNonterminal_terminal (f : N → N') (a : T) :
    mapNonterminal f (terminal a : Symbol T N) = terminal a := rfl

@[simp] theorem mapNonterminal_nonterminal (f : N → N') (A : N) :
    mapNonterminal f (nonterminal A : Symbol T N) = nonterminal (f A) := rfl

@[simp] theorem terminal?_mapNonterminal (f : N → N') (s : Symbol T N) :
    (s.mapNonterminal f).terminal? = s.terminal? := by cases s <;> rfl

instance [Countable T] [Countable N] : Countable (Symbol T N) :=
  Function.Injective.countable (f := fun s : Symbol T N => match s with
    | .terminal t => Sum.inl t
    | .nonterminal n => Sum.inr n) fun s s' h => by
    cases s <;> cases s' <;> simp_all

end Symbol

namespace ContextFreeRule

variable {T N : Type*}

/-- The positions on the right-hand side of `r` that hold a nonterminal: the slots at which a
derivation from `r` branches. -/
abbrev NonterminalPos (r : ContextFreeRule T N) : Type :=
  {i : Fin r.output.length // r.output[i].IsNonterminal}

/-- A rewrite of a concatenation `u₁ ++ u₂` happens entirely in `u₁` or entirely in `u₂`. -/
theorem Rewrites.append_split {r : ContextFreeRule T N} :
    ∀ {u₁ u₂ v : List (Symbol T N)}, r.Rewrites (u₁ ++ u₂) v →
      (∃ v₁, v = v₁ ++ u₂ ∧ r.Rewrites u₁ v₁) ∨ (∃ v₂, v = u₁ ++ v₂ ∧ r.Rewrites u₂ v₂) := by
  intro u₁ u₂ v hrw
  induction u₁ generalizing v with
  | nil => exact .inr ⟨v, by simp, by simpa using hrw⟩
  | cons x u₁ ih =>
    rw [List.cons_append] at hrw
    cases hrw with
    | head s => exact .inl ⟨r.output ++ u₁, by simp, .head u₁⟩
    | cons x hrw =>
      rcases ih hrw with ⟨v₁, rfl, hrw₁⟩ | ⟨v₂, rfl, hrw₂⟩
      · exact .inl ⟨x :: v₁, by simp, .cons x hrw₁⟩
      · exact .inr ⟨v₂, by simp, hrw₂⟩

/-- No rule rewrites a word of terminals. -/
theorem Rewrites.not_map_terminal {r : ContextFreeRule T N} {w : List T}
    {v : List (Symbol T N)} : ¬ r.Rewrites (w.map .terminal) v := fun h ↦ by
  simpa using h.nonterminal_input_mem

/-- A rewrite of a word with a single nonterminal replaces that nonterminal by the output of a
rule with that input. -/
theorem rewrites_map_terminal_append_singleton_append_iff {r : ContextFreeRule T N} {A : N}
    {w u : List T} {v : List (Symbol T N)} :
    r.Rewrites (w.map .terminal ++ [.nonterminal A] ++ u.map .terminal) v ↔
      r.input = A ∧ v = w.map .terminal ++ r.output ++ u.map .terminal := by
  refine ⟨fun h ↦ ?_, fun ⟨hA, hv⟩ ↦ hA ▸ hv ▸ (Rewrites.input_output.append_left _).append_right _⟩
  rcases h.append_split with ⟨v₁, rfl, h₁⟩ | ⟨_, -, h₂⟩
  · rcases h₁.append_split with ⟨_, -, h₀⟩ | ⟨v₂, rfl, h₃⟩
    · exact h₀.not_map_terminal.elim
    · clear h h₁
      cases h₃ with
      | head => simp
      | cons _ h => cases h
  · exact h₂.not_map_terminal.elim

/-- A rewrite of a single nonterminal replaces it by the output of a rule with that input. -/
theorem rewrites_singleton_iff {r : ContextFreeRule T N} {A : N} {v : List (Symbol T N)} :
    r.Rewrites [.nonterminal A] v ↔ r.input = A ∧ v = r.output := by
  simpa using rewrites_map_terminal_append_singleton_append_iff (r := r) (A := A) (w := [])
    (u := []) (v := v)

end ContextFreeRule

namespace ContextFreeGrammar

variable {T : Type*} {g : ContextFreeGrammar T}

/-- The rules of `g` with left-hand side `a`. -/
abbrev RulesWithLHS (g : ContextFreeGrammar T) [DecidableEq g.NT] (a : g.NT) :=
  {r : ContextFreeRule T g.NT // r ∈ g.rules.filter (·.input = a)}

/-- A production from a concatenation `u₁ ++ u₂` happens entirely in `u₁` or entirely in
`u₂`. -/
theorem Produces.append_split {u₁ u₂ v : List (Symbol T g.NT)} (h : g.Produces (u₁ ++ u₂) v) :
    (∃ v₁, v = v₁ ++ u₂ ∧ g.Produces u₁ v₁) ∨ (∃ v₂, v = u₁ ++ v₂ ∧ g.Produces u₂ v₂) := by
  obtain ⟨r, hr, hrw⟩ := h
  rcases hrw.append_split with ⟨v₁, hv, hrw₁⟩ | ⟨v₂, hv, hrw₂⟩
  · exact .inl ⟨v₁, hv, r, hr, hrw₁⟩
  · exact .inr ⟨v₂, hv, r, hr, hrw₂⟩

/-- A derivation from a concatenation `u₁ ++ u₂` splits into derivations from `u₁` and from
`u₂`. -/
theorem Derives.append_split {u₁ u₂ v : List (Symbol T g.NT)} (h : g.Derives (u₁ ++ u₂) v) :
    ∃ v₁ v₂, v = v₁ ++ v₂ ∧ g.Derives u₁ v₁ ∧ g.Derives u₂ v₂ := by
  induction h with
  | refl => exact ⟨u₁, u₂, rfl, .refl _, .refl _⟩
  | tail _ step ih =>
    obtain ⟨w₁, w₂, rfl, hd₁, hd₂⟩ := ih
    rcases step.append_split with ⟨v₁, hv, hp₁⟩ | ⟨v₂, hv, hp₂⟩
    · exact ⟨v₁, w₂, hv, hd₁.trans_produces hp₁, hd₂⟩
    · exact ⟨w₁, v₂, hv, hd₁, hd₂.trans_produces hp₂⟩

/-- A word of terminals produces nothing. -/
theorem not_produces_map_terminal {w : List T} {v : List (Symbol T g.NT)} :
    ¬ g.Produces (w.map .terminal) v := fun ⟨_, _, h⟩ ↦ h.not_map_terminal

/-- A word with a single nonterminal produces exactly the words obtained by replacing that
nonterminal with the output of one of its rules. -/
theorem produces_map_terminal_append_singleton_append_iff {A : g.NT} {w u : List T}
    {v : List (Symbol T g.NT)} :
    g.Produces (w.map .terminal ++ [.nonterminal A] ++ u.map .terminal) v ↔
      ∃ r ∈ g.rules, r.input = A ∧ v = w.map .terminal ++ r.output ++ u.map .terminal := by
  simp only [Produces, ContextFreeRule.rewrites_map_terminal_append_singleton_append_iff]

/-- A word ending in its only nonterminal produces exactly the words obtained by replacing that
nonterminal with the output of one of its rules, the step of right-linear grammars. -/
theorem produces_map_terminal_append_singleton_iff {A : g.NT} {w : List T}
    {v : List (Symbol T g.NT)} :
    g.Produces (w.map .terminal ++ [.nonterminal A]) v ↔
      ∃ r ∈ g.rules, r.input = A ∧ v = w.map .terminal ++ r.output := by
  simpa using produces_map_terminal_append_singleton_append_iff (A := A) (w := w) (u := []) (v := v)

/-- A single nonterminal produces exactly the outputs of its rules. -/
theorem produces_singleton_iff {A : g.NT} {v : List (Symbol T g.NT)} :
    g.Produces [.nonterminal A] v ↔ ∃ r ∈ g.rules, r.input = A ∧ v = r.output := by
  simp only [Produces, ContextFreeRule.rewrites_singleton_iff]

/-- A terminal of a derived word is a terminal of the source word or of the output of a rule. -/
theorem Derives.terminal_mem {u v : List (Symbol T g.NT)} (h : g.Derives u v) {a : T}
    (ha : .terminal a ∈ v) : .terminal a ∈ u ∨ ∃ r ∈ g.rules, .terminal a ∈ r.output := by
  induction h with
  | refl => exact .inl ha
  | tail _ hstep ih =>
    obtain ⟨r, hr, hrw⟩ := hstep
    obtain ⟨p, q, rfl, rfl⟩ := hrw.exists_parts
    simp only [List.mem_append] at ha
    rcases ha with (hp | ho) | hq
    · exact ih (by simp [hp])
    · exact .inr ⟨r, hr, ho⟩
    · exact ih (by simp [hq])

end ContextFreeGrammar

/-! ### Regular languages -/

section Regular

open List Symbol

namespace DFA

variable {α : Type*} {σ : Type} [Fintype α] [Fintype σ] (M : DFA α σ)
  [DecidablePred (· ∈ M.accept)]

/-- The right-linear grammar of `M` has a nonterminal for each state, a rule `q → a (M.step q a)`
for each state `q` and letter `a`, and a rule `q → ε` for each accepting state `q`. -/
def toContextFreeGrammar : ContextFreeGrammar α where
  NT := σ
  initial := M.start
  rules :=
    (Finset.univ.map ⟨fun x : σ × α ↦ ⟨x.1, [terminal x.2, nonterminal (M.step x.1 x.2)]⟩,
      fun x y h ↦ by simp_all [Prod.ext_iff]⟩).disjUnion
    ((Finset.univ.filter (· ∈ M.accept)).map ⟨fun q ↦ ⟨q, []⟩, fun p q h ↦ by simpa using h⟩)
    (by simp only [Finset.disjoint_left, Finset.mem_map]; rintro _ ⟨_, -, rfl⟩ ⟨_, -, h⟩; simp at h)

variable {M}

theorem mem_rules_toContextFreeGrammar {r : ContextFreeRule α σ} :
    r ∈ M.toContextFreeGrammar.rules ↔
      (∃ a, r.output = [terminal a, nonterminal (M.step r.input a)]) ∨
        (r.input ∈ M.accept ∧ r.output = []) := by
  obtain ⟨q, o⟩ := r
  unfold toContextFreeGrammar
  simp [eq_comm]

/-- The grammar of `M` derives every word followed by the state `M` reaches on it. -/
theorem derives_toContextFreeGrammar (w : List α) :
    M.toContextFreeGrammar.Derives [nonterminal M.start]
      (w.map terminal ++ [nonterminal (M.eval w)]) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    refine ih.trans_produces (ContextFreeGrammar.produces_map_terminal_append_singleton_iff.2
      ⟨⟨M.eval w, [terminal a, nonterminal (M.step (M.eval w) a)]⟩,
        mem_rules_toContextFreeGrammar.2 (.inl ⟨a, rfl⟩), rfl, ?_⟩)
    simp [eval_append_singleton]

/-- The sentential forms of the grammar of `M` are a word followed by the state `M` reaches on it,
and the words `M` accepts. -/
theorem derives_toContextFreeGrammar_iff {v : List (Symbol α σ)} :
    M.toContextFreeGrammar.Derives [nonterminal M.start] v ↔ ∃ w,
      v = w.map terminal ++ [nonterminal (M.eval w)] ∨
        (v = w.map terminal ∧ M.eval w ∈ M.accept) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · induction h with
    | refl => exact ⟨[], .inl rfl⟩
    | tail _ hstep ih =>
      obtain ⟨w, rfl | ⟨rfl, -⟩⟩ := ih
      · obtain ⟨r, hr, hq, rfl⟩ :=
          ContextFreeGrammar.produces_map_terminal_append_singleton_iff.1 hstep
        obtain ⟨a, ho⟩ | ⟨hacc, ho⟩ := mem_rules_toContextFreeGrammar.1 hr
        · exact ⟨w ++ [a], .inl (by simp [ho, hq, eval_append_singleton])⟩
        · exact ⟨w, .inr ⟨by simp [ho], hq ▸ hacc⟩⟩
      · exact (ContextFreeGrammar.not_produces_map_terminal hstep).elim
  · rintro ⟨w, rfl | ⟨rfl, hacc⟩⟩
    · exact derives_toContextFreeGrammar w
    · exact (derives_toContextFreeGrammar w).trans_produces
        (ContextFreeGrammar.produces_map_terminal_append_singleton_iff.2
          ⟨⟨M.eval w, []⟩, mem_rules_toContextFreeGrammar.2 (.inr ⟨hacc, rfl⟩), rfl, by simp⟩)

/-- The grammar of `M` generates the language of `M`. -/
theorem language_toContextFreeGrammar : M.toContextFreeGrammar.language = M.accepts := by
  ext w
  change M.toContextFreeGrammar.Derives [nonterminal M.start] _ ↔ _
  rw [derives_toContextFreeGrammar_iff, mem_accepts]
  refine ⟨fun ⟨u, h⟩ ↦ ?_, fun h ↦ ⟨w, .inr ⟨rfl, h⟩⟩⟩
  rcases h with h | ⟨h, hacc⟩
  · simpa using congr(nonterminal (M.eval u) ∈ $h)
  · rwa [map_injective_iff.2 (fun _ _ ↦ terminal.inj) h]

end DFA

namespace Language

variable {α : Type*}

/-- Over a finite alphabet, every regular language is context-free. -/
theorem IsRegular.isContextFree [Finite α] {L : Language α} (h : L.IsRegular) :
    L.IsContextFree := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨σ, _, M, rfl⟩ := h
  exact ⟨M.toContextFreeGrammar, DFA.language_toContextFreeGrammar⟩

/-- The language of all words is context-free exactly when the alphabet is finite: it is regular
over any alphabet, but a grammar has finitely many rules and so uses finitely many letters. -/
theorem isContextFree_top_iff : (⊤ : Language α).IsContextFree ↔ Finite α := by
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun _ ↦ IsRegular.isContextFree ?_⟩
  · have hS : (⋃ r ∈ g.rules, terminal ⁻¹' {s : Symbol α g.NT | s ∈ r.output}).Finite :=
      g.rules.finite_toSet.biUnion fun r _ ↦
        r.output.finite_toSet.preimage fun _ _ _ _ ↦ terminal.inj
    refine Set.finite_univ_iff.1 (hS.subset fun a _ ↦ ?_)
    have hd : g.Derives [nonterminal g.initial] [terminal a] :=
      (ContextFreeGrammar.mem_language_iff g [a]).1 (hg ▸ trivial)
    obtain h | ⟨r, hr, ho⟩ := hd.terminal_mem (mem_singleton_self _)
    · simp at h
    · exact Set.mem_iUnion₂.2 ⟨r, hr, ho⟩
  · exact ⟨Unit, inferInstance, ⟨fun _ _ ↦ (), (), Set.univ⟩, top_unique fun _ _ ↦ trivial⟩

end Language

end Regular
