/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Symbols, rules and derivations of a context-free grammar

Lemmas on mathlib's `Symbol`, `ContextFreeRule` and `ContextFreeGrammar` that the derivation
trees, the closure properties and the weighted grammars share. `[UPSTREAM]` candidate for
`Mathlib/Computability/ContextFreeGrammar.lean`.

## Main definitions

* `Symbol.elim`, `Symbol.terminal?`, `Symbol.IsNonterminal`, `Symbol.mapNonterminal`: definition
  by cases on a symbol, the terminal at a symbol, the nonterminal predicate, and relabelling of
  nonterminals.
* `ContextFreeRule.NonterminalPos`: the positions of a right-hand side holding a nonterminal.
* `ContextFreeGrammar.inputs`, `ContextFreeGrammar.rulesWithInput`: the nonterminals a grammar has
  a rule for, and its rules at a nonterminal.

## Main results

* `ContextFreeGrammar.Derives.append_split`: a derivation from a concatenation splits into
  derivations from the two halves.
* `ContextFreeGrammar.Derives.mapNonterminal`, `ContextFreeGrammar.Derives.of_mapNonterminal`: a
  relabelling of nonterminals that sends rules to rules sends derivations to derivations, and
  reflects them when every rule at a relabelled nonterminal is a relabelled rule.

## References

* [J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation* (2000)][hopcroft-motwani-ullman-2000]
-/

@[expose] public section

/-- If every fibre of `f` is finite, then every fibre of `List.map f` is finite. -/
theorem List.finite_preimage_map {α β : Type*} {f : α → β} (hf : ∀ b, (f ⁻¹' {b}).Finite)
    (l' : List β) : (List.map f ⁻¹' {l'}).Finite := by
  induction l' with
  | nil => simp [Set.preimage]
  | cons b l' ih =>
    refine ((hf b).image2 List.cons ih).subset fun l h ↦ ?_
    obtain ⟨a, l, rfl, ha, hl⟩ := List.map_eq_cons_iff.mp h
    exact ⟨a, ha, l, hl, rfl⟩

namespace Symbol

variable {T N N' : Type*}

/-- The function on symbols that is `f` on the terminals and `X` on the nonterminals. -/
def elim {M : Type*} (f : T → M) (X : N → M) : Symbol T N → M
  | terminal a => f a
  | nonterminal A => X A

@[simp] theorem elim_terminal {M : Type*} (f : T → M) (X : N → M) (a : T) :
    (terminal a : Symbol T N).elim f X = f a := rfl

@[simp] theorem elim_nonterminal {M : Type*} (f : T → M) (X : N → M) (A : N) :
    (nonterminal A : Symbol T N).elim f X = X A := rfl

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

theorem mapNonterminal_eq_terminal_iff {f : N → N'} {s : Symbol T N} {a : T} :
    s.mapNonterminal f = terminal a ↔ s = terminal a := by cases s <;> simp

theorem mapNonterminal_eq_nonterminal_iff {f : N → N'} {s : Symbol T N} {B : N'} :
    s.mapNonterminal f = nonterminal B ↔ ∃ A, s = nonterminal A ∧ f A = B := by cases s <;> simp

@[simp] theorem mapNonterminal_comp_terminal (f : N → N') :
    mapNonterminal f ∘ (terminal : T → Symbol T N) = terminal := rfl

theorem map_mapNonterminal_map_terminal (f : N → N') (w : List T) :
    (w.map (terminal (N := N))).map (mapNonterminal f) = w.map terminal := by simp

/-- Relabelling the nonterminals of `l` gives the string of terminals `w` if and only if `l` is `w`.
-/
@[simp] theorem map_mapNonterminal_eq_map_terminal_iff {f : N → N'} {l : List (Symbol T N)}
    {w : List T} : l.map (mapNonterminal f) = w.map terminal ↔ l = w.map terminal := by
  induction l generalizing w with
  | nil => cases w <;> simp
  | cons s l ih => cases w <;> cases s <;> simp [ih]

/-- If every fibre of `f` is finite, then every fibre of `Symbol.mapNonterminal f` is finite. -/
theorem finite_preimage_mapNonterminal {f : N → N'} (hf : ∀ B, (f ⁻¹' {B}).Finite) :
    ∀ s : Symbol T N', (mapNonterminal f ⁻¹' {s}).Finite
  | terminal a =>
    (Set.finite_singleton (terminal a)).subset fun _ ↦ mapNonterminal_eq_terminal_iff.1
  | nonterminal B => ((hf B).image nonterminal).subset fun _ h ↦
      let ⟨A, hs, hA⟩ := mapNonterminal_eq_nonterminal_iff.1 h; ⟨A, hA, hs.symm⟩

instance [Countable T] [Countable N] : Countable (Symbol T N) :=
  Function.Injective.countable (f := fun s : Symbol T N ↦ match s with
    | .terminal t => Sum.inl t
    | .nonterminal n => Sum.inr n) fun s s' h ↦ by
    cases s <;> cases s' <;> simp_all

end Symbol

namespace ContextFreeRule

variable {T N N' : Type*}

/-- Relabel the nonterminals of a rule. -/
@[simps] def mapNonterminal (f : N → N') (r : ContextFreeRule T N) : ContextFreeRule T N' :=
  ⟨f r.input, r.output.map (Symbol.mapNonterminal f)⟩

/-- If every fibre of `f` is finite, then the preimage of a finite set of rules under
`ContextFreeRule.mapNonterminal f` is finite. -/
theorem finite_preimage_mapNonterminal {f : N → N'} (hf : ∀ B, (f ⁻¹' {B}).Finite)
    {s : Set (ContextFreeRule T N')} (hs : s.Finite) : (mapNonterminal f ⁻¹' s).Finite :=
  hs.preimage' fun r _ ↦ ((hf r.input).image2 mk
    (List.finite_preimage_map (Symbol.finite_preimage_mapNonterminal hf) r.output)).subset
      fun r' h ↦ ⟨r'.input, congrArg input h, r'.output, congrArg output h, rfl⟩

protected theorem Rewrites.mapNonterminal (f : N → N') {r : ContextFreeRule T N}
    {u v : List (Symbol T N)} (h : r.Rewrites u v) :
    (r.mapNonterminal f).Rewrites (u.map (Symbol.mapNonterminal f))
      (v.map (Symbol.mapNonterminal f)) := by
  obtain ⟨p, q, rfl, rfl⟩ := h.exists_parts
  simpa using rewrites_of_exists_parts (r.mapNonterminal f) (p.map (Symbol.mapNonterminal f))
    (q.map (Symbol.mapNonterminal f))

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

theorem Rewrites.not_map_terminal {r : ContextFreeRule T N} {w : List T}
    {v : List (Symbol T N)} : ¬ r.Rewrites (w.map .terminal) v := fun h ↦ by
  simpa using h.nonterminal_input_mem

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

theorem rewrites_singleton_iff {r : ContextFreeRule T N} {A : N} {v : List (Symbol T N)} :
    r.Rewrites [.nonterminal A] v ↔ r.input = A ∧ v = r.output := by
  simpa using rewrites_map_terminal_append_singleton_append_iff (r := r) (A := A) (w := [])
    (u := []) (v := v)

end ContextFreeRule

namespace ContextFreeGrammar

variable {T : Type*} {g : ContextFreeGrammar T}

section RulesWithInput

variable [DecidableEq g.NT] {a : g.NT} {r : ContextFreeRule T g.NT}

/-- The nonterminals `g` has a rule for, the inputs of its rules. -/
def inputs (g : ContextFreeGrammar T) [DecidableEq g.NT] : Finset g.NT :=
  g.rules.image (·.input)

/-- The rules of `g` with input `a`. -/
def rulesWithInput (g : ContextFreeGrammar T) [DecidableEq g.NT] (a : g.NT) :
    Finset (ContextFreeRule T g.NT) :=
  g.rules.filter (·.input = a)

theorem mem_inputs : a ∈ g.inputs ↔ ∃ r ∈ g.rules, r.input = a :=
  Finset.mem_image

@[simp]
theorem mem_rulesWithInput : r ∈ g.rulesWithInput a ↔ r ∈ g.rules ∧ r.input = a :=
  Finset.mem_filter

theorem coe_rulesWithInput :
    (g.rulesWithInput a : Set (ContextFreeRule T g.NT)) = {r | r ∈ g.rules ∧ r.input = a} :=
  Set.ext fun _ ↦ mem_rulesWithInput

theorem input_mem_inputs (hr : r ∈ g.rules) : r.input ∈ g.inputs :=
  Finset.mem_image_of_mem _ hr

theorem mem_rulesWithInput_input (hr : r ∈ g.rules) : r ∈ g.rulesWithInput r.input :=
  mem_rulesWithInput.mpr ⟨hr, rfl⟩

theorem rulesWithInput_nonempty_iff : (g.rulesWithInput a).Nonempty ↔ a ∈ g.inputs := by
  simp [Finset.Nonempty, mem_inputs]

instance (a : g.inputs) : Nonempty (g.rulesWithInput a) :=
  (rulesWithInput_nonempty_iff.mpr a.2).to_subtype

theorem rulesWithInput_eq_empty_iff : g.rulesWithInput a = ∅ ↔ a ∉ g.inputs := by
  rw [← rulesWithInput_nonempty_iff, Finset.not_nonempty_iff_eq_empty]

end RulesWithInput

/-- A rule of the grammar produces its right-hand side from its left-hand side. -/
theorem produces_input_output (g : ContextFreeGrammar T) {r : ContextFreeRule T g.NT}
    (hr : r ∈ g.rules) : g.Produces [.nonterminal r.input] r.output :=
  ⟨r, hr, .input_output⟩

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

section MapNonterminal

variable {g' : ContextFreeGrammar T} {f : g.NT → g'.NT} {u v : List (Symbol T g.NT)}

/-- If `f` sends every rule of `g` to a rule of `g'`, then relabelling nonterminals by `f` sends
every production of `g` to a production of `g'`. -/
protected theorem Produces.mapNonterminal (hf : ∀ r ∈ g.rules, r.mapNonterminal f ∈ g'.rules)
    (h : g.Produces u v) :
    g'.Produces (u.map (Symbol.mapNonterminal f)) (v.map (Symbol.mapNonterminal f)) :=
  let ⟨r, hr, hrw⟩ := h
  ⟨r.mapNonterminal f, hf r hr, hrw.mapNonterminal f⟩

/-- If `f` sends every rule of `g` to a rule of `g'`, then relabelling nonterminals by `f` sends
every derivation of `g` to a derivation of `g'`. -/
protected theorem Derives.mapNonterminal (hf : ∀ r ∈ g.rules, r.mapNonterminal f ∈ g'.rules)
    (h : g.Derives u v) :
    g'.Derives (u.map (Symbol.mapNonterminal f)) (v.map (Symbol.mapNonterminal f)) := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih => exact ih.trans_produces (step.mapNonterminal hf)

/-- Suppose that every rule of `g'` with left-hand side `f A` is the relabelling by `f` of a rule of
`g` with left-hand side `A`. If `g'` produces `v'` from the relabelling of `u`, then `v'` is the
relabelling of some `v` that `g` produces from `u`. -/
theorem Produces.of_mapNonterminal {v' : List (Symbol T g'.NT)}
    (hf : ∀ r' ∈ g'.rules, ∀ A, r'.input = f A →
      ∃ r ∈ g.rules, r.input = A ∧ r.output.map (Symbol.mapNonterminal f) = r'.output)
    (h : g'.Produces (u.map (Symbol.mapNonterminal f)) v') :
    ∃ v, g.Produces u v ∧ v.map (Symbol.mapNonterminal f) = v' := by
  obtain ⟨r', hr', hrw⟩ := h
  obtain ⟨p', q', hu, rfl⟩ := hrw.exists_parts
  obtain ⟨u₁, q, rfl, h₁, rfl⟩ := List.map_eq_append_iff.mp hu
  obtain ⟨p, m, rfl, rfl, hm⟩ := List.map_eq_append_iff.mp h₁
  obtain ⟨s, rfl, hs⟩ := List.map_eq_singleton_iff.mp hm
  obtain ⟨A, rfl, hA⟩ := Symbol.mapNonterminal_eq_nonterminal_iff.mp hs
  obtain ⟨r, hr, rfl, ho⟩ := hf r' hr' A hA.symm
  exact ⟨p ++ r.output ++ q, ⟨r, hr, ContextFreeRule.rewrites_of_exists_parts r p q⟩, by simp [ho]⟩

/-- Suppose that every rule of `g'` with left-hand side `f A` is the relabelling by `f` of a rule of
`g` with left-hand side `A`. If `g'` derives `v'` from the relabelling of `u`, then `v'` is the
relabelling of some `v` that `g` derives from `u`. -/
theorem Derives.of_mapNonterminal {v' : List (Symbol T g'.NT)}
    (hf : ∀ r' ∈ g'.rules, ∀ A, r'.input = f A →
      ∃ r ∈ g.rules, r.input = A ∧ r.output.map (Symbol.mapNonterminal f) = r'.output)
    (h : g'.Derives (u.map (Symbol.mapNonterminal f)) v') :
    ∃ v, g.Derives u v ∧ v.map (Symbol.mapNonterminal f) = v' := by
  induction h with
  | refl => exact ⟨u, .refl _, rfl⟩
  | tail _ step ih =>
    obtain ⟨v, hd, rfl⟩ := ih
    obtain ⟨v', hp, hv'⟩ := step.of_mapNonterminal hf
    exact ⟨v', hd.trans_produces hp, hv'⟩

end MapNonterminal

theorem not_produces_map_terminal {w : List T} {v : List (Symbol T g.NT)} :
    ¬ g.Produces (w.map .terminal) v := fun ⟨_, _, h⟩ ↦ h.not_map_terminal

/-- A string of terminals derives only itself. -/
theorem Derives.eq_of_map_terminal {w : List T} {v : List (Symbol T g.NT)}
    (h : g.Derives (w.map .terminal) v) : v = w.map .terminal := by
  rcases h.eq_or_head with rfl | ⟨_, hp, _⟩
  exacts [rfl, (not_produces_map_terminal hp).elim]

/-- If `terminal a :: u` derives `v`, then `v` is `terminal a :: v'` for some `v'` that `u` derives.
-/
theorem Derives.exists_of_terminal_cons {a : T} {u v : List (Symbol T g.NT)}
    (h : g.Derives (.terminal a :: u) v) : ∃ v', v = .terminal a :: v' ∧ g.Derives u v' := by
  obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := Derives.append_split (u₁ := [.terminal a]) h
  obtain rfl := Derives.eq_of_map_terminal (w := [a]) h₁
  exact ⟨v₂, rfl, h₂⟩

theorem produces_singleton_iff {A : g.NT} {v : List (Symbol T g.NT)} :
    g.Produces [.nonterminal A] v ↔ ∃ r ∈ g.rules, r.input = A ∧ v = r.output := by
  simp only [Produces, ContextFreeRule.rewrites_singleton_iff]

end ContextFreeGrammar
