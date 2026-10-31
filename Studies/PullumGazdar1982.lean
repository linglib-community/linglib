module

public import Linglib.Core.Computability.ContextFreeGrammar.Tree
public import Linglib.Data.Examples.PullumGazdar1982
public import Linglib.Data.Examples.Readers

/-!
# Pullum and Gazdar (1982): Natural Languages and Context-Free Languages

This file formalizes [pullum-gazdar-1982]'s examination of the published arguments that some
natural language is not a context-free stringset, each of which the paper finds formally or
empirically invalid. The formal exhibits are grammars. The finite state grammar of §1 generates
unbounded long-distance number concord (`concordGrammar`, `concord_unbounded`). Grammar (9)
generates exactly the nonidentity language (8) that Chomsky's comparative argument took to be
beyond context-free power (`xyGrammar_language`), so the language is context-free
(`isXY_isContextFree`). Grammar (29) generates exactly the Dutch verb-raising verb phrases (24)
with as many object names as transitive verbs, which Huybregts's cross-serial dependencies were
held to put beyond context-free power (`dutchGrammar_language`, `isVerbPhrase_isContextFree`),
and the Dutch examples (25) to (31) fall out as predicted (`dutch_rows`). The empirical
refutations are rows: the *respectively* judgments (18) and (19) contradict the number-matching
characterization of English that the argument assumes (`respectively_converse`), and Mohawk
classificatory and possessed incorporation, (39), (40), and (43d), break the stem-matching
premise of the Mohawk argument (`stem_matching_fails`).

## Implementation notes

Grammars are mathlib's `ContextFreeGrammar`, and the language theorems go through derivation
trees: soundness by induction on a licensed tree, with what each nonterminal generates spelled out
(`Generated`), and completeness by building the derivation. The Dutch verb phrases are described
as the paper does, with the categories of the lexicon (29b) as terminals; the row predictions
decide membership by stripping the names and counting the transitive verbs (`isVerbPhrase`),
which is proved equivalent to the description. Finite stateness is the right-linear form of the
rules, since mathlib has no bridge from grammars to regular languages. The π argument of §3, the
xx-language closure argument of §1, the ditransitive schema (32), and the Mohawk translation of
Langendoen's finite state language are not formalized.

## References

* [pullum-gazdar-1982]
* [huybregts-1976]
* [bar-hillel-shamir-1960]
-/

@[expose] public section

namespace PullumGazdar1982

open Examples

private theorem produces_of_mem {T : Type*} {g : ContextFreeGrammar T} {r : ContextFreeRule T g.NT}
    (hr : r ∈ g.rules) : g.Produces [.nonterminal r.input] r.output :=
  ⟨r, hr, ContextFreeRule.Rewrites.input_output⟩

private theorem yield_eq_of_value_terminal {T : Type*} {g : ContextFreeGrammar T}
    {t : RoseTree (Symbol T g.NT)} (ht : t.Licensed g.Licenses) {a : T}
    (hv : t.value = .terminal a) :
    t.yield = [a] := by
  induction ht using RoseTree.Licensed.grammar_induction with
  | terminal b =>
    obtain rfl : b = a := by simpa [RoseTree.leaf] using hv
    simp [RoseTree.leaf]
  | nonterminal => simp at hv

/-! ### §1: unbounded concord in a finite state language -/

/-- The words of the finite state grammar of §1. -/
inductive Word
  | which | problem | problems | did | your | professor | say | she | you | thought | was | were
  | unsolvable
  deriving DecidableEq, Repr

/-- Its three nonterminals. -/
inductive ConcordNT
  | S | T | U
  deriving DecidableEq, Repr

open Symbol in
/-- In the finite state grammar of §1 a singular or plural *which*-phrase selects the chain of
*she thought* and *you thought* clauses ending in the agreeing verb. -/
def concordGrammar : ContextFreeGrammar Word where
  NT := ConcordNT
  initial := .S
  rules := {⟨.S, [terminal .which, terminal .problem, terminal .did, terminal .your,
      terminal .professor, terminal .say, nonterminal .T]⟩,
    ⟨.S, [terminal .which, terminal .problems, terminal .did, terminal .your,
      terminal .professor, terminal .say, nonterminal .U]⟩,
    ⟨.T, [terminal .she, terminal .thought, nonterminal .T]⟩,
    ⟨.T, [terminal .you, terminal .thought, nonterminal .T]⟩,
    ⟨.T, [terminal .was, terminal .unsolvable]⟩,
    ⟨.U, [terminal .she, terminal .thought, nonterminal .U]⟩,
    ⟨.U, [terminal .you, terminal .thought, nonterminal .U]⟩,
    ⟨.U, [terminal .were, terminal .unsolvable]⟩}

/-- A rule of the concord grammar. -/
private abbrev CRule := ContextFreeRule Word ConcordNT

private theorem cprod {r : CRule} (hr : r ∈ concordGrammar.rules) :
    concordGrammar.Produces [.nonterminal r.input] r.output :=
  produces_of_mem hr

/-- In a finite state grammar every rule rewrites to terminals followed by at most one
nonterminal. -/
def IsFiniteState {T : Type*} (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, ∀ s ∈ r.output.dropLast, (Symbol.terminal? s).isSome

theorem concordGrammar_isFiniteState : IsFiniteState concordGrammar := by
  intro r hr
  simp only [concordGrammar, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A chain of *she thought* and *you thought* clauses. -/
def chain (ps : List Bool) : List Word :=
  ps.flatMap λ b => if b then [.she, .thought] else [.you, .thought]

private theorem derives_chain (ps : List Bool) :
    concordGrammar.Derives [.nonterminal .U]
        ((chain ps ++ [Word.were, .unsolvable]).map .terminal) ∧
      concordGrammar.Derives [.nonterminal .T]
        ((chain ps ++ [Word.was, .unsolvable]).map .terminal) := by
  induction ps with
  | nil =>
    exact ⟨(cprod (r := ⟨.U, [.terminal .were, .terminal .unsolvable]⟩) (by decide)).single,
      (cprod (r := ⟨.T, [.terminal .was, .terminal .unsolvable]⟩) (by decide)).single⟩
  | cons b ps ih =>
    obtain ⟨ihU, ihT⟩ := ih
    cases b
    · refine ⟨(cprod (r := ⟨.U, [.terminal .you, .terminal .thought, .nonterminal .U]⟩)
          (by decide)).trans_derives ?_,
        (cprod (r := ⟨.T, [.terminal .you, .terminal .thought, .nonterminal .T]⟩)
          (by decide)).trans_derives ?_⟩
      · simpa [chain] using ihU.append_left [Symbol.terminal .you, .terminal .thought]
      · simpa [chain] using ihT.append_left [Symbol.terminal .you, .terminal .thought]
    · refine ⟨(cprod (r := ⟨.U, [.terminal .she, .terminal .thought, .nonterminal .U]⟩)
          (by decide)).trans_derives ?_,
        (cprod (r := ⟨.T, [.terminal .she, .terminal .thought, .nonterminal .T]⟩)
          (by decide)).trans_derives ?_⟩
      · simpa [chain] using ihU.append_left [Symbol.terminal .she, .terminal .thought]
      · simpa [chain] using ihT.append_left [Symbol.terminal .she, .terminal .thought]

theorem concord_unbounded (ps : List Bool) :
    [Word.which, .problems, .did, .your, .professor, .say] ++ chain ps ++ [.were, .unsolvable]
        ∈ concordGrammar.language ∧
      [Word.which, .problem, .did, .your, .professor, .say] ++ chain ps ++ [.was, .unsolvable]
        ∈ concordGrammar.language := by
  obtain ⟨hU, hT⟩ := derives_chain ps
  constructor
  · rw [ContextFreeGrammar.mem_language_iff]
    refine (cprod (r := ⟨.S, [.terminal .which, .terminal .problems, .terminal .did,
      .terminal .your, .terminal .professor, .terminal .say, .nonterminal .U]⟩)
      (by decide)).trans_derives ?_
    simpa using hU.append_left [Symbol.terminal .which, .terminal .problems, .terminal .did,
      .terminal .your, .terminal .professor, .terminal .say]
  · rw [ContextFreeGrammar.mem_language_iff]
    refine (cprod (r := ⟨.S, [.terminal .which, .terminal .problem, .terminal .did,
      .terminal .your, .terminal .professor, .terminal .say, .nonterminal .T]⟩)
      (by decide)).trans_derives ?_
    simpa using hT.append_left [Symbol.terminal .which, .terminal .problem, .terminal .did,
      .terminal .your, .terminal .professor, .terminal .say]

/-! ### §2: the nonidentity language (8) and grammar (9) -/

/-- The terminal vocabulary of (8) has the two letters of the differing substrings and the three
markers. -/
inductive Sym
  | a | b | alpha | beta | gamma
  deriving DecidableEq, Repr

/-- Among the nonterminals of grammar (9), `S₁`, `S₂`, `A₁`, `B₁` are the paper's `S'`, `S''`,
`A'`, `B'`. -/
inductive XYNT
  | S | S₁ | S₂ | A | B | A₁ | B₁ | C | D
  deriving DecidableEq, Repr

open Symbol in
/-- Grammar (9), rules (a) to (i) in order. -/
def xyGrammar : ContextFreeGrammar Sym where
  NT := XYNT
  initial := .S
  rules := {⟨.S, [terminal .alpha, nonterminal .S₁, terminal .gamma]⟩,
    ⟨.S, [terminal .alpha, nonterminal .S₂, terminal .gamma]⟩,
    ⟨.S₁, [nonterminal .C, nonterminal .S₁, nonterminal .C]⟩,
    ⟨.S₁, [nonterminal .D, terminal .beta]⟩,
    ⟨.S₁, [terminal .beta, nonterminal .D]⟩,
    ⟨.S₂, [nonterminal .A, nonterminal .B₁]⟩,
    ⟨.S₂, [nonterminal .B, nonterminal .A₁]⟩,
    ⟨.A, [nonterminal .C, nonterminal .A, nonterminal .C]⟩,
    ⟨.A, [terminal .a, terminal .beta]⟩,
    ⟨.A, [terminal .a, nonterminal .D, terminal .beta]⟩,
    ⟨.B, [nonterminal .C, nonterminal .B, nonterminal .C]⟩,
    ⟨.B, [terminal .b, terminal .beta]⟩,
    ⟨.B, [terminal .b, nonterminal .D, terminal .beta]⟩,
    ⟨.A₁, [terminal .a]⟩,
    ⟨.A₁, [terminal .a, nonterminal .D]⟩,
    ⟨.B₁, [terminal .b]⟩,
    ⟨.B₁, [terminal .b, nonterminal .D]⟩,
    ⟨.C, [terminal .a]⟩,
    ⟨.C, [terminal .b]⟩,
    ⟨.D, [nonterminal .C]⟩,
    ⟨.D, [nonterminal .C, nonterminal .D]⟩}

/-- A rule of grammar (9). -/
private abbrev XRule := ContextFreeRule Sym XYNT

private theorem xprod {r : XRule} (hr : r ∈ xyGrammar.rules) :
    xyGrammar.Produces [.nonterminal r.input] r.output :=
  produces_of_mem hr

/-- A string over `a` and `b`. -/
def AB (l : List Sym) : Prop := ∀ c ∈ l, c = .a ∨ c = .b

/-- The language (8) has a central marker between two strings over `a` and `b` that differ. -/
def IsXY (w : List Sym) : Prop :=
  ∃ x y, w = .alpha :: x ++ .beta :: y ++ [.gamma] ∧ AB x ∧ AB y ∧ x ≠ y

/-- Each nonterminal of grammar (9) generates its own strings. `S₁` generates a marker between
strings of different lengths, `S₂` a marker between strings differing at some position, `A` and
`B` a specified `a` or `b` flanked by equally many characters before it and after the marker, and
`A₁` and `B₁` a specified `a` or `b` and a tail. -/
def Generated : XYNT → List Sym → Prop
  | .C, w => w = [.a] ∨ w = [.b]
  | .D, w => w ≠ [] ∧ AB w
  | .A₁, w => ∃ d, w = .a :: d ∧ AB d
  | .B₁, w => ∃ d, w = .b :: d ∧ AB d
  | .A, w => ∃ u d u', w = u ++ .a :: d ++ .beta :: u' ∧ AB u ∧ AB d ∧ AB u' ∧
      u.length = u'.length
  | .B, w => ∃ u d u', w = u ++ .b :: d ++ .beta :: u' ∧ AB u ∧ AB d ∧ AB u' ∧
      u.length = u'.length
  | .S₁, w => ∃ x y, w = x ++ .beta :: y ∧ AB x ∧ AB y ∧ x.length ≠ y.length
  | .S₂, w => ∃ x y, w = x ++ .beta :: y ∧ AB x ∧ AB y ∧ x ≠ y
  | .S, w => IsXY w

private theorem AB_nil : AB [] := by simp [AB]

private theorem AB_cons {c : Sym} {l : List Sym} (hc : c = .a ∨ c = .b) (hl : AB l) :
    AB (c :: l) := by
  simp only [AB, List.mem_cons, forall_eq_or_imp]
  exact ⟨hc, hl⟩

private theorem AB_append {l₁ l₂ : List Sym} (h₁ : AB l₁) (h₂ : AB l₂) : AB (l₁ ++ l₂) := by
  simp only [AB, List.mem_append]
  exact λ c hc => hc.elim (h₁ c) (h₂ c)

private theorem ne_of_append_cons {u u' d e : List Sym} {p q : Sym} (hlen : u.length = u'.length)
    (hpq : p ≠ q) : u ++ p :: d ≠ u' ++ q :: e := by
  intro h
  exact hpq (List.cons.inj (List.append_inj_right h hlen)).1

private theorem exists_of_generated_C {w : List Sym} (h : Generated .C w) :
    ∃ p, w = [p] ∧ (p = .a ∨ p = .b) := by
  rcases h with rfl | rfl
  · exact ⟨.a, rfl, Or.inl rfl⟩
  · exact ⟨.b, rfl, Or.inr rfl⟩

-- (9), (8)
theorem xy_sound {t : RoseTree (Symbol Sym xyGrammar.NT)} (ht : t.Licensed xyGrammar.Licenses) :
    ∀ N, t.value = .nonterminal N → Generated N t.yield := by
  induction ht using RoseTree.Licensed.grammar_induction with
  | terminal x => simp [RoseTree.leaf]
  | nonterminal N cs hrule hcs ih =>
    intro N' hN
    obtain rfl : N = N' := Symbol.nonterminal.inj hN
    simp only [RoseTree.yield_node_nonterminal]
    rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, _ | ⟨c₄, cs⟩⟩⟩⟩ <;> simp [xyGrammar] at hrule
    · rcases hrule with ⟨rfl, h₁⟩ | ⟨rfl, h₁⟩ | ⟨rfl, h₁⟩ | ⟨rfl, h₁⟩ | ⟨rfl, h₁⟩
      · -- A₁ → a
        exact ⟨[], by simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁], AB_nil⟩
      · -- B₁ → b
        exact ⟨[], by simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁], AB_nil⟩
      · -- C → a
        exact Or.inl (by simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁])
      · -- C → b
        exact Or.inr (by simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁])
      · -- D → C
        obtain ⟨p, hp, hpab⟩ := exists_of_generated_C (ih c₁ (by simp) _ h₁)
        exact ⟨by simp [hp], by simpa [hp] using AB_cons hpab AB_nil⟩
    · rcases hrule with ⟨rfl, h₁, h₂⟩ | ⟨rfl, h₁, h₂⟩ | ⟨rfl, h₁, h₂⟩ | ⟨rfl, h₁, h₂⟩ |
        ⟨rfl, h₁, h₂⟩ | ⟨rfl, h₁, h₂⟩ | ⟨rfl, h₁, h₂⟩ | ⟨rfl, h₁, h₂⟩ | ⟨rfl, h₁, h₂⟩
      · -- S₁ → D β
        obtain ⟨hne, hab⟩ := ih c₁ (by simp) _ h₁
        refine ⟨c₁.yield, [], ?_, hab, AB_nil, by simpa using hne⟩
        simp [yield_eq_of_value_terminal (hcs c₂ (by simp)) h₂]
      · -- S₁ → β D
        obtain ⟨hne, hab⟩ := ih c₂ (by simp) _ h₂
        refine ⟨[], c₂.yield, ?_, AB_nil, hab, by simpa using (List.length_pos_iff.2 hne).ne⟩
        simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁]
      · -- S₂ → A B₁
        obtain ⟨u, d, u', hw₁, hu, hd, hu', hlen⟩ := ih c₁ (by simp) _ h₁
        obtain ⟨e, hw₂, he⟩ := ih c₂ (by simp) _ h₂
        refine ⟨u ++ .a :: d, u' ++ .b :: e, ?_, AB_append hu (AB_cons (Or.inl rfl) hd),
          AB_append hu' (AB_cons (Or.inr rfl) he), ne_of_append_cons hlen (by decide)⟩
        simp [hw₁, hw₂]
      · -- S₂ → B A₁
        obtain ⟨u, d, u', hw₁, hu, hd, hu', hlen⟩ := ih c₁ (by simp) _ h₁
        obtain ⟨e, hw₂, he⟩ := ih c₂ (by simp) _ h₂
        refine ⟨u ++ .b :: d, u' ++ .a :: e, ?_, AB_append hu (AB_cons (Or.inr rfl) hd),
          AB_append hu' (AB_cons (Or.inl rfl) he), ne_of_append_cons hlen (by decide)⟩
        simp [hw₁, hw₂]
      · -- A → a β
        refine ⟨[], [], [], ?_, AB_nil, AB_nil, AB_nil, rfl⟩
        simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁,
          yield_eq_of_value_terminal (hcs c₂ (by simp)) h₂]
      · -- B → b β
        refine ⟨[], [], [], ?_, AB_nil, AB_nil, AB_nil, rfl⟩
        simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁,
          yield_eq_of_value_terminal (hcs c₂ (by simp)) h₂]
      · -- A₁ → a D
        obtain ⟨-, hab⟩ := ih c₂ (by simp) _ h₂
        exact ⟨c₂.yield, by simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁], hab⟩
      · -- B₁ → b D
        obtain ⟨-, hab⟩ := ih c₂ (by simp) _ h₂
        exact ⟨c₂.yield, by simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁], hab⟩
      · -- D → C D
        obtain ⟨p, hp, hpab⟩ := exists_of_generated_C (ih c₁ (by simp) _ h₁)
        obtain ⟨-, hab⟩ := ih c₂ (by simp) _ h₂
        exact ⟨by simp [hp], by simpa [hp] using AB_cons hpab hab⟩
    · rcases hrule with ⟨rfl, h₁, h₂, h₃⟩ | ⟨rfl, h₁, h₂, h₃⟩ | ⟨rfl, h₁, h₂, h₃⟩ |
        ⟨rfl, h₁, h₂, h₃⟩ | ⟨rfl, h₁, h₂, h₃⟩ | ⟨rfl, h₁, h₂, h₃⟩ | ⟨rfl, h₁, h₂, h₃⟩
      · -- S → α S₁ γ
        obtain ⟨x, y, hw, hx, hy, hlen⟩ := ih c₂ (by simp) _ h₂
        refine ⟨x, y, ?_, hx, hy, λ h => hlen (by rw [h])⟩
        simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁,
          yield_eq_of_value_terminal (hcs c₃ (by simp)) h₃, hw]
      · -- S → α S₂ γ
        obtain ⟨x, y, hw, hx, hy, hne⟩ := ih c₂ (by simp) _ h₂
        refine ⟨x, y, ?_, hx, hy, hne⟩
        simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁,
          yield_eq_of_value_terminal (hcs c₃ (by simp)) h₃, hw]
      · -- S₁ → C S₁ C
        obtain ⟨p, hp, hpab⟩ := exists_of_generated_C (ih c₁ (by simp) _ h₁)
        obtain ⟨x, y, hw, hx, hy, hlen⟩ := ih c₂ (by simp) _ h₂
        obtain ⟨q, hq, hqab⟩ := exists_of_generated_C (ih c₃ (by simp) _ h₃)
        refine ⟨p :: x, y ++ [q], ?_, AB_cons hpab hx, AB_append hy (AB_cons hqab AB_nil),
          by simp; omega⟩
        simp [hp, hq, hw]
      · -- A → C A C
        obtain ⟨p, hp, hpab⟩ := exists_of_generated_C (ih c₁ (by simp) _ h₁)
        obtain ⟨u, d, u', hw, hu, hd, hu', hlen⟩ := ih c₂ (by simp) _ h₂
        obtain ⟨q, hq, hqab⟩ := exists_of_generated_C (ih c₃ (by simp) _ h₃)
        refine ⟨p :: u, d, u' ++ [q], ?_, AB_cons hpab hu, hd, AB_append hu' (AB_cons hqab AB_nil),
          by simp [hlen]⟩
        simp [hp, hq, hw]
      · -- A → a D β
        obtain ⟨-, hd⟩ := ih c₂ (by simp) _ h₂
        refine ⟨[], c₂.yield, [], ?_, AB_nil, hd, AB_nil, rfl⟩
        simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁,
          yield_eq_of_value_terminal (hcs c₃ (by simp)) h₃]
      · -- B → C B C
        obtain ⟨p, hp, hpab⟩ := exists_of_generated_C (ih c₁ (by simp) _ h₁)
        obtain ⟨u, d, u', hw, hu, hd, hu', hlen⟩ := ih c₂ (by simp) _ h₂
        obtain ⟨q, hq, hqab⟩ := exists_of_generated_C (ih c₃ (by simp) _ h₃)
        refine ⟨p :: u, d, u' ++ [q], ?_, AB_cons hpab hu, hd, AB_append hu' (AB_cons hqab AB_nil),
          by simp [hlen]⟩
        simp [hp, hq, hw]
      · -- B → b D β
        obtain ⟨-, hd⟩ := ih c₂ (by simp) _ h₂
        refine ⟨[], c₂.yield, [], ?_, AB_nil, hd, AB_nil, rfl⟩
        simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁,
          yield_eq_of_value_terminal (hcs c₃ (by simp)) h₃]

/-! #### Completeness -/

private theorem derives_C {p : Sym} (hp : p = .a ∨ p = .b) :
    xyGrammar.Derives [.nonterminal .C] [.terminal p] := by
  rcases hp with rfl | rfl
  · exact (xprod (r := ⟨.C, [.terminal .a]⟩) (by decide)).single
  · exact (xprod (r := ⟨.C, [.terminal .b]⟩) (by decide)).single

private theorem derives_D : ∀ {d : List Sym}, d ≠ [] → AB d →
    xyGrammar.Derives [.nonterminal .D] (d.map .terminal)
  | [], h, _ => absurd rfl h
  | [p], _, hab =>
    (xprod (r := ⟨.D, [.nonterminal .C]⟩) (by decide)).trans_derives
      (derives_C (hab p (by simp)))
  | p :: q :: d, _, hab =>
    (xprod (r := ⟨.D, [.nonterminal .C, .nonterminal .D]⟩) (by decide)).trans_derives
      (((derives_C (hab p (by simp))).append_right _).trans
        ((derives_D (List.cons_ne_nil q d) λ c hc => hab c (List.mem_cons_of_mem _ hc)
          ).append_left [Symbol.terminal p]))

private theorem AB_of_cons {c : Sym} {l : List Sym} (h : AB (c :: l)) : AB l :=
  λ x hx => h x (List.mem_cons_of_mem _ hx)

private theorem AB_of_append_left {l₁ l₂ : List Sym} (h : AB (l₁ ++ l₂)) : AB l₁ :=
  λ x hx => h x (List.mem_append_left _ hx)

private theorem derives_S₁ : ∀ (u v : List Sym), AB u → AB v → u.length ≠ v.length →
    xyGrammar.Derives [.nonterminal .S₁] ((u ++ .beta :: v).map .terminal)
  | [], v, _, hv, hne =>
    (xprod (r := ⟨.S₁, [.terminal .beta, .nonterminal .D]⟩) (by decide)).trans_derives
      ((derives_D (by rintro rfl; exact hne rfl) hv).append_left [Symbol.terminal .beta])
  | p :: u, v, hu, hv, hne => by
    rcases List.eq_nil_or_concat v with rfl | ⟨v', q, hv'⟩
    · exact (xprod (r := ⟨.S₁, [.nonterminal .D, .terminal .beta]⟩) (by decide)).trans_derives
        (by simpa using (derives_D (List.cons_ne_nil p u) hu).append_right [Symbol.terminal .beta])
    · rw [List.concat_eq_append] at hv'
      subst hv'
      have hne' : u.length ≠ v'.length := by simp at hne; omega
      have := derives_S₁ u v' (AB_of_cons hu) (AB_of_append_left hv) hne'
      refine (xprod (r := ⟨.S₁, [.nonterminal .C, .nonterminal .S₁, .nonterminal .C]⟩)
        (by decide)).trans_derives ?_
      have hq : q = .a ∨ q = .b := hv q (by simp)
      have h1 := (derives_C (hu p (by simp))).append_right [Symbol.nonterminal .S₁, .nonterminal .C]
      have h2 := (this.append_right [Symbol.nonterminal .C]).append_left [Symbol.terminal p]
      have h3 := (derives_C hq).append_left
        ([Symbol.terminal p] ++ (u ++ .beta :: v').map .terminal)
      simpa [List.append_assoc] using (h1.trans h2).trans h3

private theorem derives_A : ∀ (u d u' : List Sym), AB u → AB d → AB u' → u.length = u'.length →
    xyGrammar.Derives [.nonterminal .A] ((u ++ .a :: d ++ .beta :: u').map .terminal)
  | [], d, u', _, hd, _, hlen => by
    obtain rfl : u' = [] := List.eq_nil_of_length_eq_zero hlen.symm
    rcases eq_or_ne d [] with rfl | hne
    · exact (xprod (r := ⟨.A, [.terminal .a, .terminal .beta]⟩) (by decide)).single
    · refine (xprod (r := ⟨.A, [.terminal .a, .nonterminal .D, .terminal .beta]⟩)
        (by decide)).trans_derives ?_
      simpa using ((derives_D hne hd).append_left [Symbol.terminal .a]).append_right
        [Symbol.terminal .beta]
  | p :: u, d, u', hu, hd, hu', hlen => by
    rcases List.eq_nil_or_concat u' with rfl | ⟨v', q, hv'⟩
    · simp at hlen
    · rw [List.concat_eq_append] at hv'
      subst hv'
      have hlen' : u.length = v'.length := by simp at hlen; omega
      have := derives_A u d v' (AB_of_cons hu) hd (AB_of_append_left hu') hlen'
      refine (xprod (r := ⟨.A, [.nonterminal .C, .nonterminal .A, .nonterminal .C]⟩)
        (by decide)).trans_derives ?_
      have hq : q = .a ∨ q = .b := hu' q (by simp)
      have h1 := (derives_C (hu p (by simp))).append_right [Symbol.nonterminal .A, .nonterminal .C]
      have h2 := (this.append_right [Symbol.nonterminal .C]).append_left [Symbol.terminal p]
      have h3 := (derives_C hq).append_left
        ([Symbol.terminal p] ++ (u ++ .a :: d ++ .beta :: v').map .terminal)
      simpa [List.append_assoc] using (h1.trans h2).trans h3

private theorem derives_B : ∀ (u d u' : List Sym), AB u → AB d → AB u' → u.length = u'.length →
    xyGrammar.Derives [.nonterminal .B] ((u ++ .b :: d ++ .beta :: u').map .terminal)
  | [], d, u', _, hd, _, hlen => by
    obtain rfl : u' = [] := List.eq_nil_of_length_eq_zero hlen.symm
    rcases eq_or_ne d [] with rfl | hne
    · exact (xprod (r := ⟨.B, [.terminal .b, .terminal .beta]⟩) (by decide)).single
    · refine (xprod (r := ⟨.B, [.terminal .b, .nonterminal .D, .terminal .beta]⟩)
        (by decide)).trans_derives ?_
      simpa using ((derives_D hne hd).append_left [Symbol.terminal .b]).append_right
        [Symbol.terminal .beta]
  | p :: u, d, u', hu, hd, hu', hlen => by
    rcases List.eq_nil_or_concat u' with rfl | ⟨v', q, hv'⟩
    · simp at hlen
    · rw [List.concat_eq_append] at hv'
      subst hv'
      have hlen' : u.length = v'.length := by simp at hlen; omega
      have := derives_B u d v' (AB_of_cons hu) hd (AB_of_append_left hu') hlen'
      refine (xprod (r := ⟨.B, [.nonterminal .C, .nonterminal .B, .nonterminal .C]⟩)
        (by decide)).trans_derives ?_
      have hq : q = .a ∨ q = .b := hu' q (by simp)
      have h1 := (derives_C (hu p (by simp))).append_right [Symbol.nonterminal .B, .nonterminal .C]
      have h2 := (this.append_right [Symbol.nonterminal .C]).append_left [Symbol.terminal p]
      have h3 := (derives_C hq).append_left
        ([Symbol.terminal p] ++ (u ++ .b :: d ++ .beta :: v').map .terminal)
      simpa [List.append_assoc] using (h1.trans h2).trans h3

private theorem derives_A₁ {d : List Sym} (hd : AB d) :
    xyGrammar.Derives [.nonterminal .A₁] ((.a :: d).map .terminal) := by
  rcases eq_or_ne d [] with rfl | hne
  · exact (xprod (r := ⟨.A₁, [.terminal .a]⟩) (by decide)).single
  · exact (xprod (r := ⟨.A₁, [.terminal .a, .nonterminal .D]⟩) (by decide)).trans_derives
      ((derives_D hne hd).append_left [Symbol.terminal .a])

private theorem derives_B₁ {d : List Sym} (hd : AB d) :
    xyGrammar.Derives [.nonterminal .B₁] ((.b :: d).map .terminal) := by
  rcases eq_or_ne d [] with rfl | hne
  · exact (xprod (r := ⟨.B₁, [.terminal .b]⟩) (by decide)).single
  · exact (xprod (r := ⟨.B₁, [.terminal .b, .nonterminal .D]⟩) (by decide)).trans_derives
      ((derives_D hne hd).append_left [Symbol.terminal .b])

private theorem exists_differing_position : ∀ {x y : List Sym}, x.length = y.length → x ≠ y →
    ∃ u p d u' q e, x = u ++ p :: d ∧ y = u' ++ q :: e ∧ u.length = u'.length ∧ p ≠ q
  | [], [], _, hne => absurd rfl hne
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | p :: d, q :: e, hlen, hne => by
    by_cases hpq : p = q
    · subst hpq
      obtain ⟨u, p', d', u', q', e', rfl, rfl, hlen', hpq'⟩ :=
        exists_differing_position (by simpa using hlen) (λ h => hne (by rw [h]))
      exact ⟨p :: u, p', d', p :: u', q', e', rfl, rfl, by simp [hlen'], hpq'⟩
    · exact ⟨[], p, d, [], q, e, rfl, rfl, rfl, hpq⟩

private theorem derives_S₂ {x y : List Sym} (hx : AB x) (hy : AB y) (hlen : x.length = y.length)
    (hne : x ≠ y) : xyGrammar.Derives [.nonterminal .S₂] ((x ++ .beta :: y).map .terminal) := by
  obtain ⟨u, p, d, u', q, e, rfl, rfl, hlen', hpq⟩ := exists_differing_position hlen hne
  have hu := AB_of_append_left hx
  have hd := AB_of_cons (λ c hc => hx c (List.mem_append_right _ hc))
  have hu' := AB_of_append_left hy
  have he := AB_of_cons (λ c hc => hy c (List.mem_append_right _ hc))
  have hp := hx p (by simp)
  have hq := hy q (by simp)
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl hpq
  · refine (xprod (r := ⟨.S₂, [.nonterminal .A, .nonterminal .B₁]⟩) (by decide)).trans_derives ?_
    simpa [List.append_assoc] using
      ((derives_A u d u' hu hd hu' hlen').append_right _).trans ((derives_B₁ he).append_left _)
  · refine (xprod (r := ⟨.S₂, [.nonterminal .B, .nonterminal .A₁]⟩) (by decide)).trans_derives ?_
    simpa [List.append_assoc] using
      ((derives_B u d u' hu hd hu' hlen').append_right _).trans ((derives_A₁ he).append_left _)
  · exact absurd rfl hpq

-- (8)
theorem derives_xy {w : List Sym} (hw : IsXY w) :
    xyGrammar.Derives [.nonterminal .S] (w.map .terminal) := by
  obtain ⟨x, y, rfl, hx, hy, hne⟩ := hw
  rcases eq_or_ne x.length y.length with hlen | hlen
  · refine (xprod (r := ⟨.S, [.terminal .alpha, .nonterminal .S₂, .terminal .gamma]⟩)
      (by decide)).trans_derives ?_
    simpa [List.append_assoc] using
      ((derives_S₂ hx hy hlen hne).append_left [Symbol.terminal .alpha]).append_right
        [Symbol.terminal .gamma]
  · refine (xprod (r := ⟨.S, [.terminal .alpha, .nonterminal .S₁, .terminal .gamma]⟩)
      (by decide)).trans_derives ?_
    simpa [List.append_assoc] using
      ((derives_S₁ x y hx hy hlen).append_left [Symbol.terminal .alpha]).append_right
        [Symbol.terminal .gamma]

/-- Grammar (9) generates exactly the language (8). -/
theorem xyGrammar_language : xyGrammar.language = ({w | IsXY w} : Language Sym) := by
  ext w
  constructor
  · intro hw
    obtain ⟨t, ht, rfl, hv⟩ := xyGrammar.exists_licensed_tree hw
    exact xy_sound ht .S hv
  · exact λ hw => (ContextFreeGrammar.mem_language_iff _ _).2 (derives_xy hw)

/-- The nonidentity language (8) is context-free, against the formal premise of the
comparative argument. -/
theorem isXY_isContextFree : Language.IsContextFree ({w | IsXY w} : Language Sym) :=
  ⟨xyGrammar, xyGrammar_language⟩

/-! ### §4: *respectively* -/

/-- Langendoen's characterization (17) of English *respectively* sentences has each verb agree in
number with its subject. -/
def Langendoen (r : Datum) : Prop := r.feature? "subjects" = r.feature? "verbs"

instance (r : Datum) : Decidable (Langendoen r) := by unfold Langendoen; infer_instance

/-- The judgments in (19) are the exact converse of the characterization. -/
theorem respectively_converse :
    (Langendoen ex19a ∧ ex19a.judgment = .ungrammatical) ∧
      (¬ Langendoen ex19b ∧ ex19b.judgment = .acceptable) := by
  decide

-- (18b), (18)
theorem respectively_18b : Langendoen ex18b ∧ ex18b.judgment = .ungrammatical := by decide

/-! ### §5: Dutch verb raising and grammar (29) -/

/-- The categories of the lexicon (29b) are names, transitive infinitives, intransitive verbs,
transitive and intransitive VP-complement-taking infinitives, and finite transitive and
intransitive VP-complement-taking verbs. -/
inductive Cat
  | B | D | E | F | G | H | I
  deriving DecidableEq, Repr

/-- The nonterminals of grammar (29a) are the verb phrase and its VP complement. -/
inductive DutchNT
  | A | C
  deriving DecidableEq, Repr

open Symbol in
/-- Grammar (29a) has the rules `A → B C D | C E` and `C → B C F | C G | B H | I`. -/
def dutchGrammar : ContextFreeGrammar Cat where
  NT := DutchNT
  initial := .A
  rules := {⟨.A, [terminal .B, nonterminal .C, terminal .D]⟩,
    ⟨.A, [nonterminal .C, terminal .E]⟩,
    ⟨.C, [terminal .B, nonterminal .C, terminal .F]⟩,
    ⟨.C, [nonterminal .C, terminal .G]⟩,
    ⟨.C, [terminal .B, terminal .H]⟩,
    ⟨.C, [terminal .I]⟩}

/-- A rule of grammar (29). -/
private abbrev DRule := ContextFreeRule Cat DutchNT

private theorem dprod {r : DRule} (hr : r ∈ dutchGrammar.rules) :
    dutchGrammar.Produces [.nonterminal r.input] r.output :=
  produces_of_mem hr

/-- Whether a verb is subcategorized for a direct object. -/
def Cat.transitive : Cat → Bool
  | .D | .F | .H => true
  | _ => false

@[simp] theorem Cat.transitive_D : Cat.transitive .D = true := rfl
@[simp] theorem Cat.transitive_E : Cat.transitive .E = false := rfl
@[simp] theorem Cat.transitive_F : Cat.transitive .F = true := rfl
@[simp] theorem Cat.transitive_G : Cat.transitive .G = false := rfl
@[simp] theorem Cat.transitive_H : Cat.transitive .H = true := rfl
@[simp] theorem Cat.transitive_I : Cat.transitive .I = false := rfl

/-- The number of direct objects a string of verbs requires. -/
def objects (vs : List Cat) : ℕ := vs.countP Cat.transitive

@[simp] theorem objects_nil : objects [] = 0 := rfl

@[simp] theorem objects_cons (c : Cat) (w : List Cat) :
    objects (c :: w) = (if c.transitive then 1 else 0) + objects w := by
  simp [objects, List.countP_cons, Nat.add_comm]

@[simp] theorem objects_append (v w : List Cat) : objects (v ++ w) = objects v + objects w :=
  List.countP_append ..

/-- A VP complement consists of names, a finite VP-complement-taking verb, then nonfinite
VP-complement-taking verbs, with one name for each transitive verb. -/
def IsComplement (w : List Cat) : Prop :=
  ∃ n h x, w = List.replicate n .B ++ h :: x ∧ (h = .H ∨ h = .I) ∧ (∀ c ∈ x, c = .F ∨ c = .G) ∧
    n = objects (h :: x)

/-- The verb phrases of (24), as the paper describes them, consist of `n` names, a finite
VP-complement-taking verb, a string of nonfinite VP-complement-taking verbs, and a final
transitive or intransitive verb, with one name for each transitive verb. -/
def IsVerbPhrase (w : List Cat) : Prop :=
  ∃ n h x v, w = List.replicate n .B ++ h :: x ++ [v] ∧ (h = .H ∨ h = .I) ∧
    (∀ c ∈ x, c = .F ∨ c = .G) ∧ (v = .D ∨ v = .E) ∧ n = objects (h :: x ++ [v])

-- (29)
theorem dutch_sound {t : RoseTree (Symbol Cat dutchGrammar.NT)}
    (ht : t.Licensed dutchGrammar.Licenses) :
    (t.value = .nonterminal .C → IsComplement t.yield) ∧
      (t.value = .nonterminal .A → IsVerbPhrase t.yield) := by
  induction ht using RoseTree.Licensed.grammar_induction with
  | terminal a => simp [RoseTree.leaf]
  | nonterminal N cs hrule hcs ih =>
    simp only [RoseTree.value_node, Symbol.nonterminal.injEq, RoseTree.yield_node_nonterminal]
    rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, _ | ⟨c₄, cs⟩⟩⟩⟩ <;> simp [dutchGrammar] at hrule
    · -- C → I
      obtain ⟨rfl, h₁⟩ := hrule
      refine ⟨λ _ => ⟨0, .I, [], ?_, Or.inr rfl, by simp, by simp⟩,
        by simp⟩
      simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁]
    · rcases hrule with ⟨rfl, h₁, h₂⟩ | ⟨rfl, h₁, h₂⟩ | ⟨rfl, h₁, h₂⟩
      · -- A → C E
        obtain ⟨n, h, x, hw, hh, hx, hn⟩ := (ih c₁ (by simp)).1 h₁
        refine ⟨by simp, λ _ => ⟨n, h, x, .E, ?_, hh, hx, Or.inr rfl, ?_⟩⟩
        · simp [yield_eq_of_value_terminal (hcs c₂ (by simp)) h₂, hw]
        · simpa using hn
      · -- C → C G
        obtain ⟨n, h, x, hw, hh, hx, hn⟩ := (ih c₁ (by simp)).1 h₁
        refine ⟨λ _ => ⟨n, h, x ++ [.G], ?_, hh, ?_, ?_⟩, by simp⟩
        · simp [yield_eq_of_value_terminal (hcs c₂ (by simp)) h₂, hw]
        · intro c hc
          rcases List.mem_append.1 hc with hc | hc
          · exact hx c hc
          · exact Or.inr (List.mem_singleton.1 hc)
        · simpa using hn
      · -- C → B H
        refine ⟨λ _ => ⟨1, .H, [], ?_, Or.inl rfl, by simp, by simp⟩,
          by simp⟩
        simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁,
          yield_eq_of_value_terminal (hcs c₂ (by simp)) h₂]
    · rcases hrule with ⟨rfl, h₁, h₂, h₃⟩ | ⟨rfl, h₁, h₂, h₃⟩
      · -- A → B C D
        obtain ⟨n, h, x, hw, hh, hx, hn⟩ := (ih c₂ (by simp)).1 h₂
        refine ⟨by simp, λ _ => ⟨n + 1, h, x, .D, ?_, hh, hx, Or.inl rfl, ?_⟩⟩
        · simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁,
            yield_eq_of_value_terminal (hcs c₃ (by simp)) h₃, hw, List.replicate_succ]
        · simp at hn ⊢
          omega
      · -- C → B C F
        obtain ⟨n, h, x, hw, hh, hx, hn⟩ := (ih c₂ (by simp)).1 h₂
        refine ⟨λ _ => ⟨n + 1, h, x ++ [.F], ?_, hh, ?_, ?_⟩, by simp⟩
        · simp [yield_eq_of_value_terminal (hcs c₁ (by simp)) h₁,
            yield_eq_of_value_terminal (hcs c₃ (by simp)) h₃, hw, List.replicate_succ]
        · intro c hc
          rcases List.mem_append.1 hc with hc | hc
          · exact hx c hc
          · exact Or.inl (List.mem_singleton.1 hc)
        · simp at hn ⊢
          omega

theorem derives_complement : ∀ (x : List Cat) {n : ℕ} {h : Cat}, (h = .H ∨ h = .I) →
    (∀ c ∈ x, c = .F ∨ c = .G) → n = objects (h :: x) →
      dutchGrammar.Derives [.nonterminal .C]
        ((List.replicate n Cat.B ++ h :: x).map .terminal) := by
  intro x
  induction x using List.reverseRecOn with
  | nil =>
    rintro n h (rfl | rfl) - hn
    · obtain rfl : n = 1 := by simpa using hn
      exact (dprod (r := ⟨.C, [.terminal .B, .terminal .H]⟩) (by decide)).single
    · obtain rfl : n = 0 := by simpa using hn
      exact (dprod (r := ⟨.C, [.terminal .I]⟩) (by decide)).single
  | append_singleton x c ih =>
    rintro n h hh hx hn
    have hx' : ∀ c ∈ x, c = .F ∨ c = .G := λ c hc => hx c (List.mem_append_left _ hc)
    rcases hx c (by simp) with rfl | rfl
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 :=
        ⟨objects (h :: x), by simp at hn ⊢; omega⟩
      have := ((ih (n := n') hh hx'
        (by simp at hn ⊢; omega)
        ).append_left [Symbol.terminal .B]).append_right [Symbol.terminal .F]
      refine (dprod (r := ⟨.C, [.terminal .B, .nonterminal .C, .terminal .F]⟩)
        (by decide)).trans_derives ?_
      simpa [List.replicate_succ] using this
    · have := (ih (n := n) hh hx' (by simpa using hn)
        ).append_right [Symbol.terminal .G]
      refine (dprod (r := ⟨.C, [.nonterminal .C, .terminal .G]⟩) (by decide)).trans_derives ?_
      simpa using this

theorem derives_verbPhrase {w : List Cat} (hw : IsVerbPhrase w) :
    dutchGrammar.Derives [.nonterminal .A] (w.map .terminal) := by
  obtain ⟨n, h, x, v, rfl, hh, hx, rfl | rfl, hn⟩ := hw
  · have hn' : n = objects (h :: x) + 1 := by simp at hn ⊢; omega
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨_, hn'⟩
    have := ((derives_complement x (n := n') hh hx (by simp at hn ⊢; omega)
      ).append_left [Symbol.terminal .B]).append_right [Symbol.terminal .D]
    refine (dprod (r := ⟨.A, [.terminal .B, .nonterminal .C, .terminal .D]⟩)
      (by decide)).trans_derives ?_
    simpa [List.replicate_succ] using this
  · have := (derives_complement x (n := n) hh hx (by simpa using hn)
      ).append_right [Symbol.terminal .E]
    refine (dprod (r := ⟨.A, [.nonterminal .C, .terminal .E]⟩) (by decide)).trans_derives ?_
    simpa using this

/-- Grammar (29) generates exactly the verb phrases the paper describes. -/
theorem dutchGrammar_language : dutchGrammar.language = ({w | IsVerbPhrase w} : Language Cat) := by
  ext w
  constructor
  · intro hw
    obtain ⟨t, ht, rfl, hv⟩ := dutchGrammar.exists_licensed_tree hw
    exact (dutch_sound ht).2 hv
  · exact λ hw => (ContextFreeGrammar.mem_language_iff _ _).2 (derives_verbPhrase hw)

theorem isVerbPhrase_isContextFree : Language.IsContextFree ({w | IsVerbPhrase w} : Language Cat) :=
  ⟨dutchGrammar, dutchGrammar_language⟩

/-! #### The examples (25) to (31) -/

/-- `IsVerbPhrase` is decided by stripping the names, reading the first and last verb, and
counting. -/
def isVerbPhrase (w : List Cat) : Bool :=
  match w.dropWhile (· == .B) with
  | [] => false
  | h :: r =>
    match r.getLast? with
    | none => false
    | some v => (h == .H || h == .I) && r.dropLast.all (λ c => c == .F || c == .G) &&
        (v == .D || v == .E) && ((w.takeWhile (· == .B)).length == objects (h :: r))

private theorem takeWhile_replicate_append (n : ℕ) (l : List Cat) :
    (List.replicate n Cat.B ++ l).takeWhile (· == Cat.B)
      = List.replicate n Cat.B ++ l.takeWhile (· == Cat.B) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private theorem dropWhile_replicate_append (n : ℕ) (l : List Cat) :
    (List.replicate n Cat.B ++ l).dropWhile (· == Cat.B) = l.dropWhile (· == Cat.B) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private theorem eq_B_of_mem_takeWhile {l : List Cat} {c : Cat}
    (hc : c ∈ l.takeWhile (· == Cat.B)) : c = .B := by
  induction l with
  | nil => simp at hc
  | cons a l ih =>
    by_cases ha : a = .B
    · subst ha
      rw [List.takeWhile_cons_of_pos (by simp)] at hc
      rcases List.mem_cons.1 hc with rfl | hc
      · rfl
      · exact ih hc
    · rw [List.takeWhile_cons_of_neg (by simpa using ha)] at hc
      simp at hc

theorem isVerbPhrase_iff (w : List Cat) : isVerbPhrase w = true ↔ IsVerbPhrase w := by
  constructor
  · intro hw
    unfold isVerbPhrase at hw
    split at hw
    · exact absurd hw (by simp)
    · rename_i h r hd
      split at hw
      · exact absurd hw (by simp)
      · rename_i v hv
        obtain ⟨x, rfl⟩ := List.getLast?_eq_some_iff.1 hv
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true,
          List.dropLast_concat] at hw
        obtain ⟨⟨⟨hh, hx⟩, hvv⟩, hn⟩ := hw
        obtain ⟨k, hk⟩ : ∃ k, (w.takeWhile (· == Cat.B)).length = k := ⟨_, rfl⟩
        have htake : w.takeWhile (· == Cat.B) = List.replicate k Cat.B :=
          List.eq_replicate_iff.2 ⟨hk, λ c hc => eq_B_of_mem_takeWhile hc⟩
        refine ⟨k, h, x, v, ?_, hh, hx, hvv, ?_⟩
        · conv_lhs => rw [← List.takeWhile_append_dropWhile (p := (· == Cat.B)) (l := w)]
          rw [htake, hd]
          simp
        · simp only [← hk, hn, List.cons_append]
  · rintro ⟨n, h, x, v, rfl, hh, hx, hv, hn⟩
    have hB : (h == Cat.B) = false := by rcases hh with rfl | rfl <;> rfl
    unfold isVerbPhrase
    simp only [List.append_assoc, List.cons_append]
    rw [dropWhile_replicate_append, List.dropWhile_cons_of_neg (by simp [hB]),
      takeWhile_replicate_append, List.takeWhile_cons_of_neg (by simp [hB])]
    simp only [List.getLast?_concat, List.dropLast_concat, List.append_nil, List.length_replicate,
      Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true]
    exact ⟨⟨⟨hh, hx⟩, hv⟩, by simpa using hn⟩

/-- The category of a letter of a row's `categories` feature. -/
def Cat.ofChar? : Char → Option Cat
  | 'B' => some .B
  | 'D' => some .D
  | 'E' => some .E
  | 'F' => some .F
  | 'G' => some .G
  | 'H' => some .H
  | 'I' => some .I
  | _ => none

/-- A row's category string. -/
def categories (r : Datum) : Option (List Cat) :=
  (r.feature? "categories").bind λ s => s.toList.mapM Cat.ofChar?

/-- A row is predicted when its grammaticality agrees with whether its category string is a verb
phrase of grammar (29). -/
def Predicted (r : Datum) : Prop :=
  match categories r with
  | some w => r.judgment = .acceptable ↔ isVerbPhrase w = true
  | none => False

instance (r : Datum) : Decidable (Predicted r) := by
  unfold Predicted; split <;> infer_instance

/-- On (25) to (31), grammar (29) accepts the grammatical clauses and rejects the ungrammatical. -/
theorem dutch_rows : ∀ r ∈ Examples.all, r.language = "dutc1256" → Predicted r := by decide

/-! ### §6: Mohawk noun incorporation -/

/-- The stem-matching premise of the Mohawk argument says that the stem incorporated in the verb is
the head noun stem of its external argument. -/
def StemMatched (r : Datum) : Prop :=
  r.feature? "incorporated" = r.feature? "external"

instance (r : Datum) : Decidable (StemMatched r) := by
  unfold StemMatched; infer_instance

/-- Classificatory incorporation (39), (40) and possessed incorporation (43d) are grammatical
with mismatched stems. -/
theorem stem_matching_fails :
    ∀ r ∈ [ex39, ex40, ex43d], r.judgment = .acceptable ∧ ¬ StemMatched r := by
  decide

end PullumGazdar1982
