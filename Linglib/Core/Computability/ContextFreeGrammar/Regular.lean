/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar.Equations
public import Linglib.Core.Computability.ContextFreeGrammar.Union
public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Fintype.Prod

/-!
# Context-free and regular languages

This file relates the context-free languages to the regular languages. A grammar is *right-linear*
if every right-hand side is a string of terminals followed by at most one nonterminal. Over a
finite alphabet, [a language is regular if and only if a right-linear grammar generates
it](##Language.isRegular_iff_exists_isRightLinear), so [every regular language is
context-free](##Language.IsRegular.isContextFree). The intersection of a context-free language
with a regular language [is context-free](##Language.IsContextFree.inf_isRegular): for a grammar
`G` and a finite automaton `M`, the grammar `G.inter M` [generates the intersection of their
languages](##ContextFreeGrammar.language_inter).

## Implementation notes

* The right-linear grammar `M.toContextFreeGrammar` of a finite automaton `M` needs a finite
  alphabet, because a grammar has finitely many rules and so uses finitely many letters. Over an
  infinite alphabet the language of all words is regular, by an automaton with one state, but not
  context-free.
* That a right-linear grammar generates a regular language is proved from the Myhill–Nerode
  theorem, without an automaton. The left quotient of the language by a word is a union of
  languages derived from suffixes of right-hand sides, and a grammar has finitely many such
  suffixes.
* `G.inter M` is the union, over the accepting states `q` of `M`, of the *triple construction*
  `G.triple M q`. Its nonterminals are triples `(p, A, p')` of a nonterminal `A` of `G`, an entry
  state `p` and an exit state `p'`. A sentential form over triples *threads* from `p` to `q`
  (`DFA.Threads`) if reading it takes `M` from `p` to `q`, where a triple can be read only in its
  entry state and takes `M` to its exit state. The rules of `G.triple M q` are the rules over
  triples that become rules of `G` when the states are erased and whose right-hand side threads
  from the entry state to the exit state of the left-hand side.

## References

* [bar-hillel-perles-shamir-1961]
* [hopcroft-motwani-ullman-2000]
-/

@[expose] public section

open Symbol

namespace DFA

section toContextFreeGrammar

variable {α : Type*} {σ : Type} [Fintype α] [Fintype σ] {M : DFA α σ}

open scoped Classical in
/-- The *right-linear grammar* of a finite automaton `M`. Its nonterminals are the states of `M`. It
has a rule `q → a q'` for each transition from `q` to `q'` on the letter `a`, and a rule `q → ε` for
each accepting state `q`. -/
noncomputable def toContextFreeGrammar (M : DFA α σ) : ContextFreeGrammar α where
  NT := σ
  initial := M.start
  rules := Finset.image₂ (fun q a ↦ ⟨q, [terminal a, nonterminal (M.step q a)]⟩) .univ .univ ∪
    (Finset.univ.filter (· ∈ M.accept)).image (⟨·, []⟩)

theorem mem_toContextFreeGrammar_rules {r : ContextFreeRule α σ} :
    r ∈ M.toContextFreeGrammar.rules ↔
      (∃ a, r.output = [terminal a, nonterminal (M.step r.input a)]) ∨
        (r.input ∈ M.accept ∧ r.output = []) := by
  obtain ⟨q, o⟩ := r
  simp [toContextFreeGrammar, eq_comm]

/-- From the nonterminal `q`, the right-linear grammar of `M` derives the words that `M` accepts
from the state `q`. -/
theorem languageFrom_toContextFreeGrammar (M : DFA α σ) (q : σ) :
    M.toContextFreeGrammar.languageFrom [nonterminal q] = M.acceptsFrom q := by
  refine le_antisymm ?_ fun w hw ↦ ?_
  · refine M.toContextFreeGrammar.isLeast_languageFrom.2
      (?_ : M.toContextFreeGrammar.equations M.acceptsFrom ≤ M.acceptsFrom) q
    intro q w hw
    obtain ⟨r, hr, rfl, hr'⟩ := ContextFreeGrammar.mem_equations.1 hw
    obtain ⟨a, ho⟩ | ⟨hacc, ho⟩ := mem_toContextFreeGrammar_rules.1 hr
    · obtain ⟨_, rfl, v, hv, rfl⟩ : w ∈ {[a]} * M.acceptsFrom (M.step r.input a) := by
        simpa [ho] using hr'
      exact hv
    · obtain rfl : w = [] := by simpa [ho] using hr'
      exact hacc
  · induction w generalizing q with
    | nil =>
      exact ContextFreeGrammar.languageFrom_output_le (r := ⟨q, []⟩)
        (mem_toContextFreeGrammar_rules.2 (.inr ⟨hw, rfl⟩))
        (ContextFreeGrammar.mem_languageFrom_map_terminal _ [])
    | cons a w ih =>
      refine ContextFreeGrammar.languageFrom_output_le
        (r := ⟨q, [terminal a, nonterminal (M.step q a)]⟩)
        (mem_toContextFreeGrammar_rules.2 (.inl ⟨a, rfl⟩)) ?_
      exact ContextFreeGrammar.append_mem_languageFrom
        (ContextFreeGrammar.mem_languageFrom_map_terminal _ [a]) (ih _ hw)

/-- The right-linear grammar of `M` generates the language that `M` accepts. -/
@[simp] theorem language_toContextFreeGrammar (M : DFA α σ) :
    M.toContextFreeGrammar.language = M.accepts :=
  M.languageFrom_toContextFreeGrammar M.start

end toContextFreeGrammar

end DFA

namespace ContextFreeGrammar

variable {T : Type*} {g : ContextFreeGrammar T}

/-- A grammar is *right-linear* if every right-hand side is a string of terminals followed by at
most one nonterminal. -/
def IsRightLinear (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, ∀ s ∈ r.output.dropLast, ¬ s.IsNonterminal

instance : DecidablePred (IsRightLinear (T := T)) := fun g ↦
  inferInstanceAs (Decidable (∀ r ∈ g.rules, ∀ s ∈ r.output.dropLast, ¬ s.IsNonterminal))

/-- The suffixes of the right-hand sides of `g`, together with the suffixes of its start symbol. -/
private def suffixes (g : ContextFreeGrammar T) : Set (List (Symbol T g.NT)) :=
  {α | α <:+ [nonterminal g.initial] ∨ ∃ r ∈ g.rules, α <:+ r.output}

private theorem finite_suffixes : (suffixes g).Finite := by
  have h (l : List (Symbol T g.NT)) : {α | α <:+ l}.Finite :=
    l.tails.finite_toSet.subset fun _ h ↦ (List.mem_tails _ _).mpr h
  exact ((h _).union (g.rules.finite_toSet.biUnion fun r _ ↦ h r.output)).subset fun α hα ↦
    hα.imp id fun ⟨r, hr, hα⟩ ↦ Set.mem_biUnion hr hα

private theorem mem_suffixes_of_cons {s : Symbol T g.NT} {α : List (Symbol T g.NT)}
    (h : s :: α ∈ suffixes g) : α ∈ suffixes g :=
  h.imp (List.suffix_cons s α).trans fun ⟨r, hr, h⟩ ↦ ⟨r, hr, (List.suffix_cons s α).trans h⟩

private theorem IsRightLinear.eq_nil_of_nonterminal_cons_mem (hg : g.IsRightLinear) {B : g.NT}
    {α : List (Symbol T g.NT)} (h : nonterminal B :: α ∈ suffixes g) : α = [] := by
  rcases h with h | ⟨r, hr, p, hp⟩
  · simpa using h.length_le
  · by_contra hα
    refine hg r hr (nonterminal B) ?_ trivial
    rw [← hp, List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hα]
    simp

/-- In a right-linear grammar, if a suffix `α` derives a word that starts with the letter `a`, then
`α` derives `a` followed by some suffix `β`, and `β` derives the rest of the word. -/
private theorem IsRightLinear.exists_derives_terminal_cons (hg : g.IsRightLinear) {a : T}
    {w : List T} {α : List (Symbol T g.NT)} (hα : α ∈ suffixes g)
    (h : g.Derives α (terminal a :: w.map terminal)) :
    ∃ β ∈ suffixes g, g.Derives α (terminal a :: β) ∧ g.Derives β (w.map terminal) := by
  have key {b : T} {α : List (Symbol T g.NT)} (hα : terminal b :: α ∈ suffixes g)
      (h : g.Derives (terminal b :: α) (terminal a :: w.map terminal)) :
      ∃ β ∈ suffixes g, g.Derives (terminal b :: α) (terminal a :: β) ∧
        g.Derives β (w.map terminal) := by
    obtain ⟨v, hv, hd⟩ := h.exists_of_terminal_cons
    obtain ⟨rfl, rfl⟩ : a = b ∧ w.map terminal = v := by simpa using hv
    exact ⟨α, mem_suffixes_of_cons hα, .refl _, hd⟩
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact key hα (.refl _)
  | @head α α' step rest ih =>
    rcases α with _ | ⟨b | B, α⟩
    · exact (not_produces_map_terminal (w := []) step).elim
    · exact key hα (step.trans_derives rest)
    · obtain rfl := hg.eq_nil_of_nonterminal_cons_mem hα
      obtain ⟨r, hr, rfl, rfl⟩ := produces_singleton_iff.mp step
      obtain ⟨β, hβ, h₁, h₂⟩ := ih (.inr ⟨r, hr, List.suffix_rfl⟩)
      exact ⟨β, hβ, step.trans_derives h₁, h₂⟩

/-- A right-linear grammar generates a regular language. -/
theorem IsRightLinear.isRegular_language (hg : g.IsRightLinear) : g.language.IsRegular := by
  refine .of_finite_range_leftQuotient (((finite_suffixes (g := g)).finite_subsets.image
    fun S ↦ ({w | ∃ β ∈ S, g.Derives β (w.map terminal)} : Language T)).subset ?_)
  rintro _ ⟨u, rfl⟩
  induction u using List.reverseRecOn with
  | nil =>
    exact ⟨{[nonterminal g.initial]}, by simp [suffixes], by ext w; simp [Language.leftQuotient]⟩
  | append_singleton u a ih =>
    obtain ⟨S, hS, hu⟩ := ih
    refine ⟨{β ∈ suffixes g | ∃ α ∈ S, g.Derives α (terminal a :: β)}, fun _ h ↦ h.1, ?_⟩
    ext w
    have hw : u ++ [a] ++ w ∈ g.language ↔ ∃ α ∈ S, g.Derives α (terminal a :: w.map terminal) := by
      simpa [Language.leftQuotient] using (Set.ext_iff.mp hu (a :: w)).symm
    refine Iff.trans ?_ hw.symm
    constructor
    · rintro ⟨β, ⟨-, α, hα, h₁⟩, h₂⟩
      exact ⟨α, hα, h₁.trans (h₂.append_left [terminal a])⟩
    · rintro ⟨α, hα, h⟩
      obtain ⟨β, hβ, h₁, h₂⟩ := hg.exists_derives_terminal_cons (hS hα) h
      exact ⟨β, ⟨hβ, α, hα, h₁⟩, h₂⟩

end ContextFreeGrammar

namespace DFA

/-- The grammar `M.toContextFreeGrammar` is right-linear. -/
theorem isRightLinear_toContextFreeGrammar {α : Type*} {σ : Type} [Fintype α] [Fintype σ]
    (M : DFA α σ) : M.toContextFreeGrammar.IsRightLinear := by
  intro r hr s hs
  obtain ⟨a, ho⟩ | ⟨-, ho⟩ := mem_toContextFreeGrammar_rules.1 hr <;> simp_all

section Threads

variable {T N σ : Type*} (M : DFA T σ) {p q r p₀ q₀ : σ} {l l₁ l₂ : List (Symbol T (σ × N × σ))}

/-- `M.Threads p l q` means that reading the sentential form `l` takes `M` from the state `p` to the
state `q`. A terminal `a` takes a state `p` to `M.step p a`. A nonterminal `(p₀, A, q₀)` can be read
only in its entry state `p₀`, and takes it to its exit state `q₀`. -/
def Threads : σ → List (Symbol T (σ × N × σ)) → σ → Prop
  | p, [], q => p = q
  | p, .terminal a :: l, q => Threads (M.step p a) l q
  | p, .nonterminal (p₀, _, q₀) :: l, q => p = p₀ ∧ Threads q₀ l q

@[simp] theorem threads_nil : M.Threads (N := N) p [] q ↔ p = q := .rfl

@[simp] theorem threads_terminal_cons {a : T} :
    M.Threads p (terminal a :: l) q ↔ M.Threads (M.step p a) l q := .rfl

@[simp] theorem threads_nonterminal_cons {A : N} :
    M.Threads p (nonterminal (p₀, A, q₀) :: l) q ↔ p = p₀ ∧ M.Threads q₀ l q := .rfl

/-- A concatenation `l₁ ++ l₂` threads from `p` to `r` if and only if `l₁` threads from `p` to some
state `q` and `l₂` threads from `q` to `r`. -/
theorem threads_append :
    M.Threads p (l₁ ++ l₂) r ↔ ∃ q, M.Threads p l₁ q ∧ M.Threads q l₂ r := by
  induction l₁ generalizing p with
  | nil => simp
  | cons s l₁ ih => rcases s with a | ⟨p₀, A, q₀⟩ <;> simp [ih, and_assoc]

/-- A string of terminals `w` threads from `p` to `q` if and only if `M` evaluates `w` from `p` to
`q`. -/
@[simp] theorem threads_map_terminal {w : List T} :
    M.Threads (N := N) p (w.map terminal) q ↔ M.evalFrom p w = q := by
  induction w generalizing p with
  | nil => simp
  | cons a w ih => simp [ih]

end Threads

end DFA

namespace ContextFreeGrammar

variable {T : Type*} {σ : Type} [Finite σ] {G : ContextFreeGrammar T} {M : DFA T σ} {p q r : σ}

/-- The *triple construction* of a grammar `G` and a finite automaton `M`. Its nonterminals are
triples `(p, A, p')` of a nonterminal `A` of `G`, an entry state `p` and an exit state `p'`. Its
rules are the rules over triples that become rules of `G` when the states are erased, and whose
right-hand side threads from the entry state to the exit state of the left-hand side. Its start
symbol is `(M.start, G.initial, q)`. -/
noncomputable def triple (G : ContextFreeGrammar T) (M : DFA T σ) (q : σ) :
    ContextFreeGrammar T where
  NT := σ × G.NT × σ
  initial := (M.start, G.initial, q)
  rules := Set.Finite.toFinset
    (s := {r' | r'.mapNonterminal (fun X : σ × G.NT × σ ↦ X.2.1) ∈ G.rules ∧
      M.Threads r'.input.1 r'.output r'.input.2.2})
    ((ContextFreeRule.finite_preimage_mapNonterminal (f := fun X : σ × G.NT × σ ↦ X.2.1)
      (fun A ↦ (Set.finite_range fun x : σ × σ ↦ (x.1, A, x.2)).subset
        fun ⟨p, _, q⟩ h ↦ ⟨(p, q), by cases h; rfl⟩) G.rules.finite_toSet).subset fun _ h ↦ h.1)

@[simp] theorem triple_initial (G : ContextFreeGrammar T) (M : DFA T σ) (q : σ) :
    (G.triple M q).initial = (M.start, G.initial, q) := rfl

theorem mem_triple_rules {A : G.NT} {p' q' : σ} {l : List (Symbol T (σ × G.NT × σ))} :
    ⟨(p', A, q'), l⟩ ∈ (G.triple M q).rules ↔
      ⟨A, l.map (mapNonterminal (·.2.1))⟩ ∈ G.rules ∧ M.Threads p' l q' := by
  simp [triple, ContextFreeRule.mapNonterminal]

/-- Erasing the states of a rule of `G.triple M q` gives a rule of `G`. -/
theorem mapNonterminal_mem_of_mem_triple_rules {r' : ContextFreeRule T (σ × G.NT × σ)}
    (h : r' ∈ (G.triple M q).rules) : r'.mapNonterminal (·.2.1) ∈ G.rules := by
  obtain ⟨⟨p', A, q'⟩, l⟩ := r'
  exact (mem_triple_rules.mp h).1

/-- If `l` threads from `p` to `r` and `G.triple M q` produces `l'` from `l`, then `l'` threads from
`p` to `r`. -/
theorem Produces.threads {l l' : List (Symbol T (σ × G.NT × σ))}
    (h : (G.triple M q).Produces l l') (hl : M.Threads p l r) : M.Threads p l' r := by
  obtain ⟨⟨⟨p', A, q'⟩, o⟩, hr, hrw⟩ := h
  obtain ⟨pre, post, rfl, rfl⟩ := hrw.exists_parts
  obtain ⟨_, h₁₂, h₃⟩ := M.threads_append.mp hl
  obtain ⟨_, h₁, rfl, rfl⟩ := M.threads_append.mp h₁₂
  exact M.threads_append.mpr
    ⟨_, M.threads_append.mpr ⟨_, h₁, (mem_triple_rules.mp hr).2⟩, h₃⟩

/-- If `l` threads from `p` to `r` and `G.triple M q` derives `l'` from `l`, then `l'` threads from
`p` to `r`. -/
theorem Derives.threads {l l' : List (Symbol T (σ × G.NT × σ))}
    (h : (G.triple M q).Derives l l') (hl : M.Threads p l r) : M.Threads p l' r := by
  induction h with
  | refl => exact hl
  | tail _ step ih => exact step.threads ih

/-- If `G` derives the word `w` from `out`, then for every state `p` there is a form `l` over
triples that gives `out` when the states are erased, threads from `p` to `M.evalFrom p w`, and
derives `w` in `G.triple M q`. -/
theorem exists_derives_triple {out : List (Symbol T G.NT)} {w : List T}
    (hd : G.Derives out (w.map terminal)) (p : σ) :
    ∃ l, l.map (mapNonterminal (·.2.1)) = out ∧ M.Threads p l (M.evalFrom p w) ∧
      (G.triple M q).Derives l (w.map terminal) := by
  induction hd using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨w.map terminal, by simp, by simp, .refl _⟩
  | head step _ ih =>
    obtain ⟨l, hl, ht, hd⟩ := ih
    obtain ⟨r, hr, hrw⟩ := step
    obtain ⟨pre, post, rfl, rfl⟩ := hrw.exists_parts
    obtain ⟨l₁₂, l₃, rfl, h₁₂, rfl⟩ := List.map_eq_append_iff.mp hl
    obtain ⟨l₁, l₂, rfl, rfl, h₂⟩ := List.map_eq_append_iff.mp h₁₂
    obtain ⟨p₂, h₁₂, h₃⟩ := M.threads_append.mp ht
    obtain ⟨p₁, h₁, ht₂⟩ := M.threads_append.mp h₁₂
    exact ⟨l₁ ++ [nonterminal (p₁, r.input, p₂)] ++ l₃, by simp,
      M.threads_append.mpr ⟨p₂, M.threads_append.mpr ⟨p₁, h₁, rfl, rfl⟩, h₃⟩,
      (Produces.single ⟨⟨_, l₂⟩, mem_triple_rules.mpr ⟨h₂ ▸ hr, ht₂⟩,
        ContextFreeRule.rewrites_of_exists_parts _ l₁ l₃⟩).trans hd⟩

/-- A word is in the language of `G.triple M q` if and only if it is in the language of `G` and `M`
evaluates it to the state `q`. -/
theorem mem_language_triple {w : List T} :
    w ∈ (G.triple M q).language ↔ w ∈ G.language ∧ M.eval w = q := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, ?_⟩
  · simpa using Derives.mapNonterminal (g' := G) (f := fun X : σ × G.NT × σ ↦ X.2.1)
      (fun _ ↦ mapNonterminal_mem_of_mem_triple_rules) ((mem_language_iff _ _).mp h)
  · exact M.threads_map_terminal.mp (Derives.threads ((mem_language_iff _ _).mp h) ⟨rfl, rfl⟩)
  · rintro ⟨hG, rfl⟩
    obtain ⟨l, hl, ht, hd⟩ :=
      exists_derives_triple (M := M) (q := M.eval w) ((mem_language_iff _ _).mp hG) M.start
    obtain ⟨X, rfl, hX⟩ := List.map_eq_singleton_iff.mp hl
    obtain ⟨⟨p', A, q'⟩, rfl, rfl⟩ := mapNonterminal_eq_nonterminal_iff.mp hX
    obtain ⟨rfl, rfl⟩ := ht
    exact hd

/-- `G.inter M` is the union of the triple constructions `G.triple M q` over the accepting states
`q` of the finite automaton `M`. -/
noncomputable def inter (G : ContextFreeGrammar T) (M : DFA T σ) : ContextFreeGrammar T :=
  iUnion fun q : M.accept ↦ G.triple M q

/-- **Bar-Hillel's theorem**. The grammar `G.inter M` generates the intersection of the language of
`G` with the language that `M` accepts. -/
@[simp] theorem language_inter (G : ContextFreeGrammar T) (M : DFA T σ) :
    (G.inter M).language = G.language ⊓ M.accepts := by
  ext w
  simp only [inter, language_iUnion, Language.mem_iSup, mem_language_triple, Language.mem_inf,
    DFA.mem_accepts]
  exact ⟨fun ⟨q, hG, hq⟩ ↦ ⟨hG, hq ▸ q.2⟩, fun ⟨hG, hq⟩ ↦ ⟨⟨_, hq⟩, hG, rfl⟩⟩

end ContextFreeGrammar

namespace Language

variable {α : Type*} {L R : Language α}

/-- Over a finite alphabet, every regular language is context-free. -/
theorem IsRegular.isContextFree [Finite α] (h : L.IsRegular) : L.IsContextFree := by
  have := Fintype.ofFinite α
  obtain ⟨σ, _, M, rfl⟩ := h
  exact ⟨M.toContextFreeGrammar, M.language_toContextFreeGrammar⟩

/-- Over a finite alphabet, a language is regular if and only if a right-linear grammar generates
it. -/
theorem isRegular_iff_exists_isRightLinear [Finite α] :
    L.IsRegular ↔ ∃ g : ContextFreeGrammar α, g.IsRightLinear ∧ g.language = L := by
  refine ⟨fun h ↦ ?_, fun ⟨g, hg, h⟩ ↦ h ▸ hg.isRegular_language⟩
  have := Fintype.ofFinite α
  obtain ⟨σ, _, M, rfl⟩ := h
  exact ⟨_, M.isRightLinear_toContextFreeGrammar, M.language_toContextFreeGrammar⟩

/-- The intersection of a context-free language with a regular language is context-free. -/
theorem IsContextFree.inf_isRegular (hL : L.IsContextFree) (hR : R.IsRegular) :
    (L ⊓ R).IsContextFree := by
  obtain ⟨G, rfl⟩ := hL
  obtain ⟨σ, _, M, rfl⟩ := hR
  exact ⟨G.inter M, G.language_inter M⟩

end Language
