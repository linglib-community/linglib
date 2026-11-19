/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar.Union
public import Mathlib.Computability.DFA
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Fintype.Prod

/-!
# Context-free and regular languages

Over a finite alphabet, [every regular language is
context-free](##Language.IsRegular.isContextFree): the right-linear grammar
`M.toContextFreeGrammar` of a finite automaton `M` [generates the language of
`M`](##DFA.language_toContextFreeGrammar). The context-free languages are [closed under
intersection with regular languages](##Language.IsContextFree.inf_isRegular).

The intersection is the triple construction. The nonterminals of `G.triple M q` are triples
`(p, A, p')` of a nonterminal `A` of `G` with an entry and an exit state of `M`. A sentential form
over these [threads](##DFA.Threads) from `p` to `q` when reading it takes `M` from `p` to `q`,
where a terminal steps the automaton and a triple is passable only from its entry state and leaves
at its exit state. The rules are the rules over triples that erase to a rule of `G` and whose
right-hand side threads from the entry state to the exit state of their left-hand side. Erasure
then sends derivations to derivations of `G`, a production [preserves
threading](##ContextFreeGrammar.Produces.threads), and every derivation of a word in `G` [lifts
along every threading](##ContextFreeGrammar.exists_derives_triple). So `G.triple M q` [generates
the words of `G` that take `M` to `q`](##ContextFreeGrammar.mem_language_triple), and the union
`G.inter M` over the accepting states `q` [generates the
intersection](##ContextFreeGrammar.language_inter).

## Implementation notes

The right-linear grammar of `M` has a nonterminal for each state, a rule `q → a q'` for each
transition from `q` to `q'` on the letter `a`, and a rule `q → ε` for each accepting state `q`;
its sentential forms are a word `w` followed by the state `M.eval w`, or an accepted word. The
alphabet must be finite, because a grammar has finitely many rules and so uses finitely many
letters: over an infinite alphabet the language of all words is regular, by a one-state
automaton, but not context-free.

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
/-- The right-linear grammar of `M` has a nonterminal for each state, a rule `q → a (M.step q a)`
for each state `q` and letter `a`, and a rule `q → ε` for each accepting state `q`. -/
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

theorem derives_toContextFreeGrammar (w : List α) :
    M.toContextFreeGrammar.Derives [nonterminal M.start]
      (w.map terminal ++ [nonterminal (M.eval w)]) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    refine ih.trans_produces (ContextFreeGrammar.produces_map_terminal_append_singleton_iff.2
      ⟨⟨M.eval w, [terminal a, nonterminal (M.step (M.eval w) a)]⟩,
        mem_toContextFreeGrammar_rules.2 (.inl ⟨a, rfl⟩), rfl, ?_⟩)
    simp [eval_append_singleton]

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
        obtain ⟨a, ho⟩ | ⟨hacc, ho⟩ := mem_toContextFreeGrammar_rules.1 hr
        · exact ⟨w ++ [a], .inl (by simp [ho, hq, eval_append_singleton])⟩
        · exact ⟨w, .inr ⟨by simp [ho], hq ▸ hacc⟩⟩
      · exact (ContextFreeGrammar.not_produces_map_terminal hstep).elim
  · rintro ⟨w, rfl | ⟨rfl, hacc⟩⟩
    · exact derives_toContextFreeGrammar w
    · exact (derives_toContextFreeGrammar w).trans_produces
        (ContextFreeGrammar.produces_map_terminal_append_singleton_iff.2
          ⟨⟨M.eval w, []⟩, mem_toContextFreeGrammar_rules.2 (.inr ⟨hacc, rfl⟩), rfl, by simp⟩)

/-- The grammar of `M` generates the language of `M`. -/
@[simp] theorem language_toContextFreeGrammar (M : DFA α σ) :
    M.toContextFreeGrammar.language = M.accepts := by
  ext w
  change M.toContextFreeGrammar.Derives [nonterminal M.start] _ ↔ _
  rw [derives_toContextFreeGrammar_iff, mem_accepts]
  refine ⟨fun ⟨u, h⟩ ↦ ?_, fun h ↦ ⟨w, .inr ⟨rfl, h⟩⟩⟩
  rcases h with h | ⟨h, hacc⟩
  · simpa using congr(nonterminal (M.eval u) ∈ $h)
  · rwa [List.map_injective_iff.2 (fun _ _ ↦ terminal.inj) h]

end toContextFreeGrammar

section Threads

variable {T N σ : Type*} (M : DFA T σ) {p q r p₀ q₀ : σ} {l l₁ l₂ : List (Symbol T (σ × N × σ))}

/-- `M.Threads p l q` says that reading the sentential form `l` takes `M` from `p` to `q`: a
terminal steps the automaton, and a nonterminal `(p₀, A, q₀)` is passable only from its entry
state `p₀` and leaves at its exit state `q₀`. -/
def Threads : σ → List (Symbol T (σ × N × σ)) → σ → Prop
  | p, [], q => p = q
  | p, .terminal a :: l, q => Threads (M.step p a) l q
  | p, .nonterminal (p₀, _, q₀) :: l, q => p = p₀ ∧ Threads q₀ l q

@[simp] theorem threads_nil : M.Threads (N := N) p [] q ↔ p = q := .rfl

@[simp] theorem threads_terminal_cons {a : T} :
    M.Threads p (terminal a :: l) q ↔ M.Threads (M.step p a) l q := .rfl

@[simp] theorem threads_nonterminal_cons {A : N} :
    M.Threads p (nonterminal (p₀, A, q₀) :: l) q ↔ p = p₀ ∧ M.Threads q₀ l q := .rfl

/-- A concatenation threads through an intermediate state. -/
theorem threads_append :
    M.Threads p (l₁ ++ l₂) r ↔ ∃ q, M.Threads p l₁ q ∧ M.Threads q l₂ r := by
  induction l₁ generalizing p with
  | nil => simp
  | cons s l₁ ih => rcases s with a | ⟨p₀, A, q₀⟩ <;> simp [ih, and_assoc]

/-- A word threads as the automaton evaluates it. -/
@[simp] theorem threads_map_terminal {w : List T} :
    M.Threads (N := N) p (w.map terminal) q ↔ M.evalFrom p w = q := by
  induction w generalizing p with
  | nil => simp
  | cons a w ih => simp [ih]

end Threads

end DFA

namespace ContextFreeGrammar

variable {T : Type*} {σ : Type} [Finite σ] {G : ContextFreeGrammar T} {M : DFA T σ} {p q r : σ}

/-- The triple construction: the nonterminals are those of `G` between an entry and an exit state
of `M`, and the rules are those that erase to a rule of `G` and whose right-hand side threads from
the entry to the exit state of their left-hand side. The start nonterminal is that of `G` between
the start state and `q`. -/
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

/-- Erasing the states sends the rules of the triple construction to rules of `G`. -/
theorem mapNonterminal_mem_of_mem_triple_rules {r' : ContextFreeRule T (σ × G.NT × σ)}
    (h : r' ∈ (G.triple M q).rules) : r'.mapNonterminal (·.2.1) ∈ G.rules := by
  obtain ⟨⟨p', A, q'⟩, l⟩ := r'
  exact (mem_triple_rules.mp h).1

/-- A production of the triple construction preserves threading. -/
theorem Produces.threads {l l' : List (Symbol T (σ × G.NT × σ))}
    (h : (G.triple M q).Produces l l') (hl : M.Threads p l r) : M.Threads p l' r := by
  obtain ⟨⟨⟨p', A, q'⟩, o⟩, hr, hrw⟩ := h
  obtain ⟨pre, post, rfl, rfl⟩ := hrw.exists_parts
  obtain ⟨_, h₁₂, h₃⟩ := M.threads_append.mp hl
  obtain ⟨_, h₁, rfl, rfl⟩ := M.threads_append.mp h₁₂
  exact M.threads_append.mpr
    ⟨_, M.threads_append.mpr ⟨_, h₁, (mem_triple_rules.mp hr).2⟩, h₃⟩

/-- A derivation of the triple construction preserves threading. -/
theorem Derives.threads {l l' : List (Symbol T (σ × G.NT × σ))}
    (h : (G.triple M q).Derives l l') (hl : M.Threads p l r) : M.Threads p l' r := by
  induction h with
  | refl => exact hl
  | tail _ step ih => exact step.threads ih

/-- A derivation of a word in `G` lifts, from every state, to a derivation of the triple
construction from a form that threads as the automaton evaluates the word. -/
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

/-- The triple construction generates the words of `G` that take `M` to the state `q`. -/
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

/-- The grammar `G.inter M` of the intersection of `G` with a finite automaton `M` is the union of
the triple constructions at the accepting states of `M`. -/
noncomputable def inter (G : ContextFreeGrammar T) (M : DFA T σ) : ContextFreeGrammar T :=
  iUnion fun q : M.accept ↦ G.triple M q

/-- **Bar-Hillel's theorem**: `G.inter M` generates the intersection. -/
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

/-- Context-free languages are closed under intersection with regular languages. -/
theorem IsContextFree.inf_isRegular (hL : L.IsContextFree) (hR : R.IsRegular) :
    (L ⊓ R).IsContextFree := by
  obtain ⟨G, rfl⟩ := hL
  obtain ⟨σ, _, M, rfl⟩ := hR
  exact ⟨G.inter M, G.language_inter M⟩

end Language
