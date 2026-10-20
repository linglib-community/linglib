/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar

/-!
# Context-free languages are closed under intersection with regular languages

The intersection of a context-free language with a regular language is context-free. The grammar
`G.inter M` is the triple construction: its nonterminals are the nonterminals of `G` annotated
with an entry and an exit state of the automaton `M`, and a rule of `G` yields one rule for every
way of threading the states of `M` through its right-hand side. A fresh start symbol rewrites to
the start nonterminal of `G` between the start state and each accepting state of `M`.

## Main definitions

* `ContextFreeGrammar.Annotates`: `Annotates M p l out q` says that the sentential form `l` is
  `out` with its nonterminals annotated so that the states of `M` thread from `p` to `q`.
* `ContextFreeGrammar.inter`: the grammar of the intersection of a grammar with a finite
  automaton.

## Main results

* `ContextFreeGrammar.language_inter`: `G.inter M` generates the intersection.
* `Language.IsContextFree.inf_isRegular`: closure under intersection with a regular language.

## References

* [bar-hillel-perles-shamir-1961]
* [hopcroft-motwani-ullman-2000]
-/

@[expose] public section

namespace ContextFreeGrammar

variable {T N : Type*} {σ : Type} (M : DFA T σ)

/-- `Annotates M p l out q` says that the sentential form `l` is `out` with every nonterminal
`A` replaced by some `some (p', A, q')` so that the states thread from `p` to `q`. A terminal
advances the automaton, and an annotated nonterminal jumps from its entry state to its exit
state. -/
inductive Annotates : σ → List (Symbol T (Option (σ × N × σ))) → List (Symbol T N) → σ → Prop
  | nil (p : σ) : Annotates p [] [] p
  | terminal {p q : σ} (a : T) {l : List (Symbol T (Option (σ × N × σ)))}
      {out : List (Symbol T N)} (h : Annotates (M.step p a) l out q) :
      Annotates p (.terminal a :: l) (.terminal a :: out) q
  | nonterminal {p p' q : σ} (A : N) {l : List (Symbol T (Option (σ × N × σ)))}
      {out : List (Symbol T N)} (h : Annotates p' l out q) :
      Annotates p (.nonterminal (some (p, A, p')) :: l) (.nonterminal A :: out) q

namespace Annotates

variable {M} {p q r : σ} {l l₁ l₂ : List (Symbol T (Option (σ × N × σ)))}
  {out out₁ out₂ : List (Symbol T N)}

theorem append (h₁ : Annotates M p l₁ out₁ q) (h₂ : Annotates M q l₂ out₂ r) :
    Annotates M p (l₁ ++ l₂) (out₁ ++ out₂) r := by
  induction h₁ with
  | nil => exact h₂
  | terminal a _ ih => exact .terminal a (ih h₂)
  | nonterminal A _ ih => exact .nonterminal A (ih h₂)

/-- An annotation of a concatenation splits at the concatenation. -/
theorem split_out (h : Annotates M p l (out₁ ++ out₂) r) :
    ∃ l₁ l₂ q, l = l₁ ++ l₂ ∧ Annotates M p l₁ out₁ q ∧ Annotates M q l₂ out₂ r := by
  induction out₁ generalizing l p with
  | nil => exact ⟨[], l, p, rfl, .nil p, h⟩
  | cons s out₁ ih =>
    cases h with
    | terminal a h =>
      obtain ⟨l₁, l₂, q, rfl, h₁, h₂⟩ := ih h
      exact ⟨_ :: l₁, l₂, q, rfl, .terminal a h₁, h₂⟩
    | nonterminal A h =>
      obtain ⟨l₁, l₂, q, rfl, h₁, h₂⟩ := ih h
      exact ⟨_ :: l₁, l₂, q, rfl, .nonterminal A h₁, h₂⟩

/-- An annotation that is a concatenation annotates a concatenation. -/
theorem split (h : Annotates M p (l₁ ++ l₂) out r) :
    ∃ out₁ out₂ q, out = out₁ ++ out₂ ∧ Annotates M p l₁ out₁ q ∧ Annotates M q l₂ out₂ r := by
  induction l₁ generalizing out p with
  | nil => exact ⟨[], out, p, rfl, .nil p, h⟩
  | cons s l₁ ih =>
    cases h with
    | terminal a h =>
      obtain ⟨out₁, out₂, q, rfl, h₁, h₂⟩ := ih h
      exact ⟨_ :: out₁, out₂, q, rfl, .terminal a h₁, h₂⟩
    | nonterminal A h =>
      obtain ⟨out₁, out₂, q, rfl, h₁, h₂⟩ := ih h
      exact ⟨_ :: out₁, out₂, q, rfl, .nonterminal A h₁, h₂⟩

theorem map_terminal (p : σ) (w : List T) :
    Annotates (N := N) M p (w.map .terminal) (w.map .terminal) (M.evalFrom p w) := by
  induction w generalizing p with
  | nil => exact .nil p
  | cons a w ih => exact .terminal a (ih (M.step p a))

/-- A word annotates only itself, and ends where the automaton ends. -/
theorem eq_of_map_terminal_right {w : List T} (h : Annotates M p l (w.map .terminal) q) :
    l = w.map .terminal ∧ q = M.evalFrom p w := by
  induction w generalizing l p with
  | nil => cases h; exact ⟨rfl, rfl⟩
  | cons a w ih =>
    cases h with
    | terminal _ h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩

/-- A word is annotated only by itself, and ends where the automaton ends. -/
theorem eq_of_map_terminal_left {w : List T} (h : Annotates M p (w.map .terminal) out q) :
    out = w.map .terminal ∧ q = M.evalFrom p w := by
  induction w generalizing out p with
  | nil => cases h; exact ⟨rfl, rfl⟩
  | cons a w ih =>
    cases h with
    | terminal _ h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩

theorem eq_of_singleton_right {A : N} (h : Annotates M p l [.nonterminal A] q) :
    l = [.nonterminal (some (p, A, q))] := by
  cases h with
  | nonterminal _ h => cases h; rfl

theorem eq_of_singleton_left {p₀ q₀ : σ} {A : N}
    (h : Annotates M p [.nonterminal (some (p₀, A, q₀))] out q) :
    out = [.nonterminal A] ∧ p₀ = p ∧ q₀ = q := by
  cases h with
  | nonterminal _ h => cases h; exact ⟨rfl, rfl, rfl⟩

theorem none_notMem (h : Annotates M p l out q) : Symbol.nonterminal none ∉ l := by
  induction h with
  | nil => simp
  | terminal _ _ ih => simpa using ih
  | nonterminal _ _ ih => simpa using ih

end Annotates

variable [Fintype σ]

open scoped Classical in
/-- The annotations of `out` from state `p`, each with its exit state. -/
noncomputable def annotations :
    σ → List (Symbol T N) → Finset (σ × List (Symbol T (Option (σ × N × σ))))
  | p, [] => {(p, [])}
  | p, .terminal a :: out => (annotations (M.step p a) out).image fun x => (x.1, .terminal a :: x.2)
  | p, .nonterminal A :: out => Finset.univ.biUnion fun p' =>
      (annotations p' out).image fun x => (x.1, .nonterminal (some (p, A, p')) :: x.2)

theorem mem_annotations {p : σ} {out : List (Symbol T N)}
    {x : σ × List (Symbol T (Option (σ × N × σ)))} :
    x ∈ annotations M p out ↔ Annotates M p x.2 out x.1 := by
  induction out generalizing p x with
  | nil =>
    obtain ⟨q, l⟩ := x
    simp only [annotations, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact .nil _
    · rintro ⟨⟩; exact ⟨rfl, rfl⟩
  | cons s out ih =>
    obtain ⟨q, l⟩ := x
    cases s with
    | terminal a =>
      simp only [annotations, Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨q', l'⟩, h, rfl, rfl⟩; exact .terminal a (ih.mp h)
      · intro h
        cases h with
        | terminal _ h => exact ⟨(q, _), ih.mpr h, rfl, rfl⟩
    | nonterminal A =>
      simp only [annotations, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · rintro ⟨p', ⟨q', l'⟩, h, rfl, rfl⟩; exact .nonterminal A (ih.mp h)
      · intro h
        cases h with
        | nonterminal _ h => exact ⟨_, (q, _), ih.mpr h, rfl, rfl⟩

open scoped Classical in
/-- The grammar `G.inter M` generates the intersection of `G` with a finite automaton `M`. Its
nonterminals are those of `G` annotated with entry and exit states, it has each rule of `G` in
every annotation of its right-hand side, and its fresh start symbol `none` rewrites to the start
nonterminal of `G` between the start state and each accepting state. -/
noncomputable def inter (G : ContextFreeGrammar T) (M : DFA T σ) : ContextFreeGrammar T where
  NT := Option (σ × G.NT × σ)
  initial := none
  rules := (Finset.univ.filter (· ∈ M.accept)).image (fun q =>
      ⟨none, [.nonterminal (some (M.start, G.initial, q))]⟩) ∪
    G.rules.biUnion fun r => Finset.univ.biUnion fun p =>
      (annotations M p r.output).image fun x => ⟨some (p, r.input, x.1), x.2⟩

variable {G : ContextFreeGrammar T}

@[simp] theorem inter_initial : (G.inter M).initial = none := rfl

variable {M}

theorem mem_inter_rules {r' : ContextFreeRule T (G.inter M).NT} :
    r' ∈ (G.inter M).rules ↔
      (r'.input = none ∧
          ∃ q ∈ M.accept, r'.output = [.nonterminal (some (M.start, G.initial, q))]) ∨
        ∃ r ∈ G.rules, ∃ p q, r'.input = some (p, r.input, q) ∧
          Annotates M p r'.output r.output q := by
  obtain ⟨i, o⟩ := r'
  simp only [inter, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_biUnion, mem_annotations, ContextFreeRule.mk.injEq]
  refine or_congr ⟨fun ⟨q, hq, h₁, h₂⟩ => ⟨h₁.symm, q, hq, h₂.symm⟩,
    fun ⟨h₁, q, hq, h₂⟩ => ⟨q, hq, h₁.symm, h₂.symm⟩⟩
    (exists_congr fun r => and_congr_right fun _ => ?_)
  constructor
  · rintro ⟨p, ⟨q, l⟩, h, rfl, rfl⟩; exact ⟨p, q, rfl, h⟩
  · rintro ⟨p, q, rfl, h⟩; exact ⟨p, (q, o), h, rfl, rfl⟩

/-! ### The grammar generates the intersection -/

/-- A step of `G.inter M` on an annotated form is a step of `G` on the form it annotates. -/
theorem Produces.of_inter {l' t' : List (Symbol T (G.inter M).NT)}
    (step : (G.inter M).Produces l' t') {p q : σ} {out : List (Symbol T G.NT)}
    (h : Annotates M p l' out q) : ∃ out', G.Produces out out' ∧ Annotates M p t' out' q := by
  obtain ⟨r', hr', hrw⟩ := step
  obtain ⟨pre, post, rfl, rfl⟩ := hrw.exists_parts
  rcases mem_inter_rules.mp hr' with ⟨hi, -⟩ | ⟨r, hr, p₀, q₀, hi, hbody⟩
  · exact absurd (by simp [hi]) h.none_notMem
  · obtain ⟨out₁, out₃, p₂, rfl, h₁₂, h₃⟩ := h.split
    obtain ⟨out₁, out₂, p₁, rfl, h₁, h₂⟩ := h₁₂.split
    rw [hi] at h₂
    obtain ⟨rfl, rfl, rfl⟩ := h₂.eq_of_singleton_left
    exact ⟨out₁ ++ r.output ++ out₃, ⟨r, hr, ContextFreeRule.rewrites_of_exists_parts r out₁ out₃⟩,
      (h₁.append hbody).append h₃⟩

/-- A derivation of `G.inter M` from an annotated form is a derivation of `G` from the form it
annotates. -/
theorem Derives.of_inter {l' t' : List (Symbol T (G.inter M).NT)}
    (hd : (G.inter M).Derives l' t') {p q : σ} {out : List (Symbol T G.NT)}
    (h : Annotates M p l' out q) : ∃ out', G.Derives out out' ∧ Annotates M p t' out' q := by
  induction hd with
  | refl => exact ⟨out, .refl _, h⟩
  | tail _ step ih =>
    obtain ⟨out', hd', h'⟩ := ih
    obtain ⟨out'', hp, h''⟩ := step.of_inter h'
    exact ⟨out'', hd'.trans_produces hp, h''⟩

theorem language_inter_le : (G.inter M).language ≤ G.language ⊓ M.accepts := by
  intro w hw
  rcases ((mem_language_iff _ _).mp hw).eq_or_head with heq | ⟨v, hstep, hd⟩
  · cases w <;> simp at heq
  · obtain ⟨r', hr', hin, rfl⟩ := produces_singleton_iff.mp hstep
    rcases mem_inter_rules.mp hr' with ⟨-, q, hq, hout⟩ | ⟨r, -, p, q, hi, -⟩
    · rw [hout] at hd
      obtain ⟨out, hdG, h⟩ := hd.of_inter (.nonterminal (p := M.start) G.initial (.nil q))
      obtain ⟨rfl, rfl⟩ := h.eq_of_map_terminal_left
      exact ⟨(mem_language_iff _ _).mpr hdG, hq⟩
    · simp [hin] at hi

/-- Every derivation of `G` of a word is the projection of a derivation of `G.inter M` from an
annotation of its start, for any entry state. -/
theorem exists_annotates_of_derives {out : List (Symbol T G.NT)} {w : List T}
    (hd : G.Derives out (w.map .terminal)) (p : σ) :
    ∃ l, Annotates M p l out (M.evalFrom p w) ∧ (G.inter M).Derives l (w.map .terminal) := by
  induction hd using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨_, .map_terminal p w, .refl _⟩
  | head step _ ih =>
    obtain ⟨l, hl, hd⟩ := ih
    obtain ⟨r, hr, hrw⟩ := step
    obtain ⟨pre, post, rfl, rfl⟩ := hrw.exists_parts
    obtain ⟨l₁, l₃, p₂, rfl, h₁₂, h₃⟩ := hl.split_out
    obtain ⟨l₁, l₂, p₁, rfl, h₁, h₂⟩ := h₁₂.split_out
    exact ⟨l₁ ++ [.nonterminal (some (p₁, r.input, p₂))] ++ l₃,
      (h₁.append (.nonterminal r.input (.nil p₂))).append h₃,
      (Produces.single ⟨⟨_, l₂⟩, mem_inter_rules.mpr (.inr ⟨r, hr, p₁, p₂, rfl, h₂⟩),
        ContextFreeRule.rewrites_of_exists_parts _ l₁ l₃⟩).trans hd⟩

theorem le_language_inter : G.language ⊓ M.accepts ≤ (G.inter M).language := by
  rintro w ⟨hG, hM⟩
  obtain ⟨l, hl, hd⟩ :=
    exists_annotates_of_derives (M := M) ((mem_language_iff _ _).mp hG) M.start
  rw [hl.eq_of_singleton_right] at hd
  exact (mem_language_iff _ _).mpr <| (produces_singleton_iff.mpr
    ⟨⟨none, [.nonterminal (some (M.start, G.initial, M.eval w))]⟩,
      mem_inter_rules.mpr (.inl ⟨rfl, _, hM, rfl⟩), rfl, rfl⟩).trans_derives hd

/-- **Bar-Hillel's theorem**: `G.inter M` generates the intersection. -/
theorem language_inter (G : ContextFreeGrammar T) (M : DFA T σ) :
    (G.inter M).language = G.language ⊓ M.accepts :=
  language_inter_le.antisymm le_language_inter

end ContextFreeGrammar

/-- Context-free languages are closed under intersection with regular languages. -/
theorem Language.IsContextFree.inf_isRegular {α : Type*} {L R : Language α}
    (hL : L.IsContextFree) (hR : R.IsRegular) : (L ⊓ R).IsContextFree := by
  obtain ⟨G, rfl⟩ := hL
  obtain ⟨σ, _, M, rfl⟩ := hR
  exact ⟨G.inter M, G.language_inter M⟩
