/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar
public import Linglib.Core.Computability.Language

/-!
# Context-free languages are closed under string homomorphisms

A string homomorphism `φ : FreeMonoid T →* FreeMonoid T'` sends each letter `a` to the word
`φ (of a)`. Replacing every terminal `a` in every rule of a grammar `g` by that word gives the
grammar `g.stringMap φ`, which [generates the image](##ContextFreeGrammar.language_stringMap)
`Language.stringMap φ g.language`. So the context-free languages are [closed under string
homomorphisms](##Language.IsContextFree.stringMap), and [under maps of
letters](##Language.IsContextFree.map). The development follows the closure under reversal in
`Mathlib/Computability/ContextFreeGrammar.lean`.

## References

* [hopcroft-motwani-ullman-2000]
-/

@[expose] public section

variable {T T' N : Type*}

namespace Symbol

/-- The word of symbols that a string homomorphism `φ` puts in place of a symbol: the image of a
terminal, and a nonterminal unchanged. -/
def stringMap (φ : FreeMonoid T →* FreeMonoid T') : Symbol T N → List (Symbol T' N)
  | terminal a => (φ (.of a)).toList.map terminal
  | nonterminal A => [nonterminal A]

variable {φ : FreeMonoid T →* FreeMonoid T'}

@[simp] theorem stringMap_terminal (a : T) :
    stringMap φ (terminal a : Symbol T N) = (φ (.of a)).toList.map terminal := rfl

@[simp] theorem stringMap_nonterminal (A : N) :
    stringMap φ (nonterminal A : Symbol T N) = [nonterminal A] := rfl

theorem flatMap_stringMap_map_terminal (w : List T) :
    (w.map (terminal (N := N))).flatMap (stringMap φ) = (φ (.ofList w)).toList.map terminal := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]

theorem eq_map_terminal_of_flatMap_stringMap :
    ∀ {l : List (Symbol T N)} {w' : List T'}, l.flatMap (stringMap φ) = w'.map terminal →
      ∃ w : List T, l = w.map terminal ∧ (φ (.ofList w)).toList = w'
  | [], w', heq => ⟨[], rfl, by simpa using (List.map_eq_nil_iff.mp heq.symm).symm⟩
  | nonterminal _ :: _, w', heq => by cases w' <;> simp at heq
  | terminal a :: l, w', heq => by
    rw [List.flatMap_cons, stringMap_terminal, eq_comm, List.map_eq_append_iff] at heq
    obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := heq
    obtain rfl := (List.map_injective_iff.mpr fun _ _ h => terminal.inj h) h₁
    obtain ⟨w, rfl, rfl⟩ := eq_map_terminal_of_flatMap_stringMap h₂.symm
    exact ⟨a :: w, rfl, by simp⟩

theorem exists_eq_of_flatMap_stringMap :
    ∀ {l : List (Symbol T N)} {p q : List (Symbol T' N)} {X : N},
      l.flatMap (stringMap φ) = p ++ [nonterminal X] ++ q →
      ∃ l₁ l₂, l = l₁ ++ [nonterminal X] ++ l₂ ∧
        l₁.flatMap (stringMap φ) = p ∧ l₂.flatMap (stringMap φ) = q
  | [], p, q, X, heq => by simp at heq
  | nonterminal Y :: l, [], q, X, heq => by
    simp only [List.flatMap_cons, stringMap_nonterminal, List.nil_append, List.singleton_append,
      List.cons.injEq, nonterminal.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨[], l, rfl, rfl, rfl⟩
  | nonterminal Y :: l, s :: p, q, X, heq => by
    simp only [List.flatMap_cons, stringMap_nonterminal, List.cons_append, List.cons.injEq] at heq
    obtain ⟨rfl, heq⟩ := heq
    obtain ⟨l₁, l₂, rfl, rfl, rfl⟩ := exists_eq_of_flatMap_stringMap heq
    exact ⟨nonterminal Y :: l₁, l₂, rfl, by simp, rfl⟩
  | terminal a :: l, p, q, X, heq => by
    rw [List.flatMap_cons, stringMap_terminal, List.append_assoc, List.append_eq_append_iff] at heq
    rcases heq with ⟨p', rfl, heq⟩ | ⟨c, hc, heq⟩
    · obtain ⟨l₁, l₂, rfl, rfl, rfl⟩ :=
        exists_eq_of_flatMap_stringMap (List.append_assoc _ _ _ ▸ heq)
      exact ⟨terminal a :: l₁, l₂, rfl, by simp, rfl⟩
    · obtain ⟨w₁, w₂, -, -, rfl⟩ := List.map_eq_append_iff.mp hc
      cases w₂ with
      | nil =>
        rw [List.map_nil, List.nil_append] at heq
        obtain ⟨l₁, l₂, rfl, h₁, rfl⟩ := exists_eq_of_flatMap_stringMap (l := l) (p := [])
          (by simpa only [List.nil_append] using heq.symm)
        exact ⟨terminal a :: l₁, l₂, rfl, by simpa [h₁] using hc, rfl⟩
      | cons b w₂ => simp at heq

end Symbol

namespace ContextFreeRule

variable (φ : FreeMonoid T →* FreeMonoid T') {r : ContextFreeRule T N} {u v : List (Symbol T N)}

/-- The rule whose right-hand side has every terminal replaced by its image under `φ`. -/
@[simps] def stringMap (r : ContextFreeRule T N) : ContextFreeRule T' N :=
  ⟨r.input, r.output.flatMap (Symbol.stringMap φ)⟩

protected theorem Rewrites.stringMap (hr : r.Rewrites u v) :
    (r.stringMap φ).Rewrites (u.flatMap (Symbol.stringMap φ))
      (v.flatMap (Symbol.stringMap φ)) := by
  obtain ⟨p, q, rfl, rfl⟩ := hr.exists_parts
  simpa [List.flatMap_append] using rewrites_of_exists_parts (r.stringMap φ)
    (p.flatMap (Symbol.stringMap φ)) (q.flatMap (Symbol.stringMap φ))

end ContextFreeRule

namespace ContextFreeGrammar

variable (φ : FreeMonoid T →* FreeMonoid T') {g : ContextFreeGrammar T} {u v : List (Symbol T g.NT)}

open scoped Classical in
/-- The grammar whose rules are those of `g` with every terminal replaced by its image under
`φ`. -/
@[simps] noncomputable def stringMap (g : ContextFreeGrammar T) : ContextFreeGrammar T' :=
  ⟨g.NT, g.initial, g.rules.image (ContextFreeRule.stringMap φ)⟩

theorem mem_stringMap_rules {r' : ContextFreeRule T' g.NT} :
    r' ∈ (g.stringMap φ).rules ↔ ∃ r ∈ g.rules, r.stringMap φ = r' := by
  classical exact Finset.mem_image

protected theorem Produces.stringMap (huv : g.Produces u v) :
    (g.stringMap φ).Produces (u.flatMap (Symbol.stringMap φ))
      (v.flatMap (Symbol.stringMap φ)) :=
  let ⟨r, hr, hrw⟩ := huv
  ⟨r.stringMap φ, (mem_stringMap_rules φ).mpr ⟨r, hr, rfl⟩, hrw.stringMap φ⟩

protected theorem Derives.stringMap (huv : g.Derives u v) :
    (g.stringMap φ).Derives (u.flatMap (Symbol.stringMap φ))
      (v.flatMap (Symbol.stringMap φ)) := by
  induction huv with
  | refl => exact .refl _
  | tail _ step ih => exact ih.trans_produces (step.stringMap φ)

theorem Produces.of_stringMap {v' : List (Symbol T' g.NT)}
    (hp : (g.stringMap φ).Produces (u.flatMap (Symbol.stringMap φ)) v') :
    ∃ v, g.Produces u v ∧ v.flatMap (Symbol.stringMap φ) = v' := by
  obtain ⟨r', hr', hrw⟩ := hp
  obtain ⟨r, hr, rfl⟩ := (mem_stringMap_rules φ).mp hr'
  obtain ⟨p, q, hu, rfl⟩ := hrw.exists_parts
  obtain ⟨u₁, u₂, rfl, rfl, rfl⟩ := Symbol.exists_eq_of_flatMap_stringMap (N := g.NT) hu
  exact ⟨u₁ ++ r.output ++ u₂, ⟨r, hr, ContextFreeRule.rewrites_of_exists_parts r u₁ u₂⟩,
    by simp [List.flatMap_append]⟩

theorem Derives.of_stringMap {v' : List (Symbol T' g.NT)}
    (hd : (g.stringMap φ).Derives (u.flatMap (Symbol.stringMap φ)) v') :
    ∃ v, g.Derives u v ∧ v.flatMap (Symbol.stringMap φ) = v' := by
  induction hd with
  | refl => exact ⟨u, .refl _, rfl⟩
  | tail _ step ih =>
    obtain ⟨v, hd, rfl⟩ := ih
    obtain ⟨v', hp, hv'⟩ := step.of_stringMap
    exact ⟨v', hd.trans_produces hp, hv'⟩

/-- The image grammar generates the image language. -/
@[simp] theorem language_stringMap (g : ContextFreeGrammar T) :
    (g.stringMap φ).language = Language.stringMap φ g.language := by
  ext w'
  rw [mem_language_iff, Language.mem_stringMap]
  constructor
  · intro hd
    obtain ⟨v, hdg, hv⟩ :=
      Derives.of_stringMap (u := [.nonterminal g.initial]) φ (by simpa using hd)
    obtain ⟨w, rfl, rfl⟩ := Symbol.eq_map_terminal_of_flatMap_stringMap hv
    exact ⟨w, (mem_language_iff _ _).mpr hdg, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    simpa [Symbol.flatMap_stringMap_map_terminal] using
      ((mem_language_iff _ _).mp hw).stringMap φ

end ContextFreeGrammar

/-- Context-free languages are closed under string homomorphisms. -/
protected theorem Language.IsContextFree.stringMap (φ : FreeMonoid T →* FreeMonoid T')
    {L : Language T} (h : L.IsContextFree) : (Language.stringMap φ L).IsContextFree := by
  rcases h with ⟨g, rfl⟩
  exact ⟨g.stringMap φ, by simp⟩

/-- Context-free languages are closed under maps of letters. -/
protected theorem Language.IsContextFree.map (f : T → T') {L : Language T}
    (h : L.IsContextFree) : (Language.map f L).IsContextFree := by
  simpa using h.stringMap (FreeMonoid.map f)
