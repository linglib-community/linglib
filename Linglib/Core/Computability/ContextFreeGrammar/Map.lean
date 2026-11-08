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

A string homomorphism `φ : FreeMonoid T →* FreeMonoid T'` is fixed by the word `φ (of a)` it
assigns to each letter, and acts on languages by `Language.stringMap φ`. The image of a
context-free language is context-free: replace every terminal `a` in every rule by the word
`φ (of a)`.

## Main definitions

* `Symbol.applyHom`, `ContextFreeRule.applyHom`, `ContextFreeGrammar.applyHom`: a string
  homomorphism applied to a symbol, a rule and a grammar.

## Main results

* `ContextFreeGrammar.applyHom_language`: the image grammar generates the image language.
* `Language.IsContextFree.stringMap`: closure under string homomorphisms, and
  `Language.IsContextFree.map` under maps of letters.

## References

* [hopcroft-motwani-ullman-2000]
-/

@[expose] public section

variable {T T' N : Type*}

namespace Symbol

/-- The string homomorphism `φ` sends a terminal to the word of terminals it maps to and keeps a
nonterminal. -/
def applyHom (φ : FreeMonoid T →* FreeMonoid T') : Symbol T N → List (Symbol T' N)
  | terminal a => (φ (.of a)).toList.map terminal
  | nonterminal A => [nonterminal A]

variable {φ : FreeMonoid T →* FreeMonoid T'}

@[simp] theorem applyHom_terminal (a : T) :
    applyHom φ (terminal a : Symbol T N) = (φ (.of a)).toList.map terminal := rfl

@[simp] theorem applyHom_nonterminal (A : N) :
    applyHom φ (nonterminal A : Symbol T N) = [nonterminal A] := rfl

theorem flatMap_applyHom_map_terminal (w : List T) :
    (w.map (terminal (N := N))).flatMap (applyHom φ) = (φ (.ofList w)).toList.map terminal := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]

theorem eq_map_terminal_of_flatMap_applyHom :
    ∀ {l : List (Symbol T N)} {w' : List T'}, l.flatMap (applyHom φ) = w'.map terminal →
      ∃ w : List T, l = w.map terminal ∧ (φ (.ofList w)).toList = w'
  | [], w', heq => ⟨[], rfl, by simpa using (List.map_eq_nil_iff.mp heq.symm).symm⟩
  | nonterminal _ :: _, w', heq => by cases w' <;> simp at heq
  | terminal a :: l, w', heq => by
    rw [List.flatMap_cons, applyHom_terminal, eq_comm, List.map_eq_append_iff] at heq
    obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := heq
    obtain rfl := (List.map_injective_iff.mpr fun _ _ h => terminal.inj h) h₁
    obtain ⟨w, rfl, rfl⟩ := eq_map_terminal_of_flatMap_applyHom h₂.symm
    exact ⟨a :: w, rfl, by simp⟩

theorem exists_eq_of_flatMap_applyHom :
    ∀ {l : List (Symbol T N)} {p q : List (Symbol T' N)} {X : N},
      l.flatMap (applyHom φ) = p ++ [nonterminal X] ++ q →
      ∃ l₁ l₂, l = l₁ ++ [nonterminal X] ++ l₂ ∧
        l₁.flatMap (applyHom φ) = p ∧ l₂.flatMap (applyHom φ) = q
  | [], p, q, X, heq => by simp at heq
  | nonterminal Y :: l, [], q, X, heq => by
    simp only [List.flatMap_cons, applyHom_nonterminal, List.nil_append, List.singleton_append,
      List.cons.injEq, nonterminal.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨[], l, rfl, rfl, rfl⟩
  | nonterminal Y :: l, s :: p, q, X, heq => by
    simp only [List.flatMap_cons, applyHom_nonterminal, List.cons_append, List.cons.injEq] at heq
    obtain ⟨rfl, heq⟩ := heq
    obtain ⟨l₁, l₂, rfl, rfl, rfl⟩ := exists_eq_of_flatMap_applyHom heq
    exact ⟨nonterminal Y :: l₁, l₂, rfl, by simp, rfl⟩
  | terminal a :: l, p, q, X, heq => by
    rw [List.flatMap_cons, applyHom_terminal, List.append_assoc, List.append_eq_append_iff] at heq
    rcases heq with ⟨p', rfl, heq⟩ | ⟨c, hc, heq⟩
    · obtain ⟨l₁, l₂, rfl, rfl, rfl⟩ :=
        exists_eq_of_flatMap_applyHom (List.append_assoc _ _ _ ▸ heq)
      exact ⟨terminal a :: l₁, l₂, rfl, by simp, rfl⟩
    · obtain ⟨w₁, w₂, -, -, rfl⟩ := List.map_eq_append_iff.mp hc
      cases w₂ with
      | nil =>
        rw [List.map_nil, List.nil_append] at heq
        obtain ⟨l₁, l₂, rfl, h₁, rfl⟩ := exists_eq_of_flatMap_applyHom (l := l) (p := [])
          (by simpa only [List.nil_append] using heq.symm)
        exact ⟨terminal a :: l₁, l₂, rfl, by simpa [h₁] using hc, rfl⟩
      | cons b w₂ => simp at heq

end Symbol

namespace ContextFreeRule

/-- A string homomorphism applied to a rule. -/
def applyHom (φ : FreeMonoid T →* FreeMonoid T') (r : ContextFreeRule T N) :
    ContextFreeRule T' N :=
  ⟨r.input, r.output.flatMap (Symbol.applyHom φ)⟩

variable (φ : FreeMonoid T →* FreeMonoid T')

@[simp] theorem applyHom_input (r : ContextFreeRule T N) : (r.applyHom φ).input = r.input := rfl

@[simp] theorem applyHom_output (r : ContextFreeRule T N) :
    (r.applyHom φ).output = r.output.flatMap (Symbol.applyHom φ) := rfl

theorem Rewrites.applyHom {r : ContextFreeRule T N} {u v : List (Symbol T N)}
    (hr : r.Rewrites u v) :
    (r.applyHom φ).Rewrites (u.flatMap (Symbol.applyHom φ)) (v.flatMap (Symbol.applyHom φ)) := by
  obtain ⟨p, q, rfl, rfl⟩ := hr.exists_parts
  simpa [List.flatMap_append] using rewrites_of_exists_parts (r.applyHom φ)
    (p.flatMap (Symbol.applyHom φ)) (q.flatMap (Symbol.applyHom φ))

end ContextFreeRule

namespace ContextFreeGrammar

variable (φ : FreeMonoid T →* FreeMonoid T') {G : ContextFreeGrammar T}

open scoped Classical in
/-- The grammar `G.applyHom φ` replaces every terminal in every rule of `G` by its image under
`φ`. -/
noncomputable def applyHom (G : ContextFreeGrammar T) : ContextFreeGrammar T' :=
  ⟨G.NT, G.initial, G.rules.image (ContextFreeRule.applyHom φ)⟩

@[simp] theorem applyHom_NT : (G.applyHom φ).NT = G.NT := rfl

@[simp] theorem applyHom_initial : (G.applyHom φ).initial = G.initial := rfl

theorem mem_applyHom_rules {r' : ContextFreeRule T' G.NT} :
    r' ∈ (G.applyHom φ).rules ↔ ∃ r ∈ G.rules, r.applyHom φ = r' := by
  classical exact Finset.mem_image

theorem Produces.applyHom {u v : List (Symbol T G.NT)} (huv : G.Produces u v) :
    (G.applyHom φ).Produces (u.flatMap (Symbol.applyHom φ)) (v.flatMap (Symbol.applyHom φ)) :=
  let ⟨r, hr, hrw⟩ := huv
  ⟨r.applyHom φ, (mem_applyHom_rules φ).mpr ⟨r, hr, rfl⟩, hrw.applyHom φ⟩

theorem Derives.applyHom {u v : List (Symbol T G.NT)} (huv : G.Derives u v) :
    (G.applyHom φ).Derives (u.flatMap (Symbol.applyHom φ)) (v.flatMap (Symbol.applyHom φ)) := by
  induction huv with
  | refl => exact .refl _
  | tail _ step ih => exact ih.trans_produces (step.applyHom φ)

theorem Produces.of_applyHom {l : List (Symbol T G.NT)} {t' : List (Symbol T' G.NT)}
    (hp : (G.applyHom φ).Produces (l.flatMap (Symbol.applyHom φ)) t') :
    ∃ t, G.Produces l t ∧ t.flatMap (Symbol.applyHom φ) = t' := by
  obtain ⟨r', hr', hrw⟩ := hp
  obtain ⟨r, hr, rfl⟩ := (mem_applyHom_rules φ).mp hr'
  obtain ⟨p, q, hl, rfl⟩ := hrw.exists_parts
  obtain ⟨l₁, l₂, rfl, rfl, rfl⟩ := Symbol.exists_eq_of_flatMap_applyHom (N := G.NT) hl
  exact ⟨l₁ ++ r.output ++ l₂, ⟨r, hr, ContextFreeRule.rewrites_of_exists_parts r l₁ l₂⟩,
    by simp [List.flatMap_append]⟩

theorem Derives.of_applyHom {l : List (Symbol T G.NT)} {t' : List (Symbol T' G.NT)}
    (hd : (G.applyHom φ).Derives (l.flatMap (Symbol.applyHom φ)) t') :
    ∃ t, G.Derives l t ∧ t.flatMap (Symbol.applyHom φ) = t' := by
  induction hd with
  | refl => exact ⟨l, .refl _, rfl⟩
  | tail _ step ih =>
    obtain ⟨t, hd, rfl⟩ := ih
    obtain ⟨t', hp, ht'⟩ := step.of_applyHom
    exact ⟨t', hd.trans_produces hp, ht'⟩

/-- The image grammar generates the image language. -/
theorem applyHom_language (G : ContextFreeGrammar T) :
    (G.applyHom φ).language = Language.stringMap φ G.language := by
  ext w'
  rw [mem_language_iff, Language.mem_stringMap]
  constructor
  · intro hd
    obtain ⟨t, hdG, ht⟩ := Derives.of_applyHom (l := [.nonterminal G.initial]) φ (by simpa using hd)
    obtain ⟨w, rfl, rfl⟩ := Symbol.eq_map_terminal_of_flatMap_applyHom ht
    exact ⟨w, (mem_language_iff _ _).mpr hdG, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    simpa [Symbol.flatMap_applyHom_map_terminal] using ((mem_language_iff _ _).mp hw).applyHom φ

end ContextFreeGrammar

/-- Context-free languages are closed under string homomorphisms. -/
theorem Language.IsContextFree.stringMap (φ : FreeMonoid T →* FreeMonoid T') {L : Language T}
    (hL : L.IsContextFree) : (Language.stringMap φ L).IsContextFree :=
  let ⟨G, hG⟩ := hL
  ⟨G.applyHom φ, by rw [ContextFreeGrammar.applyHom_language, hG]⟩

/-- Context-free languages are closed under maps of letters. -/
theorem Language.IsContextFree.map (f : T → T') {L : Language T} (hL : L.IsContextFree) :
    (Language.map f L).IsContextFree :=
  Language.stringMap_map f ▸ hL.stringMap _
