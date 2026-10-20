/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar

/-!
# Context-free languages are closed under string homomorphisms

A map `f : T → List T'` on letters extends to a monoid homomorphism on words, `List.flatMap f`,
and to a semiring homomorphism `Language.stringMap f` on languages. The image of a context-free
language under it is context-free: replace every terminal `a` in every rule by the string `f a`.

## Main definitions

* `Language.stringMap`: the image of a language under a string homomorphism.
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

/-- The image of a language under the string homomorphism induced by `f : T → List T'`, the
monoid homomorphism `List.flatMap f` on words; `Language.map` is the case of one-letter images. -/
def Language.stringMap (f : T → List T') : Language T →+* Language T' where
  toFun := Set.image (List.flatMap f)
  map_zero' := Set.image_empty _
  map_one' := Set.image_singleton
  map_add' := Set.image_union _
  map_mul' _ _ := Set.image_image2_distrib fun _ _ => List.flatMap_append ..

@[simp] theorem Language.mem_stringMap {f : T → List T'} {L : Language T} {w : List T'} :
    w ∈ Language.stringMap f L ↔ ∃ v ∈ L, List.flatMap f v = w := Iff.rfl

theorem Language.stringMap_singleton (f : T → T') (L : Language T) :
    Language.stringMap (fun a => [f a]) L = Language.map f L := by
  show Set.image _ L = Set.image _ L
  simp [← List.map_eq_flatMap]

namespace Symbol

/-- The string homomorphism `h` sends a terminal to the string of terminals it maps to and keeps
a nonterminal. -/
def applyHom (h : T → List T') : Symbol T N → List (Symbol T' N)
  | terminal a => (h a).map terminal
  | nonterminal A => [nonterminal A]

@[simp] theorem applyHom_terminal (h : T → List T') (a : T) :
    applyHom h (terminal a : Symbol T N) = (h a).map terminal := rfl

@[simp] theorem applyHom_nonterminal (h : T → List T') (A : N) :
    applyHom h (nonterminal A : Symbol T N) = [nonterminal A] := rfl

theorem flatMap_applyHom_map_terminal (h : T → List T') (w : List T) :
    (w.map (terminal (N := N))).flatMap (applyHom h) = (w.flatMap h).map terminal := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

/-- A word of the image grammar comes from a word of the source. -/
theorem eq_map_terminal_of_flatMap_applyHom {h : T → List T'} :
    ∀ {l : List (Symbol T N)} {w' : List T'}, l.flatMap (applyHom h) = w'.map terminal →
      ∃ w : List T, l = w.map terminal ∧ w.flatMap h = w'
  | [], w', heq => ⟨[], rfl, by simpa using (List.map_eq_nil_iff.mp heq.symm).symm⟩
  | nonterminal _ :: _, w', heq => by cases w' <;> simp at heq
  | terminal a :: l, w', heq => by
    rw [List.flatMap_cons, applyHom_terminal, eq_comm, List.map_eq_append_iff] at heq
    obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := heq
    obtain rfl := (List.map_injective_iff.mpr fun _ _ h => terminal.inj h) h₁
    obtain ⟨w, rfl, rfl⟩ := eq_map_terminal_of_flatMap_applyHom h₂.symm
    exact ⟨a :: w, rfl, by simp⟩

/-- A nonterminal in the image of a sentential form comes from the same nonterminal in the
source. -/
theorem exists_eq_of_flatMap_applyHom {h : T → List T'} :
    ∀ {l : List (Symbol T N)} {p q : List (Symbol T' N)} {X : N},
      l.flatMap (applyHom h) = p ++ [nonterminal X] ++ q →
      ∃ l₁ l₂, l = l₁ ++ [nonterminal X] ++ l₂ ∧
        l₁.flatMap (applyHom h) = p ∧ l₂.flatMap (applyHom h) = q
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
def applyHom (h : T → List T') (r : ContextFreeRule T N) : ContextFreeRule T' N :=
  ⟨r.input, r.output.flatMap (Symbol.applyHom h)⟩

@[simp] theorem applyHom_input (h : T → List T') (r : ContextFreeRule T N) :
    (r.applyHom h).input = r.input := rfl

@[simp] theorem applyHom_output (h : T → List T') (r : ContextFreeRule T N) :
    (r.applyHom h).output = r.output.flatMap (Symbol.applyHom h) := rfl

theorem Rewrites.applyHom (h : T → List T') {r : ContextFreeRule T N} {u v : List (Symbol T N)}
    (hr : r.Rewrites u v) :
    (r.applyHom h).Rewrites (u.flatMap (Symbol.applyHom h)) (v.flatMap (Symbol.applyHom h)) := by
  obtain ⟨p, q, rfl, rfl⟩ := hr.exists_parts
  simpa [List.flatMap_append] using rewrites_of_exists_parts (r.applyHom h)
    (p.flatMap (Symbol.applyHom h)) (q.flatMap (Symbol.applyHom h))

end ContextFreeRule

namespace ContextFreeGrammar

variable (h : T → List T') {G : ContextFreeGrammar T}

open scoped Classical in
/-- The grammar `G.applyHom h` replaces every terminal in every rule of `G` by its image under
`h`. -/
noncomputable def applyHom (G : ContextFreeGrammar T) : ContextFreeGrammar T' :=
  ⟨G.NT, G.initial, G.rules.image (ContextFreeRule.applyHom h)⟩

@[simp] theorem applyHom_NT : (G.applyHom h).NT = G.NT := rfl

@[simp] theorem applyHom_initial : (G.applyHom h).initial = G.initial := rfl

theorem mem_applyHom_rules {r' : ContextFreeRule T' G.NT} :
    r' ∈ (G.applyHom h).rules ↔ ∃ r ∈ G.rules, r.applyHom h = r' := by
  classical exact Finset.mem_image

theorem Produces.applyHom {u v : List (Symbol T G.NT)} (huv : G.Produces u v) :
    (G.applyHom h).Produces (u.flatMap (Symbol.applyHom h)) (v.flatMap (Symbol.applyHom h)) :=
  let ⟨r, hr, hrw⟩ := huv
  ⟨r.applyHom h, (mem_applyHom_rules h).mpr ⟨r, hr, rfl⟩, hrw.applyHom h⟩

theorem Derives.applyHom {u v : List (Symbol T G.NT)} (huv : G.Derives u v) :
    (G.applyHom h).Derives (u.flatMap (Symbol.applyHom h)) (v.flatMap (Symbol.applyHom h)) := by
  induction huv with
  | refl => exact .refl _
  | tail _ step ih => exact ih.trans_produces (step.applyHom h)

/-- A step of the image grammar from the image of a sentential form is the image of a step of
the source grammar. -/
theorem Produces.of_applyHom {l : List (Symbol T G.NT)} {t' : List (Symbol T' G.NT)}
    (hp : (G.applyHom h).Produces (l.flatMap (Symbol.applyHom h)) t') :
    ∃ t, G.Produces l t ∧ t.flatMap (Symbol.applyHom h) = t' := by
  obtain ⟨r', hr', hrw⟩ := hp
  obtain ⟨r, hr, rfl⟩ := (mem_applyHom_rules h).mp hr'
  obtain ⟨p, q, hl, rfl⟩ := hrw.exists_parts
  obtain ⟨l₁, l₂, rfl, rfl, rfl⟩ := Symbol.exists_eq_of_flatMap_applyHom (N := G.NT) hl
  exact ⟨l₁ ++ r.output ++ l₂, ⟨r, hr, ContextFreeRule.rewrites_of_exists_parts r l₁ l₂⟩,
    by simp [List.flatMap_append]⟩

theorem Derives.of_applyHom {l : List (Symbol T G.NT)} {t' : List (Symbol T' G.NT)}
    (hd : (G.applyHom h).Derives (l.flatMap (Symbol.applyHom h)) t') :
    ∃ t, G.Derives l t ∧ t.flatMap (Symbol.applyHom h) = t' := by
  induction hd with
  | refl => exact ⟨l, .refl _, rfl⟩
  | tail _ step ih =>
    obtain ⟨t, hd, rfl⟩ := ih
    obtain ⟨t', hp, ht'⟩ := step.of_applyHom
    exact ⟨t', hd.trans_produces hp, ht'⟩

/-- The image grammar generates the image language. -/
theorem applyHom_language (G : ContextFreeGrammar T) :
    (G.applyHom h).language = Language.stringMap h G.language := by
  ext w'
  rw [mem_language_iff, Language.mem_stringMap]
  constructor
  · intro hd
    obtain ⟨t, hdG, ht⟩ := Derives.of_applyHom (l := [.nonterminal G.initial]) h (by simpa using hd)
    obtain ⟨w, rfl, rfl⟩ := Symbol.eq_map_terminal_of_flatMap_applyHom ht
    exact ⟨w, (mem_language_iff _ _).mpr hdG, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    simpa [Symbol.flatMap_applyHom_map_terminal] using ((mem_language_iff _ _).mp hw).applyHom h

end ContextFreeGrammar

/-- Context-free languages are closed under string homomorphisms. -/
theorem Language.IsContextFree.stringMap (f : T → List T') {L : Language T}
    (hL : L.IsContextFree) : (Language.stringMap f L).IsContextFree :=
  let ⟨G, hG⟩ := hL
  ⟨G.applyHom f, by rw [ContextFreeGrammar.applyHom_language, hG]⟩

/-- Context-free languages are closed under maps of letters. -/
theorem Language.IsContextFree.map (f : T → T') {L : Language T} (hL : L.IsContextFree) :
    (Language.map f L).IsContextFree :=
  Language.stringMap_singleton f L ▸ hL.stringMap _
