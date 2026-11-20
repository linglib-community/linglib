/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar
public import Linglib.Core.Computability.Language
public import Mathlib.Order.FixedPoints

/-!
# The equations of a context-free grammar

A context-free grammar is a system of equations between languages, one for each nonterminal: the
grammar `S → a S b | ε` is the equation `X = a X b + 1`. This file proves that the languages
derived from the nonterminals are the least solution of that system.

For an assignment `X` of languages to the nonterminals, `Language.subst X u` is the language of
the sentential form `u` with `X` substituted for its nonterminals: the product of the languages
of its symbols, where a letter `a` stands for the language of the word `a` and a nonterminal `A`
for `X A`. The equations of a grammar `g` are the map `g.equations`, which sends `X` to the
assignment whose value at `A` is the union of `Language.subst X u` over the rules `A → u`.

We write `g.languageFrom u` for the language of the words that the sentential form `u` derives.
It is multiplicative in `u`, so it is the substitution of the languages derived from the
nonterminals (`ContextFreeGrammar.languageFrom_eq_subst`), and these languages solve the
equations (`ContextFreeGrammar.equations_languageFrom`). When `X` is closed under the equations,
substituting it shrinks along derivations (`ContextFreeGrammar.Derives.subst_le`), so the
languages derived from the nonterminals are the least such `X`
(`ContextFreeGrammar.isLeast_languageFrom`) and the least fixed point of the equations
(`ContextFreeGrammar.lfp_equations`).

## Implementation notes

The right-hand side of an equation is a union over the rules of the grammar at a nonterminal,
written `⨆ r ∈ g.rules, ⨆ _ : r.input = A, …` so that the nonterminals need no decidable equality.
Nothing here uses that a grammar has finitely many rules.

## References

* [J.-M. Autebert, J. Berstel and L. Boasson, *Context-Free Languages and Pushdown
  Automata*][autebert-berstel-boasson-1997]
-/

@[expose] public section

open Symbol

namespace Language

variable {T N : Type*} {X : N → Language T}

/-- The language of a sentential form `u` with the languages `X` substituted for its
nonterminals: the product of the languages of its symbols. -/
def subst (X : N → Language T) (u : List (Symbol T N)) : Language T :=
  (u.map (Symbol.elim (fun a ↦ {[a]}) X)).prod

@[simp] theorem subst_nil : subst X [] = 1 := rfl

@[simp] theorem subst_cons (s : Symbol T N) (u : List (Symbol T N)) :
    subst X (s :: u) = s.elim (fun a ↦ {[a]}) X * subst X u := by
  simp [subst]

theorem subst_append (u v : List (Symbol T N)) : subst X (u ++ v) = subst X u * subst X v := by
  simp [subst]

@[simp] theorem subst_map_terminal (w : List T) : subst X (w.map terminal) = {w} := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    ext v
    simp [ih, mem_mul, eq_comm]

theorem subst_mono (u : List (Symbol T N)) : Monotone fun X : N → Language T ↦ subst X u := by
  intro X Y h
  change subst X u ≤ subst Y u
  induction u with
  | nil => rfl
  | cons s u ih =>
    rw [subst_cons, subst_cons]
    cases s with
    | terminal a => exact mul_le_mul_right ih _
    | nonterminal A => exact mul_le_mul' (h A) ih

/-- `Language.subst` as a monoid homomorphism from sentential forms to languages. -/
def substHom (X : N → Language T) : FreeMonoid (Symbol T N) →* Language T :=
  FreeMonoid.lift (Symbol.elim (fun a ↦ {[a]}) X)

theorem substHom_apply (u : FreeMonoid (Symbol T N)) : substHom X u = subst X u.toList :=
  FreeMonoid.lift_apply _ _

end Language

namespace ContextFreeGrammar

open Language

variable {T : Type*} (g : ContextFreeGrammar T)

/-- The language of the words that the sentential form `u` derives. -/
def languageFrom (u : List (Symbol T g.NT)) : Language T :=
  {w | g.Derives u (w.map terminal)}

variable {g} in
theorem mem_languageFrom {u : List (Symbol T g.NT)} {w : List T} :
    w ∈ g.languageFrom u ↔ g.Derives u (w.map terminal) :=
  Iff.rfl

theorem languageFrom_initial : g.languageFrom [nonterminal g.initial] = g.language :=
  rfl

theorem mem_languageFrom_map_terminal (w : List T) : w ∈ g.languageFrom (w.map terminal) :=
  Derives.refl _

@[simp] theorem languageFrom_map_terminal (x : List T) : g.languageFrom (x.map terminal) = {x} := by
  ext w
  exact ⟨fun h ↦ List.map_injective_iff.2 (fun _ _ ↦ terminal.inj) h.eq_of_map_terminal,
    fun h ↦ h ▸ .refl _⟩

@[simp] theorem languageFrom_nil : g.languageFrom [] = 1 :=
  g.languageFrom_map_terminal []

variable {g} in
theorem append_mem_languageFrom {u v : List (Symbol T g.NT)} {w₁ w₂ : List T}
    (h₁ : w₁ ∈ g.languageFrom u) (h₂ : w₂ ∈ g.languageFrom v) :
    w₁ ++ w₂ ∈ g.languageFrom (u ++ v) := by
  rw [mem_languageFrom, List.map_append]
  exact (Derives.append_right h₁ v).trans (Derives.append_left h₂ _)

theorem languageFrom_append (u v : List (Symbol T g.NT)) :
    g.languageFrom (u ++ v) = g.languageFrom u * g.languageFrom v := by
  ext w
  refine ⟨fun h ↦ ?_, fun ⟨_, h₁, _, h₂, h⟩ ↦ h ▸ append_mem_languageFrom h₁ h₂⟩
  obtain ⟨_, _, hv, h₁, h₂⟩ := Derives.append_split h
  obtain ⟨w₁, w₂, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp hv
  exact ⟨w₁, h₁, w₂, h₂, rfl⟩

@[simp] theorem languageFrom_terminal (a : T) : g.languageFrom [terminal a] = {[a]} :=
  g.languageFrom_map_terminal [a]

/-- `ContextFreeGrammar.languageFrom` as a monoid homomorphism from sentential forms to
languages. -/
def languageFromHom : FreeMonoid (Symbol T g.NT) →* Language T where
  toFun u := g.languageFrom u.toList
  map_one' := g.languageFrom_nil
  map_mul' u v := g.languageFrom_append u.toList v.toList

theorem languageFromHom_apply (u : FreeMonoid (Symbol T g.NT)) :
    g.languageFromHom u = g.languageFrom u.toList :=
  rfl

variable {g} in
/-- A sentential form derives every word that a form it derives does. -/
theorem Derives.languageFrom_le {u v : List (Symbol T g.NT)} (h : g.Derives u v) :
    g.languageFrom v ≤ g.languageFrom u :=
  fun _ hw ↦ h.trans hw

/-- A sentential form derives the product of the languages that its symbols derive. -/
theorem languageFromHom_eq_substHom :
    g.languageFromHom = substHom fun A ↦ g.languageFrom [nonterminal A] :=
  FreeMonoid.hom_eq fun s ↦ by
    cases s <;> simp [languageFromHom_apply, substHom_apply]

theorem languageFrom_eq_subst (u : List (Symbol T g.NT)) :
    g.languageFrom u = subst (fun A ↦ g.languageFrom [nonterminal A]) u :=
  (DFunLike.congr_fun g.languageFromHom_eq_substHom (FreeMonoid.ofList u)).trans
    (substHom_apply _)

variable {g} in
/-- A word derived from the right-hand side of a rule is derived from its left-hand side. -/
theorem languageFrom_output_le {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    g.languageFrom r.output ≤ g.languageFrom [nonterminal r.input] :=
  (g.produces_input_output hr).single.languageFrom_le

/-- A nonterminal derives the words that the right-hand sides of its rules derive. -/
theorem languageFrom_nonterminal (A : g.NT) : g.languageFrom [nonterminal A] =
    ⨆ r ∈ g.rules, ⨆ _ : r.input = A, g.languageFrom r.output := by
  refine le_antisymm (fun w hw ↦ ?_)
    (iSup₂_le fun r hr ↦ iSup_le fun h ↦ h ▸ languageFrom_output_le hr)
  rcases Derives.eq_or_head hw with h | ⟨_, hp, hd⟩
  · cases w <;> simp at h
  · obtain ⟨r, hr, rfl, rfl⟩ := produces_singleton_iff.mp hp
    exact mem_iSup.2 ⟨r, mem_iSup.2 ⟨hr, mem_iSup.2 ⟨rfl, hd⟩⟩⟩

/-- The equations of a grammar: `g.equations X A` is the union, over the rules `A → u` of `g`, of
the language of `u` with `X` substituted for its nonterminals. -/
def equations : (g.NT → Language T) →o (g.NT → Language T) where
  toFun X A := ⨆ r ∈ g.rules, ⨆ _ : r.input = A, subst X r.output
  monotone' _ _ h _ := iSup₂_mono fun r _ ↦ iSup_mono fun _ ↦ subst_mono r.output h

variable {g} {X : g.NT → Language T}

theorem mem_equations {A : g.NT} {w : List T} :
    w ∈ g.equations X A ↔ ∃ r ∈ g.rules, r.input = A ∧ w ∈ subst X r.output := by
  simp only [equations, OrderHom.coe_mk, mem_iSup, exists_prop]

theorem subst_output_le_equations {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    subst X r.output ≤ g.equations X r.input :=
  fun _ hw ↦ mem_equations.2 ⟨r, hr, rfl, hw⟩

/-- When `X` is closed under the equations of the grammar, substituting it shrinks along
productions. -/
theorem Produces.subst_le (h : g.equations X ≤ X) {u v : List (Symbol T g.NT)}
    (huv : g.Produces u v) : subst X v ≤ subst X u := by
  obtain ⟨r, hr, hrw⟩ := huv
  obtain ⟨p, q, rfl, rfl⟩ := hrw.exists_parts
  simp only [subst_append, subst_cons, subst_nil, mul_one, elim_nonterminal]
  exact mul_le_mul_left (mul_le_mul_right ((subst_output_le_equations hr).trans (h _)) _) _

/-- When `X` is closed under the equations of the grammar, substituting it shrinks along
derivations. -/
theorem Derives.subst_le (h : g.equations X ≤ X) {u v : List (Symbol T g.NT)}
    (huv : g.Derives u v) : subst X v ≤ subst X u := by
  induction huv with
  | refl => rfl
  | tail _ hp ih => exact (hp.subst_le h).trans ih

theorem languageFrom_le_subst (h : g.equations X ≤ X) (u : List (Symbol T g.NT)) :
    g.languageFrom u ≤ subst X u :=
  fun w hw ↦ Derives.subst_le h hw (by rw [subst_map_terminal]; rfl)

variable (g) in
/-- The languages derived from the nonterminals solve the equations of the grammar. -/
theorem equations_languageFrom :
    g.equations (fun A ↦ g.languageFrom [nonterminal A]) = fun A ↦ g.languageFrom [nonterminal A] :=
  funext fun A ↦ by simp only [equations, OrderHom.coe_mk, ← languageFrom_eq_subst,
    ← languageFrom_nonterminal]

variable (g) in
/-- The languages derived from the nonterminals of a grammar are the least assignment closed
under its equations. -/
theorem isLeast_languageFrom :
    IsLeast {X | g.equations X ≤ X} fun A ↦ g.languageFrom [nonterminal A] :=
  ⟨(g.equations_languageFrom).le, fun _ hX A ↦ by
    simpa using languageFrom_le_subst hX [nonterminal A]⟩

variable (g) in
/-- The languages derived from the nonterminals of a grammar are the least solution of its
equations. -/
theorem lfp_equations : g.equations.lfp = fun A ↦ g.languageFrom [nonterminal A] :=
  g.equations.isLeast_lfp_le.unique g.isLeast_languageFrom

/-- An assignment closed under the equations of a grammar contains its language. -/
theorem language_le_of_equations_le (h : g.equations X ≤ X) : g.language ≤ X g.initial :=
  g.isLeast_languageFrom.2 h g.initial

end ContextFreeGrammar
