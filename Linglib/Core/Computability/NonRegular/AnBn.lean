/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar.Regular
public import Linglib.Core.Computability.MyhillNerode
public import Mathlib.Order.Filter.Cofinite

/-!
# The language `{aⁿbⁿ | n ∈ ℕ}`

For letters `a` and `b`, we define `Language.anbn a b`, the language of the words `aⁿbⁿ` consisting
of `n` copies of `a` followed by `n` copies of `b`. It is the first of the languages that
[chomsky-1957] gives as not finite state.

A language that contains `aⁿbⁿ` for infinitely many `n`, and contains `aᵐbⁿ` only when `m = n`, is
not regular (`Language.not_isRegular_of_replicate_append_replicate_mem`): the left quotients by
those words `aⁿ` are pairwise distinct, since `bⁿ` is in the left quotient by `aᵐ` only when
`m = n`. For distinct letters this applies to `anbn a b` (`Language.not_isRegular_anbn`) and to the
language of the words with as many `a` as `b` (`Language.not_isRegular_setOf_count_eq`).

The grammar `ContextFreeGrammar.anbn a b` has the rules `S → a S b | ε`, so its equation is
`X = a X b + 1`. The language `anbn a b` is closed under that equation, and each `aⁿbⁿ` is derived
by induction on `n`, so the grammar generates `anbn a b` (`ContextFreeGrammar.language_anbn`),
which is therefore context-free. Hence, over a finite alphabet with two letters, the regular
languages are a proper subclass of the context-free languages
(`Language.setOf_isRegular_ssubset_setOf_isContextFree`).

## References

* [N. Chomsky, *Syntactic Structures* (1957)][chomsky-1957]
* [J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation* (2000)][hopcroft-motwani-ullman-2000]
-/

@[expose] public section

open List Symbol

variable {α β : Type*} {a b : α}

namespace Language

/-- The language `{aⁿbⁿ | n ∈ ℕ}` of the words consisting of `n` copies of the letter `a` followed
by `n` copies of the letter `b`. -/
def anbn (a b : α) : Language α := {w | ∃ n, replicate n a ++ replicate n b = w}

theorem mem_anbn {w : List α} : w ∈ anbn a b ↔ ∃ n, replicate n a ++ replicate n b = w :=
  Iff.rfl

theorem replicate_append_replicate_mem_anbn (n : ℕ) :
    replicate n a ++ replicate n b ∈ anbn a b :=
  ⟨n, rfl⟩

@[simp] theorem replicate_append_replicate_mem_anbn_iff (hab : a ≠ b) {m n : ℕ} :
    replicate m a ++ replicate n b ∈ anbn a b ↔ m = n := by
  refine ⟨fun ⟨k, hk⟩ ↦ ?_, fun h ↦ h ▸ replicate_append_replicate_mem_anbn m⟩
  classical
  have ha := congr(count a $hk)
  have hb := congr(count b $hk)
  simp [count_replicate, hab, hab.symm] at ha hb
  omega

@[simp] theorem map_anbn (f : α → β) (a b : α) : map f (anbn a b) = anbn (f a) (f b) := by
  ext w
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, by simp⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, ⟨n, rfl⟩, by simp⟩

@[simp] theorem reverse_anbn (a b : α) : (anbn a b).reverse = anbn b a := by
  ext w
  constructor
  · rintro ⟨n, h⟩
    exact ⟨n, by simpa using congr(List.reverse $h)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by simp⟩

variable {X : Language α}

/-- A language that contains `aⁿbⁿ` for infinitely many `n`, and contains `aᵐbⁿ` only when
`m = n`, is not regular: the left quotients by those `aⁿ` are pairwise distinct. -/
theorem not_isRegular_of_replicate_append_replicate_mem
    (hmem : ∃ᶠ n in Filter.atTop, replicate n a ++ replicate n b ∈ X)
    (heq : ∀ m n, replicate m a ++ replicate n b ∈ X → m = n) : ¬ X.IsRegular := fun h ↦
  Nat.frequently_atTop_iff_infinite.1 hmem <| Set.finite_coe_iff.1 <|
    h.finite_of_injective_leftQuotient
      (f := fun n : {n | replicate n a ++ replicate n b ∈ X} ↦ replicate n a) fun _ n hmn ↦
        Subtype.ext <| heq _ _ <| (Set.ext_iff.1 hmn (replicate n b)).2 n.2

/-- For distinct letters, `{aⁿbⁿ}` is not regular. -/
theorem not_isRegular_anbn (hab : a ≠ b) : ¬ (anbn a b).IsRegular :=
  not_isRegular_of_replicate_append_replicate_mem (.of_forall replicate_append_replicate_mem_anbn)
    fun _ _ ↦ (replicate_append_replicate_mem_anbn_iff hab).1

/-- For distinct letters, the language of the words with as many `a` as `b` is not regular. -/
theorem not_isRegular_setOf_count_eq [DecidableEq α] (hab : a ≠ b) :
    ¬ IsRegular {w : List α | w.count a = w.count b} :=
  not_isRegular_of_replicate_append_replicate_mem (a := a) (b := b)
    (.of_forall fun n ↦ show count a _ = count b _ by simp [count_replicate, hab, hab.symm])
    fun m n (h : count a _ = count b _) ↦ by simpa [count_replicate, hab, hab.symm] using h

end Language

namespace ContextFreeGrammar

/-- The grammar `S → a S b | ε`, with a single nonterminal. -/
def anbn (a b : α) : ContextFreeGrammar α where
  NT := Unit
  initial := ()
  rules := .cons ⟨(), [terminal a, nonterminal (), terminal b]⟩ {⟨(), []⟩} (by simp)

theorem mem_rules_anbn {r : ContextFreeRule α Unit} :
    r ∈ (anbn a b).rules ↔
      r = ⟨(), [terminal a, nonterminal (), terminal b]⟩ ∨ r = ⟨(), []⟩ := by
  unfold anbn; simp

theorem language_anbn : (anbn a b).language = Language.anbn a b := by
  refine le_antisymm
    (language_le_of_equations_le (X := fun _ ↦ Language.anbn a b) fun _ w hw ↦ ?_) ?_
  · obtain ⟨r, hr, -, hw⟩ := mem_equations.1 hw
    obtain rfl | rfl := mem_rules_anbn.1 hr
    · obtain ⟨_, rfl, _, ⟨_, ⟨n, rfl⟩, _, rfl, rfl⟩, rfl⟩ :
          w ∈ {[a]} * (Language.anbn a b * {[b]}) := by simpa using hw
      exact ⟨n + 1, by rw [replicate_succ, replicate_succ']; simp⟩
    · exact ⟨0, by simpa [eq_comm] using hw⟩
  · rintro _ ⟨n, rfl⟩
    induction n with
    | zero =>
      exact languageFrom_output_le (mem_rules_anbn.2 (.inr rfl))
        (mem_languageFrom_map_terminal _ [])
    | succ n ih =>
      refine languageFrom_output_le (mem_rules_anbn.2 (.inl rfl)) ?_
      rw [replicate_succ, replicate_succ']
      simpa using append_mem_languageFrom (mem_languageFrom_map_terminal (anbn a b) [a])
        (append_mem_languageFrom (u := [nonterminal ()]) ih (mem_languageFrom_map_terminal _ [b]))

end ContextFreeGrammar

theorem Language.isContextFree_anbn (a b : α) : (anbn a b).IsContextFree :=
  ⟨_, ContextFreeGrammar.language_anbn⟩

/-- Over a finite alphabet with two distinct letters `a` and `b`, the regular languages are a
proper subclass of the context-free languages, as `{aⁿbⁿ}` witnesses. -/
theorem Language.setOf_isRegular_ssubset_setOf_isContextFree [Finite α] [Nontrivial α] :
    {L : Language α | L.IsRegular} ⊂ {L | L.IsContextFree} := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  exact (Set.ssubset_iff_of_subset fun _ ↦ Language.IsRegular.isContextFree).2
    ⟨Language.anbn a b, Language.isContextFree_anbn a b, Language.not_isRegular_anbn hab⟩
