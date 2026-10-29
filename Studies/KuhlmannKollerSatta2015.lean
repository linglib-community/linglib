module

public import Linglib.Syntax.CCG.Grammar
public import Linglib.Core.Computability.NonContextFree.AnBnCn
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.List.Basic

/-!
# Kuhlmann, Koller and Satta (2015): Lexicalization and Generative Power in CCG

This file formalizes Example 2 of [kuhlmann-koller-satta-2015], the grammar `G₁` in the
formalism of [vijay-shanker-weir-1994] and [weir-joshi-1988] whose rules of application and
of composition of degree at most 2 are restricted to primary inputs with target `S`, and
proves that its language is `aⁿbⁿcⁿ` without the empty word (`language_eq_anbncn_sub_one`).
The completeness half follows the paper's derivation: the `b`s are composed into a cluster
`S/C/…/C` (`cluster_derives`), and each `C` argument is peeled off by crossed-composing a `c`
and backward-applying an `a` (`peel_derives`). The soundness half is an induction on
derivability showing that every derivable pair has one of the shapes that construction
produces (`reachable_of_derives`). The language is therefore not context-free
(`not_isContextFree_language`), the fact the proof of Theorem 3 invokes.

The paper's results turn on two properties of rule restrictions, which are stated here for
the substrate's rule systems: prefix-closedness (Definition 2) and the absence of target
restrictions (Definition 3). Every target-restricted rule system is prefix-closed, so the rule
system of `G₁` is (Example 6), but it is not without target restrictions (Example 8). This is
the configuration the paper's Theorems 2 and 3 separate: prefix-closed grammars with target
restrictions are weakly equivalent to tree-adjoining grammar, and without them they cannot
generate `aⁿbⁿcⁿ`.

## Implementation notes

The atoms `A`, `B`, `C`, `S` and the letters `a`, `b`, `c` are the study's own types, since
`CCG.Grammar` is parameterized over both. The lexical entry for `c` is `C\A`, the direction the
paper's derivation of `aⁿbⁿcⁿ` requires. The language is stated against `Language.anbncn`, and
the empty word drops out because no CCG grammar derives it (`CCG.Grammar.Derives.ne_nil`).
Definition 3 quantifies over the categories of the grammar, which are here all of `Cat Atom`,
the categories over the grammar's atoms.

## TODO

* Theorems 1–4 and the main lemma (a Parikh-equivalent context-free sublanguage for every
  prefix-closed grammar without target restrictions) are not formalized.

## References

* [kuhlmann-koller-satta-2015]
* [vijay-shanker-weir-1994]
* [weir-joshi-1988]
* [schiffer-maletti-2021]
-/

@[expose] public section

namespace KuhlmannKollerSatta2015

open CCG

/-- The atomic categories of the paper's Example 2 grammar. -/
inductive Atom where
  | A
  | B
  | C
  /-- The distinguished atom the target restriction is stated at. -/
  | S
  deriving Repr, DecidableEq

abbrev Acat : Cat Atom := .atom .A
abbrev Bcat : Cat Atom := .atom .B
abbrev Ccat : Cat Atom := .atom .C
abbrev Scat : Cat Atom := .atom .S

/-- The terminal letters of the paper's Example 2 grammar. -/
inductive Letter where
  | a
  | b
  | c
  deriving Repr, DecidableEq

/-- The grammar `G₁` of Example 2 has six lexical entries, its target restriction and start
at `S`, and degree bound 2, an instance of the ε-free degree-2 normal form of
[schiffer-maletti-2021]. -/
def exampleGrammar : Grammar Letter Atom :=
  .targetRestricted
    [(.a, Acat), (.c, Ccat \ Acat),
     (.b, (Scat / Ccat) / Bcat), (.b, (Bcat / Ccat) / Bcat),
     (.b, Scat / Ccat), (.b, Bcat / Ccat)]
    .S 2

/-- The cluster category `S/C/…/C` with `n` forward `C`-arguments. -/
def clusterCat : Nat → Cat Atom
  | 0 => Scat
  | n + 1 => (clusterCat n) / Ccat

@[simp] theorem target_clusterCat (n : Nat) : (clusterCat n).target = Atom.S := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [clusterCat] using ih

/-! ### The construction, as `Derives` inductions -/

theorem fc2Chain_derives (j : Nat) :
    exampleGrammar.Derives ((clusterCat (j + 1)).rslash .dot Bcat)
      (List.replicate (j + 1) .b) := by
  induction j with
  | zero => exact .lex (by decide)
  | succ j ih =>
      have h : exampleGrammar.Derives ((clusterCat (j + 2)).rslash .dot Bcat)
          (List.replicate (j + 1) .b ++ [.b]) :=
        .forward [⟨.right, .dot, Ccat⟩, ⟨.right, .dot, Bcat⟩] ih (.lex (by decide))
          ⟨by decide, by simp⟩
      simpa [List.replicate_succ'] using h

theorem cluster_derives : ∀ {n : Nat}, 1 ≤ n →
    exampleGrammar.Derives (clusterCat n) (List.replicate n .b)
  | 1, _ => .lex (by decide)
  | n + 2, _ => by
      have h : exampleGrammar.Derives (clusterCat (n + 2))
          (List.replicate (n + 1) .b ++ [.b]) :=
        .forward [⟨.right, .dot, Ccat⟩] (fc2Chain_derives n) (.lex (by decide))
          ⟨by decide, by simp⟩
      simpa [List.replicate_succ'] using h

private theorem replicate_cons_comm {α : Type*} (k : Nat) (a : α) (X : List α) :
    List.replicate k a ++ (a :: X) = a :: (List.replicate k a ++ X) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, List.cons_append, ih]

theorem peel_derives : ∀ (k : Nat) {w : List Letter},
    exampleGrammar.Derives (clusterCat k) w →
    exampleGrammar.Derives Scat
      (List.replicate k .a ++ w ++ List.replicate k .c)
  | 0, w, h => by simpa [clusterCat] using h
  | k + 1, w, h => by
      have hstep : exampleGrammar.Derives (clusterCat k) (.a :: (w ++ [.c])) :=
        .backward [] (.lex (c := Acat) (by decide))
          (.forward [⟨.left, .dot, Acat⟩] h (.lex (by decide)) ⟨by decide, by simp⟩)
          ⟨by decide, by simp⟩
      have hrec := peel_derives k hstep
      simpa [List.replicate_succ, List.cons_append, List.append_assoc,
        replicate_cons_comm] using hrec

/-! ### Soundness

The converse induction: every pair the grammar derives has one of the shapes of the
completeness construction, so the language contains nothing beyond `aⁿbⁿcⁿ`. -/

/-- The category/string pairs that `G₁` derives, namely the six lexical shapes, the degree-2
chain categories, the clusters wrapped by `i` peels, and the peel intermediates. -/
def Reachable : Cat Atom → List Letter → Prop := fun c w ↦
  (c = Acat ∧ w = [.a]) ∨
  (c = (Ccat \ Acat) ∧ w = [.c]) ∨
  (c = ((Bcat / Ccat) / Bcat) ∧ w = [.b]) ∨
  (c = (Bcat / Ccat) ∧ w = [.b]) ∨
  (∃ j : Nat, c = (clusterCat (j + 1)).rslash .dot Bcat ∧
    w = List.replicate (j + 1) .b) ∨
  (∃ k i : Nat, c = clusterCat k ∧
    w = List.replicate i .a ++ List.replicate (k + i) .b ++ List.replicate i .c) ∨
  (∃ k i : Nat, c = (clusterCat k).lslash .dot Acat ∧
    w = List.replicate i .a ++ List.replicate (k + 1 + i) .b ++
      List.replicate (i + 1) .c)

theorem reachable_of_derives {c : Cat Atom} {w : List Letter}
    (h : exampleGrammar.Derives c w) : Reachable c w := by
  induction h with
  | @lex w' c' hmem =>
    simp only [exampleGrammar, Grammar.targetRestricted, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨0, rfl, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨1, 0, rfl, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  | @forward x y m β u v _ _ hgate iha ihb =>
    obtain ⟨-, hx⟩ : _ ∧ x.target = .S := hgate
    rcases iha with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨j, h, rfl⟩ | ⟨_ | k, i, h, rfl⟩ |
      ⟨_, _, h, -⟩
    · cases h
    · cases h
    · cases h; simp at hx
    · cases h; simp at hx
    · -- the chain `(S/Cʲ⁺¹)/B` composes with `(B/C)/B` into the next chain, or with `B/C`
      cases h
      rcases ihb with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨_, h, -⟩ | ⟨_, _, h, -⟩ |
        ⟨_, _, h, -⟩ <;> simp [Cat.atom_pushArgs_eq_iff] at h <;> subst h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨j + 1, rfl, by simp [List.replicate_succ']⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨j + 2, 0, rfl, by simp [List.replicate_succ']⟩)))))
    · cases h
    · -- the cluster `S/Cᵏ⁺¹` crossed-composes with `C\A` into a peel intermediate
      cases h
      rcases ihb with ⟨h, -⟩ | ⟨h, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨_, h, -⟩ | ⟨_, _, h, -⟩ |
        ⟨_, _, h, -⟩ <;> simp [Cat.atom_pushArgs_eq_iff] at h
      subst h
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, i, rfl, ?_⟩)))))
      simp [show k + 1 + i = k + i + 1 by omega, List.replicate_succ']
    · cases h
  | @backward x y m β u v _ _ hgate iha ihb =>
    obtain ⟨-, hx⟩ : _ ∧ x.target = .S := hgate
    rcases ihb with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨_, h, -⟩ | ⟨_ | _, _, h, -⟩ |
      ⟨k, i, h, rfl⟩
    · cases h
    · cases h; simp at hx
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · -- an `a` backward-applies to a peel intermediate, giving the next cluster
      cases h
      rcases iha with ⟨h, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨_, h, -⟩ | ⟨_, _, h, -⟩ |
        ⟨_, _, h, -⟩ <;> simp [Cat.atom_pushArgs_eq_iff] at h
      subst h
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, i + 1, rfl, ?_⟩)))))
      simp [show k + (i + 1) = k + 1 + i by omega, List.replicate_succ]

/-! ### Rule restrictions (§3.1, §3.3) -/

/-- A rule system is prefix-closed (Definition 2) when every permitted instance `X/Y Yβ ⇒ Xβ`
of composition stays permitted for every prefix `β'` of the argument sequence `β`, that is, with
the outermost arguments of the secondary input already consumed, at the lowered degree. -/
def PrefixClosed {α : Type*} (R : RuleSystem α) : Prop :=
  ∀ x a (β β' : List (Cat.Arg α)), β' <+: β → R x a β → R x a β'

/-- A rule system is without target restrictions (Definition 3) when every permitted instance
`X/Y Yβ ⇒ Xβ` stays permitted under any change of the primary input's result category `X`. -/
def WithoutTargetRestrictions {α : Type*} (R : RuleSystem α) : Prop :=
  ∀ x x' a (β : List (Cat.Arg α)), R x a β → R x' a β

-- Example 2: the six rules of `G₁`, each restricted to primary inputs with target `S`
example : exampleGrammar.rules = RuleSystem.ofRestrictedRules ((List.range 3).flatMap fun n ↦
    [⟨.right, n, {.S}, Set.univ⟩, ⟨.left, n, {.S}, Set.univ⟩]) :=
  RuleSystem.targetRestricted_eq_ofRestrictedRules _ _

theorem targetRestricted_prefixClosed {α : Type*} (s : α) (d : ℕ) :
    PrefixClosed (RuleSystem.targetRestricted s d) :=
  fun _ _ _ _ hβ h ↦ ⟨hβ.length_le.trans h.1, h.2⟩

-- Example 6
theorem exampleGrammar_prefixClosed : PrefixClosed exampleGrammar.rules :=
  targetRestricted_prefixClosed _ _

-- Example 8
theorem exampleGrammar_not_withoutTargetRestrictions :
    ¬ WithoutTargetRestrictions exampleGrammar.rules :=
  fun h ↦ absurd (h Scat Bcat ⟨.right, .dot, Ccat⟩ [] ⟨Nat.zero_le _, rfl⟩).2 (by decide)

/-! ### Generative-capacity result -/

-- Example 2 [kuhlmann-koller-satta-2015]
theorem anbncn_sub_one_subset_language :
    Language.anbncn Letter.a .b .c - 1 ≤ exampleGrammar.language := by
  rintro _ ⟨⟨n, rfl⟩, hn⟩
  refine peel_derives n (cluster_derives (Nat.one_le_iff_ne_zero.2 ?_))
  rintro rfl
  exact hn rfl

theorem language_subset_anbncn : exampleGrammar.language ≤ Language.anbncn .a .b .c := by
  rintro w hw
  rcases reachable_of_derives hw with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ |
    ⟨j, h, _⟩ | ⟨_ | k, i, h, rfl⟩ | ⟨k, i, h, _⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by simp [clusterCat])
  · exact ⟨i, by simp⟩
  · exact absurd h (by simp [clusterCat])
  · exact absurd h (by simp)

/-- The language of `G₁` is `aⁿbⁿcⁿ` without the empty word ([kuhlmann-koller-satta-2015],
Example 2). -/
theorem language_eq_anbncn_sub_one :
    exampleGrammar.language = Language.anbncn .a .b .c - 1 :=
  le_antisymm
    (fun _ hw ↦ ⟨language_subset_anbncn hw, mt (Language.mem_one _).1 (Grammar.Derives.ne_nil hw)⟩)
    anbncn_sub_one_subset_language

/-- The language of `G₁` is not context-free, a fact the proof of Theorem 3 of
[kuhlmann-koller-satta-2015] invokes without proof (p. 202). -/
theorem not_isContextFree_language : ¬ exampleGrammar.language.IsContextFree := by
  refine Language.not_isContextFree_of_replicate_mem_of_count_eq (a := Letter.a) (b := .b)
    (c := .c) (by decide) (Filter.frequently_atTop.2 fun m ↦
      ⟨m + 1, by omega, anbncn_sub_one_subset_language
        ((Language.mem_sub _ _ _).2 ⟨⟨m + 1, rfl⟩, by simp⟩)⟩) ?_
  intro w hw
  obtain ⟨n, rfl⟩ := language_subset_anbncn hw
  simp [List.count_replicate]

end KuhlmannKollerSatta2015
