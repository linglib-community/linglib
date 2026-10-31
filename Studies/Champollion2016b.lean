module

public import Linglib.Core.Order.UpperLower.Closure
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Reference.ChoiceFunction
public import Linglib.Semantics.Composition.Coordination
public import Linglib.Semantics.Composition.Tree
public import Linglib.Syntax.Command
public import Linglib.Fragments.English.Coordination
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Sups

/-!
# Champollion (2016): Ten Men and Women Got Married Today: Noun Coordination and the Intersective Theory of Conjunction

This file derives the collective readings of noun coordination from the intersective *and*, on
the paper's logical forms. A plurality is a set, a raised noun an upper set of pluralities, and
Minimization of the meet of two raised nouns keeps [the minimal elements of the set product of
their generators](##minimal_mem_inter_upperClosure_iff), the collective *and* of Heycock and
Zamparelli. With Choice Closure above Minimization, [*a doctor and lawyer met* holds of any
doctor–lawyer pair](##holds_lf56) and [*ten men and women got married* of ten-person man–woman
mixtures](##holds_lf81); above *no* it [gives a reading the constraint on its scope
excludes](##not_closureBelowNo_lf61). [*Or* is never collective](##minimal_mem_union_some_iff),
and the collective entry [overgenerates on conjuncts that are not upward
entailing](##sups_noMan_noWoman).

## Implementation notes

* A plurality is a `Set E` and a property of pluralities a `Set (Set E)`. The determiner *a*,
  which is Existential Raising, is `Quantifier.Det.some`, the Montague lift is
  `Quantifier.individual`, Distributive Choice Raising is the principal filter `Set.Ici`, and
  Predicate Distributivity is `𝒫 S \ {∅}`.
* The logical forms are trees interpreted by the composition engine under a typing of the
  indices. *And* and *or* are the English coordinators at the type of their coordinands, a trace
  of a choice-function index applied to a noun is the chosen individual or plurality, and Choice
  Closure binds the index by Predicate Abstraction. It ranges over `ChoiceFunction`, whose totality
  turns the definedness condition `N ≠ ∅` of Choice Raising into a hypothesis.
* Heycock and Zamparelli's common nouns denote sets of singletons. Their counterexamples are stated
  for the individuals those singletons contain, which the singleton map carries over since it
  preserves unions.

## Errata

* (83c) and the prose after it swap the Americans and Russians of (82a) and (83b).
* (99a) prints `MIN(ER(cat)) or MIN(ER(dog))` for the `MIN(ER(cat) or ER(dog))` of its prose and
  (99b). [The two logical forms agree](##holds_lf99Printed_iff), so the slip is harmless.
* (95b) and (96b) are equivalent only when both nouns are nonempty: without dogs, (95b) holds
  vacuously while (96b) still requires every cat to be licensed.

## TODO

The split scope of indefinite numerals and Winter's pair semantics are not formalized.

## References

* [champollion-2016b]
* [partee-rooth-1983]
* [winter-2001b]
* [heycock-zamparelli-2005]
* [bergmann-1982]
-/

@[expose] public section

namespace Champollion2016b

open Quantifier Set SetFamily

variable {α E : Type*}

/-- **Determiner Fitting** (92) applies a determiner of individuals to the union of a property
of pluralities and to the union of its meet with the scope. -/
def determinerFitting (D : Det E) (A B : Set (Set E)) : Prop := D (⋃₀ A) (⋃₀ (A ∩ B))

/-! ### Raised nouns and Minimization -/

-- (12), (13)
theorem setOf_some_eq_upperClosure (N : Set α) :
    {P | Det.some N P} = upperClosure ((fun x ↦ ({x} : Set α)) '' N) := by
  ext P; simp [Det.some, Set.Nonempty]

theorem setOf_some_union (N N' : Set α) :
    {P | Det.some (N ∪ N') P} = {P | Det.some N P} ∪ {P | Det.some N' P} := by
  ext P; simp [Det.some, union_inter_distrib_right, union_nonempty]

theorem setOf_individual (x : E) : {P : Set E | individual x P} = Ici {x} := by
  ext P; exact (singleton_subset_iff (a := x) (s := P)).symm

-- (78), (79)
theorem Ici_eq_setOf_mem_powerset {M : Set E} (h : M.Nonempty) :
    Ici M = {P | M ∈ 𝒫 P \ {∅}} := by
  ext P; exact (and_iff_left h.ne_empty).symm

theorem image_singleton_sups (N N' : Set E) :
    (fun x ↦ ({x} : Set E)) '' N ⊻ (fun x ↦ ({x} : Set E)) '' N' =
      {P | ∃ x ∈ N, ∃ y ∈ N', P = {x, y}} := by
  ext P
  simp only [mem_sups, mem_image]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩

/-- Minimization of the meet of two upper closures keeps the minimal elements of the set product
of their generators, the collective conjunction of Heycock and Zamparelli (101), p. 608. -/
theorem minimal_mem_inter_upperClosure_iff [SemilatticeSup α] {s t : Set α} {a : α} :
    Minimal (· ∈ (upperClosure s : Set α) ∩ upperClosure t) a ↔ Minimal (· ∈ s ⊻ t) a := by
  rw [← UpperSet.coe_sup, ← upperClosure_sups]
  exact minimal_mem_upperClosure_iff

-- (42)
theorem minimal_mem_some_iff {N P : Set E} :
    Minimal (· ∈ {Q | Det.some N Q}) P ↔ ∃ x ∈ N, P = {x} := by
  have hanti : IsAntichain (· ≤ ·) ((fun x ↦ ({x} : Set E)) '' N) := by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ hne hle
    exact hne (by rw [singleton_subset_singleton.mp hle])
  rw [setOf_some_eq_upperClosure]
  refine minimal_mem_upperClosure_iff.trans ?_
  rw [hanti.minimal_mem_iff]
  simp [eq_comm]

-- p. 580
theorem minimal_mem_inter_some_iff {N N' P : Set E} :
    Minimal (· ∈ {Q | Det.some N Q} ∩ {Q | Det.some N' Q}) P ↔
      (∃ x ∈ N ∩ N', P = {x}) ∨ ∃ x ∈ N \ N', ∃ y ∈ N' \ N, P = {x, y} := by
  rw [setOf_some_eq_upperClosure, setOf_some_eq_upperClosure, minimal_mem_inter_upperClosure_iff,
    image_singleton_sups]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨x, hx, y, hy, rfl⟩, hmin⟩
    by_cases hxN' : x ∈ N'
    · exact Or.inl ⟨x, ⟨hx, hxN'⟩, (hmin (y := {x}) ⟨x, hx, x, hxN', (pair_eq_singleton x).symm⟩
        (singleton_subset_iff.2 (mem_insert x _))).antisymm
        (singleton_subset_iff.2 (mem_insert x _))⟩
    by_cases hyN : y ∈ N
    · exact Or.inl ⟨y, ⟨hyN, hy⟩, (hmin (y := {y}) ⟨y, hyN, y, hy, (pair_eq_singleton y).symm⟩
        (singleton_subset_iff.2 (mem_insert_of_mem x rfl))).antisymm
        (singleton_subset_iff.2 (mem_insert_of_mem x rfl))⟩
    exact Or.inr ⟨x, ⟨hx, hxN'⟩, y, ⟨hy, hyN⟩, rfl⟩
  · rintro (⟨x, ⟨hx, hx'⟩, rfl⟩ | ⟨x, ⟨hx, hxN'⟩, y, ⟨hy, hyN⟩, rfl⟩)
    · refine ⟨⟨x, hx, x, hx', (pair_eq_singleton x).symm⟩, ?_⟩
      rintro _ ⟨a, -, b, -, rfl⟩ hle
      obtain rfl : a = x := hle (mem_insert a {b})
      exact singleton_subset_iff.2 (mem_insert a {b})
    · refine ⟨⟨x, hx, y, hy, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, b, hb, rfl⟩ hle
      obtain rfl : a = x := (hle (mem_insert a {b})).resolve_right fun h ↦ hyN (h ▸ ha)
      obtain rfl : b = y := (hle (mem_insert_of_mem a rfl)).resolve_left fun h ↦ hxN' (h ▸ hb)
      exact le_rfl

-- (10), (20)
theorem minimal_mem_inter_some_iff_of_disjoint {N N' P : Set E} (h : Disjoint N N') :
    Minimal (· ∈ {Q | Det.some N Q} ∩ {Q | Det.some N' Q}) P ↔ ∃ x ∈ N, ∃ y ∈ N', P = {x, y} := by
  rw [minimal_mem_inter_some_iff, disjoint_iff_inter_eq_empty.mp h, sdiff_eq_left.mpr h,
    sdiff_eq_left.mpr h.symm]
  simp

-- (43)
theorem minimal_mem_individual_inter_some_iff {N P : Set E} {j : E} (hj : j ∈ N) :
    Minimal (· ∈ {Q | individual j Q} ∩ {Q | Det.some N Q}) P ↔ P = {j} := by
  have : {Q : Set E | individual j Q} = {Q | Det.some {j} Q} := by
    ext Q; simp [individual, Det.some]
  rw [this, minimal_mem_inter_some_iff]
  simp [hj]

theorem minimal_mem_Ici_inter_Ici_iff [Lattice α] {a b c : α} :
    Minimal (· ∈ Ici a ∩ Ici b) c ↔ c = a ⊔ b := by
  rw [Ici_inter_Ici]
  exact minimal_ge_iff

-- (40)
theorem minimal_mem_inter_individual_iff {x y : E} {P : Set E} :
    Minimal (· ∈ {Q | individual x Q} ∩ {Q | individual y Q}) P ↔ P = {x, y} := by
  rw [setOf_individual, setOf_individual, minimal_mem_Ici_inter_Ici_iff, ← singleton_union]
  rfl

-- (57)
theorem exists₂_minimal_mem_inter_individual_iff {N N' P : Set E} (hN : N.Nonempty)
    (hN' : N'.Nonempty) :
    (∃ f₁ f₂ : ChoiceFunction E,
      Minimal (· ∈ {Q | individual (f₁ N) Q} ∩ {Q | individual (f₂ N') Q}) P) ↔
      ∃ x ∈ N, ∃ y ∈ N', P = {x, y} := by
  simp only [minimal_mem_inter_individual_iff]
  exact (ChoiceFunction.exists_apply_iff_some hN fun x ↦
    ∃ f₂ : ChoiceFunction E, P = {x, f₂ N'}).trans (exists_congr fun x ↦
      and_congr_right fun _ ↦ ChoiceFunction.exists_apply_iff_some hN' fun y ↦ P = {x, y})

/-! ### Plurals -/

-- p. 592
theorem mem_sups_powerset_iff {N N' P : Set E} :
    P ∈ (𝒫 N \ {∅}) ⊻ (𝒫 N' \ {∅}) ↔
      P ⊆ N ∪ N' ∧ (P ∩ N).Nonempty ∧ (P ∩ N').Nonempty := by
  simp only [mem_sups, mem_sdiff, mem_powerset_iff, mem_singleton_iff,
    ← not_nonempty_iff_eq_empty, not_not]
  constructor
  · rintro ⟨M, ⟨hMN, x, hx⟩, W, ⟨hWN', y, hy⟩, rfl⟩
    exact ⟨union_subset_union hMN hWN', ⟨x, Or.inl hx, hMN hx⟩, ⟨y, Or.inr hy, hWN' hy⟩⟩
  · rintro ⟨hP, hPN, hPN'⟩
    refine ⟨P ∩ N, ⟨inter_subset_right, hPN⟩, P ∩ N', ⟨inter_subset_right, hPN'⟩, ?_⟩
    exact (inter_union_distrib_left P N N').symm.trans (inter_eq_left.2 hP)

-- (68), p. 592: determiner doubling counts `n` of each noun
theorem ncard_inter_union_of_exactly {N N' P : Set E} (h : Disjoint N N') {n : ℕ} (hn : n ≠ 0)
    (hP : Det.exactly n N P ∧ Det.exactly n N' P) : (P ∩ (N ∪ N')).ncard = n + n := by
  have h₁ : (P ∩ N).ncard = n := by rw [inter_comm]; exact hP.1
  have h₂ : (P ∩ N').ncard = n := by rw [inter_comm]; exact hP.2
  rw [inter_union_distrib_left, ncard_union_eq (h.mono inter_subset_right inter_subset_right)
    (finite_of_ncard_ne_zero (h₁ ▸ hn)) (finite_of_ncard_ne_zero (h₂ ▸ hn)), h₁, h₂]

-- (75), (76)
theorem ncard_le_two_of_minimal_mem_inter_some {N N' P : Set E}
    (hP : Minimal (· ∈ {Q | Det.some N Q} ∩ {Q | Det.some N' Q}) P) : P.ncard ≤ 2 := by
  rcases minimal_mem_inter_some_iff.1 hP with ⟨x, -, rfl⟩ | ⟨x, -, y, -, rfl⟩
  · simp
  · exact (ncard_insert_le x {y}).trans (by simp)

-- (80)
theorem exists₂_minimal_mem_Ici_inter_Ici_iff {N N' : Set (Set E)} {P : Set E}
    (hN : N.Nonempty) (hN' : N'.Nonempty) :
    (∃ f₁ f₂ : ChoiceFunction (Set E), Minimal (· ∈ Ici (f₁ N) ∩ Ici (f₂ N')) P) ↔
      P ∈ N ⊻ N' := by
  simp only [minimal_mem_Ici_inter_Ici_iff, mem_sups]
  exact (ChoiceFunction.exists_apply_iff_some hN fun M ↦
    ∃ f₂ : ChoiceFunction (Set E), P = M ⊔ f₂ N').trans (exists_congr fun M ↦
      and_congr_right fun _ ↦ (ChoiceFunction.exists_apply_iff_some hN' fun W ↦
        P = M ⊔ W).trans (exists_congr fun _ ↦ and_congr_right fun _ ↦ eq_comm))

/-! ### *And*, *or* and Determiner Fitting -/

/-- Minimization after Existential Raising of a disjunction keeps only singletons, so *or* is
never collective (§6.2). -/
theorem minimal_mem_union_some_iff {N N' P : Set E} :
    Minimal (· ∈ {Q | Det.some N Q} ∪ {Q | Det.some N' Q}) P ↔ ∃ x ∈ N ∪ N', P = {x} := by
  rw [← setOf_some_union, minimal_mem_some_iff]

-- p. 604
theorem determinerFitting_some_iff {A B : Set (Set E)} (hB : ∅ ∉ B) :
    determinerFitting Det.some A B ↔ Det.some A B := by
  refine ⟨fun ⟨_, _, P, hP, _⟩ ↦ ⟨P, hP⟩, fun ⟨P, hA, hB'⟩ ↦ ?_⟩
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr fun h ↦ hB (h ▸ hB')
  exact ⟨x, ⟨P, hA, hx⟩, P, ⟨hA, hB'⟩, hx⟩

-- (94)
theorem determinerFitting_no_powerset_iff (N : Set E) (S : Set (Set E)) :
    determinerFitting Det.no (𝒫 N \ {∅}) S ↔ ¬ ∃ x ∈ N, ∃ P ∈ S, x ∈ P ∧ P ⊆ N := by
  refine ⟨fun h ⟨x, hx, P, hPS, hxP, hPN⟩ ↦ h ⟨{x}, ⟨singleton_subset_iff.2 hx,
    (singleton_nonempty x).ne_empty⟩, mem_singleton x⟩ ⟨P, ⟨⟨hPN, Set.Nonempty.ne_empty ⟨x, hxP⟩⟩,
    hPS⟩, hxP⟩, fun h x _ ⟨P, ⟨⟨hPN, _⟩, hPS⟩, hxP⟩ ↦ h ⟨x, hPN hxP, P, hPS, hxP, hPN⟩⟩

-- (95b), (96b)
theorem determinerFitting_every_pairs_iff {N N' : Set E} (hN : N.Nonempty) (hN' : N'.Nonempty)
    (V : Set E) : determinerFitting Det.every {P | ∃ x ∈ N, ∃ y ∈ N', P = {x, y}} (𝒫 V \ {∅}) ↔
      Det.every (N ∪ N') V := by
  obtain ⟨x₀, hx₀⟩ := hN
  obtain ⟨y₀, hy₀⟩ := hN'
  refine ⟨fun hD z hz ↦ ?_, fun hS z ⟨_, ⟨x, hx, y, hy, rfl⟩, hz⟩ ↦ ⟨_, ⟨⟨x, hx, y, hy, rfl⟩,
    insert_subset (hS (Or.inl hx)) (singleton_subset_iff.2 (hS (Or.inr hy))),
    (insert_nonempty x _).ne_empty⟩, hz⟩⟩
  have hz' : z ∈ ⋃₀ {P | ∃ x ∈ N, ∃ y ∈ N', P = {x, y}} := by
    rcases hz with hz | hz
    exacts [⟨_, ⟨z, hz, y₀, hy₀, rfl⟩, mem_insert z _⟩,
      ⟨_, ⟨x₀, hx₀, z, hz, rfl⟩, mem_insert_of_mem x₀ rfl⟩]
  obtain ⟨_, ⟨-, hP, -⟩, hzP⟩ := hD hz'
  exact hP hzP

/- Without dogs, (95b) holds whatever is licensed. -/
example (N V : Set E) :
    determinerFitting Det.every {P | ∃ x ∈ N, ∃ y ∈ (∅ : Set E), P = {x, y}} (𝒫 V \ {∅}) := by
  rintro z ⟨_, ⟨_, -, _, hy, -⟩, -⟩
  exact hy.elim

-- (99b)–(99e)
theorem determinerFitting_every_singletons_iff (M V : Set E) :
    determinerFitting Det.every {P | ∃ x ∈ M, P = {x}} (𝒫 V \ {∅}) ↔ Det.every M V := by
  refine ⟨fun hD z hz ↦ ?_, fun hS z ⟨_, ⟨x, hx, rfl⟩, hz⟩ ↦ ⟨{x}, ⟨⟨x, hx, rfl⟩,
    singleton_subset_iff.2 (hS hx), (singleton_nonempty x).ne_empty⟩, hz⟩⟩
  obtain ⟨_, ⟨-, hP, -⟩, hzP⟩ := hD ⟨{z}, ⟨z, hz, rfl⟩, mem_singleton z⟩
  exact hP hzP

-- (97b)
theorem determinerFitting_some_pairs_iff (N N' V : Set E) :
    determinerFitting Det.some {P | ∃ x ∈ N, ∃ y ∈ N', P = {x, y}} (𝒫 V \ {∅}) ↔
      Det.some N V ∧ Det.some N' V := by
  rw [determinerFitting_some_iff fun h ↦ h.2 rfl]
  constructor
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, hV, -⟩
    exact ⟨⟨x, hx, hV (mem_insert x _)⟩, y, hy, hV (mem_insert_of_mem x rfl)⟩
  · rintro ⟨⟨x, hx, hxV⟩, y, hy, hyV⟩
    exact ⟨_, ⟨x, hx, y, hy, rfl⟩, insert_subset hxV (singleton_subset_iff.2 hyV),
      (insert_nonempty x _).ne_empty⟩

/-! ### Logical forms

The composition engine interprets the paper's logical forms, and the theorems below give the
truth conditions of each. -/

section LogicalForms

open Montague PhraseStructure Tree English.Coordination

variable {E : Type} {N N' V : Set E} {R S : Set (Set E)}

/-- The words of the logical forms: two nouns, a predicate of individuals, a relative clause and
a verb phrase that are predicates of pluralities, the numerals, the determiners and coordinators,
and the silent operators. A word the paper uses at the types of individuals and of pluralities
has one entry for each. -/
inductive Word where
  | noun₁ | noun₂ | atom | relative | vp
  | numeral (n : ℕ)
  | a | aPlural | noPlural | every | dfit
  | and | or | orNoun
  | min | cr | dcr | pdist
  | choiceClosure | choiceClosureSentence | choiceClosurePlural | choiceClosurePluralSentence
  deriving DecidableEq

/-- The type of an index: `1` and `2` range over choice functions on individuals, the others over
choice functions on pluralities. -/
def indexTy (n : ℕ) : Ty := if n ≤ 2 then (.e ⇒ .t) ⇒ .e else ((.e ⇒ .t) ⇒ .t) ⇒ .e ⇒ .t

/-- The denotations, over two nouns `N`, `N'`, a predicate `V` of individuals and predicates `R`
and `S` of pluralities: the numerals (70), *a* (23) at individuals and at pluralities, Determiner
Fitting (92), Minimization (19), Choice Raising (46), Distributive Choice Raising (78), Predicate
Distributivity (27), and Choice Closure (49), (50) over choice functions. -/
def lex (N N' V : Set E) (R S : Set (Set E)) : Word → Option (Denotation E Unit)
  | .noun₁ => some ⟨.e ⇒ .t, N⟩
  | .noun₂ => some ⟨.e ⇒ .t, N'⟩
  | .atom => some ⟨.e ⇒ .t, V⟩
  | .relative => some ⟨(.e ⇒ .t) ⇒ .t, R⟩
  | .vp => some ⟨(.e ⇒ .t) ⇒ .t, S⟩
  | .numeral n => some ⟨(.e ⇒ .t) ⇒ .t, {P : Set E | P.ncard = n}⟩
  | .a => some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, fun (A B : Set E) ↦ Det.some A B⟩
  | .aPlural => some ⟨((.e ⇒ .t) ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t) ⇒ .t,
      fun (A B : Set (Set E)) ↦ Det.some A B⟩
  | .noPlural => some ⟨((.e ⇒ .t) ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t) ⇒ .t,
      fun (A B : Set (Set E)) ↦ Det.no A B⟩
  | .every => some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, fun (A B : Set E) ↦ Det.every A B⟩
  | .dfit => some ⟨((.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t) ⇒ .t,
      fun (D : Det E) (A B : Set (Set E)) ↦ determinerFitting D A B⟩
  | .and => some (and_.reading ((.e ⇒ .t) ⇒ .t) trivial)
  | .or => some (or_.reading ((.e ⇒ .t) ⇒ .t) trivial)
  | .orNoun => some (or_.reading (.e ⇒ .t) trivial)
  | .min => some ⟨((.e ⇒ .t) ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t,
      fun (Q : Set (Set E)) (P : Set E) ↦ Minimal (· ∈ Q) P⟩
  | .cr => some ⟨((.e ⇒ .t) ⇒ .e) ⇒ (.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t,
      fun (f : Set E → E) (N P : Set E) ↦ individual (f N) P⟩
  | .dcr => some ⟨(((.e ⇒ .t) ⇒ .t) ⇒ .e ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t,
      fun (f : Set (Set E) → Set E) (N : Set (Set E)) (P : Set E) ↦ f N ⊆ P⟩
  | .pdist => some ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, fun (P : Set E) ↦ (𝒫 P \ {∅} : Set (Set E))⟩
  | .choiceClosure => some ⟨(((.e ⇒ .t) ⇒ .e) ⇒ (.e ⇒ .t) ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t,
      fun (A : (Set E → E) → Set E → Prop) (P : Set E) ↦ ∃ f : ChoiceFunction E, A f P⟩
  | .choiceClosureSentence => some ⟨(((.e ⇒ .t) ⇒ .e) ⇒ .t) ⇒ .t,
      fun (A : (Set E → E) → Prop) ↦ ∃ f : ChoiceFunction E, A f⟩
  | .choiceClosurePlural =>
      some ⟨((((.e ⇒ .t) ⇒ .t) ⇒ .e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t,
        fun (A : (Set (Set E) → Set E) → Set E → Prop) (P : Set E) ↦
          ∃ f : ChoiceFunction (Set E), A f P⟩
  | .choiceClosurePluralSentence => some ⟨((((.e ⇒ .t) ⇒ .t) ⇒ .e ⇒ .t) ⇒ .t) ⇒ .t,
      fun (A : (Set (Set E) → Set E) → Prop) ↦ ∃ f : ChoiceFunction (Set E), A f⟩

attribute [local simp] HoldsAtWith lex indexTy Coordinator.reading_of_conjunctive
  Coordinator.reading_of_disjunctive and_ or_

/-- `[[a noun₁] [c [a noun₂]]]`: Existential Raising of each noun, coordinated by `c`. -/
def raised (c : Word) : Tree Unit Word :=
  .bin (.bin (.leaf .a) (.leaf .noun₁)) (.bin (.leaf c) (.bin (.leaf .a) (.leaf .noun₂)))

/-- `[[CR t₁] noun₁] [and [[CR t₂] noun₂]]`. -/
def crAnd : Tree Unit Word :=
  .bin (.bin (.bin (.leaf .cr) (.tr 1)) (.leaf .noun₁))
    (.bin (.leaf .and) (.bin (.bin (.leaf .cr) (.tr 2)) (.leaf .noun₂)))

/-- `[[DCR t₃] X] [and [[DCR t₄] Y]]`. -/
def dcrAnd (X Y : Tree Unit Word) : Tree Unit Word :=
  .bin (.bin (.bin (.leaf .dcr) (.tr 3)) X) (.bin (.leaf .and) (.bin (.bin (.leaf .dcr) (.tr 4)) Y))

/-- `[PDIST w]`, the plural of `w` (72). -/
def plural (w : Word) : Tree Unit Word := .bin (.leaf .pdist) (.leaf w)

/-- `[[[DFIT D] X] [PDIST atom]]`. -/
def fitted (D : Word) (X : Tree Unit Word) : Tree Unit Word :=
  .bin (.bin (.bin (.leaf .dfit) (.leaf D)) X) (plural .atom)

/-- The LF (24) of the hydra *a man and woman who dated met*. -/
def lf24 : Tree Unit Word :=
  .bin (.bin (.leaf .aPlural) (.bin (.bin (.leaf .min) (raised .and)) (.leaf .relative)))
    (.leaf .vp)

/-- The LF (29) of *a man and woman had a beer*. -/
def lf29 : Tree Unit Word := .bin (.bin (.leaf .aPlural) (.bin (.leaf .min) (raised .and)))
  (plural .atom)

/-- `[∃₁ [λ₁ [∃₂ [λ₂ [MIN crAnd]]]]]`: both Choice Closures above Minimization. -/
def closedAbove : Tree Unit Word :=
  .bin (.leaf .choiceClosure) (.binder 1
    (.bin (.leaf .choiceClosure) (.binder 2 (.bin (.leaf .min) crAnd))))

/-- The LF (56) of *a doctor and lawyer met*. -/
def lf56 : Tree Unit Word := .bin (.bin (.leaf .aPlural) closedAbove) (.leaf .vp)

/-- *A doctor and lawyer met* with each Choice Closure directly above its Choice Raising. -/
def lfLocal : Tree Unit Word :=
  .bin (.bin (.leaf .aPlural) (.bin (.leaf .min)
    (.bin (.bin (.leaf .choiceClosure) (.binder 1 (.bin (.bin (.leaf .cr) (.tr 1)) (.leaf .noun₁))))
      (.bin (.leaf .and) (.bin (.leaf .choiceClosure)
        (.binder 2 (.bin (.bin (.leaf .cr) (.tr 2)) (.leaf .noun₂))))))))
    (.leaf .vp)

/-- The LF of (60a) *no man and woman have a right …*, with Choice Closure below *no*. -/
def lf60 : Tree Unit Word := .bin (.bin (.leaf .noPlural) closedAbove) (.leaf .vp)

/-- The LF (61), with Choice Closure above *no*. -/
def lf61 : Tree Unit Word :=
  .bin (.leaf .choiceClosureSentence) (.binder 1 (.bin (.leaf .choiceClosureSentence) (.binder 2
    (.bin (.bin (.leaf .noPlural) (.bin (.leaf .min) crAnd)) (.leaf .vp)))))

/-- The LF (81) of *ten men and women got married today*. -/
def lf81 : Tree Unit Word :=
  .bin (.bin (.leaf .aPlural) (.bin (.leaf (.numeral 10)) (.bin (.leaf .choiceClosurePlural)
    (.binder 3 (.bin (.leaf .choiceClosurePlural) (.binder 4
      (.bin (.leaf .min) (dcrAnd (plural .noun₁) (plural .noun₂))))))))) (.leaf .vp)

/-- The LF (83a) of *two Americans and three Russians made an excellent basketball team*. -/
def lf83 : Tree Unit Word :=
  .bin (.leaf .choiceClosurePluralSentence) (.binder 3 (.bin (.leaf .choiceClosurePluralSentence)
    (.binder 4 (.bin (.bin (.leaf .aPlural) (.bin (.leaf .min)
      (dcrAnd (.bin (.leaf (.numeral 2)) (plural .noun₁))
        (.bin (.leaf (.numeral 3)) (plural .noun₂))))) (.leaf .vp)))))

/-- The LF (95a) of *every cat and dog is licensed*. -/
def lf95 : Tree Unit Word := fitted .every (.bin (.leaf .min) (raised .and))

/-- The LF (96a) of *every cat or dog is licensed*. -/
def lf96 : Tree Unit Word :=
  .bin (.bin (.leaf .every) (.bin (.leaf .noun₁) (.bin (.leaf .orNoun) (.leaf .noun₂))))
    (.leaf .atom)

/-- The LF (97a) of *a cat and dog came running in*. -/
def lf97 : Tree Unit Word := fitted .a (.bin (.leaf .min) (raised .and))

/-- The LF (98a) of *a cat or dog came running in*. -/
def lf98 : Tree Unit Word :=
  .bin (.bin (.leaf .a) (.bin (.leaf .noun₁) (.bin (.leaf .orNoun) (.leaf .noun₂)))) (.leaf .atom)

/-- The LF of *every cat or dog is licensed* described in the prose and in (99b). -/
def lf99 : Tree Unit Word := fitted .every (.bin (.leaf .min) (raised .or))

/-- The LF as (99a) prints it, with Minimization under *or*. -/
def lf99Printed : Tree Unit Word :=
  fitted .every (.bin (.bin (.leaf .min) (.bin (.leaf .a) (.leaf .noun₁)))
    (.bin (.leaf .or) (.bin (.leaf .min) (.bin (.leaf .a) (.leaf .noun₂)))))

/-- No Choice Closure in `t` takes scope over *no*, the constraint the paper draws from (59) and
(60). -/
def ClosureBelowNo (t : Tree Unit Word) : Prop :=
  ∀ p ∈ t.positionedTerminals, ∀ q ∈ t.positionedTerminals,
    p.2.2 ∈ [.choiceClosure, .choiceClosureSentence, .choiceClosurePlural,
      .choiceClosurePluralSentence] → q.2.2 = .noPlural → ¬ t.CCommands p.1 q.1

instance : DecidablePred ClosureBelowNo := fun t ↦
  inferInstanceAs (Decidable (∀ p ∈ t.positionedTerminals, ∀ q ∈ t.positionedTerminals,
    p.2.2 ∈ [.choiceClosure, .choiceClosureSentence, .choiceClosurePlural,
      .choiceClosurePluralSentence] → q.2.2 = .noPlural → ¬ t.CCommands p.1 q.1))

variable (g : ∀ n, Ty.Domain E Unit (indexTy n))

set_option hygiene false in
/-- `⟦t⟧`: the logical form `t` holds in the model the variables `N N' V R S` give. -/
local notation "⟦" t "⟧" => HoldsAtWith indexTy (lex N N' V R S) g t

private theorem some_setOf_iff {φ : Set E → Prop} (h : ∀ P, φ P ↔ ∃ x ∈ N, ∃ y ∈ N', P = {x, y})
    (B : Set (Set E)) : Det.some {P | φ P} B ↔ ∃ x ∈ N, ∃ y ∈ N', {x, y} ∈ B := by
  simp only [Det.some, Set.Nonempty, mem_inter_iff, mem_ofPred_eq, h]
  constructor
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, hB⟩
    exact ⟨x, hx, y, hy, hB⟩
  · rintro ⟨x, hx, y, hy, hB⟩
    exact ⟨_, ⟨x, hx, y, hy, rfl⟩, hB⟩

private theorem determinerFitting_congr {D : Det E} {A A' : Set (Set E)} (h : ∀ P, P ∈ A ↔ P ∈ A')
    (B : Set (Set E)) : determinerFitting D A B ↔ determinerFitting D A' B := by
  rw [Set.ext h]

-- (21)–(24)
theorem holds_lf24 (h : Disjoint N N') : ⟦lf24⟧ ↔ ∃ x ∈ N, ∃ y ∈ N', {x, y} ∈ R ∧ {x, y} ∈ S := by
  simp [lf24, raised]
  constructor
  · rintro ⟨P, ⟨hP, hR⟩, hS⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := (minimal_mem_inter_some_iff_of_disjoint h).1 hP
    exact ⟨x, hx, y, hy, hR, hS⟩
  · rintro ⟨x, hx, y, hy, hR, hS⟩
    exact ⟨_, ⟨(minimal_mem_inter_some_iff_of_disjoint h).2 ⟨x, hx, y, hy, rfl⟩, hR⟩, hS⟩

-- (29)
theorem holds_lf29 (h : Disjoint N N') : ⟦lf29⟧ ↔ ∃ x ∈ N, ∃ y ∈ N', x ∈ V ∧ y ∈ V := by
  simp [lf29, raised, plural]
  refine (some_setOf_iff (fun _ ↦ minimal_mem_inter_some_iff_of_disjoint h) _).trans ?_
  simp [insert_subset_iff, ← nonempty_iff_ne_empty]

/-- With Choice Closure above Minimization, *a doctor and lawyer met* (56) holds when a doctor and
a lawyer met, whatever professions they share (58). -/
theorem holds_lf56 (hN : N.Nonempty) (hN' : N'.Nonempty) :
    ⟦lf56⟧ ↔ ∃ x ∈ N, ∃ y ∈ N', {x, y} ∈ S := by
  simp [lf56, closedAbove, crAnd]
  exact some_setOf_iff (fun _ ↦ exists₂_minimal_mem_inter_individual_iff hN hN') S

-- p. 587
theorem holds_lfLocal (hN : N.Nonempty) (hN' : N'.Nonempty) :
    ⟦lfLocal⟧ ↔ Det.some {P | Minimal (· ∈ {Q | Det.some N Q} ∩ {Q | Det.some N' Q}) P} S := by
  have h {N : Set E} (hN : N.Nonempty) :
      {Q | ∃ f : ChoiceFunction E, individual (f N) Q} = {Q | Det.some N Q} :=
    Set.ext fun Q ↦ ChoiceFunction.exists_apply_iff_some hN Q
  simp [lfLocal]
  show Det.some {P | Minimal (· ∈ {Q | ∃ f : ChoiceFunction E, individual (f N) Q} ∩
    {Q | ∃ f : ChoiceFunction E, individual (f N') Q}) P} S ↔ _
  rw [h hN, h hN']
  rfl

/- A doctor who is also a lawyer meets another lawyer: (56) holds and the LF with local Choice
Closure does not. -/
example {x y : E} (hx : x ∈ N ∩ N') (hy : y ∈ N') (hxy : x ≠ y) :
    HoldsAtWith indexTy (lex N N' V R {{x, y}}) g lf56 ∧
      ¬ HoldsAtWith indexTy (lex N N' V R {{x, y}}) g lfLocal := by
  refine ⟨(holds_lf56 g ⟨x, hx.1⟩ ⟨y, hy⟩).2 ⟨x, hx.1, y, hy, rfl⟩, fun h ↦ ?_⟩
  obtain ⟨P, hP, rfl⟩ := (holds_lfLocal g ⟨x, hx.1⟩ ⟨y, hy⟩).1 h
  rcases minimal_mem_inter_some_iff.1 hP with ⟨z, -, hz⟩ | ⟨z, ⟨-, hzN'⟩, w, -, hzw⟩
  · have hx' : x ∈ ({z} : Set E) := hz ▸ mem_insert x {y}
    have hy' : y ∈ ({z} : Set E) := hz ▸ mem_insert_of_mem x rfl
    exact hxy (hx'.trans hy'.symm)
  · have hz : z ∈ ({x, y} : Set E) := hzw ▸ mem_insert z {w}
    rcases hz with rfl | rfl
    exacts [hzN' hx.2, hzN' hy]

-- (60a)
theorem holds_lf60 (hN : N.Nonempty) (hN' : N'.Nonempty) :
    ⟦lf60⟧ ↔ ∀ x ∈ N, ∀ y ∈ N', {x, y} ∉ S := by
  simp [lf60, closedAbove, crAnd]
  exact Det.no_iff_not_some.trans <| (not_congr
    (some_setOf_iff (fun _ ↦ exists₂_minimal_mem_inter_individual_iff hN hN') S)).trans (by simp)

-- (60b), (61)
theorem holds_lf61 (hN : N.Nonempty) (hN' : N'.Nonempty) :
    ⟦lf61⟧ ↔ ∃ x ∈ N, ∃ y ∈ N', {x, y} ∉ S := by
  have h (a b : E) : Det.no {P | Minimal (· ∈ {Q | individual a Q} ∩ {Q | individual b Q}) P} S ↔
      {a, b} ∉ S := by
    rw [show {P | Minimal (· ∈ {Q | individual a Q} ∩ {Q | individual b Q}) P} = {{a, b}} from
      Set.ext fun _ ↦ minimal_mem_inter_individual_iff]
    simp [Det.no]
  simp [lf61, crAnd]
  constructor
  · rintro ⟨f₁, f₂, hS⟩
    exact ⟨f₁ N, f₁.apply_of_exists hN, f₂ N', f₂.apply_of_exists hN', (h _ _).1 hS⟩
  · rintro ⟨x, hx, y, hy, hS⟩
    obtain ⟨f₁, rfl⟩ := ChoiceFunction.exists_apply_eq hx
    obtain ⟨f₂, rfl⟩ := ChoiceFunction.exists_apply_eq hy
    exact ⟨f₁, f₂, (h _ _).2 hS⟩

-- p. 588
theorem closureBelowNo_lf60 : ClosureBelowNo lf60 := by decide

-- p. 588
theorem not_closureBelowNo_lf61 : ¬ ClosureBelowNo lf61 := by decide

/-- *Ten men and women got married today* (81) holds when ten people, at least one man and one
woman and nobody else, got married together. -/
theorem holds_lf81 (hN : N.Nonempty) (hN' : N'.Nonempty) :
    ⟦lf81⟧ ↔ ∃ P ∈ S, P.ncard = 10 ∧ P ⊆ N ∪ N' ∧ (P ∩ N).Nonempty ∧ (P ∩ N').Nonempty := by
  have hp (N : Set E) (hN : N.Nonempty) : (𝒫 N \ {∅} : Set (Set E)).Nonempty :=
    ⟨N, Subset.rfl, hN.ne_empty⟩
  have hmix (P : Set E) := exists₂_minimal_mem_Ici_inter_Ici_iff (P := P) (hp N hN) (hp N' hN')
  simp [lf81, dcrAnd, plural]
  constructor
  · rintro ⟨P, ⟨h10, hP⟩, hS⟩
    exact ⟨P, hS, h10, mem_sups_powerset_iff.1 ((hmix P).1 hP)⟩
  · rintro ⟨P, hS, h10, hP⟩
    exact ⟨P, ⟨h10, (hmix P).2 (mem_sups_powerset_iff.2 hP)⟩, hS⟩

-- (83)
theorem holds_lf83 (hN : ∃ A ⊆ N, A.ncard = 2) (hN' : ∃ B ⊆ N', B.ncard = 3) :
    ⟦lf83⟧ ↔ ∃ A ⊆ N, ∃ B ⊆ N', A.ncard = 2 ∧ B.ncard = 3 ∧ A ∪ B ∈ S := by
  have h (a b : Set E) : Det.some {P | Minimal (· ∈ Ici a ∩ Ici b) P} S ↔ a ∪ b ∈ S := by
    rw [show {P | Minimal (· ∈ Ici a ∩ Ici b) P} = {a ⊔ b} from
      Set.ext fun _ ↦ minimal_mem_Ici_inter_Ici_iff]
    simp [Det.some]
  have hX {N : Set E} {n : ℕ} (hN : ∃ A ⊆ N, A.ncard = n) (hn : n ≠ 0) :
      ({P : Set E | P.ncard = n} ∩ (𝒫 N \ {∅}) : Set (Set E)).Nonempty := by
    obtain ⟨A, hA, hAn⟩ := hN
    refine ⟨A, hAn, hA, fun h ↦ hn ?_⟩
    rw [← hAn, show A = ∅ from h, ncard_empty]
  let X (n : ℕ) (N : Set E) : Set (Set E) := {P : Set E | P.ncard = n} ∩ (𝒫 N \ {∅})
  simp [lf83, dcrAnd, plural]
  refine (exists₂_congr fun (f₁ f₂ : ChoiceFunction (Set E)) ↦
    h (f₁ (X 2 N)) (f₂ (X 3 N'))).trans ?_
  refine (ChoiceFunction.exists_apply_iff_some (hX hN two_ne_zero) fun M ↦
    ∃ f₂ : ChoiceFunction (Set E), M ∪ f₂ (X 3 N') ∈ S).trans ?_
  refine (exists_congr fun M ↦ and_congr_right fun _ ↦
    ChoiceFunction.exists_apply_iff_some (hX hN' three_ne_zero) fun W ↦ M ∪ W ∈ S).trans ?_
  constructor
  · rintro ⟨A, ⟨hA2, hAN, -⟩, B, ⟨hB3, hBN', -⟩, hS⟩
    exact ⟨A, hAN, B, hBN', hA2, hB3, hS⟩
  · rintro ⟨A, hAN, B, hBN', hA2, hB3, hS⟩
    refine ⟨A, ⟨hA2, hAN, fun h ↦ ?_⟩, B, ⟨hB3, hBN', fun h ↦ ?_⟩, hS⟩
    · rw [show A = ∅ from h, ncard_empty] at hA2
      exact two_ne_zero hA2.symm
    · rw [show B = ∅ from h, ncard_empty] at hB3
      exact three_ne_zero hB3.symm

-- (95)
theorem holds_lf95 (h : Disjoint N N') (hN : N.Nonempty) (hN' : N'.Nonempty) :
    ⟦lf95⟧ ↔ Det.every (N ∪ N') V := by
  simp [lf95, fitted, raised, plural]
  exact (determinerFitting_congr (fun _ ↦ minimal_mem_inter_some_iff_of_disjoint h) _).trans
    (determinerFitting_every_pairs_iff hN hN' V)

-- (96)
theorem holds_lf96 : ⟦lf96⟧ ↔ Det.every (N ∪ N') V := by
  simp [lf96]
  rfl

-- (95), (96): the universal half of Bergmann's puzzle
theorem holds_lf95_iff_holds_lf96 (h : Disjoint N N') (hN : N.Nonempty) (hN' : N'.Nonempty) :
    ⟦lf95⟧ ↔ ⟦lf96⟧ :=
  (holds_lf95 g h hN hN').trans (holds_lf96 g).symm

-- (97)
theorem holds_lf97 (h : Disjoint N N') : ⟦lf97⟧ ↔ Det.some N V ∧ Det.some N' V := by
  simp [lf97, fitted, raised, plural]
  exact (determinerFitting_congr (fun _ ↦ minimal_mem_inter_some_iff_of_disjoint h) _).trans
    (determinerFitting_some_pairs_iff N N' V)

-- (98)
theorem holds_lf98 : ⟦lf98⟧ ↔ Det.some (N ∪ N') V := by
  simp [lf98]
  rfl

/- A cat that came running in, and no dog that did: (98) holds and (97) does not. -/
example (h : Disjoint N N') {x : E} (hx : x ∈ N) (hxV : x ∈ V) (hN'V : Disjoint N' V) :
    ⟦lf98⟧ ∧ ¬ ⟦lf97⟧ := by
  rw [holds_lf98, holds_lf97 g h]
  exact ⟨⟨x, Or.inl hx, hxV⟩, fun ⟨_, y, hy, hyV⟩ ↦ disjoint_left.mp hN'V hy hyV⟩

-- (99)
theorem holds_lf99 : ⟦lf99⟧ ↔ Det.every (N ∪ N') V := by
  simp [lf99, fitted, raised, plural]
  exact (determinerFitting_congr (fun _ ↦ minimal_mem_union_some_iff) _).trans
    (determinerFitting_every_singletons_iff _ V)

-- (99a)
theorem holds_lf99Printed_iff : ⟦lf99Printed⟧ ↔ ⟦lf99⟧ := by
  rw [holds_lf99]
  simp [lf99Printed, fitted, plural]
  refine (determinerFitting_congr (fun P ↦ ?_) _).trans
    (determinerFitting_every_singletons_iff (N ∪ N') V)
  show Minimal (· ∈ {Q | Det.some N Q}) P ∨ Minimal (· ∈ {Q | Det.some N' Q}) P ↔ _
  rw [minimal_mem_some_iff, minimal_mem_some_iff]
  simp only [mem_ofPred_eq, mem_union, or_and_right, exists_or]

end LogicalForms

/-! ### The collective theory -/

-- (101)
theorem inter_subset_sups [Lattice α] (Q Q' : Set α) : Q ∩ Q' ⊆ Q ⊻ Q' :=
  fun a h ↦ ⟨a, h.1, a, h.2, sup_idem a⟩

-- p. 608
theorem sups_eq_inter [Lattice α] {Q Q' : Set α} (hQ : IsUpperSet Q) (hQ' : IsUpperSet Q') :
    Q ⊻ Q' = Q ∩ Q' := by
  refine Subset.antisymm ?_ (inter_subset_sups Q Q')
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact ⟨hQ le_sup_left ha, hQ' le_sup_right hb⟩

-- (102), (20)
theorem sups_setOf_ncard_eq_one {N N' : Set E} (h : Disjoint N N') :
    {A | A.ncard = 1 ∧ A ⊆ N} ⊻ {B | B.ncard = 1 ∧ B ⊆ N'} =
      {P | Minimal (· ∈ {Q | Det.some N Q} ∩ {Q | Det.some N' Q}) P} := by
  have hsing (N : Set E) : {A | A.ncard = 1 ∧ A ⊆ N} = (fun x ↦ ({x} : Set E)) '' N := by
    ext A
    simp only [mem_ofPred_eq, ncard_eq_one, mem_image]
    constructor
    · rintro ⟨⟨x, rfl⟩, hx⟩
      exact ⟨x, singleton_subset_iff.mp hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, singleton_subset_iff.2 hx⟩
  rw [hsing, hsing, image_singleton_sups]
  exact Set.ext fun _ ↦ (minimal_mem_inter_some_iff_of_disjoint h).symm

/-- When a man and a woman alone smiled, the collective entry of *No man and no woman smiled* (103a)
holds and the intersective one fails. -/
theorem sups_noMan_noWoman {N N' : Set E} (h : Disjoint N N') {x y : E} (hx : x ∈ N)
    (hy : y ∈ N') :
    {x, y} ∈ {P : Set E | Det.no N P} ⊻ {P | Det.no N' P} ∧
      {x, y} ∉ {P : Set E | Det.no N P} ∩ {P | Det.no N' P} := by
  refine ⟨⟨{y}, fun z hz hzy ↦ ?_, {x}, fun z hz hzx ↦ ?_, ?_⟩, fun ⟨hno, _⟩ ↦
    hno hx (mem_insert x _)⟩
  · exact disjoint_left.mp h hz (eq_of_mem_singleton hzy ▸ hy)
  · exact disjoint_left.mp h (eq_of_mem_singleton hzx ▸ hx) hz
  · exact (union_comm _ _).trans (singleton_union)

-- (103b)
theorem sups_individual_nobodyElse {x y : E} (hxy : x ≠ y) :
    {x, y} ∈ {P : Set E | individual y P} ⊻ {P | Det.no {y}ᶜ P} ∧
      {x, y} ∉ {P : Set E | individual y P} ∩ {P | Det.no {y}ᶜ P} :=
  ⟨⟨{x, y}, mem_insert_of_mem x rfl, ∅, fun _ _ h ↦ h, union_empty _⟩,
    fun ⟨_, hno⟩ ↦ hno hxy (mem_insert x _)⟩

-- (105)
theorem sups_individual_card {N W : Set E} {j : E} (hj : j ∉ N) (hW : W ⊆ N)
    (hW4 : W.ncard = 4) {p : ℕ → Prop} (h3 : p 3) (h4 : ¬ p 4) :
    insert j W ∈ {P : Set E | individual j P} ⊻ {P | p (N ∩ P).ncard} ∧
      insert j W ∉ {P : Set E | individual j P} ∩ {P | p (N ∩ P).ncard} := by
  have hNW (P : Set E) (hP : P ⊆ W) : N ∩ P = P := inter_eq_right.mpr (hP.trans hW)
  obtain ⟨w, hw⟩ := nonempty_of_ncard_ne_zero (s := W) (by omega)
  refine ⟨⟨{j, w}, mem_insert j _, W \ {w}, ?_, ?_⟩, fun ⟨_, hp⟩ ↦ h4 ?_⟩
  · rw [mem_ofPred_eq, hNW _ sdiff_subset, ncard_sdiff_singleton_of_mem hw, hW4]
    exact h3
  · change {j, w} ∪ W \ {w} = insert j W
    rw [insert_union, singleton_union, insert_sdiff_singleton, insert_eq_of_mem hw]
  · have : N ∩ insert j W = W := by
      rw [inter_insert_of_notMem hj, hNW W subset_rfl]
    rwa [mem_ofPred_eq, this, hW4] at hp

/- *John and between one and three women smiled* (105a). -/
example {N W : Set E} {j : E} (hj : j ∉ N) (hW : W ⊆ N) (hW4 : W.ncard = 4) :
    insert j W ∈ {P : Set E | individual j P} ⊻ {P | Det.between 1 3 N P} ∧
      insert j W ∉ {P : Set E | individual j P} ∩ {P | Det.between 1 3 N P} :=
  sups_individual_card (p := fun n ↦ 1 ≤ n ∧ n ≤ 3) hj hW hW4 (by decide) (by decide)

/- *John and an odd number of women smiled* (105b). -/
example {N W : Set E} {j : E} (hj : j ∉ N) (hW : W ⊆ N) (hW4 : W.ncard = 4) :
    insert j W ∈ {P : Set E | individual j P} ⊻ {P | Odd (N ∩ P).ncard} ∧
      insert j W ∉ {P : Set E | individual j P} ∩ {P | Odd (N ∩ P).ncard} :=
  sups_individual_card (p := Odd) hj hW hW4 (by decide) (by decide)

end Champollion2016b
