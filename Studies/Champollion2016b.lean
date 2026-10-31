module

public import Linglib.Core.Order.UpperLower.Closure
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Reference.ChoiceFunction
public import Linglib.Semantics.Composition.Coordinator
public import Linglib.Semantics.Composition.Coordination
public import Linglib.Semantics.Composition.Tree
public import Linglib.Syntax.Command
public import Linglib.Fragments.English.Coordination
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Sups

/-!
# Champollion (2016): Ten Men and Women Got Married Today: Noun Coordination and the Intersective Theory of Conjunction

This file derives the collective readings of noun coordination from the intersective *and*. A
plurality is a set, a raised noun is an upper set of pluralities, and Minimization of the meet of
two raised nouns keeps [the minimal elements of the set product of their
generators](##minimal_mem_and_upperClosure_iff), the collective *and* of Heycock and Zamparelli.
On the paper's logical forms, Choice Closure above Minimization makes [*a doctor and lawyer met*
hold of any doctor–lawyer pair](##holds_lf56) and [*ten men and women got married* of ten-person
man–woman mixtures](##holds_lf81); above *no* it [gives a reading the constraint on its scope
excludes](##not_closureBelowNo_lf61). [*Or* is never collective](##minimal_mem_or_some_iff), and
the collective entry [overgenerates on conjuncts that are not upward
entailing](##sups_noMan_noWoman).

## Implementation notes

* A plurality is a `Set E` and a property of pluralities a `Set (Set E)`. The determiner *a*,
  which is Existential Raising, is `Quantifier.Det.some`, the Montague lift is
  `Quantifier.individual`, Distributive Choice Raising is the principal filter `Set.Ici`, Predicate
  Distributivity is `𝒫 S \ {∅}`, and *and* and *or* are what the English coordinators denote,
  `Coordinator.denote`.
* Choice Closure quantifies over `ChoiceFunction`, whose totality turns the definedness condition
  `N ≠ ∅` of Choice Raising into a hypothesis. [Closing the choice function directly above Choice
  Raising](##ChoiceFunction.exists_apply_iff_some) gives Existential Raising.
* The logical forms are trees interpreted by the composition engine under a typing of the
  indices: a trace of a choice-function index applied to a noun is the chosen individual or
  plurality, and Choice Closure, at the types of (49) and (50), binds the index by Predicate
  Abstraction. The engine selects predicate modification only for predicates of individuals and
  of eventualities, so *ten*, a predicate of pluralities in (70), is a modifier with the same
  intersective denotation.
* Heycock and Zamparelli's common nouns denote sets of singletons. Their counterexamples are stated
  for the individuals those singletons contain, which the singleton map carries over since it
  preserves unions.

## Errata

* (83c) and the prose after it swap the Americans and Russians of (82a) and (83b).
* (99a) prints `MIN(ER(cat)) or MIN(ER(dog))` for the `MIN(ER(cat) or ER(dog))` of its prose and
  (99b). [The two are equal](##or_setOf_minimal_mem_some), so the slip is harmless.
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

open Quantifier Set SetFamily English.Coordination

private theorem and_denote {α : Type*} [CompleteBooleanAlgebra α] (s : Set α) :
    and_.denote s = sInf s :=
  Coordinator.denote_of_conjunctive rfl s

private theorem or_denote {α : Type*} [CompleteBooleanAlgebra α] (s : Set α) :
    or_.denote s = sSup s :=
  Coordinator.denote_of_disjunctive rfl s

variable {α E : Type*}

/-- **Determiner Fitting** (92) applies a determiner of individuals to the union of a property
of pluralities and to the union of its meet with the scope. -/
def determinerFitting (D : Det E) (A B : Set (Set E)) : Prop := D (⋃₀ A) (⋃₀ (A ∩ B))

/-! ### Raised nouns as upper sets -/

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

/-! ### Intersection and Minimization -/

/-- Minimization of the meet of two upper closures keeps the minimal elements of the set product
of their generators, the collective conjunction of Heycock and Zamparelli (101), p. 608. -/
theorem minimal_mem_and_upperClosure_iff [SemilatticeSup α] {s t : Set α} {a : α} :
    Minimal (· ∈ and_.denote {(upperClosure s : Set α), (upperClosure t : Set α)}) a ↔
      Minimal (· ∈ s ⊻ t) a := by
  rw [and_denote, sInf_eq_sInter, sInter_pair, ← UpperSet.coe_sup, ← upperClosure_sups]
  exact minimal_mem_upperClosure_iff

-- (18)
theorem and_some (N N' : Set E) :
    and_.denote {{P | Det.some N P}, {P | Det.some N' P}} =
      (upperClosure {P : Set E | ∃ x ∈ N, ∃ y ∈ N', P = {x, y}} : Set (Set E)) := by
  rw [and_denote, sInf_pair, setOf_some_eq_upperClosure, setOf_some_eq_upperClosure,
    ← image_singleton_sups, upperClosure_sups]
  rfl

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
theorem minimal_mem_and_some_iff {N N' P : Set E} :
    Minimal (· ∈ and_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P ↔
      (∃ x ∈ N ∩ N', P = {x}) ∨ ∃ x ∈ N \ N', ∃ y ∈ N' \ N, P = {x, y} := by
  rw [setOf_some_eq_upperClosure, setOf_some_eq_upperClosure, minimal_mem_and_upperClosure_iff,
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
theorem minimal_mem_and_some_iff_of_disjoint {N N' P : Set E} (h : Disjoint N N') :
    Minimal (· ∈ and_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P ↔
      ∃ x ∈ N, ∃ y ∈ N', P = {x, y} := by
  rw [minimal_mem_and_some_iff, disjoint_iff_inter_eq_empty.mp h, sdiff_eq_left.mpr h,
    sdiff_eq_left.mpr h.symm]
  simp

-- (42)
theorem minimal_mem_and_some_self_iff {N P : Set E} :
    Minimal (· ∈ and_.denote {{Q | Det.some N Q}, {Q | Det.some N Q}}) P ↔ ∃ x ∈ N, P = {x} := by
  rw [and_denote, sInf_pair, inf_idem, minimal_mem_some_iff]

-- (43)
theorem minimal_mem_and_individual_some_iff {N P : Set E} {j : E} (hj : j ∈ N) :
    Minimal (· ∈ and_.denote {{Q | individual j Q}, {Q | Det.some N Q}}) P ↔ P = {j} := by
  have : {Q : Set E | individual j Q} = {Q | Det.some {j} Q} := by
    ext Q; simp [individual, Det.some]
  rw [this, minimal_mem_and_some_iff]
  simp [hj]

-- (24)
theorem some_setOf_minimal_inter_iff {N N' : Set E} (h : Disjoint N N') (R S : Set (Set E)) :
    Det.some ({P | Minimal (· ∈ and_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P} ∩ R)
      S ↔ ∃ x ∈ N, ∃ y ∈ N', {x, y} ∈ R ∧ {x, y} ∈ S := by
  constructor
  · rintro ⟨_, ⟨hmin, hR⟩, hS⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := (minimal_mem_and_some_iff_of_disjoint h).1 hmin
    exact ⟨x, hx, y, hy, hR, hS⟩
  · rintro ⟨x, hx, y, hy, hR, hS⟩
    exact ⟨_, ⟨(minimal_mem_and_some_iff_of_disjoint h).2 ⟨x, hx, y, hy, rfl⟩, hR⟩, hS⟩

-- (29)
theorem some_setOf_minimal_powerset_iff {N N' : Set E} (h : Disjoint N N') (S : Set E) :
    Det.some {P | Minimal (· ∈ and_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P}
      (𝒫 S \ {∅}) ↔ ∃ x ∈ N, ∃ y ∈ N', x ∈ S ∧ y ∈ S := by
  constructor
  · rintro ⟨_, hmin, hS, -⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := (minimal_mem_and_some_iff_of_disjoint h).1 hmin
    exact ⟨x, hx, y, hy, hS (mem_insert x _), hS (mem_insert_of_mem x rfl)⟩
  · rintro ⟨x, hx, y, hy, hxS, hyS⟩
    exact ⟨_, (minimal_mem_and_some_iff_of_disjoint h).2 ⟨x, hx, y, hy, rfl⟩,
      insert_subset hxS (singleton_subset_iff.2 hyS), (insert_nonempty x _).ne_empty⟩

/-! ### Choice Raising -/

theorem minimal_mem_and_Ici_iff [Lattice α] {a b c : α} :
    Minimal (· ∈ and_.denote {Ici a, Ici b}) c ↔ c = a ⊔ b := by
  rw [and_denote, sInf_eq_sInter, sInter_pair, Ici_inter_Ici]
  exact minimal_ge_iff

-- (40)
theorem minimal_mem_and_individual_iff {x y : E} {P : Set E} :
    Minimal (· ∈ and_.denote {{Q | individual x Q}, {Q | individual y Q}}) P ↔ P = {x, y} := by
  rw [setOf_individual, setOf_individual, minimal_mem_and_Ici_iff, ← singleton_union]
  rfl

-- (52), (53)
theorem exists_minimal_mem_and_individual_iff {N P : Set E} (hN : N.Nonempty) (j : E) :
    (∃ f : ChoiceFunction E,
      Minimal (· ∈ and_.denote {{Q | individual j Q}, {Q | individual (f N) Q}}) P) ↔
      ∃ x ∈ N, P = {j, x} := by
  simp only [minimal_mem_and_individual_iff]
  exact ChoiceFunction.exists_apply_iff_some hN fun x ↦ P = {j, x}

-- (57)
theorem exists₂_minimal_mem_and_individual_iff {N N' P : Set E} (hN : N.Nonempty)
    (hN' : N'.Nonempty) :
    (∃ f₁ f₂ : ChoiceFunction E,
      Minimal (· ∈ and_.denote {{Q | individual (f₁ N) Q}, {Q | individual (f₂ N') Q}}) P) ↔
      ∃ x ∈ N, ∃ y ∈ N', P = {x, y} := by
  simp only [minimal_mem_and_individual_iff]
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

-- (68), p. 592
theorem ncard_inter_union_of_and_exactly {N N' P : Set E} (h : Disjoint N N') {n : ℕ}
    (hn : n ≠ 0) (hP : and_.denote ({fun D ↦ D N, fun D ↦ D N'} : Set (Det E → Quantifier E))
      (Det.exactly n) P) :
    (P ∩ (N ∪ N')).ncard = n + n := by
  rw [and_denote, sInf_pair] at hP
  have h₁ : (P ∩ N).ncard = n := by rw [inter_comm]; exact hP.1
  have h₂ : (P ∩ N').ncard = n := by rw [inter_comm]; exact hP.2
  rw [inter_union_distrib_left, ncard_union_eq (h.mono inter_subset_right inter_subset_right)
    (finite_of_ncard_ne_zero (h₁ ▸ hn)) (finite_of_ncard_ne_zero (h₂ ▸ hn)), h₁, h₂]

-- (75), (76)
theorem ncard_le_two_of_minimal_mem_and_some {N N' P : Set E}
    (hP : Minimal (· ∈ and_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P) :
    P.ncard ≤ 2 := by
  rcases minimal_mem_and_some_iff.1 hP with ⟨x, -, rfl⟩ | ⟨x, -, y, -, rfl⟩
  · simp
  · exact (ncard_insert_le x {y}).trans (by simp)

-- (80)
theorem exists₂_minimal_mem_and_Ici_iff {N N' : Set (Set E)} {P : Set E} (hN : N.Nonempty)
    (hN' : N'.Nonempty) :
    (∃ f₁ f₂ : ChoiceFunction (Set E), Minimal (· ∈ and_.denote {Ici (f₁ N), Ici (f₂ N')}) P) ↔
      P ∈ N ⊻ N' := by
  simp only [minimal_mem_and_Ici_iff, mem_sups]
  exact (ChoiceFunction.exists_apply_iff_some hN fun M ↦
    ∃ f₂ : ChoiceFunction (Set E), P = M ⊔ f₂ N').trans (exists_congr fun M ↦
      and_congr_right fun _ ↦ (ChoiceFunction.exists_apply_iff_some hN' fun W ↦
        P = M ⊔ W).trans (exists_congr fun _ ↦ and_congr_right fun _ ↦ eq_comm))

-- (80)
theorem exists₂_minimal_mem_and_Ici_powerset_iff {N N' P : Set E} (hN : N.Nonempty)
    (hN' : N'.Nonempty) :
    (∃ f₁ f₂ : ChoiceFunction (Set E),
      Minimal (· ∈ and_.denote
        {Ici (f₁ (𝒫 N \ {∅} : Set (Set E))), Ici (f₂ (𝒫 N' \ {∅} : Set (Set E)))}) P) ↔
      P ⊆ N ∪ N' ∧ (P ∩ N).Nonempty ∧ (P ∩ N').Nonempty := by
  have (N : Set E) (hN : N.Nonempty) : (𝒫 N \ {∅} : Set (Set E)).Nonempty :=
    ⟨N, Subset.rfl, hN.ne_empty⟩
  rw [exists₂_minimal_mem_and_Ici_iff (this N hN) (this N' hN'), mem_sups_powerset_iff]

-- (83)
theorem exists₂_some_setOf_minimal_mem_and_Ici_iff {N N' : Set (Set E)} (hN : N.Nonempty)
    (hN' : N'.Nonempty) (S : Set (Set E)) :
    (∃ f₁ f₂ : ChoiceFunction (Set E),
      Det.some {P | Minimal (· ∈ and_.denote {Ici (f₁ N), Ici (f₂ N')}) P} S) ↔
      ∃ M ∈ N, ∃ W ∈ N', M ∪ W ∈ S := by
  have (a b : Set E) : {P | Minimal (· ∈ and_.denote {Ici a, Ici b}) P} = {a ⊔ b} :=
    Set.ext fun _ ↦ minimal_mem_and_Ici_iff
  simp only [Det.some, this, singleton_inter_nonempty]
  exact (ChoiceFunction.exists_apply_iff_some hN fun M ↦
    ∃ f₂ : ChoiceFunction (Set E), M ⊔ f₂ N' ∈ S).trans (exists_congr fun M ↦
      and_congr_right fun _ ↦ ChoiceFunction.exists_apply_iff_some hN' fun W ↦ M ⊔ W ∈ S)

/-! ### Logical forms

The composition engine interprets the paper's logical forms. Choice Raising is a word applied to a
trace whose index ranges over choice functions, Choice Closure a word applied to the abstraction
over that index, and *and* the English coordinator at the type of its coordinands. -/

section LogicalForms

open Montague PhraseStructure Tree

variable {E : Type} {N N' : Set E} {S : Set (Set E)}

/-- The words of the logical forms: two nouns and a predicate of pluralities, the determiners,
*and*, the numeral *ten*, and the silent operators. -/
inductive Word where
  | noun₁
  | noun₂
  | vp
  | a
  | no
  | and
  | ten
  | min
  | cr
  | dcr
  | pdist
  | choiceClosure
  | choiceClosureSentence
  | choiceClosureDistributive
  deriving DecidableEq

/-- The type of an index: `1` and `2` range over choice functions on individuals, the others over
choice functions on pluralities. -/
def indexTy (n : ℕ) : Ty := if n ≤ 2 then (.e ⇒ .t) ⇒ .e else ((.e ⇒ .t) ⇒ .t) ⇒ .e ⇒ .t

/-- The denotations, over two nouns `N`, `N'` and a predicate `S` of pluralities. *A* (23) and
*no* hold between properties of pluralities, Minimization is (19), Choice Raising (46),
Distributive Choice Raising (78), Predicate Distributivity (27), and Choice Closure (49) and (50)
ranges over choice functions. -/
def lex (N N' : Set E) (S : Set (Set E)) : Word → Option (Denotation E Unit)
  | .noun₁ => some ⟨.e ⇒ .t, N⟩
  | .noun₂ => some ⟨.e ⇒ .t, N'⟩
  | .vp => some ⟨(.e ⇒ .t) ⇒ .t, S⟩
  | .a => some ⟨((.e ⇒ .t) ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t) ⇒ .t,
      fun (A B : Set (Set E)) ↦ Det.some A B⟩
  | .no => some ⟨((.e ⇒ .t) ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t) ⇒ .t,
      fun (A B : Set (Set E)) ↦ Det.no A B⟩
  | .and => some (and_.reading ((.e ⇒ .t) ⇒ .t) trivial)
  | .ten => some ⟨((.e ⇒ .t) ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t,
      fun (Q : Set (Set E)) (P : Set E) ↦ P.ncard = 10 ∧ P ∈ Q⟩
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
  | .choiceClosureDistributive =>
      some ⟨((((.e ⇒ .t) ⇒ .t) ⇒ .e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t,
        fun (A : (Set (Set E) → Set E) → Set E → Prop) (P : Set E) ↦
          ∃ f : ChoiceFunction (Set E), A f P⟩

/-- A logical form holds when it denotes a truth. -/
def Holds (N N' : Set E) (S : Set (Set E)) (g : ∀ n, Ty.Domain E Unit (indexTy n))
    (t : Tree Unit Word) : Prop :=
  ∃ p, interpWith indexTy (lex N N' S) g t = some ⟨.t, p⟩ ∧ p

/-- `[[CR t₁] noun₁] [and [[CR t₂] noun₂]]`. -/
def crAnd : Tree Unit Word :=
  .bin (.bin (.bin (.leaf .cr) (.tr 1)) (.leaf .noun₁))
    (.bin (.leaf .and) (.bin (.bin (.leaf .cr) (.tr 2)) (.leaf .noun₂)))

/-- The LF (56) of *a doctor and lawyer met*: both Choice Closures above Minimization. -/
def lf56 : Tree Unit Word :=
  .bin (.bin (.leaf .a) (.bin (.leaf .choiceClosure) (.binder 1
    (.bin (.leaf .choiceClosure) (.binder 2 (.bin (.leaf .min) crAnd)))))) (.leaf .vp)

/-- `[∃₁ [λ₁ [[CR t₁] noun₁]]] [and [∃₂ [λ₂ [[CR t₂] noun₂]]]]`, each Choice Closure directly above
its Choice Raising. -/
def closedAnd : Tree Unit Word :=
  .bin (.bin (.leaf .choiceClosure) (.binder 1 (.bin (.bin (.leaf .cr) (.tr 1)) (.leaf .noun₁))))
    (.bin (.leaf .and)
      (.bin (.leaf .choiceClosure) (.binder 2 (.bin (.bin (.leaf .cr) (.tr 2)) (.leaf .noun₂)))))

/-- *A doctor and lawyer met* with the Choice Closures below Minimization. -/
def lfLocal : Tree Unit Word :=
  .bin (.bin (.leaf .a) (.bin (.leaf .min) closedAnd)) (.leaf .vp)

/-- The LF of (60a) *no man and woman have a right …*, with Choice Closure below *no*. -/
def lf60 : Tree Unit Word :=
  .bin (.bin (.leaf .no) (.bin (.leaf .choiceClosure) (.binder 1
    (.bin (.leaf .choiceClosure) (.binder 2 (.bin (.leaf .min) crAnd)))))) (.leaf .vp)

/-- The LF (61), with Choice Closure above *no*. -/
def lf61 : Tree Unit Word :=
  .bin (.leaf .choiceClosureSentence) (.binder 1 (.bin (.leaf .choiceClosureSentence) (.binder 2
    (.bin (.bin (.leaf .no) (.bin (.leaf .min) crAnd)) (.leaf .vp)))))

/-- `[[DCR t₃] [PDIST noun₁]] [and [[DCR t₄] [PDIST noun₂]]]`. -/
def dcrAnd : Tree Unit Word :=
  .bin (.bin (.bin (.leaf .dcr) (.tr 3)) (.bin (.leaf .pdist) (.leaf .noun₁)))
    (.bin (.leaf .and) (.bin (.bin (.leaf .dcr) (.tr 4)) (.bin (.leaf .pdist) (.leaf .noun₂))))

/-- The LF (81) of *ten men and women got married today*. -/
def lf81 : Tree Unit Word :=
  .bin (.bin (.leaf .a) (.bin (.leaf .ten) (.bin (.leaf .choiceClosureDistributive) (.binder 3
    (.bin (.leaf .choiceClosureDistributive) (.binder 4 (.bin (.leaf .min) dcrAnd))))))) (.leaf .vp)

/-- No Choice Closure in `t` takes scope over *no*, the constraint the paper draws from (59) and
(60). -/
def ClosureBelowNo (t : Tree Unit Word) : Prop :=
  ∀ p ∈ t.positionedTerminals, ∀ q ∈ t.positionedTerminals,
    p.2.2 ∈ [.choiceClosure, .choiceClosureSentence, .choiceClosureDistributive] →
      q.2.2 = .no → ¬ t.CCommands p.1 q.1

instance : DecidablePred ClosureBelowNo := fun t ↦
  inferInstanceAs (Decidable (∀ p ∈ t.positionedTerminals, ∀ q ∈ t.positionedTerminals,
    p.2.2 ∈ [.choiceClosure, .choiceClosureSentence, .choiceClosureDistributive] →
      q.2.2 = .no → ¬ t.CCommands p.1 q.1))

variable (g : ∀ n, Ty.Domain E Unit (indexTy n))

private theorem interpWith_and {g : ∀ n, Ty.Domain E Unit (indexTy n)} {X Y : Tree Unit Word}
    {p q : Set (Set E)} (hX : interpWith indexTy (lex N N' S) g X = some ⟨(.e ⇒ .t) ⇒ .t, p⟩)
    (hY : interpWith indexTy (lex N N' S) g Y = some ⟨(.e ⇒ .t) ⇒ .t, q⟩) :
    interpWith indexTy (lex N N' S) g (.bin X (.bin (.leaf .and) Y)) =
      some ⟨(.e ⇒ .t) ⇒ .t, (and_.denote {p, q} : Set (Set E))⟩ := by
  simp only [interpWith_phrase_binary, interpWith_terminal, lex, hX, hY, Option.bind_some]
  rw [Coordinator.combine?_reading]
  simp only [Coordinator.denote_of_conjunctive (c := and_) rfl, sInf_pair]
  rfl

-- (57a)–(57c)
theorem interpWith_crAnd : interpWith indexTy (lex N N' S) g crAnd = some ⟨(.e ⇒ .t) ⇒ .t,
    (and_.denote {{Q | individual (g 1 N) Q}, {Q | individual (g 2 N') Q}} : Set (Set E))⟩ :=
  interpWith_and rfl rfl

theorem interpWith_closedAnd : interpWith indexTy (lex N N' S) g closedAnd =
    some ⟨(.e ⇒ .t) ⇒ .t, (and_.denote {{Q | ∃ f : ChoiceFunction E, individual (f N) Q},
      {Q | ∃ f : ChoiceFunction E, individual (f N') Q}} : Set (Set E))⟩ := by
  refine interpWith_and ?_ ?_ <;>
    simp only [interpWith_phrase_binary, interpWith_bind, interpWith_trace, interpWith_terminal,
      lex, Option.bind_some] <;> rfl

-- (80a)–(80c)
theorem interpWith_dcrAnd : interpWith indexTy (lex N N' S) g dcrAnd = some ⟨(.e ⇒ .t) ⇒ .t,
    (and_.denote {Ici (g 3 (𝒫 N \ {∅} : Set (Set E))), Ici (g 4 (𝒫 N' \ {∅} : Set (Set E)))} :
      Set (Set E))⟩ :=
  interpWith_and rfl rfl

-- (57)
theorem interpWith_lf56 : interpWith indexTy (lex N N' S) g lf56 = some ⟨.t, Det.some
    {P | ∃ f₁ f₂ : ChoiceFunction E,
      Minimal (· ∈ and_.denote {{Q | individual (f₁ N) Q}, {Q | individual (f₂ N') Q}}) P} S⟩ := by
  simp only [lf56, interpWith_phrase_binary, interpWith_bind, interpWith_terminal, lex,
    interpWith_crAnd, Option.bind_some]
  rfl

theorem interpWith_lfLocal : interpWith indexTy (lex N N' S) g lfLocal = some ⟨.t, Det.some
    {P | Minimal (· ∈ and_.denote {{Q | ∃ f : ChoiceFunction E, individual (f N) Q},
      {Q | ∃ f : ChoiceFunction E, individual (f N') Q}}) P} S⟩ := by
  simp only [lfLocal, interpWith_phrase_binary, interpWith_terminal, lex, interpWith_closedAnd,
    Option.bind_some]
  rfl

theorem interpWith_lf60 : interpWith indexTy (lex N N' S) g lf60 = some ⟨.t, Det.no
    {P | ∃ f₁ f₂ : ChoiceFunction E,
      Minimal (· ∈ and_.denote {{Q | individual (f₁ N) Q}, {Q | individual (f₂ N') Q}}) P} S⟩ := by
  simp only [lf60, interpWith_phrase_binary, interpWith_bind, interpWith_terminal, lex,
    interpWith_crAnd, Option.bind_some]
  rfl

theorem interpWith_lf61 : interpWith indexTy (lex N N' S) g lf61 = some ⟨.t,
    ∃ f₁ f₂ : ChoiceFunction E, Det.no {P | Minimal (· ∈ and_.denote
      {{Q | individual (f₁ N) Q}, {Q | individual (f₂ N') Q}}) P} S⟩ := by
  simp only [lf61, interpWith_phrase_binary, interpWith_bind, interpWith_terminal, lex,
    interpWith_crAnd, Option.bind_some]
  rfl

-- (80), (81)
theorem interpWith_lf81 : interpWith indexTy (lex N N' S) g lf81 = some ⟨.t, Det.some
    {P | P.ncard = 10 ∧ ∃ f₁ f₂ : ChoiceFunction (Set E), Minimal (· ∈ and_.denote
      {Ici (f₁ (𝒫 N \ {∅} : Set (Set E))), Ici (f₂ (𝒫 N' \ {∅} : Set (Set E)))}) P} S⟩ := by
  simp only [lf81, interpWith_phrase_binary, interpWith_bind, interpWith_terminal, lex,
    interpWith_dcrAnd, Option.bind_some]
  rfl

private theorem holds_iff {t : Tree Unit Word} {p : Prop}
    (h : interpWith indexTy (lex N N' S) g t = some ⟨.t, p⟩) : Holds N N' S g t ↔ p := by
  simp [Holds, h]

/-- With Choice Closure above Minimization, *a doctor and lawyer met* (56) holds when a doctor and
a lawyer met, whatever professions they share (58). -/
theorem holds_lf56 (hN : N.Nonempty) (hN' : N'.Nonempty) :
    Holds N N' S g lf56 ↔ ∃ x ∈ N, ∃ y ∈ N', {x, y} ∈ S := by
  rw [holds_iff g (interpWith_lf56 g)]
  constructor
  · rintro ⟨P, hP, hS⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := (exists₂_minimal_mem_and_individual_iff hN hN').1 hP
    exact ⟨x, hx, y, hy, hS⟩
  · rintro ⟨x, hx, y, hy, hS⟩
    exact ⟨_, (exists₂_minimal_mem_and_individual_iff hN hN').2 ⟨x, hx, y, hy, rfl⟩, hS⟩

-- p. 587
theorem holds_lfLocal (hN : N.Nonempty) (hN' : N'.Nonempty) :
    Holds N N' S g lfLocal ↔ Det.some
      {P | Minimal (· ∈ and_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P} S := by
  have h {N : Set E} (hN : N.Nonempty) :
      {Q | ∃ f : ChoiceFunction E, individual (f N) Q} = {Q | Det.some N Q} :=
    Set.ext fun Q ↦ ChoiceFunction.exists_apply_iff_some hN Q
  rw [holds_iff g (interpWith_lfLocal g), h hN, h hN']

/- A doctor who is also a lawyer meets another lawyer: (56) holds and the LF with local Choice
Closure does not. -/
example {x y : E} (hx : x ∈ N ∩ N') (hy : y ∈ N') (hxy : x ≠ y) :
    Holds N N' {{x, y}} g lf56 ∧ ¬ Holds N N' {{x, y}} g lfLocal := by
  refine ⟨(holds_lf56 g ⟨x, hx.1⟩ ⟨y, hy⟩).2 ⟨x, hx.1, y, hy, rfl⟩, fun h ↦ ?_⟩
  obtain ⟨P, hP, rfl⟩ := (holds_lfLocal g ⟨x, hx.1⟩ ⟨y, hy⟩).1 h
  rcases minimal_mem_and_some_iff.1 hP with ⟨z, -, hz⟩ | ⟨z, ⟨-, hzN'⟩, w, -, hzw⟩
  · have hx' : x ∈ ({z} : Set E) := hz ▸ mem_insert x {y}
    have hy' : y ∈ ({z} : Set E) := hz ▸ mem_insert_of_mem x rfl
    exact hxy (hx'.trans hy'.symm)
  · have hz : z ∈ ({x, y} : Set E) := hzw ▸ mem_insert z {w}
    rcases hz with rfl | rfl
    exacts [hzN' hx.2, hzN' hy]

-- (60a)
theorem holds_lf60 (hN : N.Nonempty) (hN' : N'.Nonempty) :
    Holds N N' S g lf60 ↔ ¬ ∃ x ∈ N, ∃ y ∈ N', {x, y} ∈ S := by
  rw [holds_iff g (interpWith_lf60 g)]
  constructor
  · rintro h ⟨x, hx, y, hy, hS⟩
    exact h ((exists₂_minimal_mem_and_individual_iff hN hN').2 ⟨x, hx, y, hy, rfl⟩) hS
  · rintro h P hP hS
    obtain ⟨x, hx, y, hy, rfl⟩ := (exists₂_minimal_mem_and_individual_iff hN hN').1 hP
    exact h ⟨x, hx, y, hy, hS⟩

-- (60b), (61)
theorem holds_lf61 (hN : N.Nonempty) (hN' : N'.Nonempty) :
    Holds N N' S g lf61 ↔ ∃ x ∈ N, ∃ y ∈ N', {x, y} ∉ S := by
  have h (a b : E) : Det.no {P | Minimal (· ∈ and_.denote
      {{Q | individual a Q}, {Q | individual b Q}}) P} S ↔ {a, b} ∉ S := by
    rw [show {P | Minimal (· ∈ and_.denote {{Q | individual a Q}, {Q | individual b Q}}) P} =
      {{a, b}} from Set.ext fun _ ↦ minimal_mem_and_individual_iff]
    simp [Det.no]
  simp only [holds_iff g (interpWith_lf61 g), h]
  constructor
  · rintro ⟨f₁, f₂, hS⟩
    exact ⟨f₁ N, f₁.apply_of_exists hN, f₂ N', f₂.apply_of_exists hN', hS⟩
  · rintro ⟨x, hx, y, hy, hS⟩
    obtain ⟨f₁, rfl⟩ := ChoiceFunction.exists_apply_eq hx
    obtain ⟨f₂, rfl⟩ := ChoiceFunction.exists_apply_eq hy
    exact ⟨f₁, f₂, hS⟩

-- p. 588
theorem closureBelowNo_lf60 : ClosureBelowNo lf60 := by decide

-- p. 588
theorem not_closureBelowNo_lf61 : ¬ ClosureBelowNo lf61 := by decide

/-- *Ten men and women got married today* (81) holds when ten people, at least one man and one
woman and nobody else, got married together. -/
theorem holds_lf81 (hN : N.Nonempty) (hN' : N'.Nonempty) :
    Holds N N' S g lf81 ↔
      ∃ P ∈ S, P.ncard = 10 ∧ P ⊆ N ∪ N' ∧ (P ∩ N).Nonempty ∧ (P ∩ N').Nonempty := by
  rw [holds_iff g (interpWith_lf81 g)]
  constructor
  · rintro ⟨P, ⟨h10, hP⟩, hS⟩
    exact ⟨P, hS, h10, (exists₂_minimal_mem_and_Ici_powerset_iff hN hN').1 hP⟩
  · rintro ⟨P, hS, h10, hP⟩
    exact ⟨P, ⟨h10, (exists₂_minimal_mem_and_Ici_powerset_iff hN hN').2 hP⟩, hS⟩

end LogicalForms

/-! ### *And* and *or* -/

/-- Minimization after Existential Raising of a disjunction keeps only singletons, so *or* is
never collective (§6.2). -/
theorem minimal_mem_or_some_iff {N N' P : Set E} :
    Minimal (· ∈ or_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P ↔
      ∃ x ∈ N ∪ N', P = {x} := by
  rw [or_denote, sSup_eq_sUnion, sUnion_pair, ← setOf_some_union, minimal_mem_some_iff]

-- (99)
theorem or_setOf_minimal_mem_some (N N' : Set E) :
    or_.denote {{P | Minimal (· ∈ {Q | Det.some N Q}) P},
      {P | Minimal (· ∈ {Q | Det.some N' Q}) P}} =
      {P | Minimal (· ∈ or_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P} := by
  ext P
  rw [or_denote, sSup_eq_sUnion, sUnion_pair, mem_union, mem_ofPred_eq, mem_ofPred_eq,
    mem_ofPred_eq, minimal_mem_or_some_iff, minimal_mem_some_iff, minimal_mem_some_iff]
  simp only [mem_union, or_and_right, exists_or]

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

-- (95), (96)
theorem determinerFitting_every_minimal_and_iff {N N' : Set E} (h : Disjoint N N')
    (hN : N.Nonempty) (hN' : N'.Nonempty) (S : Set E) :
    determinerFitting Det.every
      {P | Minimal (· ∈ and_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P} (𝒫 S \ {∅}) ↔
      Det.every (or_.denote {N, N'}) S := by
  have : {P | Minimal (· ∈ and_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P} =
      {P | ∃ x ∈ N, ∃ y ∈ N', P = {x, y}} :=
    Set.ext fun _ ↦ minimal_mem_and_some_iff_of_disjoint h
  rw [this, or_denote, sSup_pair]
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
example (N S : Set E) :
    determinerFitting Det.every
      {P | Minimal (· ∈ and_.denote {{Q | Det.some N Q}, {Q | Det.some (∅ : Set E) Q}}) P}
      (𝒫 S \ {∅}) := by
  rintro z ⟨P, hP, -⟩
  rcases minimal_mem_and_some_iff.1 hP with ⟨x, ⟨-, hx⟩, -⟩ | ⟨x, -, y, ⟨hy, -⟩, -⟩
  exacts [hx.elim, hy.elim]

-- (99)
theorem determinerFitting_every_minimal_or_iff (N N' S : Set E) :
    determinerFitting Det.every
      {P | Minimal (· ∈ or_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P} (𝒫 S \ {∅}) ↔
      Det.every (or_.denote {N, N'}) S := by
  have : {P | Minimal (· ∈ or_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P} =
      (fun x ↦ ({x} : Set E)) '' (N ∪ N') := by
    ext P; simp [minimal_mem_or_some_iff, eq_comm]
  rw [this, or_denote, sSup_pair]
  refine ⟨fun hD z hz ↦ ?_, fun hS z ⟨_, ⟨x, hx, rfl⟩, hz⟩ ↦ ⟨{x}, ⟨⟨x, hx, rfl⟩,
    singleton_subset_iff.2 (hS hx), (singleton_nonempty x).ne_empty⟩, hz⟩⟩
  obtain ⟨_, ⟨-, hP, -⟩, hzP⟩ := hD ⟨{z}, ⟨z, hz, rfl⟩, mem_singleton z⟩
  exact hP hzP

-- (95), (96), (99): the universal half of Bergmann's puzzle
theorem determinerFitting_every_and_iff_or {N N' : Set E} (h : Disjoint N N')
    (hN : N.Nonempty) (hN' : N'.Nonempty) (S : Set E) :
    determinerFitting Det.every
      {P | Minimal (· ∈ and_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P} (𝒫 S \ {∅}) ↔
      determinerFitting Det.every
        {P | Minimal (· ∈ or_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P}
        (𝒫 S \ {∅}) :=
  (determinerFitting_every_minimal_and_iff h hN hN' S).trans
    (determinerFitting_every_minimal_or_iff N N' S).symm

-- (97), (98)
theorem determinerFitting_some_minimal_and_iff {N N' : Set E} (h : Disjoint N N') (S : Set E) :
    determinerFitting Det.some
      {P | Minimal (· ∈ and_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P} (𝒫 S \ {∅}) ↔
      Det.some N S ∧ Det.some N' S := by
  rw [determinerFitting_some_iff fun h ↦ h.2 rfl, some_setOf_minimal_powerset_iff h]
  exact ⟨fun ⟨x, hx, y, hy, hxS, hyS⟩ ↦ ⟨⟨x, hx, hxS⟩, y, hy, hyS⟩,
    fun ⟨⟨x, hx, hxS⟩, y, hy, hyS⟩ ↦ ⟨x, hx, y, hy, hxS, hyS⟩⟩

-- (98), (97)
theorem some_or_and_not_determinerFitting_some {N N' S : Set E} (h : Disjoint N N')
    {x : E} (hx : x ∈ N) (hxS : x ∈ S) (hN'S : Disjoint N' S) :
    Det.some (or_.denote {N, N'}) S ∧
      ¬ determinerFitting Det.some
        {P | Minimal (· ∈ and_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P}
        (𝒫 S \ {∅}) := by
  rw [determinerFitting_some_minimal_and_iff h, or_denote, sSup_pair]
  exact ⟨⟨x, Or.inl hx, hxS⟩, fun ⟨_, y, hy, hyS⟩ ↦ disjoint_left.mp hN'S hy hyS⟩

/-! ### The collective theory -/

-- (101)
theorem and_subset_sups [Lattice α] (Q Q' : Set α) :
    and_.denote {Q, Q'} ⊆ Q ⊻ Q' := by
  rw [and_denote, sInf_pair]
  exact fun a h ↦ ⟨a, h.1, a, h.2, sup_idem a⟩

-- p. 608
theorem sups_eq_and [Lattice α] {Q Q' : Set α} (hQ : IsUpperSet Q)
    (hQ' : IsUpperSet Q') : Q ⊻ Q' = and_.denote {Q, Q'} := by
  refine (Subset.antisymm ?_ (and_subset_sups Q Q'))
  rw [and_denote, sInf_pair]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact ⟨hQ le_sup_left ha, hQ' le_sup_right hb⟩

-- (102), (20)
theorem sups_setOf_ncard_eq_one {N N' : Set E} (h : Disjoint N N') :
    {A | A.ncard = 1 ∧ A ⊆ N} ⊻ {B | B.ncard = 1 ∧ B ⊆ N'} =
      {P | Minimal (· ∈ and_.denote {{Q | Det.some N Q}, {Q | Det.some N' Q}}) P} := by
  have hsing (N : Set E) : {A | A.ncard = 1 ∧ A ⊆ N} = (fun x ↦ ({x} : Set E)) '' N := by
    ext A
    simp only [mem_ofPred_eq, ncard_eq_one, mem_image]
    constructor
    · rintro ⟨⟨x, rfl⟩, hx⟩
      exact ⟨x, singleton_subset_iff.mp hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, singleton_subset_iff.2 hx⟩
  rw [hsing, hsing, image_singleton_sups]
  exact Set.ext fun _ ↦ (minimal_mem_and_some_iff_of_disjoint h).symm

/-- When a man and a woman alone smiled, the collective entry of *No man and no woman smiled* (103a)
holds and the intersective one fails. -/
theorem sups_noMan_noWoman {N N' : Set E} (h : Disjoint N N') {x y : E} (hx : x ∈ N)
    (hy : y ∈ N') :
    {x, y} ∈ {P : Set E | Det.no N P} ⊻ {P | Det.no N' P} ∧
      {x, y} ∉ and_.denote {{P : Set E | Det.no N P}, {P : Set E | Det.no N' P}} := by
  rw [and_denote, sInf_pair]
  refine ⟨⟨{y}, fun z hz hzy ↦ ?_, {x}, fun z hz hzx ↦ ?_, ?_⟩, fun ⟨hno, _⟩ ↦
    hno hx (mem_insert x _)⟩
  · exact disjoint_left.mp h hz (eq_of_mem_singleton hzy ▸ hy)
  · exact disjoint_left.mp h (eq_of_mem_singleton hzx ▸ hx) hz
  · exact (union_comm _ _).trans (singleton_union)

-- (103b)
theorem sups_individual_nobodyElse {x y : E} (hxy : x ≠ y) :
    {x, y} ∈ {P : Set E | individual y P} ⊻ {P | Det.no {y}ᶜ P} ∧
      {x, y} ∉ and_.denote {{P : Set E | individual y P}, {P | Det.no {y}ᶜ P}} := by
  rw [and_denote, sInf_pair]
  exact ⟨⟨{x, y}, mem_insert_of_mem x rfl, ∅, fun _ _ h ↦ h, union_empty _⟩,
    fun ⟨_, hno⟩ ↦ hno hxy (mem_insert x _)⟩

-- (105)
theorem sups_individual_card {N W : Set E} {j : E} (hj : j ∉ N) (hW : W ⊆ N)
    (hW4 : W.ncard = 4) {p : ℕ → Prop} (h3 : p 3) (h4 : ¬ p 4) :
    insert j W ∈ {P : Set E | individual j P} ⊻ {P | p (N ∩ P).ncard} ∧
      insert j W ∉ and_.denote {{P : Set E | individual j P},
        {P | p (N ∩ P).ncard}} := by
  rw [and_denote, sInf_pair]
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
      insert j W ∉ and_.denote {{P : Set E | individual j P}, {P | Det.between 1 3 N P}} :=
  sups_individual_card (p := fun n ↦ 1 ≤ n ∧ n ≤ 3) hj hW hW4 (by decide) (by decide)

/- *John and an odd number of women smiled* (105b). -/
example {N W : Set E} {j : E} (hj : j ∉ N) (hW : W ⊆ N) (hW4 : W.ncard = 4) :
    insert j W ∈ {P : Set E | individual j P} ⊻ {P | Odd (N ∩ P).ncard} ∧
      insert j W ∉ and_.denote {{P : Set E | individual j P},
        {P | Odd (N ∩ P).ncard}} :=
  sups_individual_card (p := Odd) hj hW hW4 (by decide) (by decide)

end Champollion2016b
