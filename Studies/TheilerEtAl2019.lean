/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Inquisitive.Modal
public import Linglib.Logic.Trivalent.Proposition

/-!
# Theiler, Roelofsen and Aloni (2019): Picky predicates

A declarative and an interrogative complement denote objects of one type, an inquisitive
proposition, and a clause-embedding predicate applies to either. A declarative complement is never
inquisitive and an interrogative complement is never informative. A predicate that rejects one of
the two does so because its meaning is trivial there: true wherever it is defined, or true
nowhere.

*Be certain* holds where the subject's doxastic state resolves the complement. A neg-raising
predicate over a modal base presupposes that the base resolves the polar question of the
complement and asserts that it resolves the complement. With a declarative complement the
presupposition is the excluded middle, and a denial yields the lowered reading. With an
interrogative complement the presupposition and the assertion coincide. *Be true* is resolution
by the state that knows the world, which every interrogative complement satisfies. *Wonder* holds
where the doxastic state does not resolve the complement and the inquisitive state lies below it,
which no declarative complement allows, and *depend on* requires two alternatives of each
argument.

## Main definitions

* `TheilerEtAl2019.negRaising`: the neg-raising predicate over a modal base.
* `TheilerEtAl2019.wonder`: the worlds where an agent wonders about a proposition.
* `TheilerEtAl2019.dependsOn`: the worlds where one proposition depends on another relative to a
  modal base.

## Implementation notes

A neg-raising predicate is defined with its presupposition in the form that the modal base
resolves the polar question of the complement, which is the disjunction that it resolves the
complement or its negation.

An interrogative complement enters the results as a proposition whose informative content is
every world, and a declarative as the declarative of a set of worlds or as a proposition with one
alternative. The function of *depend on* is defined on every set of worlds and constrained on the
alternatives of its argument.

## TODO

The article's judgments are not recorded as rows, and its predicates are not read from language
file entries. The reformulation of the presupposition with the operator that ensures
inquisitiveness, which covers complements conjoining a declarative with an interrogative, is not
formalized, nor are presuppositional questions.

## References

* [theiler-etal-2019]
* [ciardelli-roelofsen-2015]
* [ciardelli-2016]
* [gajewski-2002]
* [gajewski-2007]
* [bartsch-1973]
-/

@[expose] public section

namespace TheilerEtAl2019

open Inquisitive Inquisitive.Proposition

variable {W : Type*} {M dox σ : W → Set W} {inq : W → Proposition (Set W)}
  {P P' : Proposition (Set W)} {p : Set W} {w : W}

/-! ### Responsive predicates -/

-- (9): *be certain* of a question holds where the doxastic state lies within one of its
-- alternatives
theorem mem_resolvedBy_generate {Q : Set (Set W)} :
    w ∈ (generate Q).resolvedBy dox ↔ dox w = ∅ ∨ ∃ p ∈ Q, dox w ⊆ p :=
  mem_generate

/-! ### Neg-raising predicates -/

-- the definition of inquisitive negation
theorem mem_compl_iff (P : Proposition (Set W)) (p : Set W) :
    p ∈ Pᶜ ↔ ∀ q ∈ P, q ∩ p = ∅ := by
  rw [compl_eq, mem_ofSet]
  refine ⟨fun h q hq ↦ Set.eq_empty_of_forall_notMem fun u ⟨huq, hup⟩ ↦ h hup ⟨q, hq, huq⟩,
    fun h u hu ⟨q, hq, huq⟩ ↦ ?_⟩
  exact Set.notMem_empty u (h q hq ▸ ⟨huq, hu⟩)

open Classical in
/-- The neg-raising predicate over the modal base `M` presupposes that `M` resolves the polar
question of its complement and asserts that `M` resolves the complement. -/
noncomputable def negRaising (M : W → Set W) (P : Proposition (Set W)) : W → Trivalent :=
  Trivalent.condEvent (fun w ↦ w ∈ P.query.resolvedBy M) fun w ↦ w ∈ P.resolvedBy M

-- (19): the presupposition, as the generalized excluded middle
theorem negRaising_ne_undefined_iff :
    negRaising M P w ≠ .undefined ↔ M w ∈ P ∨ M w ∈ Pᶜ := by
  simp [negRaising, resolvedBy_query, or_iff_not_imp_left]

-- with a declarative complement the presupposition is the excluded middle
theorem negRaising_ofSet_ne_undefined_iff :
    negRaising M (ofSet p) w ≠ .undefined ↔ M w ⊆ p ∨ M w ⊆ pᶜ := by
  rw [negRaising_ne_undefined_iff, compl_eq, info_ofSet]
  rfl

/-- A neg-raising predicate is false of a declarative exactly where its modal base lies within
the declarative's negation and not within the declarative: its denial is the predicate of the
negation. -/
theorem negRaising_ofSet_eq_false_iff :
    negRaising M (ofSet p) w = .false ↔ M w ⊆ pᶜ ∧ ¬ M w ⊆ p := by
  simp only [negRaising, Trivalent.condEvent_eq_false_iff, resolvedBy_query, compl_eq, info_ofSet,
    Set.mem_union, mem_resolvedBy, mem_ofSet]
  tauto

open Classical in
/-- With a complement that is not informative, what a neg-raising predicate presupposes is what
it asserts, so it is true wherever it is defined. -/
theorem negRaising_eq_true_of_info_eq_univ (h : P.info = Set.univ)
    (hd : negRaising M P w ≠ .undefined) : negRaising M P w = .true := by
  have hq : w ∈ P.query.resolvedBy M :=
    by_contra fun hn ↦ hd (Trivalent.condEvent_eq_undefined_iff.2 hn)
  exact Trivalent.condEvent_eq_true_iff.2 ⟨hq, resolvedBy_query_of_info_eq_univ h M ▸ hq⟩

-- (31)–(33): with a complement headed by the question operator, whatever the modal base and the
-- prejacent
theorem negRaising_query_eq_true (hd : negRaising M P.query w ≠ .undefined) :
    negRaising M P.query w = .true :=
  negRaising_eq_true_of_info_eq_univ (info_query P) hd

-- with a declarative complement the predicate is not trivial
theorem exists_negRaising_ofSet_eq_false :
    ∃ (M : Bool → Set Bool) (p : Set Bool) (w : Bool), negRaising M (ofSet p) w = .false :=
  ⟨fun _ ↦ {false}, {true}, true, negRaising_ofSet_eq_false_iff.2 (by simp)⟩

/-! ### Truth-evaluating predicates -/

/-- *Be true* is resolution by the state that knows the world, and it holds everywhere of a
complement that is not informative. -/
theorem resolvedBy_singleton_of_info_eq_univ (h : P.info = Set.univ) :
    P.resolvedBy (fun w ↦ {w}) = Set.univ := by
  rw [resolvedBy_singleton, h]

-- *be false* holds nowhere of such a complement
theorem compl_resolvedBy_singleton_of_info_eq_univ (h : P.info = Set.univ) :
    (P.resolvedBy fun w ↦ {w})ᶜ = ∅ := by
  rw [resolvedBy_singleton_of_info_eq_univ h, Set.compl_univ]

/-! ### Rogative predicates -/

/-- An agent wonders about `P` where her doxastic state does not resolve `P` and her inquisitive
state lies below `P`. -/
def wonder (dox : W → Set W) (inq : W → Proposition (Set W)) (P : Proposition (Set W)) : Set W :=
  (P.resolvedBy dox)ᶜ ∩ P.entertainedBy inq

/-- No one wonders about a declarative: an inquisitive state below it has its informative content,
the doxastic state, within it. -/
theorem wonder_ofSet (h : ∀ w, (inq w).info = dox w) (p : Set W) :
    wonder dox inq (ofSet p) = ∅ := by
  ext w
  simp [wonder, entertainedBy_ofSet, h]

-- an agent can wonder about a question
theorem exists_mem_wonder :
    ∃ (dox : Bool → Set Bool) (inq : Bool → Proposition (Set Bool)) (P : Proposition (Set Bool))
      (w : Bool), (∀ w, (inq w).info = dox w) ∧ w ∈ wonder dox inq P := by
  refine ⟨fun _ ↦ Set.univ, fun _ ↦ (ofSet {true}).query, (ofSet {true}).query, true,
    fun _ ↦ info_query _, ?_, mem_entertainedBy.2 le_rfl⟩
  simp only [Set.mem_compl_iff, mem_resolvedBy, query_eq_sup_compl, compl_eq, info_ofSet, mem_sup,
    mem_ofSet, not_or]
  exact ⟨fun h ↦ Bool.false_ne_true (h (Set.mem_univ false)), fun h ↦ h (Set.mem_univ true) rfl⟩

/-- `P` depends on `P'` relative to the modal base `σ` where some function from the alternatives
of `P'` to those of `P` takes every state of `σ` within an alternative into its value, and takes
two alternatives compatible with `σ` to different values. -/
def dependsOn (σ : W → Set W) (P' P : Proposition (Set W)) : Set W :=
  {w | ∃ f : Set W → Set W, (∀ a ∈ alt P', f a ∈ alt P) ∧
    (∀ q ⊆ σ w, ∀ a ∈ alt P', q ⊆ a → q ⊆ f a) ∧
    ∃ a ∈ alt P', ∃ a' ∈ alt P', (a ∩ σ w).Nonempty ∧ (a' ∩ σ w).Nonempty ∧ f a ≠ f a'}

/-- Nothing with a single alternative depends on anything, and nothing depends on what has a
single alternative. -/
theorem dependsOn_eq_empty_of_subsingleton_alt (h : (alt P).Subsingleton ∨ (alt P').Subsingleton) :
    dependsOn σ P' P = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  rintro w ⟨f, hf, -, a, ha, a', ha', -, -, hne⟩
  refine hne ?_
  rcases h with h | h
  · exact h (hf a ha) (hf a' ha')
  · rw [h ha ha']

-- (42), (43): a declarative in either argument
theorem dependsOn_ofSet_right (σ : W → Set W) (P' : Proposition (Set W)) (p : Set W) :
    dependsOn σ P' (ofSet p) = ∅ :=
  dependsOn_eq_empty_of_subsingleton_alt (.inl (alt_ofSet p ▸ Set.subsingleton_singleton))

theorem dependsOn_ofSet_left (σ : W → Set W) (p : Set W) (P : Proposition (Set W)) :
    dependsOn σ (ofSet p) P = ∅ :=
  dependsOn_eq_empty_of_subsingleton_alt (.inr (alt_ofSet p ▸ Set.subsingleton_singleton))

end TheilerEtAl2019
