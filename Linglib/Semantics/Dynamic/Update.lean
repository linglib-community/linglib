module

public import Linglib.Core.Algebra.AntidomainMonoid.Test
import Linglib.Core.Data.Set.Lattice.Order
public import Linglib.Core.Relation.SetRel
public import Linglib.Core.Data.Set.Functor
public import Mathlib.Tactic.TypeStar
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Use

/-!
# The update algebra

A dynamic meaning says how a sentence changes the state it is interpreted in, and there are two ways
to say it. As a **relation** it pairs each input with its possible outputs, as a program relates
machine states; dynamic predicate logic gives a formula such a relation between assignments. As a
**context change potential** it is a function on whole information states, as in Veltman's update
semantics. A relation acts on a state point by point, so every relation gives a context change
potential, and the ones that arise this way are those that treat each point separately. One that
inspects the state as a whole, as *might* does, need not be among them.

## Main definitions

* `Update S`, `Condition S`: relations on states, sets of states.
* `Update.test`: the test of a condition. With the antidomain `∼D = test D.domᶜ` the updates are an
  `AntidomainMonoid`, whose dynamic implication and disjunction are the tests of
`D₁.core D₂.dom` and `D₁.dom ∪ D₂.dom`.
* `Update.IsTest`: updates that never change the state.
* `Update.maxBy`: the outputs of an update at which a valuation is locally maximal.
* `Update.cumul`, `Update.strictLift`: the cumulative and the strict lift of an update to plural
  states, `Set.LiftRel` of its relation and the images of its selections.
* `Update.dist`: an update of plural states applied to each row's singleton state.
* `CCP.guard`, `CCP.might`, `CCP.must`, `CCP.negTest`: whole-state tests.
* `CCP.IsEliminative`, `CCP.IsTest`, `CCP.IsDistributive`, `CCP.IsClassical`: the classification of
  transformers.
* `CCP.up`, `CCP.down`: the content–update coercions.
* `CCP.lower`: the inverse of `SetRel.image` on distributive transformers.

## Main results

* `Update S` is a `Monoid` under sequencing (scoped); tests are its subidentities, by definition.
* `Update.dom_test`, `Update.preimage_test`, `Update.core_test`, `Update.test_comp_test`: the
  calculus of tests.
* `Update.IsTest.eq_test_dom`, `CCP.IsTest.eq_guard`: a test is the test of its truth condition, a
  guard of its acceptance condition.
* `Update.lower_image`, `CCP.image_lower`: the image and `lower` are mutually inverse on
  distributive transformers.
* `Update.strictLift_subset_cumul`, `Update.singleton_mem_strictLift_iff`: a strict lift is a
  cumulative one, and takes a one-row state to a one-row state.
* `CCP.isClassical_iff_up_down_eq`, `CCP.exists_eq_image_test_iff`: the classical transformers are
  exactly the static ones — `up` of their own content, the
images of tests; `CCP.might_not_isDistributive` separates.

## Implementation notes

An update is a mathlib relation on states. Sequencing is composition of relations, truth at a state
is membership in the domain, and the strongest postcondition, the weakest precondition and its dual
are the image, the preimage and the core (`SetRel.image`, `SetRel.preimage`, `SetRel.core`). What is
added here is the tests and the static connectives built from them.

The algebraic instances are scoped, since an update abbreviates a set of pairs and a context change
potential a function type. Sequencing distributes over arbitrary unions by mathlib's
`SetRel.comp_sUnion` and `SetRel.sUnion_comp`, and the image is left adjoint to the core by
`SetRel.image_core_gc`.

The antidomain does not validate double-negation elimination, and the whole-state test of failure
(`CCP.negTest`) is not negation by set difference (`CCP.neg`); the repairs and comparisons
particular to a framework are in the studies. Groenendijk and Stokhof's entailment notions are in
`Studies/GroenendijkStokhof1991.lean`. Acceptance and the consequence relations of dynamic meanings
are in `Consequence.lean`, and the monadic reading of the pair is in `Collapse.lean`.

## References

* [J. Groenendijk and M. Stokhof, *Dynamic Predicate Logic*][groenendijk-stokhof-1991]
* [M. Hollenberg, *An Equational Axiomatization of Dynamic Negation and Relational
  Composition*][hollenberg-1997]
* [H. Kamp and U. Reyle, *From Discourse to Logic*][kamp-reyle-1993]
* [R. Muskens, *Combining Montague Semantics and Discourse Representation*][muskens-1996]
* [I. Heim, *The Semantics of Definite and Indefinite Noun Phrases*][heim-1982]
* [I. Heim, *On the Projection Problem for Presuppositions*][heim-1983]
* [J. Groenendijk and M. Stokhof, *Two Theories of Dynamic Semantics*][groenendijk-stokhof-1990]
* [F. Veltman, *Defaults in Update Semantics*][veltman-1996]
* [R. Muskens, J. van Benthem, and A. Visser, *Dynamics*][muskens-van-benthem-visser-2011]
* [J. van Benthem, *Essays in Logical Semantics*][van-benthem-1986]
* [D. Rothschild and S. Yalcin, *Three Notions of Dynamicness in Language*][rothschild-yalcin-2016]
* [A. Gillies, *On Groenendijk and Stokhof's "Dynamic Predicate Logic"*][gillies-2022]
* [A. Brasoveanu, *Decomposing Modal Quantification*][brasoveanu-2010]
* [S. Beck and U. Sauerland, *Cumulation Is Needed: A Reply to Winter (2000)*][beck-sauerland-2000]
* [S. Minor, *Dependent Plurals and Three Levels of Multiplicity*][minor-2022]
-/

@[expose] public section

namespace DynamicSemantics

open SetRel

/-!
## Updates as relations

A relation between states says, of each input, which outputs the sentence can lead to. It may offer
several, as an existential quantifier does when it resets a variable, or none, where the sentence
fails. The sentence is true at a state when it has an output there.
-/

/-- An **update** is a relation between states, which relates each input state to its possible
outputs. It is one of the two forms a dynamic meaning takes. -/
abbrev Update (S : Type*) := SetRel S S

/-- A **condition** is a property of single states. Its test makes it an update. -/
abbrev Condition (S : Type*) := Set S

namespace Update

variable {S : Type*} {C C₁ C₂ t : Condition S} {D D₁ D₂ : Update S} {i j : S}

/-!
### The connectives

A condition is a property of states. Its test is the update that lets a state through unchanged when
the condition holds and has no output otherwise. Static meanings enter the dynamic system as tests.
-/

/-- The **test** of a condition lets a state through unchanged if the state satisfies the condition,
and has no output otherwise. -/
def test (C : Condition S) : Update S := {(a, b) | a = b ∧ b ∈ C}

@[simp] theorem mem_test : i ~[test C] j ↔ i = j ∧ j ∈ C := Iff.rfl

theorem mem_comp_test : i ~[D ○ test C] j ↔ i ~[D] j ∧ j ∈ C :=
  ⟨fun ⟨_, h, rfl, hC⟩ ↦ ⟨h, hC⟩, fun ⟨h, hC⟩ ↦ ⟨j, h, rfl, hC⟩⟩

theorem mem_test_comp : i ~[test C ○ D] j ↔ i ∈ C ∧ i ~[D] j :=
  ⟨fun ⟨_, ⟨rfl, hC⟩, h⟩ ↦ ⟨hC, h⟩, fun ⟨hC, h⟩ ↦ ⟨i, ⟨rfl, hC⟩, h⟩⟩

theorem mem_test_iff_left : i ~[test C] j ↔ i = j ∧ i ∈ C :=
  ⟨by rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩, by rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩⟩

/-!
### The update monoid

Updates are sequenced by composition: the second starts from an output of the first. The update that
changes nothing is the unit, and the update with no outputs absorbs whatever it is sequenced with.
-/

/-- Updates form a monoid under sequencing, with the update that changes nothing as unit and the
update with no outputs as zero. -/
scoped instance : MonoidWithZero (Update S) where
  mul := comp
  one := .id
  zero := ∅
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id
  zero_mul := empty_comp
  mul_zero := comp_empty

theorem mul_def (D₁ D₂ : Update S) : D₁ * D₂ = D₁ ○ D₂ := rfl

theorem one_def : (1 : Update S) = .id := rfl

theorem zero_def : (0 : Update S) = ∅ := rfl

/-!
### Tests

An update that never changes the state is a test, in Groenendijk and Stokhof's sense. A test carries
no more than a condition, the set of states it lets through, and testing two conditions in turn
tests both at once.
-/

/-- A test has an output at exactly the states that satisfy its condition. -/
@[simp] theorem dom_test (C : Condition S) : (test C).dom = C := by ext; simp

@[simp] theorem cod_test (C : Condition S) : (test C).cod = C := by ext; simp

theorem test_injective : Function.Injective (test : Condition S → Update S) :=
  Function.LeftInverse.injective dom_test

@[simp] theorem test_inj : test C₁ = test C₂ ↔ C₁ = C₂ := test_injective.eq_iff

@[simp] theorem test_univ : test (Set.univ : Condition S) = .id := by ext ⟨i, j⟩; simp

/-- Testing two conditions in turn tests their conjunction. -/
@[simp] theorem test_comp_test (C₁ C₂ : Condition S) : test C₁ ○ test C₂ = test (C₁ ∩ C₂) := by
  ext ⟨i, j⟩; simp only [mem_comp, mem_test]; grind

/-- A sequence of tests tests the conjunction of their conditions. -/
theorem prod_map_test {α : Type*} (C : α → Condition S) (l : List α) :
    (l.map fun a ↦ test (C a)).prod = test (⋂ a ∈ l, C a) := by
  induction l with
  | nil => simp [one_def]
  | cons a l ih => simp [ih, mul_def, Set.iInter_or, Set.iInter_inter_distrib]

@[simp] theorem test_empty : test (∅ : Condition S) = ∅ := by ext ⟨i, j⟩; simp

theorem test_union (C₁ C₂ : Condition S) : test (C₁ ∪ C₂) = test C₁ ∪ test C₂ := by
  ext ⟨i, j⟩; simp only [mem_test, Set.mem_union]; grind

/-- Testing that an update has an output before running it changes nothing. -/
@[simp] theorem test_dom_comp (D : Update S) : test D.dom ○ D = D := by
  ext ⟨i, j⟩
  exact ⟨fun ⟨_, ⟨rfl, _⟩, h⟩ ↦ h, fun h ↦ ⟨i, ⟨rfl, j, h⟩, h⟩⟩

@[simp] theorem image_test (C σ : Set S) : (test C).image σ = σ ∩ C := by
  ext; simp only [mem_image, mem_test]; grind

/-- The states from which a test can reach a given set of states are the members of the set that
satisfy its condition. -/
@[simp] theorem preimage_test (C t : Condition S) : (test C).preimage t = C ∩ t := by
  ext; simp only [mem_preimage, mem_test]; grind

@[simp] theorem core_test (C t : Condition S) : (test C).core t = Cᶜ ∪ t := by
  ext; simp only [mem_core, mem_test]; grind

/-- An update is a **test** if it never changes the state, that is, if each of its outputs is the
input itself ([groenendijk-stokhof-1991], Definition 11). -/
def IsTest (D : Update S) : Prop := D ⊆ .id

theorem IsTest.eq (h : IsTest D) (hij : i ~[D] j) : i = j := h hij

theorem isTest_test (C : Condition S) : IsTest (test C) := fun _ h ↦ h.1

theorem IsTest.comp (h₁ : IsTest D₁) (h₂ : IsTest D₂) : IsTest (D₁ ○ D₂) := by
  rintro ⟨_, _⟩ ⟨_, a, b⟩
  exact (h₁ a).trans (h₂ b)

/-- An update that never changes the state is the test of the condition that it has an output. This
is the remark after [groenendijk-stokhof-1991]'s Definition 11 that a test is true at an assignment
exactly when it relates the assignment to itself. -/
theorem IsTest.eq_test_dom (h : IsTest D) : D = test D.dom := by
  ext ⟨i, j⟩
  constructor
  · intro hij
    obtain rfl := h.eq hij
    exact ⟨rfl, i, hij⟩
  · rintro ⟨rfl, k, hk⟩
    obtain rfl := h.eq hk
    exact hk

theorem IsTest.cod_eq_dom (h : IsTest D) : D.cod = D.dom := by
  rw [h.eq_test_dom, cod_test, dom_test]

theorem dom_comp (D₁ D₂ : Update S) : (D₁ ○ D₂).dom = D₁.preimage D₂.dom := by
  rw [← preimage_univ_right, preimage_comp, preimage_univ_right]

theorem dom_comp_test (D : Update S) (C : Condition S) : (D ○ test C).dom = D.preimage C := by
  rw [dom_comp, dom_test]

/-!
### The antidomain

The **antidomain** of an update is the test of the states where it has no output, which interprets
negation in dynamic predicate logic. With it the updates form an antidomain monoid, as in
Hollenberg's dynamic relation algebras. Dynamic implication and disjunction are tests defined from
it.
-/

open AntidomainMonoid in
scoped instance : AntidomainMonoid (Update S) where
  antidomain D := test D.domᶜ
  isAntidomain :=
    { mul_self := fun D ↦ by
        ext ⟨i, j⟩; simp only [mul_def, zero_def, mem_test_comp]; simp; grind
      comm := fun D₁ D₂ ↦ by simp only [mul_def, test_comp_test, Set.inter_comm]
      map_map_mul_self := fun D ↦ by simp only [mul_def, dom_test, compl_compl, test_dom_comp]
      map_eq_mul := fun D₁ D₂ ↦ by
        simp only [mul_def, test_comp_test, dom_comp, dom_test]
        rw [← Set.compl_union, ← preimage_union, Set.union_compl_self, preimage_univ_right]
      map_mul_mul_self := fun D₁ D₂ ↦ by
        ext ⟨i, j⟩
        simp only [mul_def]
        rw [mem_comp_test]
        exact ⟨fun h ↦
          ⟨h, fun ⟨k, hk⟩ ↦ (mem_test_comp.1 h).1 ⟨k, j, (mem_test_comp.1 h).2, hk⟩⟩, And.left⟩ }

open AntidomainMonoid

theorem antidomain_def (D : Update S) : ∼D = test D.domᶜ := rfl

@[simp] theorem mem_antidomain : i ~[∼D] j ↔ i = j ∧ ¬∃ k, j ~[D] k := Iff.rfl

@[simp] theorem dom_antidomain (D : Update S) : (∼D).dom = D.domᶜ := dom_test _

@[simp] theorem antidomain_test (C : Condition S) : ∼(test C) = test Cᶜ := by
  rw [antidomain_def, dom_test]

/-- Taking the antidomain of an update twice gives the test that the update has an output. -/
theorem antidomain_antidomain (D : Update S) : ∼∼D = test D.dom := by
  rw [antidomain_def, dom_antidomain, compl_compl]

/-- Dynamic implication is a test. It lets a state through when every output of the first update
from that state is a state at which the second update has an output. -/
theorem dimp_eq (D₁ D₂ : Update S) : dimp D₁ D₂ = test (D₁.core D₂.dom) := by
  rw [dimp, antidomain_def, antidomain_def, mul_def, dom_comp_test, ← core_compl, compl_compl]

/-- Dynamic disjunction is a test. It lets a state through when one of the two updates has an output
there. -/
theorem dor_eq (D₁ D₂ : Update S) : dor D₁ D₂ = test (D₁.dom ∪ D₂.dom) := by
  rw [dor, antidomain_def D₁, antidomain_def D₂, mul_def, test_comp_test, antidomain_test,
    Set.compl_inter, compl_compl, compl_compl]

/-- An update is a test exactly when taking its antidomain twice returns it. -/
theorem isTest_iff_antidomain_antidomain : IsTest D ↔ ∼∼D = D :=
  ⟨fun h ↦ (antidomain_antidomain D).trans h.eq_test_dom.symm,
    fun h ↦ h ▸ antidomain_antidomain D ▸ isTest_test _⟩

/-- The conditions on states correspond one to one to the tests among the updates, and the
correspondence preserves order. A condition goes to its test, and a test goes back to the set of
states at which it has an output. -/
def testOrderIso : Condition S ≃o Test (Update S) where
  toFun C := ⟨test C, by rw [antidomain_antidomain, dom_test]⟩
  invFun D := (D : Update S).dom
  left_inv C := dom_test C
  right_inv D := Test.coe_injective ((antidomain_antidomain _).symm.trans
    D.antidomain_antidomain_coe)
  map_rel_iff' {C₁ C₂} := Test.le_iff_mul_eq.trans <| by
    change test C₁ ○ test C₂ = test C₁ ↔ C₁ ⊆ C₂
    rw [test_comp_test, test_inj, Set.inter_eq_left]

@[simp] theorem coe_testOrderIso (C : Condition S) : (testOrderIso C : Update S) = test C := rfl

@[simp] theorem testOrderIso_symm_apply (D : Test (Update S)) :
    testOrderIso.symm D = (D : Update S).dom := rfl

/-!
### Maximization

Maximization keeps, among the outputs of an update from a given input, those at which a valuation is
maximal. There may be several.
-/

/-- **Maximization** under a valuation keeps the outputs of an update at which the valuation is
maximal among the outputs from the same input. A nondeterministic update may have several such
outputs. -/
def maxBy {α : Type*} [LE α] (f : S → α) (D : Update S) : Update S :=
  {(i, j) | MaximalFor (i ~[D] ·) f j}

theorem mem_maxBy {α : Type*} [LE α] {f : S → α} :
    i ~[maxBy f D] j ↔ MaximalFor (i ~[D] ·) f j :=
  Iff.rfl

theorem mem_maxBy_iff_forall_gt {α : Type*} [Preorder α] {f : S → α} :
    i ~[maxBy f D] j ↔ i ~[D] j ∧ ∀ ⦃k⦄, f j < f k → ¬i ~[D] k :=
  and_congr_right fun _ ↦ ⟨fun h _ hlt hk ↦ hlt.not_ge (h hk hlt.le),
    fun h _ hk hle ↦ not_lt_iff_le_imp_ge.1 (fun hlt ↦ h hlt hk) hle⟩

theorem maxBy_subset {α : Type*} [LE α] (f : S → α) (D : Update S) : maxBy f D ⊆ D :=
  fun _ h ↦ h.1

theorem maxBy_eq_self {α : Type*} [Preorder α] {f : S → α}
    (h : ∀ i j, i ~[D] j → f j = f i) : maxBy f D = D := by
  ext ⟨i, j⟩
  refine ⟨And.left, fun hD ↦ ⟨hD, fun k hk _ ↦ ?_⟩⟩
  rw [h i j hD, h i k hk]

/-!
### The plural lift

A plural state is a set of states, its rows. An update of single states lifts to plural states in
two ways, cumulatively and strictly. Distribution applies an update of plural states to each row on
its own and collects the results.
-/

variable {I J : Set S}

/-- The **cumulative lift** of an update relates two plural states when every row of the input has a
successor under the update among the rows of the output, and every row of the output a predecessor
among the rows of the input. It is Brasoveanu's lift ([brasoveanu-2010] (18)), and cumulation in the
sense of [beck-sauerland-2000]. -/
def cumul (D : Update S) : Update (Set S) := {(I, J) | Set.LiftRel (· ~[D] ·) I J}

theorem mem_cumul : I ~[cumul D] J ↔ Set.LiftRel (· ~[D] ·) I J := Iff.rfl

theorem cumul_id : cumul (SetRel.id : Update S) = SetRel.id := by
  ext ⟨I, J⟩
  exact Set.liftRel_eq

theorem cumul_comp (D₁ D₂ : Update S) : cumul (D₁ ○ D₂) = cumul D₁ ○ cumul D₂ := by
  ext ⟨I, J⟩
  exact Set.liftRel_comp

theorem cumul_mono (h : D₁ ⊆ D₂) : cumul D₁ ⊆ cumul D₂ :=
  fun _ hp ↦ Set.LiftRel.imp (fun hD ↦ h hD) hp

/-- The cumulative lift of a test is the test that every row of the plural state satisfies the
condition ([brasoveanu-2010] (22)). -/
theorem cumul_test (C : Condition S) : cumul (test C) = test {I | I ⊆ C} := by
  ext ⟨I, J⟩
  simp only [cumul, Set.LiftRel, test, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hIJ : I ⊆ J := fun i hi ↦ by obtain ⟨j, hj, rfl, -⟩ := h₁ i hi; exact hj
    have hJI : J ⊆ I := fun j hj ↦ by obtain ⟨i, hi, rfl, -⟩ := h₂ j hj; exact hi
    refine ⟨Set.Subset.antisymm hIJ hJI, fun i hi ↦ ?_⟩
    obtain ⟨j, -, rfl, hC⟩ := h₁ i (hJI hi)
    exact hC
  · rintro ⟨rfl, hC⟩
    exact ⟨fun i hi ↦ ⟨i, hi, rfl, hC hi⟩, fun j hj ↦ ⟨j, hj, rfl, hC hj⟩⟩

/-- The **strict lift** of an update moves each row of a plural state to one of its successors under
the update, and the output is the set of the rows so reached ([minor-2022] (60)). An output then
never has more rows than its input, whereas the cumulative lift lets a row have several
successors. -/
def strictLift (D : Update S) : Update (Set S) :=
  {(I, J) | ∃ f : S → S, (∀ i ∈ I, i ~[D] f i) ∧ f '' I = J}

theorem mem_strictLift : I ~[strictLift D] J ↔ ∃ f : S → S, (∀ i ∈ I, i ~[D] f i) ∧ f '' I = J :=
  Iff.rfl

theorem strictLift_subset_cumul (D : Update S) : strictLift D ⊆ cumul D := by
  rintro ⟨I, J⟩ ⟨f, hf, rfl⟩
  exact ⟨fun i hi ↦ ⟨f i, Set.mem_image_of_mem f hi, hf i hi⟩,
    fun _ ⟨i, hi, hj⟩ ↦ ⟨i, hi, hj ▸ hf i hi⟩⟩

/-- The strict lift takes a state with one row to exactly the states with one row that is a
successor of it. -/
theorem singleton_mem_strictLift_iff {i : S} :
    {i} ~[strictLift D] J ↔ ∃ j, i ~[D] j ∧ J = {j} := by
  refine ⟨fun ⟨f, hf, h⟩ ↦ ⟨f i, hf i rfl, h ▸ Set.image_singleton⟩, ?_⟩
  rintro ⟨j, hj, rfl⟩
  exact ⟨fun _ ↦ j, fun k hk ↦ by rwa [Set.mem_singleton_iff.1 hk], Set.image_singleton⟩

/-- The **distributivity operator** applies an update of plural states to each row of the input
taken as a state on its own, and unites the outputs. It is (39) of [brasoveanu-2008] and (94) of
[minor-2022]. -/
def dist (D : Update (Set S)) : Update (Set S) :=
  {(I, J) | ∃ ρ : SetRel S (Set S), ρ.Nonempty ∧ ρ.dom = I ∧ ⋃₀ ρ.cod = J ∧
    ∀ p ∈ ρ, ({p.1}, p.2) ∈ D}

theorem dom_dist (D : Update (Set S)) :
    (dist D).dom = {I | I.Nonempty ∧ ∀ k ∈ I, {k} ∈ D.dom} := by
  ext I
  constructor
  · rintro ⟨J, ρ, ⟨⟨k, L⟩, hp⟩, rfl, -, hD⟩
    exact ⟨⟨k, L, hp⟩, fun k ⟨L, hk⟩ ↦ ⟨L, hD (k, L) hk⟩⟩
  · rintro ⟨⟨k, hk⟩, h⟩
    obtain ⟨L, hL⟩ := h k hk
    refine ⟨_, {p | p.1 ∈ I ∧ ({p.1}, p.2) ∈ D}, ⟨(k, L), hk, hL⟩, ?_, rfl, fun p hp ↦ hp.2⟩
    ext j
    exact ⟨fun ⟨_, hj, _⟩ ↦ hj, fun hj ↦ let ⟨L, hL⟩ := h j hj; ⟨L, hj, hL⟩⟩

/-- Distributing twice is the same as distributing once. -/
theorem dist_dist (D : Update (Set S)) : dist (dist D) = dist D := by
  ext ⟨I, J⟩
  constructor
  · rintro ⟨ρ, hne, rfl, rfl, hD⟩
    choose σ hσne hσdom hσcod hσD using hD
    have hfst {p : S × Set S} (hp : p ∈ ρ) {q : S × Set S} (hq : q ∈ σ p hp) : q.1 = p.1 :=
      Set.mem_singleton_iff.1 (hσdom p hp ▸ ⟨q.2, hq⟩)
    refine ⟨{q | ∃ p, ∃ hp : p ∈ ρ, q ∈ σ p hp}, ?_, ?_, ?_, fun q ⟨p, hp, hq⟩ ↦ hσD p hp q hq⟩
    · obtain ⟨p, hp⟩ := hne
      obtain ⟨q, hq⟩ := hσne p hp
      exact ⟨q, p, hp, hq⟩
    · ext k
      constructor
      · rintro ⟨M, p, hp, hq⟩
        obtain rfl : k = p.1 := hfst hp hq
        exact ⟨p.2, hp⟩
      · rintro ⟨L, hkL⟩
        obtain ⟨⟨k', M⟩, hq⟩ := hσne _ hkL
        obtain rfl : k' = k := hfst hkL hq
        exact ⟨M, _, hkL, hq⟩
    · ext x
      simp only [Set.mem_sUnion, SetRel.mem_cod]
      constructor
      · rintro ⟨M, ⟨k, p, hp, hq⟩, hx⟩
        exact ⟨p.2, ⟨p.1, hp⟩, hσcod p hp ▸ ⟨M, ⟨k, hq⟩, hx⟩⟩
      · rintro ⟨L, ⟨k, hkL⟩, hx⟩
        have h : ⋃₀ (σ _ hkL).cod = L := hσcod _ hkL
        rw [← h] at hx
        obtain ⟨M, ⟨k', hq⟩, hxM⟩ := hx
        exact ⟨M, ⟨k', _, hkL, hq⟩, hxM⟩
  · rintro ⟨ρ, hne, hdom, hcod, hD⟩
    refine ⟨ρ, hne, hdom, hcod, fun p hp ↦ ⟨{p}, Set.singleton_nonempty _, ?_, ?_, ?_⟩⟩
    · ext k
      simp [SetRel.mem_dom, Prod.ext_iff, eq_comm]
    · ext x
      simp [SetRel.mem_cod, Prod.ext_iff]
    · rintro q rfl
      exact hD _ hp

end Update

/-!
## Updates as functions on states

A context change potential takes a whole information state and returns one. It can look at the state
as a whole, which a relation on points cannot: whether a possibility survives may depend on which
others are present.
-/

/-- A **context change potential** is a function from information states to information states. -/
abbrev CCP (S : Type*) := Set S → Set S

namespace CCP

variable {S : Type*} {u v : CCP S}

/-- The **sequence** of two context change potentials applies the second to the result of the
first. -/
def seq (u v : CCP S) : CCP S := fun s ↦ v (u s)

/-- Context change potentials form a monoid under sequencing. -/
scoped instance : Monoid (CCP S) where
  mul := seq
  one := id
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/-- Dynamic **negation** returns the possibilities of a state that the negated update removes, that
is, the state minus its update ([heim-1982]; [veltman-1996]). -/
def neg (φ : CCP S) : CCP S := fun s ↦ s \ φ s

/-!
### Whole-state tests

A guard checks a property of the whole state, and returns either the state unchanged or the empty
state. Veltman's *might* and *must* are guards: *might* asks that an update leave something of the
state, *must* that it change nothing.
-/

/-- The **guard** of a property of whole states returns a state unchanged if it has the property,
and the empty state otherwise. -/
def guard (C : Set S → Prop) : CCP S := fun s ↦ { p ∈ s | C s }

@[simp] theorem guard_pos {C : Set S → Prop} {s} (h : C s) : guard C s = s :=
  Set.ext fun _ ↦ and_iff_left h

@[simp] theorem guard_neg {C : Set S → Prop} {s} (h : ¬C s) : guard C s = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hp ↦ h hp.2

@[simp] theorem mem_guard {C : Set S → Prop} {s : Set S} {p : S} :
    p ∈ guard C s ↔ p ∈ s ∧ C s := Iff.rfl

/-- The **negative test** of an update returns a state unchanged if the update leaves nothing of it,
and the empty state otherwise. It tests the state as a whole, and so differs from negation by set
difference. -/
def negTest (φ : CCP S) : CCP S := guard (fun s ↦ ¬ (φ s).Nonempty)

/-- **Might**, applied to an update, returns a state unchanged if the update leaves something of it,
and the empty state otherwise ([veltman-1996]). -/
def might (φ : CCP S) : CCP S := guard (fun s ↦ (φ s).Nonempty)

/-- **Must**, applied to an update, returns a state unchanged if the update does not change it, and
the empty state otherwise ([veltman-1996]). -/
def must (φ : CCP S) : CCP S := guard (fun s ↦ φ s = s)

/-!
### Classification

Three properties sort context change potentials. An eliminative one never adds possibilities, and a
test returns its input or the empty state. A distributive one treats each possibility separately.
-/

/-- A context change potential is **eliminative** if it never adds possibilities. -/
def IsEliminative (u : CCP S) : Prop := u ≤ id

theorem isEliminative_id : IsEliminative (id : CCP S) := le_rfl

theorem IsEliminative.seq (hu : IsEliminative u) (hv : IsEliminative v) :
    IsEliminative (u.seq v) :=
  fun s ↦ (hv (u s)).trans (hu s)

/-- A context change potential is a **test** if it returns either its input or the empty state, as
Veltman's tests do ([veltman-1996]). -/
def IsTest (u : CCP S) : Prop := ∀ s, u s = s ∨ u s = ∅

theorem IsTest.isEliminative (h : IsTest u) : IsEliminative u :=
  fun s p hp ↦ (h s).elim (· ▸ hp) (fun hemp ↦ (Set.notMem_empty p (hemp ▸ hp)).elim)

theorem guard_isTest (C : Set S → Prop) : IsTest (guard C) :=
  fun s ↦ (Classical.em (C s)).elim (fun h ↦ .inl (guard_pos h)) (fun h ↦ .inr (guard_neg h))

/-- A test is the guard of the property that a state has when the test returns it unchanged. -/
theorem IsTest.eq_guard (h : IsTest u) : u = guard fun s ↦ u s = s :=
  funext fun s ↦ Set.ext fun p ↦
    ⟨fun hp ↦ (h s).elim (fun hs ↦ ⟨hs ▸ hp, hs⟩)
      (fun h₀ ↦ absurd (h₀ ▸ hp) (Set.notMem_empty p)),
     fun ⟨hp, hs⟩ ↦ hs.symm ▸ hp⟩

theorem isTest_iff_exists_guard : IsTest u ↔ ∃ C, u = guard C :=
  ⟨fun h ↦ ⟨_, h.eq_guard⟩, fun ⟨C, hC⟩ ↦ hC ▸ guard_isTest C⟩

/-- A context change potential is **distributive** if its result on a state is the union of its
results on the points of the state, each taken alone. -/
def IsDistributive (φ : CCP S) : Prop :=
  ∀ s, φ s = {p | ∃ i ∈ s, p ∈ φ {i}}

/-- A context change potential is distributive exactly when it preserves arbitrary unions of
states. -/
theorem isDistributive_iff_map_sSup (φ : CCP S) :
    CCP.IsDistributive φ ↔ ∀ T : Set (Set S), φ (sSup T) = sSup (φ '' T) := by
  have h : ∀ s : Set S, {p | ∃ i ∈ s, p ∈ φ {i}} = ⨆ i ∈ s, φ {i} := fun s ↦ by ext; simp
  simp only [CCP.IsDistributive, h, sSup_image]
  exact Set.forall_map_sSup_iff.symm

/-!
### The classical fragment

A content, a set of points, updates a state by intersection. In the other direction an update has a
content, the points it does not reject when each is taken as a state on its own. An update is
classical when it is eliminative and distributive.
-/

/-- The **update of a content**, a set of points, intersects a state with the content. -/
def up (c : Set S) : CCP S := fun s ↦ s ∩ c

/-- The **content** of a context change potential is the set of points it does not reject when each
is taken as a state on its own. -/
def down (u : CCP S) : Set S := {i | (u {i}).Nonempty}

@[simp] theorem down_up (c : Set S) : down (up c) = c :=
  Set.ext fun _ ↦ Set.singleton_inter_nonempty

theorem IsEliminative.down_eq (he : IsEliminative u) : down u = {i | u {i} = {i}} :=
  Set.ext fun i ↦ show (u {i}).Nonempty ↔ u {i} = {i} from
    ⟨fun h ↦ h.subset_singleton_iff.mp (he {i}), fun h ↦ (Set.singleton_nonempty i).mono h.ge⟩

/-- A context change potential is **classical** if it is eliminative and distributive. -/
def IsClassical (u : CCP S) : Prop := IsEliminative u ∧ IsDistributive u

theorem monotone_up (c : Set S) : Monotone (up c) :=
  fun _ _ h ↦ Set.inter_subset_inter_left _ h

theorem isClassical_up (c : Set S) : IsClassical (up c) :=
  ⟨fun _ ↦ Set.inter_subset_left,
   fun _ ↦ Set.ext fun p ↦
     ⟨fun ⟨hp, hc⟩ ↦ ⟨p, hp, rfl, hc⟩, fun ⟨_, hi, hpi, hc⟩ ↦ ⟨hpi ▸ hi, hc⟩⟩⟩

/-- *Might* is not distributive in general. A point can pass as part of a larger state and yet be
rejected when it is taken alone. -/
theorem might_not_isDistributive :
    ∃ (S : Type) (φ : CCP S), ¬IsDistributive (might φ) := by
  refine ⟨Bool, (fun s ↦ {p ∈ s | p = true}), fun hD ↦ ?_⟩
  have hfalse :
      false ∈ might (fun s : Set Bool ↦ {p ∈ s | p = true}) {true, false} :=
    ⟨Or.inr rfl, true, Or.inl rfl, rfl⟩
  rw [hD] at hfalse
  obtain ⟨i, hi, hmem⟩ := hfalse
  rcases hi with rfl | rfl
  · exact Bool.false_ne_true hmem.1
  · obtain ⟨x, hx, hx'⟩ := hmem.2
    exact Bool.false_ne_true (hx ▸ hx')

end CCP

/-!
## From one to the other

A relation acts on a state through its image, the outputs of the points of the state, and a context
change potential gives a relation from each point to its outputs on that point alone. Going from a
relation to its image and back loses nothing. Starting from a context change potential, the round
trip returns it exactly when it is distributive.
-/

section RelationalBridge

variable {S : Type*} {R R' : Update S} {C : Condition S} {σ : Set S} {i j : S}

open Update SetRel

/-- The **lowering** of a context change potential is the relation that holds between a point and
each output of the potential on that point taken alone. In the other direction a relation gives a
context change potential by taking images, the strongest postcondition of
[muskens-van-benthem-visser-2011]. -/
def CCP.lower (φ : CCP S) : Update S := {p | p.2 ∈ φ {p.1}}

@[simp] theorem CCP.mem_lower {φ : CCP S} : i ~[CCP.lower φ] j ↔ j ∈ φ {i} := Iff.rfl

theorem Update.image_isDistributive (R : Update S) : CCP.IsDistributive R.image :=
  fun _ ↦ by ext; simp only [mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]; grind

/-- A relation is recovered by lowering its image, so nothing is lost in passing from relations to
functions on states. -/
theorem Update.lower_image (R : Update S) : CCP.lower R.image = R := by
  ext ⟨i, j⟩; simp

/-- Lowering a distributive context change potential and then taking the image gives it back. -/
theorem CCP.image_lower (φ : CCP S) (hd : CCP.IsDistributive φ) : (lower φ).image = φ :=
  funext fun σ ↦ (hd σ).symm

/-!
### The static fragment

The classical context change potentials are exactly the images of tests, which is van Benthem's
additivity ([van-benthem-1986]; [rothschild-yalcin-2016]; [gillies-2022]). Update semantics keeps
eliminativity, but its whole-state tests break distributivity; the random reassignment of dynamic
predicate logic does the reverse ([groenendijk-stokhof-1990], §4).
-/

theorem CCP.up_eq_image_test (C : Condition S) : CCP.up C = (test C).image :=
  funext fun σ ↦ (image_test C σ).symm

theorem Update.image_test_isEliminative (C : Condition S) :
    CCP.IsEliminative (test C).image :=
  CCP.up_eq_image_test C ▸ (CCP.isClassical_up C).1

/-- A context change potential is the image of a test exactly when it is classical. -/
theorem CCP.exists_eq_image_test_iff {φ : CCP S} :
    (∃ C : Condition S, φ = (test C).image) ↔ CCP.IsClassical φ := by
  refine ⟨fun ⟨C, hC⟩ ↦ hC ▸ ⟨image_test_isEliminative C, image_isDistributive _⟩,
    fun ⟨he, hd⟩ ↦ ⟨{i | i ∈ φ {i}}, funext fun s ↦ ?_⟩⟩
  rw [hd s, image_test]
  ext p
  exact ⟨fun ⟨i, hi, hpi⟩ ↦ have h : p = i := he {i} hpi; ⟨h ▸ hi, h ▸ hpi⟩,
    fun ⟨hp, hC⟩ ↦ ⟨p, hp, hC⟩⟩

/-- A context change potential is classical exactly when it is intersection with its own content. -/
theorem CCP.isClassical_iff_up_down_eq {φ : CCP S} :
    CCP.IsClassical φ ↔ CCP.up (CCP.down φ) = φ :=
  ⟨fun h ↦ by
      obtain ⟨C, rfl⟩ := exists_eq_image_test_iff.mpr h
      rw [← up_eq_image_test, down_up],
    fun h ↦ h ▸ CCP.isClassical_up _⟩

end RelationalBridge

end DynamicSemantics
