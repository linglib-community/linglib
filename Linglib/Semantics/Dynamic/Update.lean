module

public import Linglib.Logic.AntidomainMonoid
import Linglib.Core.Data.Set.Lattice.Order
public import Linglib.Core.Relation.SetRel
public import Linglib.Core.Data.Set.Functor
public import Mathlib.Tactic.TypeStar
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Use

/-!
# The update algebra

Dynamic meanings come in two forms: a relational update `Update S` relates
input states to output states, and a context change potential `CCP S`
transforms sets of states as wholes. An update is a mathlib `SetRel S S`, so
sequencing is `SetRel.comp`, truth at a state is `SetRel.dom`, and the
strongest postcondition, the weakest precondition, and its dual are
`SetRel.image`, `SetRel.preimage`, and `SetRel.core`; this file adds the
tests and the static connectives built from them. The image sends an update
to a transformer, `lower` recovers it, and the distributive transformers are
exactly the relational images. Acceptance and the consequence relations of
dynamic meanings are in `Consequence.lean`, and the monadic reading of the pair
is in `Collapse.lean`.

## Main definitions

* `Update S`, `Condition S`: relations on states, sets of states.
* `Update.test`: the test of a condition. With the antidomain `∼D = test D.domᶜ` the updates
  are an `AntidomainMonoid`, whose dynamic implication and disjunction are the tests of
  `D₁.core D₂.dom` and `D₁.dom ∪ D₂.dom`.
* `Update.IsTest`: updates that never change the state.
* `Update.maxBy`: the outputs of an update at which a valuation is locally maximal.
* `Update.cumul`, `Update.strictLift`: the cumulative and the strict lift of an update to plural
  states, `Set.LiftRel` of its relation and the images of its selections.
* `Update.dist`: an update of plural states applied to each row's singleton state.
* `CCP.guard`, `CCP.might`, `CCP.must`, `CCP.negTest`: whole-state tests.
* `CCP.IsEliminative`, `CCP.IsTest`, `CCP.IsDistributive`,
  `CCP.IsClassical`: the classification of transformers.
* `CCP.up`, `CCP.down`: the content–update coercions.
* `CCP.lower`: the inverse of `SetRel.image` on distributive transformers.

## Main results

* `Update S` is a `Monoid` under sequencing (scoped); tests are its
  subidentities, by definition.
* `Update.dom_test`, `Update.preimage_test`, `Update.core_test`,
  `Update.test_comp_test`: the calculus of tests.
* `Update.IsTest.eq_test_dom`, `CCP.IsTest.eq_guard`: a test is the test
  of its truth condition, a guard of its acceptance condition.
* `Update.lower_image`, `CCP.image_lower`: the image and `lower` are mutually inverse on
  distributive transformers.
* `Update.strictLift_subset_cumul`, `Update.singleton_mem_strictLift_iff`: a strict lift is a
  cumulative one, and takes a one-row state to a one-row state.
* `CCP.isClassical_iff_up_down_eq`, `CCP.exists_eq_image_test_iff`: the classical
  transformers are exactly the static ones — `up` of their own content, the
  images of tests; `CCP.might_not_isDistributive` separates.

## Implementation notes

The algebraic instances are scoped: `Update S` abbreviates a set of pairs and
`CCP S` a function type. Sequencing distributes over arbitrary unions by
mathlib's `SetRel.comp_sUnion` and `SetRel.sUnion_comp`, and the image is left
adjoint to the core by `SetRel.image_core_gc`.
The antidomain does not validate double-negation elimination and `CCP.negTest`
is not `CCP.neg`; the framework-specific repairs and comparisons live in the
studies. [groenendijk-stokhof-1991]'s entailment notions live in
`Studies/GroenendijkStokhof1991.lean`.

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

/-! ## The relational face -/

/-- A dynamic meaning as a binary relation between input and output states. Sequencing is
`SetRel.comp`, the trivial test `SetRel.id`, truth at a state `SetRel.dom`, the possible outputs
`SetRel.cod`, and the strongest postcondition, weakest precondition, and its dual are
`SetRel.image`, `SetRel.preimage`, and `SetRel.core`. -/
abbrev Update (S : Type*) := SetRel S S

/-- A static property of a single state; `test` embeds conditions into updates. -/
abbrev Condition (S : Type*) := Set S

namespace Update

variable {S : Type*} {C C₁ C₂ t : Condition S} {D D₁ D₂ : Update S} {i j : S}

/-! ### The connectives -/

/-- `test C` checks `C` without changing the state. -/
def test (C : Condition S) : Update S := {(a, b) | a = b ∧ b ∈ C}

@[simp] theorem mem_test : i ~[test C] j ↔ i = j ∧ j ∈ C := Iff.rfl

theorem mem_comp_test : i ~[D ○ test C] j ↔ i ~[D] j ∧ j ∈ C :=
  ⟨fun ⟨_, h, rfl, hC⟩ ↦ ⟨h, hC⟩, fun ⟨h, hC⟩ ↦ ⟨j, h, rfl, hC⟩⟩

theorem mem_test_comp : i ~[test C ○ D] j ↔ i ∈ C ∧ i ~[D] j :=
  ⟨fun ⟨_, ⟨rfl, hC⟩, h⟩ ↦ ⟨hC, h⟩, fun ⟨hC, h⟩ ↦ ⟨i, ⟨rfl, hC⟩, h⟩⟩

theorem mem_test_iff_left : i ~[test C] j ↔ i = j ∧ i ∈ C :=
  ⟨by rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩, by rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩⟩

/-! ### The update monoid -/

/-- `Update S` is a monoid under composition with the identity as unit and the empty update as
zero (scoped, since `Update S` abbreviates a set of pairs). -/
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

/-! ### Tests -/

/-- A test's domain is its condition. -/
@[simp] theorem dom_test (C : Condition S) : (test C).dom = C := by ext; simp

@[simp] theorem cod_test (C : Condition S) : (test C).cod = C := by ext; simp

theorem test_injective : Function.Injective (test : Condition S → Update S) :=
  Function.LeftInverse.injective dom_test

@[simp] theorem test_inj : test C₁ = test C₂ ↔ C₁ = C₂ := test_injective.eq_iff

@[simp] theorem test_univ : test (Set.univ : Condition S) = .id := by ext ⟨i, j⟩; simp

/-- Sequenced tests test the conjunction. -/
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

/-- Testing its domain before an update changes nothing. -/
@[simp] theorem test_dom_comp (D : Update S) : test D.dom ○ D = D := by
  ext ⟨i, j⟩
  exact ⟨fun ⟨_, ⟨rfl, _⟩, h⟩ ↦ h, fun h ↦ ⟨i, ⟨rfl, j, h⟩, h⟩⟩

@[simp] theorem image_test (C σ : Set S) : (test C).image σ = σ ∩ C := by
  ext; simp only [mem_image, mem_test]; grind

/-- The weakest precondition of a test conjoins its condition. -/
@[simp] theorem preimage_test (C t : Condition S) : (test C).preimage t = C ∩ t := by
  ext; simp only [mem_preimage, mem_test]; grind

@[simp] theorem core_test (C t : Condition S) : (test C).core t = Cᶜ ∪ t := by
  ext; simp only [mem_core, mem_test]; grind

/-- An update is a *test* if it never changes the state
([groenendijk-stokhof-1991], Definition 11): the tests are the subidentities. -/
def IsTest (D : Update S) : Prop := D ⊆ .id

theorem IsTest.eq (h : IsTest D) (hij : i ~[D] j) : i = j := h hij

theorem isTest_test (C : Condition S) : IsTest (test C) := fun _ h ↦ h.1

theorem IsTest.comp (h₁ : IsTest D₁) (h₂ : IsTest D₂) : IsTest (D₁ ○ D₂) := by
  rintro ⟨_, _⟩ ⟨_, a, b⟩
  exact (h₁ a).trans (h₂ b)

/-- A test is the test of its own domain, the remark after [groenendijk-stokhof-1991]'s
Definition 11 that a test is true at `g` iff it relates `g` to itself; the transformer-face
mirror is `CCP.IsTest.eq_guard`. -/
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

/-! ### The antidomain

The updates are the antidomain monoid of [hollenberg-1997]'s dynamic relation algebras: the
antidomain of an update is the test of where it has no output, which interprets negation in
dynamic predicate logic. Dynamic implication and disjunction are then the tests of the
conditions `D₁.core D₂.dom` and `D₁.dom ∪ D₂.dom`. -/

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
      modusPonens := fun D₁ D₂ ↦ by
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

/-- The double antidomain of an update is the test of its domain. -/
theorem antidomain_antidomain (D : Update S) : ∼∼D = test D.dom := by
  rw [antidomain_def, dom_antidomain, compl_compl]

/-- Dynamic implication tests that every output of the first update is an input of the second. -/
theorem dimp_eq (D₁ D₂ : Update S) : dimp D₁ D₂ = test (D₁.core D₂.dom) := by
  rw [dimp, antidomain_def, antidomain_def, mul_def, dom_comp_test, ← core_compl, compl_compl]

/-- Dynamic disjunction tests that one of the updates has an output. -/
theorem dor_eq (D₁ D₂ : Update S) : dor D₁ D₂ = test (D₁.dom ∪ D₂.dom) := by
  rw [dor, antidomain_def D₁, antidomain_def D₂, mul_def, test_comp_test, antidomain_test,
    Set.compl_inter, compl_compl, compl_compl]

/-- The tests are the fixed points of the double antidomain. -/
theorem isTest_iff_antidomain_antidomain : IsTest D ↔ ∼∼D = D :=
  ⟨fun h ↦ (antidomain_antidomain D).trans h.eq_test_dom.symm,
    fun h ↦ h ▸ antidomain_antidomain D ▸ isTest_test _⟩

/-! ### Maximization -/

/-- Maximization under a valuation `f` keeps the outputs of `D` at which `f` is maximal among
the outputs. The maxima are local, since a nondeterministic `D` may have several. -/
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

/-! ### The plural lift -/

variable {I J : Set S}

/-- The cumulative lift of an update to plural states ([brasoveanu-2010] (18)): the relation
lifting `Set.LiftRel` of the update, which is cumulation `**` in the sense of
[beck-sauerland-2000]. Every input row has a `D`-successor among the output rows, and every output
row a `D`-predecessor among the input rows. -/
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

/-- A lifted test checks its condition at every row ([brasoveanu-2010] (22)). -/
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

/-- The strict lift of an update to plural states ([minor-2022] (60)): each input row moves to
one `D`-successor, and the output state is the image. Where the cumulative lift lets a row have
several successors, a strict output is an image of its input, so never larger. -/
def strictLift (D : Update S) : Update (Set S) :=
  {(I, J) | ∃ f : S → S, (∀ i ∈ I, i ~[D] f i) ∧ f '' I = J}

theorem mem_strictLift : I ~[strictLift D] J ↔ ∃ f : S → S, (∀ i ∈ I, i ~[D] f i) ∧ f '' I = J :=
  Iff.rfl

theorem strictLift_subset_cumul (D : Update S) : strictLift D ⊆ cumul D := by
  rintro ⟨I, J⟩ ⟨f, hf, rfl⟩
  exact ⟨fun i hi ↦ ⟨f i, Set.mem_image_of_mem f hi, hf i hi⟩,
    fun _ ⟨i, hi, hj⟩ ↦ ⟨i, hi, hj ▸ hf i hi⟩⟩

/-- From a one-row state, the strict lift moves to a one-row state. -/
theorem singleton_mem_strictLift_iff {i : S} :
    {i} ~[strictLift D] J ↔ ∃ j, i ~[D] j ∧ J = {j} := by
  refine ⟨fun ⟨f, hf, h⟩ ↦ ⟨f i, hf i rfl, h ▸ Set.image_singleton⟩, ?_⟩
  rintro ⟨j, hj, rfl⟩
  exact ⟨fun _ ↦ j, fun k hk ↦ by rwa [Set.mem_singleton_iff.1 hk], Set.image_singleton⟩

/-- The distributivity operator (39) of [brasoveanu-2008] ([minor-2022] (94)) updates the singleton
state of every input row separately and glues the outputs together. -/
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

/-- Distributing twice distributes once. -/
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

/-! ## The transformer face -/

/-- A context change potential is a transformer of whole information states. -/
abbrev CCP (S : Type*) := Set S → Set S

namespace CCP

variable {S : Type*} {u v : CCP S}

/-- Sequential composition of CCPs, in diagrammatic order. -/
def seq (u v : CCP S) : CCP S := fun s ↦ v (u s)

/-- `CCP S` is a monoid under `CCP.seq` (scoped; see the implementation notes). -/
scoped instance : Monoid (CCP S) where
  mul := seq
  one := id
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/-- Dynamic negation by set difference keeps the states that do not survive `φ`
([heim-1982]; [veltman-1996]). -/
def neg (φ : CCP S) : CCP S := fun s ↦ s \ φ s

/-! ### Whole-state tests -/

/-- `guard C` passes a state through iff it satisfies `C`, else crashes to `∅`. -/
def guard (C : Set S → Prop) : CCP S := fun s ↦ { p ∈ s | C s }

@[simp] theorem guard_pos {C : Set S → Prop} {s} (h : C s) : guard C s = s :=
  Set.ext fun _ ↦ and_iff_left h

@[simp] theorem guard_neg {C : Set S → Prop} {s} (h : ¬C s) : guard C s = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hp ↦ h hp.2

@[simp] theorem mem_guard {C : Set S → Prop} {s : Set S} {p : S} :
    p ∈ guard C s ↔ p ∈ s ∧ C s := Iff.rfl

/-- `negTest φ` passes iff `φ` crashes — a whole-state consistency test, not
the set-difference `neg` (see the implementation notes). -/
def negTest (φ : CCP S) : CCP S := guard (fun s ↦ ¬ (φ s).Nonempty)

/-- `might φ` passes iff `φ` yields a nonempty result ([veltman-1996]). -/
def might (φ : CCP S) : CCP S := guard (fun s ↦ (φ s).Nonempty)

/-- `must φ` passes iff `φ` returns its input unchanged ([veltman-1996]). -/
def must (φ : CCP S) : CCP S := guard (fun s ↦ φ s = s)

/-! ### Classification -/

/-- A transformer is *eliminative* if it never adds possibilities. -/
def IsEliminative (u : CCP S) : Prop := u ≤ id

theorem isEliminative_id : IsEliminative (id : CCP S) := le_rfl

theorem IsEliminative.seq (hu : IsEliminative u) (hv : IsEliminative v) :
    IsEliminative (u.seq v) :=
  fun s ↦ (hv (u s)).trans (hu s)

/-- A transformer is a *test* if it passes its input through or crashes to
`∅` — [veltman-1996]'s tests, `Update.IsTest` one carrier up. -/
def IsTest (u : CCP S) : Prop := ∀ s, u s = s ∨ u s = ∅

theorem IsTest.isEliminative (h : IsTest u) : IsEliminative u :=
  fun s p hp ↦ (h s).elim (· ▸ hp) (fun hemp ↦ (Set.notMem_empty p (hemp ▸ hp)).elim)

theorem guard_isTest (C : Set S → Prop) : IsTest (guard C) :=
  fun s ↦ (Classical.em (C s)).elim (fun h ↦ .inl (guard_pos h)) (fun h ↦ .inr (guard_neg h))

/-- A test is the guard of its own acceptance condition — the mirror of
`Update.IsTest.eq_test_dom`. -/
theorem IsTest.eq_guard (h : IsTest u) : u = guard fun s ↦ u s = s :=
  funext fun s ↦ Set.ext fun p ↦
    ⟨fun hp ↦ (h s).elim (fun hs ↦ ⟨hs ▸ hp, hs⟩)
      (fun h₀ ↦ absurd (h₀ ▸ hp) (Set.notMem_empty p)),
     fun ⟨hp, hs⟩ ↦ hs.symm ▸ hp⟩

theorem isTest_iff_exists_guard : IsTest u ↔ ∃ C, u = guard C :=
  ⟨fun h ↦ ⟨_, h.eq_guard⟩, fun ⟨C, hC⟩ ↦ hC ▸ guard_isTest C⟩

/-- A transformer is *distributive* if it acts per-element:
`φ s = ⋃ i ∈ s, φ {i}` — equivalently, it preserves arbitrary joins
(`isDistributive_iff_map_sSup`). -/
def IsDistributive (φ : CCP S) : Prop :=
  ∀ s, φ s = {p | ∃ i ∈ s, p ∈ φ {i}}

/-- A CCP is distributive iff it preserves arbitrary joins of states. -/
theorem isDistributive_iff_map_sSup (φ : CCP S) :
    CCP.IsDistributive φ ↔ ∀ T : Set (Set S), φ (sSup T) = sSup (φ '' T) := by
  have h : ∀ s : Set S, {p | ∃ i ∈ s, p ∈ φ {i}} = ⨆ i ∈ s, φ {i} := fun s ↦ by ext; simp
  simp only [CCP.IsDistributive, h, sSup_image]
  exact Set.forall_map_sSup_iff.symm

/-! ### The classical fragment -/

/-- The static update a content determines is intersection with it. -/
def up (c : Set S) : CCP S := fun s ↦ s ∩ c

/-- The content an update determines is the set of indices whose singleton it updates
successfully. -/
def down (u : CCP S) : Set S := {i | (u {i}).Nonempty}

@[simp] theorem down_up (c : Set S) : down (up c) = c :=
  Set.ext fun _ ↦ Set.singleton_inter_nonempty

theorem IsEliminative.down_eq (he : IsEliminative u) : down u = {i | u {i} = {i}} :=
  Set.ext fun i ↦ show (u {i}).Nonempty ↔ u {i} = {i} from
    ⟨fun h ↦ h.subset_singleton_iff.mp (he {i}), fun h ↦ (Set.singleton_nonempty i).mono h.ge⟩

/-- An update is *classical* if it is eliminative and distributive. -/
def IsClassical (u : CCP S) : Prop := IsEliminative u ∧ IsDistributive u

theorem monotone_up (c : Set S) : Monotone (up c) :=
  fun _ _ h ↦ Set.inter_subset_inter_left _ h

theorem isClassical_up (c : Set S) : IsClassical (up c) :=
  ⟨fun _ ↦ Set.inter_subset_left,
   fun _ ↦ Set.ext fun p ↦
     ⟨fun ⟨hp, hc⟩ ↦ ⟨p, hp, rfl, hc⟩, fun ⟨_, hi, hpi, hc⟩ ↦ ⟨hpi ▸ hi, hc⟩⟩⟩

/-- `might` is not distributive, since a whole-state test can pass where every per-singleton
test fails. -/
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

/-! ## The bridge -/

section RelationalBridge

variable {S : Type*} {R R' : Update S} {C : Condition S} {σ : Set S} {i j : S}

open Update SetRel

/-- `lower φ` relates `i` to the outputs of `φ` on the singleton `{i}`. The other direction is
the relational image `SetRel.image`, the strongest postcondition of
[muskens-van-benthem-visser-2011]. -/
def CCP.lower (φ : CCP S) : Update S := {p | p.2 ∈ φ {p.1}}

@[simp] theorem CCP.mem_lower {φ : CCP S} : i ~[CCP.lower φ] j ↔ j ∈ φ {i} := Iff.rfl

theorem Update.image_isDistributive (R : Update S) : CCP.IsDistributive R.image :=
  fun _ ↦ by ext; simp only [mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]; grind

/-- `lower` is a left inverse of the image, so the relational face loses nothing. -/
theorem Update.lower_image (R : Update S) : CCP.lower R.image = R := by
  ext ⟨i, j⟩; simp

/-- The image is a right inverse of `lower` on distributive transformers. -/
theorem CCP.image_lower (φ : CCP S) (hd : CCP.IsDistributive φ) : (lower φ).image = φ :=
  funext fun σ ↦ (hd σ).symm

/-! ### The static fragment

Van Benthem's additivity ([van-benthem-1986]; [rothschild-yalcin-2016];
[gillies-2022]): the classical transformers are exactly the images of tests. Update semantics
keeps eliminativity but its whole-state tests break distributivity; DPL's random reassignment
does the reverse ([groenendijk-stokhof-1990], §4). -/

theorem CCP.up_eq_image_test (C : Condition S) : CCP.up C = (test C).image :=
  funext fun σ ↦ (image_test C σ).symm

theorem Update.image_test_isEliminative (C : Condition S) :
    CCP.IsEliminative (test C).image :=
  CCP.up_eq_image_test C ▸ (CCP.isClassical_up C).1

/-- A transformer is the image of a test iff it is classical. -/
theorem CCP.exists_eq_image_test_iff {φ : CCP S} :
    (∃ C : Condition S, φ = (test C).image) ↔ CCP.IsClassical φ := by
  refine ⟨fun ⟨C, hC⟩ ↦ hC ▸ ⟨image_test_isEliminative C, image_isDistributive _⟩,
    fun ⟨he, hd⟩ ↦ ⟨{i | i ∈ φ {i}}, funext fun s ↦ ?_⟩⟩
  rw [hd s, image_test]
  ext p
  exact ⟨fun ⟨i, hi, hpi⟩ ↦ have h : p = i := he {i} hpi; ⟨h ▸ hi, h ▸ hpi⟩,
    fun ⟨hp, hC⟩ ↦ ⟨p, hp, hC⟩⟩

/-- The classical updates are exactly the static ones, with `up ∘ down` as their normal
form. -/
theorem CCP.isClassical_iff_up_down_eq {φ : CCP S} :
    CCP.IsClassical φ ↔ CCP.up (CCP.down φ) = φ :=
  ⟨fun h ↦ by
      obtain ⟨C, rfl⟩ := exists_eq_image_test_iff.mpr h
      rw [← up_eq_image_test, down_up],
    fun h ↦ h ▸ CCP.isClassical_up _⟩

end RelationalBridge

end DynamicSemantics
