module

public import Mathlib.Algebra.Group.Defs
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
* `Update.test`, `Update.neg`, `Update.impl`, `Update.disj`: the test of a
  condition, and the conditions `D.domᶜ`, `D₁.core D₂.dom`, and `D₁.dom ∪ D₂.dom`.
* `Update.IsTest`: updates that never change the state.
* `Update.maxBy`: the outputs of an update at which a valuation is locally maximal.
* `Update.cumul`, `Update.strictLift`: the cumulative and the strict lift of an update to plural
  states, `Set.LiftRel` of its relation and the images of its selections.
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
`Update.neg` does not validate double-negation elimination and `CCP.negTest`
is not `CCP.neg`; the framework-specific repairs and comparisons live in the
studies. [groenendijk-stokhof-1991]'s entailment notions live in
`Studies/GroenendijkStokhof1991.lean`.

## References

* [J. Groenendijk and M. Stokhof, *Dynamic Predicate Logic*][groenendijk-stokhof-1991]
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

/-- `neg D` holds at `i` iff `D` has no output from `i`. -/
def neg (D : Update S) : Condition S := D.domᶜ

/-- `impl D₁ D₂` holds at `i` iff every `D₁`-output from `i` has a `D₂`-output. -/
def impl (D₁ D₂ : Update S) : Condition S := D₁.core D₂.dom

/-- `disj D₁ D₂` holds at `i` iff some disjunct has an output from `i`. -/
def disj (D₁ D₂ : Update S) : Condition S := D₁.dom ∪ D₂.dom

@[simp] theorem mem_test : i ~[test C] j ↔ i = j ∧ j ∈ C := Iff.rfl

/-- A test at the end of a sequence checks the output. -/
theorem mem_comp_test : i ~[D ○ test C] j ↔ i ~[D] j ∧ j ∈ C :=
  ⟨fun ⟨_, h, rfl, hC⟩ ↦ ⟨h, hC⟩, fun ⟨h, hC⟩ ↦ ⟨j, h, rfl, hC⟩⟩

/-- A test at the start of a sequence checks the input. -/
theorem mem_test_comp : i ~[test C ○ D] j ↔ i ∈ C ∧ i ~[D] j :=
  ⟨fun ⟨_, ⟨rfl, hC⟩, h⟩ ↦ ⟨hC, h⟩, fun ⟨hC, h⟩ ↦ ⟨i, ⟨rfl, hC⟩, h⟩⟩

@[simp] theorem mem_neg : i ∈ neg D ↔ ¬∃ k, i ~[D] k := Iff.rfl

@[simp] theorem mem_impl : i ∈ impl D₁ D₂ ↔ ∀ ⦃h⦄, i ~[D₁] h → ∃ k, h ~[D₂] k := Iff.rfl

@[simp] theorem mem_disj : i ∈ disj D₁ D₂ ↔ (∃ k, i ~[D₁] k) ∨ ∃ k, i ~[D₂] k := Iff.rfl

/-- A test constrains its input and output alike. -/
theorem mem_test_iff_left : i ~[test C] j ↔ i = j ∧ i ∈ C :=
  ⟨by rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩, by rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩⟩

/-- Negation is the core of the empty condition. -/
theorem neg_eq_core_empty (D : Update S) : neg D = D.core ∅ := by
  ext; simp [neg]

/-! ### The update monoid -/

/-- `Update S` is a monoid under composition with the identity as unit (scoped, since
`Update S` abbreviates a set of pairs). -/
scoped instance : Monoid (Update S) where
  mul := comp
  one := .id
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

theorem mul_def (D₁ D₂ : Update S) : D₁ * D₂ = D₁ ○ D₂ := rfl

theorem one_def : (1 : Update S) = .id := rfl

/-! ### Tests -/

/-- A test's domain is its condition. -/
@[simp] theorem dom_test (C : Condition S) : (test C).dom = C := by ext; simp

/-- A test's codomain is its condition. -/
@[simp] theorem cod_test (C : Condition S) : (test C).cod = C := by ext; simp

/-- A test is determined by its condition. -/
theorem test_injective : Function.Injective (test : Condition S → Update S) :=
  Function.LeftInverse.injective dom_test

@[simp] theorem test_inj : test C₁ = test C₂ ↔ C₁ = C₂ := test_injective.eq_iff

/-- The trivial test is the identity. -/
@[simp] theorem test_univ : test (Set.univ : Condition S) = .id := by ext ⟨i, j⟩; simp

/-- Sequenced tests test the conjunction. -/
@[simp] theorem test_comp_test (C₁ C₂ : Condition S) : test C₁ ○ test C₂ = test (C₁ ∩ C₂) := by
  ext ⟨i, j⟩; simp only [mem_comp, mem_test]; grind

/-- Negating a test complements its condition. -/
@[simp] theorem neg_test (C : Condition S) : neg (test C) = Cᶜ := by rw [neg, dom_test]

/-- The strongest postcondition of a test is the filter by its condition. -/
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

/-- `test C` is a test. -/
theorem isTest_test (C : Condition S) : IsTest (test C) := fun _ h ↦ h.1

/-- Tests are closed under sequencing. -/
theorem IsTest.comp (h₁ : IsTest D₁) (h₂ : IsTest D₂) : IsTest (D₁ ○ D₂) := by
  rintro ⟨_, _⟩ ⟨_, a, b⟩
  exact (h₁ a).trans (h₂ b)

/-- A test is the test of its own domain ([groenendijk-stokhof-1991]'s Fact 6); the
transformer-face mirror is `CCP.IsTest.eq_guard`. -/
theorem IsTest.eq_test_dom (h : IsTest D) : D = test D.dom := by
  ext ⟨i, j⟩
  constructor
  · intro hij
    obtain rfl := h.eq hij
    exact ⟨rfl, i, hij⟩
  · rintro ⟨rfl, k, hk⟩
    obtain rfl := h.eq hk
    exact hk

/-- A test's outputs are its inputs. -/
theorem IsTest.cod_eq_dom (h : IsTest D) : D.cod = D.dom := by
  rw [h.eq_test_dom, cod_test, dom_test]

/-- Negation, implication, and disjunction in terms of the domain. -/
theorem neg_eq_compl_dom (D : Update S) : neg D = D.domᶜ := rfl

theorem impl_eq_core_dom (D₁ D₂ : Update S) : impl D₁ D₂ = D₁.core D₂.dom := rfl

theorem disj_eq_dom_union_dom (D₁ D₂ : Update S) : disj D₁ D₂ = D₁.dom ∪ D₂.dom := rfl

/-- Implication curries, an implication from a sequence being an implication to the test of an
implication. -/
theorem impl_comp (D₁ D₂ D₃ : Update S) : impl (D₁ ○ D₂) D₃ = impl D₁ (test (impl D₂ D₃)) := by
  simp only [impl_eq_core_dom, dom_test, core_comp]

/-- The domain of a sequence is the weakest precondition of the second domain. -/
theorem dom_comp (D₁ D₂ : Update S) : (D₁ ○ D₂).dom = D₁.preimage D₂.dom := by
  rw [← preimage_univ_right, preimage_comp, preimage_univ_right]

/-! ### Maximization -/

/-- Maximization under a valuation `f` keeps the outputs of `D` at which no other output of `D`
has a strictly greater value. The maxima are local, since a nondeterministic `D` may have
several. -/
def maxBy {α : Type*} [Preorder α] (f : S → α) (D : Update S) : Update S :=
  {(i, j) | i ~[D] j ∧ ∀ k, i ~[D] k → ¬f j < f k}

theorem maxBy_subset {α : Type*} [Preorder α] (f : S → α) (D : Update S) : maxBy f D ⊆ D :=
  fun _ h ↦ h.1

/-- Maximizing a valuation that no output of `D` changes is vacuous. -/
theorem maxBy_eq_self {α : Type*} [Preorder α] {f : S → α}
    (h : ∀ i j, i ~[D] j → f j = f i) : maxBy f D = D := by
  ext ⟨i, j⟩
  refine ⟨And.left, fun hD ↦ ⟨hD, fun k hk hlt ↦ ?_⟩⟩
  rw [h i j hD, h i k hk] at hlt
  exact lt_irrefl _ hlt

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

/-- The lift preserves sequencing, since a path through the intermediate rows gives the
intermediate state. -/
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

/-- A guard whose condition holds passes the state through. -/
@[simp] theorem guard_pos {C : Set S → Prop} {s} (h : C s) : guard C s = s :=
  Set.ext fun _ ↦ and_iff_left h

/-- A guard whose condition fails crashes to `∅`. -/
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

/-- The identity is eliminative. -/
theorem isEliminative_id : IsEliminative (id : CCP S) := le_rfl

/-- Sequencing preserves eliminativity. -/
theorem IsEliminative.seq (hu : IsEliminative u) (hv : IsEliminative v) :
    IsEliminative (u.seq v) :=
  fun s ↦ (hv (u s)).trans (hu s)

/-- A transformer is a *test* if it passes its input through or crashes to
`∅` — [veltman-1996]'s tests, `Update.IsTest` one carrier up. -/
def IsTest (u : CCP S) : Prop := ∀ s, u s = s ∨ u s = ∅

/-- Tests are eliminative. -/
theorem IsTest.isEliminative (h : IsTest u) : IsEliminative u :=
  fun s p hp ↦ (h s).elim (· ▸ hp) (fun hemp ↦ (Set.notMem_empty p (hemp ▸ hp)).elim)

/-- Guards are tests. -/
theorem guard_isTest (C : Set S → Prop) : IsTest (guard C) :=
  fun s ↦ (Classical.em (C s)).elim (fun h ↦ .inl (guard_pos h)) (fun h ↦ .inr (guard_neg h))

/-- A test is the guard of its own acceptance condition — the mirror of
`Update.IsTest.eq_test_dom`. -/
theorem IsTest.eq_guard (h : IsTest u) : u = guard fun s ↦ u s = s :=
  funext fun s ↦ Set.ext fun p ↦
    ⟨fun hp ↦ (h s).elim (fun hs ↦ ⟨hs ▸ hp, hs⟩)
      (fun h₀ ↦ absurd (h₀ ▸ hp) (Set.notMem_empty p)),
     fun ⟨hp, hs⟩ ↦ hs.symm ▸ hp⟩

/-- The tests are exactly the guards. -/
theorem isTest_iff_exists_guard : IsTest u ↔ ∃ C, u = guard C :=
  ⟨fun h ↦ ⟨_, h.eq_guard⟩, fun ⟨C, hC⟩ ↦ hC ▸ guard_isTest C⟩

/-- A transformer is *distributive* if it acts per-element:
`φ s = ⋃ i ∈ s, φ {i}` — equivalently, it preserves arbitrary joins
(`Collapse.lean`'s `isDistributive_iff_map_sSup`). -/
def IsDistributive (φ : CCP S) : Prop :=
  ∀ s, φ s = {p | ∃ i ∈ s, p ∈ φ {i}}

/-! ### The classical fragment -/

/-- The static update a content determines is intersection with it. -/
def up (c : Set S) : CCP S := fun s ↦ s ∩ c

/-- The content an update determines is the set of indices whose singleton it updates
successfully. -/
def down (u : CCP S) : Set S := {i | (u {i}).Nonempty}

/-- `down` retracts `up`. -/
@[simp] theorem down_up (c : Set S) : down (up c) = c :=
  Set.ext fun _ ↦ Set.singleton_inter_nonempty

/-- On eliminative updates, content is acceptance on singletons. -/
theorem IsEliminative.down_eq (he : IsEliminative u) : down u = {i | u {i} = {i}} :=
  Set.ext fun i ↦ show (u {i}).Nonempty ↔ u {i} = {i} from
    ⟨fun h ↦ h.subset_singleton_iff.mp (he {i}), fun h ↦ (Set.singleton_nonempty i).mono h.ge⟩

/-- An update is *classical* if it is eliminative and distributive. -/
def IsClassical (u : CCP S) : Prop := IsEliminative u ∧ IsDistributive u

/-- Static updates are monotone. -/
theorem monotone_up (c : Set S) : Monotone (up c) :=
  fun _ _ h ↦ Set.inter_subset_inter_left _ h

/-- Static updates are classical. -/
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

/-- Relational images are distributive. -/
theorem Update.image_isDistributive (R : Update S) : CCP.IsDistributive R.image :=
  fun _ ↦ by ext; simp only [mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]; grind

/-- `lower` is a left inverse of the image, so the relational face loses nothing. -/
theorem Update.lower_image (R : Update S) : CCP.lower R.image = R := by
  ext ⟨i, j⟩; simp

/-- The image is a right inverse of `lower` on distributive transformers. -/
theorem CCP.image_lower (φ : CCP S) (hd : CCP.IsDistributive φ) : (lower φ).image = φ :=
  funext fun σ ↦ (hd σ).symm

/-- The image reflects (and preserves) the order. -/
theorem Update.image_le_image_iff : R.image ≤ R'.image ↔ R ⊆ R' :=
  ⟨fun h ⟨i, _⟩ r ↦ by
      obtain ⟨_, rfl, r'⟩ := h {i} ⟨i, rfl, r⟩
      exact r',
    fun h _ ↦ image_subset_image_left h⟩

/-! ### The static fragment

Van Benthem's additivity ([van-benthem-1986]; [rothschild-yalcin-2016];
[gillies-2022]): the classical transformers are exactly the images of tests. Update semantics
keeps eliminativity but its whole-state tests break distributivity; DPL's random reassignment
does the reverse ([groenendijk-stokhof-1990], §4). -/

/-- `up` of a condition is the image of its test. -/
theorem CCP.up_eq_image_test (C : Condition S) : CCP.up C = (test C).image :=
  funext fun σ ↦ (image_test C σ).symm

/-- The image of a test is eliminative. -/
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
