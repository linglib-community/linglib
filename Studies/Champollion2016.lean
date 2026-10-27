module

public import Linglib.Core.Order.UpperLower.Closure
public import Linglib.Semantics.Reference.ChoiceFunction
public import Linglib.Semantics.Composition.Coordinator
public import Linglib.Fragments.English.Coordination
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Sups

/-!
# Champollion 2016: noun coordination and the intersective theory of conjunction

Champollion argues that *and* has one lexical entry, the intersection of Partee and Rooth, and
that its collective uses, as in *a man and woman met*, come from silent operators of Winter that
raise each noun to a quantifier and keep the minimal sets of the conjunction. Pluralities are
sets. Existential Raising sends a noun to the upper closure of its singletons, and the upper
closure takes the set product `⊻` to intersection and union to union, so the derivation yields
the man–woman pairs for *and* and only singletons for *or*. Choice functions closed above
Minimization repair the case of overlapping nouns and give the mixtures that *ten men and women*
counts. The collective entry of Heycock and Zamparelli is the set product itself, which agrees
with intersection on upward-entailing conjuncts and overgenerates on the others.

## Main definitions

* `existentialRaising`, `minimization`, `predicateDistributivity`: ER (12), MIN (19), PDIST (27)
* `choiceRaising`, `distributiveChoiceRaising`: CR (46) and DCR (78) under a choice function
* `determinerFitting`: DFIT (92)

## Main results

* `minimization_and_existentialRaising`: Minimization after Existential Raising keeps
  the singletons of the overlap and the pairs from the differences (p. 580), the man–woman pairs
  (20) for disjoint nouns
* `minimization_and_Ici`: Minimization of two principal filters is their join
* `exists_mem_minimization_choiceRaising_iff`,
  `exists_mem_minimization_distributiveChoiceRaising_iff`: Choice Closure above Minimization
  gives every pair (57) and every mixture (80)
* `inter_setOf_ncard_minimization_existentialRaising_predicateDistributivity`: no numeral above
  two counts the Existential Raising of plural nouns (76)
* `minimization_or_existentialRaising`, `determinerFitting_every_and_iff_or`:
  *or* is never collective, and *every cat and dog* is *every cat or dog* (95), (96), (99)
* `sups_eq_and`, `sups_noMan_noWoman`, `sups_individual_card`: the set product (101)
  is intersection on upper sets and overgenerates in (103) and (105)

## Implementation notes

A plurality is a `Set E` and a property of pluralities a `Set (Set E)`, as in the paper. The
determiner *a* is `Quantifier.GQ.some`, the Montague lift is `Quantifier.NP.individual`, *and* and
*or* are what the English coordinators denote, `Coordinator.denote`, and Choice Closure quantifies
over `ChoiceFunction`, whose totality turns the definedness condition `N ≠ ∅` of Choice
Raising into a hypothesis. The counterexamples to the set product read Heycock and Zamparelli's sets
of singletons as the individuals they contain, and (76) applies the numeral at the type of the sets
it counts. The paper's (99a) writes `MIN(ER(cat)) or MIN(ER(dog))` for the `MIN(ER(cat) or ER(dog))`
of its prose and (99b), and (83c) swaps the Americans and Russians of (82a) and (83b).

## TODO

The scope constraints on Choice Closure (§4.4), determiner doubling for the ten-people reading
(§5.1), the split scope of indefinite numerals (84)–(87), and Winter's pair semantics (§7.2) are
not formalized.

## References

* [champollion-2016-coordination]
* [partee-rooth-1983]
* [winter-2001b]
* [heycock-zamparelli-2005]
* [bergmann-1982]
-/

@[expose] public section

namespace Champollion2016

open Quantifier Quantifier.NP Set SetFamily English.Coordination

private theorem and_denote {α : Type*} [CompleteBooleanAlgebra α] (s : Set α) :
    and_.denote s = sInf s :=
  Coordinator.denote_of_conjunctive rfl s

private theorem or_denote {α : Type*} [CompleteBooleanAlgebra α] (s : Set α) :
    or_.denote s = sSup s :=
  Coordinator.denote_of_disjunctive rfl s

variable {α E : Type*}

/-! ### The operators -/

/-- **Existential Raising** (12) sends `N` to the sets that meet it. At any type it is the
indefinite article *a* (23). -/
def existentialRaising (N : Set α) : Set (Set α) := {P | GQ.some N P}

@[simp]
theorem mem_existentialRaising {N P : Set α} : P ∈ existentialRaising N ↔ ∃ x ∈ N, x ∈ P :=
  Iff.rfl

/-- **Minimization** (19) keeps the minimal sets of `Q`. -/
def minimization (Q : Set (Set E)) : Set (Set E) := {P | Minimal (· ∈ Q) P}

-- (19b)
theorem mem_minimization_iff {Q : Set (Set E)} {P : Set E} :
    P ∈ minimization Q ↔ P ∈ Q ∧ ∀ P' ⊂ P, P' ∉ Q :=
  minimal_iff_forall_lt

/-- **Predicate Distributivity** (27) sends `P'` to its nonempty subsets. A plural noun is its
singular under this operator (72). -/
def predicateDistributivity (P' : Set E) : Set (Set E) := {P | P.Nonempty ∧ P ⊆ P'}

/-- **Choice Raising** (46) is the Montague lift of the member of `N` that `f` chooses. -/
def choiceRaising (f : ChoiceFunction E) (N : Set E) : Set (Set E) := {P | individual (f N) P}

/-- **Distributive Choice Raising** (78) holds of the sets that contain every member of the
plurality `f` chooses from `N`. -/
def distributiveChoiceRaising (f : ChoiceFunction (Set E)) (N : Set (Set E)) : Set (Set E) :=
  {P | GQ.every (f N) P}

/-- **Determiner Fitting** (92) applies a determiner of individuals to the union of a property
of pluralities and to the union of its meet with the scope. -/
def determinerFitting (D : GQ E) (A B : Set (Set E)) : Prop := D (⋃₀ A) (⋃₀ (A ∩ B))

/-! ### Raising and the Montague lift as upper closures -/

-- (13)
theorem existentialRaising_eq_upperClosure (N : Set α) :
    existentialRaising N = upperClosure ((fun x ↦ ({x} : Set α)) '' N) := by
  ext P; simp

theorem existentialRaising_union (N N' : Set α) :
    existentialRaising (N ∪ N') = existentialRaising N ∪ existentialRaising N' := by
  ext P; simp [or_and_right, exists_or]

theorem setOf_individual (x : E) : {P : Set E | individual x P} = Ici {x} := by
  ext P; exact (singleton_subset_iff (a := x) (s := P)).symm

theorem choiceRaising_eq_Ici (f : ChoiceFunction E) (N : Set E) :
    choiceRaising f N = Ici {f N} :=
  setOf_individual (f N)

theorem distributiveChoiceRaising_eq_Ici (f : ChoiceFunction (Set E)) (N : Set (Set E)) :
    distributiveChoiceRaising f N = Ici (f N) :=
  rfl

-- (79)
theorem distributiveChoiceRaising_eq_setOf (f : ChoiceFunction (Set E)) {N : Set (Set E)}
    (h : (f N).Nonempty) :
    distributiveChoiceRaising f N = {P | f N ∈ predicateDistributivity P} := by
  ext P; exact (and_iff_right h).symm

/-! ### Raising, Intersection, Minimization -/

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

-- (18)
theorem and_existentialRaising (N N' : Set E) :
    and_.denote {existentialRaising N, existentialRaising N'} =
      (upperClosure {P : Set E | ∃ x ∈ N, ∃ y ∈ N', P = {x, y}} : Set (Set E)) := by
  rw [and_denote, sInf_pair, existentialRaising_eq_upperClosure,
    existentialRaising_eq_upperClosure, ← image_singleton_sups, upperClosure_sups]
  rfl

/-- The minimal sets containing an `N` and an `N'` are the singletons of their overlap and the pairs
drawn from their two differences (journal p. 580). -/
theorem minimization_and_existentialRaising (N N' : Set E) :
    minimization (and_.denote
      {existentialRaising N, existentialRaising N'}) =
      {P | ∃ x ∈ N ∩ N', P = {x}} ∪ {P | ∃ x ∈ N \ N', ∃ y ∈ N' \ N, P = {x, y}} := by
  ext P
  rw [minimization, mem_ofPred_eq, and_existentialRaising]
  refine minimal_mem_upperClosure_iff.trans ⟨?_, ?_⟩
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
theorem minimization_and_existentialRaising_of_disjoint {N N' : Set E}
    (h : Disjoint N N') :
    minimization (and_.denote
      {existentialRaising N, existentialRaising N'}) =
      {P | ∃ x ∈ N, ∃ y ∈ N', P = {x, y}} := by
  rw [minimization_and_existentialRaising, disjoint_iff_inter_eq_empty.mp h,
    sdiff_eq_left.mpr h, sdiff_eq_left.mpr h.symm]
  simp

-- (42)
theorem minimization_and_existentialRaising_self (N : Set E) :
    minimization (and_.denote
      {existentialRaising N, existentialRaising N}) =
      (fun x ↦ ({x} : Set E)) '' N := by
  rw [minimization_and_existentialRaising]
  ext P
  simp [eq_comm]

-- (43)
theorem minimization_and_individual_existentialRaising {N : Set E} {j : E}
    (hj : j ∈ N) :
    minimization (and_.denote {{P : Set E | individual j P},
      existentialRaising N}) = {{j}} := by
  have : {P : Set E | individual j P} = existentialRaising {j} := by
    ext P; exact ⟨fun h ↦ ⟨j, rfl, h⟩, fun ⟨_, hx, h⟩ ↦ (eq_of_mem_singleton hx) ▸ h⟩
  rw [this, minimization_and_existentialRaising]
  ext P
  simp [hj]

-- (24)
theorem mem_existentialRaising_minimization_inter_iff {N N' : Set E} (h : Disjoint N N')
    (R S : Set (Set E)) :
    S ∈ existentialRaising (minimization (and_.denote
        {existentialRaising N,
        existentialRaising N'}) ∩ R) ↔
      ∃ x ∈ N, ∃ y ∈ N', {x, y} ∈ R ∧ {x, y} ∈ S := by
  rw [minimization_and_existentialRaising_of_disjoint h]
  constructor
  · rintro ⟨_, ⟨⟨x, hx, y, hy, rfl⟩, hR⟩, hS⟩
    exact ⟨x, hx, y, hy, hR, hS⟩
  · rintro ⟨x, hx, y, hy, hR, hS⟩
    exact ⟨_, ⟨⟨x, hx, y, hy, rfl⟩, hR⟩, hS⟩

-- (29)
theorem predicateDistributivity_mem_existentialRaising_minimization_iff {N N' : Set E}
    (h : Disjoint N N') (S : Set E) :
    predicateDistributivity S ∈ existentialRaising (minimization
        (and_.denote
        {existentialRaising N, existentialRaising N'})) ↔
      ∃ x ∈ N, ∃ y ∈ N', x ∈ S ∧ y ∈ S := by
  rw [minimization_and_existentialRaising_of_disjoint h]
  simp only [mem_existentialRaising, predicateDistributivity, mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, -, hS⟩
    exact ⟨x, hx, y, hy, hS (mem_insert x _), hS (mem_insert_of_mem x rfl)⟩
  · rintro ⟨x, hx, y, hy, hxS, hyS⟩
    exact ⟨_, ⟨x, hx, y, hy, rfl⟩, insert_nonempty x _, insert_subset hxS
      (singleton_subset_iff.2 hyS)⟩

/-! ### Choice Raising -/

/-- Minimization of the meet of two principal filters keeps only their join. This is how
Intersection and Minimization form a collective individual. -/
theorem minimization_and_Ici (a b : Set E) :
    minimization (and_.denote {Ici a, Ici b}) = {a ∪ b} := by
  rw [and_denote, sInf_pair]
  ext P
  change Minimal (· ∈ Ici a ∩ Ici b) P ↔ _
  rw [Ici_inter_Ici]
  exact minimal_ge_iff

-- (40)
theorem minimization_and_individual (x y : E) :
    minimization (and_.denote {{P : Set E | individual x P},
      {P : Set E | individual y P}}) = {{x, y}} := by
  rw [setOf_individual, setOf_individual, minimization_and_Ici, singleton_union]

-- p. 583
theorem exists_mem_choiceRaising_iff {N P : Set E} (hN : N.Nonempty) :
    (∃ f : ChoiceFunction E, P ∈ choiceRaising f N) ↔ P ∈ existentialRaising N :=
  ChoiceFunction.exists_apply_iff_some hN P

-- (53)
theorem exists_mem_minimization_individual_choiceRaising_iff {N P : Set E} (hN : N.Nonempty)
    (j : E) :
    (∃ f : ChoiceFunction E, P ∈ minimization (and_.denote
      {{P : Set E | individual j P}, choiceRaising f N})) ↔ ∃ x ∈ N, P = {j, x} := by
  simp only [setOf_individual, choiceRaising_eq_Ici, minimization_and_Ici,
    singleton_union, mem_singleton_iff]
  exact ChoiceFunction.exists_apply_iff_some hN fun x ↦ P = {j, x}

/-- With Choice Closure above Minimization, *a doctor and lawyer* (57) holds of the pair of any
doctor and any lawyer. -/
theorem exists_mem_minimization_choiceRaising_iff {N N' P : Set E} (hN : N.Nonempty)
    (hN' : N'.Nonempty) :
    (∃ f₁ f₂ : ChoiceFunction E, P ∈ minimization (and_.denote
      {choiceRaising f₁ N, choiceRaising f₂ N'})) ↔ ∃ x ∈ N, ∃ y ∈ N', P = {x, y} := by
  simp only [choiceRaising_eq_Ici, minimization_and_Ici, singleton_union,
    mem_singleton_iff]
  exact (ChoiceFunction.exists_apply_iff_some hN fun x ↦
    ∃ f₂ : ChoiceFunction E, P = insert x {f₂ N'}).trans (exists_congr fun x ↦
      and_congr_right fun _ ↦ ChoiceFunction.exists_apply_iff_some hN' fun y ↦ P = {x, y})

/-! ### Plurals -/

/-- Existential Raising of plural nouns followed by Minimization gives sets of at most two
pluralities `{M, W}`, which no numeral above two counts (75), (76). -/
theorem inter_setOf_ncard_minimization_existentialRaising_predicateDistributivity
    (N N' : Set E) {n : ℕ} (hn : 2 < n) :
    {Q : Set (Set E) | Q.ncard = n} ∩ minimization (and_.denote
      {existentialRaising (predicateDistributivity N),
      existentialRaising (predicateDistributivity N')}) = ∅ := by
  rw [minimization_and_existentialRaising, eq_empty_iff_forall_notMem]
  rintro _ ⟨hcard, ⟨M, -, rfl⟩ | ⟨M, -, W, -, rfl⟩⟩
  · simp only [mem_ofPred_eq, ncard_singleton] at hcard
    omega
  · have := ncard_insert_le M ({W} : Set (Set E))
    simp only [mem_ofPred_eq, ncard_singleton] at hcard this
    omega

/-- With Distributive Choice Raising and Choice Closure above Minimization, *men and women* (80)
denotes the unions of a plurality from each noun. -/
theorem exists_mem_minimization_distributiveChoiceRaising_iff {N N' : Set (Set E)} {P : Set E}
    (hN : N.Nonempty) (hN' : N'.Nonempty) :
    (∃ f₁ f₂ : ChoiceFunction (Set E), P ∈ minimization (and_.denote
      {distributiveChoiceRaising f₁ N, distributiveChoiceRaising f₂ N'})) ↔ P ∈ N ⊻ N' := by
  simp only [distributiveChoiceRaising_eq_Ici, minimization_and_Ici,
    mem_singleton_iff,
    mem_sups]
  exact (ChoiceFunction.exists_apply_iff_some hN fun M ↦
    ∃ f₂ : ChoiceFunction (Set E), P = M ∪ f₂ N').trans (exists_congr fun M ↦
      and_congr_right fun _ ↦ (ChoiceFunction.exists_apply_iff_some hN' fun W ↦
        P = M ∪ W).trans (exists_congr fun _ ↦ and_congr_right fun _ ↦ eq_comm))

-- (83)
theorem exists_mem_existentialRaising_minimization_distributiveChoiceRaising_iff
    {N N' : Set (Set E)} (hN : N.Nonempty) (hN' : N'.Nonempty) (S : Set (Set E)) :
    (∃ f₁ f₂ : ChoiceFunction (Set E), S ∈ existentialRaising (minimization
      (and_.denote {distributiveChoiceRaising f₁ N,
        distributiveChoiceRaising f₂ N'}))) ↔
      ∃ M ∈ N, ∃ W ∈ N', M ∪ W ∈ S := by
  simp only [distributiveChoiceRaising_eq_Ici, minimization_and_Ici,
    mem_existentialRaising, mem_singleton_iff, exists_eq_left]
  exact (ChoiceFunction.exists_apply_iff_some hN fun M ↦
    ∃ f₂ : ChoiceFunction (Set E), M ∪ f₂ N' ∈ S).trans (exists_congr fun M ↦
      and_congr_right fun _ ↦ ChoiceFunction.exists_apply_iff_some hN' fun W ↦ M ∪ W ∈ S)

/-! ### *And* and *or* -/

/-- Minimization after Existential Raising of a disjunction keeps only singletons, so *or* is
never collective (§6.2). -/
theorem minimization_or_existentialRaising (N N' : Set E) :
    minimization (or_.denote
      {existentialRaising N, existentialRaising N'}) =
      (fun x ↦ ({x} : Set E)) '' (N ∪ N') := by
  have hanti : IsAntichain (· ≤ ·) ((fun x ↦ ({x} : Set E)) '' (N ∪ N')) := by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ hne hle
    exact hne (by rw [singleton_subset_singleton.mp hle])
  rw [or_denote, sSup_pair]
  ext P
  change Minimal (· ∈ existentialRaising N ∪ existentialRaising N') P ↔ _
  rw [← existentialRaising_union, existentialRaising_eq_upperClosure]
  exact hanti.minimal_mem_upperClosure_iff_mem

-- p. 604
theorem determinerFitting_some_iff {A B : Set (Set E)} (hB : ∅ ∉ B) :
    determinerFitting GQ.some A B ↔ GQ.some A B := by
  refine ⟨fun ⟨_, _, P, hP, _⟩ ↦ ⟨P, hP⟩, fun ⟨P, hA, hB'⟩ ↦ ?_⟩
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr fun h ↦ hB (h ▸ hB')
  exact ⟨x, ⟨P, hA, hx⟩, P, ⟨hA, hB'⟩, hx⟩

-- (94)
theorem determinerFitting_no_predicateDistributivity_iff (N : Set E) (S : Set (Set E)) :
    determinerFitting GQ.no (predicateDistributivity N) S ↔
      ¬ ∃ x ∈ N, ∃ P ∈ S, x ∈ P ∧ P ⊆ N := by
  refine ⟨fun h ⟨x, hx, P, hPS, hxP, hPN⟩ ↦ h x ⟨{x}, ⟨singleton_nonempty x,
    singleton_subset_iff.2 hx⟩, mem_singleton x⟩ ⟨P, ⟨⟨⟨x, hxP⟩, hPN⟩, hPS⟩, hxP⟩,
    fun h x _ ⟨P, ⟨⟨_, hPN⟩, hPS⟩, hxP⟩ ↦ h ⟨x, hPN hxP, P, hPS, hxP, hPN⟩⟩

-- (95)
theorem determinerFitting_every_minimization_and {N N' : Set E} (h : Disjoint N N')
    (hN : N.Nonempty) (hN' : N'.Nonempty) (S : Set E) :
    determinerFitting GQ.every (minimization (and_.denote
      {existentialRaising N, existentialRaising N'})) (predicateDistributivity S) ↔
      GQ.every (or_.denote {N, N'}) S := by
  rw [minimization_and_existentialRaising_of_disjoint h,
    or_denote, sSup_pair]
  obtain ⟨x₀, hx₀⟩ := hN
  obtain ⟨y₀, hy₀⟩ := hN'
  refine ⟨fun hD z hz ↦ ?_, fun hS z ⟨_, ⟨x, hx, y, hy, rfl⟩, hz⟩ ↦ ⟨_, ⟨⟨x, hx, y, hy, rfl⟩,
    insert_nonempty x _, insert_subset (hS x (Or.inl hx)) (singleton_subset_iff.2
      (hS y (Or.inr hy)))⟩, hz⟩⟩
  · have hz' : z ∈ ⋃₀ {P | ∃ x ∈ N, ∃ y ∈ N', P = {x, y}} := by
      rcases hz with hz | hz
      exacts [⟨_, ⟨z, hz, y₀, hy₀, rfl⟩, mem_insert z _⟩,
        ⟨_, ⟨x₀, hx₀, z, hz, rfl⟩, mem_insert_of_mem x₀ rfl⟩]
    obtain ⟨_, ⟨-, -, hP⟩, hzP⟩ := hD z hz'
    exact hP hzP

-- (99)
theorem determinerFitting_every_minimization_or (N N' S : Set E) :
    determinerFitting GQ.every (minimization (or_.denote
      {existentialRaising N, existentialRaising N'})) (predicateDistributivity S) ↔
      GQ.every (or_.denote {N, N'}) S := by
  rw [minimization_or_existentialRaising, or_denote, sSup_pair]
  refine ⟨fun hD z hz ↦ ?_, fun hS z ⟨_, ⟨x, hx, rfl⟩, hz⟩ ↦ ⟨{x}, ⟨⟨x, hx, rfl⟩,
    singleton_nonempty x, singleton_subset_iff.2 (hS x hx)⟩, hz⟩⟩
  obtain ⟨_, ⟨-, -, hP⟩, hzP⟩ := hD z ⟨{z}, ⟨z, hz, rfl⟩, mem_singleton z⟩
  exact hP hzP

/-- *Every cat and dog* and *every cat or dog* agree, which solves the universal half of
Bergmann's puzzle (95), (96), (99). -/
theorem determinerFitting_every_and_iff_or {N N' : Set E} (h : Disjoint N N')
    (hN : N.Nonempty) (hN' : N'.Nonempty) (S : Set E) :
    determinerFitting GQ.every (minimization (and_.denote
      {existentialRaising N, existentialRaising N'})) (predicateDistributivity S) ↔
      determinerFitting GQ.every (minimization (or_.denote
        {existentialRaising N, existentialRaising N'})) (predicateDistributivity S) :=
  (determinerFitting_every_minimization_and h hN hN' S).trans
    (determinerFitting_every_minimization_or N N' S).symm

-- (97), (98)
theorem determinerFitting_some_minimization_and {N N' : Set E} (h : Disjoint N N')
    (S : Set E) :
    determinerFitting GQ.some (minimization (and_.denote
      {existentialRaising N, existentialRaising N'})) (predicateDistributivity S) ↔
      GQ.some N S ∧ GQ.some N' S := by
  rw [determinerFitting_some_iff fun h ↦ Set.not_nonempty_empty
    (h : ∅ ∈ predicateDistributivity S).1]
  change predicateDistributivity S ∈ existentialRaising _ ↔ _
  rw [predicateDistributivity_mem_existentialRaising_minimization_iff h]
  exact ⟨fun ⟨x, hx, y, hy, hxS, hyS⟩ ↦ ⟨⟨x, hx, hxS⟩, y, hy, hyS⟩,
    fun ⟨⟨x, hx, hxS⟩, y, hy, hyS⟩ ↦ ⟨x, hx, y, hy, hxS, hyS⟩⟩

-- (98), (97)
theorem some_or_and_not_determinerFitting_some {N N' S : Set E} (h : Disjoint N N')
    {x : E} (hx : x ∈ N) (hxS : x ∈ S) (hN'S : Disjoint N' S) :
    GQ.some (or_.denote {N, N'}) S ∧
      ¬ determinerFitting GQ.some (minimization (and_.denote
        {existentialRaising N, existentialRaising N'})) (predicateDistributivity S) := by
  rw [determinerFitting_some_minimization_and h,
    or_denote, sSup_pair]
  exact ⟨⟨x, Or.inl hx, hxS⟩, fun ⟨_, y, hy, hyS⟩ ↦ disjoint_left.mp hN'S hy hyS⟩

/-! ### The collective theory -/

-- (101)
theorem and_subset_sups [Lattice α] (Q Q' : Set α) :
    and_.denote {Q, Q'} ⊆ Q ⊻ Q' := by
  rw [and_denote, sInf_pair]
  exact fun a h ↦ ⟨a, h.1, a, h.2, sup_idem a⟩

/-- On upward-entailing conjuncts the collective and the intersective entries agree (p. 608). -/
theorem sups_eq_and [Lattice α] {Q Q' : Set α} (hQ : IsUpperSet Q)
    (hQ' : IsUpperSet Q') : Q ⊻ Q' = and_.denote {Q, Q'} := by
  refine (Subset.antisymm ?_ (and_subset_sups Q Q'))
  rw [and_denote, sInf_pair]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact ⟨hQ le_sup_left ha, hQ' le_sup_right hb⟩

-- (102), (20)
theorem sups_setOf_ncard_eq_one {N N' : Set E} (h : Disjoint N N') :
    {A | A.ncard = 1 ∧ A ⊆ N} ⊻ {B | B.ncard = 1 ∧ B ⊆ N'} =
      minimization (and_.denote {existentialRaising N,
        existentialRaising N'}) := by
  have hsing (N : Set E) : {A | A.ncard = 1 ∧ A ⊆ N} = (fun x ↦ ({x} : Set E)) '' N := by
    ext A
    simp only [mem_ofPred_eq, ncard_eq_one, mem_image]
    constructor
    · rintro ⟨⟨x, rfl⟩, hx⟩
      exact ⟨x, singleton_subset_iff.mp hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, singleton_subset_iff.2 hx⟩
  rw [hsing, hsing, image_singleton_sups,
    minimization_and_existentialRaising_of_disjoint h]

/-- When a man and a woman alone smiled, the collective entry of *No man and no woman smiled* (103a)
holds and the intersective one fails. -/
theorem sups_noMan_noWoman {N N' : Set E} (h : Disjoint N N') {x y : E} (hx : x ∈ N)
    (hy : y ∈ N') :
    {x, y} ∈ {P : Set E | GQ.no N P} ⊻ {P | GQ.no N' P} ∧
      {x, y} ∉ and_.denote
        {{P : Set E | GQ.no N P}, {P : Set E | GQ.no N' P}} := by
  rw [and_denote, sInf_pair]
  refine ⟨⟨{y}, fun z hz hzy ↦ ?_, {x}, fun z hz hzx ↦ ?_, ?_⟩, fun ⟨hno, _⟩ ↦
    hno x hx (mem_insert x _)⟩
  · exact disjoint_left.mp h hz (eq_of_mem_singleton hzy ▸ hy)
  · exact disjoint_left.mp h (eq_of_mem_singleton hzx ▸ hx) hz
  · exact (union_comm _ _).trans (singleton_union)

-- (103b)
theorem sups_individual_nobodyElse {x y : E} (hxy : x ≠ y) :
    {x, y} ∈ {P : Set E | individual y P} ⊻ {P | GQ.no (· ≠ y) P} ∧
      {x, y} ∉ and_.denote {{P : Set E | individual y P},
        {P : Set E | GQ.no (· ≠ y) P}} := by
  rw [and_denote, sInf_pair]
  exact ⟨⟨{x, y}, mem_insert_of_mem x rfl, ∅, fun _ _ h ↦ h, union_empty _⟩,
    fun ⟨_, hno⟩ ↦ hno x hxy (mem_insert x _)⟩

/-- For a condition true of three and false of four (105), the collective entry holds of John and
four women but the intersective entry does not. -/
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

example {N W : Set E} {j : E} (hj : j ∉ N) (hW : W ⊆ N) (hW4 : W.ncard = 4) :
    insert j W ∈ {P : Set E | individual j P} ⊻ {P | Odd (N ∩ P).ncard} ∧
      insert j W ∉ and_.denote {{P : Set E | individual j P},
        {P | Odd (N ∩ P).ncard}} :=
  sups_individual_card (p := Odd) hj hW hW4 (by decide) (by decide)

example {N W : Set E} {j : E} (hj : j ∉ N) (hW : W ⊆ N) (hW4 : W.ncard = 4) :
    insert j W ∈
      {P : Set E | individual j P} ⊻ {P | 1 ≤ (N ∩ P).ncard ∧ (N ∩ P).ncard ≤ 3} ∧
      insert j W ∉ and_.denote {{P : Set E | individual j P},
        {P | 1 ≤ (N ∩ P).ncard ∧ (N ∩ P).ncard ≤ 3}} :=
  sups_individual_card (p := fun n ↦ 1 ≤ n ∧ n ≤ 3) hj hW hW4 (by decide) (by decide)

end Champollion2016
