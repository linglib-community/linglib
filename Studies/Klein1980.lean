module

public import Linglib.Semantics.Degree.Delineation
public import Studies.Kamp1975

/-!
# Klein (1980): A Semantics for Positive and Comparative Adjectives

Klein gives gradable adjectives a semantics without degrees. Relative to a comparison class an
adjective is a partial predicate, with a positive extension, a negative extension and a gap of
borderline cases between them; the comparative is derived from the positive by quantifying over
comparison classes, and degrees, where they are wanted, are recovered as classes of entities no
comparison class tells apart. The delineation vocabulary of `Degree.Delineation` supplies the
extensions, the induced ordering, Klein's two constraints and the modifiers *very* and *fairly*;
this file states the paper's claims about them.

Under the constraints the ordering of a comparison class is a strict partial order, and where the
adjective is complete, nondistinct members being equivalent, it is a [linear ordering up to
equivalence](##linear_ordering). *Tall*, read off a measure, has no gaps, so nothing is more
determinate than it and it is [linear](##tall_linear). *Clever* is not: when mathematical skill is
relevant but no finer criterion is fixed, Jude and Mona are nondistinct, yet a context that judges
mental arithmetic ranks Jude above Mona and one that judges proof theory ranks Mona above Jude, so
the two are incommensurable rather than equivalent and *clever* is [not
linear](##clever_not_linear), though each context meets the consistency constraint and none ranks
a pair both ways. Klein's *as … as* is Kamp's *at least as* over all completions.

## Implementation notes

* The measure-induced delineation, its monotonicity and its ordering-to-degree equivalence are
  substrate (`Delineation.ofMeasure`, `Delineation.outranks_ofMeasure_iff`); the study states
  what the paper adds on top of them.
* The contexts of Klein's Figure 3 are modelled for Jude and Mona alone: `clever` is the context
  `c2`, which leaves both undecided in every class, and `clever21` and `clever22` are its
  refinements `c21` and `c22`, each deciding a class that contains both.
* Klein derives the strict partial order from both of his constraints; the consistency constraint
  (37) suffices (`Delineation.IsMonotoneOn.isStrictOrder_outranks`).

## References

* [klein-1980]
* [kamp-1975]
-/

@[expose] public section

namespace Klein1980

open Degree Delineation

variable {E D : Type*} [LinearOrder D]

/-! ### The ordering within a comparison class (§3.3) -/

/-- Klein's theorem (p. 25): an adjective that meets his constraints (36) and (37) at the class `C`
and is complete there orders `C` strictly, any two members being equivalent or ranked one way or
the other, a linear ordering up to equivalence. -/
theorem linear_ordering {d : Delineation E} {𝒟 : Set (Delineation E)} {C : Set E}
    (hm : d.IsMonotoneOn (𝒫 C)) (hs : d.IsNontrivialOn C) (hc : d.IsComplete 𝒟 C) :
    IsStrictOrder E (d.Outranks C) ∧
      ∀ u ∈ C, ∀ v ∈ C, d.Equivalent 𝒟 C u v ∨ d.Outranks C u v ∨ d.Outranks C v u :=
  ⟨hm.isStrictOrder_outranks, fun _ hu _ hv ↦ equivalent_or_outranks_or_outranks hc hs hu hv⟩

/-- *Tall*, read off a height measure, is linear: its delineation has no gaps, so nothing is more
determinate than it. -/
theorem tall_linear (μ : E → D) : IsLinear {ofMeasure μ} := by
  refine isLinear_of_forall_isGapless ?_
  rintro _ rfl
  exact isGapless_ofMeasure μ

/-! ### A nonlinear adjective (§3.3, Figure 3) -/

/-- Two entities, Jude and Mona. -/
inductive Clever2
  | j
  | m
  deriving DecidableEq

/-- *Clever* at Klein's context `c2`, where mathematical skill is relevant but no finer criterion
is fixed, leaves Jude and Mona undecided in every class. -/
def clever : Delineation Clever2 :=
  ⟨fun _ ↦ ∅, fun _ ↦ ∅, fun _ ↦ Set.disjoint_empty _⟩

/-- *Clever* at `c21`, which judges mental arithmetic: a class containing Jude and Mona puts Jude
in the positive extension and Mona in the negative one. -/
def clever21 : Delineation Clever2 where
  pos X := {x | x = .j ∧ .j ∈ X ∧ .m ∈ X}
  neg X := {x | x = .m ∧ .j ∈ X ∧ .m ∈ X}
  disjoint_pos_neg _ := Set.disjoint_left.2 fun _ hj hm ↦ absurd (hj.1.symm.trans hm.1) (by decide)

/-- *Clever* at `c22`, which judges proof theory: a class containing Jude and Mona puts Mona in
the positive extension and Jude in the negative one. -/
def clever22 : Delineation Clever2 where
  pos X := {x | x = .m ∧ .j ∈ X ∧ .m ∈ X}
  neg X := {x | x = .j ∧ .j ∈ X ∧ .m ∈ X}
  disjoint_pos_neg _ := Set.disjoint_left.2 fun _ hm hj ↦ absurd (hm.1.symm.trans hj.1) (by decide)

/-- The contexts of Figure 3 for Jude and Mona: `c2` and its two refinements. -/
def cleverContexts : Set (Delineation Clever2) := {clever, clever21, clever22}

theorem clever_le_clever21 : clever ≤ clever21 :=
  le_def.2 fun _ ↦ ⟨Set.empty_subset _, Set.empty_subset _⟩

theorem clever_le_clever22 : clever ≤ clever22 :=
  le_def.2 fun _ ↦ ⟨Set.empty_subset _, Set.empty_subset _⟩

-- At `c2` neither (34) nor (35) is true: Jude and Mona are nondistinct.
theorem nondistinct_clever : clever.Nondistinct Set.univ .j .m :=
  fun _ _ _ _ ↦ ⟨Iff.rfl, Iff.rfl⟩

-- (34) is true at `c21` and (35) at `c22`.
theorem outranks_clever21 : clever21.Outranks Set.univ .j .m :=
  ⟨Set.univ, subset_rfl, ⟨rfl, trivial, trivial⟩, ⟨rfl, trivial, trivial⟩⟩

theorem outranks_clever22 : clever22.Outranks Set.univ .m .j :=
  ⟨Set.univ, subset_rfl, ⟨rfl, trivial, trivial⟩, ⟨rfl, trivial, trivial⟩⟩

theorem isMonotone_clever21 : clever21.IsMonotone := by
  rintro - - - - a b ⟨rfl, -⟩ ⟨rfl, -⟩
  exact ⟨fun h ↦ absurd h.1 (by decide), fun h ↦ absurd h.1 (by decide)⟩

theorem isMonotone_clever22 : clever22.IsMonotone := by
  rintro - - - - a b ⟨rfl, -⟩ ⟨rfl, -⟩
  exact ⟨fun h ↦ absurd h.1 (by decide), fun h ↦ absurd h.1 (by decide)⟩

/-- *Clever* is not linear: Jude and Mona are nondistinct at `c2`, but its refinement `c21` tells
them apart, so they are incommensurable rather than equivalent (§3.3). -/
theorem clever_not_linear : ¬ IsLinear cleverContexts := fun h ↦ by
  have := h clever (Set.mem_insert _ _) Set.univ .j trivial .m trivial nondistinct_clever clever21
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) clever_le_clever21 Set.univ subset_rfl trivial
    trivial
  exact absurd (this.1.1 ⟨rfl, trivial, trivial⟩).1 (by decide)

/-! ### *Very* narrows the comparison class (eq. 42)

*Very* narrows the comparison class to the positive extension. The substrate's
`Delineation.very_subset` needs Klein's domain restriction, that a delineation classifies only
members of its class; measure-induced delineations lack it, yet *very A* entails *A* for them by
transitivity of the measure order, while being tall does not make one very tall. -/

theorem very_ofMeasure_subset (μ : E → D) (C : Set E) :
    (Delineation.ofMeasure μ).very C ⊆ Delineation.ofMeasure μ C :=
  fun _ ⟨_, ⟨z, hz, hlt'⟩, hlt⟩ ↦ ⟨z, hz, hlt'.trans hlt⟩

theorem exists_mem_not_mem_very :
    ∃ x : Fin 3, x ∈ Delineation.ofMeasure id Set.univ ∧
      x ∉ (Delineation.ofMeasure id).very Set.univ := by
  refine ⟨1, ⟨0, Set.mem_univ _, by decide⟩, ?_⟩
  rintro ⟨y, ⟨z, -, hzy⟩, hy⟩
  simp only [id] at hzy hy
  omega

/-! ### Degrees recovered (§4.2, eq. 62)

Degrees are dispensable but recoverable: the degree of `u` in a comparison class is the class
of entities nondistinct from `u`, so degrees emerge from comparison classes rather than being
primitive. -/

/-- Klein's degree of `u` at a comparison class is the set of entities nondistinct from `u`. -/
def kleinDegree (d : Delineation E) (C : Set E) (u : E) : Set E :=
  {v | d.Nondistinct C u v}

/-- For measure-induced delineations, two entities share a Klein degree iff they share a
measure value. -/
theorem kleinDegree_ofMeasure (μ : E → D) {C : Set E} {a b : E} (ha : a ∈ C) (hb : b ∈ C) :
    b ∈ kleinDegree (Delineation.ofMeasure μ) C a ↔ μ a = μ b := by
  have hab : ({a, b} : Set E) ⊆ C := Set.insert_subset ha (Set.singleton_subset_iff.2 hb)
  refine ⟨fun h ↦ by_contra fun hne ↦ ?_, fun heq X _ _ _ ↦ by simp [heq]⟩
  have key := (h {a, b} hab (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)).1
  simp only [Delineation.mem_ofMeasure, Set.mem_insert_iff, Set.mem_singleton_iff,
    exists_eq_or_imp, exists_eq_left, lt_irrefl, false_or, or_false] at key
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact lt_asymm (key.2 hlt) hlt
  · exact lt_asymm hgt (key.1 hgt)

/-! ### *As … as* and Kamp's *at least as* (§5.3)

Both quantify universally over ways of making the predicate precise, completions for Kamp and
comparison classes for Klein, so over all completions the two preorders coincide. -/

/-- Klein's preorder is Kamp's over all completions of the same extension function. -/
theorem preorder_le_iff_kampPreorder_le (d : Delineation E) (u v : E) :
    d.preorder.le u v ↔ (Kamp1975.kampPreorder (fun C x ↦ x ∈ d C) Set.univ).le u v :=
  d.preorder_le_iff.trans ⟨fun h c _ ↦ h c, fun h c ↦ h c (Set.mem_univ _)⟩

end Klein1980
