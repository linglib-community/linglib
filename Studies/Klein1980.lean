module

public import Linglib.Semantics.Degree.Delineation
public import Studies.Kamp1975

/-!
# Klein (1980): A Semantics for Positive and Comparative Adjectives

Klein gives gradable adjectives a semantics without degrees. An adjective is a predicate whose
extension is fixed relative to a comparison class, the comparative is derived from the positive
by quantifying over comparison classes, and degrees, where they are wanted, are recovered as
classes of entities no comparison class tells apart. The delineation vocabulary of
`Degree.Delineation` supplies comparison classes, the induced ordering, monotonicity and the
modifiers *very* and *fairly*; this file states the paper's claims about them. A nonlinear
adjective such as *clever* switches criterion with the comparison class, so its ordering ranks
two entities each above the other, which monotonicity forbids. Klein's *as … as* is Kamp's
*at least as* over all completions.

## Main statements

* `clever_not_monotone`: the delineation for *clever* is not monotone, so no measure induces it.
* `isStrictWeakOrder_outranks`: under monotonicity the ordering is a strict weak order.
* `kleinDegree_ofMeasure`: Klein's degrees agree with equality of measure.
* `preorder_le_iff_kampPreorder_le`: the equative is Kamp's *at least as* over all completions.

## Implementation notes

* The measure-induced delineation, its monotonicity and its ordering-to-degree equivalence are
  substrate (`Delineation.ofMeasure`, `Delineation.outranks_ofMeasure_iff`); the study states
  what the paper adds on top of them.

## References

* [klein-1980]
* [kamp-1975]
-/

@[expose] public section

namespace Klein1980

open Degree

/-! ### Linear and nonlinear adjectives (§2.2, §3.3)

*Tall* is linear, a single criterion and a monotone delineation, while *clever* can produce
cycles: which of two entities counts as clever depends on which criterion the comparison class
makes salient. -/

/-- Two entities, Jude and Mona. -/
inductive Clever2
  | j
  | m

/-- This delineation for *clever* applies two conflicting criteria. Jude is clever when Mona is
absent from the comparison class, Mona when Jude is, and neither when both are present. -/
def cleverDel : Delineation Clever2 :=
  ⟨fun C ↦ {x | match x with | .j => Clever2.m ∉ C | .m => Clever2.j ∉ C}⟩

theorem clever_nonlinear : cleverDel.IsNonlinear :=
  ⟨{Clever2.j, Clever2.m}, Clever2.j, Clever2.m,
    ⟨{Clever2.j}, by simp, by simp [cleverDel], by simp [cleverDel]⟩,
    ⟨{Clever2.m}, by simp, by simp [cleverDel], by simp [cleverDel]⟩⟩

theorem clever_not_monotone : ¬ cleverDel.IsMonotone :=
  fun h ↦ h.not_isNonlinear clever_nonlinear

/-! ### *Very* narrows the comparison class (eq. 42)

*Very* narrows the comparison class to the positive extension. The substrate's
`Delineation.very_subset` needs Klein's domain restriction, that a delineation classifies only
members of its class; measure-induced delineations lack it, yet *very A* entails *A* for them by
transitivity of the measure order, while being tall does not make one very tall. -/

variable {E D : Type*} [LinearOrder D]

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

theorem kleinDegree_ofMeasure (μ : E → D) {C : Set E} {a b : E} (ha : a ∈ C) (hb : b ∈ C) :
    b ∈ kleinDegree (Delineation.ofMeasure μ) C a ↔ μ a = μ b := by
  have hab : ({a, b} : Set E) ⊆ C := Set.insert_subset ha (Set.singleton_subset_iff.2 hb)
  refine ⟨fun h ↦ by_contra fun hne ↦ ?_, fun heq X _ _ _ ↦ by simp [heq]⟩
  have key := h {a, b} hab (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)
  simp only [Delineation.mem_ofMeasure, Set.mem_insert_iff, Set.mem_singleton_iff,
    exists_eq_or_imp, exists_eq_left, lt_irrefl, false_or, or_false] at key
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact lt_asymm (key.2 hlt) hlt
  · exact lt_asymm hgt (key.1 hgt)

/-! ### Non-triviality (§5) -/

/-- A delineation is non-trivial when every comparison class with at least two members contains
a member in the extension and a member outside it. -/
def IsNontrivial (d : Delineation E) : Prop :=
  ∀ C : Set E, (∃ a ∈ C, ∃ b ∈ C, a ≠ b) → ∃ u ∈ C, ∃ v ∈ C, u ∈ d C ∧ v ∉ d C

/-! ### The ordering is a strict weak order (§6)

Under monotonicity the context-relative ordering is irreflexive, transitive and has transitive
incomparability, the ordering structure a degree scale would give without degrees in the
ontology. -/

theorem isStrictWeakOrder_outranks {d : Delineation E} (hmono : d.IsMonotone) (C : Set E) :
    IsStrictWeakOrder E (d.Outranks C) where
  irrefl _ := fun ⟨_, _, h, h'⟩ ↦ h' h
  trans _ _ _ := hmono.outranks_trans
  incomp_trans _ b _ := fun ⟨hab, hba⟩ ⟨hbc, hcb⟩ ↦
    ⟨fun hac ↦ (hac.cotrans b).elim hab hbc, fun hca ↦ (hca.cotrans b).elim hcb hba⟩

theorem outranks_or_outranks_or_nondistinct (d : Delineation E) (C : Set E) (u v : E) :
    d.Outranks C u v ∨ d.Outranks C v u ∨ d.Nondistinct C u v := by
  by_cases h1 : d.Outranks C u v
  · exact .inl h1
  · by_cases h2 : d.Outranks C v u
    · exact .inr (.inl h2)
    · exact .inr (.inr (Delineation.nondistinct_of_not_outranks h1 h2))

/-! ### *As … as* and Kamp's *at least as* (§5.3)

Both quantify universally over ways of making the predicate precise, completions for Kamp and
comparison classes for Klein, so over all completions the two preorders coincide. -/

theorem preorder_le_iff_kampPreorder_le (d : Delineation E) (u v : E) :
    d.preorder.le u v ↔ (Kamp1975.kampPreorder (fun C x ↦ x ∈ d C) Set.univ).le u v :=
  d.preorder_le_iff.trans ⟨fun h c _ ↦ h c, fun h c ↦ h c (Set.mem_univ _)⟩

end Klein1980
