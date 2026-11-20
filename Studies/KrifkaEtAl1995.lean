module

public import Linglib.Semantics.Genericity.Normality

/-!
# Krifka et al. (1995): the semantics of the generic operator

[krifka-etal-1995] compare analyses of the operator GEN of characterizing sentences. Three of
them are stated here over a type `X` of cases, with restrictors and matrices sets of cases.

On *relevant quantification* GEN quantifies universally over the cases of the restrictor in a
contextually given set, `Genericity.Normality.restrict`. On the *prototype* analysis it quantifies
over the typical cases of the restrictor, where typicality is any `Genericity.Normality`. On the
*modal* analysis GEN is evaluated with a modal base `B` and an ordering source `p`, and we
define `modalGen B p R S` to hold when every case `u ∈ B ∩ R` has a case `v ∈ B` at least as
normal, `v ≤ u`, such that `S` holds of every case at least as normal as `v`.

The restrictor of `modalGen` selects the cases to start from and the matrix is evaluated at
normal cases whether or not they are cases of the restrictor. So `modalGen` is antitone in the
restrictor (`restrictorAntitone_modalGen`), it is the GEN of no normality
(`not_exists_gen_eq_modalGen`), and over a preorder with incomparable most normal cases its
matrices are not closed under intersection (`exists_modalGen_not_inter`).

## Implementation notes

* The individuals that the paper binds in the restrictor and the worlds of its modal base are
  one type of cases here, a pair of an individual and a world in the intended models, ordered by
  the ordering source on the world with the individual held fixed.
* `modalGen` follows the printed clause, in which only the first quantifier is restricted by the
  restrictor, the second by the modal base, and the third by neither. The conditional whose
  antecedent restricts the modal base throughout is `Conditional.variablyStrictImp`. The rule of
  [heim-1982] that the paper compares its clause with quantifies over the accessible cases of
  the restrictor at least as normal as every other, which on a total preorder are the normal
  cases of `(Normality.minimals p).comp (Normality.restrict B)`.

## TODO

* The situation-semantic and nonmonotonic analyses of the same section are not formalized.

## References

* [krifka-etal-1995]
* [heim-1982]
-/

@[expose] public section

namespace KrifkaEtAl1995

open Genericity Conditional Set

variable {X : Type*} {N : Normality X} {B R R' S S' : Set X} {p : Preorder X}

/-! ### Relevant quantification and prototypes -/

-- (74)
theorem exists_mem_gen_not_subset :
    ∃ (N : Normality Bool) (R S : Set Bool), N.gen R S ∧ ¬ R ⊆ S :=
  ⟨.restrict {true}, univ, {true}, fun _ hx ↦ hx.1,
    fun h ↦ Bool.false_ne_true (h (mem_univ false))⟩

/-- (79): restricted to the cases of its own matrix, every generic is true. -/
theorem gen_restrict_self : (Normality.restrict S).gen R S :=
  inter_subset_left

/-- (82): two generics with one restrictor whose matrices are disjoint on it make every generic
with that restrictor true. -/
theorem gen_of_disjoint (hS : N.gen R S) (hS' : N.gen R S') (h : Disjoint (R ∩ S) S')
    (T : Set X) : N.gen R T := by
  simp [N.normal_eq_empty_of_disjoint hS hS' h]

/-! ### The modal analysis -/

/-- (86): GEN over a modal base `B` and an ordering source `p` holds when every case of the
restrictor in `B` has a case in `B` at least as normal, every case at least as normal as which is
a case of the matrix. -/
def modalGen (B : Set X) (p : Preorder X) : Quantifier.Det X :=
  fun R S ↦ ∀ u ∈ B ∩ R, ∃ v ∈ B, p.le v u ∧ ∀ w, p.le w v → w ∈ S

theorem modalGen_iff :
    modalGen B p R S ↔ ∀ u ∈ B ∩ R, ∃ v ∈ B, p.le v u ∧ ∀ w, p.le w v → w ∈ S := Iff.rfl

theorem scopeMonotone_modalGen : (modalGen B p).ScopeMonotone :=
  fun _ _ _ h hS u hu ↦ let ⟨v, hv, hvu, hvS⟩ := hS u hu; ⟨v, hv, hvu, fun w hw ↦ h (hvS w hw)⟩

/-- The modal analysis licenses strengthening the restrictor. -/
theorem restrictorAntitone_modalGen : (modalGen B p).RestrictorAntitone :=
  fun _ _ _ h hR u hu ↦ hR u ⟨hu.1, h hu.2⟩

/-- The modal analysis is the GEN of no normality: over two cases of which the more normal is not
a case of the restrictor, a matrix true of that case alone holds and the empty matrix does not. -/
theorem not_exists_gen_eq_modalGen :
    ¬ ∃ N : Normality Bool, N.gen = modalGen univ inferInstance := by
  rintro ⟨N, hN⟩
  have h : N.gen {true} {false} := by
    rw [hN]
    exact fun u _ ↦ ⟨false, trivial, Bool.false_le u, fun w hw ↦ le_bot_iff.1 hw⟩
  have h' : N.gen {true} ∅ := fun x hx ↦
    Bool.noConfusion ((N.normal_subset _ hx).symm.trans (h hx))
  rw [hN] at h'
  obtain ⟨v, -, -, hv⟩ := h' true ⟨trivial, rfl⟩
  exact hv v le_rfl

/-- Over a preorder with incomparable most normal cases, two matrices can each hold on the modal
analysis while their intersection does not. -/
theorem exists_modalGen_not_inter :
    ∃ R S S' : Set (Set Bool),
      modalGen {s | s.Nonempty} inferInstance R S ∧ modalGen {s | s.Nonempty} inferInstance R S' ∧
        ¬ modalGen {s | s.Nonempty} inferInstance R (S ∩ S') := by
  refine ⟨{univ}, {s | s ⊆ {true}}, {s | s ⊆ {false}}, ?_, ?_, fun h ↦ ?_⟩
  · rintro u ⟨-, rfl⟩
    exact ⟨{true}, singleton_nonempty _, subset_univ _, fun _ hw ↦ hw⟩
  · rintro u ⟨-, rfl⟩
    exact ⟨{false}, singleton_nonempty _, subset_univ _, fun _ hw ↦ hw⟩
  obtain ⟨v, ⟨x, hx⟩, -, hv⟩ := h univ ⟨univ_nonempty, rfl⟩
  exact Bool.noConfusion ((hv v le_rfl).1 hx ▸ (hv v le_rfl).2 hx)

end KrifkaEtAl1995
