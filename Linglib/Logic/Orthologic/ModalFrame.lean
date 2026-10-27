module

public import Linglib.Logic.Orthologic.CompatFrame
public import Linglib.Logic.Orthologic.Epistemic
public import Linglib.Logic.Modal.Basic

/-!
# Modal compatibility frames

This file defines Holliday and Mandelkern's modal compatibility frames, the possibility semantics
for `must` and `might`. A compatibility frame `F` carries an epistemic accessibility relation
`R`; necessity is the Kripke operator `□A = {x | R(x) ⊆ A}`, which is `SetRel.core R`, and
`◇A = ¬□¬A` negates with the orthocomplement of `F` rather than the Boolean complement.

Three conditions on `R` make the regular propositions of `F` an epistemic ortholattice
(`Logic/Orthologic/Epistemic.lean`). R-regularity is exactly the condition for `□` to preserve
regularity, which makes the regular propositions with `□` a modal ortholattice; reflexivity makes
it T; and over these, Knowability is exactly the condition for Wittgenstein's Law.

## Main definitions

* `Orthologic.diamond F R`: `◇A = ¬□¬A` on sets.
* `Orthologic.IsRRegular F R`, `Orthologic.IsKnowable F R`: R-regularity and Knowability.
* `Orthologic.CompatFrame.necHom`: `□` as a map on `F.Regular` preserving meets and `⊤`.

## Main results

* `Orthologic.isRRegular_iff_isRegular_core`: R-regularity iff `□` preserves regularity.
* `Orthologic.isKnowable_iff`: Knowability iff `□` reflects contradiction on regular sets.
* `Orthologic.disjoint_orthoNeg_diamond`: `¬A` and `◇A` are disjoint.
* `Orthologic.CompatFrame.isKnowable_iff_wittgensteinLaw`: over a reflexive R-regular relation,
  Knowability iff the regular propositions satisfy Wittgenstein's Law.

## Implementation notes

The paper's frame classes are conjunctions of conditions on a bare relation, stated as Prop
classes like `ModalLogic.IsSerial`: a *modal* compatibility frame is R-regular, a *T* frame is
also reflexive (`R.IsRefl`), and an *epistemic* frame also satisfies Knowability. Each theorem
assumes only the conditions it uses.

## References

* [holliday-mandelkern-2024]
-/

@[expose] public section

namespace Orthologic

open ModalLogic SetRel

variable {S : Type*} (F : CompatFrame S) (R : SetRel S S)

/-- The possibility `◇A = ¬□¬A` negates with the orthocomplement, so `x` makes `◇A` true iff
every possibility compatible with `x` accesses one compatible with an `A`-possibility
([holliday-mandelkern-2024] eq. (4)). -/
def diamond (A : Set S) : Set S :=
  orthoNeg F (R.core (orthoNeg F A))

instance [Fintype S] [DecidableRel F.compat] [∀ x y, Decidable (x ~[R] y)] (A : Set S)
    [DecidablePred (· ∈ A)] : DecidablePred (· ∈ diamond F R A) := fun x ↦
  inferInstanceAs (Decidable (x ∈ orthoNeg F (R.core (orthoNeg F A))))

/-- A relation is R-regular when a possibility accessing one compatible with `y` is compatible
with a possibility according to which `y` might obtain ([holliday-mandelkern-2024]
Definition 4.20). -/
class IsRRegular : Prop where
  /-- The condition is stated in the `◇`-free form of [holliday-mandelkern-2024] Lemma 4.21. -/
  rRegular : ∀ x y' y, x ~[R] y' → F.compat y' y →
    ∃ x', F.compat x x' ∧ ∀ x'', F.compat x' x'' → ∃ y'', x'' ~[R] y'' ∧ F.compat y'' y

/-- A relation satisfies Knowability when every possibility `x` has one at which everything
settled true by `x` is known, since all it accesses refine `x` ([holliday-mandelkern-2024]
Definition 4.26). -/
class IsKnowable : Prop where
  knowable : ∀ x, ∃ y, ∀ z, y ~[R] z → refines F z x

variable {F}

/-- Over an R-regular frame, `□` of a regular set is regular ([holliday-mandelkern-2024]
Proposition 4.22). -/
theorem isRegular_core [IsRRegular F R] {A : Set S} (hA : IsRegular F A) :
    IsRegular F (R.core A) := by
  intro x
  by_cases hx : x ∈ R.core A
  · exact Or.inl hx
  simp only [mem_core, not_forall] at hx
  obtain ⟨y, hxy, hyA⟩ := hx
  obtain hyA' | ⟨z, hyz, hz⟩ := hA y
  · exact absurd hyA' hyA
  obtain ⟨x', hxx', hx'⟩ := IsRRegular.rRegular x y z hxy hyz
  refine Or.inr ⟨x', hxx', fun x'' hx'x'' hnec ↦ ?_⟩
  obtain ⟨y'', hy'', hy''z⟩ := hx' x'' hx'x''
  exact hz y'' hy''z.symm (hnec hy'')

/-- Over an R-regular frame `¬◇A = □¬A`, since `□¬A` is regular. -/
theorem orthoNeg_diamond [IsRRegular F R] (A : Set S) :
    orthoNeg F (diamond F R A) = R.core (orthoNeg F A) :=
  orthoNeg_orthoNeg_of_isRegular F (isRegular_core R (orthoNeg_isRegular F A))

variable (F)

/-- R-regularity holds iff `□` preserves regularity, extending Proposition 4.22 of
[holliday-mandelkern-2024] by its converse. -/
theorem isRRegular_iff_isRegular_core :
    IsRRegular F R ↔ ∀ A, IsRegular F A → IsRegular F (R.core A) := by
  refine ⟨fun _ _ ↦ isRegular_core R, fun h ↦ ⟨fun x y' y hxy' hy'y ↦ ?_⟩⟩
  obtain hx | ⟨x', hxx', hx'⟩ := h _ (orthoNeg_isRegular F {y}) x
  · exact (hx hxy' y hy'y rfl).elim
  refine ⟨x', hxx', fun x'' hx'x'' ↦ ?_⟩
  simpa [mem_orthoNeg] using hx' x'' hx'x''

/-- Knowability holds iff `□` reflects contradiction on regular sets, the frame counterpart of
[holliday-mandelkern-2024] Lemma 3.25. -/
theorem isKnowable_iff :
    IsKnowable F R ↔ ∀ A, IsRegular F A → R.core A = ∅ → A = ∅ := by
  refine ⟨fun ⟨hK⟩ A hA h ↦ Set.eq_empty_of_forall_notMem fun x hx ↦ ?_, fun h ↦ ⟨fun x ↦ ?_⟩⟩
  · obtain ⟨y, hy⟩ := hK x
    exact Set.eq_empty_iff_forall_notMem.mp h y fun z hyz ↦ hA.mem_of_refines (hy z hyz) hx
  · have hx : x ∈ orthoNeg F (orthoNeg F {x}) :=
      (refines_iff_mem_orthoNeg_orthoNeg F).mp fun _ ↦ id
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr
      (mt (h _ (orthoNeg_isRegular F _)) (Set.nonempty_iff_ne_empty.mp ⟨x, hx⟩))
    exact ⟨y, fun _ hyz ↦ (refines_iff_mem_orthoNeg_orthoNeg F).mpr (hy hyz)⟩

/-- Over a reflexive relation with Knowability, `¬A` and `◇A` are disjoint for every set `A`,
regular or not, and without R-regularity ([holliday-mandelkern-2024] Proposition 4.27). -/
theorem disjoint_orthoNeg_diamond [R.IsRefl] [IsKnowable F R] (A : Set S) :
    Disjoint (orthoNeg F A) (diamond F R A) := by
  refine Set.disjoint_left.mpr fun x hxA hx ↦ ?_
  obtain ⟨y, hy⟩ := IsKnowable.knowable (F := F) (R := R) x
  exact hx y (hy y R.rfl y (F.refl y)) fun z hyz w hzw ↦ hxA w (hy z hyz w hzw)

/-! ### The modal ortholattice of regular propositions -/

/-- `F.necHom R` is `□` on the regular propositions of an R-regular frame, which preserves meets
and `⊤` and so makes them the modal ortholattice `O(F)` of [holliday-mandelkern-2024]
Proposition 4.23. -/
def CompatFrame.necHom [IsRRegular F R] : InfTopHom F.Regular F.Regular where
  toFun A := F.regOf (R.core A) (isRegular_core R A.isRegular)
  map_inf' _ _ := SetLike.coe_injective (core_inter ..)
  map_top' := SetLike.coe_injective core_univ

namespace CompatFrame

variable {F} [IsRRegular F R]

@[simp] theorem coe_necHom (A : F.Regular) : (F.necHom R A : Set S) = R.core A := rfl

theorem coe_diamondHom_necHom (A : F.Regular) :
    (diamondHom (F.necHom R) A : Set S) = diamond F R A := by
  simp only [diamondHom_apply, Regular.coe_compl, coe_necHom, diamond]

/-- Over a reflexive relation `□A ≤ A` ([holliday-mandelkern-2024] Proposition 4.25; footnote 22
weakens reflexivity). -/
theorem necHom_le [R.IsRefl] (A : F.Regular) : F.necHom R A ≤ A :=
  Concept.extent_subset_extent_iff.mp fun x hx ↦ hx (R.refl x)

theorem necHom_le_necHom_necHom [R.IsTrans] (A : F.Regular) :
    F.necHom R A ≤ F.necHom R (F.necHom R A) :=
  Concept.extent_subset_extent_iff.mp fun _ hx _ hxy _ hyz ↦ hx (R.trans hxy hyz)

variable (F)

/-- Over a reflexive R-regular relation, Knowability is exactly Wittgenstein's Law for the modal
ortholattice. The forward direction is [holliday-mandelkern-2024] Proposition 4.27. -/
theorem isKnowable_iff_wittgensteinLaw [R.IsRefl] :
    IsKnowable F R ↔ WittgensteinLaw (F.necHom R) := by
  rw [wittgensteinLaw_iff_eq_bot (necHom_le R), isKnowable_iff]
  refine ⟨fun h A hA ↦ ?_, fun h A hA hnec ↦ ?_⟩
  · rw [← Regular.coe_eq_empty] at hA ⊢
    exact h A A.isRegular hA
  · exact Regular.coe_eq_empty.mpr (h (F.regOf A hA) (Regular.coe_eq_empty.mp hnec))

/-- Over a reflexive relation with Knowability the modal ortholattice satisfies Wittgenstein's
Law, so it is an epistemic ortholattice ([holliday-mandelkern-2024] Proposition 4.27). -/
theorem wittgensteinLaw_necHom [R.IsRefl] [IsKnowable F R] :
    WittgensteinLaw (F.necHom R) :=
  (isKnowable_iff_wittgensteinLaw F R).mp inferInstance

end CompatFrame

end Orthologic
