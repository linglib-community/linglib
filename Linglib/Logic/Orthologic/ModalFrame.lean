module

public import Linglib.Core.Relation.SetRel
public import Linglib.Logic.Orthologic.CompatFrame
public import Linglib.Logic.Orthologic.Epistemic

/-!
# Modal compatibility frames

This file defines Holliday and Mandelkern's modal compatibility frames, the possibility semantics
for *must* and *might*. An accessibility relation $R$ gives the Kripke necessity
$\Box A = \{x \mid R(x) \subseteq A\}$, and $\Diamond A = \neg \Box \neg A$ negates with the
orthocomplement, so [$x$ settles $\Diamond A$](##mem_diamond) when every possibility compatible
with $x$ accesses one compatible with an $A$-possibility. [R-regularity is exactly the condition
for $\Box$ to preserve regularity](##isRRegular_iff_isRegular_core), which makes the regular
propositions a modal ortholattice. Reflexivity makes it T, as does [every possibility accessing
one it refines](##CompatFrame.necHom_le_of_forall_exists_refines), and over these [Knowability is
exactly Wittgenstein's Law](##CompatFrame.isKnowable_iff_wittgensteinLaw). Without T,
[$\neg A$ and $\Diamond^n A$ are disjoint](##disjoint_orthoNeg_diamond_iterate) once every $x$ is
compatible with a possibility whose $n$-step successors all refine $x$.

## Main definitions

* `Orthologic.diamond F R`: $\Diamond A = \neg \Box \neg A$ on sets.
* `Orthologic.IsRRegular F R`, `Orthologic.IsKnowable F R`: R-regularity and Knowability.
* `Orthologic.CompatFrame.necHom`: $\Box$ as a map on `F.Regular` preserving meets and $\top$.

## Implementation notes

The paper's frame classes are conjunctions of conditions on a bare relation, stated as Prop
classes like mathlib's `SetRel.IsRefl`: a *modal* compatibility frame is R-regular, a *T* frame is
also reflexive (`R.IsRefl`), and an *epistemic* frame also satisfies Knowability. Each theorem
assumes only the conditions it uses.

## References

* [holliday-mandelkern-2024]
-/

@[expose] public section

namespace Orthologic

open SetRel

variable {S : Type*} (F : CompatFrame S) (R : SetRel S S)

/-- The possibility `◇A = ¬□¬A` negates with the orthocomplement. -/
def diamond (A : Set S) : Set S :=
  orthoNeg F (R.core (orthoNeg F A))

instance [Fintype S] [DecidableRel F.compat] [∀ x y, Decidable (x ~[R] y)] (A : Set S)
    [DecidablePred (· ∈ A)] : DecidablePred (· ∈ diamond F R A) := fun x ↦
  inferInstanceAs (Decidable (x ∈ orthoNeg F (R.core (orthoNeg F A))))

variable {F R} in
/-- `x` makes `◇A` true iff every possibility compatible with `x` accesses one compatible with an
`A`-possibility ([holliday-mandelkern-2024] eq. (4)). -/
theorem mem_diamond {A : Set S} {x : S} : x ∈ diamond F R A ↔
    ∀ x', F.compat x x' → ∃ y', x' ~[R] y' ∧ ∃ y'', F.compat y' y'' ∧ y'' ∈ A := by
  simp only [diamond, mem_orthoNeg, mem_core, not_forall, not_not, exists_prop]

/-- `◇` sees a set only through its regular closure `¬¬A`. -/
theorem diamond_orthoNeg_orthoNeg (A : Set S) :
    diamond F R (orthoNeg F (orthoNeg F A)) = diamond F R A := by
  unfold diamond
  rw [(isRegular_orthoNeg F A).orthoNeg_orthoNeg]

/-- A relation is R-regular when a possibility accessing one compatible with `y` is compatible
with a possibility according to which `y` might obtain, one in `◇↓y` for `↓y` the refinements of
`y` ([holliday-mandelkern-2024] Definition 4.20). -/
class IsRRegular : Prop where
  rRegular : ∀ x y' y, x ~[R] y' → F.compat y' y →
    ∃ x', F.compat x x' ∧ x' ∈ diamond F R {z | refines F z y}

/-- R-regularity can be written without `◇` ([holliday-mandelkern-2024] Lemma 4.21). -/
theorem isRRegular_iff : IsRRegular F R ↔ ∀ x y' y, x ~[R] y' → F.compat y' y →
    ∃ x', F.compat x x' ∧ ∀ x'', F.compat x' x'' → ∃ y'', x'' ~[R] y'' ∧ F.compat y'' y := by
  have key x' y : x' ∈ diamond F R {z | refines F z y} ↔
      ∀ x'', F.compat x' x'' → ∃ y'', x'' ~[R] y'' ∧ F.compat y'' y := by
    rw [show {z | refines F z y} = orthoNeg F (orthoNeg F {y}) from
      Set.ext fun _ ↦ refines_iff_mem_orthoNeg_orthoNeg F, diamond_orthoNeg_orthoNeg, mem_diamond]
    simp only [Set.mem_singleton_iff, exists_eq_right]
  exact ⟨fun ⟨h⟩ ↦ by simpa only [key] using h, fun h ↦ ⟨by simpa only [key] using h⟩⟩

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
  obtain ⟨x', hxx', hx'⟩ := (isRRegular_iff F R).1 ‹_› x y z hxy hyz
  refine Or.inr ⟨x', hxx', fun x'' hx'x'' hnec ↦ ?_⟩
  obtain ⟨y'', hy'', hy''z⟩ := hx' x'' hx'x''
  exact hz y'' hy''z.symm (hnec hy'')

/-- Over an R-regular frame `¬◇A = □¬A`, since `□¬A` is regular. -/
theorem orthoNeg_diamond [IsRRegular F R] (A : Set S) :
    orthoNeg F (diamond F R A) = R.core (orthoNeg F A) :=
  (isRegular_core R (isRegular_orthoNeg F A)).orthoNeg_orthoNeg

variable (F)

/-- R-regularity holds iff `□` preserves regularity, extending Proposition 4.22 of
[holliday-mandelkern-2024] by its converse. -/
theorem isRRegular_iff_isRegular_core :
    IsRRegular F R ↔ ∀ A, IsRegular F A → IsRegular F (R.core A) := by
  refine ⟨fun _ _ ↦ isRegular_core R, fun h ↦ (isRRegular_iff F R).2 fun x y' y hxy' hy'y ↦ ?_⟩
  obtain hx | ⟨x', hxx', hx'⟩ := h _ (isRegular_orthoNeg F {y}) x
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
      (mt (h _ (isRegular_orthoNeg F _)) (Set.nonempty_iff_ne_empty.mp ⟨x, hx⟩))
    exact ⟨y, fun _ hyz ↦ (refines_iff_mem_orthoNeg_orthoNeg F).mpr (hy hyz)⟩

variable {F R} in
private theorem not_image_iterate_subset_orthoNeg :
    ∀ (n : ℕ) {A : Set S} {x y : S}, x ∈ (diamond F R)^[n] A → F.compat x y →
      ¬ R.image^[n] {y} ⊆ orthoNeg F A
  | 0, _, _, _, hx, hxy, h => h rfl _ hxy.symm hx
  | n + 1, _, _, y, hx, hxy, h => by
    rw [Function.iterate_succ_apply'] at hx
    obtain ⟨y', hyy', y'', hy'y'', hy''⟩ := mem_diamond.1 hx y hxy
    refine not_image_iterate_subset_orthoNeg n hy'' hy'y''.symm (subset_trans ?_ h)
    rw [Function.iterate_succ_apply]
    exact image_mono.iterate n (Set.singleton_subset_iff.2 ⟨y, rfl, hyy'⟩)

/-- When every possibility `x` is compatible with some `y` whose possibilities `n` steps of access
away all refine `x`, `¬A` and `◇ⁿA` are disjoint for every set `A`, with neither reflexivity nor
R-regularity ([holliday-mandelkern-2024] Remark 4.28). -/
theorem disjoint_orthoNeg_diamond_iterate {n : ℕ}
    (h : ∀ x, ∃ y, F.compat y x ∧ ∀ z ∈ R.image^[n] {y}, refines F z x) (A : Set S) :
    Disjoint (orthoNeg F A) ((diamond F R)^[n] A) := by
  refine Set.disjoint_left.mpr fun x hxA hx ↦ ?_
  obtain ⟨y, hyx, hy⟩ := h x
  exact not_image_iterate_subset_orthoNeg n hx hyx.symm fun z hz ↦
    (isRegular_orthoNeg F A).mem_of_refines (hy z hz) hxA

/-- Over a reflexive relation with Knowability, `¬A` and `◇A` are disjoint for every set `A`,
regular or not, and without R-regularity ([holliday-mandelkern-2024] Proposition 4.27). -/
theorem disjoint_orthoNeg_diamond [R.IsRefl] [IsKnowable F R] (A : Set S) :
    Disjoint (orthoNeg F A) (diamond F R A) := by
  refine disjoint_orthoNeg_diamond_iterate F R (n := 1) (fun x ↦ ?_) A
  obtain ⟨y, hy⟩ := IsKnowable.knowable (F := F) (R := R) x
  exact ⟨y, (hy y R.rfl y (F.refl y)).symm, fun z ⟨_, hy', hyz⟩ ↦ hy z (hy' ▸ hyz)⟩

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

/-- `□A ≤ A` holds when every possibility accesses one that it refines
([holliday-mandelkern-2024] footnote 22). -/
theorem necHom_le_of_forall_exists_refines (h : ∀ x, ∃ y, x ~[R] y ∧ refines F x y)
    (A : F.Regular) : F.necHom R A ≤ A :=
  Concept.extent_subset_extent_iff.mp fun x hx ↦
    let ⟨_, hxy, hr⟩ := h x
    A.isRegular.mem_of_refines hr (hx hxy)

/-- Over a reflexive relation `□A ≤ A` ([holliday-mandelkern-2024] Proposition 4.25). -/
theorem necHom_le [R.IsRefl] (A : F.Regular) : F.necHom R A ≤ A :=
  necHom_le_of_forall_exists_refines R (fun x ↦ ⟨x, R.rfl, fun _ ↦ id⟩) A

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
