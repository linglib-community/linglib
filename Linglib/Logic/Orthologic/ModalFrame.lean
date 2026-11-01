module

public import Linglib.Core.Relation.SetRel
public import Linglib.Logic.Orthologic.Compatibility
public import Linglib.Logic.Orthologic.Epistemic

/-!
# Modal compatibility frames

This file defines Holliday and Mandelkern's modal compatibility frames, the possibility semantics
for *must* and *might*. An accessibility relation $R$ gives the Kripke necessity
$\Box A = \{x \mid R(x) \subseteq A\}$, and $\Diamond A = \neg \Box \neg A$ negates with the
orthocomplement, so [$x$ settles $\Diamond A$](##mem_diamond) when every possibility compatible
with $x$ accesses one compatible with an $A$-possibility. [R-regularity is exactly the condition
for $\Box$ to preserve regularity](##isRRegular_iff_isExtent_core), which makes the regular
propositions a modal ortholattice. Reflexivity makes it T, as does [every possibility accessing
one it refines](##Compatibility.necHom_le_of_forall_exists_mem_ofObject), and over these
[Knowability is exactly Wittgenstein's Law](##Compatibility.isKnowable_iff_wittgensteinLaw).
Without T, [$\neg A$ and $\Diamond^n A$ are disjoint](##disjoint_upperPolar_diamond_iterate) once
every $x$ is compatible with a possibility whose $n$-step successors all refine $x$.

## Main definitions

* `Orthologic.diamond F R`: $\Diamond A = \neg \Box \neg A$ on sets.
* `Orthologic.IsRRegular F R`, `Orthologic.IsKnowable F R`: R-regularity and Knowability.
* `Orthologic.Compatibility.necHom`: $\Box$ as a map on `F.Regular` preserving meets and $\top$.

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

open Order Concept SetRel

variable {S : Type*} (F : Compatibility S) (R : SetRel S S)

/-- The possibility `◇A = ¬□¬A` negates with the orthocomplement. -/
def diamond (A : Set S) : Set S :=
  upperPolar F.ortho (R.core (upperPolar F.ortho A))

instance [Fintype S] [DecidableRel F.compat] [∀ x y, Decidable (x ~[R] y)] (A : Set S)
    [DecidablePred (· ∈ A)] : DecidablePred (· ∈ diamond F R A) := fun x ↦
  inferInstanceAs (Decidable (x ∈ upperPolar F.ortho (R.core (upperPolar F.ortho A))))

variable {F R} in
/-- `x` makes `◇A` true iff every possibility compatible with `x` accesses one compatible with an
`A`-possibility ([holliday-mandelkern-2024] eq. (4)). -/
theorem mem_diamond {A : Set S} {x : S} : x ∈ diamond F R A ↔
    ∀ x', F.compat x x' → ∃ y', x' ~[R] y' ∧ ∃ y'', F.compat y' y'' ∧ y'' ∈ A := by
  simp only [diamond, F.mem_upperPolar_ortho, mem_core, not_forall, not_not, exists_prop]

/-- `◇` sees a set only through its regular closure. -/
theorem diamond_extentClosure (A : Set S) :
    diamond F R (extentClosure F.ortho A) = diamond F R A := by
  rw [diamond, diamond, extentClosure_apply, upperPolar_lowerPolar_upperPolar]

/-- A relation is R-regular when a possibility accessing one compatible with `y` is compatible
with a possibility according to which `y` might obtain, one in `◇↓y` for `↓y` the refinements of
`y` ([holliday-mandelkern-2024] Definition 4.20). -/
class IsRRegular : Prop where
  rRegular : ∀ x y' y, x ~[R] y' → F.compat y' y →
    ∃ x', F.compat x x' ∧ x' ∈ diamond F R (ofObject F.ortho y)

/-- R-regularity can be written without `◇` ([holliday-mandelkern-2024] Lemma 4.21). -/
theorem isRRegular_iff : IsRRegular F R ↔ ∀ x y' y, x ~[R] y' → F.compat y' y →
    ∃ x', F.compat x x' ∧ ∀ x'', F.compat x' x'' → ∃ y'', x'' ~[R] y'' ∧ F.compat y'' y := by
  have key x' y : x' ∈ diamond F R (ofObject F.ortho y) ↔
      ∀ x'', F.compat x' x'' → ∃ y'', x'' ~[R] y'' ∧ F.compat y'' y := by
    rw [coe_ofObject, diamond_extentClosure, mem_diamond]
    simp only [Set.mem_singleton_iff, exists_eq_right]
  exact ⟨fun ⟨h⟩ ↦ by simpa only [key] using h, fun h ↦ ⟨by simpa only [key] using h⟩⟩

/-- A relation satisfies Knowability when every possibility `x` has one at which everything
settled true by `x` is known, since all it accesses refine `x` ([holliday-mandelkern-2024]
Definition 4.26). -/
class IsKnowable : Prop where
  knowable : ∀ x, ∃ y, ∀ z, y ~[R] z → z ∈ ofObject F.ortho x

variable {F}

/-- Over an R-regular frame, `□` of a regular set is regular ([holliday-mandelkern-2024]
Proposition 4.22). -/
theorem isExtent_core [IsRRegular F R] {A : Set S} (hA : IsExtent F.ortho A) :
    IsExtent F.ortho (R.core A) := by
  rw [F.isExtent_ortho_iff] at hA ⊢
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
theorem upperPolar_diamond [IsRRegular F R] (A : Set S) :
    upperPolar F.ortho (diamond F R A) = R.core (upperPolar F.ortho A) :=
  (isExtent_core R (isExtent_upperPolar F.ortho A)).upperPolar_upperPolar

variable (F)

/-- R-regularity holds iff `□` preserves regularity, extending Proposition 4.22 of
[holliday-mandelkern-2024] by its converse. -/
theorem isRRegular_iff_isExtent_core :
    IsRRegular F R ↔ ∀ A, IsExtent F.ortho A → IsExtent F.ortho (R.core A) := by
  refine ⟨fun _ _ ↦ isExtent_core R, fun h ↦ (isRRegular_iff F R).2 fun x y' y hxy' hy'y ↦ ?_⟩
  obtain hx | ⟨x', hxx', hx'⟩ :=
    (F.isExtent_ortho_iff _).1 (h _ (isExtent_upperPolar F.ortho {y})) x
  · exact ((F.ortho_iff y y').1 (hx hxy' rfl) hy'y.symm).elim
  refine ⟨x', hxx', fun x'' hx'x'' ↦ ?_⟩
  simpa [F.mem_upperPolar_ortho] using hx' x'' hx'x''

/-- Knowability holds iff `□` reflects contradiction on regular sets, the frame counterpart of
[holliday-mandelkern-2024] Lemma 3.25. -/
theorem isKnowable_iff :
    IsKnowable F R ↔ ∀ A, IsExtent F.ortho A → R.core A = ∅ → A = ∅ := by
  refine ⟨fun ⟨hK⟩ A hA h ↦ Set.eq_empty_of_forall_notMem fun x hx ↦ ?_, fun h ↦ ⟨fun x ↦ ?_⟩⟩
  · obtain ⟨y, hy⟩ := hK x
    exact Set.eq_empty_iff_forall_notMem.mp h y fun z hyz ↦ hA.mem_of_mem_ofObject (hy z hyz) hx
  · obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr <| mt (h _ (ofObject F.ortho x).isExtent_extent)
      (Set.nonempty_iff_ne_empty.mp ⟨x, mem_ofObject_self x⟩)
    exact ⟨y, fun _ hyz ↦ hy hyz⟩

variable {F R} in
private theorem not_image_iterate_subset_upperPolar :
    ∀ (n : ℕ) {A : Set S} {x y : S}, x ∈ (diamond F R)^[n] A → F.compat x y →
      ¬ R.image^[n] {y} ⊆ upperPolar F.ortho A
  | 0, _, _, _, hx, hxy, h => F.mem_upperPolar_ortho.1 (h rfl) _ hxy.symm hx
  | n + 1, _, _, y, hx, hxy, h => by
    rw [Function.iterate_succ_apply'] at hx
    obtain ⟨y', hyy', y'', hy'y'', hy''⟩ := mem_diamond.1 hx y hxy
    refine not_image_iterate_subset_upperPolar n hy'' hy'y''.symm (subset_trans ?_ h)
    rw [Function.iterate_succ_apply]
    exact image_mono.iterate n (Set.singleton_subset_iff.2 ⟨y, rfl, hyy'⟩)

/-- When every possibility `x` is compatible with some `y` whose possibilities `n` steps of access
away all refine `x`, `¬A` and `◇ⁿA` are disjoint for every set `A`, with neither reflexivity nor
R-regularity ([holliday-mandelkern-2024] Remark 4.28). -/
theorem disjoint_upperPolar_diamond_iterate {n : ℕ}
    (h : ∀ x, ∃ y, F.compat y x ∧ R.image^[n] {y} ⊆ ofObject F.ortho x) (A : Set S) :
    Disjoint (upperPolar F.ortho A) ((diamond F R)^[n] A) := by
  refine Set.disjoint_left.mpr fun x hxA hx ↦ ?_
  obtain ⟨y, hyx, hy⟩ := h x
  exact not_image_iterate_subset_upperPolar n hx hyx.symm fun z hz ↦
    (isExtent_upperPolar F.ortho A).mem_of_mem_ofObject (hy hz) hxA

/-- Over a reflexive relation with Knowability, `¬A` and `◇A` are disjoint for every set `A`,
regular or not, and without R-regularity ([holliday-mandelkern-2024] Proposition 4.27). -/
theorem disjoint_upperPolar_diamond [R.IsRefl] [IsKnowable F R] (A : Set S) :
    Disjoint (upperPolar F.ortho A) (diamond F R A) := by
  refine disjoint_upperPolar_diamond_iterate F R (n := 1) (fun x ↦ ?_) A
  obtain ⟨y, hy⟩ := IsKnowable.knowable (F := F) (R := R) x
  exact ⟨y, (F.mem_ofObject_ortho.1 (hy y R.rfl) y (F.refl y)).symm,
    fun z ⟨_, hy', hyz⟩ ↦ hy z (hy' ▸ hyz)⟩

/-! ### The modal ortholattice of regular propositions -/

/-- `F.necHom R` is `□` on the regular propositions of an R-regular frame, which preserves meets
and `⊤` and so makes them the modal ortholattice `O(F)` of [holliday-mandelkern-2024]
Proposition 4.23. -/
def Compatibility.necHom [IsRRegular F R] : InfTopHom F.Regular F.Regular where
  toFun A := .ofIsExtent _ (R.core A) (isExtent_core R A.isExtent_extent)
  map_inf' _ _ := SetLike.coe_injective (core_inter ..)
  map_top' := SetLike.coe_injective core_univ

namespace Compatibility

variable {F} [IsRRegular F R]

@[simp] theorem coe_necHom (A : F.Regular) : (F.necHom R A : Set S) = R.core A := rfl

theorem coe_diamondHom_necHom (A : F.Regular) :
    (diamondHom (F.necHom R) A : Set S) = diamond F R A := by
  simp only [diamondHom_apply, coe_compl, coe_necHom, diamond]

/-- `□A ≤ A` holds when every possibility accesses one that it refines
([holliday-mandelkern-2024] footnote 22). -/
theorem necHom_le_of_forall_exists_mem_ofObject (h : ∀ x, ∃ y, x ~[R] y ∧ x ∈ ofObject F.ortho y)
    (A : F.Regular) : F.necHom R A ≤ A :=
  extent_subset_extent_iff.mp fun x hx ↦
    let ⟨_, hxy, hr⟩ := h x
    A.isExtent_extent.mem_of_mem_ofObject hr (hx hxy)

/-- Over a reflexive relation `□A ≤ A` ([holliday-mandelkern-2024] Proposition 4.25). -/
theorem necHom_le [R.IsRefl] (A : F.Regular) : F.necHom R A ≤ A :=
  necHom_le_of_forall_exists_mem_ofObject R (fun x ↦ ⟨x, R.rfl, mem_ofObject_self x⟩) A

theorem necHom_le_necHom_necHom [R.IsTrans] (A : F.Regular) :
    F.necHom R A ≤ F.necHom R (F.necHom R A) :=
  extent_subset_extent_iff.mp fun _ hx _ hxy _ hyz ↦ hx (R.trans hxy hyz)

variable (F)

/-- Over a reflexive R-regular relation, Knowability is exactly Wittgenstein's Law for the modal
ortholattice. The forward direction is [holliday-mandelkern-2024] Proposition 4.27. -/
theorem isKnowable_iff_wittgensteinLaw [R.IsRefl] :
    IsKnowable F R ↔ WittgensteinLaw (F.necHom R) := by
  rw [wittgensteinLaw_iff_eq_bot (necHom_le R), isKnowable_iff]
  refine ⟨fun h A hA ↦ ?_, fun h A hA hnec ↦ ?_⟩
  · rw [← coe_eq_empty] at hA ⊢
    exact h A A.isExtent_extent hA
  · exact coe_eq_empty.mpr (h (.ofIsExtent _ A hA) (coe_eq_empty.mp hnec))

/-- Over a reflexive relation with Knowability the modal ortholattice satisfies Wittgenstein's
Law, so it is an epistemic ortholattice ([holliday-mandelkern-2024] Proposition 4.27). -/
theorem wittgensteinLaw_necHom [R.IsRefl] [IsKnowable F R] :
    WittgensteinLaw (F.necHom R) :=
  (isKnowable_iff_wittgensteinLaw F R).mp inferInstance

end Compatibility

end Orthologic
