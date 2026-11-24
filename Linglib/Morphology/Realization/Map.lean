/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Realization.Basic

/-!
# Maps of realizations

This file carries a realization along maps. The transpose exchanges indices and contexts. The
image `S.map g` applies a map `g` of forms, as a transcription does, and forms that `g` identifies
pool their cells. The composite `S.comp T` realizes an index through the intermediate forms of
`S`, each realized in the same context by `T`. The pullback `T.comap i k` realizes each index in
each context as `T` realizes their images under maps `i` of indices and `k` of contexts. A
realization that equals a pullback of `T` has the forms of `T`, and one that is below a pullback
has some of them, as a lexeme has some of the forms of its root; suppletion, overabundance and
syncretism pass from a pullback to `T`. The reduction of a realization merges the indices that
have the same forms in every context, and every realization is the pullback of its reduction.

## Main definitions

* `Realization.transpose`: the realization of contexts at indices.
* `Realization.map`: the image under a map of forms.
* `Realization.comp`: the composite through intermediate forms.
* `Realization.comap`: the pullback along maps of indices and contexts.
* `Realization.reduce`: the quotient that merges indices with the same forms.

## Main results

* `Realization.mem_cells_map`: a form of the image fills the cells its preimages fill.
* `Realization.IsSyncretic.map`, `Realization.IsSuppletive.of_map`: syncretism passes to the
  image, and suppletion back from it.
* `Realization.IsSuppletive.of_comap`, `Realization.IsOverabundant.of_comap`,
  `Realization.IsSyncretic.of_comap`: suppletion, overabundance and syncretism pass from a
  pullback.
* `Realization.ker_le_ker_comap_realize`: a pullback gives indices with the same image the same
  forms.
* `Realization.comap_reduce`: every realization is the pullback of its reduction.

## Implementation notes

* A pullback translates contexts without consulting the index, so categorial information has to
  sit in the context.

## References

* [harley-2014]
* [marantz-1997]
* [embick-2021]
* [borer-2013]
* [stump-2001]
* [bonami-stump-2016]
* [spencer-2013]
* [beard-1995]
* [haspelmath-2025b]
* [lohndal-2020]
* [blevins-2016]
* [arad-2005]
* [gouskova-bobaljik-2020]
* [corbett-2007]
* [stump-2016]
* [thornton-2011]
-/

@[expose] public section

namespace Morphology

open Function Relator

variable {R Ctx F G M K : Type*}

namespace Realization

variable (S : Realization R Ctx F) {T : Realization R Ctx F} {r r' : R} {c c' : Ctx} {f f' : F}

/-! ### Transpose, image and composition -/

/-- The transpose of `S` realizes each context at each index as `S` realizes the index in the
context, so that comparing one context across indices is comparing one index of the transpose
across contexts. -/
def transpose (S : Realization R Ctx F) : Realization Ctx R F := ⟨swap S.realize⟩

@[simp] theorem transpose_realize (c : Ctx) (r : R) : S.transpose.realize c r = S.realize r c :=
  rfl

@[simp] theorem transpose_transpose : S.transpose.transpose = S := rfl

/-- The cells of a form at a context of the transpose are the indices the form realizes there. -/
@[simp] theorem mem_cells_transpose : r ∈ S.transpose.cells c f ↔ c ∈ S.cells r f := Iff.rfl

/-- The contexts that the transpose does not distinguish are those that every index realizes
alike. -/
theorem ker_transpose_realize_iff :
    Setoid.ker S.transpose.realize c c' ↔ ∀ r, Setoid.ker (S.realize r) c c' := by
  simp [Setoid.ker_def, funext_iff]

/-- The image of `S` under a map of forms. -/
def map [DecidableEq G] (g : F → G) (S : Realization R Ctx F) : Realization R Ctx G :=
  ⟨fun r c ↦ (S.realize r c).image g⟩

section Map

variable [DecidableEq G] (g : F → G)

@[simp] theorem map_realize (r : R) (c : Ctx) : (S.map g).realize r c = (S.realize r c).image g :=
  rfl

@[simp] theorem exponents_map (r : R) : (S.map g).exponents r = g '' S.exponents r := by
  ext; simp only [mem_exponents, map_realize, Finset.mem_image, Set.mem_image]; tauto

/-- A form of the image fills the cells its preimages fill: forms that the map identifies, as a
transcription that omits a distinction does, pool their cells. -/
theorem mem_cells_map {y : G} : c ∈ (S.map g).cells r y ↔ ∃ f, c ∈ S.cells r f ∧ g f = y := by
  simp [cells]

variable {S}

theorem IsInvariant.map (h : S.IsInvariant r) : (S.map g).IsInvariant r := by
  simpa [IsInvariant] using Set.Subsingleton.image h g

theorem IsSyncretic.map (h : S.IsSyncretic r) : (S.map g).IsSyncretic r :=
  let ⟨_, _, hne, _, hf, hf'⟩ := isSyncretic_iff.1 h
  isSyncretic_of_mem hne (Finset.mem_image_of_mem g hf) (Finset.mem_image_of_mem g hf')

variable {g}

theorem IsSuppletive.of_map (h : (S.map g).IsSuppletive r) : S.IsSuppletive r :=
  Set.nontrivial_of_image g _ (by simpa [IsSuppletive] using h)

@[simp] theorem isLicensed_map_iff : (S.map g).IsLicensed r c ↔ S.IsLicensed r c :=
  Finset.image_nonempty

@[simp] theorem isTotal_map_iff : (S.map g).IsTotal ↔ S.IsTotal := by simp [isTotal_iff]

end Map

/-- The composite `S.comp T` realizes an index through the intermediate forms of `S`, each
realized in the same context by `T`: the Kleisli composition of `Finset`-valued maps. A
late-insertion grammar factors its realization this way, and so does a choice of stem followed by
its inflection. -/
def comp [DecidableEq G] (S : Realization R Ctx F) (T : Realization F Ctx G) :
    Realization R Ctx G :=
  ⟨fun r c ↦ (S.realize r c).biUnion fun f ↦ T.realize f c⟩

section Comp

variable [DecidableEq G] {S} {T : Realization F Ctx G} {g : G}

@[simp] theorem mem_comp_realize :
    g ∈ (S.comp T).realize r c ↔ ∃ f ∈ S.realize r c, g ∈ T.realize f c :=
  Finset.mem_biUnion

theorem mem_cells_comp : c ∈ (S.comp T).cells r g ↔ ∃ f ∈ S.realize r c, c ∈ T.cells f g :=
  mem_comp_realize

theorem IsTotal.comp (hS : S.IsTotal) (hT : T.IsTotal) : (S.comp T).IsTotal := fun r c ↦
  let ⟨f, hf⟩ := hS r c
  let ⟨g, hg⟩ := hT f c
  ⟨g, mem_comp_realize.2 ⟨f, hf, hg⟩⟩

theorem comp_assoc {H : Type*} [DecidableEq H] (S : Realization R Ctx F) (T : Realization F Ctx G)
    (U : Realization G Ctx H) : (S.comp T).comp U = S.comp (T.comp U) := by
  ext r c h; simp only [mem_comp_realize]; tauto

end Comp

/-! ### Pullback -/

section Comap

variable {R₁ C₁ R₂ C₂ R₃ C₃ : Type*} (i : R₁ → R₂) (k : C₁ → C₂) (T T' : Realization R₂ C₂ F)
  {r r' : R₁} {c : C₁}

/-- The pullback of `T` along maps of indices and of contexts realizes each index in each context
as `T` realizes their images. A realization equal to a pullback of `T` merges indices and
translates contexts while keeping the forms of each cell, and one below a pullback has, in each
cell, some of the forms `T` gives its image. -/
def comap : Realization R₁ C₁ F := ⟨fun r c ↦ T.realize (i r) (k c)⟩

@[simp] theorem comap_realize (r : R₁) (c : C₁) :
    (T.comap i k).realize r c = T.realize (i r) (k c) := rfl

@[simp] theorem comap_id (S : Realization R Ctx F) : S.comap id id = S := rfl

theorem comap_comap (j : R₂ → R₃) (l : C₂ → C₃) (U : Realization R₃ C₃ F) :
    (U.comap j l).comap i k = U.comap (j ∘ i) (l ∘ k) := rfl

variable {T T'} in
@[gcongr] theorem comap_mono (h : T ≤ T') : T.comap i k ≤ T'.comap i k := fun _ _ ↦ h _ _

@[simp] theorem isLicensed_comap_iff : (T.comap i k).IsLicensed r c ↔ T.IsLicensed (i r) (k c) :=
  Iff.rfl

/-- The cells of a form in a pullback are the contexts sent to its cells. -/
@[simp] theorem cells_comap (r : R₁) (f : F) :
    (T.comap i k).cells r f = k ⁻¹' T.cells (i r) f := rfl

/-- The allomorphs of an index of a pullback are among those of its image. -/
theorem exponents_comap_subset (r : R₁) : (T.comap i k).exponents r ⊆ T.exponents (i r) :=
  fun _ ⟨c, hf⟩ ↦ ⟨k c, hf⟩

variable {i k T}

theorem IsSuppletive.of_comap (h : (T.comap i k).IsSuppletive r) : T.IsSuppletive (i r) :=
  Set.Nontrivial.mono h (exponents_comap_subset i k T r)

theorem IsInvariant.comap (h : T.IsInvariant (i r)) : (T.comap i k).IsInvariant r :=
  Set.Subsingleton.anti h (exponents_comap_subset i k T r)

theorem IsOverabundant.of_comap (h : (T.comap i k).IsOverabundant r) : T.IsOverabundant (i r) :=
  mt (fun ht _ _ _ hf hf' ↦ ht hf hf') h

/-- Syncretism passes from a pullback that keeps contexts apart. -/
theorem IsSyncretic.of_comap (hk : Injective k) (h : (T.comap i k).IsSyncretic r) :
    T.IsSyncretic (i r) :=
  mt (fun ht _ _ _ hf hf' ↦ hk (ht hf hf')) h

theorem IsUnivalent.comap (h : T.IsUnivalent) : (T.comap i k).IsUnivalent :=
  fun r _ _ _ hf hf' ↦ h (i r) hf hf'

theorem IsTotal.comap (h : T.IsTotal) : (T.comap i k).IsTotal := fun r c ↦ h (i r) (k c)

variable (i k T)

/-- A pullback gives indices with the same image the same forms in every context. -/
theorem ker_le_ker_comap_realize : Setoid.ker i ≤ Setoid.ker (T.comap i k).realize :=
  fun r r' (h : i r = i r') ↦ funext fun c ↦ by rw [comap_realize, comap_realize, h]

end Comap

/-! ### Reduction -/

/-- The reduction of `S` merges the indices that have the same forms in every context. -/
def reduce : Realization (Quotient (Setoid.ker S.realize)) Ctx F := ⟨Setoid.kerLift S.realize⟩

@[simp] theorem reduce_realize_mk (r : R) : S.reduce.realize ⟦r⟧ = S.realize r := rfl

/-- Every realization is the pullback of its reduction, which by `ker_le_ker_comap_realize` and
`Setoid.ker_mk_eq` merges as many indices as a pullback can. -/
@[simp] theorem comap_reduce : S.reduce.comap Quotient.mk'' id = S := rfl

/-- Distinct indices of the reduction differ in their forms in some context. -/
theorem reduce_realize_injective : Injective S.reduce.realize := Setoid.kerLift_injective _

end Realization

end Morphology
