module

public import Linglib.Semantics.Dynamic.DRS.Gluing
public import Linglib.Semantics.Dynamic.DRS.Verification

/-!
# Realizers of basic DRSs

A basic DRS is true under an assignment of its context's referents when each literal holds, and its
realizers, the assignments that make it true, are the [verifying
embeddings](##DRT.Theory.verifies_toDRS_iff) of the DRS. Assignments form a presheaf on contexts
that is a sheaf for a presieve [exactly when it is jointly surjective on
referents](##DRT.isSheafFor_assignments_iff), the first of Abramsky and Sadrzadeh's two conditions
on covers. An assignment [realizes the least gluing](##DRT.Cover.realizers_pushforward) of a
family along a cover exactly when its restrictions realize the local theories, so the realizers of
the gluing are [the compatible families of local realizers](##DRT.Cover.realizersEquiv).

## Implementation notes

Abramsky and Sadrzadeh leave a sheaf-theoretic semantics of DRSs to future work; this file only
shows that truth is compatible with their gluing.

## References

* [abramsky-sadrzadeh-2014]
* [kamp-reyle-1993]
-/

@[expose] public section

open CategoryTheory FirstOrder Language Structure Presieve

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} {c c' : Context L V}

/-! ### Truth of basic DRSs -/

namespace Literal

variable [L.Structure M]

/-- `l.Holds g` says that the assignment `g` makes `l` true, its atom holding when `l` is
positive and failing when it is negative. -/
def Holds (l : Literal c) (g : c.vars → M) : Prop := RelMap l.rel.1.2 (g ∘ l.args) ↔ l.pos

@[simp] theorem holds_map (f : c ⟶ c') (l : Literal c) (g : c'.vars → M) :
    (l.map f).Holds g ↔ l.Holds (g ∘ f.map) :=
  .rfl

theorem holds_comp_val_iff (l : Literal c) (g : V → M) :
    l.Holds (g ∘ Subtype.val) ↔ (l.atom.Realize g ↔ l.pos) :=
  .rfl

variable (M) in
/-- The realizers of a set of literals are the assignments of the context's referents that make
each of them true. -/
def realizers (S : Set (Literal c)) : Set (c.vars → M) :=
  upperPolar (fun l g ↦ l.Holds g) S

variable {S : Set (Literal c)}

theorem mem_realizers {g : c.vars → M} : g ∈ realizers M S ↔ ∀ l ∈ S, l.Holds g :=
  .rfl

theorem realizers_iUnion {ι : Sort*} (S : ι → Set (Literal c)) :
    realizers M (⋃ i, S i) = ⋂ i, realizers M (S i) :=
  upperPolar_iUnion ..

theorem realizers_image_map (f : c ⟶ c') (S : Set (Literal c)) :
    realizers M (map f '' S) = (· ∘ f.map) ⁻¹' realizers M S := by
  ext
  simp [mem_realizers]

theorem comp_val_mem_realizers_iff (hpos : ∀ l ∈ S, l.pos) {g : V → M} :
    g ∘ Subtype.val ∈ realizers M S ↔ g ∈ Atom.realizers M (atom '' S) := by
  simp only [mem_realizers, holds_comp_val_iff, Atom.mem_realizers, Set.forall_mem_image]
  exact forall₂_congr fun l hl ↦ by simp [hpos l hl]

end Literal

namespace Theory

variable [L.Structure M] {s : Theory c}

/-- An embedding verifies the DRS of a theory exactly when its restriction to the context's
referents realizes the theory. -/
theorem verifies_toDRS_iff {g : V → M} :
    VerifiesTotal g s.toDRS ↔ g ∘ Subtype.val ∈ Literal.realizers M (s.lits : Set (Literal c)) := by
  rw [verifiesTotal_iff, Literal.mem_realizers]
  simp only [toDRS, DRS.conditions_mk, List.mem_map, Finset.mem_toList, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, Finset.mem_coe]
  refine forall₂_congr fun l _ ↦ ?_
  rw [Literal.holds_comp_val_iff]
  unfold Literal.toCondition
  cases l.pos <;> simp [Box.Extends, ← funext_iff]

variable [DecidableEq V] [∀ n, DecidableEq (L.Relations n)]

theorem comp_mem_realizers_restrict {f : c ⟶ c'} {s : Theory c'} {g : c'.vars → M}
    (h : g ∈ Literal.realizers M (s.lits : Set (Literal c'))) :
    g ∘ f.map ∈ Literal.realizers M ((s.restrict f).lits : Set (Literal c)) :=
  Literal.mem_realizers.2 fun _ hl ↦ Literal.mem_realizers.1 h _ (mem_restrict.1 hl)

end Theory

/-! ### The sheaf of assignments -/

variable (L V M) in
/-- Assignments of values to the referents of contexts form a presheaf, restricting by
precomposition. -/
def assignments : (Context L V)ᵒᵖ ⥤ Type (max w x) where
  obj c := c.unop.vars → M
  map f := TypeCat.ofHom (· ∘ f.unop.map)

@[simp] theorem assignments_map {c c' : (Context L V)ᵒᵖ} (f : c ⟶ c') (g : c.unop.vars → M) :
    (assignments L V M).map f g = g ∘ f.unop.map :=
  rfl

variable (L V) in
/-- A presieve belongs to the referent precoverage when every referent of the context is the image
of a referent of some member. -/
abbrev referentPrecoverage : Precoverage (Context L V) :=
  Types.jointlySurjectivePrecoverage.comap (Context.varsFunctor L V)

variable {R : Presieve c}

theorem mem_referentPrecoverage_iff : R ∈ referentPrecoverage L V c ↔
    ∀ t : c.vars, ∃ (Y : Context L V) (f : Y ⟶ c), R f ∧ ∃ y, f.map y = t := by
  simp only [mem_comap_jointlySurjectivePrecoverage_iff, Set.mem_range, Context.varsFunctor_map]
  rfl

/-- A family of assignments is compatible when its members agree wherever the presieve identifies
referents. -/
theorem compatible_assignments_iff {x : FamilyOfElements (assignments L V M) R} :
    x.Compatible ↔ ∀ ⦃Y₁ Y₂ : Context L V⦄ ⦃f₁ : Y₁ ⟶ c⦄ ⦃f₂ : Y₂ ⟶ c⦄ (h₁ : R f₁) (h₂ : R f₂)
      (a : Y₁.vars) (b : Y₂.vars), f₁.map a = f₂.map b → x f₁ h₁ a = x f₂ h₂ b := by
  refine ⟨fun hx Y₁ Y₂ f₁ f₂ h₁ h₂ a b hab ↦ ?_, fun hx Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hg ↦
    funext fun z ↦ hx h₁ h₂ _ _ (congrFun (congrArg Context.Hom.map hg) z)⟩
  have := hx (Z := ⟨∅, {(a : V)}⟩) ⟨Finset.empty_subset _, fun _ ↦ a⟩
    ⟨Finset.empty_subset _, fun _ ↦ b⟩ h₁ h₂ (Context.hom_ext (funext fun _ ↦ hab))
  exact congrFun this ⟨a, Finset.mem_singleton_self _⟩

theorem arrows_compatible_assignments_iff {ι : Type*} {Y : ι → Context L V} {π : ∀ i, Y i ⟶ c}
    {x : ∀ i, (Y i).vars → M} :
    Arrows.Compatible (assignments L V M) π x ↔
      ∀ i j a b, (π i).map a = (π j).map b → x i a = x j b := by
  refine ⟨fun hx i j a b hab ↦ ?_, fun hx i j Z gi gj hg ↦
    funext fun z ↦ hx i j _ _ (congrFun (congrArg Context.Hom.map hg) z)⟩
  have := hx i j ⟨∅, {(a : V)}⟩ ⟨Finset.empty_subset _, fun _ ↦ a⟩
    ⟨Finset.empty_subset _, fun _ ↦ b⟩ (Context.hom_ext (funext fun _ ↦ hab))
  exact congrFun this ⟨a, Finset.mem_singleton_self _⟩

/-- Assignments glue uniquely along a presieve jointly surjective on referents. -/
theorem isSheafFor_assignments (hR : R ∈ referentPrecoverage L V c) :
    R.IsSheafFor (assignments L V M) := by
  choose Y f hf y hy using mem_referentPrecoverage_iff.1 hR
  refine fun x hx ↦ ⟨fun t ↦ x (f t) (hf t) (y t), fun Z g hg ↦ funext fun z ↦
    compatible_assignments_iff.1 hx _ _ _ _ (hy _), fun t ht ↦ funext fun u ↦ ?_⟩
  simpa [hy] using congrFun (ht (f u) (hf u)) (y u)

/-- Assignments to a nontrivial structure are a sheaf for a presieve iff it is jointly surjective
on referents. -/
theorem isSheafFor_assignments_iff [Nontrivial M] :
    R.IsSheafFor (assignments L V M) ↔ R ∈ referentPrecoverage L V c := by
  refine ⟨fun h ↦ mem_referentPrecoverage_iff.2 fun t ↦ by_contra fun ht ↦ ?_,
    isSheafFor_assignments⟩
  push Not at ht
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne M
  have := h.isSeparatedFor (fun _ _ _ _ ↦ a) (fun _ ↦ a) (Function.update (fun _ ↦ a) t b)
    (fun _ _ _ ↦ rfl) fun Y f hf ↦ funext fun s ↦ by simp [ht Y f hf s]
  simpa [hab] using congrFun this t

variable (L V) in
/-- Presieves jointly surjective on referents form a coverage; a referent of a pulled-back context
lifts to a context of its own. -/
def referentCoverage : Coverage (Context L V) where
  toPrecoverage := referentPrecoverage L V
  pullback := by
    intro c d g S hS
    refine ⟨fun Z h ↦ ∃ (W : Context L V) (i : Z ⟶ W) (e : W ⟶ c), S e ∧ i ≫ e = h ≫ g, ?_,
      fun Z h hh ↦ hh⟩
    change S ∈ referentPrecoverage L V c at hS
    rw [mem_referentPrecoverage_iff] at hS ⊢
    intro t
    obtain ⟨W, e, he, w, hw⟩ := hS (g.map t)
    exact ⟨⟨∅, {(t : V)}⟩, ⟨Finset.empty_subset _, fun _ ↦ t⟩,
      ⟨W, ⟨Finset.empty_subset _, fun _ ↦ w⟩, e, he, Context.hom_ext (funext fun _ ↦ hw)⟩,
      ⟨t, Finset.mem_singleton_self _⟩, rfl⟩

/-- Assignments are a sheaf for the topology of covers jointly surjective on referents. -/
theorem isSheaf_referentCoverage :
    Presieve.IsSheaf (referentCoverage L V).toGrothendieck (assignments L V M) :=
  (isSheaf_coverage _ _).2 fun _ ↦ isSheafFor_assignments

/-! ### Truth along a cover -/

namespace Cover

variable {ι : Type*} {C : Cover c ι}

theorem presieve_mem_referentPrecoverage (C : Cover c ι) :
    C.presieve ∈ referentPrecoverage L V c :=
  (ofArrows_mem_comap_jointlySurjectivePrecoverage_iff _).2 C.exists_map_eq

variable [L.Structure M] [Fintype ι] [DecidableEq V] [∀ n, DecidableEq (L.Relations n)]
  (x : ∀ i, Theory (C.part i))

/-- An assignment makes the renamed local literals of a family true exactly when its restriction
along every cover morphism realizes the local theory. -/
theorem realizers_pushforward : Literal.realizers M (C.pushforward x : Set (Literal c)) =
    ⋂ i, (· ∘ (C.map i).map) ⁻¹' Literal.realizers M ((x i).lits : Set (Literal (C.part i))) := by
  simp only [pushforward, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
    Finset.coe_image, Literal.realizers_iUnion, Literal.realizers_image_map]

/-- The realizers of the renamed local literals of a family, its least gluing when it has one, are
the compatible families of local realizers. -/
noncomputable def realizersEquiv :
    Literal.realizers M (C.pushforward x : Set (Literal c)) ≃
      {g : Subtype (Arrows.Compatible (assignments L V M) C.map) //
        ∀ i, g.1 i ∈ Literal.realizers M ((x i).lits : Set (Literal (C.part i)))} :=
  (Equiv.ofBijective _ ((isSheafFor_ofArrows_iff_bijective_toCompatible _ _).1
    (isSheafFor_assignments C.presieve_mem_referentPrecoverage))).subtypeEquiv fun g ↦
      (Set.ext_iff.1 (realizers_pushforward x) g).trans Set.mem_iInter

end Cover

end DRT
