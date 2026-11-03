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
on covers. An assignment [realizes the least gluing](##DRT.Cover.mem_realizers_iff) of a family
along a cover exactly when its restrictions realize the local theories, so the realizers of the
gluing are [the compatible families of local realizers](##DRT.Cover.realizersEquiv).

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

end Literal

namespace Theory

variable [L.Structure M]

variable (M) in
/-- The realizers of a theory are the assignments of the context's referents that make each of its
literals true. -/
def realizers (s : Theory c) : Set (c.vars → M) := {g | ∀ l ∈ s.lits, l.Holds g}

variable {s : Theory c}

theorem mem_realizers {g : c.vars → M} : g ∈ s.realizers M ↔ ∀ l ∈ s.lits, l.Holds g :=
  .rfl

/-- An embedding verifies the DRS of a theory exactly when its restriction to the context's
referents realizes the theory. -/
theorem verifies_toDRS_iff {g : V → M} :
    VerifiesTotal g s.toDRS ↔ g ∘ Subtype.val ∈ s.realizers M := by
  rw [verifiesTotal_iff, mem_realizers]
  simp only [toDRS, DRS.conditions_mk, List.mem_map, Finset.mem_toList, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun l _ ↦ ?_
  rw [Literal.holds_comp_val_iff]
  unfold Literal.toCondition
  cases l.pos <;> simp [Box.Extends, ← funext_iff]

theorem comp_val_mem_realizers_iff (hpos : ∀ l ∈ s.lits, l.pos) {g : V → M} :
    g ∘ Subtype.val ∈ s.realizers M ↔
      g ∈ Atom.realizers M (Literal.atom '' (s.lits : Set (Literal c))) := by
  simp only [mem_realizers, Literal.holds_comp_val_iff, Atom.mem_realizers, Set.forall_mem_image,
    Finset.mem_coe]
  exact forall₂_congr fun l hl ↦ by simp [hpos l hl]

variable [DecidableEq V] [∀ n, DecidableEq (L.Relations n)]

theorem comp_mem_realizers_restrict {f : c ⟶ c'} {s : Theory c'} {g : c'.vars → M}
    (h : g ∈ s.realizers M) : g ∘ f.map ∈ (s.restrict f).realizers M :=
  fun _ hl ↦ h _ (mem_restrict.1 hl)

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
  refine hab (congrFun (h.isSeparatedFor (fun _ _ _ _ ↦ a) (fun _ ↦ a)
    (Function.update (fun _ ↦ a) t b) (fun _ _ _ ↦ rfl) fun Y f hf ↦ funext fun s ↦ ?_) t |>.trans
    (Function.update_self ..))
  show Function.update (fun _ ↦ a) t b (f.map s) = a
  exact Function.update_of_ne (ht Y f hf s) _ _

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
  {x : ∀ i, Theory (C.part i)} {s : Theory c}

/-- An assignment realizes the least gluing of a family exactly when its restriction along every
cover morphism realizes the local theory. -/
theorem mem_realizers_iff (hs : s.lits = C.pushforward x) {g : c.vars → M} :
    g ∈ s.realizers M ↔ ∀ i, g ∘ (C.map i).map ∈ (x i).realizers M := by
  simp only [Theory.mem_realizers, hs, mem_pushforward, forall_exists_index, and_imp]
  exact ⟨fun h i m hm ↦ h _ i m hm rfl, by rintro h _ i m hm rfl; exact h i m hm⟩

/-- The realizers of the least gluing of a family are the compatible families of local
realizers. -/
noncomputable def realizersEquiv (hs : s.lits = C.pushforward x) :
    s.realizers M ≃ {g : ∀ i, (x i).realizers M //
      Arrows.Compatible (assignments L V M) C.map fun i ↦ (g i).1} :=
  ((Equiv.ofBijective _ ((isSheafFor_ofArrows_iff_bijective_toCompatible _ _).1
    (isSheafFor_assignments C.presieve_mem_referentPrecoverage))).subtypeEquiv
      (q := fun g ↦ ∀ i, g.1 i ∈ (x i).realizers M) fun _ ↦ mem_realizers_iff hs).trans
    { toFun g := ⟨fun i ↦ ⟨g.1.1 i, g.2 i⟩, g.1.2⟩
      invFun g := ⟨⟨fun i ↦ (g.1 i).1, g.2⟩, fun i ↦ (g.1 i).2⟩ }

end Cover

end DRT
