module

public import Linglib.Semantics.Dynamic.DRS.Presheaf
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.JointlySurjective
public import Mathlib.Data.Fintype.Inv
public import Mathlib.Data.Finset.Union
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Gluing basic DRSs

This file shows that basic DRSs form a sheaf and identifies the topology. A presieve on a context
covers it when it is jointly surjective on literals: every literal of the context renames a
literal of some member. A compatible family of local theories over any presieve has an
amalgamation, the renamings of the local literals, and the amalgamation is unique iff the
presieve covers; these covers form a coverage, for which basic DRSs are a sheaf.

[abramsky-sadrzadeh-2014] glue along covers jointly surjective on referents and on the
vocabulary. Along such a cover the renamings of the local literals are the least candidate: a
gluing exists iff they are consistent and restrict back to every part, it is unique when the
cover is jointly surjective on literals too, and it always exists when the local vocabularies are
pairwise disjoint and the cover maps injective. Read on DRSs, it is then the merge of the renamed
local DRSs: discourse representation theory's merge followed by unification of referents.

## Main definitions

* `DRT.literalCoverage`: the coverage of presieves jointly surjective on literals.
* `DRT.amalgamate`: the amalgamation of a compatible family.
* `DRT.Cover`, `DRT.Cover.IsGluing`: covers in the paper's sense, and gluing along them.

## Main statements

* `DRT.isSeparatedFor_iff`, `DRT.isSheafFor_iff`, `DRT.isSheaf_literalCoverage`: basic DRSs are
  separated, and a sheaf, for a presieve iff it is jointly surjective on literals.
* `DRT.Cover.exists_isGluing_iff`: a gluing exists iff the renamed local literals form one.
* `DRT.Cover.coe_conditions_toDRS_glue`: under disjoint vocabularies and injective cover maps the
  gluing is the merge of the renamed local DRSs.

## Implementation notes

Compatibility is tested on contexts with fresh referents for the arguments of a relation, so
amalgamation assumes that `V` has as many referents as each arity in the vocabulary;
`isSheaf_literalCoverage` assumes `V` infinite, like the paper's variables.

## References

* [abramsky-sadrzadeh-2014]
* [mac-lane-moerdijk-1992]
-/

@[expose] public section

open CategoryTheory FirstOrder Presieve

namespace DRT

universe u v w

variable {L : Language.{u, v}} {V : Type w} {c : Context L V} {R : Presieve c}

/-! ### Literal covers -/

variable (L V) in
/-- A presieve belongs to the literal precoverage when every literal of the context renames a
literal of some member. -/
abbrev literalPrecoverage : Precoverage (Context L V) :=
  Types.jointlySurjectivePrecoverage.comap (Literal.functor L V)

theorem mem_literalPrecoverage_iff : R ∈ literalPrecoverage L V c ↔
    ∀ l : Literal c, ∃ (Y : Context L V) (f : Y ⟶ c), R f ∧ ∃ m : Literal Y, m.map f = l := by
  simp only [mem_comap_jointlySurjectivePrecoverage_iff, Set.mem_range, Literal.functor_map]
  rfl

section Sheaf

variable [DecidableEq V]

variable (L V) in
/-- Presieves jointly surjective on literals form a coverage; a literal over a pulled-back
context lifts to the context of its own arguments. -/
def literalCoverage : Coverage (Context L V) where
  toPrecoverage := literalPrecoverage L V
  pullback := by
    intro c d g S hS
    refine ⟨fun Z h => ∃ (W : Context L V) (i : Z ⟶ W) (e : W ⟶ c), S e ∧ i ≫ e = h ≫ g, ?_,
      fun Z h hh => hh⟩
    change S ∈ literalPrecoverage L V c at hS
    rw [mem_literalPrecoverage_iff] at hS ⊢
    rintro ⟨⟨r, hr⟩, a, p⟩
    obtain ⟨W, e, he, ⟨⟨r', hr'⟩, a', p'⟩, hm⟩ := hS (Literal.map g ⟨⟨r, hr⟩, a, p⟩)
    obtain ⟨h₁, h₂, rfl⟩ := Literal.mk.inj hm.symm
    obtain rfl : r = r' := congrArg Subtype.val h₁
    have ha : g.map ∘ a = e.map ∘ a' := eq_of_heq h₂
    let Z : Context L V := ⟨{r}, Finset.univ.image fun k => (a k : V)⟩
    have hk (t : Z.vars) : ∃ k, (a k : V) = t := by
      obtain ⟨k, -, hk⟩ := Finset.mem_image.1 t.2; exact ⟨k, hk⟩
    refine ⟨Z, ⟨Finset.singleton_subset_iff.2 hr, fun t => ⟨t, ?_⟩⟩,
      ⟨W, ⟨Finset.singleton_subset_iff.2 hr', fun t => a' (hk t).choose⟩, e, he, ?_⟩,
      ⟨⟨r, Finset.mem_singleton_self r⟩, fun k => ⟨a k, ?_⟩, p⟩, rfl⟩
    · obtain ⟨k, hk⟩ := hk t; exact hk ▸ (a k).2
    · refine Context.hom_ext (funext fun t => ?_)
      have := congrFun ha (hk t).choose
      simp only [Function.comp_apply] at this
      simp only [Context.comp_map, Function.comp_apply, ← this]
      exact congrArg _ (Subtype.ext (hk t).choose_spec)
    · simp [Z]

/-! ### Amalgamation -/

namespace Literal

/-- `testCtx r e` has the one relation symbol `r` and the referents `e 0, …, e (n - 1)`. -/
private def testCtx (r : Σ n, L.Relations n) (e : Fin r.1 ↪ V) : Context L V :=
  ⟨{r}, Finset.univ.map e⟩

/-- `testLit r e p` is the literal `±r(e 0, …, e (n - 1))`. -/
private def testLit (r : Σ n, L.Relations n) (e : Fin r.1 ↪ V) (p : Bool) :
    Literal (testCtx r e) :=
  ⟨⟨r, Finset.mem_singleton_self r⟩, fun k => ⟨e k, Finset.mem_map_of_mem _ (Finset.mem_univ k)⟩,
    p⟩

/-- `testHom e hr a` sends `e k` to `a k`. -/
private def testHom {r : Σ n, L.Relations n} (e : Fin r.1 ↪ V) {d : Context L V}
    (hr : r ∈ d.vocab) (a : Fin r.1 → d.vars) : testCtx r e ⟶ d :=
  ⟨Finset.singleton_subset_iff.2 hr, fun t =>
    a (e.invOfMemRange ⟨t, by obtain ⟨k, -, hk⟩ := Finset.mem_map.1 t.2; exact ⟨k, hk⟩⟩)⟩

private theorem testLit_map {r : Σ n, L.Relations n} (e : Fin r.1 ↪ V) {d : Context L V}
    (hr : r ∈ d.vocab) (a : Fin r.1 → d.vars) (p : Bool) :
    (testLit r e p).map (testHom e hr a) = ⟨⟨r, hr⟩, a, p⟩ := by
  simp only [testLit, testHom, map, Function.comp_def,
    Function.Embedding.right_inv_of_invOfMemRange]

end Literal

open Literal

variable [∀ n, DecidableEq (L.Relations n)]

variable {x : FamilyOfElements (presheaf L V) R}

theorem mem_of_compatible (hx : x.Compatible) {Y₁ Y₂ : Context L V} {f₁ : Y₁ ⟶ c}
    {f₂ : Y₂ ⟶ c} (h₁ : R f₁) (h₂ : R f₂) {l : Literal Y₁} {m : Literal Y₂}
    (hlm : l.map f₁ = m.map f₂) (hm : m ∈ Theory.lits (x f₂ h₂)) (e : Fin l.rel.1.1 ↪ V) :
    l ∈ Theory.lits (x f₁ h₁) := by
  obtain ⟨⟨r, hr⟩, a, p⟩ := l
  obtain ⟨⟨r', hr'⟩, a', p'⟩ := m
  obtain ⟨h₁', h₂', rfl⟩ := Literal.mk.inj hlm
  obtain rfl : r = r' := congrArg Subtype.val h₁'
  have hc := hx (testHom e hr a) (testHom e hr' a') h₁ h₂ (Context.hom_ext (funext fun t => by
    simpa [testHom] using congrFun (eq_of_heq h₂') _))
  simp only [presheaf_map, Quiver.Hom.unop_op] at hc
  have := Theory.mem_restrict.2 ((testLit_map e hr' a' p).symm ▸ hm :
    (testLit r e p).map (testHom e hr' a') ∈ Theory.lits (x f₂ h₂))
  rwa [← hc, Theory.mem_restrict, testLit_map] at this

variable (hx : x.Compatible) (hc : ∀ r ∈ c.vocab, Nonempty (Fin r.1 ↪ V))
include hx hc

private theorem mem_of_compatible' {Y Z : Context L V} {f : Y ⟶ c} {g : Z ⟶ c} (hf : R f)
    (hg : R g) {l : Literal Y} {m : Literal Z} (hlm : l.map f = m.map g)
    (hm : m ∈ Theory.lits (x g hg)) : l ∈ Theory.lits (x f hf) :=
  mem_of_compatible hx hf hg hlm hm (hc _ (f.incl l.rel.2)).some

/-- The amalgamation of a compatible family holds the renamings of the local literals. -/
noncomputable def amalgamate : Theory c where
  lits := by classical exact Finset.univ.filter fun l =>
    ∃ (Y : Context L V) (f : Y ⟶ c) (hf : R f), ∃ m ∈ Theory.lits (x f hf), m.map f = l
  consistent l hl hn := by
    classical
    obtain ⟨Y, f, hf, m, hm, rfl⟩ := (Finset.mem_filter.1 hl).2
    obtain ⟨Z, g, hg, m', hm', h⟩ := (Finset.mem_filter.1 hn).2
    rw [neg_map] at h
    exact Theory.consistent _ m hm (mem_of_compatible' hx hc hf hg h.symm hm')

theorem isAmalgamation_amalgamate : x.IsAmalgamation (amalgamate hx hc) := fun Y f hf => by
  classical
  refine Theory.ext (Finset.ext fun l => ?_)
  simp only [presheaf_map, Quiver.Hom.unop_op, Theory.mem_restrict, amalgamate,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨Z, g, hg, m, hm, h⟩ => mem_of_compatible' hx hc hf hg h.symm hm,
    fun hl => ⟨Y, f, hf, l, hl, rfl⟩⟩

omit hx hc

/-! ### The sheaf condition -/

theorem isSeparatedFor_iff : R.IsSeparatedFor (presheaf L V) ↔ R ∈ literalPrecoverage L V c := by
  rw [mem_literalPrecoverage_iff]
  refine ⟨fun h l => by_contra fun hl => ?_, fun h x t₁ t₂ h₁ h₂ => ?_⟩
  · push Not at hl
    let t : Theory c := ⟨{l}, by
      simp only [Literal.Consistent, Finset.mem_singleton]
      rintro _ rfl
      exact neg_ne_self _⟩
    refine (show (⊥ : Theory c) ≠ t from fun h => by simpa [t] using congrArg Theory.lits h)
      (h (fun _ _ _ => (⊥ : Theory _)) (⊥ : Theory c) t (fun _ f _ => Theory.restrict_bot f)
        fun Y f hf => Theory.ext (Finset.ext fun m => ?_))
    simp only [presheaf_map, Quiver.Hom.unop_op, Theory.mem_restrict, t, Finset.mem_singleton,
      hl Y f hf m]
    exact iff_of_false id (Finset.notMem_empty m)
  · refine Theory.ext (Finset.ext fun l => ?_)
    obtain ⟨Y, f, hf, m, rfl⟩ := h l
    rw [← Theory.mem_restrict, ← Theory.mem_restrict]
    change m ∈ ((presheaf L V).map f.op t₁).lits ↔ m ∈ ((presheaf L V).map f.op t₂).lits
    rw [h₁ f hf, h₂ f hf]

theorem isSheafFor_iff (hc : ∀ r ∈ c.vocab, Nonempty (Fin r.1 ↪ V)) :
    R.IsSheafFor (presheaf L V) ↔ R ∈ literalPrecoverage L V c := by
  rw [← isSeparatedFor_iff, ← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  exact and_iff_left fun x hx => ⟨_, isAmalgamation_amalgamate hx hc⟩

theorem isSheaf_literalCoverage [Infinite V] :
    Presieve.IsSheaf (literalCoverage L V).toGrothendieck (presheaf L V) :=
  (isSheaf_coverage _ _).2 fun _ hR => (isSheafFor_iff fun _ _ =>
    ⟨Fin.valEmbedding.trans (Infinite.natEmbedding V)⟩).2 hR

end Sheaf

/-! ### Covers -/

/-- A cover of a context, in [abramsky-sadrzadeh-2014]'s sense, is a family of context morphisms
jointly surjective on referents and on the vocabulary (`⋃ Im fᵢ = X` and `L = ⋃ Lᵢ`). -/
structure Cover (c : Context L V) (ι : Type*) where
  /-- The covering contexts. -/
  part : ι → Context L V
  /-- The covering morphisms. -/
  map : ∀ i, part i ⟶ c
  /-- Every referent is the image of a referent of some part. -/
  exists_map_eq : ∀ x : c.vars, ∃ i y, (map i).map y = x
  /-- Every relation symbol is in the vocabulary of some part. -/
  exists_mem_vocab : ∀ r ∈ c.vocab, ∃ i, r ∈ (part i).vocab

namespace Cover

variable {ι : Type*} (C : Cover c ι)

/-- `C.presieve` is the presieve of the covering morphisms. -/
abbrev presieve : Presieve c := Presieve.ofArrows C.part C.map

/-- `s` glues the family `x` over the cover when `P(fᵢ)(s) = xᵢ` for every `i`. -/
def IsGluing (P : (Context L V)ᵒᵖ ⥤ Type*) (x : ∀ i, P.obj (Opposite.op (C.part i)))
    (s : P.obj (Opposite.op c)) : Prop :=
  ∀ i, P.map (C.map i).op s = x i

variable {C}

theorem presieve_mem_literalPrecoverage_iff : C.presieve ∈ literalPrecoverage L V c ↔
    ∀ l : Literal c, ∃ i, ∃ m : Literal (C.part i), m.map (C.map i) = l := by
  simp only [ofArrows_mem_comap_jointlySurjectivePrecoverage_iff, Set.mem_range,
    Literal.functor_map]
  rfl

theorem eq_of_map_eq (hdisj : Pairwise fun i j => Disjoint (C.part i).vocab (C.part j).vocab)
    {i j : ι} {m : Literal (C.part i)} {m' : Literal (C.part j)}
    (h : m.map (C.map i) = m'.map (C.map j)) : i = j :=
  by_contra fun hij => Finset.disjoint_left.1 (hdisj hij) m.rel.2
    (by rw [show m.rel.1 = m'.rel.1 from congrArg (fun l : Literal c => l.rel.1) h]; exact m'.rel.2)

variable [DecidableEq V] [∀ n, DecidableEq (L.Relations n)] {x : ∀ i, Theory (C.part i)}
  {s s' : Theory c}

instance [Fintype ι] : Decidable (C.IsGluing (presheaf L V) x s) :=
  inferInstanceAs (Decidable (∀ i, s.restrict (C.map i) = x i))

/-- `C.pushforward x` holds the renamings of the local literals, `{±A(fᵢ(x̄)) | ±A(x̄) ∈ sᵢ}`. -/
def pushforward [Fintype ι] (C : Cover c ι) (x : ∀ i, Theory (C.part i)) : Finset (Literal c) :=
  Finset.univ.biUnion fun i => (x i).lits.image (Literal.map (C.map i))

@[simp] theorem mem_pushforward [Fintype ι] {l : Literal c} :
    l ∈ C.pushforward x ↔ ∃ i, ∃ m ∈ (x i).lits, m.map (C.map i) = l := by
  simp [pushforward]

variable [Fintype ι]

instance : Decidable (C.presieve ∈ literalPrecoverage L V c) :=
  decidable_of_iff _ presieve_mem_literalPrecoverage_iff.symm

theorem IsGluing.pushforward_subset (hs : C.IsGluing (presheaf L V) x s) :
    C.pushforward x ⊆ s.lits := by
  intro l hl
  obtain ⟨i, m, hm, rfl⟩ := mem_pushforward.1 hl
  rw [← hs i] at hm
  exact Theory.mem_restrict.1 hm

theorem exists_isGluing_iff : (∃ s, C.IsGluing (presheaf L V) x s) ↔
    ∃ h : Literal.Consistent (C.pushforward x), C.IsGluing (presheaf L V) x ⟨_, h⟩ := by
  refine ⟨fun ⟨s, hs⟩ => ⟨s.consistent.mono hs.pushforward_subset, fun i => ?_⟩,
    fun ⟨_, h⟩ => ⟨_, h⟩⟩
  refine Theory.ext (Finset.ext fun l => ?_)
  simp only [presheaf_map, Quiver.Hom.unop_op, Theory.mem_restrict]
  refine ⟨fun hl => ?_, fun hl => mem_pushforward.2 ⟨i, l, hl, rfl⟩⟩
  rw [← hs i]
  exact Theory.mem_restrict.2 (hs.pushforward_subset hl)

theorem IsGluing.unique (hC : C.presieve ∈ literalPrecoverage L V c)
    (hs : C.IsGluing (presheaf L V) x s) (hs' : C.IsGluing (presheaf L V) x s') : s = s' := by
  have (t : Theory c) (ht : C.IsGluing (presheaf L V) x t) : t.lits = C.pushforward x :=
    subset_antisymm (fun l hl => by
      obtain ⟨i, m, rfl⟩ := presieve_mem_literalPrecoverage_iff.1 hC l
      exact mem_pushforward.2 ⟨i, m, by rw [← ht i]; exact Theory.mem_restrict.2 hl, rfl⟩)
      ht.pushforward_subset
  exact Theory.ext ((this s hs).trans (this s' hs').symm)

/-! ### Disjoint vocabularies -/

/-- `C.glue` is the theory of the renamed local literals, consistent when the vocabularies are
pairwise disjoint and the cover maps injective. -/
def glue (C : Cover c ι) (hdisj : Pairwise fun i j => Disjoint (C.part i).vocab (C.part j).vocab)
    (hinj : ∀ i, Function.Injective (C.map i).map) (x : ∀ i, Theory (C.part i)) : Theory c where
  lits := C.pushforward x
  consistent _ hl hn := by
    obtain ⟨i, m, hm, rfl⟩ := mem_pushforward.1 hl
    obtain ⟨j, m', hm', h⟩ := mem_pushforward.1 hn
    rw [Literal.neg_map] at h
    obtain rfl : i = j := (eq_of_map_eq hdisj h).symm
    exact (x i).consistent m hm (Literal.map_injective (hinj i) h ▸ hm')

variable (hdisj : Pairwise fun i j => Disjoint (C.part i).vocab (C.part j).vocab)
  (hinj : ∀ i, Function.Injective (C.map i).map) (x)

theorem isGluing_glue : C.IsGluing (presheaf L V) x (C.glue hdisj hinj x) := fun i =>
  Theory.ext (Finset.ext fun l => by
    simp only [presheaf_map, Quiver.Hom.unop_op, Theory.mem_restrict, glue, mem_pushforward]
    grind [eq_of_map_eq, Literal.map_injective])

theorem referents_toDRS_glue : (C.glue hdisj hinj x).toDRS.referents =
    Finset.univ.biUnion fun i => ((x i).toDRS.map (C.map i).extend).referents := by
  ext t
  simp only [Theory.referents_toDRS, DRS.referents_map, Finset.mem_biUnion, Finset.mem_univ,
    Finset.mem_image, true_and]
  constructor
  · intro ht
    obtain ⟨i, y, hy⟩ := C.exists_map_eq ⟨t, ht⟩
    exact ⟨i, y, y.2, by rw [Context.Hom.extend_coe, hy]⟩
  · rintro ⟨i, y, hy, rfl⟩
    rw [show (C.map i).extend y = _ from Context.Hom.extend_coe (C.map i) ⟨y, hy⟩]
    exact ((C.map i).map ⟨y, hy⟩).2

theorem coe_conditions_toDRS_glue :
    ((C.glue hdisj hinj x).toDRS.conditions : Multiset (Condition L V)) =
      ∑ i, (((x i).toDRS.map (C.map i).extend).conditions : Multiset (Condition L V)) := by
  have hpd : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      fun i => (x i).lits.image (Literal.map (C.map i)) := fun _ _ _ _ hij =>
    Finset.disjoint_left.2 fun l hi hj => by
      obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨m', -, h⟩ := Finset.mem_image.1 hj
      exact hij (eq_of_map_eq hdisj h.symm)
  rw [Theory.coe_conditions_toDRS, Finset.sum_eq_multiset_sum]
  change (Finset.univ.biUnion _).val.map _ = _
  rw [← Finset.disjiUnion_eq_biUnion _ _ hpd, Finset.disjiUnion_val, Multiset.map_bind]
  change (Finset.univ.val.map _).sum = _
  refine congrArg _ (Multiset.map_congr rfl fun i _ => ?_)
  rw [Finset.image_val,
    Multiset.dedup_eq_self.2 ((x i).lits.nodup.map (Literal.map_injective (hinj i))),
    Multiset.map_map, DRS.conditions_map, ← Multiset.map_coe, Theory.coe_conditions_toDRS,
    Multiset.map_map]
  exact Multiset.map_congr rfl fun l _ => Literal.toCondition_map _ l

end Cover

end DRT
