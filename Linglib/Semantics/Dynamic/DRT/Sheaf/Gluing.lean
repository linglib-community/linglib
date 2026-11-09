module

public import Linglib.Semantics.Dynamic.DRT.Sheaf.Presheaf
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.JointlySurjective
public import Mathlib.Data.Fintype.Inv
public import Mathlib.Data.Finset.Union
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Gluing basic DRSs

This file shows that basic DRSs form a sheaf. A presieve on a context is jointly surjective on
literals when every literal of the context renames a literal of some member. Sets of literals
amalgamate along any presieve and consistency is local, so basic DRSs are
[separated](##DRT.Context.DRS.isSeparatedFor_iff), and [a sheaf](##DRT.Context.DRS.isSheafFor_iff),
for a presieve exactly when it is jointly surjective on literals; these presieves form a coverage
for which basic DRSs are [a sheaf](##DRT.Context.DRS.isSheaf_literalCoverage). Abramsky and
Sadrzadeh glue along covers jointly surjective on referents and on the vocabulary: a family glues
[exactly when it is compatible](##DRT.Context.Cover.exists_isGluing_iff_compatible), and the
renamings of its local literals are then [the least
gluing](##DRT.Context.Cover.exists_isGluing_iff). Under pairwise disjoint vocabularies and injective
cover maps every family glues, to [the merge of the renamed local
DRSs](##DRT.Context.Cover.coe_conditions_toDRS_glue).

## Implementation notes

Amalgamation needs as many referents as each arity in the vocabulary, so
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

/-! ### Comparing literals

Compatibility speaks of restrictions along maps out of a common context, not of literals. To
compare a literal `l` of one member with a literal `m` of another that renames to the same literal,
`freshCtx r e` supplies that context: its literal `freshLit r e p` has pairwise distinct
arguments, so `freshHom` maps it onto both `l` and `m`. Distinct arguments need as many referents
as the arity of `r`, the hypothesis amalgamation carries. -/

namespace Literal

variable [DecidableEq V]

/-- `freshCtx r e` has the one relation symbol `r` and the distinct referents
`e 0, …, e (n - 1)`. -/
private def freshCtx (r : Σ n, L.Relations n) (e : Fin r.1 ↪ V) : Context L V :=
  ⟨{r}, Finset.univ.map e⟩

/-- `freshLit r e p` is the literal `±r(e 0, …, e (n - 1))`. -/
private def freshLit (r : Σ n, L.Relations n) (e : Fin r.1 ↪ V) (p : Bool) :
    Literal (freshCtx r e) :=
  ⟨⟨r, Finset.mem_singleton_self r⟩, fun k ↦ ⟨e k, Finset.mem_map_of_mem _ (Finset.mem_univ k)⟩,
    p⟩

/-- `freshHom e hr a` sends `e k` to `a k`. -/
private def freshHom {r : Σ n, L.Relations n} (e : Fin r.1 ↪ V) {d : Context L V}
    (hr : r ∈ d.vocab) (a : Fin r.1 → d.vars) : freshCtx r e ⟶ d :=
  ⟨Finset.singleton_subset_iff.2 hr, fun t ↦
    a (e.invOfMemRange ⟨t, by obtain ⟨k, -, hk⟩ := Finset.mem_map.1 t.2; exact ⟨k, hk⟩⟩)⟩

/-- `freshHom` maps `freshLit` onto any literal of `r` with the same sign. -/
private theorem freshLit_map {r : Σ n, L.Relations n} (e : Fin r.1 ↪ V) {d : Context L V}
    (hr : r ∈ d.vocab) (a : Fin r.1 → d.vars) (p : Bool) :
    (freshLit r e p).map (freshHom e hr a) = ⟨⟨r, hr⟩, a, p⟩ := by
  simp only [freshLit, freshHom, map, Function.comp_def,
    Function.Embedding.right_inv_of_invOfMemRange]

end Literal

namespace Context

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
    refine ⟨((Sieve.generate S).pullback g).arrows, ?_, fun _ _ h ↦ h⟩
    change S ∈ literalPrecoverage L V c at hS
    rw [mem_literalPrecoverage_iff] at hS ⊢
    rintro ⟨⟨r, hr⟩, a, p⟩
    obtain ⟨W, e, he, ⟨⟨r', hr'⟩, a', p'⟩, hm⟩ := hS (Literal.map g ⟨⟨r, hr⟩, a, p⟩)
    obtain ⟨h₁, h₂, rfl⟩ := Literal.mk.inj hm.symm
    obtain rfl : r = r' := congrArg Subtype.val h₁
    have ha : g.map ∘ a = e.map ∘ a' := eq_of_heq h₂
    let Z : Context L V := ⟨{r}, Finset.univ.image fun k ↦ (a k : V)⟩
    have hk (t : Z.vars) : ∃ k, (a k : V) = t := by
      obtain ⟨k, -, hk⟩ := Finset.mem_image.1 t.2; exact ⟨k, hk⟩
    refine ⟨Z, ⟨Finset.singleton_subset_iff.2 hr, fun t ↦ ⟨t, ?_⟩⟩,
      ⟨W, ⟨Finset.singleton_subset_iff.2 hr', fun t ↦ a' (hk t).choose⟩, e, he, ?_⟩,
      ⟨⟨r, Finset.mem_singleton_self r⟩, fun k ↦ ⟨a k, ?_⟩, p⟩, rfl⟩
    · obtain ⟨k, hk⟩ := hk t; exact hk ▸ (a k).2
    · refine Context.hom_ext (funext fun t ↦ ?_)
      have := congrFun ha (hk t).choose
      simp only [Function.comp_apply] at this
      simp only [Context.comp_map, Function.comp_apply, ← this]
      exact congrArg _ (Subtype.ext (hk t).choose_spec)
    · simp [Z]

/-! ### Amalgamation -/

open Literal

variable [∀ n, DecidableEq (L.Relations n)]

section LiteralSets

variable {x : FamilyOfElements (literalSets L V) R}

/-- Members of a compatible family agree on literals whose arguments the presieve identifies. -/
theorem mem_iff_of_compatible (hx : x.Compatible) {Y₁ Y₂ : Context L V} {f₁ : Y₁ ⟶ c}
    {f₂ : Y₂ ⟶ c} (h₁ : R f₁) (h₂ : R f₂) {r : Σ n, L.Relations n} (hr₁ : r ∈ Y₁.vocab)
    (hr₂ : r ∈ Y₂.vocab) {a₁ : Fin r.1 → Y₁.vars} {a₂ : Fin r.1 → Y₂.vars}
    (ha : f₁.map ∘ a₁ = f₂.map ∘ a₂) (p : Bool) (e : Fin r.1 ↪ V) :
    ⟨⟨r, hr₁⟩, a₁, p⟩ ∈ x f₁ h₁ ↔ ⟨⟨r, hr₂⟩, a₂, p⟩ ∈ x f₂ h₂ := by
  have := hx (freshHom e hr₁ a₁) (freshHom e hr₂ a₂) h₁ h₂
    (Context.hom_ext (funext fun t ↦ by simpa [freshHom] using congrFun ha _))
  simpa [freshLit_map] using congrArg (freshLit r e p ∈ ·) this

/-- `amalgamate x` holds the renamings of the literals of the members of `x`. -/
noncomputable def amalgamate (x : FamilyOfElements (literalSets L V) R) : Finset (Literal c) := by
  classical exact Finset.univ.filter fun l ↦
    ∃ (Y : Context L V) (f : Y ⟶ c) (hf : R f), ∃ m ∈ x f hf, m.map f = l

@[simp] theorem mem_amalgamate {l : Literal c} :
    l ∈ amalgamate x ↔ ∃ (Y : Context L V) (f : Y ⟶ c) (hf : R f), ∃ m ∈ x f hf, m.map f = l := by
  classical simp [amalgamate]

/-- Given as many referents as each arity in the vocabulary, a compatible family of sets of
literals amalgamates to the renamings of its literals. -/
theorem isAmalgamation_amalgamate (hx : x.Compatible)
    (hc : ∀ r ∈ c.vocab, Nonempty (Fin r.1 ↪ V)) : x.IsAmalgamation (amalgamate x) :=
  fun Y f hf ↦ by
    change Literal.preimage f (amalgamate x) = x f hf
    ext l
    simp only [mem_preimage, mem_amalgamate]
    refine ⟨fun ⟨Z, g, hg, m, hm, h⟩ ↦ ?_, fun hl ↦ ⟨Y, f, hf, l, hl, rfl⟩⟩
    obtain ⟨⟨r, hr⟩, a, p⟩ := l
    obtain ⟨⟨r', hr'⟩, a', p'⟩ := m
    obtain ⟨h₁, h₂, rfl⟩ := Literal.mk.inj h
    obtain rfl : r' = r := congrArg Subtype.val h₁
    exact (mem_iff_of_compatible hx hf hg hr hr' (eq_of_heq h₂).symm _
      (hc _ (f.incl hr)).some).2 hm

theorem isSeparatedFor_literalSets (hR : R ∈ literalPrecoverage L V c) :
    R.IsSeparatedFor (literalSets L V) := fun _ t₁ t₂ h₁ h₂ ↦ by
  ext l
  obtain ⟨Y, f, hf, m, rfl⟩ := mem_literalPrecoverage_iff.1 hR l
  simpa using congrArg (m ∈ ·) ((h₁ f hf).trans (h₂ f hf).symm)

end LiteralSets

/-! ### The sheaf condition -/

namespace DRS

/-- Given as many referents as each arity in the vocabulary, a compatible family of basic DRSs has
an amalgamation, consistent because each of its literals comes from a member. -/
theorem exists_isAmalgamation {x : FamilyOfElements (presheaf L V) R} (hx : x.Compatible)
    (hc : ∀ r ∈ c.vocab, Nonempty (Fin r.1 ↪ V)) : ∃ t, x.IsAmalgamation t := by
  have ht := isAmalgamation_amalgamate (hx.map (consistentLiteralSets L V).ι) hc
  refine ⟨⟨_, Consistent.of_preimage fun l hl ↦ ?_⟩, fun Y f hf ↦ Subtype.ext (ht f hf)⟩
  obtain ⟨Y, f, hf, m, -, rfl⟩ := mem_amalgamate.1 hl
  exact ⟨Y, f, ⟨m, rfl⟩, (congrArg Consistent (ht f hf)).mpr (x f hf).2⟩

/-- Basic DRSs are separated for a presieve iff it is jointly surjective on literals. -/
theorem isSeparatedFor_iff : R.IsSeparatedFor (presheaf L V) ↔ R ∈ literalPrecoverage L V c := by
  refine ⟨fun h ↦ mem_literalPrecoverage_iff.2 fun l ↦ by_contra fun hl ↦ ?_, fun hR x _ _ h₁ h₂ ↦
    Subtype.ext (isSeparatedFor_literalSets hR _ _ _ (h₁.map (consistentLiteralSets L V).ι)
      (h₂.map (consistentLiteralSets L V).ι))⟩
  push Not at hl
  have := h (fun _ _ _ ↦ ⟨∅, consistent_empty⟩) ⟨∅, consistent_empty⟩ ⟨{l}, consistent_singleton l⟩
    (fun _ _ _ ↦ Subtype.ext (by ext; simp))
    fun Y f hf ↦ Subtype.ext (by ext m; simpa using hl Y f hf m)
  simpa using congrArg Subtype.val this

/-- Basic DRSs are a sheaf for a presieve iff it is jointly surjective on literals. -/
theorem isSheafFor_iff (hc : ∀ r ∈ c.vocab, Nonempty (Fin r.1 ↪ V)) :
    R.IsSheafFor (presheaf L V) ↔ R ∈ literalPrecoverage L V c := by
  rw [← isSeparatedFor_iff, ← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  exact and_iff_left fun _ hx ↦ exists_isAmalgamation hx hc

/-- Basic DRSs are a sheaf for the topology of covers jointly surjective on literals. -/
theorem isSheaf_literalCoverage [Infinite V] :
    Presieve.IsSheaf (literalCoverage L V).toGrothendieck (presheaf L V) :=
  (isSheaf_coverage _ _).2 fun _ hR ↦ (isSheafFor_iff fun _ _ ↦
    ⟨Fin.valEmbedding.trans (Infinite.natEmbedding V)⟩).2 hR

end DRS

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

/-- A family with a gluing is compatible. -/
theorem IsGluing.compatible {P : (Context L V)ᵒᵖ ⥤ Type*}
    {x : ∀ i, P.obj (Opposite.op (C.part i))} {s : P.obj (Opposite.op c)} (hs : C.IsGluing P x s) :
    Arrows.Compatible P C.map x :=
  funext hs ▸ (Arrows.toCompatible P C.map s).2

/-- A cover is jointly surjective on literals iff one part carries each relation symbol together
with each tuple of its arguments, the sign playing no role; covers carry the symbols and the
referents only separately. -/
theorem presieve_mem_literalPrecoverage_iff : C.presieve ∈ literalPrecoverage L V c ↔
    ∀ (r : c.vocab) (a : Fin r.1.1 → c.vars),
      ∃ i, r.1 ∈ (C.part i).vocab ∧ ∃ a' : Fin r.1.1 → (C.part i).vars, (C.map i).map ∘ a' = a := by
  simp only [ofArrows_mem_comap_jointlySurjectivePrecoverage_iff, Set.mem_range,
    Literal.functor_map]
  refine ⟨fun h r a ↦ ?_, fun h ⟨r, a, p⟩ ↦ ?_⟩
  · obtain ⟨i, ⟨⟨r', hr'⟩, a', p'⟩, hm⟩ := h ⟨r, a, true⟩
    obtain ⟨h₁, h₂, -⟩ := Literal.mk.inj hm
    obtain rfl : r' = r.1 := congrArg Subtype.val h₁
    exact ⟨i, hr', a', eq_of_heq h₂⟩
  · obtain ⟨i, hr, a', rfl⟩ := h r a
    exact ⟨i, ⟨⟨r.1, hr⟩, a', p⟩, rfl⟩

theorem eq_of_map_eq (hdisj : Pairwise fun i j ↦ Disjoint (C.part i).vocab (C.part j).vocab)
    {i j : ι} {m : Literal (C.part i)} {m' : Literal (C.part j)}
    (h : m.map (C.map i) = m'.map (C.map j)) : i = j :=
  hdisj.eq <| Finset.not_disjoint_iff.2 ⟨_, m.rel.2, congrArg (·.rel.1) h ▸ m'.rel.2⟩

variable [DecidableEq V] [∀ n, DecidableEq (L.Relations n)] {x : ∀ i, (C.part i).DRS}
  {s s' : c.DRS}

instance [Fintype ι] : Decidable (C.IsGluing (DRS.presheaf L V) x s) :=
  inferInstanceAs (Decidable (∀ i, s.restrict (C.map i) = x i))

/-- Given as many referents as each arity in the vocabulary, a family glues iff it is
compatible. -/
theorem exists_isGluing_iff_compatible (hc : ∀ r ∈ c.vocab, Nonempty (Fin r.1 ↪ V)) :
    (∃ s, C.IsGluing (DRS.presheaf L V) x s) ↔ Arrows.Compatible (DRS.presheaf L V) C.map x :=
  ⟨fun ⟨_, hs⟩ ↦ hs.compatible, fun hx ↦
    have ⟨t, ht⟩ := DRS.exists_isAmalgamation hx.familyOfElements_compatible hc
    ⟨t, fun i ↦ (ht _ (ofArrows.mk i)).trans (hx.familyOfElements_ofArrows_mk i)⟩⟩

/-- A gluing is unique along a cover jointly surjective on literals. -/
theorem IsGluing.unique (hC : C.presieve ∈ literalPrecoverage L V c)
    (hs : C.IsGluing (DRS.presheaf L V) x s) (hs' : C.IsGluing (DRS.presheaf L V) x s') : s = s' :=
  (DRS.isSeparatedFor_iff.2 hC).ext fun _ _ ⟨i⟩ ↦ (hs i).trans (hs' i).symm

/-- `C.pushforward x` holds the renamings of the local literals, `{±A(fᵢ(x̄)) | ±A(x̄) ∈ sᵢ}`. -/
def pushforward [Fintype ι] (C : Cover c ι) (x : ∀ i, (C.part i).DRS) : Finset (Literal c) :=
  Finset.univ.biUnion fun i ↦ (x i).1.image (Literal.map (C.map i))

@[simp] theorem mem_pushforward [Fintype ι] {l : Literal c} :
    l ∈ C.pushforward x ↔ ∃ i, ∃ m ∈ (x i).1, m.map (C.map i) = l := by
  simp [pushforward]

variable [Fintype ι]

instance : Decidable (C.presieve ∈ literalPrecoverage L V c) :=
  decidable_of_iff _ presieve_mem_literalPrecoverage_iff.symm

theorem IsGluing.pushforward_subset (hs : C.IsGluing (DRS.presheaf L V) x s) :
    C.pushforward x ⊆ s.1 := by
  intro l hl
  obtain ⟨i, m, hm, rfl⟩ := mem_pushforward.1 hl
  rw [← hs i] at hm
  exact DRS.mem_restrict.1 hm

/-- A family glues iff the renamings of its local literals form a gluing, which is then the
least one. -/
theorem exists_isGluing_iff : (∃ s, C.IsGluing (DRS.presheaf L V) x s) ↔
    ∃ h : Literal.Consistent (C.pushforward x), C.IsGluing (DRS.presheaf L V) x ⟨_, h⟩ := by
  refine ⟨fun ⟨s, hs⟩ ↦ ⟨s.2.mono hs.pushforward_subset, fun i ↦ ?_⟩, fun ⟨_, h⟩ ↦ ⟨_, h⟩⟩
  refine Subtype.ext (Finset.ext fun l ↦ ?_)
  simp only [DRS.presheaf_map, Quiver.Hom.unop_op, DRS.mem_restrict]
  refine ⟨fun hl ↦ ?_, fun hl ↦ mem_pushforward.2 ⟨i, l, hl, rfl⟩⟩
  rw [← hs i]
  exact DRS.mem_restrict.2 (hs.pushforward_subset hl)

/-! ### Disjoint vocabularies -/

/-- `C.glue` is the basic DRS of the renamed local literals, consistent when the vocabularies are
pairwise disjoint and the cover maps injective. -/
def glue (C : Cover c ι) (hdisj : Pairwise fun i j ↦ Disjoint (C.part i).vocab (C.part j).vocab)
    (hinj : ∀ i, Function.Injective (C.map i).map) (x : ∀ i, (C.part i).DRS) : c.DRS :=
  ⟨C.pushforward x, fun _ hl hn ↦ by
    obtain ⟨i, m, hm, rfl⟩ := mem_pushforward.1 hl
    obtain ⟨j, m', hm', h⟩ := mem_pushforward.1 hn
    rw [Literal.neg_map] at h
    obtain rfl : i = j := (eq_of_map_eq hdisj h).symm
    exact (x i).2 m hm (Literal.map_injective (hinj i) h ▸ hm')⟩

variable (hdisj : Pairwise fun i j ↦ Disjoint (C.part i).vocab (C.part j).vocab)
  (hinj : ∀ i, Function.Injective (C.map i).map) (x)

theorem isGluing_glue : C.IsGluing (DRS.presheaf L V) x (C.glue hdisj hinj x) := fun i ↦
  Subtype.ext (Finset.ext fun l ↦ by
    simp only [DRS.presheaf_map, Quiver.Hom.unop_op, DRS.mem_restrict, glue, mem_pushforward]
    grind [eq_of_map_eq, Literal.map_injective])

theorem referents_toDRS_glue : (C.glue hdisj hinj x).toDRS.referents =
    Finset.univ.biUnion fun i ↦ ((x i).toDRS.map (C.map i).extend).referents := by
  ext t
  simp only [DRS.referents_toDRS, DRS.referents_map, Finset.mem_biUnion, Finset.mem_univ,
    Finset.mem_image, true_and]
  constructor
  · intro ht
    obtain ⟨i, y, hy⟩ := C.exists_map_eq ⟨t, ht⟩
    exact ⟨i, y, y.2, by rw [Context.Hom.extend_coe, hy]⟩
  · rintro ⟨i, y, hy, rfl⟩
    rw [show (C.map i).extend y = _ from Context.Hom.extend_coe (C.map i) ⟨y, hy⟩]
    exact ((C.map i).map ⟨y, hy⟩).2

/-- The conditions of the glued DRS are those of the renamed local DRSs, as a multiset, so the
gluing is the merge of the local DRSs after unification of referents. -/
theorem coe_conditions_toDRS_glue :
    ((C.glue hdisj hinj x).toDRS.conditions : Multiset (Condition L V)) =
      ∑ i, (((x i).toDRS.map (C.map i).extend).conditions : Multiset (Condition L V)) := by
  have key {Y : Context L V} (s : Finset (Literal Y)) (g : Literal Y → Condition L V) :
      s.val.map g = ∑ l ∈ s, {g l} := by
    rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton (s.val.map g), Multiset.map_map]
    rfl
  simp only [DRS.coe_conditions_toDRS, DRS.conditions_map, ← Multiset.map_coe,
    Multiset.map_map]
  simp only [key]
  rw [show (C.glue hdisj hinj x).1 = C.pushforward x from rfl, pushforward, Finset.sum_biUnion
    fun i _ j _ hij ↦ Finset.disjoint_left.2 fun l hi hj ↦ by
      obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨m', -, h⟩ := Finset.mem_image.1 hj
      exact hij (eq_of_map_eq hdisj h.symm)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_image fun _ _ _ _ h ↦ Literal.map_injective (hinj i) h]
  simp [Literal.toCondition_map]

end Cover

end Context

end DRT
