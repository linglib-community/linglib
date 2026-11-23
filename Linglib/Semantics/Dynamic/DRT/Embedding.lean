module

public import Linglib.Core.Data.Part
public import Linglib.Semantics.Dynamic.DRT.Semantics
public import Mathlib.Data.Finset.Piecewise

/-!
# Verifying embeddings

An *embedding* is a partial function from discourse referents to the individuals of a model `M`.
An embedding `g` extends `f` on a universe `U` when `f ⊆ g` and `Dom g = Dom f ∪ U`, and an
embedding verifies an atomic condition when its referents are valued and the values satisfy it in
`M`. This is the interpretation `Interpretation.embedding M`.

A DRS `K` is *true* in `M` when some embedding with domain the universe of `K` verifies `K`
(`DRS.isTrue_iff`). Whether an embedding has a verifying extension depends only on its values at
the referents occurring in the DRS (`DRS.mem_dom_eval_embedding_congr`), and the merge `K ⊕ K'`
denotes the composite of `K` and `K'` when the universe of `K'` contains no referent that the
conditions of `K` use outside the universe of `K` (`DRS.eval_embedding_merge`).

## Implementation notes

A referent that a sub-DRS declares again is already valued, so declaring it again has no
effect, and whether it is valued matters to verification. Coincidence is therefore stated over
the occurring referents `DRS.varFinset`, not the free ones.

## References

* [kamp-reyle-1993]
* [kamp-vangenabith-reyle-2011]
-/

@[expose] public section

open FirstOrder FirstOrder.Language
open DynamicSemantics (Update)
open SetRel

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} [DecidableEq V] (M : Type x) [L.Structure M]

/-- The interpretation of DRSs in the partial embeddings into a model: `f[U]g` when `f ⊆ g` and
`Dom g = Dom f ∪ U`, and an atom is verified when its referents are valued and their values
satisfy it. -/
def Interpretation.embedding : Interpretation L V (V → Part M) where
  extend U := {(f, g) | (f ≤ g) ∧ PFun.Dom g = PFun.Dom f ∪ ↑U}
  atom a := {g | ∃ v : Fin a.arity → M, (∀ i, v i ∈ g (a.args i)) ∧ Structure.RelMap a.rel v}
  eq x y := {g | ∃ m : M, m ∈ g x ∧ m ∈ g y}
  extend_empty := by
    ext ⟨f, g⟩
    constructor
    · rintro ⟨hle, hdom⟩
      rw [Finset.coe_empty, Set.union_empty] at hdom
      exact PFun.eq_of_le_of_dom_subset hle hdom.subset
    · rintro rfl
      exact ⟨le_rfl, by rw [Finset.coe_empty, Set.union_empty]⟩
  extend_union U U' := by
    classical
    ext ⟨f, g⟩
    constructor
    · rintro ⟨hle, hdom⟩
      have hdom' : PFun.Dom g = PFun.Dom f ∪ ↑U ∪ ↑U' := by
        rw [hdom, Finset.coe_union, Set.union_assoc]
      have hdomh : PFun.Dom ((PFun.Dom f ∪ ↑U).piecewise g ⊥) = PFun.Dom f ∪ ↑U := by
        ext x
        show (((PFun.Dom f ∪ ↑U).piecewise g ⊥ : V → Part M) x).Dom ↔ _
        by_cases hx : x ∈ PFun.Dom f ∪ ↑U
        · rw [Set.piecewise_eq_of_mem _ _ _ hx]
          exact iff_of_true (show x ∈ PFun.Dom g by rw [hdom']; exact Or.inl hx) hx
        · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
          exact iff_of_false Part.not_none_dom hx
      refine ⟨(PFun.Dom f ∪ ↑U).piecewise g ⊥, ⟨fun x ↦ ?_, hdomh⟩, fun x ↦ ?_, ?_⟩
      · by_cases hx : x ∈ PFun.Dom f ∪ ↑U
        · rw [Set.piecewise_eq_of_mem _ _ _ hx]
          exact hle x
        · rw [Set.piecewise_eq_of_notMem _ _ _ hx,
            Part.eq_bot_iff_not_dom.2 fun hfx ↦ hx (Or.inl hfx)]
          exact le_rfl
      · by_cases hx : x ∈ PFun.Dom f ∪ ↑U
        · rw [Set.piecewise_eq_of_mem _ _ _ hx]
        · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
          exact bot_le
      · rw [hdomh, hdom']
    · rintro ⟨h, ⟨hle₁, hdom₁⟩, hle₂, hdom₂⟩
      exact ⟨hle₁.trans hle₂, by rw [hdom₂, hdom₁, Finset.coe_union, Set.union_assoc]⟩

/-- A DRS is *true* in `M` when some embedding verifies it from the empty embedding
(Def. 1.4.5). -/
def DRS.IsTrue (K : DRS L V) (M : Type x) [L.Structure M] : Prop :=
  ∃ g : V → Part M, ⊥ ~[K.eval (.embedding M)] g

variable {M} {K : DRS L V} {f g : V → Part M}

theorem Interpretation.mem_extend_embedding {U : Finset V} :
    f ~[(Interpretation.embedding (L := L) M).extend U] g ↔
      f ≤ g ∧ PFun.Dom g = PFun.Dom f ∪ ↑U := Iff.rfl

@[simp] theorem Condition.mem_verifiers_embedding_atom (a : L.Atom V) :
    g ⊨[.embedding M] Condition.atom a ↔
      ∃ v : Fin a.arity → M, (∀ i, v i ∈ g (a.args i)) ∧ Structure.RelMap a.rel v := by
  rw [Condition.verifiers_atom]
  rfl

@[simp] theorem Condition.mem_verifiers_embedding_eq (x y : V) :
    g ⊨[.embedding M] (Condition.eq x y : Condition L V) ↔ ∃ m : M, m ∈ g x ∧ m ∈ g y := by
  rw [Condition.verifiers_eq]
  rfl

theorem DRS.mem_eval_embedding_mk {U : Finset V} {cs : List (Condition L V)} :
    f ~[(DRS.mk U cs).eval (.embedding M)] g ↔
      f ≤ g ∧ PFun.Dom g = PFun.Dom f ∪ ↑U ∧ g ∈ Condition.verifiersAll (.embedding M) cs := by
  rw [DRS.eval_mk, Update.mem_comp_test]
  exact and_assoc

/-- `⟨f, g⟩` verifies `K`: `g` extends `f` on the universe of `K` and verifies `K`
(Kamp, van Genabith and Reyle, Def. 19(i)). -/
theorem DRS.mem_eval_embedding :
    f ~[K.eval (.embedding M)] g ↔
      f ≤ g ∧ PFun.Dom g = PFun.Dom f ∪ ↑K.referents ∧ g ⊨[.embedding M] K := by
  cases K
  exact DRS.mem_eval_embedding_mk

/-- A DRS is true in `M` when an embedding of its universe verifies it. -/
theorem DRS.isTrue_iff :
    K.IsTrue M ↔ ∃ g : V → Part M, PFun.Dom g = ↑K.referents ∧ g ⊨[.embedding M] K := by
  refine exists_congr fun g ↦ DRS.mem_eval_embedding.trans ?_
  rw [PFun.dom_bot, Set.empty_union]
  exact and_iff_right bot_le

/-- Extending an embedding on a referent is a covering step of the extension order when the
referent is not valued, and changes nothing when it is. -/
theorem Interpretation.mem_extend_embedding_singleton (u : V) :
    f ~[(Interpretation.embedding (L := L) M).extend {u}] g ↔
      (¬(f u).Dom ∧ f ⋖ g ∧ (g u).Dom) ∨ ((f u).Dom ∧ g = f) := by
  rw [Interpretation.mem_extend_embedding, Finset.coe_singleton]
  constructor
  · rintro ⟨hle, hdom⟩
    by_cases hu : (f u).Dom
    · refine .inr ⟨hu, (PFun.eq_of_le_of_dom_subset hle ?_).symm⟩
      rw [hdom]
      exact Set.union_subset subset_rfl (Set.singleton_subset_iff.2 hu)
    · have hgu : (g u).Dom := by
        have hmem : u ∈ PFun.Dom g := by
          rw [hdom]
          exact Set.mem_union_right _ rfl
        exact hmem
      refine .inl ⟨hu, Pi.covBy_iff.2 ⟨u, Part.covBy_iff.2 ⟨hu, hgu⟩, fun y hy => ?_⟩, hgu⟩
      by_cases hyf : (f y).Dom
      · exact PFun.le_iff_eqOn_dom.mp hle hyf
      · have hgy : ¬(g y).Dom := fun hgy => by
          have hmem : y ∈ PFun.Dom g := hgy
          rw [hdom] at hmem
          rcases hmem with h | h
          · exact hyf h
          · exact hy h
        rw [Part.eq_bot_iff_not_dom.2 hyf, Part.eq_bot_iff_not_dom.2 hgy]
  · rintro (⟨hu, hcov, hgu⟩ | ⟨hu, rfl⟩)
    · obtain ⟨x, hx, hagree⟩ := Pi.covBy_iff.1 hcov
      obtain ⟨hfx, hgx⟩ := Part.covBy_iff.1 hx
      have hxu : x = u := by
        by_contra hxu
        exact hu (by rw [hagree u fun h => hxu h.symm]; exact hgu)
      subst hxu
      refine ⟨hcov.le, Set.ext fun y => ?_⟩
      rw [Set.mem_union, Set.mem_singleton_iff]
      by_cases hyx : y = x
      · subst hyx
        exact iff_of_true hgx (.inr rfl)
      · show (g y).Dom ↔ (f y).Dom ∨ y = x
        rw [← hagree y hyx]
        exact ⟨Or.inl, fun h => h.resolve_right hyx⟩
    · exact ⟨le_rfl, by
        rw [Set.union_eq_left.mpr (Set.singleton_subset_iff.2 (show u ∈ PFun.Dom g from hu))]⟩

/-! ### Coincidence -/

private theorem DRS.mem_eval_embedding_piecewise {U : Finset V} {cs : List (Condition L V)}
    (hIH : ∀ {k k' : V → Part M}, Set.EqOn k k' ↑(Condition.varFinsetL cs) →
      (k ∈ Condition.verifiersAll (.embedding M) cs ↔
        k' ∈ Condition.verifiersAll (.embedding M) cs))
    {f f' g' : V → Part M}
    (h : Set.EqOn f f' ↑(DRS.varFinset (.mk U cs : DRS L V)))
    (hv : f' ~[(DRS.mk U cs).eval (.embedding M)] g') :
    f ~[(DRS.mk U cs).eval (.embedding M)] (U.piecewise g' f) ∧
      ∀ ⦃x⦄, f x = f' x → U.piecewise g' f x = g' x := by
  obtain ⟨hle, hdom, hh⟩ := DRS.mem_eval_embedding_mk.mp hv
  have hag : ∀ ⦃x⦄, f x = f' x → U.piecewise g' f x = g' x := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Finset.piecewise_eq_of_mem _ _ _ hxU
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hxU, hx]
      by_cases hxd : (f' x).Dom
      · exact PFun.le_iff_eqOn_dom.mp hle hxd
      · have hgb : ¬(g' x).Dom := fun hgx => by
          have hmem : x ∈ PFun.Dom g' := hgx
          rw [hdom] at hmem
          rcases hmem with hmem | hmem
          · exact hxd hmem
          · exact hxU (Finset.mem_coe.mp hmem)
        rw [Part.eq_bot_iff_not_dom.2 hxd, Part.eq_bot_iff_not_dom.2 hgb]
  refine ⟨DRS.mem_eval_embedding_mk.mpr ⟨Pi.le_def.mpr fun x => ?_, Set.ext fun x => ?_, ?_⟩, hag⟩
  · by_cases hxU : x ∈ U
    · rw [Finset.piecewise_eq_of_mem _ _ _ hxU]
      calc f x = f' x := h (by simp [hxU])
        _ ≤ g' x := hle x
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hxU]
  · show (U.piecewise g' f x).Dom ↔ x ∈ PFun.Dom f ∪ ↑U
    by_cases hxU : x ∈ U
    · have hgx : (g' x).Dom := by
        have hmem : x ∈ PFun.Dom g' := by
          rw [hdom]
          exact Set.mem_union_right _ (Finset.mem_coe.mpr hxU)
        exact hmem
      rw [Finset.piecewise_eq_of_mem _ _ _ hxU]
      exact iff_of_true hgx (Set.mem_union_right _ (Finset.mem_coe.mpr hxU))
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hxU]
      constructor
      · exact fun hfx => Set.mem_union_left _ hfx
      · intro hx
        rcases hx with hx | hx
        · exact hx
        · exact absurd (Finset.mem_coe.mp hx) hxU
  · refine (hIH fun x hx => ?_).mpr hh
    exact hag (h (by simp only [DRS.varFinset_mk, Finset.coe_union, Set.mem_union]; exact .inr hx))

mutual
/-- Whether an embedding has an extension verifying a DRS depends only on its values at the
referents occurring in the DRS. -/
theorem DRS.mem_dom_eval_embedding_congr (K : DRS L V) {f f' : V → Part M}
    (h : Set.EqOn f f' ↑K.varFinset) :
    f ∈ (K.eval (.embedding M)).dom ↔ f' ∈ (K.eval (.embedding M)).dom := by
  match K with
  | .mk U cs =>
    have hIH : ∀ {k k' : V → Part M}, Set.EqOn k k' ↑(Condition.varFinsetL cs) →
        (k ∈ Condition.verifiersAll (.embedding M) cs ↔
          k' ∈ Condition.verifiersAll (.embedding M) cs) :=
      fun hkk' => Condition.mem_verifiersAll_embedding_congr cs hkk'
    exact ⟨fun ⟨g, hg⟩ => ⟨_, (DRS.mem_eval_embedding_piecewise hIH h.symm hg).1⟩,
      fun ⟨g, hg⟩ => ⟨_, (DRS.mem_eval_embedding_piecewise hIH h hg).1⟩⟩
/-- Whether an embedding verifies a condition depends only on its values at the referents
occurring in the condition. -/
theorem Condition.mem_verifiers_embedding_congr (c : Condition L V) {g g' : V → Part M}
    (h : Set.EqOn g g' ↑c.varFinset) : g ⊨[.embedding M] c ↔ g' ⊨[.embedding M] c := by
  match c with
  | .atom a =>
    simp only [Condition.mem_verifiers_embedding_atom]
    refine exists_congr fun v => and_congr_left fun _ => forall_congr' fun i => ?_
    rw [h (by simp only [Condition.varFinset_atom, Finset.coe_image, Finset.coe_univ,
      Set.image_univ]; exact Set.mem_range_self i)]
  | .eq u v =>
    simp only [Condition.mem_verifiers_embedding_eq]
    rw [h (by simp), h (by simp)]
  | .neg K =>
    rw [Condition.varFinset_neg] at h
    rw [Condition.verifiers_neg, Set.mem_compl_iff, Set.mem_compl_iff]
    exact not_congr (DRS.mem_dom_eval_embedding_congr K h)
  | .imp a c =>
    obtain ⟨Ua, csa⟩ := a
    rw [Condition.varFinset_imp] at h
    have ha := h.mono (Finset.coe_subset.mpr Finset.subset_union_left)
    have hc := h.mono (Finset.coe_subset.mpr Finset.subset_union_right)
    have hIHa : ∀ {k k' : V → Part M}, Set.EqOn k k' ↑(Condition.varFinsetL csa) →
        (k ∈ Condition.verifiersAll (.embedding M) csa ↔
          k' ∈ Condition.verifiersAll (.embedding M) csa) :=
      fun hkk' => Condition.mem_verifiersAll_embedding_congr csa hkk'
    simp only [Condition.mem_verifiers_imp]
    constructor
    · intro hL g₁' hg₁'
      obtain ⟨hver, hag⟩ := DRS.mem_eval_embedding_piecewise hIHa ha hg₁'
      obtain ⟨g₂, hg₂⟩ := hL _ hver
      exact (DRS.mem_dom_eval_embedding_congr c fun x hx => hag (hc hx)).mp ⟨g₂, hg₂⟩
    · intro hR g₁ hg₁
      obtain ⟨hver, hag⟩ := DRS.mem_eval_embedding_piecewise hIHa ha.symm hg₁
      obtain ⟨g₂, hg₂⟩ := hR _ hver
      exact (DRS.mem_dom_eval_embedding_congr c fun x hx => hag (hc hx).symm).mp ⟨g₂, hg₂⟩
  | .dis l r =>
    rw [Condition.varFinset_dis] at h
    rw [Condition.verifiers_dis]
    exact or_congr
      (DRS.mem_dom_eval_embedding_congr l
        (h.mono (Finset.coe_subset.mpr Finset.subset_union_left)))
      (DRS.mem_dom_eval_embedding_congr r
        (h.mono (Finset.coe_subset.mpr Finset.subset_union_right)))
theorem Condition.mem_verifiersAll_embedding_congr (cs : List (Condition L V))
    {g g' : V → Part M} (h : Set.EqOn g g' ↑(Condition.varFinsetL cs)) :
    g ∈ Condition.verifiersAll (.embedding M) cs ↔
      g' ∈ Condition.verifiersAll (.embedding M) cs := by
  match cs with
  | [] => simp
  | c :: cs =>
    rw [Condition.varFinsetL_cons, Finset.coe_union] at h
    rw [Condition.mem_verifiersAll_cons, Condition.mem_verifiersAll_cons]
    exact and_congr (Condition.mem_verifiers_embedding_congr c (h.mono Set.subset_union_left))
      (Condition.mem_verifiersAll_embedding_congr cs (h.mono Set.subset_union_right))
end

/-- An embedding that values no referent occurring in a DRS has a verifying extension exactly
when the DRS is true. -/
theorem DRS.mem_dom_eval_embedding_iff_isTrue {f : V → Part M}
    (hf : ∀ x ∈ K.varFinset, f x = ⊥) : f ∈ (K.eval (.embedding M)).dom ↔ K.IsTrue M :=
  DRS.mem_dom_eval_embedding_congr K fun x hx => hf x (Finset.mem_coe.mp hx)

/-! ### The Merging Lemma -/

/-- The Merging Lemma: a merge denotes the composite of its parts when the universe of `K₂`
contains no referent that the conditions of `K₁` use outside the universe of `K₁`. -/
theorem DRS.eval_embedding_merge (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions \ K₁.referents)) :
    (K₁.merge K₂).eval (.embedding M) = K₁.eval (.embedding M) ○ K₂.eval (.embedding M) := by
  refine DRS.eval_merge K₁ K₂ fun s t hs hst ↦
    Condition.mem_verifiersAll_embedding_congr _ fun x hx ↦ ?_
  obtain ⟨r, -, hdom₁⟩ := hs
  obtain ⟨hle, hdom₂⟩ := hst
  by_cases hxs : (s x).Dom
  · exact PFun.le_iff_eqOn_dom.mp hle hxs
  · have hxt : ¬(t x).Dom := fun hxt ↦ by
      have hmem : x ∈ PFun.Dom t := hxt
      rw [hdom₂] at hmem
      rcases hmem with hmem | hmem
      · exact hxs hmem
      · refine Finset.disjoint_left.mp hfresh (Finset.mem_coe.mp hmem)
          (Finset.mem_sdiff.mpr ⟨Finset.mem_coe.mp hx, fun hU₁ ↦ hxs ?_⟩)
        show x ∈ PFun.Dom s
        rw [hdom₁]
        exact Or.inr (Finset.mem_coe.mpr hU₁)
    rw [Part.eq_bot_iff_not_dom.2 hxs, Part.eq_bot_iff_not_dom.2 hxt]

end DRT
