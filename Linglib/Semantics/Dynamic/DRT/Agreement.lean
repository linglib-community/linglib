module

public import Linglib.Semantics.Dynamic.DRT.Translation
public import Linglib.Semantics.Dynamic.DRT.Embedding

/-!
# Embeddings and assignments

A total assignment `f'` *completes* a partial embedding `f` when it agrees with `f` on the domain
of `f`. On a DRS in which no referent is declared twice along a nesting path, an embedding has a
verifying extension exactly when an assignment completing it has one
(`DRS.mem_dom_eval_assignment_iff_embedding`), so a proper such DRS is true in a model exactly
when some assignment verifies it (`DRS.mem_dom_eval_assignment_iff_isTrue`), which is when its
first-order translation holds (`DRS.isTrue_iff_realize_toFormula`).

On a DRS that declares a referent again the two interpretations differ: the referent keeps its
value in an embedding and takes a new one in an assignment.

## References

* [kamp-reyle-1993]
* [muskens-1996]
-/

@[expose] public section

open FirstOrder FirstOrder.Language
open SetRel

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} [DecidableEq V] {M : Type x} [L.Structure M]

omit [DecidableEq V] [L.Structure M] in
private theorem dom_res {X : Set V} {f' : V → M} : PFun.Dom (PFun.res f' X) = X :=
  PFun.dom_restrict _

omit [DecidableEq V] [L.Structure M] in
private theorem mem_res_of_mem {X : Set V} {f' : V → M} {x : V} (hx : x ∈ X) :
    f' x ∈ PFun.res f' X x :=
  (PFun.mem_res _ _ _ _).2 ⟨hx, rfl⟩

open Classical in
/-- Read a partial embedding totally, defaulting to `f'` off its domain. -/
private noncomputable def toTotal (g : V → Part M) (f' : V → M) : V → M :=
  fun x ↦ (g x).getOrElse (f' x)

open Classical in
omit [DecidableEq V] [L.Structure M] in
private theorem toTotal_mem {g : V → Part M} {f' : V → M} {x : V} (h : (g x).Dom) :
    toTotal g f' x ∈ g x := by
  show (g x).getOrElse (f' x) ∈ g x
  rw [Part.getOrElse_of_dom _ h]
  exact Part.get_mem h

open Classical in
omit [DecidableEq V] [L.Structure M] in
private theorem toTotal_of_not_dom {g : V → Part M} {f' : V → M} {x : V} (h : ¬(g x).Dom) :
    toTotal g f' x = f' x :=
  Part.getOrElse_of_not_dom _ h _

private theorem mem_eval_embedding_res {X U : Finset V} {cs : List (Condition L V)}
    (hXU : Disjoint X U)
    (hIH : ∀ (k : V → Part M) (k' : V → M), PFun.Dom k = ↑(X ∪ U) →
      (∀ x ∈ X ∪ U, k' x ∈ k x) → (k' ∈ Condition.verifiersAll (.assignment M) cs ↔
        k ∈ Condition.verifiersAll (.embedding M) cs))
    {f : V → Part M} {f' g' : V → M}
    (hdom : PFun.Dom f = ↑X) (hff' : ∀ x ∈ X, f' x ∈ f x)
    (hext : ∀ x ∉ U, g' x = f' x) (hv : g' ∈ Condition.verifiersAll (.assignment M) cs) :
    f ~[(DRS.mk U cs).eval (.embedding M)] (PFun.res g' ↑(X ∪ U)) := by
  have hagree : ∀ x ∈ X, g' x = f' x := fun x hx =>
    hext x (Finset.disjoint_left.mp hXU hx)
  refine DRS.mem_eval_embedding_mk.mpr
    ⟨Pi.le_def.mpr fun x a ha => ?_, by rw [dom_res, hdom, Finset.coe_union], ?_⟩
  · have hxX : x ∈ X := by
      have hd : x ∈ PFun.Dom f := Part.dom_iff_mem.2 ⟨a, ha⟩
      rwa [hdom, Finset.mem_coe] at hd
    have hax : a = f' x := Part.mem_unique ha (hff' x hxX)
    rw [hax, ← hagree x hxX]
    exact mem_res_of_mem (by simp [hxX])
  · exact (hIH _ g' dom_res fun x hx => mem_res_of_mem (by simpa using hx)).mp hv

private theorem mem_eval_assignment_toTotal {X U : Finset V} {cs : List (Condition L V)}
    (hIH : ∀ (k : V → Part M) (k' : V → M), PFun.Dom k = ↑(X ∪ U) →
      (∀ x ∈ X ∪ U, k' x ∈ k x) → (k' ∈ Condition.verifiersAll (.assignment M) cs ↔
        k ∈ Condition.verifiersAll (.embedding M) cs))
    {f g : V → Part M} {f' : V → M}
    (hdom : PFun.Dom f = ↑X) (hff' : ∀ x ∈ X, f' x ∈ f x)
    (hv : f ~[(DRS.mk U cs).eval (.embedding M)] g) :
    f' ~[(DRS.mk U cs).eval (.assignment M)] (toTotal g f') := by
  obtain ⟨hle, hdomg, hh⟩ := DRS.mem_eval_embedding_mk.mp hv
  have hval : ∀ x ∈ X ∪ U, toTotal g f' x ∈ g x := by
    intro x hx
    refine toTotal_mem ?_
    show x ∈ PFun.Dom g
    rw [hdomg, hdom, ← Finset.coe_union]
    exact Finset.mem_coe.mpr hx
  refine DRS.mem_eval_assignment.mpr ⟨fun x hxU => ?_,
    (hIH g _ (by rw [hdomg, hdom, Finset.coe_union]) hval).mpr hh⟩
  by_cases hxg : (g x).Dom
  · have hxX : x ∈ X := by
      have hmem : x ∈ PFun.Dom g := hxg
      rw [hdomg, hdom] at hmem
      rcases hmem with h | h
      · rwa [Finset.mem_coe] at h
      · exact absurd (Finset.mem_coe.mp h) hxU
    have hfg : f x = g x := PFun.le_iff_eqOn_dom.mp hle
      (show x ∈ PFun.Dom f by rw [hdom]; exact Finset.mem_coe.mpr hxX)
    exact Part.mem_unique (toTotal_mem hxg) (hfg ▸ hff' x hxX)
  · exact toTotal_of_not_dom hxg

private theorem mem_dom_eval_iff_of {X U : Finset V} {cs : List (Condition L V)}
    (hXU : Disjoint X U)
    (hIH : ∀ (k : V → Part M) (k' : V → M), PFun.Dom k = ↑(X ∪ U) →
      (∀ x ∈ X ∪ U, k' x ∈ k x) → (k' ∈ Condition.verifiersAll (.assignment M) cs ↔
        k ∈ Condition.verifiersAll (.embedding M) cs))
    {f : V → Part M} {f' : V → M}
    (hdom : PFun.Dom f = ↑X) (hff' : ∀ x ∈ X, f' x ∈ f x) :
    f' ∈ ((DRS.mk U cs).eval (.assignment M)).dom ↔
      f ∈ ((DRS.mk U cs).eval (.embedding M)).dom := by
  constructor
  · rintro ⟨g', hg'⟩
    obtain ⟨hext, hv⟩ := DRS.mem_eval_assignment.mp hg'
    exact ⟨_, mem_eval_embedding_res hXU hIH hdom hff' hext hv⟩
  · rintro ⟨g, hg⟩
    exact ⟨_, mem_eval_assignment_toTotal hIH hdom hff' hg⟩

mutual
/-- On a condition that declares no referent twice, an embedding verifies it exactly when an
assignment completing the embedding does. -/
theorem Condition.mem_verifiers_assignment_iff_embedding {X : Finset V} (c : Condition L V)
    (hrf : Condition.ReuseFreeAt X c) (hfv : c.freeVarFinset ⊆ X)
    {f : V → Part M} {f' : V → M}
    (hdom : PFun.Dom f = ↑X) (hff' : ∀ x ∈ X, f' x ∈ f x) :
    f' ⊨[.assignment M] c ↔ f ⊨[.embedding M] c := by
  match c with
  | .atom a =>
    simp only [Condition.mem_verifiers_assignment_atom, Condition.mem_verifiers_embedding_atom,
      Atom.Realize]
    have hval : ∀ i, f' (a.args i) ∈ f (a.args i) := fun i =>
      hff' _ (hfv (by simp [Condition.freeVarFinset_atom]))
    constructor
    · exact fun h => ⟨f' ∘ a.args, hval, h⟩
    · rintro ⟨v, hv, hrel⟩
      have : f' ∘ a.args = v := funext fun i => Part.mem_unique (hval i) (hv i)
      rwa [this]
  | .eq u v =>
    simp only [Condition.mem_verifiers_assignment_eq, Condition.mem_verifiers_embedding_eq]
    have hu : f' u ∈ f u := hff' u (hfv (by simp))
    have hv : f' v ∈ f v := hff' v (hfv (by simp))
    constructor
    · exact fun h => ⟨f' u, hu, by rw [h]; exact hv⟩
    · rintro ⟨m, hum, hvm⟩
      rw [Part.mem_unique hu hum, Part.mem_unique hv hvm]
  | .neg K =>
    obtain ⟨U, cs⟩ := K
    rw [Condition.reuseFreeAt_neg, DRS.reuseFreeAt_mk] at hrf
    rw [Condition.freeVarFinset_neg] at hfv
    have hfvc := DRS.freeVarFinset_subset_iff.mp hfv
    rw [Condition.verifiers_neg, Condition.verifiers_neg, Set.mem_compl_iff, Set.mem_compl_iff]
    exact not_congr (mem_dom_eval_iff_of hrf.1 (fun k k' hk hkk' =>
      Condition.mem_verifiersAll_assignment_iff_embedding cs hrf.2 hfvc hk hkk') hdom hff')
  | .imp a c =>
    obtain ⟨Ua, csa⟩ := a
    obtain ⟨Uc, csc⟩ := c
    rw [Condition.reuseFreeAt_imp, DRS.reuseFreeAt_mk, DRS.reuseFreeAt_mk] at hrf
    obtain ⟨⟨hXUa, hrfa⟩, hXUc, hrfc⟩ := hrf
    rw [Condition.freeVarFinset_imp, Finset.union_subset_iff] at hfv
    obtain ⟨hfva, hfvc'⟩ := hfv
    have hfvca : Condition.freeVarFinsetL csa ⊆ X ∪ Ua := DRS.freeVarFinset_subset_iff.mp hfva
    have hfvcc : Condition.freeVarFinsetL csc ⊆ (X ∪ Ua) ∪ Uc := by
      intro x hx
      by_cases hxUc : x ∈ Uc
      · exact Finset.mem_union_right _ hxUc
      · by_cases hxUa : x ∈ Ua
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hxUa)
        · refine Finset.mem_union_left _ (Finset.mem_union_left _ (hfvc' ?_))
          rw [DRS.freeVarFinset_mk, Finset.mem_sdiff, Finset.mem_sdiff]
          exact ⟨⟨hx, hxUc⟩, hxUa⟩
    have hIHa : ∀ (k : V → Part M) (k' : V → M), PFun.Dom k = ↑(X ∪ Ua) →
        (∀ x ∈ X ∪ Ua, k' x ∈ k x) → (k' ∈ Condition.verifiersAll (.assignment M) csa ↔
          k ∈ Condition.verifiersAll (.embedding M) csa) :=
      fun k k' hk hkk' =>
        Condition.mem_verifiersAll_assignment_iff_embedding csa hrfa hfvca hk hkk'
    have hIHc : ∀ (k : V → Part M) (k' : V → M), PFun.Dom k = ↑((X ∪ Ua) ∪ Uc) →
        (∀ x ∈ (X ∪ Ua) ∪ Uc, k' x ∈ k x) → (k' ∈ Condition.verifiersAll (.assignment M) csc ↔
          k ∈ Condition.verifiersAll (.embedding M) csc) :=
      fun k k' hk hkk' =>
        Condition.mem_verifiersAll_assignment_iff_embedding csc hrfc hfvcc hk hkk'
    simp only [Condition.mem_verifiers_imp]
    constructor
    · intro hL g₁ hg₁
      have hg₁' := mem_eval_assignment_toTotal hIHa hdom hff' hg₁
      obtain ⟨hle₁, hdom₁, hh₁⟩ := DRS.mem_eval_embedding_mk.mp hg₁
      have hdom₁' : PFun.Dom g₁ = ↑(X ∪ Ua) := by rw [hdom₁, hdom, Finset.coe_union]
      have hff₁ : ∀ x ∈ X ∪ Ua, toTotal g₁ f' x ∈ g₁ x := fun x hx =>
        toTotal_mem (show x ∈ PFun.Dom g₁ by rw [hdom₁']; exact Finset.mem_coe.mpr hx)
      exact (mem_dom_eval_iff_of hXUc hIHc hdom₁' hff₁).mp (hL _ hg₁')
    · intro hR g₁' hg₁'
      obtain ⟨hext₁, hv₁⟩ := DRS.mem_eval_assignment.mp hg₁'
      have hg₁ := mem_eval_embedding_res hXUa hIHa hdom hff' hext₁ hv₁
      have hff₁ : ∀ x ∈ X ∪ Ua, g₁' x ∈ PFun.res g₁' ↑(X ∪ Ua) x := fun x hx =>
        mem_res_of_mem (Finset.mem_coe.mpr hx)
      exact (mem_dom_eval_iff_of hXUc hIHc dom_res hff₁).mpr (hR _ hg₁)
  | .dis l r =>
    obtain ⟨Ul, csl⟩ := l
    obtain ⟨Ur, csr⟩ := r
    rw [Condition.reuseFreeAt_dis, DRS.reuseFreeAt_mk, DRS.reuseFreeAt_mk] at hrf
    obtain ⟨⟨hXUl, hrfl⟩, hXUr, hrfr⟩ := hrf
    rw [Condition.freeVarFinset_dis, Finset.union_subset_iff] at hfv
    have hfvcl := DRS.freeVarFinset_subset_iff.mp hfv.1
    have hfvcr := DRS.freeVarFinset_subset_iff.mp hfv.2
    rw [Condition.verifiers_dis, Condition.verifiers_dis]
    exact or_congr
      (mem_dom_eval_iff_of hXUl (fun k k' hk hkk' =>
        Condition.mem_verifiersAll_assignment_iff_embedding csl hrfl hfvcl hk hkk') hdom hff')
      (mem_dom_eval_iff_of hXUr (fun k k' hk hkk' =>
        Condition.mem_verifiersAll_assignment_iff_embedding csr hrfr hfvcr hk hkk') hdom hff')
theorem Condition.mem_verifiersAll_assignment_iff_embedding {X : Finset V}
    (cs : List (Condition L V))
    (hrf : Condition.ReuseFreeAllAt X cs) (hfv : Condition.freeVarFinsetL cs ⊆ X)
    {f : V → Part M} {f' : V → M}
    (hdom : PFun.Dom f = ↑X) (hff' : ∀ x ∈ X, f' x ∈ f x) :
    f' ∈ Condition.verifiersAll (.assignment M) cs ↔
      f ∈ Condition.verifiersAll (.embedding M) cs := by
  match cs with
  | [] => simp
  | c :: cs =>
    rw [Condition.reuseFreeAllAt_cons] at hrf
    rw [Condition.freeVarFinsetL_cons, Finset.union_subset_iff] at hfv
    rw [Condition.mem_verifiersAll_cons, Condition.mem_verifiersAll_cons]
    exact and_congr
      (Condition.mem_verifiers_assignment_iff_embedding c hrf.1 hfv.1 hdom hff')
      (Condition.mem_verifiersAll_assignment_iff_embedding cs hrf.2 hfv.2 hdom hff')
end

/-- On a DRS that declares no referent twice, an embedding has a verifying extension exactly
when an assignment completing it does. -/
theorem DRS.mem_dom_eval_assignment_iff_embedding {X : Finset V} {K : DRS L V}
    (hrf : K.ReuseFreeAt X) (hfv : K.freeVarFinset ⊆ X)
    {f : V → Part M} {f' : V → M}
    (hdom : PFun.Dom f = ↑X) (hff' : ∀ x ∈ X, f' x ∈ f x) :
    f' ∈ (K.eval (.assignment M)).dom ↔ f ∈ (K.eval (.embedding M)).dom := by
  obtain ⟨U, cs⟩ := K
  rw [DRS.reuseFreeAt_mk] at hrf
  have hfvc := DRS.freeVarFinset_subset_iff.mp hfv
  exact mem_dom_eval_iff_of hrf.1 (fun k k' hk hkk' =>
    Condition.mem_verifiersAll_assignment_iff_embedding cs hrf.2 hfvc hk hkk') hdom hff'

/-- A proper DRS that declares no referent twice is true exactly when an assignment has an
extension verifying it. -/
theorem DRS.mem_dom_eval_assignment_iff_isTrue {K : DRS L V} (hrf : K.ReuseFreeAt ∅)
    (hK : K.IsProper) (f' : V → M) : f' ∈ (K.eval (.assignment M)).dom ↔ K.IsTrue M :=
  DRS.mem_dom_eval_assignment_iff_embedding hrf (hK ▸ Finset.Subset.refl _) (f := ⊥)
    (by simp) fun x hx => absurd hx (Finset.notMem_empty x)

/-- The truth of a proper DRS that declares no referent twice is the truth of its first-order
translation (§1.5). -/
theorem DRS.isTrue_iff_realize_toFormula {K : DRS L V} (hrf : K.ReuseFreeAt ∅)
    (hK : K.IsProper) (f' : V → M) : K.IsTrue M ↔ K.toFormula.Realize f' :=
  (DRS.mem_dom_eval_assignment_iff_isTrue hrf hK f').symm.trans
    (DRS.realize_toFormula K f').symm

end DRT
