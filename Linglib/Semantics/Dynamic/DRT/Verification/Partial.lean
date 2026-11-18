module

public import Linglib.Core.Data.Part
public import Linglib.Semantics.Dynamic.DRT.Verification.Total
public import Mathlib.Data.Finset.Piecewise

/-!
# Verification by partial embeddings

This file defines verification in Kamp and Reyle's form. A pair of partial embeddings — families
`V → Part M` — verifies a DRS when the output extends the input by exactly the universe of the
DRS and verifies its conditions, an atomic condition requiring its referents to be valued. A DRS
is true in a model when an embedding of its universe verifies it from the empty input. On DRSs
that declare no referent twice this [agrees with verification by total
assignments](##DRT.DRS.exists_extends_verifiesTotal_iff_exists_verifies).

## Main definitions

* `DRT.DRS.Verifies`, `DRT.Condition.Holds`: verification of DRSs and conditions.
* `DRT.DRS.IsTrue`: truth in a model.

## Main statements

* `DRT.DRS.verifies_merge`: a merge is verified by sequencing, when the second universe captures
  no referent the first DRS's conditions use outside its own.
* `DRT.DRS.exists_verifies_iff_isTrue`: an input valuing no occurring referent verifies a DRS
  exactly when the DRS is true.

## Implementation notes

* On a DRS that re-declares a referent the two semantics diverge:
  `[ | [x | man x] ⇒ [x | mortal x]]` says that every man is mortal under `Verifies`, where the
  re-declaration is inert, and that there is a mortal if there is a man under `VerifiesTotal`
  (`Studies/Muskens1996.lean`).
* `Verifies` reads an input at its occurring referents, not only the free ones: whether a
  re-declared referent is already valued matters. Congruence is therefore stated over
  `varFinset`; under `VerifiesTotal` the free referents suffice.

## References

* [kamp-reyle-1993]
* [kamp-vangenabith-reyle-2011]
* [muskens-1996]
-/

@[expose] public section

open FirstOrder FirstOrder.Language

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M]

/-! ### Verification by partial embeddings -/

mutual
/-- `DRS.Verifies K f g` says the pair of partial embeddings `⟨f, g⟩` *verifies* `K`: the output
`g` extends the input `f` by exactly the universe and verifies the conditions (Kamp, van Genabith
and Reyle, Def. 19(i)). This packages how Def. 1.4.4(ii)(f) enters a sub-DRS; Def. 1.4.4(i), that
`f` verifies `K`, is unary, and is `Condition.HoldsAll K.conditions f` here. -/
def DRS.Verifies : DRS L V → (V → Part M) → (V → Part M) → Prop
  | .mk U cs, f, g => f ≤ g ∧ PFun.Dom g = PFun.Dom f ∪ ↑U ∧ Condition.HoldsAll cs g
/-- `Condition.Holds c g` says the partial embedding `g` verifies the DRS-condition `c`
(Def. 1.4.4(ii)); an atomic condition requires its referents to be valued, and a sub-DRS is
entered by extension. -/
def Condition.Holds : Condition L V → (V → Part M) → Prop
  | .atom a, g => ∃ v : Fin a.arity → M, (∀ i, v i ∈ g (a.args i)) ∧ Structure.RelMap a.rel v
  | .eq u v, g => ∃ m : M, m ∈ g u ∧ m ∈ g v
  | .neg K, g => ¬ ∃ g', DRS.Verifies K g g'
  | .imp a c, g => ∀ g', DRS.Verifies a g g' → ∃ g'', DRS.Verifies c g' g''
  | .dis l r, g => (∃ g', DRS.Verifies l g g') ∨ ∃ g', DRS.Verifies r g g'
/-- `Condition.HoldsAll cs g` says `g` verifies every condition of `cs`. -/
def Condition.HoldsAll : List (Condition L V) → (V → Part M) → Prop
  | [], _ => True
  | c :: cs, g => Condition.Holds c g ∧ Condition.HoldsAll cs g
end

theorem DRS.verifies_iff {K : DRS L V} {f g : V → Part M} :
    K.Verifies f g ↔
      f ≤ g ∧ PFun.Dom g = PFun.Dom f ∪ ↑K.referents ∧ Condition.HoldsAll K.conditions g := by
  obtain ⟨U, cs⟩ := K
  exact Iff.rfl

/-- A DRS is *true* in `M` when an embedding of its universe verifies it from the empty input
(Def. 1.4.5). -/
def DRS.IsTrue (K : DRS L V) (M : Type x) [L.Structure M] : Prop :=
  ∃ g : V → Part M, K.Verifies ⊥ g

variable {f g : V → Part M}

@[simp] theorem DRS.verifies_mk (U : Finset V) (cs : List (Condition L V)) :
    DRS.Verifies (.mk U cs) f g ↔
      f ≤ g ∧ PFun.Dom g = PFun.Dom f ∪ ↑U ∧ Condition.HoldsAll cs g := Iff.rfl

@[simp] theorem Condition.holds_atom (a : L.Atom V) :
    (Condition.atom a).Holds g ↔
      ∃ v : Fin a.arity → M, (∀ i, v i ∈ g (a.args i)) ∧ Structure.RelMap a.rel v := Iff.rfl

@[simp] theorem Condition.holds_eq (u v : V) :
    (Condition.eq u v : Condition L V).Holds g ↔ ∃ m : M, m ∈ g u ∧ m ∈ g v := Iff.rfl

@[simp] theorem Condition.holds_neg (K : DRS L V) :
    (Condition.neg K).Holds g ↔ ¬ ∃ g', K.Verifies g g' := Iff.rfl

@[simp] theorem Condition.holds_imp (a c : DRS L V) :
    (Condition.imp a c).Holds g ↔ ∀ g', a.Verifies g g' → ∃ g'', c.Verifies g' g'' := Iff.rfl

@[simp] theorem Condition.holds_dis (l r : DRS L V) :
    (Condition.dis l r).Holds g ↔ (∃ g', l.Verifies g g') ∨ ∃ g', r.Verifies g g' := Iff.rfl

@[simp] theorem Condition.holdsAll_nil : Condition.HoldsAll ([] : List (Condition L V)) g :=
  trivial

@[simp] theorem Condition.holdsAll_cons (c : Condition L V) (cs : List (Condition L V)) :
    Condition.HoldsAll (c :: cs) g ↔ c.Holds g ∧ Condition.HoldsAll cs g := Iff.rfl

theorem Condition.holdsAll_iff {cs : List (Condition L V)} :
    Condition.HoldsAll cs g ↔ ∀ c ∈ cs, c.Holds g := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

@[simp] theorem Condition.holdsAll_append (cs ds : List (Condition L V)) :
    Condition.HoldsAll (cs ++ ds) g ↔ Condition.HoldsAll cs g ∧ Condition.HoldsAll ds g := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih, and_assoc]

/-- Established referents persist: a verifying output extends its input (Kamp, van Genabith and
Reyle, Def. 27(ii)). -/
theorem DRS.Verifies.le {K : DRS L V} (h : K.Verifies f g) : f ≤ g := by
  obtain ⟨U, cs⟩ := K
  exact h.1

theorem DRS.Verifies.domain_eq {K : DRS L V} (h : K.Verifies f g) :
    PFun.Dom g = PFun.Dom f ∪ ↑K.referents := by
  obtain ⟨U, cs⟩ := K
  exact h.2.1

theorem DRS.Verifies.holdsAll {K : DRS L V} (h : K.Verifies f g) :
    Condition.HoldsAll K.conditions g := by
  obtain ⟨U, cs⟩ := K
  exact h.2.2

@[simp] theorem DRS.verifies_empty : (DRS.empty : DRS L V).Verifies f g ↔ g = f := by
  simp only [DRS.empty, DRS.verifies_mk, Condition.holdsAll_nil, and_true,
    Finset.coe_empty, Set.union_empty]
  exact ⟨fun ⟨hle, hdom⟩ => (PFun.eq_of_le_of_dom_subset hle hdom.subset).symm,
    fun h => h ▸ ⟨le_rfl, rfl⟩⟩

/-- Introducing a referent is a covering step of the extension order when the referent is novel,
and inert when it is familiar. -/
theorem DRS.verifies_singleton_nil_iff (u : V) :
    DRS.Verifies (.mk {u} [] : DRS L V) f g ↔
      (¬(f u).Dom ∧ f ⋖ g ∧ (g u).Dom) ∨ ((f u).Dom ∧ g = f) := by
  simp only [DRS.verifies_mk, Condition.holdsAll_nil, and_true, Finset.coe_singleton]
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

/-! ### Coincidence

Verification reads an embedding at its occurring referents: whether a re-declared referent is
already valued matters (fn. 4), so the congruence is over `varFinset`, not `freeVarFinset`. -/

section Congruence

variable [DecidableEq V]

private theorem DRS.verifies_piecewise {U : Finset V} {cs : List (Condition L V)}
    (hIH : ∀ {k k' : V → Part M}, Set.EqOn k k' ↑(Condition.varFinsetL cs) →
      (Condition.HoldsAll cs k ↔ Condition.HoldsAll cs k'))
    {f f' g' : V → Part M}
    (h : Set.EqOn f f' ↑(DRS.varFinset (.mk U cs : DRS L V)))
    (hv : DRS.Verifies (.mk U cs) f' g') :
    DRS.Verifies (.mk U cs) f (U.piecewise g' f) ∧
      ∀ ⦃x⦄, f x = f' x → U.piecewise g' f x = g' x := by
  obtain ⟨hle, hdom, hh⟩ := hv
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
  refine ⟨⟨Pi.le_def.mpr fun x => ?_, Set.ext fun x => ?_, ?_⟩, hag⟩
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
/-- Whether some output verifies a DRS reads the input only at the occurring referents. -/
theorem DRS.exists_verifies_congr (K : DRS L V) {f f' : V → Part M}
    (h : Set.EqOn f f' ↑K.varFinset) :
    (∃ g, K.Verifies f g) ↔ ∃ g, K.Verifies f' g := by
  match K with
  | .mk U cs =>
    have hIH : ∀ {k k' : V → Part M}, Set.EqOn k k' ↑(Condition.varFinsetL cs) →
        (Condition.HoldsAll cs k ↔ Condition.HoldsAll cs k') :=
      fun hkk' => Condition.holdsAll_congr cs hkk'
    exact ⟨fun ⟨g, hg⟩ => ⟨_, (DRS.verifies_piecewise hIH h.symm hg).1⟩,
      fun ⟨g, hg⟩ => ⟨_, (DRS.verifies_piecewise hIH h hg).1⟩⟩
/-- A condition reads an embedding only at its occurring referents. -/
theorem Condition.holds_congr (c : Condition L V) {g g' : V → Part M}
    (h : Set.EqOn g g' ↑c.varFinset) : c.Holds g ↔ c.Holds g' := by
  match c with
  | .atom a =>
    simp only [Condition.holds_atom]
    refine exists_congr fun v => and_congr_left fun _ => forall_congr' fun i => ?_
    rw [h (by simp only [Condition.varFinset_atom, Finset.coe_image, Finset.coe_univ,
      Set.image_univ]; exact Set.mem_range_self i)]
  | .eq u v =>
    simp only [Condition.holds_eq]
    rw [h (by simp), h (by simp)]
  | .neg K =>
    rw [Condition.varFinset_neg] at h
    exact not_congr (DRS.exists_verifies_congr K h)
  | .imp a c =>
    obtain ⟨Ua, csa⟩ := a
    rw [Condition.varFinset_imp] at h
    have ha := h.mono (Finset.coe_subset.mpr Finset.subset_union_left)
    have hc := h.mono (Finset.coe_subset.mpr Finset.subset_union_right)
    have hIHa : ∀ {k k' : V → Part M}, Set.EqOn k k' ↑(Condition.varFinsetL csa) →
        (Condition.HoldsAll csa k ↔ Condition.HoldsAll csa k') :=
      fun hkk' => Condition.holdsAll_congr csa hkk'
    simp only [Condition.holds_imp]
    constructor
    · intro hL g₁' hg₁'
      obtain ⟨hver, hag⟩ := DRS.verifies_piecewise hIHa ha hg₁'
      obtain ⟨g₂, hg₂⟩ := hL _ hver
      exact (DRS.exists_verifies_congr c fun x hx => hag (hc hx)).mp ⟨g₂, hg₂⟩
    · intro hR g₁ hg₁
      obtain ⟨hver, hag⟩ := DRS.verifies_piecewise hIHa ha.symm hg₁
      obtain ⟨g₂, hg₂⟩ := hR _ hver
      exact (DRS.exists_verifies_congr c fun x hx => hag (hc hx).symm).mp ⟨g₂, hg₂⟩
  | .dis l r =>
    rw [Condition.varFinset_dis] at h
    exact or_congr
      (DRS.exists_verifies_congr l (h.mono (Finset.coe_subset.mpr Finset.subset_union_left)))
      (DRS.exists_verifies_congr r (h.mono (Finset.coe_subset.mpr Finset.subset_union_right)))
theorem Condition.holdsAll_congr (cs : List (Condition L V)) {g g' : V → Part M}
    (h : Set.EqOn g g' ↑(Condition.varFinsetL cs)) :
    Condition.HoldsAll cs g ↔ Condition.HoldsAll cs g' := by
  match cs with
  | [] => exact Iff.rfl
  | c :: cs =>
    rw [Condition.varFinsetL_cons, Finset.coe_union] at h
    exact and_congr (Condition.holds_congr c (h.mono Set.subset_union_left))
      (Condition.holdsAll_congr cs (h.mono Set.subset_union_right))
end

/-- An input valuing no occurring referent verifies a DRS exactly when the DRS is true. -/
theorem DRS.exists_verifies_iff_isTrue {K : DRS L V} {f : V → Part M}
    (hf : ∀ x ∈ K.varFinset, f x = ⊥) : (∃ g, K.Verifies f g) ↔ K.IsTrue M :=
  DRS.exists_verifies_congr K fun x hx => hf x (Finset.mem_coe.mp hx)

end Congruence

/-! ### The Merging Lemma -/

/-- The Merging Lemma: a merge is verified by sequencing its parts, when the universe of `K₂`
captures no referent the conditions of `K₁` use outside `K₁`'s own universe. Re-declaring a
referent of `K₁`'s universe is inert, and no referential presupposition is needed. -/
theorem DRS.verifies_merge [DecidableEq V] (K₁ K₂ : DRS L V)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions \ K₁.referents)) :
    (K₁.merge K₂).Verifies f g ↔ ∃ h, K₁.Verifies f h ∧ K₂.Verifies h g := by
  classical
  obtain ⟨U₁, cs₁⟩ := K₁
  obtain ⟨U₂, cs₂⟩ := K₂
  simp only [DRS.merge, DRS.verifies_mk, Condition.holdsAll_append, Finset.coe_union]
  constructor
  · rintro ⟨hle, hdom, hh₁, hh₂⟩
    set h : V → Part M := (PFun.Dom f ∪ ↑U₁).piecewise g ⊥ with hdef
    have happly : ∀ ⦃x⦄, x ∈ PFun.Dom f ∪ ↑U₁ → h x = g x := fun x hx =>
      Set.piecewise_eq_of_mem _ _ _ hx
    have hbot : ∀ ⦃x⦄, x ∉ PFun.Dom f ∪ ↑U₁ → h x = ⊥ := fun x hx =>
      Set.piecewise_eq_of_notMem _ _ _ hx
    have hsub : PFun.Dom f ∪ ↑U₁ ⊆ PFun.Dom g := by
      rw [hdom, ← Set.union_assoc]
      exact Set.subset_union_left
    have hdomh : PFun.Dom h = PFun.Dom f ∪ ↑U₁ := by
      ext x
      show (h x).Dom ↔ _
      by_cases hx : x ∈ PFun.Dom f ∪ ↑U₁
      · rw [happly hx]
        exact iff_of_true (hsub hx) hx
      · rw [hbot hx]
        exact iff_of_false Part.not_none_dom hx
    have heq : Set.EqOn h g ↑(Condition.varFinsetL cs₁) := by
      intro x hx
      by_cases hxm : x ∈ PFun.Dom f ∪ ↑U₁
      · exact happly hxm
      · rw [hbot hxm]
        by_contra hgx
        have hxg : x ∈ PFun.Dom g := by
          by_contra hd
          exact hgx (Part.eq_bot_iff_not_dom.2 hd).symm
        rw [hdom] at hxg
        rcases hxg with hmem | hmem | hmem
        · exact hxm (Or.inl hmem)
        · exact hxm (Or.inr hmem)
        · exact Finset.disjoint_left.mp hfresh (Finset.mem_coe.mp hmem)
            (Finset.mem_sdiff.mpr ⟨hx, fun hU₁ => hxm (Or.inr (Finset.mem_coe.mpr hU₁))⟩)
    refine ⟨h, ⟨?_, hdomh, (Condition.holdsAll_congr cs₁ heq).mpr hh₁⟩,
      ?_, by rw [hdom, hdomh, Set.union_assoc], hh₂⟩
    · exact Pi.le_def.mpr fun x => by
        by_cases hx : x ∈ PFun.Dom f ∪ ↑U₁
        · rw [happly hx]
          exact hle x
        · rw [hbot (by exact hx)]
          rw [Part.eq_bot_iff_not_dom.2 fun hfx => hx (Or.inl hfx)]
    · exact Pi.le_def.mpr fun x => by
        by_cases hx : x ∈ PFun.Dom f ∪ ↑U₁
        · exact (happly hx).le
        · exact (hbot hx) ▸ bot_le
  · rintro ⟨h, ⟨hle₁, hdom₁, hh₁⟩, hle₂, hdom₂, hh₂⟩
    have heq : Set.EqOn h g ↑(Condition.varFinsetL cs₁) := by
      intro x hx
      by_cases hxh : (h x).Dom
      · exact PFun.le_iff_eqOn_dom.mp hle₂ hxh
      · rw [Part.eq_bot_iff_not_dom.2 hxh]
        by_contra hgx
        have hxg : x ∈ PFun.Dom g := by
          by_contra hd
          exact hgx (Part.eq_bot_iff_not_dom.2 hd).symm
        rw [hdom₂] at hxg
        rcases hxg with hmem | hmem
        · exact hxh hmem
        · refine Finset.disjoint_left.mp hfresh (Finset.mem_coe.mp hmem)
            (Finset.mem_sdiff.mpr ⟨hx, fun hU₁ => ?_⟩)
          have hxd : x ∈ PFun.Dom h := by
            rw [hdom₁]
            exact Set.mem_union_right _ (Finset.mem_coe.mpr hU₁)
          exact hxh hxd
    exact ⟨hle₁.trans hle₂, by rw [hdom₂, hdom₁, Set.union_assoc],
      (Condition.holdsAll_congr cs₁ heq).mp hh₁, hh₂⟩

/-! ### Agreement with total assignments

On reuse-free DRSs the total and partial semantics agree: a total verifying extension restricts
to a partial one, and a partial one totalizes by reading the input off its domain. On a DRS that
re-declares a referent they diverge (fn. 4; witness in `Studies/Muskens1996.lean`). -/

section Agreement

variable [DecidableEq V]

omit [DecidableEq V] in
private theorem dom_res {X : Set V} {f' : V → M} : PFun.Dom (PFun.res f' X) = X :=
  PFun.dom_restrict _

omit [DecidableEq V] in
private theorem mem_res_of_mem {X : Set V} {f' : V → M} {x : V} (hx : x ∈ X) :
    f' x ∈ PFun.res f' X x :=
  (PFun.mem_res _ _ _ _).2 ⟨hx, rfl⟩

open Classical in
/-- Read a partial embedding totally, defaulting to `f'` off its domain. -/
private noncomputable def toTotal (g : V → Part M) (f' : V → M) : V → M :=
  fun x ↦ (g x).getOrElse (f' x)

open Classical in
omit [DecidableEq V] in
private theorem toTotal_mem {g : V → Part M} {f' : V → M} {x : V} (h : (g x).Dom) :
    toTotal g f' x ∈ g x := by
  show (g x).getOrElse (f' x) ∈ g x
  rw [Part.getOrElse_of_dom _ h]
  exact Part.get_mem h

open Classical in
omit [DecidableEq V] in
private theorem toTotal_of_not_dom {g : V → Part M} {f' : V → M} {x : V} (h : ¬(g x).Dom) :
    toTotal g f' x = f' x :=
  Part.getOrElse_of_not_dom _ h _

private theorem verifies_res {X U : Finset V} {cs : List (Condition L V)}
    (hXU : Disjoint X U)
    (hIH : ∀ (k : V → Part M) (k' : V → M), PFun.Dom k = ↑(X ∪ U) →
      (∀ x ∈ X ∪ U, k' x ∈ k x) → (VerifiesAllTotal k' cs ↔ Condition.HoldsAll cs k))
    {f : V → Part M} {f' g' : V → M}
    (hdom : PFun.Dom f = ↑X) (hff' : ∀ x ∈ X, f' x ∈ f x)
    (hext : DRS.Extends (.mk U cs : DRS L V) f' g') (hv : VerifiesAllTotal g' cs) :
    DRS.Verifies (.mk U cs) f (PFun.res g' ↑(X ∪ U)) := by
  have hagree : ∀ x ∈ X, g' x = f' x := fun x hx =>
    hext x (Finset.disjoint_left.mp hXU hx)
  refine ⟨Pi.le_def.mpr fun x a ha => ?_, by rw [dom_res, hdom, Finset.coe_union], ?_⟩
  · have hxX : x ∈ X := by
      have hd : x ∈ PFun.Dom f := Part.dom_iff_mem.2 ⟨a, ha⟩
      rwa [hdom, Finset.mem_coe] at hd
    have hax : a = f' x := Part.mem_unique ha (hff' x hxX)
    rw [hax, ← hagree x hxX]
    exact mem_res_of_mem (by simp [hxX])
  · exact (hIH _ g' dom_res fun x hx => mem_res_of_mem (by simpa using hx)).mp hv

open Classical in
private theorem extends_verifiesTotal_toTotal {X U : Finset V} {cs : List (Condition L V)}
    (hIH : ∀ (k : V → Part M) (k' : V → M), PFun.Dom k = ↑(X ∪ U) →
      (∀ x ∈ X ∪ U, k' x ∈ k x) → (VerifiesAllTotal k' cs ↔ Condition.HoldsAll cs k))
    {f g : V → Part M} {f' : V → M}
    (hdom : PFun.Dom f = ↑X) (hff' : ∀ x ∈ X, f' x ∈ f x)
    (hv : DRS.Verifies (.mk U cs) f g) :
    DRS.Extends (.mk U cs : DRS L V) f' (toTotal g f') ∧ VerifiesAllTotal (toTotal g f') cs := by
  obtain ⟨hle, hdomg, hh⟩ := hv
  have hval : ∀ x ∈ X ∪ U, toTotal g f' x ∈ g x := by
    intro x hx
    refine toTotal_mem ?_
    show x ∈ PFun.Dom g
    rw [hdomg, hdom, ← Finset.coe_union]
    exact Finset.mem_coe.mpr hx
  constructor
  · intro x hxU
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
  · exact (hIH g _ (by rw [hdomg, hdom, Finset.coe_union]) hval).mpr hh

mutual
theorem Condition.verifiesConditionTotal_iff_holds {X : Finset V} (c : Condition L V)
    (hrf : Condition.ReuseFreeAt X c) (hfv : c.freeVarFinset ⊆ X)
    {f : V → Part M} {f' : V → M}
    (hdom : PFun.Dom f = ↑X) (hff' : ∀ x ∈ X, f' x ∈ f x) :
    VerifiesConditionTotal f' c ↔ c.Holds f := by
  match c with
  | .atom a =>
    simp only [verifiesTotal_atom, Condition.holds_atom, Atom.Realize]
    have hval : ∀ i, f' (a.args i) ∈ f (a.args i) := fun i =>
      hff' _ (hfv (by simp [Condition.freeVarFinset_atom]))
    constructor
    · exact fun h => ⟨f' ∘ a.args, hval, h⟩
    · rintro ⟨v, hv, hrel⟩
      have : f' ∘ a.args = v := funext fun i => Part.mem_unique (hval i) (hv i)
      rwa [this]
  | .eq u v =>
    simp only [verifiesTotal_eq, Condition.holds_eq]
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
    have hIH : ∀ (k : V → Part M) (k' : V → M), PFun.Dom k = ↑(X ∪ U) →
        (∀ x ∈ X ∪ U, k' x ∈ k x) → (VerifiesAllTotal k' cs ↔ Condition.HoldsAll cs k) :=
      fun k k' hk hkk' => Condition.verifiesAllTotal_iff_holdsAll cs hrf.2 hfvc hk hkk'
    simp only [verifiesTotal_neg, Condition.holds_neg]
    refine not_congr ⟨fun ⟨g', hg'⟩ => ⟨_, verifies_res hrf.1 hIH hdom hff' hg'.1
      ((verifiesTotal_mk U cs).mp hg'.2 |> verifiesAllTotal_iff.mpr)⟩, fun ⟨g, hg⟩ => ?_⟩
    obtain ⟨hext, hv⟩ := extends_verifiesTotal_toTotal hIH hdom hff' hg
    exact ⟨_, hext, (verifiesTotal_mk U cs).mpr (verifiesAllTotal_iff.mp hv)⟩
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
        (∀ x ∈ X ∪ Ua, k' x ∈ k x) →
          (VerifiesAllTotal k' csa ↔ Condition.HoldsAll csa k) :=
      fun k k' hk hkk' => Condition.verifiesAllTotal_iff_holdsAll csa hrfa hfvca hk hkk'
    have hIHc : ∀ (k : V → Part M) (k' : V → M), PFun.Dom k = ↑((X ∪ Ua) ∪ Uc) →
        (∀ x ∈ (X ∪ Ua) ∪ Uc, k' x ∈ k x) →
          (VerifiesAllTotal k' csc ↔ Condition.HoldsAll csc k) :=
      fun k k' hk hkk' => Condition.verifiesAllTotal_iff_holdsAll csc hrfc hfvcc hk hkk'
    simp only [verifiesTotal_imp, Condition.holds_imp]
    constructor
    · intro hL g₁ hg₁
      obtain ⟨hext₁, hv₁⟩ := extends_verifiesTotal_toTotal hIHa hdom hff' hg₁
      obtain ⟨h', hexth', hvh'⟩ := hL (toTotal g₁ f') hext₁ ((verifiesTotal_mk Ua csa).mpr
        (verifiesAllTotal_iff.mp hv₁))
      obtain ⟨hle₁, hdom₁, hh₁⟩ := hg₁
      have hdom₁' : PFun.Dom g₁ = ↑(X ∪ Ua) := by rw [hdom₁, hdom, Finset.coe_union]
      have hff₁ : ∀ x ∈ X ∪ Ua, toTotal g₁ f' x ∈ g₁ x := fun x hx =>
        toTotal_mem (show x ∈ PFun.Dom g₁ by rw [hdom₁']; exact Finset.mem_coe.mpr hx)
      exact ⟨_, verifies_res hXUc hIHc hdom₁' hff₁ hexth'
        (verifiesAllTotal_iff.mpr ((verifiesTotal_mk Uc csc).mp hvh'))⟩
    · intro hR g₁' hext₁ hv₁
      have hg₁ := verifies_res hXUa hIHa hdom hff' hext₁
        (verifiesAllTotal_iff.mpr ((verifiesTotal_mk Ua csa).mp hv₁))
      obtain ⟨g₂, hg₂⟩ := hR _ hg₁
      have hff₁ : ∀ x ∈ X ∪ Ua, g₁' x ∈ PFun.res g₁' ↑(X ∪ Ua) x := fun x hx =>
        mem_res_of_mem (Finset.mem_coe.mpr hx)
      obtain ⟨hext₂, hv₂⟩ := extends_verifiesTotal_toTotal hIHc dom_res hff₁ hg₂
      exact ⟨_, hext₂, (verifiesTotal_mk Uc csc).mpr (verifiesAllTotal_iff.mp hv₂)⟩
  | .dis l r =>
    obtain ⟨Ul, csl⟩ := l
    obtain ⟨Ur, csr⟩ := r
    rw [Condition.reuseFreeAt_dis, DRS.reuseFreeAt_mk, DRS.reuseFreeAt_mk] at hrf
    obtain ⟨⟨hXUl, hrfl⟩, hXUr, hrfr⟩ := hrf
    rw [Condition.freeVarFinset_dis, Finset.union_subset_iff] at hfv
    have hfvcl := DRS.freeVarFinset_subset_iff.mp hfv.1
    have hfvcr := DRS.freeVarFinset_subset_iff.mp hfv.2
    have hIHl : ∀ (k : V → Part M) (k' : V → M), PFun.Dom k = ↑(X ∪ Ul) →
        (∀ x ∈ X ∪ Ul, k' x ∈ k x) →
          (VerifiesAllTotal k' csl ↔ Condition.HoldsAll csl k) :=
      fun k k' hk hkk' => Condition.verifiesAllTotal_iff_holdsAll csl hrfl hfvcl hk hkk'
    have hIHr : ∀ (k : V → Part M) (k' : V → M), PFun.Dom k = ↑(X ∪ Ur) →
        (∀ x ∈ X ∪ Ur, k' x ∈ k x) →
          (VerifiesAllTotal k' csr ↔ Condition.HoldsAll csr k) :=
      fun k k' hk hkk' => Condition.verifiesAllTotal_iff_holdsAll csr hrfr hfvcr hk hkk'
    simp only [verifiesTotal_dis, Condition.holds_dis]
    refine or_congr ⟨fun ⟨g', hext, hv⟩ => ⟨_, verifies_res hXUl hIHl hdom hff' hext
        (verifiesAllTotal_iff.mpr ((verifiesTotal_mk Ul csl).mp hv))⟩, fun ⟨g, hg⟩ => ?_⟩
      ⟨fun ⟨g', hext, hv⟩ => ⟨_, verifies_res hXUr hIHr hdom hff' hext
        (verifiesAllTotal_iff.mpr ((verifiesTotal_mk Ur csr).mp hv))⟩, fun ⟨g, hg⟩ => ?_⟩
    · obtain ⟨hext, hv⟩ := extends_verifiesTotal_toTotal hIHl hdom hff' hg
      exact ⟨_, hext, (verifiesTotal_mk Ul csl).mpr (verifiesAllTotal_iff.mp hv)⟩
    · obtain ⟨hext, hv⟩ := extends_verifiesTotal_toTotal hIHr hdom hff' hg
      exact ⟨_, hext, (verifiesTotal_mk Ur csr).mpr (verifiesAllTotal_iff.mp hv)⟩
theorem Condition.verifiesAllTotal_iff_holdsAll {X : Finset V} (cs : List (Condition L V))
    (hrf : Condition.ReuseFreeAllAt X cs) (hfv : Condition.freeVarFinsetL cs ⊆ X)
    {f : V → Part M} {f' : V → M}
    (hdom : PFun.Dom f = ↑X) (hff' : ∀ x ∈ X, f' x ∈ f x) :
    VerifiesAllTotal f' cs ↔ Condition.HoldsAll cs f := by
  match cs with
  | [] => exact Iff.rfl
  | c :: cs =>
    rw [Condition.reuseFreeAllAt_cons] at hrf
    rw [Condition.freeVarFinsetL_cons, Finset.union_subset_iff] at hfv
    exact and_congr
      (Condition.verifiesConditionTotal_iff_holds c hrf.1 hfv.1 hdom hff')
      (Condition.verifiesAllTotal_iff_holdsAll cs hrf.2 hfv.2 hdom hff')
end

/-- On a reuse-free DRS the total and partial semantics agree: some total extension of `f'`
verifies `K` iff some partial output verifies it from the partial reading of `f'`. -/
theorem DRS.exists_extends_verifiesTotal_iff_exists_verifies {X : Finset V} {K : DRS L V}
    (hrf : K.ReuseFreeAt X) (hfv : K.freeVarFinset ⊆ X)
    {f : V → Part M} {f' : V → M}
    (hdom : PFun.Dom f = ↑X) (hff' : ∀ x ∈ X, f' x ∈ f x) :
    (∃ g', K.Extends f' g' ∧ VerifiesTotal g' K) ↔ ∃ g, K.Verifies f g := by
  obtain ⟨U, cs⟩ := K
  rw [DRS.reuseFreeAt_mk] at hrf
  have hfvc := DRS.freeVarFinset_subset_iff.mp hfv
  have hIH : ∀ (k : V → Part M) (k' : V → M), PFun.Dom k = ↑(X ∪ U) →
      (∀ x ∈ X ∪ U, k' x ∈ k x) → (VerifiesAllTotal k' cs ↔ Condition.HoldsAll cs k) :=
    fun k k' hk hkk' => Condition.verifiesAllTotal_iff_holdsAll cs hrf.2 hfvc hk hkk'
  constructor
  · rintro ⟨g', hext, hv⟩
    exact ⟨_, verifies_res hrf.1 hIH hdom hff' hext
      (verifiesAllTotal_iff.mpr ((verifiesTotal_mk U cs).mp hv))⟩
  · rintro ⟨g, hg⟩
    obtain ⟨hext, hv⟩ := extends_verifiesTotal_toTotal hIH hdom hff' hg
    exact ⟨_, hext, (verifiesTotal_mk U cs).mpr (verifiesAllTotal_iff.mp hv)⟩

end Agreement

end DRT
