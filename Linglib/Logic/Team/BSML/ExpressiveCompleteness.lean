module

public import Linglib.Logic.Team.BSML.Properties
public import Linglib.Logic.Team.BSML.Characteristic
public import Linglib.Logic.Team.Definability

/-!
# Expressive completeness for BSML

Anttila, with Knudstorp, proves that BSML is [expressively complete](##BSML.definableClass_eq) for
the classes of pointed team models that are convex, union closed and invariant under bounded
bisimulation, a question Aloni, Anttila and Yang left open; its `NE`-free fragment, classical modal
logic, is [complete for the flat ones](##BSML.definableClass_neFree_eq) and [expresses strictly
less](##BSML.definableClass_neFree_ssubset). Such a class is fixed by the depth `k` world types of
its teams, which over finitely many atoms are finite in number, so [a convex union-closed property
of sets of types is expressed by one formula across all
models](##BSML.exists_formula_iff_image_mem).

## Implementation notes

Successor sets and teams are `Finset`s, so the classes range over image-finite pointed models with
finite teams and worlds in one universe, where the source takes arbitrary ones. Union closure is
binary, which on finite teams is the source's closure under nonempty unions, and it crosses models
through their disjoint union. The atoms are finite and there is at least one, since BSML has no
tautology without atoms.

## References

* [aloni-2022]
* [aloni-anttila-yang-2024]
* [anttila-2025]
* [anttila-knudstorp-2025]
-/

@[expose] public section

namespace BSML

open Team ModalLogic

universe u

variable {Atom : Type*}

/-- Support at a pointed team model. -/
abbrev pointedSupport (φ : Formula Atom) (p : PointedTeam.{u} Atom) : Prop :=
  support p.model φ p.team

/-! ### Sets of types -/

section Types

variable [Inhabited Atom] {n k : ℕ} (e : Fin n → Atom) {W : Type*} [DecidableEq W]

/-- The disjunction of the Hintikka formulas of a set of types. -/
noncomputable def typeDisj (S : Finset (WorldType n k)) : Formula Atom :=
  bigDisj (S.toList.map (hintikka e k))

theorem support_typeDisj_iff (M : KripkeModel W Atom) (S : Finset (WorldType n k)) (t : Finset W) :
    support M (typeDisj e S) t ↔ t.image (worldType e M k) ⊆ S := by
  simp only [typeDisj, support_bigDisj_hintikka_iff, Finset.mem_toList, Finset.image_subset_iff]

/-- A convex union-closed property of sets of types is expressed by one formula across all models:
a team supports the formula exactly when its worlds' types form a set with the property
([anttila-2025] Lemmas 3.2.9, 3.2.10 and 3.3.4, on types in place of valuations). -/
theorem exists_formula_iff_image_mem (T : Set (Finset (WorldType n k))) (hc : T.OrdConnected)
    (hs : SupClosed T) :
    ∃ φ : Formula Atom, ∀ {W : Type u} [DecidableEq W] (M : KripkeModel W Atom) (t : Finset W),
      support M φ t ↔ t.image (worldType e M k) ∈ T := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | hne
  · exact ⟨.strongFalsum, fun M t ↦ iff_of_false (not_support_strongFalsum M t) (by simp)⟩
  set F : Finset (Finset (WorldType n k)) := T.toFinset
  have hF : F.Nonempty := Set.toFinset_nonempty.2 hne
  set U : Finset (WorldType n k) := F.sup id
  have hU : U ∈ T := hs.finsetSup_mem hF fun s hs ↦ Set.mem_toFinset.1 hs
  have hle {s} (h : s ∈ T) : s ⊆ U := Finset.le_sup (f := id) (Set.mem_toFinset.2 h)
  set H : Finset (Finset (WorldType n k)) :=
    Finset.univ.filter fun H ↦ ∀ s ∈ T, (s ∩ H).Nonempty
  refine ⟨.conj (typeDisj e U)
    (bigConj (H.toList.map fun H ↦ .disj (.conj (typeDisj e H) .ne) (typeDisj e U))),
    fun {W} _ M t ↦ ⟨?_, fun ht ↦ ?_⟩⟩
  · rintro ⟨hup, hhit⟩
    have hup := (support_typeDisj_iff e M U t).1 hup
    have hnot : (t.image (worldType e M k))ᶜ ∉ H := fun hmem ↦ by
      obtain ⟨t₁, ⟨h₁, x, hx⟩, t₂, -, hsplit⟩ := (support_bigConj_iff M _ t).1 hhit _
        (List.mem_map.2 ⟨_, Finset.mem_toList.2 hmem, rfl⟩)
      have hxt : x ∈ t := le_sup_left.trans_eq hsplit hx
      exact Finset.mem_compl.1 ((support_typeDisj_iff e M _ t₁).1 h₁
        (Finset.mem_image_of_mem _ hx)) (Finset.mem_image_of_mem _ hxt)
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hnot
    obtain ⟨s, hs', hsne⟩ := hnot
    have hsub : s ⊆ t.image (worldType e M k) := fun a ha ↦ by
      by_contra hat
      exact hsne ⟨a, Finset.mem_inter.2 ⟨ha, Finset.mem_compl.2 hat⟩⟩
    exact hc.out hs' hU ⟨hsub, hup⟩
  · have hup := (support_typeDisj_iff e M U t).2 (hle ht)
    refine ⟨hup, (support_bigConj_iff M _ t).2 fun ψ hψ ↦ ?_⟩
    obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hψ
    obtain ⟨a, ha⟩ := (Finset.mem_filter.1 (Finset.mem_toList.1 hS)).2 _ ht
    obtain ⟨hat, haS⟩ := Finset.mem_inter.1 ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hat
    refine ⟨{v}, ⟨(support_typeDisj_iff e M S {v}).2 ?_, Finset.singleton_nonempty v⟩, t, hup, ?_⟩
    · simpa using haS
    · exact Finset.union_eq_right.2 (Finset.singleton_subset_iff.2 hv)

end Types

/-! ### Expressive completeness -/

section Completeness

private theorem image_filter_mem {W τ : Type*} [DecidableEq W] [DecidableEq τ] {f : W → τ}
    {s : Finset W} {σ : Finset τ} (h : σ ⊆ s.image f) :
    (s.filter (f · ∈ σ)).image f = σ := by
  ext a
  simp only [Finset.mem_image, Finset.mem_filter]
  refine ⟨fun ⟨v, ⟨_, hv⟩, e⟩ ↦ e ▸ hv, fun ha ↦ ?_⟩
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (h ha)
  exact ⟨v, ⟨hv, ha⟩, rfl⟩

private theorem stateBisim_of_image_eq {n k : ℕ} {e : Fin n → Atom} (he : e.Surjective)
    {W W' : Type*} [DecidableEq W] [DecidableEq W'] {M : KripkeModel W Atom}
    {M' : KripkeModel W' Atom} {s : Finset W} {s' : Finset W'}
    (h : s.image (worldType e M k) = s'.image (worldType e M' k)) : StateBisim k M s M' s' := by
  refine ⟨fun w hw ↦ ?_, fun w' hw' ↦ ?_⟩
  · obtain ⟨w', hw', hb⟩ := Finset.mem_image.1 (h ▸ Finset.mem_image_of_mem _ hw)
    exact ⟨w', hw', (worldType_eq_iff_worldBisim he k w w').1 hb.symm⟩
  · obtain ⟨w, hw, hb⟩ := Finset.mem_image.1 (h.symm ▸ Finset.mem_image_of_mem _ hw')
    exact ⟨w, hw, (worldType_eq_iff_worldBisim he k w w').1 hb⟩

private theorem image_sum_inl {n k : ℕ} {e : Fin n → Atom} (he : e.Surjective) {W W' : Type*}
    [DecidableEq W] [DecidableEq W'] (M : KripkeModel W Atom) (M' : KripkeModel W' Atom)
    (s : Finset W) :
    (s.map .inl).image (worldType e (M.sum M') k) = s.image (worldType e M k) := by
  ext a
  simp only [Finset.mem_image, Finset.mem_map, Function.Embedding.inl_apply,
    exists_exists_and_eq_and]
  exact exists_congr fun w ↦ and_congr_right fun _ ↦ by
    rw [(worldType_eq_iff_worldBisim he k _ _).2 (WorldBisim.sum_inl k M M' w)]

private theorem image_sum_inr {n k : ℕ} {e : Fin n → Atom} (he : e.Surjective) {W W' : Type*}
    [DecidableEq W] [DecidableEq W'] (M : KripkeModel W Atom) (M' : KripkeModel W' Atom)
    (s : Finset W') :
    (s.map .inr).image (worldType e (M.sum M') k) = s.image (worldType e M' k) := by
  ext a
  simp only [Finset.mem_image, Finset.mem_map, Function.Embedding.inr_apply,
    exists_exists_and_eq_and]
  exact exists_congr fun w ↦ and_congr_right fun _ ↦ by
    rw [(worldType_eq_iff_worldBisim he k _ _).2 (WorldBisim.sum_inr k M M' w)]

variable [Fintype Atom] [Inhabited Atom]

/-- **BSML is expressively complete** for the convex, union-closed classes of pointed team models
invariant under bounded bisimulation ([anttila-2025] Theorem 3.3.7 and the remark after it, p. 83).
-/
theorem definableClass_eq :
    definableClass (pointedSupport : Formula Atom → PointedTeam.{u} Atom → Prop) =
      {P | (∀ {W : Type u} [DecidableEq W] (M : KripkeModel W Atom),
        (fiber P M).OrdConnected ∧ SupClosed (fiber P M)) ∧ BoundedBisimInvariant P} := by
  apply Set.Subset.antisymm
  · refine definableClass_subset fun φ ↦ ⟨fun M ↦ ?_, φ.modalDepth, fun p hp p' hb ↦ ?_⟩
    · exact ⟨ordConnected_support M φ, supClosed_support M φ⟩
    · exact (invariant_eval φ le_rfl true hb).1 hp
  · rintro P ⟨hclosed, k, hk⟩
    obtain ⟨e, he⟩ : ∃ e : Fin (Fintype.card Atom) → Atom, e.Surjective :=
      ⟨_, (Fintype.equivFin Atom).symm.surjective⟩
    let τ (p : PointedTeam.{u} Atom) := p.team.image (worldType e p.model k)
    have hmem {p} : p ∈ P ↔ τ p ∈ τ '' P :=
      ⟨Set.mem_image_of_mem τ, fun ⟨q, hq, h⟩ ↦ hk q hq p (stateBisim_of_image_eq he h)⟩
    have hc : (τ '' P).OrdConnected := ⟨by
      rintro _ ⟨q₁, hq₁, rfl⟩ _ ⟨⟨W, M, s₂⟩, hq₂, rfl⟩ σ ⟨h₁, h₂⟩
      have hs₁ : s₂.filter (worldType e M k · ∈ τ q₁) ∈ fiber P M :=
        hmem.2 ⟨q₁, hq₁, (image_filter_mem (h₁.trans h₂)).symm⟩
      have hs : s₂.filter (worldType e M k · ∈ σ) ∈ fiber P M :=
        (hclosed M).1.out hs₁ hq₂ ⟨fun v hv ↦ Finset.mem_filter.2
          ⟨(Finset.mem_filter.1 hv).1, h₁ (Finset.mem_filter.1 hv).2⟩, Finset.filter_subset _ _⟩
      exact ⟨_, hs, image_filter_mem h₂⟩⟩
    have hs : SupClosed (τ '' P) := by
      rintro _ ⟨⟨W₁, M₁, s₁⟩, h₁, rfl⟩ _ ⟨⟨W₂, M₂, s₂⟩, h₂, rfl⟩
      have h₁' : s₁.map .inl ∈ fiber P (M₁.sum M₂) :=
        hmem.2 ⟨_, h₁, (image_sum_inl he M₁ M₂ s₁).symm⟩
      have h₂' : s₂.map .inr ∈ fiber P (M₁.sum M₂) :=
        hmem.2 ⟨_, h₂, (image_sum_inr he M₁ M₂ s₂).symm⟩
      refine ⟨_, (hclosed (M₁.sum M₂)).2 h₁' h₂', ?_⟩
      simp only [τ, Finset.sup_eq_union, Finset.image_union, image_sum_inl he, image_sum_inr he]
    have hex : ∃ φ : Formula Atom, ∀ {W : Type u} [DecidableEq W] (M : KripkeModel W Atom)
        (t : Finset W), support M φ t ↔ t.image (worldType e M k) ∈ τ '' P :=
      exists_formula_iff_image_mem e _ hc hs
    obtain ⟨φ, hφ⟩ := hex
    exact ⟨φ, Set.ext fun p ↦ (hφ p.model p.team).trans hmem.symm⟩

/-- The `NE`-free fragment of BSML is expressively complete for the flat classes invariant under
bounded bisimulation ([aloni-anttila-yang-2024] Proposition 3.13; [anttila-2025] p. 25). -/
theorem definableClass_neFree_eq :
    definableClass (fun (φ : {φ : Formula Atom // φ.NEFree}) (p : PointedTeam.{u} Atom) ↦
        pointedSupport φ.1 p) =
      {P | (∀ {W : Type u} [DecidableEq W] (M : KripkeModel W Atom), IsFlat (fiber P M)) ∧
        BoundedBisimInvariant P} := by
  apply Set.Subset.antisymm
  · refine definableClass_subset fun φ ↦ ⟨fun M ↦ isFlat_support_of_neFree φ.2 M,
      φ.1.modalDepth, fun p hp p' hb ↦ (invariant_eval φ.1 le_rfl true hb).1 hp⟩
  · rintro P ⟨hflat, k, hk⟩
    obtain ⟨e, he⟩ : ∃ e : Fin (Fintype.card Atom) → Atom, e.Surjective :=
      ⟨_, (Fintype.equivFin Atom).symm.surjective⟩
    obtain ⟨L, hL⟩ : ∃ L : Finset (WorldType (Fintype.card Atom) k), ∀ σ, σ ∈ L ↔
        ∃ p : PointedTeam.{u} Atom, ∃ w, p.team = {w} ∧ p ∈ P ∧ worldType e p.model k w = σ := by
      classical
      exact ⟨Finset.univ.filter fun σ ↦ ∃ p : PointedTeam.{u} Atom, ∃ w, p.team = {w} ∧ p ∈ P ∧
        worldType e p.model k w = σ, fun σ ↦ by simp⟩
    refine ⟨⟨typeDisj e L, neFree_bigDisj _ ?_⟩, Set.ext fun p ↦ ?_⟩
    · simpa using fun τ _ ↦ neFree_hintikka e k τ
    obtain ⟨W, M, t⟩ := p
    change support M (typeDisj e L) t ↔ t ∈ fiber P M
    rw [support_typeDisj_iff, hflat M t, Finset.image_subset_iff]
    refine forall₂_congr fun v _ ↦ ⟨fun hv ↦ ?_, fun hv ↦ (hL _).2
      ⟨⟨W, M, {v}⟩, v, rfl, hv, rfl⟩⟩
    obtain ⟨q, w, hs₀, hp, hw⟩ := (hL _).1 hv
    refine hk q hp ⟨W, M, {v}⟩ (stateBisim_of_image_eq he ?_)
    simp [hs₀, hw]

omit [Fintype Atom] [Inhabited Atom] in
/-- Classical modal logic expresses strictly less than BSML ([anttila-2025] p. 25). -/
theorem definableClass_neFree_ssubset :
    definableClass (fun (φ : {φ : Formula Atom // φ.NEFree}) (p : PointedTeam.{u} Atom) ↦
        pointedSupport φ.1 p) ⊂
      definableClass (pointedSupport : Formula Atom → PointedTeam.{u} Atom → Prop) := by
  refine ⟨definableClass_subset_of_translation (·.1) fun _ _ ↦ Iff.rfl, fun h ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := h ⟨.ne, rfl⟩
  let M : KripkeModel PUnit.{u + 1} Atom := ⟨fun _ ↦ ∅, fun _ _ ↦ False⟩
  have hne : pointedSupport .ne (PointedTeam.mk PUnit M ∅) :=
    (Set.ext_iff.1 hφ _).1 (isFlat_support_of_neFree φ.2 M).empty_mem
  exact Finset.not_nonempty_empty hne

end Completeness

end BSML
