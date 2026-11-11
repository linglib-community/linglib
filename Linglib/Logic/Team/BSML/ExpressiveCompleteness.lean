module

public import Linglib.Logic.Team.BSML.Properties
public import Linglib.Logic.Team.BSML.Characteristic

/-!
# Expressive completeness for BSML

The expressive power of a logic over the atoms $\mathsf{X}$ is the class $\|L\|_{\mathsf{X}}$ of
properties its formulas express, here the `Set.range` of support over [pointed team
models](##ModalLogic.PointedTeam). BSML is, by a result of Knudstorp's, [expressively
complete](##BSML.range_support_eq) for the classes that are convex, union closed and invariant under
bounded bisimulation; [convexity cannot be dropped](##BSML.range_support_ssubset_supClosed). Its
`NE`-free fragment, classical modal logic, is [complete for the flat
classes](##BSML.range_support_neFree_eq) and [expresses strictly
less](##BSML.range_support_neFree_ssubset). An invariant class reads only [the depth `k` world types
of a team](##ModalLogic.mem_iff_types_mem_image), so [a convex union-closed property of sets of
types is one formula across all models](##BSML.exists_formula_iff_image_mem).

## Implementation notes

Successor sets and teams are `Finset`s, so the classes range over image-finite pointed models with
finite teams and worlds in one universe, and a model may have no worlds, where the source takes
arbitrary models with nonempty sets of worlds. At a fixed depth nothing is lost: over finitely many
atoms there are finitely many types, so every pointed model is `k`-bisimilar to an image-finite one
with a finite team. Union closure is binary and per model, which on finite teams is the source's
closure under nonempty unions; the proof carries it across models through their disjoint union.

The atoms are finite and there is at least one, which drops the source's case of no atoms.
`Formula` has no primitive `⊥`, and over no atoms its `NE`-free fragment is empty, so
`range_support_neFree_eq` would fail there; `⊥` and `⊤` are `p ∧ ¬p` and `p ∨ ¬p` for some
atom.

## TODO

Theorem 3.3.7 of Anttila's thesis proper, for the fragments without bilateral negation, and the
completeness of BSML with global disjunction and with the emptiness operator (Theorems 2.3.15 and
2.3.17 there); `Formula` has neither of these connectives.

## References

* [aloni-2022]
* [aloni-anttila-yang-2024]
* [anttila-2025]
* [anttila-knudstorp-2025]
* [knudstorp-2023]
-/

public section

namespace BSML

open Team ModalLogic

universe u

variable {Atom : Type*}

/-! ### Sets of types -/

section Types

variable [Inhabited Atom] {n k : ℕ} {e : Fin n → Atom} {W : Type*} [DecidableEq W]

private theorem support_disj_conj_ne_verum_iff (M : KripkeModel W Atom)
    (S : Finset (WorldType n k)) (t : Finset W) :
    support M (.disj (.conj (typeDisj e S) .ne) verum) t ↔
      ¬Disjoint (t.image (worldType e M k)) S := by
  rw [Finset.not_disjoint_iff]
  constructor
  · rintro ⟨t₁, ⟨h₁, x, hx⟩, t₂, -, rfl⟩
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_union_left _ hx),
      (support_typeDisj_iff M S t₁).1 h₁ (Finset.mem_image_of_mem _ hx)⟩
  · rintro ⟨_, ht, ha⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 ht
    exact ⟨{v}, ⟨(support_typeDisj_iff M S {v}).2 (by simpa using ha), Finset.singleton_nonempty v⟩,
      t, support_verum M t, Finset.union_eq_right.2 (Finset.singleton_subset_iff.2 hv)⟩

variable (e) in
/-- A convex union-closed property of sets of types is expressed by one formula across all models:
a team supports the formula exactly when its worlds' types form a set with the property. This is the
first proof of [anttila-2025] Theorem 3.3.5 (Lemmas 3.3.2, 3.2.10 and 3.3.3, assembled on p. 82) on
types in place of valuations, with one conjunct for each set of types meeting every set in `T` in
place of its tuples of valuations. -/
theorem exists_formula_iff_image_mem (T : Set (Finset (WorldType n k))) (hc : T.OrdConnected)
    (hs : SupClosed T) :
    ∃ φ : Formula Atom, ∀ {W : Type u} [DecidableEq W] (M : KripkeModel W Atom) (t : Finset W),
      support M φ t ↔ t.image (worldType e M k) ∈ T := by
  classical
  let U := T.toFinset.sup id
  let H := Finset.univ.filter fun S ↦ ∀ s ∈ T, ¬Disjoint s S
  refine ⟨.conj (typeDisj e U)
    (bigConj (H.toList.map fun S ↦ .disj (.conj (typeDisj e S) .ne) verum)), fun {W} _ M t ↦ ?_⟩
  simp only [support_conj, support_typeDisj_iff, support_bigConj_iff, List.forall_mem_map,
    Finset.mem_toList, support_disj_conj_ne_verum_iff]
  generalize t.image (worldType e M k) = σ
  refine ⟨fun ⟨hU, hH⟩ ↦ ?_, fun hσ ↦ ⟨Finset.le_sup (f := id) (Set.mem_toFinset.2 hσ),
    fun S hS ↦ (Finset.mem_filter.1 hS).2 σ hσ⟩⟩
  obtain ⟨s, hsT, hsσ⟩ : ∃ s ∈ T, Disjoint s σᶜ := by
    by_contra! h
    exact hH σᶜ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩) disjoint_compl_right
  exact hc.out hsT (hs.finsetSup_mem ⟨s, Set.mem_toFinset.2 hsT⟩ fun _ h ↦ Set.mem_toFinset.1 h)
    ⟨disjoint_compl_right_iff.1 hsσ, hU⟩

end Types

/-! ### Expressive completeness -/

section Completeness

/-- The class a formula expresses is invariant under bounded bisimulation, at the formula's modal
depth ([aloni-anttila-yang-2024] Theorem 3.8). -/
theorem boundedBisimInvariant_support (φ : Formula Atom) :
    BoundedBisimInvariant {p : PointedTeam.{u} Atom | support p.model φ p.team} :=
  ⟨φ.modalDepth, fun _ hp _ hb ↦ ((invariant_den φ le_rfl).1 hb).1 hp⟩

/-- **BSML is not expressively complete** for the union-closed classes invariant under bounded
bisimulation: the teams holding both a `p`-world and a `¬p`-world, with the empty team, are such a
class, but no convex one ([anttila-2025] Fact 2.3.19, p. 30). -/
theorem range_support_ssubset_supClosed [Nonempty Atom] :
    (Set.range fun φ : Formula Atom ↦ {p : PointedTeam.{u} Atom | support p.model φ p.team}) ⊂
      {P | Fiberwise (fun T ↦ SupClosed T) P ∧ BoundedBisimInvariant P} := by
  refine ⟨Set.range_subset_iff.2 fun φ ↦ ⟨fun M ↦ supClosed_support M φ,
    boundedBisimInvariant_support φ⟩, fun h ↦ ?_⟩
  inhabit Atom
  let ψ : Formula Atom := .disj (.conj (.atom default) .ne) (.conj (.neg (.atom default)) .ne)
  let Q : Set (PointedTeam.{u} Atom) :=
    {q | support q.model ψ q.team ∨ support q.model .falsum q.team}
  have hsup {W : Type u} [DecidableEq W] (M : KripkeModel W Atom) :
      SupClosed (PointedTeam.mk W M ⁻¹' Q) := by
    rintro s (hs | hs) t (ht | ht)
    · exact .inl (supClosed_support M ψ hs ht)
    · rw [(support_falsum M t).1 ht, Finset.sup_eq_union, Finset.union_empty]; exact .inl hs
    · rw [(support_falsum M s).1 hs, Finset.sup_eq_union, Finset.empty_union]; exact .inl ht
    · rw [(support_falsum M s).1 hs, (support_falsum M t).1 ht]
      exact .inr ((support_falsum M _).2 (Finset.union_empty _))
  have hinv : BoundedBisimInvariant Q := ⟨0, by
    rintro ⟨W, M, s⟩ (hs | hs) ⟨W', M', s'⟩ hb
    · exact .inl (((invariant_den ψ (by simp [ψ, Formula.modalDepth])).1 hb).1 hs)
    · exact .inr (((invariant_den .falsum (by simp [Formula.falsum, Formula.modalDepth])).1
        hb).1 hs)⟩
  obtain ⟨φ, hφ⟩ := h ⟨hsup, hinv⟩
  let M : KripkeModel (ULift.{u} Bool) Atom := ⟨fun _ ↦ ∅, fun _ w ↦ w.down = true⟩
  let a : ULift.{u} Bool := ⟨true⟩
  have hiff (t : Finset (ULift.{u} Bool)) : support M φ t ↔ t ∈ PointedTeam.mk _ M ⁻¹' Q :=
    Set.ext_iff.1 hφ (.mk _ M t)
  have hbot : (∅ : Finset (ULift.{u} Bool)) ∈ PointedTeam.mk _ M ⁻¹' Q :=
    .inr ((support_falsum M _).2 rfl)
  have htop : ({a, ⟨false⟩} : Finset (ULift.{u} Bool)) ∈ PointedTeam.mk _ M ⁻¹' Q :=
    .inl ⟨{a}, ⟨by simp [a, M, Team.flat, Formula.den], Finset.singleton_nonempty _⟩, {⟨false⟩},
      ⟨by simp [M, Team.flat, Formula.den], Finset.singleton_nonempty _⟩, rfl⟩
  rcases (hiff _).1 ((ordConnected_support M φ).out ((hiff _).2 hbot) ((hiff _).2 htop)
    (show _ ∈ Set.Icc _ _ from ⟨Finset.empty_subset {a}, by simp⟩)) with hmid | hmid
  · obtain ⟨_, _, u, ⟨hu, x, hx⟩, hsplit⟩ := hmid
    have hxa : x = a := Finset.mem_singleton.1 (le_sup_right.trans_eq hsplit hx)
    subst hxa
    exact hu _ hx rfl
  · exact Finset.singleton_ne_empty a ((support_falsum M _).1 hmid)

/-- Classical modal logic expresses strictly less than BSML ([anttila-2025] p. 25). -/
theorem range_support_neFree_ssubset :
    (Set.range fun φ : {φ : Formula Atom // φ.NEFree} ↦
        {p : PointedTeam.{u} Atom | support p.model φ.1 p.team}) ⊂
      (Set.range fun φ : Formula Atom ↦ {p : PointedTeam.{u} Atom | support p.model φ p.team}) := by
  refine ⟨fun _ ⟨φ, h⟩ ↦ ⟨φ.1, h⟩, fun h ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := h ⟨.ne, rfl⟩
  let M : KripkeModel PUnit.{u + 1} Atom := ⟨fun _ ↦ ∅, fun _ _ ↦ False⟩
  exact Finset.not_nonempty_empty
    ((Set.ext_iff.1 hφ ⟨PUnit, M, ∅⟩).1 (isFlat_support_of_neFree φ.2 M).empty_mem)

variable [Finite Atom] [Nonempty Atom]

/-- **BSML is expressively complete** for the convex, union-closed classes of pointed team models
invariant under bounded bisimulation: the remark after [anttila-2025] Theorem 3.3.7, p. 83, which
the conclusion of [aloni-anttila-yang-2024] reports as [knudstorp-2023]'s unpublished result. -/
theorem range_support_eq :
    (Set.range fun φ : Formula Atom ↦ {p : PointedTeam.{u} Atom | support p.model φ p.team}) =
      {P | Fiberwise (fun T ↦ T.OrdConnected ∧ SupClosed T) P ∧ BoundedBisimInvariant P} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun φ ↦
    ⟨fun M ↦ ⟨ordConnected_support M φ, supClosed_support M φ⟩,
      boundedBisimInvariant_support φ⟩) ?_
  rintro P ⟨hclosed, k, hk⟩
  inhabit Atom
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin Atom
  have he := e.symm.surjective
  obtain ⟨φ, hφ⟩ := exists_formula_iff_image_mem.{u} e.symm _
    (ordConnected_image_types he hk fun M ↦ (hclosed M).1)
    (supClosed_image_types he hk fun M ↦ (hclosed M).2)
  exact ⟨φ, Set.ext fun p ↦ (hφ p.model p.team).trans (mem_iff_types_mem_image he hk).symm⟩

/-- The `NE`-free fragment of BSML is expressively complete for the flat classes invariant under
bounded bisimulation ([aloni-anttila-yang-2024] Proposition 3.13; [anttila-2025] Proposition 2.3.13,
p. 27). -/
theorem range_support_neFree_eq :
    (Set.range fun φ : {φ : Formula Atom // φ.NEFree} ↦
        {p : PointedTeam.{u} Atom | support p.model φ.1 p.team}) =
      {P | Fiberwise (fun T ↦ IsFlat T) P ∧ BoundedBisimInvariant P} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun φ ↦
    ⟨fun M ↦ isFlat_support_of_neFree φ.2 M, boundedBisimInvariant_support φ.1⟩) ?_
  rintro P ⟨hflat, k, hk⟩
  inhabit Atom
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin Atom
  obtain ⟨L, hL⟩ := (Set.toFinite {σ : WorldType n k | ∃ p ∈ P, ∃ w, p.team = {w} ∧
    worldType e.symm p.model k w = σ}).exists_finset
  refine ⟨⟨typeDisj e.symm L, neFree_typeDisj L⟩, Set.ext fun p ↦ ?_⟩
  obtain ⟨W, M, t⟩ := p
  change support M (typeDisj e.symm L) t ↔ t ∈ PointedTeam.mk W M ⁻¹' P
  rw [support_typeDisj_iff, hflat M t, Finset.image_subset_iff]
  refine forall₂_congr fun v _ ↦ ⟨fun hv ↦ ?_, fun hv ↦ (hL _).2 ⟨⟨W, M, {v}⟩, hv, v, rfl, rfl⟩⟩
  obtain ⟨q, hq, w, hs₀, hw⟩ := (hL _).1 hv
  exact hk q hq ⟨W, M, {v}⟩ ((image_worldType_eq_iff_stateBisim e.symm.surjective).1
    (by simp [hs₀, hw]))

end Completeness

end BSML
