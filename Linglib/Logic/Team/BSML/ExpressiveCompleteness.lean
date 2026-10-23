module

public import Linglib.Logic.Team.BSML.Properties
public import Linglib.Logic.Team.BSML.Characteristic

/-!
# Expressive completeness for BSML

Anttila, with Knudstorp, proves that BSML is expressively complete for the convex, union-closed,
bounded-bisimulation-invariant team properties, a question Aloni, Anttila and Yang left open. In
the vocabulary of `Team/Definability.lean` this is `definableClass (support M) =
{P | P.OrdConnected ∧ SupClosed P ∧ BisimClosed M P}`. One inclusion collects the closure
properties of support; the other is proved within one model over finitely many atoms, from the
characteristic formulas of `Characteristic.lean`.

## Main results

* `bisimClosed_support`: support is closed under bounded bisimulation.
* `definableClass_support_subset`, `subset_definableClass_support`: the two inclusions.
* `definableClass_support_eq`: their equality.

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
* [anttila-2025] Anttila, Not Nothing: Nonemptiness in Team Semantics
* [anttila-knudstorp-2025] Anttila and Knudstorp, Convex Team Logics
-/

@[expose] public section

namespace BSML

open Team ModalLogic

variable {W : Type*} [DecidableEq W] {Atom : Type*}

/-! ### Bounded-bisimulation closure -/

/-- The support of a formula is closed under bisimulation at its modal depth. -/
theorem bisimClosed_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    BisimClosed M {t | support M φ t} :=
  ⟨φ.modalDepth, invariant_eval φ le_rfl true⟩

/-! ### Expressive completeness -/

/-- Every BSML-definable team property is convex, union-closed and
    bounded-bisimulation-closed ([anttila-2025] §3.3.2). -/
theorem definableClass_support_subset (M : KripkeModel W Atom) :
    definableClass (support M) ⊆ {P | P.OrdConnected ∧ SupClosed P ∧ BisimClosed M P} :=
  definableClass_subset fun φ ↦
    ⟨ordConnected_support M φ, supClosed_support M φ, bisimClosed_support M φ⟩

/-- Every convex, union-closed, bounded-bisimulation-closed team property is BSML-definable
    ([anttila-2025] Theorem 3.3.7 and the remark after it, p. 83, here within one model and over
    finitely many atoms).

    The defining formula conjoins an upper bound — the flat disjunction
    `δ_U` of the characteristic formulas of the union `U` of all teams of
    `P` — with, for every set `T` of worlds whose bisimilarity classes meet
    every team of `P`, the hitting disjunct `(δ_T ∧ NE) ∨ δ_U`. A
    supporting team `t` lies under `U` and meets every such transversal;
    the worlds not bisimilar into `t` therefore fail to be a transversal,
    which yields a team `s₀ ∈ P` whose classes `t` covers, and `s₀ ∪ (U`
    restricted to `t`'s classes`)` lies in `P` by convexity between `s₀`
    and `U` and is bisimilar to `t` — so `t ∈ P` by bisimulation closure. -/
theorem subset_definableClass_support [Fintype W] [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) :
    {P | P.OrdConnected ∧ SupClosed P ∧ BisimClosed M P} ⊆ definableClass (support M) := by
  classical
  rintro P ⟨hconv', hsup', k, hbisim⟩
  rw [mem_definableClass]
  rcases Set.eq_empty_or_nonempty P with rfl | hP
  · refine ⟨.strongFalsum, Eq.symm ?_⟩
    ext t
    exact iff_of_false (Set.notMem_empty t) (not_support_strongFalsum M t)
  · set PF : Finset (Finset W) := P.toFinset with hPF
    have hPFne : PF.Nonempty := Set.toFinset_nonempty.mpr hP
    set U : Finset W := PF.sup id with hUdef
    have hUP : U ∈ P :=
      hsup'.finsetSup_mem hPFne (fun s hs => Set.mem_toFinset.mp hs)
    have hsubU : ∀ s ∈ P, s ⊆ U :=
      fun s hs => Finset.le_sup (f := id) (Set.mem_toFinset.mpr hs)
    set 𝒯 : Finset (Finset W) := Finset.univ.filter
      (fun T => ∀ s ∈ PF, ∃ v ∈ s, ∃ w ∈ T, WorldBisim k M w M v) with h𝒯
    set e : Fin (Fintype.card Atom) → Atom := fun i ↦ (Fintype.equivFin Atom).symm i
    have he : Function.Surjective e := (Fintype.equivFin Atom).symm.surjective
    set δ : Finset W → Formula Atom :=
      fun S ↦ bigDisj ((S.toList.map (worldType e M k)).map (hintikka e k)) with hδdef
    have hδ : ∀ S t : Finset W, support M (δ S) t ↔ ∀ v ∈ t, ∃ w ∈ S, WorldBisim k M w M v :=
      fun S t ↦ by
        simp only [hδdef, support_bigDisj_hintikka_iff, List.mem_map, Finset.mem_toList]
        exact forall₂_congr fun v _ ↦ exists_congr fun w ↦
          and_congr_right fun _ ↦ worldType_eq_iff_worldBisim he k w v
    refine ⟨.conj (δ U)
      (bigConj (𝒯.toList.map (fun T => .disj (.conj (δ T) .ne) (δ U)))), Eq.symm ?_⟩
    ext t
    constructor
    · intro htP
      refine ⟨(hδ U t).mpr
        (fun v hv => ⟨v, hsubU t htP hv, WorldBisim.refl k M v⟩), ?_⟩
      refine (support_bigConj_iff M _ t).mpr (fun ψ hψ => ?_)
      obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hψ
      have hTtrans := (Finset.mem_filter.mp (Finset.mem_toList.mp hT)).2
      obtain ⟨v, hvt, w, hwT, hb⟩ := hTtrans t (Set.mem_toFinset.mpr htP)
      refine ⟨{v}, ⟨?_, Finset.singleton_nonempty v⟩, t, ?_, ?_⟩
      · refine (hδ T {v}).mpr (fun x hx => ?_)
        obtain rfl := Finset.mem_singleton.mp hx
        exact ⟨w, hwT, hb⟩
      · exact (hδ U t).mpr
          (fun x hx => ⟨x, hsubU t htP hx, WorldBisim.refl k M x⟩)
      · show {v} ∪ t = t
        exact Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr hvt)
    · rintro ⟨hupper, hhits⟩
      have hcov : ∀ v ∈ t, ∃ w ∈ U, WorldBisim k M w M v :=
        (hδ U t).mp hupper
      set T₀ : Finset W := Finset.univ.filter
        (fun w => ¬ ∃ v ∈ t, WorldBisim k M w M v) with hT₀def
      have hT₀notin : T₀ ∉ 𝒯 := by
        intro hmem
        have hhit := (support_bigConj_iff M _ t).mp hhits _
          (List.mem_map.mpr ⟨T₀, Finset.mem_toList.mpr hmem, rfl⟩)
        obtain ⟨t₁, ⟨hδ₁, hne₁⟩, t₂, -, hsplit⟩ := hhit
        obtain ⟨x, hx⟩ := hne₁
        obtain ⟨w, hwT₀, hb⟩ := (hδ T₀ t₁).mp hδ₁ x hx
        exact (Finset.mem_filter.mp hwT₀).2
          ⟨x, le_sup_left.trans_eq hsplit hx, hb⟩
      have hs₀ : ∃ s₀ ∈ PF, ∀ w ∈ s₀, ∃ v ∈ t, WorldBisim k M w M v := by
        by_contra hno
        refine hT₀notin (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun s hs => ?_⟩)
        by_contra hall
        refine hno ⟨s, hs, fun w hw => ?_⟩
        by_contra hwnc
        exact hall ⟨w, hw, w,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwnc⟩, WorldBisim.refl k M w⟩
      obtain ⟨s₀, hs₀PF, hs₀cov⟩ := hs₀
      have hs₀P : s₀ ∈ P := Set.mem_toFinset.mp hs₀PF
      set t'' : Finset W :=
        s₀ ∪ U.filter (fun w => ∃ v ∈ t, WorldBisim k M w M v) with ht''def
      have hbis : StateBisim k M t'' M t := by
        constructor
        · intro w hw
          rcases Finset.mem_union.mp hw with hw₀ | hwU
          · exact hs₀cov w hw₀
          · exact (Finset.mem_filter.mp hwU).2
        · intro v hv
          obtain ⟨w, hwU, hb⟩ := hcov v hv
          exact ⟨w, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwU, v, hv, hb⟩), hb⟩
      have ht''P : t'' ∈ P :=
        hconv'.out hs₀P hUP (Set.mem_Icc.mpr
          ⟨Finset.subset_union_left,
           Finset.union_subset (hsubU s₀ hs₀P) (Finset.filter_subset _ _)⟩)
      exact (hbisim hbis).mp ht''P

/-- **BSML is expressively complete** for the convex, union-closed,
    bounded-bisimulation-closed team properties ([anttila-2025] Theorem 3.3.7 and the remark
    after it, p. 83, in within-model finite-atom form). -/
theorem definableClass_support_eq [Fintype W] [Fintype Atom] [Inhabited Atom]
    (M : KripkeModel W Atom) :
    definableClass (support M) = {P | P.OrdConnected ∧ SupClosed P ∧ BisimClosed M P} :=
  (definableClass_support_subset M).antisymm (subset_definableClass_support M)

end BSML
