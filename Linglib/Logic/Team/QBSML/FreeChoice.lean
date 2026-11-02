module

public import Linglib.Logic.Team.QBSML.Enrichment
public import Linglib.Logic.Team.QBSML.Properties

/-!
# Free choice in QBSML

This file proves the free-choice, ignorance, distribution and negation facts of QBSML for
arbitrary models. Each fact is a support consequence whose premise is a pragmatically enriched
formula: an enriched split disjunction under a modal or a quantifier needs a non-empty witness
for each disjunct, and the witness is transplanted into a `◇` or `∃` claim. Aloni and van
Ormondt state the facts for the numerals `three ∨ more` of their modified-numeral puzzles;
here they are stated for `NE`-free `α`, `β` where the proof allows, and for atoms where it
does not.

## Main results

* `QBSML.witnesses_of_enrich_disj`: an enriched split disjunction yields a non-empty substate
  supporting each disjunct, the shared core.
* `QBSML.narrowScopeFC`, `QBSML.boxFC`, `QBSML.universalFC`: the free-choice facts, Facts 8,
  7 and 9.
* `QBSML.boxExiFC`: quantified box free choice, `[□∃x(α ∨ β)]⁺ ⊨ ◇∃xα ∧ ◇∃xβ`.
* `QBSML.ignorance`, `QBSML.distribution`, `QBSML.distributionEpi`, `QBSML.negationStrip`:
  Facts 3, 5, 6 and 10.
* `QBSML.ignorance_of_assign_eq`: Fact 3 for any `NE`-free disjuncts on a state whose indices share
  one assignment.

## Implementation notes

Facts 3 and 6 need a state-based accessibility relation; the others hold in every model. Fact
4, obviation, is a countermodel claim and lives with its model in
`Studies/AloniVanOrmondt2023.lean`. `□` is the derived `¬◇¬`, so Fact 7 and the quantified
composite go through `support_enrich_nec_iff` rather than the paper's primitive `□` clause.
Universal free choice is the pattern Chemla attested experimentally, and the quantified
composite is the shape behind Yan's Asher and Heim solutions.

## References

* [aloni-vanormondt-2023] Aloni and van Ormondt, Modified Numerals and Split Disjunction: The
  First-Order Case
* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [chemla-2009b] Chemla, Universal implicatures and free choice effects: Experimental data
* [yan-2023] Yan, Monotonicity in Intensional Contexts: Weakening and Pragmatic Effects under
  Modals and Attitudes
-/

@[expose] public section

namespace QBSML

open Team

variable {W Var Domain Const Pred : Type*}
variable [DecidableEq W]
variable [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]
variable (M : Model W Domain Const Pred)
variable {α β : Formula Var Const Pred} {s : Finset (Index W Var Domain)}

/-! ### The split witnesses -/

/-- An enriched split disjunction yields a non-empty substate supporting each disjunct. This is the
shared core of the free-choice facts. -/
theorem witnesses_of_enrich_disj {u : Finset (Index W Var Domain)} (hα : α.NEFree)
    (hβ : β.NEFree) (h : support M (Formula.disj α β).enrich u) :
    (∃ t ⊆ u, t.Nonempty ∧ support M α t) ∧ ∃ t ⊆ u, t.Nonempty ∧ support M β t :=
  have ⟨t₁, h₁, t₂, h₂, hu⟩ := h.1
  ⟨⟨t₁, le_sup_left.trans_eq hu, nonempty_of_support_enrich h₁,
      support_of_support_enrich hα h₁⟩,
    ⟨t₂, le_sup_right.trans_eq hu, nonempty_of_support_enrich h₂,
      support_of_support_enrich hβ h₂⟩⟩

private theorem possFC_on (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (.poss (Formula.disj α β).enrich) s) :
    support M (.poss α) s ∧ support M (.poss β) s :=
  ⟨fun i hi ↦
    have ⟨_, hu, _, h'⟩ := h i hi
    (witnesses_of_enrich_disj M hα hβ h').1.imp fun _ ⟨ht, hne, h₁⟩ ↦ ⟨ht.trans hu, hne, h₁⟩,
   fun i hi ↦
    have ⟨_, hu, _, h'⟩ := h i hi
    (witnesses_of_enrich_disj M hα hβ h').2.imp fun _ ⟨ht, hne, h₂⟩ ↦ ⟨ht.trans hu, hne, h₂⟩⟩

/-! ### Free choice (Facts 7, 8 and 9) -/

/-- Narrow-scope free choice (Fact 8) is `[◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β` for `NE`-free `α`, `β`. -/
theorem narrowScopeFC (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (Formula.enrich (.poss (.disj α β))) s) :
    support M (.poss α) s ∧ support M (.poss β) s :=
  possFC_on M hα hβ h.1

/-- Universal free choice `[∀x◇(α ∨ β)]⁺ ⊨ ∀x◇α ∧ ∀x◇β` holds for `NE`-free `α`, `β` (Fact 9, via
Fact 8). -/
theorem universalFC {x : Var} (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (Formula.enrich (.univ x (.poss (.disj α β)))) s) :
    support M (.univ x (.poss α)) s ∧ support M (.univ x (.poss β)) s :=
  possFC_on M hα hβ h.1.1

/-- Box free choice `[□(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β` holds for `NE`-free `α`, `β` (Fact 7). -/
theorem boxFC (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (Formula.enrich (Formula.nec (.disj α β))) s) :
    support M (.poss α) s ∧ support M (.poss β) s := by
  rw [support_enrich_nec_iff] at h
  exact ⟨fun i hi ↦ (witnesses_of_enrich_disj M hα hβ (h.1 i hi)).1,
    fun i hi ↦ (witnesses_of_enrich_disj M hα hβ (h.1 i hi)).2⟩

/-! ### Quantified □-free choice

`[□∃x(α ∨ β)]⁺ ⊨ ◇∃xα ∧ ◇∃xβ` is the composite of Fact 7 with an existential under the
modal, the form Yan's Asher and Heim solutions invoke (see `Studies/Yan2023.lean`). -/

/-- A non-empty state supporting `γ` inside the universal extension `u[x]` yields a non-empty
substate of `u` supporting `∃xγ`: the indices of `u` with an `x`-variant in it. -/
private theorem exists_support_exi_of_subset_extendUniversal {γ : Formula Var Const Pred} {x : Var}
    {u t : Finset (Index W Var Domain)} (htu : t ⊆ State.extendUniversal u x) (htne : t.Nonempty)
    (h : support M γ t) : ∃ v ⊆ u, v.Nonempty ∧ support M (.exi x γ) v := by
  classical
  refine ⟨u.filter fun i ↦ ∃ j ∈ t, j ∈ i.variants x, Finset.filter_subset _ _, ?_,
    t, fun j hj ↦ ?_, fun i hi ↦ (Finset.mem_filter.mp hi).2, h⟩
  · obtain ⟨j, hj⟩ := htne
    obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp (htu hj)
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, j, hj, hji⟩⟩
  · obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp (htu hj)
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, j, hj, hji⟩, hji⟩

/-- Quantified box free choice is `[□∃x(α ∨ β)]⁺ ⊨ ◇∃xα ∧ ◇∃xβ` for `NE`-free `α`, `β`.
The enriched premise puts the enriched split disjunction on a state inside the universal extension
of each index's successors, and each non-empty half yields a `◇∃x` witness. -/
theorem boxExiFC {x : Var} (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M
      (Formula.enrich (Formula.nec (.exi x (.disj α β)))) s) :
    support M (.poss (.exi x α)) s ∧ support M (.poss (.exi x β)) s := by
  rw [support_enrich_nec_iff] at h
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · obtain ⟨S, hS, -, hD⟩ := (h.1 i hi).1
    obtain ⟨t, htS, htne, ht⟩ := (witnesses_of_enrich_disj M hα hβ hD).1
    exact exists_support_exi_of_subset_extendUniversal M (htS.trans hS) htne ht
  · obtain ⟨S, hS, -, hD⟩ := (h.1 i hi).1
    obtain ⟨t, htS, htne, ht⟩ := (witnesses_of_enrich_disj M hα hβ hD).2
    exact exists_support_exi_of_subset_extendUniversal M (htS.trans hS) htne ht

/-! ### Ignorance (Fact 3) -/

private theorem poss_predc_of_stateBased {P : Pred} {c : Const}
    {t : Finset (Index W Var Domain)} (hSB : IsStateBased M.access (State.worldProj s))
    (hts : t ⊆ s)
    (htne : t.Nonempty) (h : support M (.predc P c) t) :
    support M (.poss (.predc P c)) s := by
  refine support_poss_iff.mpr fun i hi ↦ ?_
  refine ⟨State.worldProj t, ?_, State.worldProj_nonempty htne, ?_⟩
  · rw [hSB i.world (State.mem_worldProj.mpr ⟨i, hi, rfl⟩)]
    exact State.worldProj_mono hts
  · intro k hk
    obtain ⟨hkw, -⟩ := State.mem_modalLift.mp hk
    obtain ⟨j, hj, hjw⟩ := State.mem_worldProj.mp hkw
    rw [← hjw]
    exact h j hj

/-- Ignorance `[Pc₁ ∨ Qc₂]⁺ ⊨ ◇Pc₁ ∧ ◇Qc₂` holds for constant atoms on a state-based `R` (Fact 3).
-/
theorem ignorance {P Q : Pred} {c₁ c₂ : Const} (hSB : IsStateBased M.access (State.worldProj s))
    (h : support M
      (Formula.enrich (.disj (.predc P c₁) (.predc Q c₂))) s) :
    support M (.poss (.predc P c₁)) s ∧
    support M (.poss (.predc Q c₂)) s := by
  obtain ⟨t₁, h₁, t₂, h₂, hsplit⟩ := h.1
  exact ⟨poss_predc_of_stateBased M hSB (le_sup_left.trans_eq hsplit)
      h₁.2 h₁.1,
    poss_predc_of_stateBased M hSB (le_sup_right.trans_eq hsplit)
      h₂.2 h₂.1⟩

private theorem poss_of_subset_of_assign_eq {γ : Formula Var Const Pred}
    {g : PartialAssign Var Domain} {t : Finset (Index W Var Domain)}
    (hSB : IsStateBased M.access (State.worldProj s)) (hg : ∀ i ∈ s, i.assign = g) (hts : t ⊆ s)
    (htne : t.Nonempty) (h : support M γ t) : support M (.poss γ) s :=
  support_poss_iff.mpr fun i hi ↦
    ⟨State.worldProj t, hSB i.world (State.mem_worldProj.mpr ⟨i, hi, rfl⟩) ▸
      State.worldProj_mono hts, State.worldProj_nonempty htne, by
        rwa [State.modalLift_worldProj_of_subset fun j hj ↦ State.mem_modalLift.mpr
          ⟨State.mem_worldProj.mpr ⟨j, hts hj, rfl⟩, (hg j (hts hj)).trans (hg i hi).symm⟩]⟩

/-- Ignorance `[α ∨ β]⁺ ⊨ ◇α ∧ ◇β` holds for `NE`-free `α`, `β` on a state-based `R` when the
indices of the state share one assignment, the generalisation of Fact 3 to arbitrary disjuncts. -/
theorem ignorance_of_assign_eq {g : PartialAssign Var Domain} (hα : α.NEFree) (hβ : β.NEFree)
    (hSB : IsStateBased M.access (State.worldProj s)) (hg : ∀ i ∈ s, i.assign = g)
    (h : support M (Formula.disj α β).enrich s) :
    support M (.poss α) s ∧ support M (.poss β) s :=
  have ⟨⟨_, ht₁, hne₁, h₁⟩, _, ht₂, hne₂, h₂⟩ := witnesses_of_enrich_disj M hα hβ h
  ⟨poss_of_subset_of_assign_eq M hSB hg ht₁ hne₁ h₁,
    poss_of_subset_of_assign_eq M hSB hg ht₂ hne₂ h₂⟩

/-! ### Negation behaviour (Fact 10) -/

/-- Negation `[¬(α ∨ β)]⁺ ⊨ ¬α ∧ ¬β` holds for `NE`-free `α`, `β` in every model (Fact 10). -/
theorem negationStrip (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (Formula.enrich (.neg (.disj α β))) s) :
    support M (.neg α) s ∧ support M (.neg β) s := by
  have hDisj : antiSupport M (.disj α.enrich β.enrich) s := (antiSupport_conj_ne M _ s).mp h.1
  exact ⟨antiSupport_of_antiSupport_enrich hα hDisj.1,
    antiSupport_of_antiSupport_enrich hβ hDisj.2⟩

/-! ### Distribution (Facts 5 and 6) -/

private theorem exi_of_subset_extendUniversal_singleton
    {γ : Formula Var Const Pred}
    {i : Index W Var Domain} {x : Var} {t : Finset (Index W Var Domain)}
    (htsub : t ⊆ State.extendUniversal {i} x) (htne : t.Nonempty)
    (hsupp : support M γ t) :
    support M (.exi x γ) {i} :=
  have ⟨_, hv, hne, h⟩ := exists_support_exi_of_subset_extendUniversal M htsub htne hsupp
  (hne.subset_singleton_iff.mp hv) ▸ h

/-- Distribution `[∀x(α ∨ β)]⁺ ⊨ ∃xα ∧ ∃xβ` holds for `NE`-free `α`, `β` on a singleton state (Fact
5). -/
theorem distribution {x : Var} {i : Index W Var Domain}
    (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (Formula.enrich (.univ x (.disj α β))) {i}) :
    support M (.exi x α) {i} ∧ support M (.exi x β) {i} := by
  obtain ⟨t₁, h₁, t₂, h₂, hsplit⟩ := h.1.1
  exact ⟨exi_of_subset_extendUniversal_singleton M
      (le_sup_left.trans_eq hsplit)
      (nonempty_of_support_enrich h₁) (support_of_support_enrich hα h₁),
    exi_of_subset_extendUniversal_singleton M (le_sup_right.trans_eq hsplit)
      (nonempty_of_support_enrich h₂) (support_of_support_enrich hβ h₂)⟩

private theorem exi_poss_atom_of_subset_extendUniversal
    {P : Pred} {x : Var} {t : Finset (Index W Var Domain)}
    (hSB : IsStateBased M.access (State.worldProj s))
    (htsub : t ⊆ State.extendUniversal s x) (htne : t.Nonempty)
    (hsupp : support M (.pred P x) t) :
    support M (.exi x (.poss (.pred P x))) s := by
  obtain ⟨j₀, hj₀⟩ := htne
  obtain ⟨i₀, hi₀s, d, hupd⟩ := State.mem_extendUniversal.mp (htsub hj₀)
  obtain ⟨d', hassign, hmem⟩ := hsupp j₀ hj₀
  rw [← hupd] at hassign hmem
  simp only [Index.assign_update, PartialAssign.update_self, Flat.coe_inj] at hassign
  rw [← hassign] at hmem
  rw [Index.world_update] at hmem
  -- hmem : d ∈ M.relInterp₁ P i₀.world
  refine support_exi_iff.mpr ⟨fun _ ↦ {d}, fun j _ ↦ Finset.singleton_nonempty d,
    support_poss_iff.mpr fun j hj ↦ ?_⟩
  obtain ⟨i, his, d'', hd'', hupd'⟩ := State.mem_extendFunctional.mp hj
  rw [Finset.mem_singleton] at hd''
  subst hd''
  refine ⟨{i₀.world}, ?_, Finset.singleton_nonempty _, ?_⟩
  · intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    have hjw : j.world ∈ State.worldProj s :=
      State.mem_worldProj.mpr ⟨i, his, by rw [← hupd', Index.world_update]⟩
    rw [hSB j.world hjw]
    exact State.mem_worldProj.mpr ⟨i₀, hi₀s, rfl⟩
  · intro k hk
    obtain ⟨hkw, hka⟩ := State.mem_modalLift.mp hk
    rw [Finset.mem_singleton] at hkw
    refine ⟨d'', ?_, ?_⟩
    · rw [hka, ← hupd']
      simp only [Index.assign_update, PartialAssign.update_self]
    · rw [hkw]
      exact hmem

/-- Epistemic distribution `[∀x(Px ∨ Qx)]⁺ ⊨ ∃x◇Px ∧ ∃x◇Qx` holds for atoms on a state-based `R`
(Fact 6). -/
theorem distributionEpi {P Q : Pred} {x : Var} (hSB : IsStateBased M.access (State.worldProj s))
    (h : support M
      (Formula.enrich (.univ x (.disj (.pred P x) (.pred Q x)))) s) :
    support M (.exi x (.poss (.pred P x))) s ∧
    support M (.exi x (.poss (.pred Q x))) s := by
  obtain ⟨t₁, h₁, t₂, h₂, hsplit⟩ := h.1.1
  exact ⟨exi_poss_atom_of_subset_extendUniversal M hSB
      (le_sup_left.trans_eq hsplit)
      (nonempty_of_support_enrich h₁) h₁.1,
    exi_poss_atom_of_subset_extendUniversal M hSB
      (le_sup_right.trans_eq hsplit)
      (nonempty_of_support_enrich h₂) h₂.1⟩

end QBSML
