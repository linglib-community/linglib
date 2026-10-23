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

* `QBSML.diamond_split`: an enriched split disjunction supported on a modal pairing yields a
  non-empty world-set witness for each disjunct, the shared core.
* `QBSML.narrowScopeFC`, `QBSML.boxFC`, `QBSML.universalFC`: the free-choice facts, Facts 8,
  7 and 9.
* `QBSML.boxExiFC`: quantified box free choice, `[□∃x(α ∨ β)]⁺ ⊨ ◇∃xα ∧ ◇∃xβ`.
* `QBSML.ignorance`, `QBSML.distribution`, `QBSML.distributionEpi`, `QBSML.negationStrip`:
  Facts 3, 5, 6 and 10.

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

/-! ### The diamond split -/

private theorem poss_of_subset_modalLift {X : Finset W}
    {g : PartialAssign Var Domain} {t : Finset (Index W Var Domain)}
    (hα : α.NEFree) (ht : t ⊆ State.modalLift X g)
    (h : support M α.enrich t) :
    ∃ Y, Y ⊆ X ∧ Y.Nonempty ∧ support M α (State.modalLift Y g) :=
  ⟨State.worldProj t, State.worldProj_subset_of_subset_modalLift ht,
    State.worldProj_nonempty (nonempty_of_support_enrich h),
    (State.modalLift_worldProj_of_subset ht).symm ▸ support_of_support_enrich hα h⟩

theorem diamond_split {X : Finset W} {g : PartialAssign Var Domain}
    (hα : α.NEFree) (hβ : β.NEFree)
    (hsupp : support M (Formula.disj α β).enrich (State.modalLift X g)) :
    (∃ Y, Y ⊆ X ∧ Y.Nonempty ∧ support M α (State.modalLift Y g)) ∧
    (∃ Y, Y ⊆ X ∧ Y.Nonempty ∧ support M β (State.modalLift Y g)) := by
  obtain ⟨t₁, h₁, t₂, h₂, hsplit⟩ := hsupp.1
  exact ⟨poss_of_subset_modalLift M hα (le_sup_left.trans_eq hsplit) h₁,
    poss_of_subset_modalLift M hβ (le_sup_right.trans_eq hsplit) h₂⟩

private theorem possFC_on (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (.poss (Formula.disj α β).enrich) s) :
    support M (.poss α) s ∧ support M (.poss β) s := by
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · obtain ⟨X, hX, -, hsupp⟩ := h i hi
    exact (diamond_split M hα hβ hsupp).1.imp
      fun Y ⟨hYX, hYne, hY⟩ ↦ ⟨hYX.trans hX, hYne, hY⟩
  · obtain ⟨X, hX, -, hsupp⟩ := h i hi
    exact (diamond_split M hα hβ hsupp).2.imp
      fun Y ⟨hYX, hYne, hY⟩ ↦ ⟨hYX.trans hX, hYne, hY⟩

/-! ### Free choice (Facts 7, 8 and 9) -/

/-- Narrow-scope free choice (Fact 8) is `[◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β` for `NE`-free `α`, `β`. -/
theorem narrowScopeFC (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (Formula.enrich (.poss (.disj α β))) s) :
    support M (.poss α) s ∧ support M (.poss β) s :=
  possFC_on M hα hβ h.1

/-- Universal free choice (Fact 9) is `[∀x◇(α ∨ β)]⁺ ⊨ ∀x◇α ∧ ∀x◇β` for `NE`-free `α`, `β`.
It is Fact 8 at the universal extension `s[x]`. -/
theorem universalFC {x : Var} (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (Formula.enrich (.univ x (.poss (.disj α β)))) s) :
    support M (.univ x (.poss α)) s ∧ support M (.univ x (.poss β)) s :=
  possFC_on M hα hβ h.1.1

/-- Box free choice (Fact 7) is `[□(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β` for `NE`-free `α`, `β`, with the
derived `□`. The enriched premise puts the enriched disjunction on each index's full accessible
lift, where the diamond split produces the witnesses. -/
theorem boxFC (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (Formula.enrich (Formula.nec (.disj α β))) s) :
    support M (.poss α) s ∧ support M (.poss β) s := by
  rw [support_enrich_nec_iff] at h
  exact ⟨fun i hi ↦ (diamond_split M hα hβ (h.1 i hi)).1,
    fun i hi ↦ (diamond_split M hα hβ (h.1 i hi)).2⟩

/-! ### Quantified □-free choice

`[□∃x(α ∨ β)]⁺ ⊨ ◇∃xα ∧ ◇∃xβ` is the composite of Fact 7 with an existential under the
modal, the form Yan's Asher and Heim solutions invoke (see `Studies/Yan2023.lean`). -/

private theorem poss_exi_of_subset_extendFunctional
    {γ : Formula Var Const Pred} {X₀ : Finset W}
    {g : PartialAssign Var Domain} {x : Var}
    {hf : Index W Var Domain → Finset Domain}
    {t : Finset (Index W Var Domain)}
    (htsub : t ⊆ State.extendFunctional (State.modalLift X₀ g) x hf)
    (htne : t.Nonempty) (hsupp : support M γ t) :
    ∃ Y, Y ⊆ X₀ ∧ Y.Nonempty ∧
      support M (.exi x γ) (State.modalLift Y g) := by
  have hpar : ∀ j ∈ t, ∃ i ∈ State.modalLift (State.worldProj t) g,
      ∃ d, Index.update i x d = j := by
    intro j hj
    obtain ⟨i, hi, d, -, rfl⟩ := State.mem_extendFunctional.mp (htsub hj)
    refine ⟨i, State.mem_modalLift.mpr
      ⟨?_, (State.mem_modalLift.mp hi).2⟩, d, rfl⟩
    exact State.mem_worldProj.mpr ⟨i.update x d, hj, Index.world_update i x d⟩
  have hcov : ∀ i' ∈ State.modalLift (State.worldProj t) g,
      ∃ d, Index.update i' x d ∈ t := by
    intro i' hi'
    obtain ⟨hi'w, hi'g⟩ := State.mem_modalLift.mp hi'
    obtain ⟨j, hjt, hjw⟩ := State.mem_worldProj.mp hi'w
    obtain ⟨i, hi, d, -, rfl⟩ := State.mem_extendFunctional.mp (htsub hjt)
    have hii' : i' = i := by
      refine Prod.ext ?_ (hi'g.trans (State.mem_modalLift.mp hi).2.symm)
      show i'.world = i.world
      rw [← hjw, Index.world_update]
    exact ⟨d, hii' ▸ hjt⟩
  refine ⟨State.worldProj t, ?_, State.worldProj_nonempty htne,
    support_exi_of_update_closure M hpar hcov hsupp⟩
  intro w hw
  obtain ⟨j, hjt, rfl⟩ := State.mem_worldProj.mp hw
  obtain ⟨i, hi, d, -, rfl⟩ := State.mem_extendFunctional.mp (htsub hjt)
  rw [Index.world_update]
  exact (State.mem_modalLift.mp hi).1

theorem boxExiFC {x : Var} (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M
      (Formula.enrich (Formula.nec (.exi x (.disj α β)))) s) :
    support M (.poss (.exi x α)) s ∧ support M (.poss (.exi x β)) s := by
  rw [support_enrich_nec_iff] at h
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · obtain ⟨hf, -, hD⟩ := (h.1 i hi).1
    obtain ⟨t₁, h₁, t₂, -, hsplit⟩ := hD.1
    exact poss_exi_of_subset_extendFunctional M
      (le_sup_left.trans_eq hsplit)
      (nonempty_of_support_enrich h₁) (support_of_support_enrich hα h₁)
  · obtain ⟨hf, -, hD⟩ := (h.1 i hi).1
    obtain ⟨t₁, -, t₂, h₂, hsplit⟩ := hD.1
    exact poss_exi_of_subset_extendFunctional M
      (le_sup_right.trans_eq hsplit)
      (nonempty_of_support_enrich h₂) (support_of_support_enrich hβ h₂)

/-! ### Ignorance (Fact 3) -/

private theorem poss_predc_of_stateBased {P : Pred} {c : Const}
    {t : Finset (Index W Var Domain)} (hSB : IsStateBased M.access (State.worldProj s))
    (hts : t ⊆ s)
    (htne : t.Nonempty) (h : support M (.predc P c) t) :
    support M (.poss (.predc P c)) s := by
  intro i hi
  refine ⟨State.worldProj t, ?_, State.worldProj_nonempty htne, ?_⟩
  · rw [hSB i.world (State.mem_worldProj.mpr ⟨i, hi, rfl⟩)]
    exact State.worldProj_mono hts
  · intro k hk
    obtain ⟨hkw, -⟩ := State.mem_modalLift.mp hk
    obtain ⟨j, hj, hjw⟩ := State.mem_worldProj.mp hkw
    rw [← hjw]
    exact h j hj

/-- Ignorance (Fact 3) is `[Pc₁ ∨ Qc₂]⁺ ⊨ ◇Pc₁ ∧ ◇Qc₂` on a state-based `R`. It is stated
for constant atoms, as in the paper's `Pa ∨ Pb`, since the transplant argument needs
assignment-invariance and fails with a free variable in place of the constant. -/
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

/-! ### Negation behaviour (Fact 10) -/

/-- Negation behaviour (Fact 10) is `[¬(α ∨ β)]⁺ ⊨ ¬α ∧ ¬β` for `NE`-free `α`, `β`, in every
model. Stripping the outer `NE` leaves anti-support of the enriched disjuncts, which
enrichment strengthens to classical anti-support of each. -/
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
    support M (.exi x γ) {i} := by
  refine support_exi_of_update_closure M ?_ ?_ hsupp
  · intro j hj
    obtain ⟨d, i', hi', hupd⟩ := State.mem_extendUniversal.mp (htsub hj)
    exact ⟨i', hi', d, hupd⟩
  · intro i' hi'
    rw [Finset.mem_singleton] at hi'
    subst hi'
    obtain ⟨j₀, hj₀⟩ := htne
    obtain ⟨d, i'', hi'', hupd⟩ := State.mem_extendUniversal.mp (htsub hj₀)
    rw [Finset.mem_singleton] at hi''
    subst hi''
    exact ⟨d, by rwa [hupd]⟩

/-- Distribution at maximal information (Fact 5) is `[∀x(α ∨ β)]⁺ ⊨ ∃xα ∧ ∃xβ` for `NE`-free
`α`, `β` on a singleton state `{i}`. The enriched premise splits the universal extension of
`{i}` into non-empty parts, and each part extends the same index, so it is the image of a
functional extension witnessing the existential. -/
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
  obtain ⟨d, i₀, hi₀s, hupd⟩ := State.mem_extendUniversal.mp (htsub hj₀)
  obtain ⟨d', hassign, hmem⟩ := hsupp j₀ hj₀
  rw [← hupd] at hassign hmem
  simp only [Index.assign_update, Function.update_self,
    Flat.coe_inj] at hassign
  rw [← hassign] at hmem
  rw [Index.world_update] at hmem
  -- hmem : d ∈ M.relInterp₁ P i₀.world
  refine ⟨fun _ ↦ {d}, fun j _ ↦ Finset.singleton_nonempty d, ?_⟩
  intro j hj
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
      simp only [Index.assign_update, Function.update_self]
    · rw [hkw]
      exact hmem

/-- Epistemic distribution (Fact 6) is `[∀x(Px ∨ Qx)]⁺ ⊨ ∃x◇Px ∧ ∃x◇Qx` on a state-based
`R`. It is stated for atoms, as in the paper, since the proof evaluates the atom pointwise at
a single transplanted world. -/
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
