module

public import Linglib.Logic.Team.BSML.Classical
public import Linglib.Logic.Team.BSML.Negation
public import Linglib.Logic.Team.BSML.Properties

/-!
# Natural deduction for BSML

Aloni, Anttila and Yang axiomatize BSML by a natural deduction system: the rules BSML shares with
its extensions by the global disjunction `⩔` and the emptiness operator, and three
`⊥NE`-translation rules that simulate `⩔`, which BSML lacks. The system grows out of Anttila's
thesis. This file encodes it as `Derives` and proves it sound.

The `∨` rules are constrained because `NE` breaks downward closure: `∨I` introduces only `NE`-free
disjuncts, and the side derivations of `¬I`, `∨E` and `∨Mon` have `NE`-free undischarged
assumptions. The translation rules act on an occurrence `[ψ]` in the scope of no `¬` and no `◇`,
where `φ[ψ]` is equivalent to `φ[ψ ∧ NE/ψ] ⩔ φ[ψ ∧ ⊥/ψ]`.

## Main definitions

* `Formula.Context`: one-hole contexts whose hole is under no `¬` except inside `□`;
  `Formula.Context.Distributive` picks out those built from `∧` and `∨` alone.
* `Derives`: the system, written `Γ ⊢ φ`.

## Main results

* `Formula.Context.setOf_support_fill`: the split behind the translation rules.
* `soundness`; completeness is proved in `Completeness.lean`.
* `Derives.fill`: replacement in a context.
* `strongFalsum_derives`, `conj_disj_derives_disj_conj`, `disj_conj_ne_derives_conj_ne`,
  `poss_derives_poss_conj_ne`, `poss_disj_conj_ne_derives_conj_poss`: derivations from the
  papers, the last being free choice.
* `not_atom_derives_disj_ne`, `not_poss_disj_derives_conj_poss`: non-derivations, by soundness.

## Implementation notes

`⊥` is `Formula.falsum`, `p ∧ ¬p` for the default atom, as in Aloni's original syntax; the paper
takes `⊥` as primitive. Contexts are upper bounds on undischarged assumptions, so the
`NE`-freeness conditions on side derivations are conditions on their contexts. The paper chains
derivations freely, but substituting a derivation for an assumption of a side derivation can break
that side derivation's condition, so composition is the rule `cut`; weakening follows from it.
Result numbers and pages follow arXiv:2305.11777v3.

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
* [anttila-2021] Anttila, The Logic of Free Choice: Axiomatizations of State-based Modal Logics
-/

@[expose] public section

namespace BSML

open ModalLogic (KripkeModel)

open Team

variable {Atom : Type*} {W : Type*} [DecidableEq W]

/-! ### Contexts -/

/-- A one-hole context whose hole is in the scope of no `¬`, except as part of `□ = ¬◇¬`.
    These are the positions at which replacement holds ([aloni-anttila-yang-2024] Lemma 4.4). -/
inductive Formula.Context (Atom : Type*) where
  | hole
  | conjLeft (C : Context Atom) (ψ : Formula Atom)
  | conjRight (φ : Formula Atom) (C : Context Atom)
  | disjLeft (C : Context Atom) (ψ : Formula Atom)
  | disjRight (φ : Formula Atom) (C : Context Atom)
  | poss (C : Context Atom)
  | nec (C : Context Atom)

namespace Formula.Context

/-- `C.fill φ` is the formula `C` with `φ` in its hole. -/
def fill : Context Atom → Formula Atom → Formula Atom
  | hole, φ => φ
  | conjLeft C ψ, φ => .conj (C.fill φ) ψ
  | conjRight χ C, φ => .conj χ (C.fill φ)
  | disjLeft C ψ, φ => .disj (C.fill φ) ψ
  | disjRight χ C, φ => .disj χ (C.fill φ)
  | poss C, φ => .poss (C.fill φ)
  | nec C, φ => Formula.nec (C.fill φ)

/-- A context is distributive when its hole is under no modality, so that it is built from `∧`
    and `∨` alone. These are the `⩔`-distributive positions of [aloni-anttila-yang-2024] (p. 28). -/
def Distributive : Context Atom → Prop
  | hole => True
  | conjLeft C _ | conjRight _ C | disjLeft C _ | disjRight _ C => C.Distributive
  | poss _ | nec _ => False

/-- At a distributive position, `ψ` splits into `ψ ∧ NE` and `ψ ∧ ⊥`. The teams supporting
    `C.fill ψ` are those supporting `C.fill (ψ ∧ NE)` together with those supporting
    `C.fill (ψ ∧ ⊥)` ([aloni-anttila-yang-2024] p. 34). -/
theorem setOf_support_fill [Inhabited Atom] (M : KripkeModel W Atom) (ψ : Formula Atom) :
    ∀ {C : Context Atom}, C.Distributive →
      {s | support M (C.fill ψ) s} = {s | support M (C.fill (.conj ψ .ne)) s} ∪
        {s | support M (C.fill (.conj ψ .falsum)) s}
  | hole, _ => by
    ext s
    change _ ↔ (_ ∧ s.Nonempty) ∨ (_ ∧ support M .falsum s)
    rw [support_falsum, ← and_or_left, and_iff_left s.eq_empty_or_nonempty.symm]
    exact Iff.rfl
  | conjLeft C θ, hC => by
    change {s | _} ∩ {s | _} = ({s | _} ∩ {s | _}) ∪ ({s | _} ∩ {s | _})
    rw [setOf_support_fill M ψ (C := C) hC, Set.union_inter_distrib_right]
  | conjRight θ C, hC => by
    change {s | _} ∩ {s | _} = ({s | _} ∩ {s | _}) ∪ ({s | _} ∩ {s | _})
    rw [setOf_support_fill M ψ (C := C) hC, Set.inter_union_distrib_left]
  | disjLeft C θ, hC => by
    change tensor _ _ = tensor _ _ ∪ tensor _ _
    rw [setOf_support_fill M ψ (C := C) hC, tensor_eq_sups, tensor_eq_sups, tensor_eq_sups,
      Set.sups_union_left]
  | disjRight θ C, hC => by
    change tensor _ _ = tensor _ _ ∪ tensor _ _
    rw [setOf_support_fill M ψ (C := C) hC, tensor_eq_sups, tensor_eq_sups, tensor_eq_sups,
      Set.sups_union_right]
  | poss _, hC | nec _, hC => hC.elim

end Formula.Context

/-! ### The system -/

/-- The natural deduction system for BSML ([aloni-anttila-yang-2024] Definition 4.33) has the
    rules of Definition 4.1, boxes (a)–(f), and the three `⊥NE`-translation rules. `Derives Γ φ`
    says that `φ` is derivable from formulas in `Γ`, and `cut` composes derivations. -/
inductive Derives [Inhabited Atom] : Set (Formula Atom) → Formula Atom → Prop where
  /-- An assumption. -/
  | hyp {Γ φ} : φ ∈ Γ → Derives Γ φ
  /-- Composition of derivations. -/
  | cut {Γ Δ φ ψ} : Derives Γ φ → Derives (insert φ Δ) ψ → Derives (Γ ∪ Δ) ψ
  /-- `∧I`. -/
  | conjI {Γ₁ Γ₂ φ ψ} : Derives Γ₁ φ → Derives Γ₂ ψ → Derives (Γ₁ ∪ Γ₂) (.conj φ ψ)
  /-- `∧E`, left. -/
  | conjE₁ {Γ φ ψ} : Derives Γ (.conj φ ψ) → Derives Γ φ
  /-- `∧E`, right. -/
  | conjE₂ {Γ φ ψ} : Derives Γ (.conj φ ψ) → Derives Γ ψ
  /-- `¬I`, for classical `α` and `NE`-free undischarged assumptions. -/
  | negI {Γ α} : α.NEFree → (∀ γ ∈ Γ, Formula.NEFree γ) →
      Derives (insert α Γ) .falsum → Derives Γ (.neg α)
  /-- `¬E`, ex falso for classical formulas. -/
  | negE {Γ₁ Γ₂ α β} : α.NEFree → β.NEFree →
      Derives Γ₁ α → Derives Γ₂ (.neg α) → Derives (Γ₁ ∪ Γ₂) β
  /-- `¬¬E`, downward. -/
  | dneE {Γ φ} : Derives Γ (.neg (.neg φ)) → Derives Γ φ
  /-- `¬¬E`, upward. -/
  | dneI {Γ φ} : Derives Γ φ → Derives Γ (.neg (.neg φ))
  /-- `DM∧`, downward. -/
  | dmConjE {Γ φ ψ} : Derives Γ (.neg (.conj φ ψ)) → Derives Γ (.disj (.neg φ) (.neg ψ))
  /-- `DM∧`, upward. -/
  | dmConjI {Γ φ ψ} : Derives Γ (.disj (.neg φ) (.neg ψ)) → Derives Γ (.neg (.conj φ ψ))
  /-- `DM∨`, downward. -/
  | dmDisjE {Γ φ ψ} : Derives Γ (.neg (.disj φ ψ)) → Derives Γ (.conj (.neg φ) (.neg ψ))
  /-- `DM∨`, upward. -/
  | dmDisjI {Γ φ ψ} : Derives Γ (.conj (.neg φ) (.neg ψ)) → Derives Γ (.neg (.disj φ ψ))
  /-- `¬NEE`, downward. -/
  | negNeE {Γ} : Derives Γ (.neg .ne) → Derives Γ .falsum
  /-- `¬NEE`, upward. -/
  | negNeI {Γ} : Derives Γ .falsum → Derives Γ (.neg .ne)
  /-- `∨I`, for an `NE`-free introduced disjunct. -/
  | disjI {Γ φ ψ} : ψ.NEFree → Derives Γ φ → Derives Γ (.disj φ ψ)
  /-- `∨W`. -/
  | disjW {Γ φ} : Derives Γ φ → Derives Γ (.disj φ φ)
  /-- `Com∨`. -/
  | disjCom {Γ φ ψ} : Derives Γ (.disj φ ψ) → Derives Γ (.disj ψ φ)
  /-- `Ass∨`. -/
  | disjAss {Γ φ ψ χ} : Derives Γ (.disj φ (.disj ψ χ)) → Derives Γ (.disj (.disj φ ψ) χ)
  /-- `∨E`, for `NE`-free undischarged assumptions in the side derivations. -/
  | disjE {Γ Δ₁ Δ₂ φ ψ χ} : (∀ γ ∈ Δ₁, Formula.NEFree γ) → (∀ γ ∈ Δ₂, Formula.NEFree γ) →
      Derives Γ (.disj φ ψ) → Derives (insert φ Δ₁) χ → Derives (insert ψ Δ₂) χ →
      Derives (Γ ∪ Δ₁ ∪ Δ₂) χ
  /-- `∨Mon`, for `NE`-free undischarged assumptions in the side derivation. -/
  | disjMon {Γ Δ φ ψ χ} : (∀ γ ∈ Δ, Formula.NEFree γ) →
      Derives Γ (.disj φ ψ) → Derives (insert ψ Δ) χ → Derives (Γ ∪ Δ) (.disj φ χ)
  /-- `⊥E`. -/
  | falsumE {Γ φ} : Derives Γ (.disj .falsum φ) → Derives Γ φ
  /-- `⊥⊥Ctr`. -/
  | strongFalsumCtr {Γ φ} (ψ) : Derives Γ (.disj .strongFalsum φ) → Derives Γ ψ
  /-- `◇Mon`, for a side derivation from `φ` alone. -/
  | possMon {Γ φ ψ} : Derives {φ} ψ → Derives Γ (.poss φ) → Derives Γ (.poss ψ)
  /-- `□Mon`, for a side derivation from the boxed formulas alone. -/
  | necMon {Γ ψ} (φs : List (Formula Atom)) :
      Derives {δ | δ ∈ φs} ψ → (∀ δ ∈ φs, Derives Γ (Formula.nec δ)) →
      Derives Γ (Formula.nec ψ)
  /-- `Inter◇□`, downward. -/
  | interE {Γ φ} : Derives Γ (.neg (.poss φ)) → Derives Γ (Formula.nec (.neg φ))
  /-- `Inter◇□`, upward. -/
  | interI {Γ φ} : Derives Γ (Formula.nec (.neg φ)) → Derives Γ (.neg (.poss φ))
  /-- `◇Sep`. -/
  | possSep {Γ φ ψ} : Derives Γ (.poss (.disj φ (.conj ψ .ne))) → Derives Γ (.poss ψ)
  /-- `◇Join`. -/
  | possJoin {Γ₁ Γ₂ φ ψ} : Derives Γ₁ (.poss φ) → Derives Γ₂ (.poss ψ) →
      Derives (Γ₁ ∪ Γ₂) (.poss (.disj φ ψ))
  /-- `□Inst`. -/
  | necInst {Γ φ} : Derives Γ (Formula.nec (.conj φ .ne)) → Derives Γ (.poss φ)
  /-- `□◇Join`. -/
  | necPossJoin {Γ₁ Γ₂ φ ψ} : Derives Γ₁ (Formula.nec φ) → Derives Γ₂ (.poss ψ) →
      Derives (Γ₁ ∪ Γ₂) (Formula.nec (.disj φ ψ))
  /-- `⊥NETrs`. -/
  | neTrs {Γ Δ₁ Δ₂ ψ χ} (C : Formula.Context Atom) : C.Distributive →
      Derives Γ (C.fill ψ) → Derives (insert (C.fill (.conj ψ .ne)) Δ₁) χ →
      Derives (insert (C.fill (.conj ψ .falsum)) Δ₂) χ → Derives (Γ ∪ Δ₁ ∪ Δ₂) χ
  /-- `◇⊥NETrs`. -/
  | possNeTrs {Γ ψ} (C : Formula.Context Atom) : C.Distributive →
      Derives Γ (.poss (C.fill ψ)) →
      Derives Γ (.disj (.poss (C.fill (.conj ψ .ne))) (.poss (C.fill (.conj ψ .falsum))))
  /-- `□⊥NETrs`. -/
  | necNeTrs {Γ ψ} (C : Formula.Context Atom) : C.Distributive →
      Derives Γ (Formula.nec (C.fill ψ)) →
      Derives Γ (.disj (Formula.nec (C.fill (.conj ψ .ne)))
        (Formula.nec (C.fill (.conj ψ .falsum))))

@[inherit_doc] scoped infix:50 " ⊢ " => Derives

variable [Inhabited Atom] {Γ Δ : Set (Formula Atom)} {φ ψ χ : Formula Atom}

/-! ### Soundness -/

/-- **Soundness** ([aloni-anttila-yang-2024] Theorem 4.34). Every team supporting the premises
    supports what they derive. -/
theorem soundness (h : Γ ⊢ φ) (M : KripkeModel W Atom) :
    ∀ s : Finset W, (∀ γ ∈ Γ, support M γ s) → support M φ s := by
  induction h with
  | hyp hφ => exact fun s hΓ ↦ hΓ _ hφ
  | cut _ _ ih₁ ih₂ =>
    intro s hΓ
    refine ih₂ s fun γ hγ ↦ ?_
    rcases hγ with rfl | hγ
    exacts [ih₁ s fun γ hγ ↦ hΓ γ (.inl hγ), hΓ γ (.inr hγ)]
  | conjI _ _ ih₁ ih₂ =>
    exact fun s hΓ ↦ ⟨ih₁ s fun γ hγ ↦ hΓ γ (.inl hγ), ih₂ s fun γ hγ ↦ hΓ γ (.inr hγ)⟩
  | conjE₁ _ ih => exact fun s hΓ ↦ (ih s hΓ).1
  | conjE₂ _ ih => exact fun s hΓ ↦ (ih s hΓ).2
  | @negI Γ α hα hΓ _ ih =>
    intro s hs
    refine (antiSupport_iff_forall_not_realize hα).mpr fun w hw hr ↦ ?_
    refine Finset.singleton_ne_empty w ((support_falsum M _).mp (ih {w} ?_))
    rintro γ (rfl | hγ)
    · exact (support_singleton_iff_realize hα).mpr hr
    · exact isLowerSet_support_of_neFree (hΓ γ hγ) M (Finset.singleton_subset_iff.mpr hw)
        (hs γ hγ)
  | negE _ hβ _ _ ih₁ ih₂ =>
    intro s hΓ
    rw [eq_empty_of_support_of_antiSupport (ih₁ s fun γ hγ ↦ hΓ γ (.inl hγ))
      (ih₂ s fun γ hγ ↦ hΓ γ (.inr hγ))]
    exact support_empty_of_neFree hβ M
  | dneE _ ih | dneI _ ih | dmConjE _ ih | dmConjI _ ih | dmDisjE _ ih | dmDisjI _ ih
  | interE _ ih | interI _ ih => exact ih
  | negNeE _ ih => exact fun s hΓ ↦ (support_falsum M s).mpr (ih s hΓ)
  | negNeI _ ih => exact fun s hΓ ↦ (support_falsum M s).mp (ih s hΓ)
  | disjI hψ _ ih => exact fun s hΓ ↦ ⟨s, ih s hΓ, ∅, support_empty_of_neFree hψ M, by simp⟩
  | disjW _ ih => exact fun s hΓ ↦ ⟨s, ih s hΓ, s, ih s hΓ, by simp⟩
  | disjCom _ ih =>
    intro s hΓ
    obtain ⟨t₁, h₁, t₂, h₂, rfl⟩ := ih s hΓ
    exact ⟨t₂, h₂, t₁, h₁, Finset.union_comm _ _⟩
  | disjAss _ ih =>
    intro s hΓ
    obtain ⟨t₁, h₁, _, ⟨t₂, h₂, t₃, h₃, rfl⟩, rfl⟩ := ih s hΓ
    exact ⟨t₁ ∪ t₂, ⟨t₁, h₁, t₂, h₂, rfl⟩, t₃, h₃, Finset.union_assoc _ _ _⟩
  | @disjE Γ Δ₁ Δ₂ φ ψ χ hΔ₁ hΔ₂ _ _ _ ihmaj ih₁ ih₂ =>
    intro s hΓ
    obtain ⟨t₁, hφ, t₂, hψ, rfl⟩ := ihmaj _ fun γ hγ ↦ hΓ γ (.inl (.inl hγ))
    refine supClosed_support M χ (ih₁ t₁ ?_) (ih₂ t₂ ?_)
    · rintro γ (rfl | hγ)
      · exact hφ
      · exact isLowerSet_support_of_neFree (hΔ₁ γ hγ) M Finset.subset_union_left
          (hΓ γ (.inl (.inr hγ)))
    · rintro γ (rfl | hγ)
      · exact hψ
      · exact isLowerSet_support_of_neFree (hΔ₂ γ hγ) M Finset.subset_union_right
          (hΓ γ (.inr hγ))
  | @disjMon Γ Δ φ ψ χ hΔ _ _ ihmaj ih =>
    intro s hΓ
    obtain ⟨t₁, hφ, t₂, hψ, rfl⟩ := ihmaj _ fun γ hγ ↦ hΓ γ (.inl hγ)
    refine ⟨t₁, hφ, t₂, ih t₂ ?_, rfl⟩
    rintro γ (rfl | hγ)
    · exact hψ
    · exact isLowerSet_support_of_neFree (hΔ γ hγ) M Finset.subset_union_right (hΓ γ (.inr hγ))
  | falsumE _ ih =>
    intro s hΓ
    obtain ⟨t₁, h₁, t₂, h₂, rfl⟩ := ih s hΓ
    rwa [(support_falsum M t₁).mp h₁, Finset.empty_union]
  | strongFalsumCtr _ _ ih =>
    intro s hΓ
    obtain ⟨t₁, h₁, -⟩ := ih s hΓ
    exact absurd h₁ (not_support_strongFalsum M t₁)
  | possMon _ _ ihD ihPoss =>
    intro s hΓ w hw
    obtain ⟨t, hsub, hne, hφ⟩ := ihPoss s hΓ w hw
    exact ⟨t, hsub, hne, ihD t fun γ hγ ↦ hγ ▸ hφ⟩
  | necMon _ _ _ ihD ihboxes => exact fun s hΓ w hw ↦ ihD _ fun δ hδ ↦ ihboxes δ hδ s hΓ w hw
  | possSep _ ih =>
    intro s hΓ w hw
    obtain ⟨t, hsub, _, t₁, -, t₂, ⟨hψ, hne⟩, rfl⟩ := ih s hΓ w hw
    exact ⟨t₂, Finset.subset_union_right.trans hsub, hne, hψ⟩
  | possJoin _ _ ih₁ ih₂ =>
    intro s hΓ w hw
    obtain ⟨t₁, hsub₁, hne₁, hφ⟩ := ih₁ s (fun γ hγ ↦ hΓ γ (.inl hγ)) w hw
    obtain ⟨t₂, hsub₂, -, hψ⟩ := ih₂ s (fun γ hγ ↦ hΓ γ (.inr hγ)) w hw
    exact ⟨t₁ ∪ t₂, Finset.union_subset hsub₁ hsub₂, hne₁.mono Finset.subset_union_left,
      t₁, hφ, t₂, hψ, rfl⟩
  | necInst _ ih =>
    intro s hΓ w hw
    obtain ⟨hφ, hne⟩ := ih s hΓ w hw
    exact ⟨M.access w, subset_rfl, hne, hφ⟩
  | necPossJoin _ _ ih₁ ih₂ =>
    intro s hΓ w hw
    obtain ⟨t, hsub, -, hψ⟩ := ih₂ s (fun γ hγ ↦ hΓ γ (.inr hγ)) w hw
    exact ⟨M.access w, ih₁ s (fun γ hγ ↦ hΓ γ (.inl hγ)) w hw, t, hψ,
      Finset.union_eq_left.mpr hsub⟩
  | @neTrs Γ Δ₁ Δ₂ ψ χ C hC _ _ _ ih ih₁ ih₂ =>
    intro s hΓ
    have h : s ∈ {s | support M (C.fill ψ) s} := ih s fun γ hγ ↦ hΓ γ (.inl (.inl hγ))
    rw [Formula.Context.setOf_support_fill M ψ hC] at h
    rcases h with h | h
    · exact ih₁ s <| by rintro γ (rfl | hγ); exacts [h, hΓ γ (.inl (.inr hγ))]
    · exact ih₂ s <| by rintro γ (rfl | hγ); exacts [h, hΓ γ (.inr hγ)]
  | @possNeTrs Γ ψ C hC _ ih =>
    intro s hΓ
    have h : s ∈ poss M.access {t | support M (C.fill ψ) t} := ih s hΓ
    rwa [Formula.Context.setOf_support_fill M ψ hC, poss_union] at h
  | @necNeTrs Γ ψ C hC _ ih =>
    intro s hΓ
    have h : s ∈ nec M.access {t | support M (C.fill ψ) t} := ih s hΓ
    rwa [Formula.Context.setOf_support_fill M ψ hC, nec_union] at h

theorem consequence_of_derives (h : {φ} ⊢ ψ) : Consequence (W := W) φ ψ :=
  fun M t ht ↦ soundness h M t fun _ hγ ↦ hγ ▸ ht

/-! ### Derived rules -/

/-- A formula derives itself. -/
theorem Derives.single (φ : Formula Atom) : {φ} ⊢ φ := .hyp rfl

theorem Derives.mono (hΓΔ : Γ ⊆ Δ) (h : Γ ⊢ φ) : Δ ⊢ φ :=
  Set.union_eq_self_of_subset_left hΓΔ ▸ h.cut (.hyp (Set.mem_insert φ Δ))

theorem Derives.cut' (h₁ : Γ ⊢ φ) (h₂ : insert φ Γ ⊢ ψ) : Γ ⊢ ψ :=
  Set.union_self Γ ▸ h₁.cut h₂

/-- Derivations compose with a derivation from a single premise. -/
theorem Derives.trans (h₁ : Γ ⊢ φ) (h₂ : {φ} ⊢ ψ) : Γ ⊢ ψ :=
  h₁.cut' (h₂.mono (by simp))

/-- `∧I` applies within one set of premises. -/
theorem Derives.conj (h₁ : Γ ⊢ φ) (h₂ : Γ ⊢ ψ) : Γ ⊢ .conj φ ψ :=
  Set.union_self Γ ▸ h₁.conjI h₂

theorem Derives.possMon' (h₁ : Γ ⊢ .poss φ) (h₂ : {φ} ⊢ ψ) : Γ ⊢ .poss ψ := .possMon h₂ h₁

theorem Derives.disjMon' (h₁ : Γ ⊢ .disj φ ψ) (h₂ : {ψ} ⊢ χ) : Γ ⊢ .disj φ χ := by
  simpa using h₁.disjMon (Δ := ∅) (by simp) (by simpa using h₂)

/-- **Replacement** ([aloni-anttila-yang-2024] Lemma 4.4). A derivation of `ψ` from `φ` carries
    over to any context in which the hole is under no `¬` except as part of `□`. -/
theorem Derives.fill (h : {φ} ⊢ ψ) : ∀ C : Formula.Context Atom, {C.fill φ} ⊢ C.fill ψ
  | .hole => h
  | .conjLeft C θ =>
    have h₀ := Derives.single (.conj (C.fill φ) θ)
    (h₀.conjE₁.trans (h.fill C)).conj h₀.conjE₂
  | .conjRight θ C =>
    have h₀ := Derives.single (.conj θ (C.fill φ))
    h₀.conjE₁.conj (h₀.conjE₂.trans (h.fill C))
  | .disjLeft C θ => ((Derives.single (.disj (C.fill φ) θ)).disjCom.disjMon' (h.fill C)).disjCom
  | .disjRight θ C => (Derives.single (.disj θ (C.fill φ))).disjMon' (h.fill C)
  | .poss C => .possMon (h.fill C) (.single _)
  | .nec C => .necMon [C.fill φ] (by simpa using h.fill C) (by simpa using .single _)

/-! ### Derivations from the papers -/

/-- The strong contradiction derives everything ([aloni-anttila-yang-2024] Lemma 4.2). -/
theorem strongFalsum_derives (φ : Formula Atom) : {.strongFalsum} ⊢ φ :=
  .strongFalsumCtr φ (.disjI Formula.neFree_falsum (.single _))

theorem derives_neg_falsum : (∅ : Set (Formula Atom)) ⊢ .neg .falsum :=
  .negI Formula.neFree_falsum (by simp) (.hyp (Set.mem_insert _ _))

/-- Conjunction with an `NE`-free formula distributes over `∨`
    ([aloni-anttila-yang-2024] Proposition 4.6 (i)). Each disjunct needs `φ`, which only `cut`
    can supply without putting the premise into a side derivation. -/
theorem conj_disj_derives_disj_conj (hφ : φ.NEFree) :
    {.conj φ (.disj ψ χ)} ⊢ .disj (.conj φ ψ) (.conj φ χ) := by
  have hφ' : ∀ γ ∈ ({φ} : Set (Formula Atom)), γ.NEFree := by rintro _ rfl; exact hφ
  have hψ : insert ψ {φ} ⊢ .conj φ ψ :=
    ((Derives.single φ).mono (by simp)).conj ((Derives.single ψ).mono (by simp))
  have hχ : insert χ {φ} ⊢ .conj φ χ :=
    ((Derives.single φ).mono (by simp)).conj ((Derives.single χ).mono (by simp))
  have h₁ := ((Derives.single (.disj ψ χ)).disjMon hφ' hχ).disjCom.disjMon hφ' hψ
  have h₀ := Derives.single (.conj φ (.disj ψ χ))
  refine h₀.conjE₁.cut' (((h₀.conjE₂.mono (by simp)).cut' (h₁.disjCom.mono ?_)))
  intro x; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]; tauto

/-- A disjunction with an `NE`-conjunct is nonempty ([aloni-anttila-yang-2024] Lemma 4.17).
    The paper derives it with `⩔`; here `⊥NETrs` on the hole splits the premise, and its
    `⊥`-branch closes by `⊥⊥Ctr`. -/
theorem disj_conj_ne_derives_conj_ne :
    {.disj φ (.conj ψ .ne)} ⊢ .conj (.disj φ (.conj ψ .ne)) .ne := by
  set θ : Formula Atom := .disj φ (.conj ψ .ne)
  have hstrong : {.conj .falsum (.conj ψ .ne)} ⊢ .strongFalsum :=
    have h₀ := Derives.single (Formula.conj .falsum (.conj ψ .ne))
    h₀.conjE₁.conj h₀.conjE₂.conjE₂
  have hfalsum : {.conj θ .falsum} ⊢ .conj θ .ne :=
    have h₀ := Derives.single (Formula.conj θ .falsum)
    .strongFalsumCtr _ ((h₀.conjE₂.conj h₀.conjE₁).trans
      (conj_disj_derives_disj_conj Formula.neFree_falsum) |>.disjMon' hstrong |>.disjCom)
  simpa using Derives.neTrs (Δ₁ := ∅) (Δ₂ := ∅) (ψ := θ) (χ := .conj θ .ne) .hole trivial
    (.single θ) (.hyp (Set.mem_insert _ _)) (by simpa [Formula.Context.fill] using hfalsum)

/-- A possibility has a nonempty witness ([aloni-anttila-yang-2024] Lemma 4.21). `◇⊥NETrs`
    splits `◇φ` into `◇(φ ∧ NE) ∨ ◇(φ ∧ ⊥)`, and `◇⊥` refutes itself. -/
theorem poss_derives_poss_conj_ne : {.poss φ} ⊢ .poss (.conj φ .ne) := by
  have hsplit : {.poss φ} ⊢ .disj (.poss (.conj φ .ne)) (.poss (.conj φ .falsum)) :=
    .possNeTrs (ψ := φ) .hole trivial (.single _)
  have hneg : {.poss (.conj φ .falsum)} ⊢ .neg (.poss .falsum) :=
    .interI (.necMon [] (by simpa using derives_neg_falsum) (by simp))
  have hfalsum : {.poss (.conj φ .falsum)} ⊢ .falsum := by
    have h := (Derives.single (Formula.poss (.conj φ .falsum))).possMon'
      (Derives.single (Formula.conj φ .falsum)).conjE₂
    simpa using h.negE (α := .poss .falsum) Formula.neFree_falsum Formula.neFree_falsum hneg
  exact (hsplit.disjMon' hfalsum).disjCom.falsumE

/-- **Free choice** ([anttila-2021] Proposition 4.2.5, p. 71). A possibility of a disjunction
    of nonempty disjuncts yields both possibilities, by `◇Sep` once directly and once after
    `Com∨`. -/
theorem poss_disj_conj_ne_derives_conj_poss :
    {.poss (.disj (.conj φ .ne) (.conj ψ .ne))} ⊢ .conj (.poss φ) (.poss ψ) :=
  have h₀ := Derives.single (Formula.disj (.conj φ .ne) (.conj ψ .ne))
  have h₁ := Derives.single (Formula.poss (.disj (.conj φ .ne) (.conj ψ .ne)))
  (Derives.possSep (h₁.possMon' h₀.disjCom)).conj (.possSep h₁)

/-! ### Non-derivations -/

/-- Unrestricted `∨I` would be unsound, since `p ⊬ p ∨ NE`. The empty team supports `p` but not
    `p ∨ NE` ([aloni-anttila-yang-2024] p. 19). -/
theorem not_atom_derives_disj_ne (p : Atom) : ¬ {.atom p} ⊢ .disj (.atom p) .ne := by
  intro hd
  let M : KripkeModel Unit Atom := ⟨fun _ ↦ ∅, fun _ _ ↦ true⟩
  obtain ⟨t₁, -, t₂, hne, h⟩ := soundness hd M ∅ fun γ hγ ↦ hγ ▸ empty_supports_atom M p
  exact hne.ne_empty (Finset.union_eq_empty.mp h).2

/-- Free choice fails without enrichment, `◇(p ∨ q) ⊬ ◇p ∧ ◇q` for distinct atoms. A world that
    sees only a `q`-world is a zero-model of `◇(p ∨ q)`, the empty team witnessing `p`, but does
    not support `◇p`, as at the world `w_∅` of the state `s_b` in [aloni-anttila-yang-2024]
    Figure 3(b) (pp. 6–7). -/
theorem not_poss_disj_derives_conj_poss {p q : Atom} (hpq : p ≠ q) :
    ¬ {.poss (.disj (.atom p) (.atom q))} ⊢ .conj (.poss (.atom p)) (.poss (.atom q)) := by
  intro hd
  let M : KripkeModel Unit Atom := ⟨fun _ ↦ {()}, fun r _ ↦ r = q⟩
  have h := soundness hd M {()} fun γ hγ ↦ hγ ▸ fun _ _ ↦
    ⟨{()}, subset_rfl, Finset.singleton_nonempty _, ∅, empty_supports_atom M p, {()},
      fun _ _ ↦ by simp [M], by simp⟩
  obtain ⟨s, hs, ⟨⟨⟩, hu⟩, hp⟩ := h.1 () (Finset.mem_singleton_self _)
  exact hpq (by simpa [M] using hp () hu)

end BSML
