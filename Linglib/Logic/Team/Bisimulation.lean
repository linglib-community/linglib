module

public import Linglib.Logic.Team.Kripke
public import Linglib.Logic.Team.Operations
public import Linglib.Logic.Team.Atoms
public import Linglib.Core.Data.Set.Functor

/-!
# Bisimulation for modal team logics

Two teams are related by the lifting `Set.LiftRel r` of a relation `r` on points when every
point of each team is `r`-related to a point of the other. Team properties `P` and `P'` are
invariant under `r` when teams related in this way agree on them. Every connective of
`Team/Operations.lean` preserves invariance, the modalities one step down a chain of relations,
so a team logic whose evaluation is a fold over these connectives is invariant under bounded
bisimulation of Kripke models.

## Main definitions

* `Team.Invariant r P P'`: teams related by the lifting of `r` agree on `P` and `P'`.
* `ModalLogic.WorldBisim k M w M' w'`: `k`-bisimilarity of pointed Kripke models.
* `ModalLogic.StateBisim k M s M' s'`: its lifting to teams.
* `ModalLogic.BisimClosed M P`: closure of a team property of `M` under bounded bisimulation.

## Main results

* `Team.invariant_flat`, `Team.Invariant.inter`, `Team.Invariant.union`,
  `Team.Invariant.tensor`, `Team.invariant_dep`, `Team.invariant_incl`: the non-modal
  connectives and atoms preserve invariance.
* `Team.Invariant.poss`, `Team.Invariant.nec`, `Team.Invariant.possWitness`,
  `Team.Invariant.possLax`, `Team.Invariant.necImage`: the modalities preserve invariance one
  step down.
* `Set.LiftRel.exists_finset_union_eq`: the lifting transports splits of a team.

## Implementation notes

[aloni-anttila-yang-2024] relativize bisimilarity to a finite set of atoms. Here it compares
every atom of the atom type, which is the paper's notion when that type is the finite set.

## References

* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
* [anttila-haggblom-yang-2025] Anttila, Häggblom and Yang, Axiomatizing modal inclusion logic
  and its variants
* [vaananen-2008] Väänänen, Modal Dependence Logic
-/

@[expose] public section

open scoped Relator

namespace Team

variable {α β : Type*} {r r₁ : α → β → Prop} {p : α → Prop} {p' : β → Prop}
  {P Q : TeamProperty α} {P' Q' : TeamProperty β}

/-- Team properties `P` and `P'` are invariant under a relation `r` on points when teams related
    by the lifting `Set.LiftRel r` agree on them. -/
def Invariant (r : α → β → Prop) (P : TeamProperty α) (P' : TeamProperty β) : Prop :=
  ∀ ⦃s : Finset α⦄ ⦃s' : Finset β⦄, Set.LiftRel r ↑s ↑s' → (s ∈ P ↔ s' ∈ P')

/-! ### Non-modal connectives and atoms -/

theorem invariant_flat (hp : (r ⇒ Iff) p p') : Invariant r (flat p) (flat p') :=
  fun _ _ hs ↦ ⟨fun h b hb ↦ let ⟨a, ha, hab⟩ := hs.2 b hb; (hp hab).1 (h a ha),
    fun h a ha ↦ let ⟨b, hb, hab⟩ := hs.1 a ha; (hp hab).2 (h b hb)⟩

theorem invariant_ne : Invariant r (ne : TeamProperty α) (ne : TeamProperty β) :=
  fun _ _ hs ↦ by simpa using hs.nonempty_iff

theorem invariant_singleton_empty : Invariant r ({∅} : TeamProperty α) ({∅} : TeamProperty β) :=
  fun _ _ hs ↦ by simpa using hs.eq_empty_iff

theorem invariant_univ : Invariant r (Set.univ : TeamProperty α) (Set.univ : TeamProperty β) :=
  fun _ _ _ ↦ Iff.rfl

theorem Invariant.inter (h₁ : Invariant r P P') (h₂ : Invariant r Q Q') :
    Invariant r (P ∩ Q) (P' ∩ Q') :=
  fun _ _ hs ↦ and_congr (h₁ hs) (h₂ hs)

theorem Invariant.union (h₁ : Invariant r P P') (h₂ : Invariant r Q Q') :
    Invariant r (P ∪ Q) (P' ∪ Q') :=
  fun _ _ hs ↦ or_congr (h₁ hs) (h₂ hs)

theorem invariant_dep {γ δ : Type*} {f : α → γ} {f' : β → γ} {g : α → δ} {g' : β → δ}
    (hf : (r ⇒ Eq) f f') (hg : (r ⇒ Eq) g g') :
    Invariant r ((↑) ⁻¹' dep f g) ((↑) ⁻¹' dep f' g') := by
  intro s s' hs
  simp only [Set.mem_preimage, mem_dep]
  constructor
  · intro h b₁ hb₁ b₂ hb₂ hfb
    obtain ⟨a₁, ha₁, h₁⟩ := hs.2 b₁ hb₁
    obtain ⟨a₂, ha₂, h₂⟩ := hs.2 b₂ hb₂
    rw [← hg h₁, ← hg h₂]
    exact h a₁ ha₁ a₂ ha₂ (by rw [hf h₁, hf h₂, hfb])
  · intro h a₁ ha₁ a₂ ha₂ hfa
    obtain ⟨b₁, hb₁, h₁⟩ := hs.1 a₁ ha₁
    obtain ⟨b₂, hb₂, h₂⟩ := hs.1 a₂ ha₂
    rw [hg h₁, hg h₂]
    exact h b₁ hb₁ b₂ hb₂ (by rw [← hf h₁, ← hf h₂, hfa])

theorem invariant_incl {γ : Type*} {f g : α → γ} {f' g' : β → γ} (hf : (r ⇒ Eq) f f')
    (hg : (r ⇒ Eq) g g') : Invariant r ((↑) ⁻¹' incl f g) ((↑) ⁻¹' incl f' g') := by
  intro s s' hs
  simp only [Set.mem_preimage, mem_incl]
  constructor
  · intro h b₁ hb₁
    obtain ⟨a₁, ha₁, h₁⟩ := hs.2 b₁ hb₁
    obtain ⟨a₂, ha₂, hfa⟩ := h a₁ ha₁
    obtain ⟨b₂, hb₂, h₂⟩ := hs.1 a₂ ha₂
    exact ⟨b₂, hb₂, by rw [← hf h₁, ← hg h₂, hfa]⟩
  · intro h a₁ ha₁
    obtain ⟨b₁, hb₁, h₁⟩ := hs.1 a₁ ha₁
    obtain ⟨b₂, hb₂, hfb⟩ := h b₁ hb₁
    obtain ⟨a₂, ha₂, h₂⟩ := hs.2 b₂ hb₂
    exact ⟨a₂, ha₂, by rw [hf h₁, hg h₂, hfb]⟩

/-- Invariant properties agree on the singleton teams of related points. -/
theorem Invariant.singleton (h : Invariant r P P') :
    (r ⇒ Iff) (fun a ↦ {a} ∈ P) fun b ↦ {b} ∈ P' :=
  fun _ _ hab ↦ h (by simpa using hab)

/-! ### Flat modalities

The modalities take an invariance under `r` to an invariance under `r₁`, given that
`r₁`-related points have successor sets related by the lifting of `r`. For Kripke models `r₁`
is bisimilarity at depth `k + 1` and `r` at depth `k`
([aloni-anttila-yang-2024] Lemma 3.7(i)). -/

variable {R : α → Finset α} {R' : β → Finset β}

/-- A sub-team of a team related by the lifting of `r` has a related sub-team on the other
    side. -/
theorem _root_.Set.LiftRel.exists_finset_subset {s t : Finset α} {s' : Finset β}
    (hs : Set.LiftRel r ↑s ↑s') (ht : t ⊆ s) : ∃ t' ⊆ s', Set.LiftRel r ↑t ↑t' := by
  classical
  refine ⟨s'.filter fun b ↦ ∃ a ∈ t, r a b, Finset.filter_subset _ _, fun a ha ↦ ?_,
    fun b hb ↦ (Finset.mem_filter.1 hb).2⟩
  obtain ⟨b, hb, hab⟩ := hs.1 a (ht ha)
  exact ⟨b, Finset.mem_filter.2 ⟨hb, a, ha, hab⟩, hab⟩

theorem Invariant.nec (hR : ∀ a b, r₁ a b → Set.LiftRel r ↑(R a) ↑(R' b))
    (h : Invariant r P P') : Invariant r₁ (nec R P) (nec R' P') :=
  invariant_flat fun _ _ hab ↦ h (hR _ _ hab)

theorem Invariant.poss (hR : ∀ a b, r₁ a b → Set.LiftRel r ↑(R a) ↑(R' b))
    (h : Invariant r P P') : Invariant r₁ (poss R P) (poss R' P') := by
  refine invariant_flat fun a b hab ↦ ⟨?_, ?_⟩
  · rintro ⟨t, ht, htne, htP⟩
    obtain ⟨t', ht', htt'⟩ := (hR a b hab).exists_finset_subset ht
    exact ⟨t', ht', Finset.coe_nonempty.1 (htt'.nonempty_iff.1 htne), (h htt').1 htP⟩
  · rintro ⟨t', ht', htne, htP⟩
    obtain ⟨t, ht, htt'⟩ := (Set.liftRel_swap.2 (hR a b hab)).exists_finset_subset ht'
    rw [Set.liftRel_swap] at htt'
    exact ⟨t, ht, Finset.coe_nonempty.1 (htt'.nonempty_iff.2 htne), (h htt').2 htP⟩

variable [DecidableEq α] [DecidableEq β]

/-! ### Splits -/

/-- A split of a team related by the lifting of `r` has a related split on the other side
    ([aloni-anttila-yang-2024] Lemma 3.7(ii)). -/
theorem _root_.Set.LiftRel.exists_finset_union_eq {s t u : Finset α} {s' : Finset β}
    (hs : Set.LiftRel r ↑s ↑s') (hsplit : t ∪ u = s) :
    ∃ t' u' : Finset β, t' ∪ u' = s' ∧ Set.LiftRel r ↑t ↑t' ∧ Set.LiftRel r ↑u ↑u' := by
  classical
  subst hsplit
  have key (v : Finset α) (hv : v ⊆ t ∪ u) :
      Set.LiftRel r ↑v ↑(s'.filter fun b ↦ ∃ a ∈ v, r a b) :=
    ⟨fun a ha ↦ (hs.1 a (hv ha)).imp fun b ⟨hb, hab⟩ ↦ ⟨Finset.mem_filter.2 ⟨hb, a, ha, hab⟩, hab⟩,
      fun b hb ↦ (Finset.mem_filter.1 hb).2⟩
  refine ⟨_, _, ?_, key t Finset.subset_union_left, key u Finset.subset_union_right⟩
  refine (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)).antisymm
    fun b hb ↦ ?_
  obtain ⟨a, ha, hab⟩ := hs.2 b hb
  exact Finset.mem_union.2 <| (Finset.mem_union.1 ha).imp
    (fun h ↦ Finset.mem_filter.2 ⟨hb, a, h, hab⟩) fun h ↦ Finset.mem_filter.2 ⟨hb, a, h, hab⟩

theorem Invariant.tensor (h₁ : Invariant r P P') (h₂ : Invariant r Q Q') :
    Invariant r (tensor P Q) (tensor P' Q') := by
  intro s s' hs
  constructor
  · rintro ⟨t, ht, u, hu, rfl⟩
    obtain ⟨t', u', hsplit, htt', huu'⟩ := hs.exists_finset_union_eq rfl
    exact ⟨t', (h₁ htt').1 ht, u', (h₂ huu').1 hu, hsplit⟩
  · rintro ⟨t', ht', u', hu', rfl⟩
    obtain ⟨t, u, hsplit, htt', huu'⟩ := (Set.liftRel_swap.2 hs).exists_finset_union_eq rfl
    rw [Set.liftRel_swap] at htt' huu'
    exact ⟨t, (h₁ htt').2 ht', u, (h₂ huu').2 hu', hsplit⟩

/-! ### Image modalities of dependence and inclusion logic -/

theorem Invariant.necImage (hR : ∀ a b, r₁ a b → Set.LiftRel r ↑(R a) ↑(R' b))
    (h : Invariant r P P') : Invariant r₁ (necImage R P) (necImage R' P') := fun _ _ hs ↦
  h (by simp only [biUnionHom_apply, Finset.coe_biUnion]; exact hs.biUnion fun a _ b _ ↦ hR a b)

/-- A team `Y` meeting the successor set of each point of `s` has a counterpart meeting the
    successor set of each point of a related `s'`, related to the part of `Y` reachable
    from `s`. -/
private theorem exists_liftRel_witness (hR : ∀ a b, r₁ a b → Set.LiftRel r ↑(R a) ↑(R' b))
    {s : Finset α} {s' : Finset β} (hs : Set.LiftRel r₁ ↑s ↑s') {Y : Finset α}
    (hY : ∀ a ∈ s, ∃ y ∈ Y, y ∈ R a) :
    ∃ Y' ⊆ s'.biUnion R', (∀ b ∈ s', ∃ y' ∈ Y', y' ∈ R' b) ∧
      Set.LiftRel r ↑(Y ∩ s.biUnion R) ↑Y' := by
  classical
  refine ⟨(s'.biUnion R').filter fun y' ↦ ∃ y ∈ Y ∩ s.biUnion R, r y y', Finset.filter_subset _ _,
    fun b hb ↦ ?_, fun y hy ↦ ?_, fun y' hy' ↦ (Finset.mem_filter.1 hy').2⟩
  · obtain ⟨a, ha, hab⟩ := hs.2 b hb
    obtain ⟨y, hyY, hya⟩ := hY a ha
    obtain ⟨y', hy'b, hyy'⟩ := (hR a b hab).1 y hya
    exact ⟨y', Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨b, hb, hy'b⟩, y,
      Finset.mem_inter.2 ⟨hyY, Finset.mem_biUnion.2 ⟨a, ha, hya⟩⟩, hyy'⟩, hy'b⟩
  · obtain ⟨a, ha, hya⟩ := Finset.mem_biUnion.1 (Finset.mem_inter.1 hy).2
    obtain ⟨b, hb, hab⟩ := hs.1 a ha
    obtain ⟨y', hy'b, hyy'⟩ := (hR a b hab).1 y hya
    exact ⟨y', Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨b, hb, hy'b⟩, y, hy, hyy'⟩, hyy'⟩

/-- The single-witness possibility modality preserves invariance between downward-closed
    properties. -/
theorem Invariant.possWitness (hR : ∀ a b, r₁ a b → Set.LiftRel r ↑(R a) ↑(R' b))
    (hP : IsLowerSet P) (hP' : IsLowerSet P') (h : Invariant r P P') :
    Invariant r₁ (possWitness R P) (possWitness R' P') := by
  intro s s' hs
  constructor
  · rintro ⟨Y, hY, hYP⟩
    obtain ⟨Y', -, hY', hYY'⟩ := exists_liftRel_witness hR hs hY
    exact ⟨Y', hY', (h hYY').1 (hP Finset.inter_subset_left hYP)⟩
  · rintro ⟨Y', hY', hYP⟩
    obtain ⟨Y, -, hY, hYY'⟩ := exists_liftRel_witness
      (fun b a hba ↦ Set.liftRel_swap.2 (hR a b hba)) (Set.liftRel_swap.2 hs) hY'
    rw [Set.liftRel_swap] at hYY'
    exact ⟨Y, hY, (h hYY').2 (hP' Finset.inter_subset_left hYP)⟩

theorem Invariant.possLax (hR : ∀ a b, r₁ a b → Set.LiftRel r ↑(R a) ↑(R' b))
    (h : Invariant r P P') : Invariant r₁ (possLax R P) (possLax R' P') := by
  intro s s' hs
  constructor
  · rintro ⟨S, hS, hwit, hSP⟩
    obtain ⟨S', hS', hwit', hSS'⟩ := exists_liftRel_witness hR hs hwit
    rw [Finset.inter_eq_left.2 hS] at hSS'
    exact ⟨S', hS', hwit', (h hSS').1 hSP⟩
  · rintro ⟨S', hS', hwit', hSP⟩
    obtain ⟨S, hS, hwit, hSS'⟩ := exists_liftRel_witness
      (fun b a hba ↦ Set.liftRel_swap.2 (hR a b hba)) (Set.liftRel_swap.2 hs) hwit'
    rw [Finset.inter_eq_left.2 hS', Set.liftRel_swap] at hSS'
    exact ⟨S, hS, hwit, (h hSS').2 hSP⟩

end Team

namespace ModalLogic

variable {W W' Atom : Type*}

/-! ### Bisimulation of Kripke models -/

/-- Pointed Kripke models are `k`-bisimilar ([aloni-anttila-yang-2024] Definition 3.1) when they
    agree on every atom and, at positive depth, their successor sets are related by the lifting
    of bisimilarity one depth down. -/
def WorldBisim : ℕ → KripkeModel W Atom → W → KripkeModel W' Atom → W' → Prop
  | 0,     M, w, M', w' => ∀ p : Atom, M.val p w ↔ M'.val p w'
  | k + 1, M, w, M', w' =>
      (∀ p : Atom, M.val p w ↔ M'.val p w') ∧
      Set.LiftRel (WorldBisim k M · M' ·) ↑(M.access w) ↑(M'.access w')

theorem WorldBisim.refl (k : ℕ) (M : KripkeModel W Atom) (w : W) : WorldBisim k M w M w := by
  induction k generalizing w with
  | zero => intro _; rfl
  | succ k ih => exact ⟨fun _ ↦ Iff.rfl, Set.liftRel_refl_of_refl_on fun v _ ↦ ih v⟩

theorem WorldBisim.val_iff {k : ℕ} {M : KripkeModel W Atom} {w : W} {M' : KripkeModel W' Atom}
    {w' : W'} (h : WorldBisim k M w M' w') (p : Atom) : M.val p w ↔ M'.val p w' :=
  match k, h with
  | 0, h => h p
  | _ + 1, ⟨h, _⟩ => h p

/-- Teams are `k`-bisimilar ([aloni-anttila-yang-2024] Definition 3.6) when they are related by
    the lifting of `k`-bisimilarity of their worlds. -/
def StateBisim (k : ℕ) (M : KripkeModel W Atom) (s : Finset W) (M' : KripkeModel W' Atom)
    (s' : Finset W') : Prop :=
  Set.LiftRel (WorldBisim k M · M' ·) ↑s ↑s'

/-- A team property of `M` is closed under bounded bisimulation when, for some depth `k`, it is
    invariant under `k`-bisimilarity within `M`. -/
def BisimClosed (M : KripkeModel W Atom) (P : Team.TeamProperty W) : Prop :=
  ∃ k : ℕ, Team.Invariant (WorldBisim k M · M ·) P P

end ModalLogic
