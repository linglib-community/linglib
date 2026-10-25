module

public import Linglib.Semantics.Dynamic.DRS.Basic

/-!
# Verifying embeddings for DRSs

This file defines verification of DRSs by total embeddings into a
`FirstOrder.Language.Structure`, the semantics of Muskens's relational DRT. `Verifies f K` says
that `f` verifies every condition of `K`, and a sub-DRS is entered by existentially reassigning
its universe along `Box.Extends`, the antecedent of a conditional staying visible in its
consequent. The clauses follow Kamp and Reyle's Defs. 1.4.4, 2.1.4 and 2.4.2, but their
embeddings are partial and a sub-DRS extends them, keeping the value of a referent already
assigned; that semantics is `DRS.toRelAt` (`DRS/Indexed.lean`), and the two agree on DRSs that
declare no referent twice (`DRS.trueRel_iff_toRelAt`). Verification reads an embedding only at the
free referents, so whether some extension of an input verifies a proper DRS does not depend on
the input.

## Main definitions

* `DRT.VerifiesCondition`, `DRT.Verifies`: `f` verifies a DRS-condition, resp. the
  DRS `K`.

## Main statements

* `DRT.verifies_map`: alphabetic variants (Def. 1.4.8) have the same semantics.
* `DRT.verifiesCondition_congr`, `DRT.exists_extends_verifies_congr`: verification
  reads an embedding only at the free referents.
* `DRT.exists_extends_verifies_iff_of_isProper`: a proper DRS is verified by some
  extension of any input iff some embedding verifies it.

## Implementation notes

* On a DRS that re-declares a referent the two semantics diverge (Muskens's fn. 4):
  `[ | [x | man x] ⇒ [x | mortal x]]` says that every man is mortal in Kamp and Reyle's, and
  that there is a mortal if there is a man here (`Studies/Muskens1996.lean`).
* `Verifies`, `VerifiesCondition` and `VerifiesAll` are defined by structural recursion
  through the nested conditions, so the clause characterizations (`verifies_neg`, …) hold by
  `Iff.rfl`; `verifies_iff` recovers the `∀ c ∈ K.conditions` form.

## References

* [kamp-reyle-1993]
* [muskens-1996]
-/

@[expose] public section

open FirstOrder FirstOrder.Language

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M]

mutual
/-- `Verifies f K` says the embedding `f` *verifies* the DRS `K`, that is, every condition
of `K` (Def. 1.4.4). -/
def Verifies : (V → M) → DRS L V → Prop
  | f, ⟨_, cs⟩ => VerifiesAll f cs
/-- `VerifiesCondition f c` says the embedding `f` *verifies* the DRS-condition `c`
(Def. 1.4.4(ii)); a sub-DRS is entered by existentially (re)assigning along its extension
relation. -/
def VerifiesCondition : (V → M) → Condition L V → Prop
  | f, .atom a => a.Realize f
  | f, .eq a b => f a = f b
  | f, .neg K => ¬ ∃ g, K.Extends f g ∧ Verifies g K
  | f, .imp a c => ∀ g, a.Extends f g → Verifies g a → ∃ h, c.Extends g h ∧ Verifies h c
  | f, .dis l r => (∃ g, l.Extends f g ∧ Verifies g l) ∨ (∃ g, r.Extends f g ∧ Verifies g r)
/-- `VerifiesAll f cs` says `f` verifies every condition of `cs`. -/
def VerifiesAll : (V → M) → List (Condition L V) → Prop
  | _, [] => True
  | f, c :: cs => VerifiesCondition f c ∧ VerifiesAll f cs
end

/-! ### Structural simp API -/

variable {f : V → M}

theorem verifiesAll_iff {cs : List (Condition L V)} :
    VerifiesAll f cs ↔ ∀ c ∈ cs, VerifiesCondition f c := by
  induction cs with
  | nil => simp [VerifiesAll]
  | cons c cs ih => simp [VerifiesAll, ih]

@[simp] theorem verifies_mk (U : Finset V) (conds : List (Condition L V)) :
    Verifies f (.mk U conds) ↔ ∀ c ∈ conds, VerifiesCondition f c := verifiesAll_iff

theorem verifies_iff {K : DRS L V} :
    Verifies f K ↔ ∀ c ∈ K.conditions, VerifiesCondition f c := by
  cases K; exact verifiesAll_iff

@[simp] theorem verifies_empty : Verifies f (.empty : DRS L V) := by
  simp [DRS.empty]

@[simp] theorem verifies_merge [DecidableEq V] (K₁ K₂ : DRS L V) :
    Verifies f (K₁.merge K₂) ↔ Verifies f K₁ ∧ Verifies f K₂ := by
  simp only [verifies_iff, DRS.conditions_merge, List.forall_mem_append]

@[simp] theorem verifies_atom (a : L.Atom V) : VerifiesCondition f (.atom a) ↔ a.Realize f :=
  .rfl

@[simp] theorem verifies_eq (a b : V) :
    VerifiesCondition f (.eq a b : Condition L V) ↔ f a = f b := Iff.rfl

@[simp] theorem verifies_neg (K : DRS L V) :
    VerifiesCondition f (.neg K) ↔ ¬ ∃ g, K.Extends f g ∧ Verifies g K := Iff.rfl

@[simp] theorem verifies_imp (a c : DRS L V) :
    VerifiesCondition f (.imp a c) ↔
      ∀ g, a.Extends f g → Verifies g a → ∃ h, c.Extends g h ∧ Verifies h c := Iff.rfl

@[simp] theorem verifies_dis (l r : DRS L V) :
    VerifiesCondition f (.dis l r) ↔
      (∃ g, l.Extends f g ∧ Verifies g l) ∨ (∃ g, r.Extends f g ∧ Verifies g r) := Iff.rfl

theorem verifies_perm {U : Finset V} {cs ds : List (Condition L V)} (h : cs.Perm ds) :
    Verifies f (.mk U cs) ↔ Verifies f (.mk U ds) := by
  simp only [verifies_mk, h.mem_iff]

/-! ### Alphabetic variants -/

section Map

variable {W : Type*} [DecidableEq W]

private theorem verifies_map_all (e : V ≃ W) (K : DRS L V) (g : W → M)
    (ih : ∀ c ∈ K.conditions, ∀ u : W → M,
      VerifiesCondition u (c.map e) ↔ VerifiesCondition (u ∘ e) c) :
    Verifies g (K.map e) ↔ Verifies (g ∘ e) K := by
  simp only [verifies_iff, DRS.conditions_map, List.forall_mem_map]
  exact forall_congr' fun c => imp_congr_right fun hc => ih c hc g

private theorem exists_extends_verifies_map_aux (e : V ≃ W) (K : DRS L V) (f : W → M)
    (ih : ∀ c ∈ K.conditions, ∀ u : W → M,
      VerifiesCondition u (c.map e) ↔ VerifiesCondition (u ∘ e) c) :
    (∃ g, (K.map e).Extends f g ∧ Verifies g (K.map e)) ↔
      ∃ g, K.Extends (f ∘ e) g ∧ Verifies g K :=
  (exists_congr fun g => and_congr_right fun _ => verifies_map_all e K g ih).trans
    (DRS.exists_extends_map e K f (Verifies · K))

theorem verifies_map_condition (e : V ≃ W) (f : W → M) (c : Condition L V) :
    VerifiesCondition f (c.map e) ↔ VerifiesCondition (f ∘ e) c := by
  induction c generalizing f with
  | atom a => simp [Condition.map]
  | eq a b => simp [Condition.map]
  | neg K ih =>
    simp only [Condition.map, verifies_neg]
    exact not_congr (exists_extends_verifies_map_aux e K f ih)
  | imp a c iha ihc =>
    simp only [Condition.map, verifies_imp]
    refine Iff.trans (forall_congr' fun g => imp_congr_right fun _ => imp_congr
      (verifies_map_all e a g iha) (exists_extends_verifies_map_aux e c g ihc)) ?_
    exact DRS.forall_extends_map e a f
      (fun u => Verifies u a → ∃ h', c.Extends u h' ∧ Verifies h' c)
  | dis l r ihl ihr =>
    simp only [Condition.map, verifies_dis]
    exact or_congr (exists_extends_verifies_map_aux e l f ihl)
      (exists_extends_verifies_map_aux e r f ihr)

/-- `f` verifies `K.map e` iff `f ∘ e` verifies `K`, so alphabetic variants have the same
semantics. -/
theorem verifies_map (e : V ≃ W) (f : W → M) (K : DRS L V) :
    Verifies f (K.map e) ↔ Verifies (f ∘ e) K :=
  verifies_map_all e K f (fun c _ u => verifies_map_condition e u c)

theorem exists_extends_verifies_map (e : V ≃ W) (f : W → M) (K : DRS L V) :
    (∃ g, (K.map e).Extends f g ∧ Verifies g (K.map e)) ↔
      ∃ g, K.Extends (f ∘ e) g ∧ Verifies g K :=
  (exists_congr fun g => and_congr_right fun _ => verifies_map e g K).trans
    (DRS.exists_extends_map e K f (Verifies · K))

end Map

/-! ### Coincidence -/

section Coincidence

variable [DecidableEq V]

private theorem verifies_of_eqOn {K : DRS L V}
    (ih : ∀ c ∈ K.conditions, ∀ {g₁ g₂ : V → M}, Set.EqOn g₁ g₂ ↑c.freeVarFinset →
      (VerifiesCondition g₁ c ↔ VerifiesCondition g₂ c))
    (g g' : V → M) (hgg' : Set.EqOn g g' ↑(Condition.freeVarFinsetL K.conditions)) :
    Verifies g K → Verifies g' K := fun hv => verifies_iff.2 fun c hc =>
  (ih c hc (hgg'.mono (Finset.coe_subset.mpr
    (Condition.freeVarFinset_subset_freeVarFinsetL hc)))).mp (verifies_iff.1 hv c hc)

/-- Verification of a condition reads the embedding only at its free referents
(Def. 1.4.2). -/
theorem verifiesCondition_congr (c : Condition L V) {f₁ f₂ : V → M}
    (h : Set.EqOn f₁ f₂ ↑c.freeVarFinset) : VerifiesCondition f₁ c ↔ VerifiesCondition f₂ c := by
  induction c generalizing f₁ f₂ with
  | atom a =>
    simp only [verifies_atom, Atom.Realize]
    rw [show f₁ ∘ a.args = f₂ ∘ a.args from funext fun i => h (by simp)]
  | eq a b =>
    simp only [verifies_eq]
    rw [h (by simp), h (by simp)]
  | neg K ih =>
    rw [Condition.freeVarFinset_neg, DRS.coe_freeVarFinset] at h
    simp only [verifies_neg]
    exact not_congr (Box.exists_extends_congr K (verifies_of_eqOn ih) h)
  | imp a c iha ihc =>
    rw [Condition.freeVarFinset_imp, Finset.coe_union, Finset.coe_sdiff,
      DRS.coe_freeVarFinset, DRS.coe_freeVarFinset, ← Set.union_sdiff_distrib] at h
    simp only [verifies_imp]
    refine Box.forall_extends_congr a (S := ↑(Condition.freeVarFinsetL a.conditions) ∪
      (↑(Condition.freeVarFinsetL c.conditions) \ ↑c.referents)) ?_ h
    intro g g' hgg' H hv'
    exact Box.exists_extends_imp c (verifies_of_eqOn ihc) (hgg'.mono Set.subset_union_right)
      (H (verifies_of_eqOn iha g' g (hgg'.symm.mono Set.subset_union_left) hv'))
  | dis l r ihl ihr =>
    rw [Condition.freeVarFinset_dis, Finset.coe_union, DRS.coe_freeVarFinset,
      DRS.coe_freeVarFinset] at h
    simp only [verifies_dis]
    exact or_congr
      (Box.exists_extends_congr l (verifies_of_eqOn ihl) (h.mono Set.subset_union_left))
      (Box.exists_extends_congr r (verifies_of_eqOn ihr) (h.mono Set.subset_union_right))

/-- "Some extension verifies `K`" reads the input embedding only at `K`'s free
referents. -/
theorem exists_extends_verifies_congr {K : DRS L V} {f₁ f₂ : V → M}
    (h : Set.EqOn f₁ f₂ ↑K.freeVarFinset) :
    (∃ g, K.Extends f₁ g ∧ Verifies g K) ↔ ∃ g, K.Extends f₂ g ∧ Verifies g K := by
  rw [DRS.coe_freeVarFinset] at h
  exact Box.exists_extends_congr K
    (verifies_of_eqOn fun c _ _ _ => verifiesCondition_congr c) h

/-- A proper DRS is verified by some extension of any input iff some embedding
verifies it. -/
theorem exists_extends_verifies_iff_of_isProper {K : DRS L V} (hK : K.IsProper)
    (f : V → M) : (∃ g, K.Extends f g ∧ Verifies g K) ↔ ∃ g : V → M, Verifies g K := by
  refine ⟨fun ⟨g, _, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ =>
    (exists_extends_verifies_congr (f₁ := g) ?_).mp ⟨g, Box.Extends.refl K g, hg⟩⟩
  rw [DRS.IsProper] at hK
  simp [hK]

end Coincidence

end DRT
