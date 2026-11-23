/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Modal.Kripke
public import Linglib.Phonology.Autosegmental.TierTree.Realization

/-!
# The Kripke model of a representation along a tree of tiers

A representation along a tree of tiers is a Kripke model, `AR.toKripkeModel`: its worlds are
the positions on the tiers, a position sees its children, and the atom `⟨j, b⟩` is true at the
positions of tier `j` labelled `b`. A slot bears `b` on tier `j` when a position it reaches makes
that atom true (`mem_melody_iff_exists_val`). Representations whose models are related by a
bisimulation therefore bear the same labels at related slots
(`IsBisimulation.mem_melody_iff`). Material that no slot dominates, such as an autosegment left
floating by delinking, plays no part.

A relation between positions of the same tier is a bisimulation when related positions carry
the same label and each child of one is related to a child of the other
(`isBisimulation_toKripkeModel`). When each token of two representations has at most one line
to each lower tier, the converse holds: two slots that bear the same labels are bisimilar
(`exists_isBisimulation_iff_mem_melody`), so a slot is bisimilar to the slot of a symbol in a
realization exactly when it bears the labels that the primitive of that symbol bears
(`exists_isBisimulation_prod_map_iff`). The condition is needed: a slot with two tokens on the
tier below, one of them childless, bears the labels of a slot with one and is not bisimilar to it
(`exists_mem_melody_iff_and_not_isBisimulation`).

A phonological frame of [bird-blackburn-1991] has precedence, overlap and dominance between its
nodes, with a modality for each and the labels of nodes as propositional variables;
`toKripkeModel` is the dominance part of such a frame, and [potts-pullum-2002] state the content
of constraints in a modal language over structures of this kind. Modal formulas are preserved
under bisimulation ([blackburn-derijke-venema-2001]), so none of them tells a token that two
positions share from two copies of it. Attribute-value structures are Kripke models in the
same way, and there [blackburn-1992] states structure sharing with nominals, symbols true at
exactly one node, as [bird-blackburn-1991] do to state that two syllables share no mora; in
the automata of [kasper-rounds-1990] two paths lead to the same token exactly when they lead to
the same state.

## References

* [bird-blackburn-1991]
* [blackburn-1992]
* [blackburn-derijke-venema-2001]
* [kasper-rounds-1990]
* [potts-pullum-2002]
-/

@[expose] public section

open ModalLogic

namespace Autosegmental.AR

variable {ι : Type*} {τ : ι → Type*} [Fintype ι] [DecidableEq ι] {T : ParentTree ι}
  {X Y Z : AR τ}

/-- The Kripke model of a representation along a tree of tiers: a position sees its children,
and the atom `⟨j, b⟩` is true at the positions of tier `j` labelled `b`. -/
def toKripkeModel (T : ParentTree ι) (X : AR τ) : KripkeModel (ι × ℕ) (Σ j, τ j) where
  access := X.children T
  val a := fun (i, q) ↦ (X.word i)[q]?.map (Sigma.mk i) = some a

@[simp] theorem toKripkeModel_access (v : ι × ℕ) :
    (X.toKripkeModel T).access v = X.children T v := rfl

theorem toKripkeModel_val_self {j : ι} {q : ℕ} {b : τ j} :
    (X.toKripkeModel T).val ⟨j, b⟩ (j, q) ↔ (X.word j)[q]? = some b :=
  Option.map_eq_some_iff.trans
    ⟨fun ⟨_, ha, he⟩ ↦ by cases he; exact ha, fun h ↦ ⟨b, h, rfl⟩⟩

/-- A slot bears a label on a tier when a position it reaches makes the atom true. -/
theorem mem_melody_iff_exists_val {k : ℕ} {j : ι} {b : τ j} :
    b ∈ X.melody T k j ↔ ∃ v, X.Dom T (T.root, k) v ∧ (X.toKripkeModel T).val ⟨j, b⟩ v := by
  rw [mem_melody_iff_exists_dom]
  constructor
  · rintro ⟨q, hq, hb⟩
    exact ⟨(j, q), hq, toKripkeModel_val_self.mpr hb⟩
  · rintro ⟨⟨i, q⟩, hv, hval⟩
    obtain ⟨a, ha, he⟩ := Option.map_eq_some_iff.mp hval
    cases he
    exact ⟨q, hv, ha⟩

/-- Representations whose Kripke models are related by a bisimulation bear the same labels at
related slots. -/
theorem _root_.ModalLogic.KripkeModel.IsBisimulation.mem_melody_iff {r : ι × ℕ → ι × ℕ → Prop}
    (h : (Y.toKripkeModel T).IsBisimulation (Z.toKripkeModel T) r) {k k' : ℕ}
    (hr : r (T.root, k) (T.root, k')) {j : ι} {b : τ j} :
    b ∈ Y.melody T k j ↔ b ∈ Z.melody T k' j := by
  simp only [mem_melody_iff_exists_val]
  constructor
  · rintro ⟨v, hv, hval⟩
    obtain ⟨v', hv', hrv⟩ := h.exists_reflTransGen hr hv
    exact ⟨v', hv', (h.val_iff hrv _).mp hval⟩
  · rintro ⟨v', hv', hval⟩
    obtain ⟨v, hv, hrv⟩ := h.symm.exists_reflTransGen hr hv'
    exact ⟨v, hv, (h.val_iff hrv _).mpr hval⟩

/-- A relation between positions of the same tier is a bisimulation when related positions
carry the same label and each child of one is related to a child of the other. -/
theorem isBisimulation_toKripkeModel {R : ι → ℕ → ℕ → Prop}
    (label : ∀ ⦃j q q'⦄, R j q q' → (Y.word j)[q]? = (Z.word j)[q']?)
    (forth : ∀ ⦃i p p' j q⦄, R i p p' → (j, q) ∈ Y.children T (i, p) →
      ∃ q', (j, q') ∈ Z.children T (i, p') ∧ R j q q')
    (back : ∀ ⦃i p p' j q'⦄, R i p p' → (j, q') ∈ Z.children T (i, p') →
      ∃ q, (j, q) ∈ Y.children T (i, p) ∧ R j q q') :
    (Y.toKripkeModel T).IsBisimulation (Z.toKripkeModel T)
      fun v v' ↦ ∃ j q q', v = (j, q) ∧ v' = (j, q') ∧ R j q q' where
  val_iff := by
    rintro _ _ ⟨j, q, q', rfl, rfl, hR⟩ a
    show (Y.word j)[q]?.map (Sigma.mk j) = some a ↔ (Z.word j)[q']?.map (Sigma.mk j) = some a
    rw [label hR]
  liftRel_access := by
    rintro _ _ ⟨i, p, p', rfl, rfl, hR⟩
    exact ⟨fun ⟨j, q⟩ hc ↦
        let ⟨q', hc', hR'⟩ := forth hR hc; ⟨(j, q'), hc', j, q, q', rfl, rfl, hR'⟩,
      fun ⟨j, q'⟩ hc ↦
        let ⟨q, hc', hR'⟩ := back hR hc; ⟨(j, q), hc', j, q, q', rfl, rfl, hR'⟩⟩

/-! ### The labels a slot bears as a complete invariant -/

private theorem forth_of_mem_melody (hY : Y.IsFunctional T) {k k' : ℕ}
    (h : ∀ (j : ι) (b : τ j), b ∈ X.melody T k j → b ∈ Y.melody T k' j) {i j : ι} {p p' q : ℕ}
    (hp : X.Dom T (T.root, k) (i, p)) (hp' : Y.Dom T (T.root, k') (i, p'))
    (hc : (j, q) ∈ X.children T (i, p)) :
    ∃ q', (j, q') ∈ Y.children T (i, p') ∧ X.Dom T (T.root, k) (j, q) ∧
      Y.Dom T (T.root, k') (j, q') := by
  obtain ⟨hpar, hr, hl⟩ := mem_children.1 hc
  have hq : X.Dom T (T.root, k) (j, q) := hp.tail hc
  obtain ⟨q', hq', -⟩ := mem_melody_iff_exists_dom.1
    (h j _ (mem_melody_iff_exists_dom.2 ⟨q, hq, List.getElem?_eq_getElem hl.lt_right⟩))
  refine ⟨q', ?_, hq, hq'⟩
  rcases Relation.ReflTransGen.cases_tail hq' with he | ⟨u, hu, hc'⟩
  · exact absurd (congrArg Prod.fst he) hr
  · obtain rfl : u = (i, p') := hY.eq_of_dom hu hp' ((mem_children.1 hc').1.symm.trans hpar)
    exact hc'

private theorem label_of_mem_melody (hY : Y.IsFunctional T) {k k' : ℕ}
    (h : ∀ (j : ι) (b : τ j), b ∈ X.melody T k j → b ∈ Y.melody T k' j) {j : ι} {q q' : ℕ}
    (hq : X.Dom T (T.root, k) (j, q)) (hq' : Y.Dom T (T.root, k') (j, q')) {b : τ j}
    (hb : (X.word j)[q]? = some b) : (Y.word j)[q']? = some b := by
  obtain ⟨q₁, hd, hb'⟩ := mem_melody_iff_exists_dom.1
    (h j b (mem_melody_iff_exists_dom.2 ⟨q, hq, hb⟩))
  obtain ⟨-, rfl⟩ := Prod.mk.inj (hY.eq_of_dom hd hq' rfl)
  exact hb'

/-- When each token of two representations has at most one line to each lower tier, two slots
are bisimilar exactly when they bear the same labels. -/
theorem exists_isBisimulation_iff_mem_melody (hX : X.IsFunctional T) (hY : Y.IsFunctional T)
    {k k' : ℕ} :
    (∃ r, (X.toKripkeModel T).IsBisimulation (Y.toKripkeModel T) r ∧
        r (T.root, k) (T.root, k')) ↔
      ∀ (j : ι) (b : τ j), b ∈ X.melody T k j ↔ b ∈ Y.melody T k' j := by
  constructor
  · rintro ⟨r, hB, hr⟩ j b
    exact hB.mem_melody_iff hr
  · intro h
    refine ⟨_, isBisimulation_toKripkeModel (R := fun j q q' ↦
      X.Dom T (T.root, k) (j, q) ∧ Y.Dom T (T.root, k') (j, q')) ?_ ?_ ?_,
      T.root, k, k', rfl, rfl, .refl, .refl⟩
    · rintro j q q' ⟨hq, hq'⟩
      exact Option.ext fun b ↦ ⟨label_of_mem_melody hY (fun j b ↦ (h j b).1) hq hq',
        label_of_mem_melody hX (fun j b ↦ (h j b).2) hq' hq⟩
    · rintro i p p' j q ⟨hp, hp'⟩ hc
      obtain ⟨q', hc', hq, hq'⟩ := forth_of_mem_melody hY (fun j b ↦ (h j b).1) hp hp' hc
      exact ⟨q', hc', hq, hq'⟩
    · rintro i p p' j q' ⟨hp, hp'⟩ hc
      obtain ⟨q, hc', hq', hq⟩ := forth_of_mem_melody hX (fun j b ↦ (h j b).2) hp' hp hc
      exact ⟨q, hc', hq, hq'⟩

/-- A slot of a functional representation is bisimilar to the slot of a symbol in a realization
exactly when it bears the labels that the primitive of that symbol bears. -/
theorem exists_isBisimulation_prod_map_iff {S : Type*} (g₀ : S → AR τ) {w : List S}
    (hX : X.IsFunctional T) (h1 : ∀ s t, ((g₀ s).word t).length ≤ 1)
    (hroot : ∀ s, ((g₀ s).word T.root).length = 1) {k k' : ℕ} (hk' : k' < w.length) :
    (∃ r, (X.toKripkeModel T).IsBisimulation ((w.map g₀).prod.toKripkeModel T) r ∧
        r (T.root, k) (T.root, k')) ↔
      ∀ (j : ι) (b : τ j), b ∈ X.melody T k j ↔ b ∈ (g₀ w[k']).melody T 0 j :=
  (exists_isBisimulation_iff_mem_melody hX (isFunctional_prod_map T h1)).trans <|
    forall_congr' fun _ ↦ forall_congr' fun _ ↦ iff_congr Iff.rfl
      ((mem_melody_prod_map T g₀ hroot).trans ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hk', h⟩⟩)

/-! ### Slots that bear the same labels and are not bisimilar -/

private def chain : ParentTree (Fin 3) :=
  .ofIterate (fun i ↦ if i = 2 then 1 else 0) 0 2 (by decide)

/-- A slot with two tokens on the middle tier, the first of them with a token below it. -/
private def forked : AR fun _ : Fin 3 ↦ Unit :=
  fromRel (fun i ↦ if i = 1 then [(), ()] else [()])
    fun i j p _ ↦ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2 ∧ p = 0)

/-- A slot with one token on each tier below it. -/
private def straight : AR fun _ : Fin 3 ↦ Unit :=
  fromRel (fun _ ↦ [()]) fun i j _ _ ↦ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

/-- Slots that bear the same labels need not be bisimilar when a token has two lines to one
tier: a slot with two tokens on the tier below, one of them childless, bears the labels of a
slot with one. -/
theorem exists_mem_melody_iff_and_not_isBisimulation :
    ∃ (T : ParentTree (Fin 3)) (X Y : AR fun _ : Fin 3 ↦ Unit), Y.IsFunctional T ∧
      (∀ j b, b ∈ X.melody T 0 j ↔ b ∈ Y.melody T 0 j) ∧
      ¬ ∃ r, (X.toKripkeModel T).IsBisimulation (Y.toKripkeModel T) r ∧
        r (T.root, 0) (T.root, 0) := by
  refine ⟨chain, forked, straight, fun j p q q' _ hl hl' ↦ ?_, by decide, ?_⟩
  · have h := hl.lt_right
    have h' := hl'.lt_right
    have hlen : (straight.word j).length = 1 := rfl
    omega
  · rintro ⟨r, hB, hr⟩
    obtain ⟨hforth, -⟩ := hB.liftRel_access hr
    obtain ⟨v, hv, hrv⟩ := hforth (1, 1) (show (1, 1) ∈ forked.children chain (0, 0) by decide)
    have hv' : v ∈ straight.children chain (0, 0) := hv
    obtain rfl : v = (1, 0) := by
      rw [show straight.children chain (0, 0) = {(1, 0)} by decide] at hv'
      exact Finset.mem_singleton.1 hv'
    obtain ⟨-, hback⟩ := hB.liftRel_access hrv
    obtain ⟨u, hu, -⟩ :=
      hback (2, 0) (show (2, 0) ∈ straight.children chain (1, 0) by decide)
    have hu' : u ∈ forked.children chain (1, 1) := hu
    rw [show forked.children chain (1, 1) = ∅ by decide] at hu'
    exact absurd hu' (Finset.notMem_empty u)

end Autosegmental.AR
