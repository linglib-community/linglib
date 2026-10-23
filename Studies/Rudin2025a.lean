module

public import Linglib.Semantics.Modality.Background

/-!
# Rudin (2025): Asserting epistemic modals

This file formalizes the paper's Neo-Stalnakerian formalization of assertion. A speaker who
asserts a sentence presents her epistemic state as one in which the sentence is known: the
meta-intensionalization of a sentence is the set of states at all of whose worlds it is true
relative to that very state (`MI`), an assertion proposes that the context be refined into that
set in the most conservative way, and a hearer may reject it when no nonempty refinement of her
own state lies in it (`Compatible`). For a sentence whose truth does not depend on the state the
set is the downward closure of its proposition, so the update is the intersection of Stalnaker,
the largest refinement in the set. For *might* under the simple quantificational semantics the set
is the states that contain a prejacent world, so the update is the consistency test of Veltman,
and rejection turns on the rejector's information while truth turns on the assertor's: the
dissociation of truth from acceptance that Khoo observed (`dissociation`). Under the ordering
semantics of Kratzer a state carries an ordering source, and asserting *might* adds the prejacent
to it, a commensurate update whenever the base has a prejacent world
(`mightOrdUpdate_commensurate`). The appendices' *must* and relational semantics are also
formalized.

## Implementation notes

Epistemic states are sets of worlds, and the ordering version pairs a base with a Kratzer ordering
source, its best worlds being the minimal worlds of the base. Commensurativity is stated as
the paper states it, membership of the update in the meta-intensionalized set on every
compatible context;
conservativity, quantified over sentences, is rendered for the simple version by the update being
the largest refinement in the set. The commensurativity of the ordering update for *might* uses a
finite frame, the paper's limit assumption. The ordering update for *must* adds the prejacent and
drops the propositions disjoint from it; the paper argues on two three-world scenarios that both
steps are needed, and both are formalized.

## TODO

* The paper claims that after the *must* update every best world is a prejacent world, since
  an ordering proposition overlapping the prejacent favors its prejacent worlds. Two
  overlapping propositions can jointly leave a non-prejacent world best
  (`overlapping_not_sufficient`), so the *must* update is not commensurate in general.

## References

* [D. Rudin, *Asserting epistemic modals* (2025)][rudin-2025a]
* [R. C. Stalnaker, *Assertion* (1978)][stalnaker-1978]
* [F. Veltman, *Defaults in Update Semantics* (1996)][veltman-1996]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
* [J. Khoo, *Modal Disagreements* (2015)][khoo-2015]
* [S. Yalcin, *Epistemic Modals* (2007)][yalcin-2007]
-/

@[expose] public section

namespace Rudin2025a

open Modality

variable {W : Type*}

/-! ### Meta-intensionalization -/

/-- An information-sensitive denotation gives truth at a world relative to an epistemic state. -/
abbrev Denotation (W : Type*) := Set W → W → Prop

/-- A proposition is a sentence whose truth does not depend on the state. -/
def plain (p : Set W) : Denotation W := fun _ w ↦ w ∈ p

/-- Under the simple quantificational semantics *might* is true when some world of the state is a
prejacent world. -/
def might (p : Set W) : Denotation W := fun i _ ↦ (i ∩ p).Nonempty

/-- Under the simple quantificational semantics *must* is true when every world of the state is a
prejacent world. -/
def must (p : Set W) : Denotation W := fun i _ ↦ i ⊆ p

/-- The meta-intensionalization of a sentence consists of the states in which the speaker knows it,
those at all of whose worlds it is true relative to the state itself. -/
def MI (s : Denotation W) : Set (Set W) := {i | ∀ w ∈ i, s i w}

/-- A context is compatible with a sentence when some nonempty refinement, a subset, lies in
the sentence's meta-intensionalization. -/
def Compatible (s : Denotation W) (c : Set W) : Prop := ∃ c' ⊆ c, c'.Nonempty ∧ c' ∈ MI s

/-- Rejection of an assertion is licensed when the rejector's state is not compatible with
the sentence. -/
def RejectionLicensed (s : Denotation W) (i : Set W) : Prop := ¬ Compatible s i

/-- An update is commensurate with a sentence when it takes every compatible context into
the sentence's meta-intensionalization. -/
def Commensurate (s : Denotation W) (f : Set W → Set W) : Prop :=
  ∀ c, Compatible s c → f c ∈ MI s

theorem MI_plain (p : Set W) : MI (plain p) = {i | i ⊆ p} := by
  ext i; simp [MI, plain, Set.subset_def]

theorem mem_MI_might {p i : Set W} (hi : i.Nonempty) : i ∈ MI (might p) ↔ (i ∩ p).Nonempty :=
  let ⟨w, hw⟩ := hi
  ⟨fun h ↦ h w hw, fun h _ _ ↦ h⟩

theorem MI_must (p : Set W) : MI (must p) = MI (plain p) := by
  ext i
  exact ⟨fun h w hw ↦ h w hw hw, fun h _ _ v hv ↦ h v hv⟩

theorem compatible_plain {p c : Set W} : Compatible (plain p) c ↔ (c ∩ p).Nonempty := by
  constructor
  · rintro ⟨c', hc'c, ⟨w, hw⟩, hMI⟩
    exact ⟨w, hc'c hw, hMI w hw⟩
  · rintro ⟨w, hwc, hwp⟩
    exact ⟨{w}, Set.singleton_subset_iff.2 hwc, Set.singleton_nonempty w,
      fun v hv ↦ Set.mem_singleton_iff.1 hv ▸ hwp⟩

theorem compatible_might {p c : Set W} : Compatible (might p) c ↔ (c ∩ p).Nonempty := by
  constructor
  · rintro ⟨c', hc'c, hne, hMI⟩
    exact ((mem_MI_might hne).1 hMI).mono (Set.inter_subset_inter_left p hc'c)
  · intro h
    have hc : c.Nonempty := h.mono Set.inter_subset_left
    exact ⟨c, subset_rfl, hc, (mem_MI_might hc).2 h⟩

theorem rejectionLicensed_plain {p i : Set W} : RejectionLicensed (plain p) i ↔ i ∩ p = ∅ := by
  rw [RejectionLicensed, compatible_plain, Set.not_nonempty_iff_eq_empty]

theorem rejectionLicensed_plain_iff {p i : Set W} :
    RejectionLicensed (plain p) i ↔ i ∈ MI (plain pᶜ) := by
  rw [rejectionLicensed_plain, MI_plain, Set.mem_ofPred_eq, Set.subset_compl_iff_disjoint_right,
    Set.disjoint_iff_inter_eq_empty]

theorem rejectionLicensed_might {p i : Set W} : RejectionLicensed (might p) i ↔ i ∩ p = ∅ := by
  rw [RejectionLicensed, compatible_might, Set.not_nonempty_iff_eq_empty]

/-! ### Update potentials -/

/-- The Stalnakerian update is intersection with the proposition. -/
def plainUpdate (p c : Set W) : Set W := c ∩ p

theorem plainUpdate_commensurate (p : Set W) : Commensurate (plain p) (plainUpdate p) :=
  fun _ _ _ h ↦ h.2

theorem plainUpdate_greatest {p c c' : Set W} (hc' : c' ⊆ c) (h : c' ∈ MI (plain p)) :
    c' ⊆ plainUpdate p c :=
  fun w hw ↦ ⟨hc' hw, h w hw⟩

/-- The update of *might* returns the context itself when it has a prejacent world, and the absurd
context otherwise. -/
def mightUpdate (p c : Set W) : Set W := {w ∈ c | (c ∩ p).Nonempty}

theorem mightUpdate_of_nonempty {p c : Set W} (h : (c ∩ p).Nonempty) : mightUpdate p c = c := by
  ext w; simp [mightUpdate, h]

theorem mightUpdate_of_empty {p c : Set W} (h : c ∩ p = ∅) : mightUpdate p c = ∅ := by
  ext w; simp [mightUpdate, h]

theorem mightUpdate_commensurate (p : Set W) : Commensurate (might p) (mightUpdate p) := by
  intro c hc
  have h := compatible_might.1 hc
  rw [mightUpdate_of_nonempty h]
  exact (mem_MI_might (h.mono Set.inter_subset_left)).2 h

theorem mightUpdate_greatest {p c c' : Set W} (hc' : c' ⊆ c) (hne : c'.Nonempty)
    (h : c' ∈ MI (might p)) : c' ⊆ mightUpdate p c :=
  fun _ hw ↦ ⟨hc' hw, ((mem_MI_might hne).1 h).mono (Set.inter_subset_inter_left p hc')⟩

theorem must_updates_as_plain (p : Set W) : Commensurate (must p) (plainUpdate p) := by
  intro c _
  rw [MI_must]
  exact fun _ h ↦ h.2

theorem dissociation {p a r : Set W} (ha : (a ∩ p).Nonempty) (hr : r ∩ p = ∅) :
    a ∈ MI (might p) ∧ RejectionLicensed (might p) r :=
  ⟨fun _ _ ↦ ha, rejectionLicensed_might.2 hr⟩

/-! ### The ordering semantics -/

/-- An epistemic state of the ordering version consists of a modal base and an ordering source. -/
structure OrdState (W : Type*) where
  base : Set W
  ordering : Set (W → Prop)

/-- The best worlds of a state are the worlds of the base that no other world of the base betters
under the ordering source. -/
def OrdState.best (i : OrdState W) : Set W := (premisePreorder i.ordering).minimals i.base

/-- A denotation relative to a state with an ordering source. -/
abbrev OrdDenotation (W : Type*) := OrdState W → W → Prop

/-- A proposition. -/
def plainOrd (p : Set W) : OrdDenotation W := fun _ w ↦ w ∈ p

/-- Under the ordering semantics *might* is true when some best world is a prejacent world. -/
def mightOrd (p : Set W) : OrdDenotation W := fun i _ ↦ (i.best ∩ p).Nonempty

/-- Under the ordering semantics *must* is true when every best world is a prejacent world. -/
def mustOrd (p : Set W) : OrdDenotation W := fun i _ ↦ i.best ⊆ p

/-- Meta-intensionalization over the base of a state. -/
def MIOrd (s : OrdDenotation W) : Set (OrdState W) := {i | ∀ w ∈ i.base, s i w}

/-- A refinement shrinks the base; the ordering source may change freely. -/
def OrdState.Refines (i' i : OrdState W) : Prop := i'.base ⊆ i.base

/-- Compatibility, with a nonempty base in place of a nonempty state. -/
def CompatibleOrd (s : OrdDenotation W) (c : OrdState W) : Prop :=
  ∃ c', c'.Refines c ∧ c'.base.Nonempty ∧ c' ∈ MIOrd s

/-- A proposition still updates by intersection, the ordering source untouched. -/
def plainOrdUpdate (p : Set W) (c : OrdState W) : OrdState W := ⟨c.base ∩ p, c.ordering⟩

theorem plainOrdUpdate_mem_MIOrd (p : Set W) (c : OrdState W) :
    plainOrdUpdate p c ∈ MIOrd (plainOrd p) :=
  fun _ h ↦ h.2

open scoped Classical in
/-- The update of *might* adds the prejacent to the ordering source when the base has a prejacent
world, and otherwise empties the base. -/
noncomputable def mightOrdUpdate (p : Set W) (c : OrdState W) : OrdState W :=
  if (c.base ∩ p).Nonempty then ⟨c.base, insert (· ∈ p) c.ordering⟩ else ⟨∅, c.ordering⟩

theorem mightOrdUpdate_of_compatible {p : Set W} {c : OrdState W} (h : (c.base ∩ p).Nonempty) :
    mightOrdUpdate p c = ⟨c.base, insert (· ∈ p) c.ordering⟩ := by
  rw [mightOrdUpdate, ite_eq_left h]

theorem mightOrdUpdate_commensurate [Finite W] {p : Set W} {c : OrdState W}
    (h : (c.base ∩ p).Nonempty) : mightOrdUpdate p c ∈ MIOrd (mightOrd p) := by
  rw [mightOrdUpdate_of_compatible h]
  intro _ _
  obtain ⟨m, hm⟩ := Preorder.minimals_nonempty (premisePreorder (insert (· ∈ p) c.ordering))
    (s := c.base ∩ p) h
  refine ⟨m, ?_, (Preorder.minimals_subset _ _ hm).2⟩
  rw [Preorder.mem_minimals_iff] at hm
  show m ∈ (premisePreorder (insert (· ∈ p) c.ordering)).minimals c.base
  rw [Preorder.mem_minimals_iff]
  refine ⟨hm.1.1, fun ⦃v⦄ hv hvm ↦ ?_⟩
  by_cases hvp : v ∈ p
  · exact hm.2 ⟨hv, hvp⟩ hvm
  · exact absurd (hvm (· ∈ p) (Set.mem_insert _ _) hm.1.2) hvp

theorem compatibleOrd_might {p : Set W} {c : OrdState W} :
    CompatibleOrd (mightOrd p) c ↔ (c.base ∩ p).Nonempty := by
  constructor
  · rintro ⟨c', hc'c, ⟨v, hv⟩, hMI⟩
    obtain ⟨m, hmb, hmp⟩ := hMI v hv
    exact ⟨m, hc'c (Preorder.minimals_subset _ _ hmb), hmp⟩
  · rintro ⟨w, hwb, hwp⟩
    refine ⟨⟨c.base, {(· ∈ p)}⟩, subset_rfl, ⟨w, hwb⟩, fun _ _ ↦ ⟨w, ?_, hwp⟩⟩
    show w ∈ (premisePreorder {(· ∈ p)}).minimals c.base
    rw [Preorder.minimals_ofCriteria_eq ⟨w, hwb, by simpa using hwp⟩]
    exact ⟨hwb, by simpa using hwp⟩

theorem rejectionOrd_might {p : Set W} {i : OrdState W} :
    ¬ CompatibleOrd (mightOrd p) i ↔ i.base ∩ p = ∅ := by
  rw [compatibleOrd_might, Set.not_nonempty_iff_eq_empty]

/-! ### *must* under the ordering semantics -/

open scoped Classical in
/-- The update of *must* adds the prejacent to the ordering source and removes the propositions
disjoint from it, when the base has a prejacent world. -/
noncomputable def mustOrdUpdate (p : Set W) (c : OrdState W) : OrdState W :=
  if (c.base ∩ p).Nonempty then
    ⟨c.base, insert (· ∈ p) {q ∈ c.ordering | ∃ w ∈ p, q w}⟩
  else ⟨∅, c.ordering⟩

theorem mustOrd_singleton {p : Set W} {c : OrdState W} (h : (c.base ∩ p).Nonempty) :
    (⟨c.base, {(· ∈ p)}⟩ : OrdState W) ∈ MIOrd (mustOrd p) := by
  obtain ⟨w, hwb, hwp⟩ := h
  intro _ _ v hv
  change v ∈ (premisePreorder {(· ∈ p)}).minimals c.base at hv
  rw [Preorder.minimals_ofCriteria_eq ⟨w, hwb, by simpa using hwp⟩] at hv
  simpa using hv.2

theorem compatibleOrd_must [Finite W] {p : Set W} {c : OrdState W} :
    CompatibleOrd (mustOrd p) c ↔ (c.base ∩ p).Nonempty := by
  constructor
  · rintro ⟨c', hc'c, ⟨v, hv⟩, hMI⟩
    obtain ⟨m, hm⟩ := Preorder.minimals_nonempty (premisePreorder (c'.ordering))
      (s := c'.base) ⟨v, hv⟩
    exact ⟨m, hc'c (Preorder.minimals_subset _ _ hm), hMI v hv hm⟩
  · intro h
    exact ⟨⟨c.base, {(· ∈ p)}⟩, subset_rfl, h.mono Set.inter_subset_left, mustOrd_singleton h⟩

/-- Decide a claim about a three-world state by unfolding the operators. -/
scoped macro "decide_states" : tactic =>
  `(tactic| (simp only [MIOrd, mustOrd, OrdState.best, Preorder.mem_minimals_iff,
      premisePreorder, Preorder.ofCriteria_le_iff,
      Set.mem_ofPred_eq, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, Set.subset_def,
      Set.mem_inter_iff, Set.Nonempty, forall_eq_or_imp, forall_eq, Set.mem_empty_iff_false,
      false_implies,
      implies_true, true_and, and_true, forall_const]; decide))

theorem must_needs_prejacent :
    (⟨Set.univ, ∅⟩ : OrdState (Fin 3)) ∉ MIOrd (mustOrd {0, 1}) ∧
      (⟨Set.univ, {(· ∈ ({0, 1} : Set (Fin 3)))}⟩ : OrdState (Fin 3)) ∈ MIOrd (mustOrd {0, 1}) := by
  decide_states

theorem must_needs_removal :
    (⟨Set.univ, {(· ∈ ({0, 1} : Set (Fin 3))), (· ∈ ({2} : Set (Fin 3)))}⟩ : OrdState (Fin 3)) ∉
      MIOrd (mustOrd {0, 1}) := by
  decide_states

theorem mustOrdUpdate_removal :
    mustOrdUpdate ({0, 1} : Set (Fin 3)) ⟨Set.univ, {(· ∈ ({2} : Set (Fin 3)))}⟩ ∈
      MIOrd (mustOrd {0, 1}) := by
  have h : {q ∈ ({(· ∈ ({2} : Set (Fin 3)))} : Set (Fin 3 → Prop)) |
      ∃ w ∈ ({0, 1} : Set (Fin 3)), q w} = ∅ := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
      not_and]
    rintro rfl
    simp
  rw [mustOrdUpdate, ite_eq_left ⟨0, Set.mem_univ _, by simp⟩, h, insert_empty_eq]
  exact must_needs_prejacent.2

theorem overlapping_not_sufficient :
    ∃ o : Set (Fin 3 → Prop), (∀ q ∈ o, ∃ w ∈ ({0, 1} : Set (Fin 3)), q w) ∧
      (⟨Set.univ, insert (· ∈ ({0, 1} : Set (Fin 3))) o⟩ : OrdState (Fin 3)) ∉ MIOrd (mustOrd {0,
      1}) :=
  ⟨{(· ∈ ({1, 2} : Set (Fin 3))), (· ∈ ({0, 2} : Set (Fin 3)))}, by decide_states, by decide_states⟩

/-! ### The relational semantics -/

/-- *might* on an accessibility function. -/
def mightRel (f : W → Set W) (p : Set W) (w : W) : Prop := (f w ∩ p).Nonempty

/-- Epistemic closure says that from every world of the state the whole state is accessible. -/
def Closed (f : W → Set W) (i : Set W) : Prop := ∀ w ∈ i, f w = i

theorem relational_might {f : W → Set W} {p i : Set W} (hf : Closed f i) (hi : i.Nonempty) :
    (∀ w ∈ i, mightRel f p w) ↔ (i ∩ p).Nonempty := by
  obtain ⟨v, hv⟩ := hi
  exact ⟨fun h ↦ hf v hv ▸ h v hv, fun h w hw ↦ by rw [mightRel, hf w hw]; exact h⟩

theorem relational_must {f : W → Set W} {p i : Set W} (hf : Closed f i) :
    (∀ w ∈ i, f w ⊆ p) ↔ i ⊆ p :=
  ⟨fun h w hw ↦ h w hw (hf w hw ▸ hw), fun h w hw ↦ (hf w hw).symm ▸ h⟩

theorem relational_ordering {f : W → Set W} {g : W → Set (W → Prop)} {p : Set W}
    {i : OrdState W} (hf : Closed f i.base) (hg : ∀ w ∈ i.base, g w = i.ordering)
    (hi : i.base.Nonempty) :
    (∀ w ∈ i.base, ((premisePreorder (g w)).minimals (f w) ∩ p).Nonempty) ↔
      i ∈ MIOrd (mightOrd p) := by
  obtain ⟨v, hv⟩ := hi
  constructor
  · intro h _ _
    have := h v hv
    rwa [hf v hv, hg v hv] at this
  · intro h w hw
    rw [hf w hw, hg w hw]
    exact h v hv

end Rudin2025a
