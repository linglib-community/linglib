module

public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.UpperLower.Closure
public import Linglib.Discourse.Commitment.Proposition

/-!
# Commitment spaces

A commitment space is a set of discourse states with a least member, the root, which is the
current state; the other members are the continuations the conversation projects. A basic speech
act keeps the projected states that carry its commitments, and the least of them is the new root.
A meta-speech act keeps the root and prunes the continuations, as a question restricts them to the
answers it proposes and a denegation removes the states an act would reach. Conjunction and
disjunction of acts are intersection and union of the sets of states they reach, which need not
be rooted, so the laws relating the acts are stated on those sets.

Commitment Space Semantics is the instance over sets of propositions ordered by inclusion. A basic
act adds propositions, and an assertion adds the proposition `k⊢φ` that the speaker is committed
to its content, while a polar question proposes that the addressee commit to `φ` or to `¬φ`. The
participant whose commitment an act projects is thus the speaker of an assertion and the
addressee of a question.

## Main definitions

* `Commitment.Space S`: rooted sets of states, ordered by inclusion, with the free space
  `Space.Ici`.
* `Space.restrict`, `Space.denegate`, `Space.question`: the meta-speech acts.
* `Space.update`: the basic act adding `k`.
* `Space.assert`, `Space.monopolarQuestion`, `Space.bipolarQuestion`: assertion and polar
  questions in Commitment Space Semantics.
* `Space.ProjectsCommitment`: the act projects a participant's commitment on its content.

## Main results

* `Space.root_update_mem_iff`, `Space.coe_update_of_root_mem`: a space admits an update iff its
  states above `k` have a least member, and the update is then the restriction
  `{c ∈ C | √C + A ⊆ c}`.
* `Space.coe_update_sSup`: the update by a join is the conjunction of the updates.
* `Space.sdiff_coe_denegate`, `Space.coe_denegate_inter`: two denegations cancel, and de
  Morgan's laws hold for them.
* `Space.projectsCommitment_Ici_assert_iff`, `Space.projectsCommitment_Ici_bipolarQuestion_iff`:
  in the space of all states, an assertion projects only its author's commitment and a bipolar
  question only that of the participant it is put to, unless their commitments coincide.

## Implementation notes

* The operations are total. `restrict` and `denegate` always keep the root, and `update` roots
  at the meet of the states above `k`, adjoining it when it is not one of them. The space
  admits the update when that root is one of its states, `(C.update k).root ∈ C`; this and
  "not redundant", `¬ k ≤ C.root`, are hypotheses of the theorems, not arguments of the
  operations.
* The root of an update is `k ⊔ C.root` only when the space projects that state
  (`Space.root_update_of_mem`). After a question it carries the proposal as well, so an
  assertion on a space need not add exactly its content to the common ground.
* The root is a field; it is determined by the states, which makes `Space S` a `SetLike`.

## References

* [A. Cohen and M. Krifka, *Superlative quantifiers and meta-speech acts*
  (2014)][cohen-krifka-2014]
* [M. Krifka, *Bias in Commitment Space Semantics: Declarative Questions, Negated Questions,
  and Question Tags* (2015)][krifka-2015]
* [T. van der Leer, *Commitments, beliefs and expectations in conversation*
  (2026)][van-der-leer-2026]
* [E. Coppock and S. Wechsler, *The proper treatment of egophoricity in Kathmandu Newari*
  (2018)][coppock-wechsler-2018]
-/

@[expose] public section

namespace Commitment

/-- A commitment space is a set of states with a least member, its root. -/
structure Space (S : Type*) [LE S] where
  /-- The states the space projects. -/
  carrier : Set S
  /-- The current state. -/
  root : S
  /-- The root is the least state. -/
  isLeast' : IsLeast carrier root

namespace Space

section PartialOrder

variable {S : Type*} [PartialOrder S] (C : Space S) {D E : Set S} {c d : S}

instance : SetLike (Space S) S where
  coe := carrier
  coe_injective := by
    rintro ⟨s, r, h⟩ ⟨_, r', h'⟩ (rfl : s = _)
    obtain rfl := h.unique h'
    rfl

/-- Spaces are ordered by inclusion, and the smaller space is the stronger act. -/
instance : PartialOrder (Space S) := .ofSetLike (Space S)

@[ext] theorem ext {C D : Space S} (h : ∀ c, c ∈ C ↔ c ∈ D) : C = D := SetLike.ext h

@[simp] theorem mem_carrier : c ∈ C.carrier ↔ c ∈ C := Iff.rfl

@[simp] theorem mem_mk {s : Set S} {r : S} (h : IsLeast s r) : c ∈ mk s r h ↔ c ∈ s := Iff.rfl

@[simp, norm_cast] theorem coe_mk {s : Set S} {r : S} (h : IsLeast s r) :
    (mk s r h : Set S) = s := rfl

protected theorem isLeast : IsLeast (C : Set S) C.root := C.isLeast'

theorem root_mem : C.root ∈ C := C.isLeast.1

theorem root_le (hc : c ∈ C) : C.root ≤ c := C.isLeast.2 hc

/-- The space with only its root. -/
instance : Singleton S (Space S) := ⟨fun c ↦ ⟨{c}, c, isLeast_singleton⟩⟩

@[simp, norm_cast] theorem coe_singleton (c : S) : (({c} : Space S) : Set S) = {c} := rfl

@[simp] theorem mem_singleton : d ∈ ({c} : Space S) ↔ d = c := Iff.rfl

@[simp] theorem root_singleton (c : S) : ({c} : Space S).root = c := rfl

/-- The free space on `c` has every state above `c`. -/
protected def Ici (c : S) : Space S := ⟨Set.Ici c, c, isLeast_Ici⟩

@[simp, norm_cast] theorem coe_Ici (c : S) : (Space.Ici c : Set S) = Set.Ici c := rfl

@[simp] theorem mem_Ici : d ∈ Space.Ici c ↔ c ≤ d := Iff.rfl

@[simp] theorem root_Ici (c : S) : (Space.Ici c).root = c := rfl

/-! ### Meta-speech acts -/

/-- `C.restrict D` has the root and the members of `C` in `D`. A meta-speech act is such a
restriction, which keeps the root and prunes the continuations. -/
def restrict (D : Set S) : Space S :=
  ⟨insert C.root (↑C ∩ D), C.root, Set.mem_insert _ _,
    Set.forall_mem_insert.2 ⟨le_rfl, fun _ hd ↦ C.root_le hd.1⟩⟩

@[simp] theorem root_restrict (D : Set S) : (C.restrict D).root = C.root := rfl

@[simp, norm_cast] theorem coe_restrict (D : Set S) :
    (C.restrict D : Set S) = insert C.root (↑C ∩ D) := rfl

@[simp] theorem mem_restrict : d ∈ C.restrict D ↔ d = C.root ∨ d ∈ C ∧ d ∈ D := Iff.rfl

theorem coe_restrict_of_root_mem (h : C.root ∈ D) : (C.restrict D : Set S) = ↑C ∩ D :=
  Set.insert_eq_of_mem ⟨C.root_mem, h⟩

theorem coe_restrict_union (D E : Set S) :
    (C.restrict (D ∪ E) : Set S) = ↑(C.restrict D) ∪ ↑(C.restrict E) := by
  rw [coe_restrict, coe_restrict, coe_restrict, Set.inter_union_distrib_left,
    Set.insert_union_distrib]

theorem coe_restrict_inter (D E : Set S) :
    (C.restrict (D ∩ E) : Set S) = ↑(C.restrict D) ∩ ↑(C.restrict E) := by
  rw [coe_restrict, coe_restrict, coe_restrict, Set.inter_inter_distrib_left,
    Set.insert_inter_distrib]

/-- The denegation `C − D` has the root and the members of `C` outside `D`
([cohen-krifka-2014] (26), [krifka-2015] (5), [van-der-leer-2026] Definition 22). -/
def denegate (D : Set S) : Space S := C.restrict Dᶜ

@[simp] theorem root_denegate (D : Set S) : (C.denegate D).root = C.root := rfl

@[simp] theorem mem_denegate : d ∈ C.denegate D ↔ d = C.root ∨ d ∈ C ∧ d ∉ D := Iff.rfl

theorem coe_denegate_of_root_notMem (h : C.root ∉ D) : (C.denegate D : Set S) = ↑C \ D :=
  C.coe_restrict_of_root_mem h

/-- Two denegations cancel ([cohen-krifka-2014] (28)). -/
theorem sdiff_coe_denegate (hD : D ⊆ C) (h : C.root ∉ D) :
    (C : Set S) \ ↑(C.denegate D) = D := by
  rw [C.coe_denegate_of_root_notMem h, Set.sdiff_sdiff_cancel_left hD]

/-- De Morgan's law `∼[A & B] = ∼A ∨ ∼B` for denegations ([cohen-krifka-2014] (34)). -/
theorem coe_denegate_inter (D E : Set S) :
    (C.denegate (D ∩ E) : Set S) = ↑(C.denegate D) ∪ ↑(C.denegate E) := by
  rw [denegate, Set.compl_inter, coe_restrict_union]; rfl

/-- De Morgan's law `∼[A ∨ B] = ∼A & ∼B` for denegations ([cohen-krifka-2014] (35)), whose two
sides are rooted though the disjunction is not. -/
theorem coe_denegate_union (D E : Set S) :
    (C.denegate (D ∪ E) : Set S) = ↑(C.denegate D) ∩ ↑(C.denegate E) := by
  rw [denegate, Set.compl_union, coe_restrict_inter]; rfl

/-- The question `C.question P` keeps the root and proposes the continuations that carry one of
the acts in `P` ([krifka-2015] (23), (27)). -/
def question (P : Set S) : Space S := C.restrict (upperClosure P)

@[simp] theorem root_question (P : Set S) : (C.question P).root = C.root := rfl

theorem mem_question {P : Set S} : d ∈ C.question P ↔ d = C.root ∨ d ∈ C ∧ ∃ p ∈ P, p ≤ d :=
  .rfl

/-- A question with alternative proposals is the disjunction of the questions
([krifka-2015] (31), (34)). -/
theorem coe_question_union (P Q : Set S) :
    (C.question (P ∪ Q) : Set S) = ↑(C.question P) ∪ ↑(C.question Q) := by
  rw [question, upperClosure_union, UpperSet.coe_inf, coe_restrict_union]
  rfl

end PartialOrder

/-! ### Basic speech acts -/

section CompleteLattice

variable {S : Type*} [CompleteLattice S] (C : Space S) {D : Set S} {k l d : S}

/-- The update `C + k` has the states of `C` above `k`, rooted at their meet
([cohen-krifka-2014] (23), [krifka-2015] (2), (3)). -/
def update (k : S) : Space S :=
  ⟨insert (sInf (↑C ∩ Set.Ici k)) (↑C ∩ Set.Ici k), sInf (↑C ∩ Set.Ici k), Set.mem_insert _ _,
    Set.forall_mem_insert.2 ⟨le_rfl, fun _ hd ↦ sInf_le hd⟩⟩

theorem root_update (k : S) : (C.update k).root = sInf (↑C ∩ Set.Ici k) := rfl

@[simp] theorem mem_update : d ∈ C.update k ↔ d = (C.update k).root ∨ d ∈ C ∧ k ≤ d := Iff.rfl

theorem le_root_update (k : S) : k ≤ (C.update k).root := le_sInf fun _ hd ↦ hd.2

theorem root_le_root_update (k : S) : C.root ≤ (C.update k).root :=
  le_sInf fun _ hd ↦ C.root_le hd.1

/-- The space admits an update, in that the new root is one of its states, iff its states above
`k` have a least member. -/
theorem root_update_mem_iff : (C.update k).root ∈ C ↔ ∃ r, IsLeast (↑C ∩ Set.Ici k) r := by
  refine ⟨fun h ↦ ⟨_, ⟨h, C.le_root_update k⟩, fun _ hd ↦ sInf_le hd⟩, fun ⟨r, hr⟩ ↦ ?_⟩
  rw [root_update, hr.csInf_eq]
  exact hr.1.1

theorem root_update_of_mem (h : k ⊔ C.root ∈ C) : (C.update k).root = k ⊔ C.root :=
  IsLeast.csInf_eq ⟨⟨h, le_sup_left⟩, fun _ hd ↦ sup_le hd.2 (C.root_le hd.1)⟩

/-- An update the space admits is its restriction to the states above `k`. -/
theorem coe_update_of_root_mem (h : (C.update k).root ∈ C) :
    (C.update k : Set S) = ↑C ∩ Set.Ici k :=
  Set.insert_eq_of_mem ⟨h, C.le_root_update k⟩

theorem update_le (h : (C.update k).root ∈ C) : C.update k ≤ C := by
  rintro d (rfl | hd)
  exacts [h, hd.1]

theorem root_mem_update_iff : C.root ∈ C.update k ↔ k ≤ C.root :=
  ⟨fun h ↦ h.elim (fun e ↦ e ▸ C.le_root_update k) And.right, fun h ↦ Or.inr ⟨C.root_mem, h⟩⟩

/-- Adding more is the stronger act ([cohen-krifka-2014] (86)). -/
theorem update_le_update (hkl : k ≤ l) (h : (C.update l).root ∈ C) :
    C.update l ≤ C.update k := by
  rintro d (rfl | hd)
  exacts [Or.inr ⟨h, hkl.trans (C.le_root_update l)⟩, Or.inr ⟨hd.1, hkl.trans hd.2⟩]

theorem update_congr {C' : Space S} (h : (↑C ∩ Set.Ici k : Set S) = ↑C' ∩ Set.Ici l) :
    C.update k = C'.update l :=
  SetLike.coe_injective (congrArg (fun R ↦ insert (sInf R) R) h)

theorem update_update (h : (C.update k).root ∈ C) (l : S) :
    (C.update k).update l = C.update (l ⊔ k) :=
  update_congr _ <| by
    rw [C.coe_update_of_root_mem h, Set.inter_assoc, Set.Ici_inter_Ici, sup_comm]

/-- Admitted updates commute ([cohen-krifka-2014] (31), [krifka-2015] (6)). -/
theorem update_comm (hk : (C.update k).root ∈ C) (hl : (C.update l).root ∈ C) :
    (C.update k).update l = (C.update l).update k := by
  rw [C.update_update hk, C.update_update hl, sup_comm]

theorem restrict_coe_update (k : S) : C.restrict (C.update k) = C.restrict (Set.Ici k) := by
  ext d
  simp only [mem_restrict, SetLike.mem_coe, mem_update, Set.mem_Ici]
  refine or_congr_right (and_congr_right fun hd ↦ ⟨fun h ↦ ?_, fun h ↦ Or.inr ⟨hd, h⟩⟩)
  exact h.elim (fun e ↦ e ▸ C.le_root_update k) And.right

/-- A question with one proposal restricts the space to the states of its update
([krifka-2015] (27)). -/
theorem question_singleton (k : S) : C.question {k} = C.restrict (C.update k) := by
  rw [question, restrict_coe_update, upperClosure_singleton, UpperSet.coe_Ici]

theorem update_restrict_of_subset (h : ↑C ∩ Set.Ici k ⊆ D) :
    (C.restrict D).update k = C.update k :=
  update_congr _ <| Set.ext fun _ ↦
    ⟨fun ⟨hd, hk⟩ ↦ ⟨hd.elim (fun e ↦ e ▸ C.root_mem) And.left, hk⟩,
      fun hd ↦ ⟨Or.inr ⟨hd.1, h hd⟩, hd.2⟩⟩

/-- The update by a join is the conjunction of the updates ([cohen-krifka-2014] (31)), when the
space admits it. -/
theorem coe_update_sSup {K : Set S} (hK : K.Nonempty) (h : (C.update (sSup K)).root ∈ C) :
    (C.update (sSup K) : Set S) = ⋂ k ∈ K, (C.update k : Set S) := by
  rw [C.coe_update_of_root_mem h]
  ext d
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_Ici, sSup_le_iff, Set.mem_iInter,
    mem_update]
  refine ⟨fun hd k hk ↦ Or.inr ⟨hd.1, hd.2 k hk⟩, fun hd ↦ ?_⟩
  have hle : ∀ k ∈ K, k ≤ d := fun k hk ↦
    (hd k hk).elim (fun e ↦ e ▸ C.le_root_update k) And.right
  refine ⟨?_, hle⟩
  by_contra hC
  obtain ⟨k, hk⟩ := hK
  have e : d = (C.update k).root := (hd k hk).resolve_right fun h' ↦ hC h'.1
  have hk' : C.update k = C.update (sSup K) :=
    update_congr _ <| Set.ext fun x ↦ and_congr_right fun hx ↦
      ⟨fun hkx ↦ sSup_le fun k' hk' ↦ (hle k' hk').trans (e.le.trans (sInf_le ⟨hx, hkx⟩)),
        (le_sSup hk).trans⟩
  exact hC (by rw [e, hk']; exact h)

end CompleteLattice

/-! ### Commitment space semantics -/

variable {κ W : Type*} (C : Space (Set (Set W))) (O : κ → SetRel W W) (k : κ) (φ : Set W)
  {d : Set (Set W)}

/-- The assertion `C + k⊢φ` adds the proposition that `k` is committed to `φ`
([cohen-krifka-2014] (37), [krifka-2015] (14)). -/
def assert : Space (Set (Set W)) := C.update {committed O k φ}

theorem mem_assert :
    d ∈ C.assert O k φ ↔ d = (C.assert O k φ).root ∨ d ∈ C ∧ committed O k φ ∈ d :=
  or_congr_right (and_congr_right fun _ ↦ Set.singleton_subset_iff)

theorem committed_mem_root_assert : committed O k φ ∈ (C.assert O k φ).root :=
  Set.singleton_subset_iff.1 (C.le_root_update _)

theorem root_assert_of_mem (h : insert (committed O k φ) C.root ∈ C) :
    (C.assert O k φ).root = insert (committed O k φ) C.root :=
  C.root_update_of_mem h

theorem root_mem_assert_iff : C.root ∈ C.assert O k φ ↔ committed O k φ ∈ C.root :=
  C.root_mem_update_iff.trans Set.singleton_subset_iff

theorem committed_mem_of_mem_assert (hd : d ∈ C.assert O k φ) : committed O k φ ∈ d :=
  ((C.mem_assert O k φ).1 hd).elim (· ▸ C.committed_mem_root_assert O k φ) And.right

/-- The monopolar question proposes `k`'s commitment to `φ` ([krifka-2015] (27)). -/
def monopolarQuestion : Space (Set (Set W)) := C.question {{committed O k φ}}

/-- The bipolar question proposes `k`'s commitment to `φ` or to `¬φ` ([krifka-2015] (23)). -/
def bipolarQuestion : Space (Set (Set W)) := C.question {{committed O k φ}, {committed O k φᶜ}}

theorem mem_monopolarQuestion :
    d ∈ C.monopolarQuestion O k φ ↔ d = C.root ∨ d ∈ C ∧ committed O k φ ∈ d := by
  simp [monopolarQuestion, mem_question]

theorem mem_bipolarQuestion :
    d ∈ C.bipolarQuestion O k φ ↔
      d = C.root ∨ d ∈ C ∧ (committed O k φ ∈ d ∨ committed O k φᶜ ∈ d) := by
  simp [bipolarQuestion, mem_question]

/-- The bipolar question is the disjunction of the monopolar questions of `φ` and of `¬φ`
([krifka-2015] (31)). -/
theorem coe_bipolarQuestion :
    (C.bipolarQuestion O k φ : Set (Set (Set W))) =
      ↑(C.monopolarQuestion O k φ) ∪ ↑(C.monopolarQuestion O k φᶜ) := by
  rw [bipolarQuestion, Set.insert_eq, coe_question_union]
  rfl

/-! ### Projected commitments -/

/-- An act taking `C` to `D` projects `k`'s commitment on `φ` when every state of `D` beyond the
root of `C` carries `k⊢φ` or `k⊢¬φ`. The participant whose commitment to its content an act
projects is its epistemic authority ([coppock-wechsler-2018]). -/
def ProjectsCommitment (D : Space (Set (Set W))) : Prop :=
  ∀ d ∈ D, d ≠ C.root → committed O k φ ∈ d ∨ committed O k φᶜ ∈ d

/-- An assertion projects its author's commitment. -/
theorem projectsCommitment_assert : C.ProjectsCommitment O k φ (C.assert O k φ) := fun _ hd _ ↦
  .inl (C.committed_mem_of_mem_assert O k φ hd)

/-- A bipolar question projects the commitment of the participant it is put to. -/
theorem projectsCommitment_bipolarQuestion :
    C.ProjectsCommitment O k φ (C.bipolarQuestion O k φ) := fun _ hd hne ↦
  (((C.mem_bipolarQuestion O k φ).1 hd).resolve_left hne).2

variable {O k φ} {l : κ}

/-- In the space of all states, an assertion by `l` projects `k`'s commitment only when `l`'s
commitment to `φ` is `k`'s commitment to `φ` or to `¬φ`. -/
theorem projectsCommitment_Ici_assert_iff :
    (Space.Ici ∅).ProjectsCommitment O k φ ((Space.Ici ∅).assert O l φ) ↔
      committed O k φ = committed O l φ ∨ committed O k φᶜ = committed O l φ := by
  refine ⟨fun h ↦ h {committed O l φ} (((Space.Ici ∅).mem_assert O l φ).2
    (.inr ⟨Set.empty_subset _, rfl⟩)) (Set.singleton_ne_empty _), fun h d hd _ ↦ ?_⟩
  have hl := (Space.Ici ∅).committed_mem_of_mem_assert O l φ hd
  rcases h with h | h <;> simp only [h, hl, true_or, or_true]

/-- In the space of all states, a bipolar question put to `l` projects `k`'s commitment only when
`l`'s commitments to `φ` and to `¬φ` are each `k`'s commitment to `φ` or to `¬φ`. -/
theorem projectsCommitment_Ici_bipolarQuestion_iff :
    (Space.Ici ∅).ProjectsCommitment O k φ ((Space.Ici ∅).bipolarQuestion O l φ) ↔
      (committed O k φ = committed O l φ ∨ committed O k φᶜ = committed O l φ) ∧
        (committed O k φ = committed O l φᶜ ∨ committed O k φᶜ = committed O l φᶜ) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h d hd hne ↦ ?_⟩
  · exact h {committed O l φ} (((Space.Ici ∅).mem_bipolarQuestion O l φ).2
      (.inr ⟨Set.empty_subset _, .inl rfl⟩)) (Set.singleton_ne_empty _)
  · exact h {committed O l φᶜ} (((Space.Ici ∅).mem_bipolarQuestion O l φ).2
      (.inr ⟨Set.empty_subset _, .inr rfl⟩)) (Set.singleton_ne_empty _)
  · rcases (Space.Ici ∅).projectsCommitment_bipolarQuestion O l φ d hd hne with hl | hl
    · rcases h.1 with h | h <;> simp only [h, hl, true_or, or_true]
    · rcases h.2 with h | h <;> simp only [h, hl, true_or, or_true]

end Space

end Commitment
