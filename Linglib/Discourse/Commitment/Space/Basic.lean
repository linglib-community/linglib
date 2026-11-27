module

public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.GaloisConnection.Defs
public import Mathlib.Order.UpperLower.Closure

/-!
# Commitment spaces

Let `S` be a partial order of states, in which a larger state carries more commitments. A
*commitment space* is a set of states with a least element, called its *root*. The root is the
current state of the conversation, and the other members are the states it may develop into.

A speech act changes the space. The *update* by a state `k` keeps the members above `k`, and its
root is their infimum. The *restriction* to a set `D` of states keeps the root and the members
that belong to `D`. Two restrictions have names. The *denegation* of `D` keeps the members
outside `D`, and the *question* with proposals `P` keeps the members above some member of `P`.

## Main definitions

* `Space S`: a commitment space with states in `S`.
* `Space.Ici c`: the space of all states above `c`.
* `Space.update C k`: the members of `C` above `k`, with their infimum as root.
* `Space.restrict C D`: the root of `C` and the members of `C` in `D`.
* `Space.denegate C D`: the root of `C` and the members of `C` outside `D`.
* `Space.question C P`: the root of `C` and the members of `C` above some member of `P`.

## Main results

* `Space.gc_root_Ici`: the root and the space of all states above a state form a Galois
  connection, `C ≤ Space.Ici c ↔ c ≤ C.root`.
* `Space.root_update_mem_iff`: the root of `C.update k` is a member of `C` if and only if the
  members of `C` above `k` have a least element.
* `Space.update_question_of_mem`: if `k ∈ P`, updating `C.question P` by `k` gives `C.update k`.
* `Space.coe_update_sSup`: the update by the supremum of a nonempty set of states is the
  intersection of the updates by its members, if the root of that update is a member of `C`.
* `Space.coe_denegate_inter`, `Space.coe_denegate_union`: De Morgan's laws for denegation.

## Implementation notes

The operations are total. A restriction always keeps the root. An update takes as its root the
infimum of the members above `k`, and adds that state when it is not already a member. That the
new root is a member of the space is a hypothesis of the results that need it, not an argument of
the update.

The root is a field although the set of states determines it, which makes a space a `SetLike`.

## References

* [cohen-krifka-2014]
* [krifka-2015]
* [van-der-leer-2026]
-/

@[expose] public section

namespace Commitment

/-- A **commitment space** is a set of states with a least element, its root. -/
structure Space (S : Type*) [LE S] where
  /-- The states of the space. -/
  carrier : Set S
  /-- The root, the current state. -/
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

/-- Commitment spaces are ordered by inclusion of their sets of states. -/
instance : PartialOrder (Space S) := .ofSetLike (Space S)

@[ext] theorem ext {C D : Space S} (h : ∀ c, c ∈ C ↔ c ∈ D) : C = D := SetLike.ext h

@[simp] theorem mem_carrier : c ∈ C.carrier ↔ c ∈ C := Iff.rfl

@[simp] theorem mem_mk {s : Set S} {r : S} (h : IsLeast s r) : c ∈ mk s r h ↔ c ∈ s := Iff.rfl

@[simp, norm_cast] theorem coe_mk {s : Set S} {r : S} (h : IsLeast s r) :
    (mk s r h : Set S) = s := rfl

protected theorem isLeast : IsLeast (C : Set S) C.root := C.isLeast'

theorem root_mem : C.root ∈ C := C.isLeast.1

theorem root_le (hc : c ∈ C) : C.root ≤ c := C.isLeast.2 hc

/-- The commitment space `{c}` has `c` as its only state. -/
instance : Singleton S (Space S) := ⟨fun c ↦ ⟨{c}, c, isLeast_singleton⟩⟩

@[simp, norm_cast] theorem coe_singleton (c : S) : (({c} : Space S) : Set S) = {c} := rfl

@[simp] theorem mem_singleton : d ∈ ({c} : Space S) ↔ d = c := Iff.rfl

@[simp] theorem root_singleton (c : S) : ({c} : Space S).root = c := rfl

/-- `Space.Ici c` is the commitment space of all states above `c`. -/
protected def Ici (c : S) : Space S := ⟨Set.Ici c, c, isLeast_Ici⟩

@[simp, norm_cast] theorem coe_Ici (c : S) : (Space.Ici c : Set S) = Set.Ici c := rfl

@[simp] theorem mem_Ici : d ∈ Space.Ici c ↔ c ≤ d := Iff.rfl

@[simp] theorem root_Ici (c : S) : (Space.Ici c).root = c := rfl

/-- A space is contained in the space of all states above `c` if and only if its root is above
`c`. -/
theorem le_Ici_iff : C ≤ Space.Ici c ↔ c ≤ C.root :=
  ⟨fun h ↦ h C.root_mem, fun h _ hd ↦ h.trans (C.root_le hd)⟩

/-- A smaller space has a larger root. -/
theorem root_le_root {C D : Space S} (h : C ≤ D) : D.root ≤ C.root := D.root_le (h C.root_mem)

/-- The root and the space of all states above a state form a Galois connection. -/
theorem gc_root_Ici : GaloisConnection (fun C : Space S ↦ OrderDual.toDual C.root)
    (fun c : Sᵒᵈ ↦ Space.Ici (OrderDual.ofDual c)) :=
  fun C c ↦ (C.le_Ici_iff (c := OrderDual.ofDual c)).symm

/-- The Galois connection between the root and the space of all states above a state is an
insertion: the root of `Space.Ici c` is `c`. -/
def giRootIci : GaloisInsertion (fun C : Space S ↦ OrderDual.toDual C.root)
    (fun c : Sᵒᵈ ↦ Space.Ici (OrderDual.ofDual c)) :=
  gc_root_Ici.toGaloisInsertion fun _ ↦ le_rfl

/-! ### Meta-speech acts -/

/-- The **restriction** of `C` to `D` has the root of `C` and the members of `C` that belong to `D`.
-/
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

/-- The **denegation** of `D` in `C` has the root of `C` and the members of `C` outside `D`
([cohen-krifka-2014] (26), [krifka-2015] (5), [van-der-leer-2026] Definition 22). -/
def denegate (D : Set S) : Space S := C.restrict Dᶜ

@[simp] theorem root_denegate (D : Set S) : (C.denegate D).root = C.root := rfl

@[simp] theorem mem_denegate : d ∈ C.denegate D ↔ d = C.root ∨ d ∈ C ∧ d ∉ D := Iff.rfl

theorem coe_denegate_of_root_notMem (h : C.root ∉ D) : (C.denegate D : Set S) = ↑C \ D :=
  C.coe_restrict_of_root_mem h

/-- If `D` is a set of members of `C` that does not contain the root, the members of `C` outside the
denegation of `D` are exactly `D` ([cohen-krifka-2014] (28)). -/
theorem sdiff_coe_denegate (hD : D ⊆ C) (h : C.root ∉ D) :
    (C : Set S) \ ↑(C.denegate D) = D := by
  rw [C.coe_denegate_of_root_notMem h, Set.sdiff_sdiff_cancel_left hD]

/-- The denegation of an intersection is the union of the denegations ([cohen-krifka-2014] (34)). -/
theorem coe_denegate_inter (D E : Set S) :
    (C.denegate (D ∩ E) : Set S) = ↑(C.denegate D) ∪ ↑(C.denegate E) := by
  rw [denegate, Set.compl_inter, coe_restrict_union]; rfl

/-- The denegation of a union is the intersection of the denegations ([cohen-krifka-2014] (35)). -/
theorem coe_denegate_union (D E : Set S) :
    (C.denegate (D ∪ E) : Set S) = ↑(C.denegate D) ∩ ↑(C.denegate E) := by
  rw [denegate, Set.compl_union, coe_restrict_inter]; rfl

/-- The **question** on `C` with proposals `P` has the root of `C` and the members of `C` above some
member of `P` ([krifka-2015] (23), (27)). -/
def question (P : Set S) : Space S := C.restrict (upperClosure P)

@[simp] theorem root_question (P : Set S) : (C.question P).root = C.root := rfl

theorem mem_question {P : Set S} : d ∈ C.question P ↔ d = C.root ∨ d ∈ C ∧ ∃ p ∈ P, p ≤ d :=
  .rfl

/-- A question with a proposal below the root is the space itself. -/
theorem question_eq_self {P : Set S} (h : ∃ p ∈ P, p ≤ C.root) : C.question P = C :=
  ext fun _ ↦ ⟨fun hd ↦ hd.elim (· ▸ C.root_mem) And.left, fun hd ↦
    let ⟨p, hp, hle⟩ := h; .inr ⟨hd, p, hp, hle.trans (C.root_le hd)⟩⟩

/-- The question with proposals `P ∪ Q` is the union of the questions with proposals `P` and `Q`
([krifka-2015] (31), (34)). -/
theorem coe_question_union (P Q : Set S) :
    (C.question (P ∪ Q) : Set S) = ↑(C.question P) ∪ ↑(C.question Q) := by
  rw [question, upperClosure_union, UpperSet.coe_inf, coe_restrict_union]
  rfl

end PartialOrder

/-! ### Basic speech acts -/

section CompleteLattice

variable {S : Type*} [CompleteLattice S] (C : Space S) {D : Set S} {k l d : S}

/-- The **update** of `C` by `k` has the members of `C` above `k`, with their infimum as root
([cohen-krifka-2014] (23), [krifka-2015] (2), (3)). -/
def update (k : S) : Space S :=
  ⟨insert (sInf (↑C ∩ Set.Ici k)) (↑C ∩ Set.Ici k), sInf (↑C ∩ Set.Ici k), Set.mem_insert _ _,
    Set.forall_mem_insert.2 ⟨le_rfl, fun _ hd ↦ sInf_le hd⟩⟩

theorem root_update (k : S) : (C.update k).root = sInf (↑C ∩ Set.Ici k) := rfl

@[simp] theorem mem_update : d ∈ C.update k ↔ d = (C.update k).root ∨ d ∈ C ∧ k ≤ d := Iff.rfl

theorem le_root_update (k : S) : k ≤ (C.update k).root := le_sInf fun _ hd ↦ hd.2

theorem root_le_root_update (k : S) : C.root ≤ (C.update k).root :=
  le_sInf fun _ hd ↦ C.root_le hd.1

theorem le_of_mem_update (h : d ∈ C.update k) : k ≤ d :=
  h.elim (fun e ↦ e ▸ C.le_root_update k) And.right

theorem root_le_of_mem_update (h : d ∈ C.update k) : C.root ≤ d :=
  h.elim (fun e ↦ e ▸ C.root_le_root_update k) fun h ↦ C.root_le h.1

/-- The root of the update of `C` by `k` is a member of `C` if and only if the members of `C` above
`k` have a least element. -/
theorem root_update_mem_iff : (C.update k).root ∈ C ↔ ∃ r, IsLeast (↑C ∩ Set.Ici k) r := by
  refine ⟨fun h ↦ ⟨_, ⟨h, C.le_root_update k⟩, fun _ hd ↦ sInf_le hd⟩, fun ⟨r, hr⟩ ↦ ?_⟩
  rw [root_update, hr.csInf_eq]
  exact hr.1.1

theorem root_update_of_mem (h : k ⊔ C.root ∈ C) : (C.update k).root = k ⊔ C.root :=
  IsLeast.csInf_eq ⟨⟨h, le_sup_left⟩, fun _ hd ↦ sup_le hd.2 (C.root_le hd.1)⟩

/-- If the root of the update of `C` by `k` is a member of `C`, the update consists of the members
of `C` above `k`. -/
theorem coe_update_of_root_mem (h : (C.update k).root ∈ C) :
    (C.update k : Set S) = ↑C ∩ Set.Ici k :=
  Set.insert_eq_of_mem ⟨h, C.le_root_update k⟩

theorem update_le (h : (C.update k).root ∈ C) : C.update k ≤ C := by
  rintro d (rfl | hd)
  exacts [h, hd.1]

theorem root_mem_update_iff : C.root ∈ C.update k ↔ k ≤ C.root :=
  ⟨fun h ↦ h.elim (fun e ↦ e ▸ C.le_root_update k) And.right, fun h ↦ Or.inr ⟨C.root_mem, h⟩⟩

/-- If `k ≤ l` and the root of the update by `l` is a member of `C`, the update by `l` is contained
in the update by `k` ([cohen-krifka-2014] (86)). -/
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

/-- Two updates commute when the root of each is a member of `C` ([cohen-krifka-2014] (31),
[krifka-2015] (6)). -/
theorem update_comm (hk : (C.update k).root ∈ C) (hl : (C.update l).root ∈ C) :
    (C.update k).update l = (C.update l).update k := by
  rw [C.update_update hk, C.update_update hl, sup_comm]

theorem restrict_coe_update (k : S) : C.restrict (C.update k) = C.restrict (Set.Ici k) := by
  ext d
  simp only [mem_restrict, SetLike.mem_coe, mem_update, Set.mem_Ici]
  refine or_congr_right (and_congr_right fun hd ↦ ⟨fun h ↦ ?_, fun h ↦ Or.inr ⟨hd, h⟩⟩)
  exact h.elim (fun e ↦ e ▸ C.le_root_update k) And.right

/-- The question with the single proposal `k` is the restriction of `C` to the states of its update
by `k` ([krifka-2015] (27)). -/
theorem question_singleton (k : S) : C.question {k} = C.restrict (C.update k) := by
  rw [question, restrict_coe_update, upperClosure_singleton, UpperSet.coe_Ici]

theorem update_restrict_of_subset (h : ↑C ∩ Set.Ici k ⊆ D) :
    (C.restrict D).update k = C.update k :=
  update_congr _ <| Set.ext fun _ ↦
    ⟨fun ⟨hd, hk⟩ ↦ ⟨hd.elim (fun e ↦ e ▸ C.root_mem) And.left, hk⟩,
      fun hd ↦ ⟨Or.inr ⟨hd.1, h hd⟩, hd.2⟩⟩

/-- If `k` is one of the proposals of a question on `C`, updating the question by `k` gives the
update of `C` by `k`. -/
theorem update_question_of_mem {P : Set S} (hk : k ∈ P) : (C.question P).update k = C.update k :=
  C.update_restrict_of_subset fun _ hd ↦ ⟨k, hk, hd.2⟩

/-- If the root of the update by the supremum of a nonempty set `K` is a member of `C`, that update
is the intersection of the updates by the members of `K` ([cohen-krifka-2014] (31)). -/
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

end Space

end Commitment
