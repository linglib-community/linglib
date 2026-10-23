module

public import Linglib.Semantics.Reference.Iota

/-!
# De re attitudes by acquaintance

For Lewis the objects of attitudes are properties of centers, a subject at a time in a world, and
a relation the subject bears to things serves as a description: at each center it picks out the
unique thing the center bears it to, when there is one. A relation thus determines a partial
concept, of which a concept, a value at every center, is the total case. A subject ascribes a
property to a res under a partial concept when its value at her center is the res and every
alternative has the property of its value there; a de re belief is such an ascription under a
relation of acquaintance, and identity, the concept of the self, makes belief de se the case of
belief de re through identity.

## Main definitions

* `Acquaintance.relatum`: the partial concept of a relation, through the iota operator.
* `Acquaintance.deRe`: the property of having a value of a partial concept that has a property.
* `Acquaintance.AscribesUnder`: ascription of a property to a res under a partial concept.

## Main statements

* `Acquaintance.relatum_eq_some_iff`: a center's relatum is what it bears the relation to and
  nothing else to.
* `Acquaintance.mem_deRe_relatum_iff`: the de re property of a relation is the property of
  bearing it uniquely to something that has the property.
* `Acquaintance.relatum_eq`: a concept is the partial concept of the relation of identity with
  its values.
* `Acquaintance.ascribesUnder_comp_some`, `Acquaintance.ascribesUnder_comp_some_apply`: ascription
  under a concept, and ascription under identity as self-ascription.

## References

* [lewis-1979-attitudes]
* [cresswell-vonstechow-1982]
* [heim-1994-comments]
* [abusch-1997]
-/

@[expose] public section

namespace Acquaintance

variable {α C : Type*} {R : α → C → Prop} {k : C → Option α} {c : C → α} {P : α → Set C}
  {A : Set C} {p : C} {y : α}

/-- The relatum of the center `p` under `R` is the unique thing `p` bears `R` to, and `none` when
there is no such thing or several. -/
noncomputable def relatum (R : α → C → Prop) (p : C) : Option α := iota (R · p)

/-- The property of having a value under the partial concept `k` that has `P`, the centers that
do. -/
def deRe (k : C → Option α) (P : α → Set C) : Set C := {p | ∃ y ∈ k p, p ∈ P y}

/-- At the center `p`, with attitude alternatives `A`, the subject ascribes `P` to `y` under `k`
when `k` picks out `y` at her center and she self-ascribes the property of having a value under
`k` that has `P`, every alternative having it. -/
def AscribesUnder (A : Set C) (p : C) (k : C → Option α) (y : α) (P : α → Set C) : Prop :=
  k p = some y ∧ A ⊆ deRe k P

theorem relatum_eq_some_iff : relatum R p = some y ↔ R y p ∧ ∀ z, R z p → z = y :=
  iota_eq_some_iff _

theorem relatum_eq (c : C → α) : relatum (fun y p ↦ y = c p) = some ∘ c :=
  funext fun p ↦ iota_ident (c p)

theorem mem_deRe_iff_of_eq_some (h : k p = some y) : p ∈ deRe k P ↔ p ∈ P y :=
  ⟨fun ⟨_, hz, hP⟩ ↦ Option.some_inj.1 (h.symm.trans hz) ▸ hP, fun hP ↦ ⟨y, h, hP⟩⟩

theorem mem_deRe_relatum_iff :
    p ∈ deRe (relatum R) P ↔ ∃ y, (R y p ∧ ∀ z, R z p → z = y) ∧ p ∈ P y :=
  exists_congr fun _ ↦ and_congr_left' relatum_eq_some_iff

@[simp] theorem mem_deRe_comp_some : p ∈ deRe (some ∘ c) P ↔ p ∈ P (c p) :=
  mem_deRe_iff_of_eq_some rfl

theorem ascribesUnder_comp_some :
    AscribesUnder A p (some ∘ c) y P ↔ y = c p ∧ ∀ q ∈ A, q ∈ P (c q) :=
  and_congr (Option.some_inj.trans eq_comm)
    ⟨fun h _ hq ↦ mem_deRe_comp_some.1 (h hq), fun h _ hq ↦ mem_deRe_comp_some.2 (h _ hq)⟩

theorem ascribesUnder_comp_some_apply :
    AscribesUnder A p (some ∘ c) (c p) P ↔ ∀ q ∈ A, q ∈ P (c q) := by
  simp [ascribesUnder_comp_some]

end Acquaintance
