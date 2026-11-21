module

public import Linglib.Semantics.Exhaustification.Basic

/-!
# Krifka (1995): The Semantics and Pragmatics of Polarity Items

A polarity item introduces alternatives, and its distribution follows from how the proposition
it yields is ordered with respect to the alternative propositions, together with the kind of
assertion made.

A *BFA structure* is a triple of a background `B`, a foreground `F` and a set `A` of alternatives
to the foreground. Its proposition is `B F`, and each alternative `F'` gives the alternative
proposition `B F'`. An operator applied to a BFA structure applies to its background and leaves
the foreground and the alternatives as they are (`BFA.map`), so a monotone operator keeps the
order between the proposition and its alternatives and an antitone one reverses it.

For a common ground `c`, the *scalar assertion* of a BFA structure keeps the worlds of
`c ∩ B F` at which no alternative `F'` with `c ∩ B F' ⊂ c ∩ B F` holds (`BFA.scalAssert`).
Where every alternative proposition is comparable with the proposition in `c`, this is the
exhaustification of `c ∩ B F` against the alternatives (`BFA.scalAssert_eq_exh`). It is `c ∩ B F`
when the proposition entails its alternatives (`BFA.scalAssert_eq_of_forall_subset`), as under
negation, and it is empty when the alternatives are strictly stronger and cover the proposition
(`BFA.scalAssert_eq_empty`). The second is the case of a weak polarity item in a positive
sentence, whose alternatives together make up its foreground.

The *emphatic assertion* of a BFA structure is defined when its proposition is less likely than
each alternative proposition and less likely than their conjunction (`BFA.EmphAssertable`). For
a likelihood on which a less likely comparable proposition is strictly stronger, the proposition
is then strictly stronger than each alternative and than their conjunction
(`BFA.EmphAssertable.ssubset`, `BFA.EmphAssertable.ssubset_iInter`). So an emphatic assertion is
undefined where an alternative entails the proposition (`BFA.EmphAssertable.not_subset`), and
under negation it is undefined where the alternatives cover the proposition
(`BFA.not_emphAssertable_map_compl`): a strong polarity item has alternatives that do not make
up its foreground.

## Implementation notes

* The foreground and its alternatives have an arbitrary type `D`, and the background is a
  function from `D` to propositions. The source requires that the foreground not be among the
  alternatives and remarks that nothing of theoretical importance hinges on it; the requirement
  is not a field here.
* `BFA.map` is the rule for applying an operator to a BFA structure. The rule for applying a BFA
  structure to an argument is not stated, since the background here already yields a proposition.
* The likelihood `p <_c q` is a relation `lt` on propositions, and the common ground enters by
  intersection.
* `BFA.scalAssert_eq_empty` has as a hypothesis that the alternatives are strictly stronger than
  the proposition in the common ground, which the definition of scalar assertion asks of each
  alternative it removes.

## TODO

* The examples and their judgments, and the items of the later sections (expressions of minimal
  or maximal quantity, positive polarity items, questions), are not treated.

## References

* [krifka-1995a]
-/

@[expose] public section

namespace Krifka1995

open Exhaustification

variable {W D : Type*}

/-- A BFA structure: a background, a foreground and the alternatives to the foreground. -/
structure BFA (W D : Type*) where
  /-- The background, which applies to the foreground and to its alternatives. -/
  background : D → Set W
  /-- The foreground, the polarity item or the item in focus. -/
  foreground : D
  /-- The alternatives to the foreground. -/
  alternatives : Set D

namespace BFA

variable {s : BFA W D} {c : Set W} {F' : D} {α : Set W → Set W}

/-- The proposition of a BFA structure, the background applied to the foreground. -/
def prop (s : BFA W D) : Set W := s.background s.foreground

/-- (25a): An operator applies to the background of a BFA structure. -/
@[simps] def map (α : Set W → Set W) (s : BFA W D) : BFA W D :=
  ⟨α ∘ s.background, s.foreground, s.alternatives⟩

@[simp] theorem prop_map (α : Set W → Set W) (s : BFA W D) : (s.map α).prop = α s.prop := rfl

theorem map_map (α β : Set W → Set W) (s : BFA W D) : (s.map α).map β = s.map (β ∘ α) := rfl

@[simp] theorem map_id (s : BFA W D) : s.map id = s := rfl

/-! ### Scalar assertion -/

/-- (31b): The scalar assertion of a BFA structure restricts the common ground to the worlds of
its proposition at which no alternative that is strictly stronger in the common ground holds. -/
def scalAssert (s : BFA W D) (c : Set W) : Set W :=
  {i | i ∈ c ∧ i ∈ s.prop ∧
    ¬ ∃ F' ∈ s.alternatives, c ∩ s.background F' ⊂ c ∩ s.prop ∧ i ∈ s.background F'}

theorem scalAssert_subset (s : BFA W D) (c : Set W) : s.scalAssert c ⊆ c ∩ s.prop :=
  fun _ h ↦ ⟨h.1, h.2.1⟩

/-- (31a): The alternative propositions are informationally ordered with respect to the
proposition in the common ground. -/
def IsOrdered (s : BFA W D) (c : Set W) : Prop :=
  ∀ F' ∈ s.alternatives, c ∩ s.background F' ⊆ c ∩ s.prop ∨ c ∩ s.prop ⊆ c ∩ s.background F'

/-- Where the alternative propositions are informationally ordered, scalar assertion is the
exhaustification of the proposition against them in the common ground. -/
theorem scalAssert_eq_exh (h : s.IsOrdered c) :
    s.scalAssert c = exh ((fun F' ↦ c ∩ s.background F') '' s.alternatives) (c ∩ s.prop) := by
  ext i
  constructor
  · rintro ⟨hc, hp, hn⟩
    refine ⟨⟨hc, hp⟩, ?_⟩
    rintro _ ⟨F', hF', rfl⟩ hi
    exact (h F' hF').elim
      (fun hle ↦ of_not_not fun hnot ↦ hn ⟨F', hF', ⟨hle, hnot⟩, hi.2⟩) id
  · rintro ⟨⟨hc, hp⟩, hall⟩
    exact ⟨hc, hp, fun ⟨F', hF', hss, hi⟩ ↦ hss.2 (hall _ ⟨F', hF', rfl⟩ ⟨hc, hi⟩)⟩

/-- (33): Where the proposition entails every alternative proposition in the common ground,
scalar assertion adds the proposition and nothing else. -/
theorem scalAssert_eq_of_forall_subset
    (h : ∀ F' ∈ s.alternatives, c ∩ s.prop ⊆ c ∩ s.background F') :
    s.scalAssert c = c ∩ s.prop :=
  (scalAssert_subset s c).antisymm fun _ hi ↦
    ⟨hi.1, hi.2, fun ⟨F', hF', hss, _⟩ ↦ hss.2 (h F' hF')⟩

/-- (32): Where every alternative proposition is strictly stronger than the proposition in the
common ground and the alternatives cover it, scalar assertion yields the empty common ground. -/
theorem scalAssert_eq_empty (hlt : ∀ F' ∈ s.alternatives, c ∩ s.background F' ⊂ c ∩ s.prop)
    (hcover : c ∩ s.prop ⊆ ⋃ F' ∈ s.alternatives, s.background F') : s.scalAssert c = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hi ↦
    let ⟨F', hF', hiF'⟩ := Set.mem_iUnion₂.1 (hcover ⟨hi.1, hi.2.1⟩)
    hi.2.2 ⟨F', hF', hlt F' hF', hiF'⟩

-- (27): Under negation the proposition entails the alternatives it was entailed by.
theorem scalAssert_map_compl (h : ∀ F' ∈ s.alternatives, s.background F' ⊆ s.prop) :
    (s.map compl).scalAssert c = c ∩ s.propᶜ :=
  scalAssert_eq_of_forall_subset fun F' hF' ↦
    Set.inter_subset_inter_right c (Set.compl_subset_compl.2 (h F' hF'))

/-! ### Emphatic assertion -/

/-- (40): The emphatic assertion of a BFA structure is defined when its proposition is less
likely in the common ground than each alternative proposition and than their conjunction. -/
structure EmphAssertable (lt : Set W → Set W → Prop) (s : BFA W D) (c : Set W) : Prop where
  /-- (a): The proposition is less likely than each alternative proposition. -/
  lt_of_mem : ∀ F' ∈ s.alternatives, lt (c ∩ s.prop) (c ∩ s.background F')
  /-- (b): The proposition is less likely than the conjunction of the alternative
  propositions. -/
  lt_iInter : lt (c ∩ s.prop) (⋂ F' ∈ s.alternatives, c ∩ s.background F')

namespace EmphAssertable

variable {lt : Set W → Set W → Prop}
  (hlt : ∀ p q : Set W, p ⊆ q ∨ q ⊆ p → lt p q → p ⊂ q)

include hlt

-- (41a)
theorem ssubset (h : EmphAssertable lt s c) (hF' : F' ∈ s.alternatives)
    (hcomp : c ∩ s.prop ⊆ c ∩ s.background F' ∨ c ∩ s.background F' ⊆ c ∩ s.prop) :
    c ∩ s.prop ⊂ c ∩ s.background F' :=
  hlt _ _ hcomp (h.lt_of_mem F' hF')

-- (41b)
theorem ssubset_iInter (h : EmphAssertable lt s c) (hord : s.IsOrdered c) :
    c ∩ s.prop ⊂ ⋂ F' ∈ s.alternatives, c ∩ s.background F' :=
  hlt _ _ (.inl (Set.subset_iInter₂ fun F' hF' ↦ (h.ssubset hlt hF' (hord F' hF').symm).1))
    h.lt_iInter

/-- (45b): An emphatic assertion is not defined where an alternative proposition entails the
proposition. -/
theorem not_subset (h : EmphAssertable lt s c) (hF' : F' ∈ s.alternatives) :
    ¬ c ∩ s.background F' ⊆ c ∩ s.prop :=
  fun hle ↦ (h.ssubset hlt hF' (.inr hle)).2 hle

end EmphAssertable

/-- (38): Under negation an emphatic assertion is not defined where the alternatives cover the
proposition and each entails it, so the alternatives of a strong polarity item are not
exhaustive. -/
theorem not_emphAssertable_map_compl {lt : Set W → Set W → Prop}
    (hlt : ∀ p q : Set W, p ⊆ q ∨ q ⊆ p → lt p q → p ⊂ q)
    (hsub : ∀ F' ∈ s.alternatives, s.background F' ⊆ s.prop)
    (hcover : s.prop ⊆ ⋃ F' ∈ s.alternatives, s.background F') (hne : s.alternatives.Nonempty) :
    ¬ EmphAssertable lt (s.map compl) c := fun h ↦ by
  have hord : (s.map compl).IsOrdered c := fun F' hF' ↦
    .inr (Set.inter_subset_inter_right c (Set.compl_subset_compl.2 (hsub F' hF')))
  refine (h.ssubset_iInter hlt hord).2 fun i hi ↦ ?_
  obtain ⟨F₀, hF₀⟩ := hne
  have hic : i ∈ c := (Set.mem_iInter₂.1 hi F₀ hF₀).1
  refine ⟨hic, fun hip ↦ ?_⟩
  obtain ⟨F', hF', hiF'⟩ := Set.mem_iUnion₂.1 (hcover hip)
  exact (Set.mem_iInter₂.1 hi F' hF').2 hiF'

end BFA

end Krifka1995
