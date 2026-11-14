module

public import Mathlib.Basic.Rel
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Form Copy

Two inscriptions of a syntactic object are structurally identical when they coincide once the
identity of their tokens is forgotten. By default structurally identical inscriptions are
repetitions, each interpreted on its own, as the two inscriptions of *many people* in *many
people praised many people*. Form Copy assigns the copy relation to such a pair when one
c-commands the other, and copies are interpreted as one element, as in the passive *many people
were praised*. Form Copy builds no structure: it is a relation on the inscriptions of an object.

Internal Merge leaves a copy in this sense, one object at two positions. Obligatory control is
Form Copy between an inscription merged into the controlling verb's theta position and a
repetition merged independently as the embedded subject, so that at Transfer control and raising
present the same configuration. Marcolli, Chomsky and Berwick model Form Copy as the restriction
of the operad action of Merge to a diagonal, the inputs at the identified positions being one
object, so that the coproduct extracts identified copies only together.

## Main definitions

* `SyntacticObject.erase`: the tree of lexical items an object inscribes, forgetting its tokens
* `SyntacticObject.StructurallyIdentical`: two inscriptions with one erasure
* `SyntacticObject.IsRepetition`: structurally identical inscriptions that are distinct objects
* `SyntacticObject.renumber`: an inscription of an object from fresh tokens
* `SyntacticObject.copyRel`: the copy relation Form Copy assigns in an object
* `SyntacticObject.HasDistinctItems`: no two tokens of an object inscribe one lexical item

## Main results

* `SyntacticObject.StructurallyIdentical.merge`: structural identity is a congruence for Merge
* `SyntacticObject.mk_mem_copyRel_merge`: Form Copy relates an object merged with a term to every
  structurally identical inscription inside that term
* `SyntacticObject.self_mem_copyRel_merge_iff`: the copy Internal Merge leaves is related to its
  antecedent, unless the whole object moves
* `SyntacticObject.structurallyIdentical_renumber`: a fresh inscription is structurally identical
  to the original
* `SyntacticObject.copyRel_subset_id`: in an object whose tokens inscribe distinct items, Form Copy
  relates each inscription only to itself

## Implementation notes

Syntactic objects are values, so a copy is one object at two vertices and a repetition two
objects with one erasure. Form Copy applies at the phase level, and the Phase Impenetrability
Condition bounds its reach further; that timing is not modelled.

## TODO

The modified coproduct on the diagonal, whose coassociativity Marcolli, Chomsky and Berwick
sketch through a Hopf algebra of graphs, and the deletion of the lower copy at externalization.

## References

* [chomsky-etal-2023]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.SyntacticObject

open UnorderedTree

variable {s t x y l r l' r' : SyntacticObject}

/-! ### Structural identity -/

/-- The syntactic object over lexical items that an object inscribes, forgetting which token fills
each leaf. -/
def erase (s : SyntacticObject) : SyntacticObject LexicalItem := s.map LexicalItem.Token.item

/-- Two inscriptions are structurally identical when they coincide once token identity is
forgotten. -/
def StructurallyIdentical (x y : SyntacticObject) : Prop := x.erase = y.erase

instance : DecidableRel StructurallyIdentical := fun x y ↦
  inferInstanceAs (Decidable (x.erase = y.erase))

theorem structurallyIdentical_equivalence : Equivalence StructurallyIdentical :=
  InvImage.equivalence _ _ eq_equivalence

@[refl]
theorem StructurallyIdentical.refl (x : SyntacticObject) : StructurallyIdentical x x := rfl

theorem StructurallyIdentical.symm (h : StructurallyIdentical x y) : StructurallyIdentical y x :=
  Eq.symm h

theorem StructurallyIdentical.trans (h : StructurallyIdentical x y)
    (h' : StructurallyIdentical y t) : StructurallyIdentical x t :=
  Eq.trans h h'

/-- Structural identity is a congruence for Merge. -/
theorem StructurallyIdentical.merge (hl : StructurallyIdentical l l')
    (hr : StructurallyIdentical r r') : StructurallyIdentical (merge l r) (merge l' r') := by
  simp only [StructurallyIdentical, erase, map_merge] at *
  rw [hl, hr]

theorem StructurallyIdentical.numNodes_eq (h : StructurallyIdentical x y) :
    x.toUnorderedTree.numNodes = y.toUnorderedTree.numNodes := by
  simpa [erase] using congrArg (·.toUnorderedTree.numNodes) h

/-- Two inscriptions are repetitions when they are structurally identical but distinct objects,
built from different tokens: the default relation between identical inscriptions. -/
def IsRepetition (x y : SyntacticObject) : Prop := StructurallyIdentical x y ∧ x ≠ y

instance : DecidableRel IsRepetition := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-! ### Fresh inscriptions -/

variable {f : LexicalItem.Token → LexicalItem.Token}

theorem erase_map (hf : ∀ t, (f t).item = t.item) (s : SyntacticObject) :
    (s.map f).erase = s.erase := by
  rw [erase, erase, map_map]
  exact congrArg (map · s) (funext hf)

/-- The inscription of `s` from fresh tokens, each index raised by `k`, as External Merge
introduces a second inscription of an object. -/
def renumber (k : ℕ) : SyntacticObject → SyntacticObject :=
  map fun t ↦ ⟨t.item, t.id + k⟩

/-- A renumbered inscription is structurally identical to the original. -/
theorem structurallyIdentical_renumber (k : ℕ) (s : SyntacticObject) :
    StructurallyIdentical s (s.renumber k) :=
  (erase_map (f := fun t ↦ ⟨t.item, t.id + k⟩) (fun _ ↦ rfl) s).symm

/-! ### The copy relation -/

/-- The copy relation Form Copy assigns in `s` holds of a pair of structurally identical
inscriptions, the first c-commanding the second. -/
def copyRel (s : SyntacticObject) : SetRel SyntacticObject SyntacticObject :=
  {p | CCommands s p.1 p.2 ∧ StructurallyIdentical p.1 p.2}

@[simp]
theorem mem_copyRel : (x, y) ∈ s.copyRel ↔ CCommands s x y ∧ StructurallyIdentical x y :=
  Iff.rfl

instance (s : SyntacticObject) (p : SyntacticObject × SyntacticObject) :
    Decidable (p ∈ s.copyRel) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Form Copy relates an object merged with a term to every structurally identical inscription
inside that term: the configuration of control, where the lower inscription is a repetition. -/
theorem mk_mem_copyRel_merge (h : Contains t y) (hxy : StructurallyIdentical x y) :
    (x, y) ∈ (merge x t).copyRel := by
  refine ⟨cCommands_merge_left ?_ (mem_terms.2 (Relation.TransGen.to_reflTransGen h)), hxy⟩
  rintro rfl
  exact (numNodes_lt_of_contains h).ne hxy.numNodes_eq.symm

theorem self_mem_copyRel_merge (h : Contains t x) : (x, x) ∈ (merge x t).copyRel :=
  mk_mem_copyRel_merge h rfl

/-- A term merged with the object it is a term of is related to itself exactly when it is a proper
term: an object merged with itself c-commands nothing. -/
theorem self_mem_copyRel_merge_iff (hx : x ∈ t.terms) : (x, x) ∈ (merge x t).copyRel ↔ x ≠ t := by
  refine ⟨?_, fun hne ↦ self_mem_copyRel_merge
    ((containsOrEq_iff_eq_or_contains.1 (mem_terms.1 hx)).resolve_left hne)⟩
  rintro ⟨⟨z, -, hxz, -⟩, -⟩ rfl
  obtain ⟨-, -, -, -, hne⟩ := id hxz
  rcases Sisters.of_merge hxz with ⟨w, hw, hwx, -⟩ | ⟨w, hw, hwx, -⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact contains_irrefl x (Relation.TransGen.tail' (mem_terms.1 hw) hwx)
  · exact contains_irrefl x (Relation.TransGen.tail' (mem_terms.1 hw) hwx)
  all_goals exact hne rfl

/-! ### Objects without repetitions -/

/-- No two distinct tokens of `s` inscribe one lexical item, at a leaf or at a trace. -/
def HasDistinctItems (s : SyntacticObject) : Prop :=
  ∀ ⦃a b : LexicalItem.Token⦄, (leaf a ∈ s.terms ∨ traceOf a ∈ s.terms) →
    (leaf b ∈ s.terms ∨ traceOf b ∈ s.terms) → a.item = b.item → a = b

theorem StructurallyIdentical.eq_of_mem_terms (hs : s.HasDistinctItems) (hx : x ∈ s.terms)
    (hy : y ∈ s.terms) (h : StructurallyIdentical x y) : x = y := by
  replace h : x.map LexicalItem.Token.item = y.map LexicalItem.Token.item := h
  induction x using ind generalizing y with
  | leaf a =>
    rcases exists_form y with ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨l, r, rfl⟩ <;>
      simp only [map_leaf, map_trace, map_traceOf, map_merge] at h
    · exact congrArg leaf (hs (.inl hx) (.inl hy) (leaf_inj.1 h))
    · exact absurd h (leaf_ne_trace _)
    · exact absurd h (leaf_ne_labelledTrace _ _)
    · exact absurd h (leaf_ne_merge _ _ _)
  | trace =>
    rcases exists_form y with ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨l, r, rfl⟩ <;>
      simp only [map_leaf, map_trace, map_traceOf, map_merge] at h
    · exact absurd h.symm (leaf_ne_trace _)
    · rfl
    · exact absurd h (trace_ne_labelledTrace _)
    · exact absurd h (trace_ne_merge _ _)
  | traceOf a =>
    rcases exists_form y with ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨l, r, rfl⟩ <;>
      simp only [map_leaf, map_trace, map_traceOf, map_merge] at h
    · exact absurd h (labelledTrace_ne_leaf _ _)
    · exact absurd h.symm (trace_ne_labelledTrace _)
    · exact congrArg traceOf (hs (.inr hx) (.inr hy) (labelledTrace_inj.1 h))
    · exact absurd h (labelledTrace_ne_merge _ _ _)
  | merge l r ihl ihr =>
    rcases exists_form y with ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨l', r', rfl⟩ <;>
      simp only [map_leaf, map_trace, map_traceOf, map_merge] at h
    · exact absurd h.symm (leaf_ne_merge _ _ _)
    · exact absurd h.symm (trace_ne_merge _ _)
    · exact absurd h.symm (labelledTrace_ne_merge _ _ _)
    · obtain ⟨hl, hr⟩ := mem_terms_of_merge_mem_terms hx
      obtain ⟨hl', hr'⟩ := mem_terms_of_merge_mem_terms hy
      rcases merge_eq_merge_iff.1 h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [ihl hl hl' h₁, ihr hr hr' h₂]
      · rw [ihl hl hr' h₁, ihr hr hl' h₂, SyntacticObject.merge_comm]

/-- In such an object Form Copy relates each inscription only to itself: its copies are those
Internal Merge leaves. -/
theorem copyRel_subset_id (hs : s.HasDistinctItems) : s.copyRel ⊆ .id :=
  fun ⟨_, _⟩ ⟨hc, h⟩ ↦ h.eq_of_mem_terms hs hc.left_mem_terms hc.mem_terms

end Minimalist.SyntacticObject
