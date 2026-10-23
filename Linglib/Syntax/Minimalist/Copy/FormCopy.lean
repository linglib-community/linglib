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

/-- The tree of lexical items and traces an object inscribes, forgetting which token fills each
leaf. -/
def erase (s : SyntacticObject) : UnorderedTree (Option LexicalItem ⊕ Option LexicalItem) :=
  s.val.map (Sum.map (Option.map LexicalItem.Token.item) (Option.map LexicalItem.Token.item))

@[simp]
theorem erase_leaf (tok : LexicalItem.Token) :
    (leaf tok).erase = UnorderedTree.leaf (.inl (some tok.item)) :=
  map_leaf _ _

@[simp]
theorem erase_trace : trace.erase = UnorderedTree.leaf (.inr none) :=
  map_leaf _ _

@[simp]
theorem erase_traceOf (tok : LexicalItem.Token) :
    (traceOf tok).erase = UnorderedTree.leaf (.inr (some tok.item)) :=
  map_leaf _ _

@[simp]
theorem erase_merge (l r : SyntacticObject) :
    (merge l r).erase = node (.inl none) {l.erase, r.erase} := by
  simp [erase, map_node]

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
  simp only [StructurallyIdentical, erase_merge] at *
  rw [hl, hr]

theorem StructurallyIdentical.numNodes_eq (h : StructurallyIdentical x y) :
    x.val.numNodes = y.val.numNodes := by
  simpa [erase] using congrArg UnorderedTree.numNodes h

/-- Two inscriptions are repetitions when they are structurally identical but distinct objects,
built from different tokens: the default relation between identical inscriptions. -/
def IsRepetition (x y : SyntacticObject) : Prop := StructurallyIdentical x y ∧ x ≠ y

instance : DecidableRel IsRepetition := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-! ### Fresh inscriptions -/

/-- The vertex map renaming the token of a lexical leaf or a trace by `f`. -/
def Vertex.mapToken (f : LexicalItem.Token → LexicalItem.Token) : Vertex → Vertex :=
  Sum.map (Option.map f) (Option.map f)

theorem isSyntacticObject_map_mapToken (f : LexicalItem.Token → LexicalItem.Token)
    (s : SyntacticObject) : IsSyntacticObject (s.val.map (Vertex.mapToken f)) := by
  induction s using ind with
  | leaf tok => exact (leaf (f tok)).2
  | trace => exact trace.2
  | traceOf tok => exact (traceOf (f tok)).2
  | merge l r hl hr =>
    convert (merge ⟨_, hl⟩ ⟨_, hr⟩).2 using 1
    simp [map_node, Vertex.mapToken]

/-- The object `s` with each of its tokens renamed by `f`. -/
def mapTokens (f : LexicalItem.Token → LexicalItem.Token) (s : SyntacticObject) :
    SyntacticObject :=
  ⟨s.val.map (Vertex.mapToken f), isSyntacticObject_map_mapToken f s⟩

variable {f : LexicalItem.Token → LexicalItem.Token}

@[simp]
theorem mapTokens_leaf (tok : LexicalItem.Token) : (leaf tok).mapTokens f = leaf (f tok) :=
  Subtype.ext (map_leaf _ _)

@[simp]
theorem mapTokens_trace : trace.mapTokens f = trace :=
  Subtype.ext (map_leaf _ _)

@[simp]
theorem mapTokens_traceOf (tok : LexicalItem.Token) :
    (traceOf tok).mapTokens f = traceOf (f tok) :=
  Subtype.ext (map_leaf _ _)

@[simp]
theorem mapTokens_merge (l r : SyntacticObject) :
    (merge l r).mapTokens f = merge (l.mapTokens f) (r.mapTokens f) :=
  Subtype.ext (by simp [mapTokens, map_node, Vertex.mapToken])

theorem erase_mapTokens (hf : ∀ t, (f t).item = t.item) (s : SyntacticObject) :
    (s.mapTokens f).erase = s.erase := by
  simp only [erase, mapTokens, map_map]
  congr 1
  funext v
  rcases v with (_ | t) | (_ | t) <;> simp [Vertex.mapToken, hf]

/-- The inscription of `s` from fresh tokens, each index raised by `k`, as External Merge
introduces a second inscription of an object. -/
def renumber (k : ℕ) : SyntacticObject → SyntacticObject :=
  mapTokens fun t ↦ ⟨t.item, t.id + k⟩

/-- A renumbered inscription is structurally identical to the original. -/
theorem structurallyIdentical_renumber (k : ℕ) (s : SyntacticObject) :
    StructurallyIdentical s (s.renumber k) :=
  (erase_mapTokens (f := fun t ↦ ⟨t.item, t.id + k⟩) (fun _ ↦ rfl) s).symm

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
  induction x using ind generalizing y with
  | leaf a =>
    rcases exists_form y with ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨l, r, rfl⟩ <;>
      have hv := congrArg UnorderedTree.value h <;> simp at hv
    exact congrArg leaf (hs (.inl hx) (.inl hy) hv)
  | trace =>
    rcases exists_form y with ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨l, r, rfl⟩ <;>
      have hv := congrArg UnorderedTree.value h <;> simp at hv
    rfl
  | traceOf a =>
    rcases exists_form y with ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨l, r, rfl⟩ <;>
      have hv := congrArg UnorderedTree.value h <;> simp at hv
    exact congrArg traceOf (hs (.inr hx) (.inr hy) hv)
  | merge l r ihl ihr =>
    rcases exists_form y with ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨l', r', rfl⟩
    iterate 3 (have hv := congrArg UnorderedTree.value h; simp at hv)
    have hc := congrArg UnorderedTree.children h
    simp only [erase_merge, children_node] at hc
    obtain ⟨hl, hr⟩ := mem_terms_of_merge_mem_terms hx
    obtain ⟨hl', hr'⟩ := mem_terms_of_merge_mem_terms hy
    rcases Multiset.pair_eq_pair_iff.1 hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [ihl hl hl' h₁, ihr hr hr' h₂]
    · rw [ihl hl hr' h₁, ihr hr hl' h₂, SyntacticObject.merge_comm]

/-- In such an object Form Copy relates each inscription only to itself: its copies are those
Internal Merge leaves. -/
theorem copyRel_subset_id (hs : s.HasDistinctItems) : s.copyRel ⊆ .id :=
  fun ⟨_, _⟩ ⟨hc, h⟩ ↦ h.eq_of_mem_terms hs hc.left_mem_terms hc.mem_terms

end Minimalist.SyntacticObject
