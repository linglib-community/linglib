module

public import Linglib.Semantics.Dynamic.DRT.Sheaf.Context
public import Linglib.Semantics.Dynamic.DRT.Syntax
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.Data.Finset.Sort

/-!
# The presheaf of basic DRSs

This file defines the presheaf of basic discourse representation structures on the category of
contexts. Sets of literals over contexts form a presheaf, restricting along a context morphism `f`
by preimage under renaming, `F(f)(s) ⊢ ±A(x̄) ⟺ s ⊢ ±A(f(x̄))`; the consistent sets form a
subpresheaf, whose sections at a context `(L, X)`, the DRSs over it, are the basic DRSs `(X, s)`.
`Context.DRS.toDRS` realises a section as a `DRS` whose conditions are literals.

## Implementation notes

Abramsky and Sadrzadeh take the deductive closures of consistent finite sets of literals; in a
relational language the closure adds no literal, so a section is the consistent set itself.

## References

* [abramsky-sadrzadeh-2014]
* [kamp-reyle-1993]
-/

@[expose] public section

open CategoryTheory FirstOrder Opposite

namespace DRT

universe u v w

variable {L : Language.{u, v}} {V : Type w}

/-- A condition is a literal when it is an atom or the negation of a one-atom box with no
referents. -/
def Condition.IsLiteral : Condition L V → Prop
  | .atom _ => True
  | .neg K => K.referents = ∅ ∧ ∃ a, K.conditions = [.atom a]
  | _ => False

/-- A DRS is basic when every condition is a literal. -/
def DRS.IsBasic (K : DRS L V) : Prop := ∀ d ∈ K.conditions, d.IsLiteral

namespace Literal

variable {c c' : Context L V}

/-- The atom of a literal, over the referents. -/
def atom (l : Literal c) : L.Atom V := ⟨l.rel.1.2, fun i => l.args i⟩

/-- `l.toCondition` is the atom of `l`, or for a negative literal the negation of the one-atom
box with no referents. -/
def toCondition (l : Literal c) : Condition L V :=
  if l.pos then .atom l.atom else .neg ⟨∅, [.atom l.atom]⟩

/-- Renaming a literal is `Condition.map` along the extended referent map. -/
theorem toCondition_map [DecidableEq V] (f : c ⟶ c') (l : Literal c) :
    (l.map f).toCondition = l.toCondition.map f.extend := by
  cases hp : l.pos <;>
    simp [toCondition, atom, map, Condition.map, DRS.map, hp, Function.comp_def, Language.Atom.map]

theorem consistent_empty : Consistent (∅ : Finset (Literal c)) := by simp [Consistent]

theorem consistent_singleton (l : Literal c) : Consistent {l} := by
  simpa [Consistent] using neg_ne_self l

variable [DecidableEq V] [∀ n, DecidableEq (L.Relations n)]

/-- `preimage f s` holds the literals whose renaming along `f` is in `s`. -/
def preimage (f : c ⟶ c') (s : Finset (Literal c')) : Finset (Literal c) :=
  Finset.univ.filter fun l ↦ l.map f ∈ s

@[simp] theorem mem_preimage {f : c ⟶ c'} {s : Finset (Literal c')} {l : Literal c} :
    l ∈ preimage f s ↔ l.map f ∈ s := by
  simp [preimage]

theorem Consistent.preimage {s : Finset (Literal c')} (hs : Consistent s) (f : c ⟶ c') :
    Consistent (preimage f s) :=
  fun _ hl hn ↦ hs _ (mem_preimage.1 hl) (mem_preimage.1 hn)

/-- A set of literals is consistent when each of its literals renames a literal along a morphism
whose preimage of the set is consistent. -/
theorem Consistent.of_preimage {s : Finset (Literal c)}
    (h : ∀ l ∈ s, ∃ (Y : Context L V) (f : Y ⟶ c), (∃ m : Literal Y, m.map f = l) ∧
      Consistent (Literal.preimage f s)) :
    Consistent s := by
  intro l hl hn
  obtain ⟨Y, f, ⟨m, rfl⟩, hf⟩ := h l hl
  exact hf m (mem_preimage.2 hl) (mem_preimage.2 (by rwa [← neg_map]))

end Literal

namespace Context

/-- A DRS over a context is a consistent set of its literals, the conditions of the basic DRS
`(X, s)` on the context's referents; a section of `Context.DRS.presheaf`. -/
abbrev DRS (c : Context L V) := {s : Finset (Literal c) // Literal.Consistent s}

namespace DRS

variable {c : Context L V}

/-- `s.toDRS` is the basic DRS `(X, s)`, with the context's referents and the literals as
conditions. -/
noncomputable def toDRS (s : c.DRS) : DRT.DRS L V :=
  ⟨c.vars, s.1.toList.map Literal.toCondition⟩

@[simp] theorem referents_toDRS (s : c.DRS) : s.toDRS.referents = c.vars := rfl

theorem coe_conditions_toDRS (s : c.DRS) :
    (s.toDRS.conditions : Multiset (Condition L V)) = s.1.val.map Literal.toCondition := by
  simp [toDRS, ← Multiset.map_coe]

theorem isBasic_toDRS (s : c.DRS) : s.toDRS.IsBasic := by
  rintro _ hd
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hd
  unfold Literal.toCondition
  split
  · trivial
  · exact ⟨rfl, _, rfl⟩

end DRS

variable (L V) [DecidableEq V] [∀ n, DecidableEq (L.Relations n)]

/-- Sets of literals form a presheaf on contexts, restricting by preimage under renaming. -/
abbrev literalSets : (Context L V)ᵒᵖ ⥤ Type (max v w) where
  obj c := Finset (Literal c.unop)
  map f := TypeCat.ofHom (Literal.preimage f.unop)

/-- The consistent sets of literals form a subpresheaf of the literal sets. -/
def consistentLiteralSets : Subfunctor (literalSets L V) where
  obj _ := {s | Literal.Consistent s}
  map f _ hs := hs.preimage f.unop

/-- DRSs over contexts form the presheaf of consistent sets of literals. -/
abbrev DRS.presheaf : (Context L V)ᵒᵖ ⥤ Type (max v w) := (consistentLiteralSets L V).toFunctor

variable {L V}

@[simp] theorem literalSets_map {c c' : (Context L V)ᵒᵖ} (f : c ⟶ c')
    (s : Finset (Literal c.unop)) :
    (literalSets L V).map f s = Literal.preimage f.unop s :=
  rfl

namespace DRS

variable {c c' : Context L V}

/-- `s.restrict f` holds `±A(x̄)` iff `s` holds `±A(f(x̄))`. -/
def restrict (f : c ⟶ c') (s : c'.DRS) : c.DRS :=
  ⟨Literal.preimage f s.1, s.2.preimage f⟩

@[simp] theorem mem_restrict {f : c ⟶ c'} {s : c'.DRS} {l : Literal c} :
    l ∈ (s.restrict f).1 ↔ l.map f ∈ s.1 :=
  Literal.mem_preimage

@[simp] theorem presheaf_map {c c' : (Context L V)ᵒᵖ} (f : c ⟶ c') (s : c.unop.DRS) :
    (presheaf L V).map f s = s.restrict f.unop :=
  rfl

end DRS

end Context

end DRT
