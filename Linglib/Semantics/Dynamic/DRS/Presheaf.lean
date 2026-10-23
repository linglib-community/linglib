module

public import Linglib.Semantics.Dynamic.DRS.Basic
public import Linglib.Semantics.Dynamic.DRS.Context
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.Data.Finset.Sort

/-!
# The presheaf of basic DRSs

This file defines the presheaf of basic discourse representation structures on the category of
contexts: at a context `(L, X)` its sections are the consistent finite sets of literals over the
context, and restriction along a context morphism `f` is substitution-preimage,
`F(f)(s) ⊢ ±A(x̄) ⟺ s ⊢ ±A(f(x̄))`. A section `s` at `(L, X)` is the basic DRS `(X, s)`, which
`Theory.toDRS` realises as a `DRS` whose conditions are literals.

## Main definitions

* `DRT.Theory`: consistent finite sets of literals over a context, with `Theory.restrict`.
* `DRT.presheaf`: the presheaf `(Context L V)ᵒᵖ ⥤ Type`.
* `DRT.Literal.toCondition`, `DRT.Theory.toDRS`: literals as DRS-conditions, sections as basic
  DRSs.

## Main statements

* `DRT.Literal.toCondition_map`: renaming a literal is `Condition.map` along the extended
  referent map.
* `DRT.Theory.isBasic_toDRS`: sections realise as basic DRSs.

## Implementation notes

Abramsky and Sadrzadeh take the deductive closures of consistent finite sets of literals; in a
relational language the closure adds no literal, so a section is the consistent set itself.

## References

* [abramsky-sadrzadeh-2014]
* [kamp-reyle-1993]
-/

@[expose] public section

open CategoryTheory FirstOrder

namespace DRT

universe u v w

variable {L : Language.{u, v}} {V : Type w}

/-- A theory over a context is a consistent finite set of literals, the conditions of a basic
DRS. -/
@[ext] structure Theory (c : Context L V) where
  /-- The literals held true. -/
  lits : Finset (Literal c)
  /-- No literal occurs with both signs. -/
  consistent : Literal.Consistent lits

/-- A condition is a literal when it is an atom or the negation of a one-atom box with no
referents. -/
def Condition.IsLiteral : Condition L V → Prop
  | .atom _ => True
  | .neg K => K.referents = ∅ ∧ ∃ a, K.conditions = [.atom a]
  | _ => False

/-- A DRS is basic when every condition is a literal. -/
def DRS.IsBasic (K : DRS L V) : Prop := ∀ d ∈ K.conditions, d.IsLiteral

/-- The atom of a literal, over the referents. -/
def Literal.atom {c : Context L V} (l : Literal c) : L.Atom V := ⟨l.rel.1.2, fun i => l.args i⟩

/-- `l.toCondition` is the atom of `l`, or for a negative literal the negation of the one-atom
box with no referents. -/
def Literal.toCondition {c : Context L V} (l : Literal c) : Condition L V :=
  if l.pos then .atom l.atom else .neg ⟨∅, [.atom l.atom]⟩

theorem Literal.toCondition_map [DecidableEq V] {c c' : Context L V} (f : c ⟶ c')
    (l : Literal c) : (l.map f).toCondition = l.toCondition.map f.extend := by
  cases hp : l.pos <;>
    simp [toCondition, atom, map, Condition.map, DRS.map, hp, Function.comp_def, Language.Atom.map]

namespace Theory

variable {c c' : Context L V}

instance : Bot (Theory c) := ⟨⟨∅, by simp [Literal.Consistent]⟩⟩

@[simp] theorem lits_bot : (⊥ : Theory c).lits = ∅ := rfl

/-- `s.toDRS` is the basic DRS `(X, s)`, with the context's referents and the literals as
conditions. -/
noncomputable def toDRS (s : Theory c) : DRS L V := ⟨c.vars, s.lits.toList.map Literal.toCondition⟩

@[simp] theorem referents_toDRS (s : Theory c) : s.toDRS.referents = c.vars := rfl

theorem coe_conditions_toDRS (s : Theory c) :
    (s.toDRS.conditions : Multiset (Condition L V)) = s.lits.val.map Literal.toCondition := by
  simp [toDRS, ← Multiset.map_coe]

theorem isBasic_toDRS (s : Theory c) : s.toDRS.IsBasic := by
  rintro _ hd
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hd
  unfold Literal.toCondition
  split
  · trivial
  · exact ⟨rfl, _, rfl⟩

variable [DecidableEq V] [∀ n, DecidableEq (L.Relations n)]

instance : DecidableEq (Theory c) := fun _ _ => decidable_of_iff _ Theory.ext_iff.symm

/-- `s.restrict f` holds `±A(x̄)` iff `s` holds `±A(f(x̄))`. -/
def restrict (f : c ⟶ c') (s : Theory c') : Theory c where
  lits := Finset.univ.filter fun l => l.map f ∈ s.lits
  consistent _ hl hn := s.consistent _ (Finset.mem_filter.1 hl).2 (Finset.mem_filter.1 hn).2

@[simp] theorem mem_restrict {f : c ⟶ c'} {s : Theory c'} {l : Literal c} :
    l ∈ (s.restrict f).lits ↔ l.map f ∈ s.lits := by simp [restrict]

@[simp] theorem restrict_bot (f : c ⟶ c') : (⊥ : Theory c').restrict f = ⊥ := by
  ext; simp

end Theory

variable (L V) [DecidableEq V] [∀ n, DecidableEq (L.Relations n)]

/-- Basic DRSs form a presheaf on contexts, restricting along context morphisms. -/
def presheaf : (Context L V)ᵒᵖ ⥤ Type (max v w) where
  obj c := Theory c.unop
  map f := TypeCat.ofHom fun s => s.restrict f.unop

variable {L V}

@[simp] theorem presheaf_obj (c : (Context L V)ᵒᵖ) : (presheaf L V).obj c = Theory c.unop := rfl

@[simp] theorem presheaf_map {c c' : (Context L V)ᵒᵖ} (f : c ⟶ c') (s : Theory c.unop) :
    (presheaf L V).map f s = s.restrict f.unop := rfl

end DRT
