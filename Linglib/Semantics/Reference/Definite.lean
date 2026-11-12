module

public import Linglib.Logic.Trivalent.Part
public import Linglib.Semantics.Reference.Character

/-!
# Definite denotations

A pronoun, a definite description, a demonstrative and a bound variable denote, at a context and
a world, at most one individual. This is the partial denotation of Heim and Kratzer: an
expression whose presupposition fails denotes nothing, a feature of a pronoun is a partial
identity function that narrows where it denotes, and the kinds of definite differ only in how the
individual is chosen, as Büring argues. Predicating a scope of a definite gives
[a trivalent proposition](##Definite.toTrivalent), undefined where the definite denotes nothing.
A [variable restricted to a domain](##Definite.var) denotes the assignment's value at its index
where that value lies in the domain. A character is the definite that denotes everywhere, and it
is directly referential exactly when [that definite is rigid at every
context](##Kaplan.Character.isDirectlyReferential_iff).

## Implementation notes

A two-dimensional account, on which a presupposition is stored beside a value that is defined
either way, is finer than this one and maps onto it; it belongs to the studies that argue for
it. The dynamic case, where a definite introduces a family of referents, is left to the first
dynamic consumer that needs it.

## References

* [buring-2012]
* [heim-kratzer-1998]
-/

@[expose] public section

/-- A definite denotes, at a context and a world, at most one individual. -/
abbrev Definite (Ctx : Type*) (W : Type*) (E : Type*) := Ctx → W → Part E

namespace Definite

variable {Ctx : Type*} {W : Type*} {E : Type*}

/-- Predicating `scope` of a definite at a context gives the trivalent proposition that is
undefined where the definite denotes nothing and the value of `scope` at its referent
elsewhere. -/
noncomputable def toTrivalent (nd : Definite Ctx W E) (scope : E → W → Prop) (c : Ctx) :
    W → Trivalent :=
  fun w ↦ Trivalent.ofPart ((nd c w).map (scope · w))

section Values

variable {nd : Definite Ctx W E} {scope : E → W → Prop} {c : Ctx} {w : W}

@[simp] theorem toTrivalent_eq_undefined_iff :
    nd.toTrivalent scope c w = .undefined ↔ ¬ (nd c w).Dom := by
  simp [toTrivalent]

@[simp] theorem toTrivalent_eq_true_iff :
    nd.toTrivalent scope c w = .true ↔ ∃ e ∈ nd c w, scope e w := by
  simp only [toTrivalent, Trivalent.ofPart_eq_true_iff, Part.mem_map_iff, eq_iff_iff]
  exact ⟨fun ⟨_, ⟨e, he, h⟩, ha⟩ ↦ ⟨e, he, h.2 ha⟩, fun ⟨e, he, h⟩ ↦ ⟨_, ⟨e, he, .rfl⟩, h⟩⟩

@[simp] theorem toTrivalent_eq_false_iff :
    nd.toTrivalent scope c w = .false ↔ ∃ e ∈ nd c w, ¬ scope e w := by
  simp only [toTrivalent, Trivalent.ofPart_eq_false_iff, Part.mem_map_iff, eq_iff_iff]
  exact ⟨fun ⟨_, ⟨e, he, h⟩, ha⟩ ↦ ⟨e, he, fun hs ↦ ha (h.1 hs)⟩,
    fun ⟨e, he, h⟩ ↦ ⟨_, ⟨e, he, .rfl⟩, h⟩⟩

end Values

/-! ### Variables -/

section Var

variable {ι : Type*} {i : ι} {D : Set E} {scope : E → W → Prop} {g : ι → E} {w : W} {e : E}

/-- A variable restricted to a domain denotes the value `g i` of its index under the assignment
where that value lies in the domain `D`, and nothing elsewhere. -/
def var (i : ι) (D : Set E) : Definite (ι → E) W E := fun g _ ↦ ⟨g i ∈ D, fun _ ↦ g i⟩

@[simp] theorem var_dom : (var (W := W) i D g w).Dom ↔ g i ∈ D := Iff.rfl

@[simp] theorem mem_var : e ∈ var (W := W) i D g w ↔ g i ∈ D ∧ g i = e :=
  ⟨fun ⟨h, he⟩ ↦ ⟨h, he⟩, fun ⟨h, he⟩ ↦ ⟨h, he⟩⟩

theorem var_toTrivalent_eq_undefined_iff :
    (var i D).toTrivalent scope g w = .undefined ↔ g i ∉ D := by
  simp

theorem var_toTrivalent_eq_true_iff :
    (var i D).toTrivalent scope g w = .true ↔ g i ∈ D ∧ scope (g i) w := by
  simp

end Var

end Definite

/-! ### Characters as definites -/

namespace Kaplan.Character

variable {C W E : Type*}

/-- A character is the definite that denotes at every context and world. -/
def toDefinite (χ : Character C W E) : Definite C W E := fun c w ↦ Part.some (χ c w)

@[simp] theorem toNominal_apply (χ : Character C W E) (c : C) (w : W) :
    χ.toDefinite c w = Part.some (χ c w) :=
  rfl

theorem isDirectlyReferential_iff (χ : Character C W E) :
    χ.IsDirectlyReferential ↔ ∀ c, IsRigid (χ.toDefinite c) :=
  forall_congr' fun _ ↦ (Part.some_injective (α := E)).isRigid_comp_iff.symm

end Kaplan.Character
