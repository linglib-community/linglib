module

public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Reference.Character

/-!
# Nominal denotations

A pronoun, a definite description, a demonstrative and a bound variable are one kind of
thing: a presuppositional, context-relative individual denotation, differing only in the
*selector* that chooses the individual (the assignment value, the iota, the demonstratum) and
in the intrinsic *presupposition* (φ-features, uniqueness, deixis), as Büring argues. A
`Nominal` is that common shape. Resolving it against a scope is `presupOfReferent` of the
selector at a context (`Nominal.resolve`), so a definite built from `presupOfReferent` is a
resolved `Nominal.ofReferent` by `rfl` (`ofReferent_resolve`), and the full denotation
restricts the resolved one to where the intrinsic presupposition holds (`Nominal.toTrivalent`),
which is where a pronoun's φ-features project. A variable restricted to a domain
(`Nominal.var`) selects the assignment's value at its index and presupposes that the value lies
in the domain. A character is the total nominal with no
presupposition (`Character.toNominal`), and it is directly referential exactly when that
nominal's selector is rigid at every context (`Character.isDirectlyReferential_iff`).

## Implementation notes

The selector is `Option`-valued against a context; the dynamic case, where a selector returns
a family of referents, is the functor-parameterised generalisation of this signature and is
left to the first dynamic consumer that needs it.

## References

* [buring-2012]
* [heim-kratzer-1998]
-/

@[expose] public section

open Presupposition

/-- A presuppositional, context-relative individual denotation.

`presup` is the intrinsic presupposition beyond definedness — φ-features for
a pronoun, deixis for a demonstrative, vacuous for a definite (whose only
presupposition is that the selector is defined). `selector` is the partial
choice of referent (`g i`, `ι`, the demonstratum) at a context and world. -/
structure Nominal (Ctx : Type*) (W : Type*) (E : Type*) where
  /-- Intrinsic presupposition beyond definedness (φ-features, deixis). -/
  presup : Ctx → W → Prop
  /-- The partial referent selector. -/
  selector : Ctx → W → Option E

namespace Nominal

variable {Ctx : Type*} {W : Type*} {E : Type*}

/-- The simplest nominal is a context-free referent selector with no intrinsic
presupposition, a bare iota or definite. `(ofReferent r).resolve scope ⟨⟩`
unfolds to `presupOfReferent r scope`, so any `presupOfReferent`-built
denotation is an `ofReferent` resolved (`ofReferent_resolve`). -/
def ofReferent (referent : W → Option E) : Nominal Unit W E where
  presup := fun _ _ => True
  selector := fun _ => referent

/-- Resolving a nominal against a `scope` at context `c` gives the trivalent proposition defined
where a referent is selected and applying `scope` to it there. It is `presupOfReferent` over
`nd.selector c`, so any `presupOfReferent`-built denotation is a `resolve`, by `rfl`. -/
noncomputable def resolve (nd : Nominal Ctx W E) (scope : E → W → Prop) (c : Ctx) :
    W → Trivalent :=
  presupOfReferent (nd.selector c) scope

theorem ofReferent_resolve (referent : W → Option E) (scope : E → W → Prop) :
    (ofReferent referent).resolve scope ⟨⟩ = presupOfReferent referent scope :=
  rfl

open Classical in
/-- The full denotation is `resolve` restricted to where the intrinsic presupposition holds,
the two presuppositions conjoined. For a definite the intrinsic presupposition is vacuous, so
`toTrivalent` and `resolve` agree; for a pronoun the conjoined presupposition is where the
φ-features project. -/
noncomputable def toTrivalent (nd : Nominal Ctx W E) (scope : E → W → Prop) (c : Ctx) :
    W → Trivalent :=
  fun w ↦ Trivalent.transplication (Trivalent.ofProp (nd.presup c w)) (nd.resolve scope c w)

section Values

variable {nd : Nominal Ctx W E} {scope : E → W → Prop} {c : Ctx} {w : W}

@[simp] theorem resolve_eq_undefined_iff :
    nd.resolve scope c w = .undefined ↔ nd.selector c w = none :=
  presupOfReferent_eq_undefined_iff

@[simp] theorem toTrivalent_eq_undefined_iff :
    nd.toTrivalent scope c w = .undefined ↔ (nd.presup c w → nd.selector c w = none) := by
  simp [toTrivalent, imp_iff_not_or]

@[simp] theorem toTrivalent_eq_true_iff :
    nd.toTrivalent scope c w = .true ↔
      nd.presup c w ∧ ∃ e, nd.selector c w = some e ∧ scope e w := by
  simp [toTrivalent, resolve]

end Values

/-! ### Variables -/

section Var

variable {ι : Type*} {i : ι} {D : Set E} {scope : E → W → Prop} {g : ι → E} {w : W}

/-- A variable restricted to a domain selects the value `g i` of its index under the assignment
and presupposes that the value lies in the domain `D`. -/
@[simps]
def var (i : ι) (D : Set E) : Nominal (ι → E) W E where
  presup g _ := g i ∈ D
  selector g _ := some (g i)

theorem var_toTrivalent_eq_undefined_iff :
    (var i D).toTrivalent scope g w = .undefined ↔ g i ∉ D := by
  simp

theorem var_toTrivalent_eq_true_iff :
    (var i D).toTrivalent scope g w = .true ↔ g i ∈ D ∧ scope (g i) w := by
  simp

end Var

@[ext] theorem ext {nd₁ nd₂ : Nominal Ctx W E}
    (hp : nd₁.presup = nd₂.presup) (hs : nd₁.selector = nd₂.selector) : nd₁ = nd₂ := by
  cases nd₁; cases nd₂; cases hp; cases hs; rfl

end Nominal

/-! ### Characters as nominals -/

namespace Kaplan.Character


variable {C W E : Type*}

/-- A character is a nominal denotation that is total and has no presupposition. -/
def toNominal (χ : Character C W E) : Nominal C W E where
  presup _ _ := True
  selector c w := some (χ c w)

@[simp] theorem toNominal_presup (χ : Character C W E) (c : C) (w : W) :
    χ.toNominal.presup c w = True :=
  rfl

@[simp] theorem toNominal_selector (χ : Character C W E) (c : C) (w : W) :
    χ.toNominal.selector c w = some (χ c w) :=
  rfl

theorem isDirectlyReferential_iff (χ : Character C W E) :
    χ.IsDirectlyReferential ↔ ∀ c, IsRigid (χ.toNominal.selector c) :=
  forall_congr' fun _ ↦ (Option.some_injective E).isRigid_comp_iff.symm

end Kaplan.Character
