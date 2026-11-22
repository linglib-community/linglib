/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.ConstructionGrammar.Form

/-!
# Constructions

A construction is a learned pairing of a form with a meaning, the unit of grammatical knowledge in
construction grammar. A `Construction Sem` pairs a `TypedForm` with a meaning of type `Sem`, and
`Construction.map` changes the meaning along a function, keeping the form.

## References

* [goldberg-1995]
* [goldberg-2003]
* [goldberg-2006]
* [fillmore-kay-oconnor-1988]
-/

@[expose] public section

namespace ConstructionGrammar

/-- A construction is a learned pairing of form and meaning. The meaning pole is typed by the
domain that owns the construction, such as a composition rule or a presupposition, with `Unit`
for a purely formal record or a defective, form-only construction. -/
structure Construction (Sem : Type*) where
  /-- `form` is the form pole. -/
  form : TypedForm String
  /-- `meaning` is the meaning pole. -/
  meaning : Sem
  /-- `pragmaticPoint` records whether the construction carries a conventional pragmatic point
      ([fillmore-kay-oconnor-1988] §1.1.4). -/
  pragmaticPoint : Bool := false
  deriving DecidableEq, Repr

variable {Sem : Type*}

/-- The specificity of a construction is that of its form. -/
def Construction.specificity (c : Construction Sem) : Specificity :=
  c.form.specificity

/-- `c.map f` reinterprets the meaning pole of `c` along `f`, keeping the form. -/
@[simps]
def Construction.map {Sem' : Type*} (f : Sem → Sem') (c : Construction Sem) :
    Construction Sem' :=
  { form := c.form, meaning := f c.meaning, pragmaticPoint := c.pragmaticPoint }

@[simp]
theorem Construction.map_id (c : Construction Sem) : c.map id = c := rfl

@[simp]
theorem Construction.map_map {Sem' Sem'' : Type*} (g : Sem' → Sem'') (f : Sem → Sem')
    (c : Construction Sem) : (c.map f).map g = c.map (g ∘ f) := rfl

@[simp]
theorem Construction.specificity_map {Sem' : Type*} (f : Sem → Sem') (c : Construction Sem) :
    (c.map f).specificity = c.specificity := rfl

/-- A construction is a formal idiom in the sense of [fillmore-kay-oconnor-1988] §1.1.3, a
lexically open idiom, when its form is not lexically specified. The distinction is a cline
(fn. 3), which `Specificity` discretizes. -/
def Construction.IsFormalIdiom (c : Construction Sem) : Prop :=
  c.specificity ≠ .lexicallySpecified

instance (c : Construction Sem) : Decidable c.IsFormalIdiom :=
  inferInstanceAs (Decidable (¬ _))

end ConstructionGrammar
