/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Studies.Kripke1980
public import Linglib.Semantics.Quantification.Defs

/-!
# Almog (2014): Referential Mechanics

This file formalizes the formal core of [almog-2014]. Rigid designation and directly
referential content are separated by Kaplan's `dthat`: `dthat[the φ]` designates rigidly and
so is scope-inert (`dthat_deRe_iff_deDicto`), yet two descriptions that co-denote at the
context world rigidify to one content (`dthat_eq_dthat_of_eq`), so rigidity alone leaves the
informativeness of an identity unexplained, while a structured singular proposition keeps the
individuals apart (`SingularProposition.mk_ne_mk_of_ne`). Co-referential rigid designators
have the same content, `IsRigid.eq_of_apply_eq`, which is the book's "no entailments" thesis:
direct reference assigns *Cicero is Cicero* and *Cicero is Tully* one proposition and is
silent on whether it is necessary or believed. Donnellan's referential use is a different
mechanism from rigidification: reference fixed by contact with the object before any
description is deployed is the constant character, and it diverges from `dthat` of the
description whenever the description misfits (`const_ne_dthat_of_ne`). The Russell–Partee–
Kaplan challenge is the type gap between referential and quantificational subjects: the
Montague lift `Quantifier.NP.individual` is injective (`Quantifier.NP.individual_injective`)
but the universal quantifier is not in its image (`not_exists_individual_eq_forall`), so a
subject of type `E` cannot serve *every philosopher*.

## Implementation notes

The book's taxonomy of three mechanisms of direct reference (designation, singular
proposition, referential use), whose pairwise independence it argues expression by
expression, is not formalized: a profile assigned to an expression by fiat is not derivable
from its semantics, so nothing would be proved about it.

## References

* [almog-2014]
* [kaplan-1989]
* [kripke-1980]
* [donnellan-1966]
-/

@[expose] public section

namespace Almog2014

open Kripke1980 Kaplan

variable {W E : Type*} {desc desc₁ desc₂ : W → E} {c w₀ w : W}

/-! ### Rigidity without singularity -/

theorem dthat_deRe_iff_deDicto (P : E → W → Prop) :
    deRe P (Character.dthat desc c) w₀ w ↔ deDicto P (Character.dthat desc c) w :=
  (isRigid_iff_deRe_iff_deDicto (Character.dthat desc c) w₀).1 (isRigid_const (desc c)) P w

theorem dthat_eq_dthat_of_eq (h : desc₁ c = desc₂ c) :
    (Character.dthat desc₁ : Character W W E) c = Character.dthat desc₂ c :=
  funext λ _ => h

/-- A singular proposition: a structured pair of an individual and a property. -/
structure SingularProposition (W E : Type*) where
  /-- The individual the proposition is about. -/
  individual : E
  /-- The property predicated of it. -/
  property : E → W → Prop

namespace SingularProposition

variable {a b : E} {P : E → W → Prop}

/-- The unstructured proposition a singular proposition determines. -/
def flatten (p : SingularProposition W E) : W → Prop := p.property p.individual

theorem mk_ne_mk_of_ne (h : a ≠ b) : mk a P ≠ mk b P :=
  λ e => h (congrArg individual e)

end SingularProposition

/-! ### Referential use is not rigidification -/

theorem const_ne_dthat_of_ne {intended : E} (h : desc c ≠ intended) :
    (Character.const intended : Character W W E) c ≠ Character.dthat desc c :=
  λ e => h (congrFun e c).symm

/-! ### The Russell–Partee–Kaplan challenge -/

theorem not_exists_individual_eq_forall (a b : E) (hab : a ≠ b) :
    ¬ ∃ e : E, Quantifier.NP.individual e = λ P => ∀ x, P x := by
  rintro ⟨e, he⟩
  have h : ∀ x, x = e := (congrFun he (· = e)).mp rfl
  exact hab ((h a).trans (h b).symm)

end Almog2014
