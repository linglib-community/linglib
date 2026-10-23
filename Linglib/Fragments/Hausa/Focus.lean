/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Fragments.Hausa.TAM
public import Linglib.Fragments.Hausa.Tone
public import Linglib.Semantics.Focus.Marking
public import Linglib.Syntax.Category.Particle.Basic

/-!
# Hausa focus and the stabilizer

Hausa focuses a constituent by fronting it to a focus slot at the beginning of its clause,
where the stabilizer may follow it: *Hàdīzà cē ta ci lambā̀* 'It was Hadiza who won the prize'.
The clause after a fronted focus is a Rel environment, so its TAM must be a Rel form: *Audù nē ya
tàfi kā̀suwā* 'It is Audu who went to the market', with the preterite, against *Audù yā tàfi
kā̀suwā* 'Audu has gone to the market', with the completive ([newman-2000]). A focus may also stay
in place, with the TAM of a general clause and no marking of any kind; the particle rarely
follows it then, at the end of the clause or before an adjunct: *Audù yaa sàyi zoobèe ne* 'Audu
bought a RING' ([hartmann-zimmermann-2007-exhaustivity]).

The stabilizer has polar tone and no agreement feature but gender: it is *cē* after a feminine
singular and *nē* after anything else, a masculine, a plural, feminine coordinations included, a
prepositional phrase or a verb phrase. It can always be left out, and
[hartmann-zimmermann-2007-exhaustivity] argue that it marks not focus but exhaustivity, being
excluded where a property is known to hold of more than the focus.

## Main definitions

* `Hausa.ne`, `Hausa.ce`, `Hausa.stabilizer` — the stabilizer and its agreement
* `Hausa.FocusConfig` — a focused clause: its TAM, the TAM its PAC surfaces in, the PAC's subject
  cell, the focus strategy, and the focus's agreement features
* `Hausa.FocusConfig.Licensed` — a fronted focus takes a Rel counterpart of the clause's TAM, a
  focus in place a general TAM unchanged

## Main results

* `Hausa.FocusConfig.pacTAM_ne_iff` — a licensed focus changes the TAM exactly when it is fronted
  and the TAM does not occur in Rel environments, so fronting is audible in the PAC with the
  completive, the continuous and the potential and nowhere else

## References

* [newman-2000]
* [hartmann-zimmermann-2007-exhaustivity]
-/

@[expose] public section

namespace Hausa

open Agreement Tone

/-! ### The stabilizer -/

/-- *nē*, the stabilizer after a phrase that is not feminine. -/
def ne : Particle := { form := "nē", position := some .postHost }

/-- *cē*, the stabilizer after a feminine. -/
def ce : Particle := { form := "cē", position := some .postHost }

/-- The stabilizer after a phrase of the given gender; a plural, a prepositional phrase and a verb
phrase have none. -/
def stabilizer (g : Option Gender) : Particle := if g = some .feminine then ce else ne

theorem stabilizer_eq_ce_iff (g : Option Gender) : stabilizer g = ce ↔ g = some .feminine := by
  unfold stabilizer
  split_ifs with h
  · simpa using h
  · simpa [ne, ce] using h

/-- The stabilizer's tone after *rìgā* 'gown' is low: *rìgā cè* 'it's a gown'. -/
example : polarAfter [.H] = some .L := rfl

/-- The stabilizer's tone after *mōtà* 'car' is high: *mōtà cē* 'it's a car'. -/
example : polarAfter [.L] = some .H := rfl

/-! ### Focus configurations -/

/-- A focused clause records its TAM as a general clause has it, the TAM its PAC surfaces in, the
PAC's subject cell, the focus strategy, the gender of the focus (none for a plural), and whether the
stabilizer surfaces. -/
structure FocusConfig where
  tam : TAM
  pacTAM : TAM
  cell : Bundle
  strategy : Focus.Strategy
  focusGender : Option Gender
  hasStab : Bool
  deriving Repr

namespace FocusConfig

variable (c : FocusConfig)

/-- A fronted focus takes a Rel counterpart of the clause's TAM; a focus in place leaves a general
TAM unchanged. -/
def Licensed : Prop :=
  (c.strategy = .inSitu → c.pacTAM = c.tam ∧ c.tam ∈ TAM.general) ∧
    (c.strategy = .exSitu → c.pacTAM ∈ c.tam.relCounterparts)

instance : Decidable c.Licensed := inferInstanceAs (Decidable (_ ∧ _))

/-- The surface PAC. -/
def pac : Option String := c.pacTAM.form c.cell

/-- The stabilizer, if it surfaces. -/
def stab? : Option Particle :=
  if c.hasStab then some (stabilizer c.focusGender) else none

variable {c}

/-- A licensed focus changes the TAM exactly when it is fronted and the TAM does not occur in Rel
environments. -/
theorem pacTAM_ne_iff (h : c.Licensed) :
    c.pacTAM ≠ c.tam ↔ c.strategy = .exSitu ∧ c.tam ∉ TAM.rel := by
  cases hs : c.strategy
  · simp [(h.1 hs).1]
  · simpa using TAM.ne_iff_not_mem_rel _ _ (h.2 hs)

end FocusConfig

/-- A focus in place, with the clause's TAM. -/
def mkInSitu (tam : TAM) (cell : Bundle) (g : Option Gender) (hasStab : Bool := false) :
    FocusConfig :=
  ⟨tam, tam, cell, .inSitu, g, hasStab⟩

/-- A fronted focus, its PAC in the TAM `pacTAM`. -/
def mkExSitu (tam pacTAM : TAM) (cell : Bundle) (g : Option Gender) (hasStab : Bool := true) :
    FocusConfig :=
  ⟨tam, pacTAM, cell, .exSitu, g, hasStab⟩

/-- In *Audù nē ya tàfi kā̀suwā* 'It is Audu who went to the market', the fronted subject takes the
preterite *ya* for the completive. -/
example :
    let c := mkExSitu .completive .preterite
      ((Bundle.personNumber .third .singular).set .gender .masculine) (some .masculine)
    c.Licensed ∧ c.pac = some "ya" ∧ c.stab? = some ne := by
  decide

/-- The completive does not occur after a fronted focus. -/
example :
    ¬ (mkExSitu .completive .completive
        ((Bundle.personNumber .third .singular).set .gender .masculine)
        (some .masculine)).Licensed := by
  decide

/-- In *Audù yaa sàyi zoobèe ne* 'Audu bought a RING', the object focus stays in place, the TAM
keeps its general form, and the stabilizer ends the clause. -/
example :
    let c := mkInSitu .completive
      ((Bundle.personNumber .third .singular).set .gender .masculine) (some .masculine) true
    c.Licensed ∧ c.pac = some "yā" ∧ c.stab? = some ne := by
  decide

/-- In *Hàdīzà cē ta ci lambā̀* 'It was Hadiza who won the prize', the stabilizer agrees with the
feminine focus. -/
example :
    (mkExSitu .completive .preterite ((Bundle.personNumber .third .singular).set .gender .feminine)
      (some .feminine)).stab? = some ce := by
  decide

end Hausa
