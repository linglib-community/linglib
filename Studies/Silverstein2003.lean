module

public import Linglib.Fragments.Basque.Pronouns
public import Linglib.Fragments.Dutch.Pronouns
public import Linglib.Fragments.German.Pronouns
public import Linglib.Fragments.Mayan.Kiche.Pronouns
public import Linglib.Fragments.Romance.Italian.Pronouns
public import Linglib.Fragments.Romance.Spanish.Pronouns
public import Linglib.Fragments.Tamil.Pronouns
public import Mathlib.Data.Fintype.Pi

/-!
# Silverstein (2003): Indexical order and the dialectics of sociolinguistic life

Silverstein argues that the first-order index of deference in a system of familiar and polite
address is an exchange of forms between two participants and not a single form:
[who gives the familiar form and receives the polite one](##Silverstein2003.DeferenceEntitled)
is entitled to deference, [no one is in a symmetric
exchange](##Silverstein2003.exists_deferenceEntitled_iff), and [no reading of one token
recovers this](##Silverstein2003.not_exists_forall_deferenceEntitled_iff). The reading of a
single polite form as elevated is a second-order construal, which takes the form as a figure
on the literal second person singular. In six fragments every pronoun for one addressee is
[the literal form or such a figure](##Silverstein2003.ordinary_or_tropes), and Dutch *u*, a
form dedicated to politeness, [is neither](##Silverstein2003.dutch_u).

## Implementation notes

A form is literal for the addressee when its agreement person and number realize the single
addressee, and it tropes when it denotes the addressee and its agreement does not. The pronouns
are those of the fragments, which do not include French, Yokuts or Worora, three of the four
languages Silverstein names.

## TODO

* Indexical order itself, the competition of an n-th and an n + 1st value and the replacement
  of one by the other, is not formalized, nor are the Javanese speech levels, the reading of
  indicators, markers and stereotypes as orders, or the register of wine tasting.

## References

* [silverstein-2003]
* [ackema-neeleman-2018]
* [adamson-zompi-2025]
-/

@[expose] public section

namespace Silverstein2003

open SpeechAct

/-! ### Exchanges of address -/

/-- A form of address is familiar or polite. -/
inductive Address where
  /-- The familiar form, T. -/
  | t
  /-- The polite form, V. -/
  | v
  deriving DecidableEq, Fintype, Repr

/-- An exchange of address is the form each participant gives the other. -/
abbrev Exchange := Role → Address

variable {u : Exchange} {r s : Role}

/-- A participant is entitled to deference in an exchange when they give the familiar form and
receive the polite one. -/
def DeferenceEntitled (u : Exchange) (r : Role) : Prop := u r = .t ∧ u r.other = .v

instance : Decidable (DeferenceEntitled u r) := inferInstanceAs (Decidable (_ ∧ _))

theorem DeferenceEntitled.eq (hr : DeferenceEntitled u r) (hs : DeferenceEntitled u s) :
    r = s := by
  by_contra h
  rw [Role.eq_other_of_ne h] at hr
  exact absurd (hr.1.symm.trans hs.2) (by decide)

/-- Someone is entitled to deference exactly when the exchange is asymmetric. -/
theorem exists_deferenceEntitled_iff :
    (∃ r, DeferenceEntitled u r) ↔ u .speaker ≠ u .addressee := by
  revert u; decide

/-- Deference entitlement is not a function of the form a participant gives. -/
theorem not_exists_forall_deferenceEntitled_iff :
    ¬ ∃ f : Address → Prop, ∀ (u : Exchange) r, DeferenceEntitled u r ↔ f (u r) := by
  rintro ⟨f, hf⟩
  have h₁ := (hf (fun r ↦ if r = .speaker then .t else .v) .speaker).1 (by decide)
  exact absurd ((hf (fun _ ↦ .t) .speaker).2 h₁) (by decide)

/-! ### Polite forms as figures -/

/-- A pronoun tropes on the second person singular when it denotes the single addressee and its
agreement person and number do not. -/
def Tropes (p : PersonalPronoun) : Prop :=
  Person.Category.addressee ∈ p.referential ∧ Person.Category.addressee ∉ p.categories

instance (p : PersonalPronoun) : Decidable (Tropes p) := inferInstanceAs (Decidable (_ ∧ _))

/-- In the German, Italian, Spanish, Tamil, K'iche' and Basque fragments a pronoun for one
addressee denotes what its agreement realizes or tropes on the second person singular. -/
theorem ordinary_or_tropes :
    ∀ I ∈ [German.Pronouns.personal, Italian.Pronouns.personal, Spanish.Pronouns.personal,
        Tamil.Pronouns.personal, Kiche.Pronouns.personal, Basque.Pronouns.personal],
      ∀ p ∈ I, Person.Category.addressee ∈ p.referential → p.IsOrdinary ∨ Tropes p := by
  decide

-- each of the six has a polite form that tropes
example : Tropes German.Pronouns.sie_formal ∧ Tropes Italian.Pronouns.lei_formal ∧
    Tropes Spanish.Pronouns.usted ∧ Tropes Tamil.Pronouns.niiŋgæ ∧ Tropes Kiche.Pronouns.laal ∧
    Tropes Basque.Pronouns.zu := by
  decide

/-- Dutch *u* denotes the addressee beyond what its second person singular agreement realizes
and does not trope. -/
theorem dutch_u :
    Person.Category.addressee ∈ Dutch.Pronouns.u.referential ∧
      ¬ Dutch.Pronouns.u.IsOrdinary ∧ ¬ Tropes Dutch.Pronouns.u := by
  decide

end Silverstein2003
