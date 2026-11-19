/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Restrict
public import Linglib.Syntax.Feature.HasPhi
public import Linglib.Fragments.Hungarian.Pronouns
public import Linglib.Fragments.Hungarian.Reciprocals
public import Linglib.Fragments.Hungarian.Phonology
public import Linglib.Data.Examples.Rakosi2020
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Gloss
public import Linglib.Morphology.Word.Leipzig

/-!
# Rákosi (2020): Reciprocal anaphors in singular constructions in Hungarian

A Hungarian subject can trigger singular agreement on the verb and yet supply a plurality: a
quantified noun phrase, a coordination of singulars, a collective noun, and a null pronoun bound
by a plural all do, and [the verb's number follows the kind of subject](##verb_agreement). A
reflexive [is acceptable exactly when it agrees with the verb](##reflexive_acceptable_iff_agree),
so these subjects reject the plural reflexive, whereas the invariable reciprocal *egymás*
[needs only the plurality](##reciprocal_acceptable_iff) and is
[accepted with a singular verb in all four constructions](##reciprocal_with_singular_verb). The
two conditions dissociate: the reflexive's judgment
[is not a function of its antecedent](##not_factorsThrough_antecedent), nor the reciprocal's
[of the verb's number](##not_factorsThrough_verbNumber).

## Implementation notes

* The verb's agreement is read off the gloss line, and the reflexive's features off
  `Hungarian.Pronouns.reflexives`; a row records only the kind of its antecedent, a level of
  `Examples.Antecedent`, and marks its anaphor, naming the pronoun.
* The anaphor a row names is checked against the fragment: each is [the reciprocal or a
  reflexive](##pronoun_mem_inventory), each marked word [begins as its pronoun is
  written](##printed), and [no other word does](##anaphors_marked).
* The plural reflexive with a singular subject included in its reference is acceptable without
  agreeing, but only as a referential pronoun: where the paper tests the bound reading,
  [it is available exactly under agreement](##boundVariable_iff_agree).
* `Examples.Antecedent.SuppliesPlurality` holds of the bound null pronoun, which the paper calls
  a singular variable: the plurality is that of its binder.

## References

* [rakosi-2020]
-/

@[expose] public section

namespace Rakosi2020

open Hungarian.Pronouns Hungarian.Reciprocals
open Examples (all Antecedent antecedent)

/-! ### Antecedents -/

namespace Examples.Antecedent

/-- The numbers of the verb that agrees with the antecedent: plural with a plural noun phrase,
either number with a coordination, and singular otherwise. -/
def agreement : Antecedent → Finset Number
  | plural => {.plural}
  | coordinate => {.singular, .plural}
  | _ => {.singular}

/-- The antecedent gives a reciprocal a plurality to distribute over: it denotes one, or, as a
bound variable, ranges over the members of one. The inclusive subject is "not plural in any
sense". -/
def SuppliesPlurality : Antecedent → Prop
  | atomic | inclusive => False
  | _ => True

instance : DecidablePred SuppliesPlurality := fun a ↦ by
  cases a <;> unfold SuppliesPlurality <;> infer_instance

end Examples.Antecedent

/-! ### The rows -/

/-- The pronoun of the Hungarian fragment that a lexeme of the data is. -/
def Examples.Lexeme.pronoun : Examples.Lexeme → Pronoun
  | .egymas => Hungarian.Reciprocals.egymas.toPronoun
  | .maga => Hungarian.Pronouns.maga.toPronoun
  | .maguk => Hungarian.Pronouns.maguk.toPronoun
  | .magunk => Hungarian.Pronouns.magunk.toPronoun

/-- The anaphor of the row, the pronoun its marked word is a form of. -/
def anaphor? (e : Datum) : Option Pronoun :=
  (e.spans.findSome? Examples.lexeme?).map (·.pronoun)

/-- The anaphor of the row is the pronoun `p`. -/
def HasAnaphor (e : Datum) (p : Pronoun) : Prop := anaphor? e = some p

instance (e : Datum) (p : Pronoun) : Decidable (HasAnaphor e p) :=
  inferInstanceAs (Decidable (_ = _))

/-- The word begins as the pronoun is written, vowel length aside: its stem is the pronoun where
the source segments the word into several morphs, and the word begins with the pronoun
otherwise. -/
def WrittenAs (w : GlossedWord) (p : Pronoun) : Prop :=
  ∃ x ∈ Hungarian.transcribe? p.form,
    if 1 < w.morphs.length then (Hungarian.graphemes w.stem).mapM Hungarian.ofGrapheme = some x
    else ∃ y ∈ (Hungarian.graphemes w.wordform).mapM Hungarian.ofGrapheme, x <+: y

instance (w : GlossedWord) (p : Pronoun) : Decidable (WrittenAs w p) := by
  unfold WrittenAs; infer_instance

/-- The rows whose anaphor is the pronoun `p`. -/
def rowsWith (p : Pronoun) : Set Datum := {e | e ∈ all ∧ HasAnaphor e p}

instance (p : Pronoun) : DecidablePred (· ∈ rowsWith p) := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-- The features of the verb the anaphor is an argument of, read off the gloss line: the last
word glossed with a person. -/
def verb? (e : Datum) : Option Morphology.Features :=
  (e.glossedWords.map (·.features)).reverse.find? fun f ↦ (f .person).isSome

/-- The number of the verb. -/
def verbNumber? (e : Datum) : Option Number := (verb? e).bind (· .number)

-- every anaphor the data names is the reciprocal or a reflexive of the fragment
theorem pronoun_mem_inventory :
    ∀ l : Examples.Lexeme,
      l.pronoun = egymas.toPronoun ∨ ∃ r ∈ reflexives, l.pronoun = r.toPronoun := by
  decide

-- every marked word begins as the pronoun it names is written
theorem printed :
    ∀ e ∈ all, ∀ s ∈ e.spans, ∀ l ∈ Examples.lexeme? s,
      ∃ w ∈ (s.words e).head?, s.length = 1 ∧ WrittenAs w l.pronoun := by
  decide

-- no unmarked word begins as the reciprocal or a reflexive is written
theorem anaphors_marked :
    ∀ e ∈ all, ∀ i < e.glossedWords.length, ∀ w ∈ e.glossedWords[i]?,
      (WrittenAs w egymas.toPronoun ∨ ∃ r ∈ reflexives, WrittenAs w r.toPronoun) →
        ∃ s ∈ e.spans, s.start = i ∧ (Examples.lexeme? s).isSome := by
  decide

theorem isSome_verbNumber : ∀ e ∈ all, (verbNumber? e).isSome := by decide

/-! ### Verb agreement -/

-- (7), (10), (14)
theorem verb_agreement :
    Datum.Checks (fun e ↦ if anaphor? e = none then
        (antecedent e).bind fun a ↦ (verbNumber? e).map (a, ·) else none)
      (fun p ↦ .ofProp (p.2 ∈ p.1.agreement)) all 8 := by
  decide

/-! ### The reflexive -/

/-- A reflexive whose subject is not merely included in its reference is acceptable exactly when
it agrees with the verb in person and number. -/
theorem reflexive_acceptable_iff_agree :
    ∀ e ∈ all, antecedent e ≠ some .inclusive → ∀ r ∈ reflexives, HasAnaphor e r.toPronoun →
      ∀ v ∈ verb? e, (e.judgment = .acceptable ↔ HasPhi.Agree r.toPronoun v) := by
  decide

-- (4a), (4b)
theorem boundVariable_iff_agree :
    ∀ e ∈ all, ∀ r ∈ reflexives, HasAnaphor e r.toPronoun → ∀ v ∈ verb? e,
      ∀ j ∈ Examples.reading e .boundVariable,
        (j = .acceptable ↔ HasPhi.Agree r.toPronoun v) := by
  decide

/-- The reflexive's judgment is not a function of its antecedent: a coordination takes the
singular reflexive with a singular verb and rejects it with a plural one ((11a), (11b')). -/
theorem not_factorsThrough_antecedent :
    ¬ ((rowsWith maga.toPronoun).domRestrict Datum.judgment).FactorsThrough
      ((rowsWith maga.toPronoun).domRestrict antecedent) := fun h ↦
  absurd (@h ⟨Examples.ex_11a, by decide⟩ ⟨Examples.ex_11b_, by decide⟩ rfl) (by decide)

/-! ### The reciprocal -/

/-- The reciprocal is acceptable exactly when its antecedent supplies a plurality. -/
theorem reciprocal_acceptable_iff :
    ∀ e ∈ all, HasAnaphor e egymas.toPronoun →
      ∃ a ∈ antecedent e, (e.judgment = .acceptable ↔ a.SuppliesPlurality) := by
  decide

/-- The reciprocal's judgment is not a function of the verb's number: a singular verb rejects it
with an atomic subject and takes it with a coordination ((2a), (12)). -/
theorem not_factorsThrough_verbNumber :
    ¬ ((rowsWith egymas.toPronoun).domRestrict Datum.judgment).FactorsThrough
      ((rowsWith egymas.toPronoun).domRestrict verbNumber?) := fun h ↦
  absurd (@h ⟨Examples.ex_2a, by decide⟩ ⟨Examples.ex_12, by decide⟩ (by decide)) (by decide)

/-- With each of the four antecedents of §§3–6, the reciprocal is accepted with a singular
verb. -/
theorem reciprocal_with_singular_verb :
    ∀ a ∈ [Antecedent.quantified, .coordinate, .collective, .boundPro], ∃ e ∈ all,
      antecedent e = some a ∧ HasAnaphor e egymas.toPronoun ∧
        verbNumber? e = some .singular ∧ e.judgment = .acceptable := by
  decide

end Rakosi2020
