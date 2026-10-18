module

public import Linglib.Core.Computability.RegularExpressions
public import Linglib.Fragments.Finnish.Declension
public import Linglib.Fragments.Finnish.Infinitives
public import Linglib.Fragments.Finnish.Possession

/-!
# Finnish morphotactics

A Finnish nominal takes number, case and possessive endings and clitics, always in that order,
as *pullo-i-ssa-nne-kin* 'in your bottles too' (Karlsson §3.1), and a non-finite verb form puts
the function ending of its infinitive before them, as *sano-e-ssa-ni* 'while I say' (§3.3). The
plural is -t in the nominative and -i elsewhere, -j between two vowels, and clitics come last,
more than one occasionally, as *on-ko-han* (§25.6).

Some endings determine more than their own position. The nominative plural -t stands on the
border between number and case, so no case ending follows it. The comitative -ine contains a
fossilized plural -i, so no number ending precedes it, and on a noun a possessive ending always
follows it (§16.4). Infinitives are never marked for number, each takes only its own cases
(`Finnish.Infinitive.cases`), and the translative of the A infinitive takes a possessive
ending (§22.2.2).

Before a possessive ending the final consonant of an ending is dropped, so that the nominative
and the genitive coincide, as in *ove-mme* 'our door, of our door', and the illative loses its
-n, as in *auto-o-ni* 'into my car'. The translative is -kse. After a case ending in a short
vowel the third person is usually -Vn, as in *talo-ssa-an* 'in his house', beside the older
-nsA, except after a partitive -A that follows a stem-final A, as in *kala-a-nsa* (§14.1).

## Main definitions

* `Finnish.Clitic`: the common clitics.
* `Finnish.Nominal.Slot`, `Finnish.Nominal.Exponent`, `Finnish.Nominal.template`: the positions,
  their exponents and their order.
* `Finnish.Nominal.WellFormed`: the strings of endings that make a word.
* `Finnish.Nominal.realize`: the surface forms of a stem with a string of endings.

## Main results

* `Finnish.Nominal.not_wellFormed_nominativePlural_case`,
  `Finnish.Nominal.not_wellFormed_comitative`: the nominative plural takes no case ending and a
  comitative needs a possessive ending.
* `Finnish.Nominal.continuations_third`: the third-person possessive ending after the inessive
  and after the illative.
* `Finnish.Nominal.realize_gen_possessive`: with a possessive ending the genitive is the
  nominative.

## Implementation notes

The genitive plural -ten, which follows the consonant stem of the singular without the plural
-i, as in *nais-ten* 'of the women', is not represented, nor the rarer clitics -kA and -s, nor
the passive of the E infinitive. Which alternant of an ending a stem takes is not represented
either, so a stem has every form its endings allow.

## References

* [karlsson-2017]
-/

@[expose] public section

namespace Finnish

open Phonology Agreement

/-- The common clitics (§25.6). -/
inductive Clitic where
  /-- -kO, of yes-no questions. -/
  | kO
  /-- -kin 'also, too'. -/
  | kin
  /-- -kAAn '(not) either', -kin of negative sentences. -/
  | kAAn
  /-- -hAn, emphasis. -/
  | hAn
  /-- -pA, emphasis. -/
  | pA
  deriving DecidableEq, Repr

/-- The form of a clitic. -/
def Clitic.form : Clitic → List Segment
  | .kO => [k, O]
  | .kin => [k, i, n]
  | .kAAn => [k, A, A, n]
  | .hAn => [h, A, n]
  | .pA => [p, A]

namespace Nominal

open Number.System (singularPlural)

/-- The positions of the endings of a nominal and of a non-finite verb form. -/
inductive Slot where
  /-- The function ending of an infinitive. -/
  | function
  /-- The plural. -/
  | number
  /-- The case ending. -/
  | case
  /-- The possessive ending. -/
  | possession
  /-- The clitics. -/
  | clitic
  deriving DecidableEq, Repr

/-- The endings of each position. -/
inductive Exponent : Slot → Type where
  /-- The function ending of an infinitive. -/
  | infinitive (i : Infinitive) : Exponent .function
  /-- The nominative plural -t. -/
  | nominativePlural : Exponent .number
  /-- The plural -i of the cases other than the nominative. -/
  | plural : Exponent .number
  /-- A case ending. -/
  | case (c : Case) : Exponent .case
  /-- A possessive ending, a cell of `Finnish.Possession.endings`. -/
  | possessive (p : Bundle) : Exponent .possession
  /-- A clitic. -/
  | clitic (c : Clitic) : Exponent .clitic
  deriving DecidableEq

open RegularExpression in
/-- The endings come in the order function, number, case and possessive, each of which a word may
lack, and are followed by any number of clitics (§3.1, §3.3). -/
def template : RegularExpression Slot :=
  sublists [.function, .number, .case, .possession] * (char .clitic).star

variable {σ : Slot}

/-- An ending determines the value of its own position, and the nominative plural also determines
the case, the comitative the number, and an infinitive the number, which is never marked. A clitic
determines none. -/
def Exponent.fills : Exponent σ → List Slot
  | .infinitive _ => [.function, .number]
  | .nominativePlural => [.number, .case]
  | .plural => [.number]
  | .case .com => [.case, .number]
  | .case _ => [.case]
  | .possessive _ => [.possession]
  | .clitic _ => []

/-- The case an ending realizes. -/
def Exponent.case? : Exponent σ → Option Case
  | .nominativePlural => some .nom
  | .case c => some c
  | _ => none

/-- The infinitive an ending is the function ending of. -/
def Exponent.infinitive? : Exponent σ → Option Infinitive
  | .infinitive i => some i
  | _ => none

/-- The case of a string of endings, the nominative if none realizes one. -/
def caseOf (es : List (Σ σ, Exponent σ)) : Case := (es.findSome? (·.2.case?)).getD .nom

/-- The string of endings has a possessive ending. -/
def HasPossessive (es : List (Σ σ, Exponent σ)) : Prop := ∃ e ∈ es, e.1 = .possession

instance (es : List (Σ σ, Exponent σ)) : Decidable (HasPossessive es) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A string of endings makes a word when they are in the order of the template, no position is
determined twice, a comitative is followed by a possessive ending, and an infinitive is in one
of its cases, its translative with a possessive ending. -/
def WellFormed (es : List (Σ σ, Exponent σ)) : Prop :=
  es.map Sigma.fst ∈ template.matches' ∧ (es.flatMap (·.2.fills)).Nodup ∧
    (caseOf es = .com → HasPossessive es) ∧
    ∀ i ∈ es.findSome? (·.2.infinitive?),
      caseOf es ∈ i.cases ∧ (i = .a ∧ caseOf es = .transl → HasPossessive es)

instance : DecidablePred WellFormed := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The nominative plural takes no case ending: *pullo-t* but not *pullo-t-ssa*. -/
theorem not_wellFormed_nominativePlural_case (c : Case) :
    ¬ WellFormed [⟨_, .nominativePlural⟩, ⟨_, .case c⟩] := by
  intro h
  have := h.2.1
  cases c <;> simp_all [Exponent.fills]

/-- A comitative needs a possessive ending: *vaimo-ine-ni* but not *vaimo-ine*. -/
theorem not_wellFormed_comitative : ¬ WellFormed [⟨_, .case .com⟩] := by
  decide

/-! ### Realization -/

/-- Finnish nominals distinguish the singular and the plural. -/
abbrev numberSystem : Number.System := .singularPlural

/-- The endings of the case `c` in the number `num`, where in the plural the genitive is -en, or
-den or -tten (§13.1.2), the partitive -A or -tA and the illative -hVn or -siin. -/
def caseEndings (num : numberSystem.values) (c : Case) : List (List Segment) :=
  singularPlural.elim (Declension.endings c)
    (match c with
    | .gen => [[e, n], [d, e, n], [t, t, e, n]]
    | .part => [[A], [t, A]]
    | .ill => [[h, V, n], [s, i, i, n]]
    | c => Declension.endings c) num

/-- Before a possessive ending the translative -ksi is -kse, and a final consonant is dropped. -/
def beforePossessive (x : List Segment) : List Segment :=
  if x = [k, s, i] then [k, s, e]
  else if ∀ y ∈ x.getLast?, y.IsVowel then x else x.dropLast

/-- Every ending of the case ends in a vowel, as those of the local cases, the partitive, the
essive, the translative, the abessive and the comitative do. -/
def EndsInVowel (c : Case) : Prop := ∀ x ∈ Declension.endings c, ∃ y ∈ x.getLast?, y.IsVowel

instance (c : Case) : Decidable (EndsInVowel c) := inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The forms of the possessive ending of the cell `p` after the word `w`, whose last case
ending is of the case `c`: after a case ending in a short vowel the third person is -Vn or
-nsA, except after a partitive -A that follows a stem-final A. -/
def possessiveForms (p : Bundle) (c : Option Case) (w : List Segment) : List (List Segment) :=
  if p.person = .third ∧ (∃ c' ∈ c, EndsInVowel c') ∧
      ¬ (c = some .part ∧ (w.rtake 2 = [a, A] ∨ w.rtake 2 = [ä, A])) then
    [[V, n], [n, s, A]]
  else (Possession.endings.realize p).toList

/-- The next ending is a possessive ending. -/
def BeforePossessive (es : List (Σ σ, Exponent σ)) : Prop := ∃ e ∈ es.head?, e.1 = .possession

instance (es : List (Σ σ, Exponent σ)) : Decidable (BeforePossessive es) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The underlying forms of the word `w` followed by the endings `es`, where `num` is the number
the preceding endings mark and `c` the case of the last case ending. The plural -i is -j between two
vowels (§5.4). -/
def continuations (w : List Segment) (num : numberSystem.values) (c : Option Case) :
    List (Σ σ, Exponent σ) → List (List Segment)
  | [] => [w]
  | ⟨_, .infinitive i⟩ :: es => continuations (i.base w) num c es
  | ⟨_, .nominativePlural⟩ :: es =>
    continuations (w ++ if BeforePossessive es then [] else [t]) (numberSystem.value .plural) c es
  | ⟨_, .plural⟩ :: es =>
    (continuations (w ++ [i]) (numberSystem.value .plural) c es).map fun x ↦
      if (∃ y ∈ w.getLast?, y.IsVowel) ∧ ∃ y ∈ x[w.length + 1]?, y.IsVowel then x.set w.length j
      else x
  | ⟨_, .case c'⟩ :: es =>
    (caseEndings num c').flatMap fun x ↦
      continuations (w ++ if BeforePossessive es then beforePossessive x else x) num (some c') es
  | ⟨_, .possessive p⟩ :: es =>
    (possessiveForms p c w).flatMap fun x ↦ continuations (w ++ x) num c es
  | ⟨_, .clitic k⟩ :: es => continuations (w ++ k.form) num c es

/-- The surface forms of the stem `w` with the endings `es`. -/
def realize (w : List Segment) (es : List (Σ σ, Exponent σ)) : List (List Segment) :=
  (continuations w (numberSystem.value .singular) none es).map surface

/-- The third person is -Vn or -nsA after the inessive, as in *talo-ssa-an* 'in his house', and
-nsA alone after the illative, whose endings end in a consonant, as in *talo-o-nsa* 'into his
house'. -/
theorem continuations_third :
    continuations [] (numberSystem.value .singular) none [⟨_, .case .ine⟩,
                                 ⟨_, .possessive (.personNumber .third .singular)⟩] =
        [[s, s, A, V, n], [s, s, A, n, s, A]] ∧
      continuations [] (numberSystem.value .singular) none [⟨_, .case .ill⟩,
                                   ⟨_, .possessive (.personNumber .third .singular)⟩] =
        [[V, n, s, A], [h, V, n, s, A], [s, e, e, n, s, A]] := by
  decide

/-- With a possessive ending the genitive is the nominative, as in *ove-mme* 'our door, of our
door'. -/
theorem realize_gen_possessive (w : List Segment) (p : Bundle) :
    realize w [⟨_, .case .gen⟩, ⟨_, .possessive p⟩] = realize w [⟨_, .possessive p⟩] := by
  have hn : ¬ n.IsVowel := by decide
  have hg : ¬ EndsInVowel .gen := by decide
  simp [realize, continuations, caseEndings, Declension.endings, beforePossessive,
    BeforePossessive, possessiveForms, hn, hg]

end Nominal

end Finnish
