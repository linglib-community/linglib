module

public import Linglib.Data.Examples.Ozaki2026
public import Linglib.Syntax.Case.Dependent
public import Linglib.Syntax.Minimalist.Verbal.Voice
public import Linglib.Fragments.Japanese.Verbs
public import Linglib.Fragments.Japanese.Voice
public import Linglib.Semantics.ArgumentStructure.Unaccusativity
public import Linglib.Data.Examples.Readers

/-!
# Ozaki (2026): Japanese Accusative/Ablative Alternation Verbs Are Unaccusative

This file formalizes Ozaki's argument that the Japanese verbs of departure whose
source argument is marked either accusative *o* or ablative *kara*, *hanareru* 'leave' and
*deru* 'exit', project one dyadic unaccusative structure under both markings. The source is
an argument whatever its marking, since it elides under an overt adjunct, the argumenthood
diagnostic of Funakoshi, and scrambles long-distance, that of Saito; and the
verbs project no thematic Voice (Kratzer) under either marking, since their passive
is the indirect passive, the direct passive with *niyotte* being ungrammatical, and the
accusative wh-adjunct *nani-o* 'why' of Kurafuji is unavailable, as with
unaccusatives. Each diagnostic returns the same verdict for both markings (`verdict`,
`judgment_eq_verdict`, `diagnostics_both_markings`). The alternation is then a matter of case
assignment: *kara* is a lexical ablative assigned by an optional postposition, and *o* is the
dependent accusative assigned to a caseless noun phrase c-commanded by another, which the
ablative bleeds (`acc_variant`, `abl_variant`, `accusative_without_voice`).

## Implementation notes

The examples are the generated rows of `Data/Examples/Ozaki2026`, the (9), (13), and (26)
pairs split into an accusative and an ablative row. The case algorithm is the one-domain
dependent-case assignment of `Syntax/Case/Dependent`, and the absence of thematic Voice is the
non-thematic Voice head of `Syntax/Minimalist/Verbal/Voice`, which the Japanese Fragment records
for both verbs and from which it derives their unaccusativity.

## References

* [ozaki-2026]
* [funakoshi-2016]
* [saito-1985]
* [kurafuji-1997]
* [kratzer-1996]
-/

@[expose] public section

namespace Ozaki2026

open Ozaki2026.Examples Case DependentCase Minimalist.Voice

/-! ### The diagnostics -/

/-- The diagnostic an example applies. -/
def diagnostic (e : Datum) : Option String := e.feature? "diagnostic"

/-- The marking of the source in an example. -/
def marking (e : Datum) : Option String := e.feature? "marking"

/-- The argument's verdict on a diagnostic is that the alternation, the argumenthood
diagnostics and the indirect passive succeed, and the direct passive and the wh-adjunct fail. -/
def verdict : Option String → Judgment
  | some "direct_passive" | some "nani_o" => .ungrammatical
  | _ => .acceptable

theorem judgment_eq_verdict : ∀ e ∈ Examples.all, e.judgment = verdict (diagnostic e) := by decide

theorem diagnostics_both_markings :
    ∀ m ∈ ["acc", "abl"],
      (∃ e ∈ Examples.all, marking e = some m ∧ diagnostic e = some "ellipsis" ∧
        e.judgment = .acceptable) ∧
      (∃ e ∈ Examples.all, marking e = some m ∧ diagnostic e = some "scrambling" ∧
        e.judgment = .acceptable) ∧
      ∃ e ∈ Examples.all, marking e = some m ∧ diagnostic e = some "nani_o" ∧
        e.judgment = .ungrammatical := by
  decide

theorem alternation_verbs_unaccusative :
    ∀ v ∈ [Japanese.hanareru, Japanese.deru],
      v.voiceType = some .nonThematic ∧ v.IsUnaccusative ∧
        v.passivizable = false := by
  decide

-- (20)
theorem not_directPassivizable :
    ¬ Japanese.hanareru.HasExternalArgument ∧ ¬ anticausative.AssignsTheta := by
  decide

/-! ### Case assignment (§3) -/

/-- The participants of *hanareru* 'leave' are the leaver and the source, the leaver
c-commanding the source in the one Spell-Out domain. -/
inductive Participant
  | leaver
  | source
  deriving DecidableEq, Repr

/-- In the accusative variant (28) leaver and source are caseless noun phrases. -/
def accVariant : Participant → Option Case := fun _ ↦ none

/-- In the ablative variant (29) the postposition has valued the source ablative. -/
def ablVariant : Participant → Option Case
  | .leaver => none
  | .source => some .abl

/-- The cases of a variant. -/
def cases (lex : Participant → Option Case) : Valuation Participant (Case × Mechanism) :=
  assignCases .accusative lex [.leaver, .source]

/-- In the accusative variant the source receives dependent accusative by (27) and the
leaver unmarked nominative. -/
theorem acc_variant :
    (cases accVariant).valueOf .source = some (.acc, .dependent) ∧
      (cases accVariant).valueOf .leaver = some (.nom, .unmarked) := by
  decide

theorem abl_variant :
    (cases ablVariant).valueOf .source = some (.abl, .lexical) ∧
      (cases ablVariant).valueOf .leaver = some (.nom, .unmarked) := by
  decide

theorem accusative_without_voice :
    ¬ anticausative.AssignsTheta ∧
      ((cases accVariant).valueOf .source).map (·.2) = some .dependent := by
  decide

end Ozaki2026
