module

public import Linglib.Data.Examples.Ozaki2026
public import Linglib.Syntax.Case.Dependent
public import Linglib.Syntax.Minimalist.Verbal.Voice
public import Linglib.Fragments.Japanese.Verbs
public import Linglib.Fragments.Japanese.Voice
public import Linglib.Semantics.ArgumentStructure.Unaccusativity

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

/-- Every example's judgment is its diagnostic's verdict, whatever the marking of the
source. -/
theorem judgment_eq_verdict : ∀ e ∈ Examples.all, e.judgment = verdict (diagnostic e) := by decide

/-- Both markings are attested with each marking-sensitive diagnostic, the source eliding and
scrambling and the wh-adjunct out under accusative and under ablative alike. -/
theorem diagnostics_both_markings :
    ∀ m ∈ ["acc", "abl"],
      (∃ e ∈ Examples.all, marking e = some m ∧ diagnostic e = some "ellipsis" ∧
        e.judgment = .acceptable) ∧
      (∃ e ∈ Examples.all, marking e = some m ∧ diagnostic e = some "scrambling" ∧
        e.judgment = .acceptable) ∧
      ∃ e ∈ Examples.all, marking e = some m ∧ diagnostic e = some "nani_o" ∧
        e.judgment = .ungrammatical := by
  decide

/-- The Fragment records both verbs with non-thematic Voice, from which their unaccusativity
is derived, and as non-passivizable. -/
theorem alternation_verbs_unaccusative :
    ∀ v ∈ [Japanese.hanareru, Japanese.deru],
      v.voiceType = some .nonThematic ∧ v.IsUnaccusative ∧
        v.passivizable = false := by
  decide

/-- The direct passive requires a verb introducing an external argument, which the
non-thematic head does not provide, so (20) is out. -/
theorem not_directPassivizable :
    ¬ Japanese.DirectPassivizable Japanese.hanareru ∧ ¬ anticausative.AssignsTheta := by
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

/-- In the ablative variant the lexical ablative bleeds dependent accusative, and the leaver
is unaffected. -/
theorem abl_variant :
    (cases ablVariant).valueOf .source = some (.abl, .lexical) ∧
      (cases ablVariant).valueOf .leaver = some (.nom, .unmarked) := by
  decide

/-- The accusative needs no thematic Voice, since the non-thematic head assigns no θ-role
and the source's accusative is configurational rather than assigned by a functional head. -/
theorem accusative_without_voice :
    ¬ anticausative.AssignsTheta ∧
      ((cases accVariant).valueOf .source).map (·.2) = some .dependent := by
  decide

end Ozaki2026
