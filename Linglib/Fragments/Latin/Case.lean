module

public import Linglib.Syntax.Case.Function

/-!
# Latin case

The traditional description of Latin has six cases: nominative, vocative, accusative, genitive,
dative and ablative. The vocative is a form of address standing outside the clause, and it is
distinct from the nominative only in the singular of non-neuter second-declension nouns
(`Latin.Declension`).

The ablative continues three cases that were once distinct, an ablative, a locative and an
instrumental, and it expresses source, location and instrument accordingly. A separate locative
survives for names of towns and a few nouns such as *domī* 'at home'. The goal of motion is
expressed by the accusative, there being no allative; the dative of the place to which is a
use of the poets and of later prose ([greenough-kittredge-howard-dooge-1903] §428) and is not
among the functions of the dative here. Blake takes Latin as his running example of an
inflectional case system.

## Main definitions

* `Latin.Case`: the six cases, in the order of the school paradigms.
* `Latin.Case.label`, `Latin.Case.functions`: the comparative value each case is named for, and
  the functions it marks.

## References

* [blake-1994]
* [greenough-kittredge-howard-dooge-1903]
-/

@[expose] public section

namespace Latin

/-- The six cases, in the order of the school paradigms. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The vocative. -/
  | voc
  /-- The accusative. -/
  | acc
  /-- The genitive. -/
  | gen
  /-- The dative. -/
  | dat
  /-- The ablative. -/
  | abl
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a case is named for. -/
def label : Case → _root_.Case
  | nom => .nom
  | voc => .voc
  | acc => .acc
  | gen => .gen
  | dat => .dat
  | abl => .abl

/-- The functions a case marks: the accusative also expresses the goal of motion,
and the ablative location and instrument as well as source. The dative marks the indirect object
of a verb of giving ([greenough-kittredge-howard-dooge-1903] §362), the one pleased or to whom
something seems (§§367, 375), the possessor with *esse* (§373), the agent with the gerundive
(§374), the one benefited (§376), the possessor of what the sentence is about, in place of a
genitive (§377), the person judging (§378), and the purpose or end (§382). -/
def functions : Case → Finset _root_.Case.Function
  | acc => {.argument .P, .spatial none .goal}
  | dat => {.argument .R, .experiencer, .predicativePossessor, .passiveAgent, .beneficiary,
      .externalPossessor, .judicantis, .purpose}
  | abl => {.spatial none .source, .spatial none .place, .instrumental}
  | c => c.label.functions

theorem label_functions_inter_nonempty (c : Case) :
    (c.label.functions ∩ c.functions).Nonempty := by
  cases c <;> decide

end Case

end Latin
