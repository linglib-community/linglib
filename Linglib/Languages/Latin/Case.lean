module

public import Linglib.Syntax.Feature.Case.Function

/-!
# Latin case

The traditional description of Latin has six cases: nominative, vocative, accusative, genitive,
dative and ablative. The vocative is a form of address standing outside the clause, and it is
distinct from the nominative only in the singular of non-neuter second-declension nouns
(`Latin.Declension`).

The ablative continues three cases that were once distinct, an ablative, a locative and an
instrumental, and it expresses source, location and instrument accordingly. A separate locative
survives for names of towns and a few nouns such as *domī* 'at home'. The goal of motion is
expressed by the accusative, there being no allative; the dative with verbs of motion is mainly
poetic ([pinkster-2015] §10.11, [greenough-kittredge-howard-dooge-1903] §428) and is not among
the functions of the dative here. Blake takes Latin as his running example of an
inflectional case system.

## Main definitions

* `Latin.Case`: the six cases, in the order of the school paradigms.
* `Latin.Case.label`, `Latin.Case.functions`: the comparative value each case is named for, and
  the functions it marks.

## References

* [blake-1994]
* [greenough-kittredge-howard-dooge-1903]
* [pinkster-2015]
* [pinkster-2021]
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
and the ablative location and instrument as well as source. The dative marks the recipient of a
verb of transfer and the addressee of one of communication ([pinkster-2015] §4.52), the
experiencer of *libet* 'it pleases' (§4.27), the possessor with *sum* (§4.26), the agent with the
gerundive and, mainly in the perfect, with the passive (§5.8), the beneficiary (§10.70), the
one whose inalienable part an argument is, *mi malae dolent* 'my jaws hurt', the sympathetic
dative (§10.96), the one from whose perspective the clause is viewed, the *dativus iudicantis*
(§10.102), and, not frequently, the purpose in a gerund or gerundive clause, *alligando fasces*
'for tying up bundles' ([pinkster-2021] §§16.100, 16.106). The dative of a noun traditionally
called of purpose ([greenough-kittredge-howard-dooge-1903] §382) is for Pinkster a beneficiary
with an abstract noun (§10.70) or a predicative dative (§9.34), and is not what the purpose
function here records. -/
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
