module

public import Linglib.Fragments.English.Verbs.Attitude
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes

/-!
# English complementizers

The four English subordinators: *that* and *for*, which mark finite and infinitival
declaratives, and *whether* and its variant *if*, which mark closed interrogatives. *that*
fixes no mood, since the matrix predicate licenses a subjunctive (*we insist that the work be
finished*, *\*we hope that the work be finished*), and *if*, unlike *whether*, types no
infinitival (*she can't make up her mind whether to accept*, *\*if to accept*). Conditional
*if* is `English.Conditionals.if_`, the preposition *for* is `English.Adpositions.for_`, and
the infinitival marker *to* is `English.Auxiliaries.toInf`.

## TODO

*for* requires an overt accusative subject right after it (*for her to be interviewed*), a
requirement the selection relation reads off the position alone, so every infinitival frame
takes *for*, the raising and control frames included.

## References

* [huddleston-pullum-2002]
* [noonan-2007]
-/

@[expose] public section

namespace English.Complementizers

/-- *that*, the subordinator of finite declaratives, omissible under most verbs. The clause is
indicative or, under a mandative predicate, subjunctive ([huddleston-pullum-2002] ch. 11
§3.2, §7.1.1), so no coding is recorded. -/
def that : Complementizer where
  morphs := [.free "that"]
  types := .only .declarative
  verbForm := some .Fin

/-- *if*, the variant of *whether* confined to finite clauses ([huddleston-pullum-2002]
ch. 11 §5.2). -/
def if_ : Complementizer where
  morphs := [.free "if"]
  coding := some .indicative
  types := .of {.polar, .alternative}
  verbForm := some .Fin

/-- *whether*, the subordinator of closed interrogatives, finite or infinitival. -/
def whether : Complementizer where
  morphs := [.free "whether"]
  types := .of {.polar, .alternative}

/-- *for*, the subordinator of infinitival declaratives with a subject
([huddleston-pullum-2002] ch. 14 §1.4.1). -/
def for_ : Complementizer where
  morphs := [.free "for"]
  coding := some .infinitive
  types := .only .declarative
  verbForm := some .Inf

/-- The complementizers. -/
def complementizers : List Complementizer := [that, if_, whether, for_]

/-- The infinitival interrogative complement, *make up one's mind whether to accept*. -/
def infinitivalQuestion : ArgumentFrame :=
  ⟨some .nominal, [.clausal (coding := some .infinitive) (types := .interrogatives)]⟩

/-! ### Selection -/

/-- A mandative subjunctive is a *that*-clause. -/
theorem subjunctiveClause_takes_that : ArgumentFrame.subjunctiveClause.Takes that := by
  decide

/-- An infinitival interrogative takes *whether* and not *if*. -/
theorem infinitivalQuestion_takes :
    infinitivalQuestion.Takes whether ∧ ¬ infinitivalQuestion.Takes if_ := by
  decide

/-- *know* takes declaratives and interrogatives. -/
theorem typers_know : Verbs.know.typers complementizers = [that, if_, whether] := by
  decide

/-- *believe* takes declaratives only. -/
theorem typers_believe : Verbs.believe.typers complementizers = [that] := by
  decide

/-- *wonder* takes interrogatives only. -/
theorem typers_wonder : Verbs.wonder.typers complementizers = [if_, whether] := by
  decide

end English.Complementizers
