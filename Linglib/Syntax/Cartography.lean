module

public import Linglib.Core.Order.OrdConnected
public import Linglib.Syntax.Minimalist.ExtendedProjection
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Tactic.DeriveFintype

/-!
# The hierarchy of clausal functional heads

Cinque matches the order of adverb classes against the order of the clausal functional heads that
morphology and scope reveal, and finds the two aligned one to one: each adverb class is the
specifier of one head. The result is his universal hierarchy of clausal functional projections, a
linear order of heads from the speech-act mood at the top to the lower completive aspect at the
bottom. `Cartography.Head` is that order, its constructors listed bottom-up, each with the adverb
class Cinque pairs with it, and `Cartography.Head.family` reads off the kind of head his label
names: a mood, a modality, a tense, an aspect or Voice.

A clause that projects up to a head contains every head below it, so the heads of a clause of size
`h` are the lower set `Set.Iic h`, and the heads in a clause of size `b` but not in one of size `a`
form the interval `Set.Ioc a b` (`Set.Iic_sdiff_Iic`). A later proposal that adds heads to
Cinque's refines the order: its hierarchy receives an order embedding of `Cartography.Head`, and a
head it places immediately above or below one of Cinque's covers it or is covered by it. The
categorial features of `Minimalist.Cat` coarsen the order: `Cartography.Head.cat` sends each head
to its category, and a higher head's category has at least as high an F-value in the verbal
extended projection, so each F-value is taken by an interval of the hierarchy. Cinque's own kinds of head are not:
moods, modalities, tenses and aspects interleave.

## Main definitions

* `Cartography.Head`: the heads of the universal hierarchy, with its linear order.
* `Cartography.Head.family`: the kind of head, `Cartography.Family`.
* `Cartography.Head.cat`: the category of a head in `Minimalist.Cat`.

## Main statements

* `Cartography.Head.monotone_fValue_cat`: the F-values of the categories are monotone in the
  hierarchy.
* `Cartography.Head.not_isContiguous_family`: the kinds of head are not intervals of it.

## Implementation notes

* The order is Cinque's second approximation of the hierarchy. His first approximation has a root
  modal head among the lowest aspects. The second keeps the volitional modal as its only root
  head, below habitual and the higher repetitive and frequentative aspects, and orders volition
  above obligation and ability or permission without placing those two among the heads; they are
  not heads here.
* Cinque marks the pairing of *characteristically* with generic or progressive aspect, and the
  head of *always*, as uncertain.
* `Head.cat` sends Cinque's four aspect heads below Voice to inner aspect, the aspect of the v
  shell, the other aspect heads to outer aspect, and the moods other than the evidential to
  `Cat.Mood`.

## References

* [cinque-1999]
-/

@[expose] public section

namespace Cartography

/-- A head of the universal hierarchy of clausal functional projections, bottom-up, each with the
adverb class in its specifier. -/
inductive Head
  /-- *completely*, the lower singular completive aspect. -/
  | aspSgCompletiveII
  /-- *often*, the lower frequentative aspect. -/
  | aspFrequentativeII
  /-- *again*, the lower repetitive aspect. -/
  | aspRepetitiveII
  /-- *fast*, *early*, the lower celerative aspect. -/
  | aspCelerativeII
  /-- *well*, Voice. -/
  | voice
  /-- *tutto*, plural completive aspect. -/
  | aspPlCompletive
  /-- *completely*, the higher singular completive aspect. -/
  | aspSgCompletiveI
  /-- *almost*, prospective aspect. -/
  | aspProspective
  /-- *characteristically*, generic or progressive aspect. -/
  | aspGenericProgressive
  /-- *briefly*, durative aspect. -/
  | aspDurative
  /-- *soon*, proximative aspect. -/
  | aspProximative
  /-- *just*, retrospective aspect. -/
  | aspRetrospective
  /-- *always*, perfect aspect. -/
  | aspPerfect
  /-- *still*, continuative aspect. -/
  | aspContinuative
  /-- *no longer*, terminative aspect. -/
  | aspTerminative
  /-- *already*, anterior tense. -/
  | tAnterior
  /-- *quickly*, the higher celerative aspect. -/
  | aspCelerativeI
  /-- *intentionally*, volitional modality. -/
  | modVolitional
  /-- *often*, the higher frequentative aspect. -/
  | aspFrequentativeI
  /-- *again*, the higher repetitive aspect. -/
  | aspRepetitiveI
  /-- *usually*, habitual aspect. -/
  | aspHabitual
  /-- *possibly*, alethic possibility. -/
  | modPossibility
  /-- *necessarily*, alethic necessity. -/
  | modNecessity
  /-- *perhaps*, irrealis mood. -/
  | moodIrrealis
  /-- *then*, future tense. -/
  | tFuture
  /-- *once*, past tense. -/
  | tPast
  /-- *probably*, epistemic modality. -/
  | modEpistemic
  /-- *allegedly*, evidential mood. -/
  | moodEvidential
  /-- *fortunately*, evaluative mood. -/
  | moodEvaluative
  /-- *frankly*, speech-act mood. -/
  | moodSpeechAct
  deriving DecidableEq, Fintype, Repr

/-- The kinds of clausal functional head that Cinque's labels name. -/
inductive Family
  | mood
  | modality
  | tense
  | aspect
  | voice
  deriving DecidableEq, Fintype, Repr

namespace Head

/-- A head is below another when it is merged lower. -/
instance : LinearOrder Head := LinearOrder.lift' Head.ctorIdx (by decide)

/-- The kind of head. -/
def family : Head → Family
  | voice => .voice
  | tAnterior | tFuture | tPast => .tense
  | modVolitional | modPossibility | modNecessity | modEpistemic => .modality
  | moodIrrealis | moodEvidential | moodEvaluative | moodSpeechAct => .mood
  | _ => .aspect

/-- The category of a head among the categorial features. -/
def cat : Head → Minimalist.Cat
  | voice => .Voice
  | aspSgCompletiveII | aspFrequentativeII | aspRepetitiveII | aspCelerativeII => .InnerAsp
  | tAnterior | tFuture | tPast => .T
  | modVolitional | modPossibility | modNecessity | modEpistemic => .Mod
  | moodEvidential => .Evid
  | moodIrrealis | moodEvaluative | moodSpeechAct => .Mood
  | _ => .Asp

theorem family_cat (h : Head) : h.cat.family = .verbal := by
  cases h <;> rfl

theorem monotone_fValue_cat : Monotone fun h : Head ↦ h.cat.fValue := by
  unfold Monotone
  decide

theorem isContiguous_fValue_cat : IsContiguous fun h : Head ↦ h.cat.fValue :=
  monotone_fValue_cat.isContiguous

/-- No order on the kinds of head is coarsened by the hierarchy
(`isContiguous_iff_exists_monotone`): the anterior tense and the volitional modality sit among the
aspects. -/
theorem not_isContiguous_family : ¬ IsContiguous family := by
  unfold IsContiguous
  decide

end Head

end Cartography
