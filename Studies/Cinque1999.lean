module

public import Linglib.Syntax.Cartography

/-!
# Cinque (1999): the order of clausal functional heads

Chapter 3 orders the clausal functional heads pair by pair, each pair from the order of suffixes,
particles or auxiliaries in some languages, and recapitulates the pairs in §3.6; by transitivity
they give a single order, the first approximation (96). An order extends a list of pairs when it
puts the first head of each pair above the second. (96) extends the recapitulated pairs, but they
do not fix it: they leave celerative and completive aspect unordered with retrospective through
prospective aspect (95), and an order that puts these below perfect aspect but above retrospective
aspect extends them too. (96) moves root modality from above perfect aspect, where the suffix order
(19) puts it, to the level of prospective aspect. The second approximation (92),
`Cartography.Head`, extends the pairs and (19), root modality aside, once the split heads are
identified, except that it puts the lower completive below the lower repetitive and frequentative
aspects, the conflict between Fula and Italian that Cinque leaves open (§4.27): no choice among the
split heads of (92) keeps the chain of perfect, celerative, completive and repetitive aspect.

## Main statements

* `extends_evidence_first`: (96) extends the recapitulated pairs.
* `extends_evidence_firstVariant`: so does an order with the opposite choice in (95).
* `not_extends_suffixOrder_first`: (96) does not extend (19).
* `extends_second`: (92) extends the pairs other than completive above repetitive and iterative
  aspect, and (19).
* `not_chain_second`: no choice of split heads in (92) keeps the Fula chain.

## Implementation notes

* The heads are those of (96). A position of a stated order may hold several heads, ordered by
  neither ("/" in (19) and (96)).
* The pairs are the headings of §3.6, with the orders of Fula and Navajo below (95), of (30) and
  n. 61 for durative aspect, of the auxiliaries (21) and Thai (93) for Voice. Cinque flags two as
  without evidence, irrealis mood above habitual aspect and perfect above retrospective aspect; the
  heading prospective above completive aspect, which the corpus does not determine, and
  retrospective above durative aspect, placed "without real evidence", are left out.
* No pair of §3.6 places root modality among the aspects; its move below them in (96) follows the
  remark opening §3.6 that the Turkish suffix *-Ebil* is permission or ability in its lower
  position. (92) places none of the ability and obligation modals of the chapter's data, so the
  comparison with (92) leaves root modality out.
* (96) prints no `>` between Voice and celerative aspect at a line break; the reading supplies it,
  as Fula's V-COMPLETIVE-CELERATIVE-VOICE does. The celerative and completive of (95) are those of
  (92) below Voice, as §4.25 and §4.26 identify them; repetitive and iterative aspect are the lower
  repetitive and frequentative.

## References

* [cinque-1999]
-/

@[expose] public section

namespace Cinque1999

/-- The heads of the first approximation (96). -/
inductive Head
  | moodSpeechAct
  | moodEvaluative
  | moodEvidential
  | modEpistemic
  | tPast
  | tFuture
  | moodIrrealis
  | modRoot
  | aspHabitual
  | tAnterior
  | aspPerfect
  | aspRetrospective
  | aspDurative
  | aspProgressive
  | aspProspective
  | voice
  | aspCelerative
  | aspCompletive
  | aspRepetitive
  | aspIterative
  deriving DecidableEq, Fintype, Repr

open Head

/-- The position of a head in a stated order, counted from the top. -/
def level (o : List (List Head)) (h : Head) : ℕ := o.findIdx (h ∈ ·)

/-- An order, given by its positions from the top, extends a list of pairs when it puts the first
head of each pair above the second. -/
def Extends (o : List (List Head)) (ps : List (Head × Head)) : Prop :=
  ∀ p ∈ ps, level o p.1 < level o p.2

instance (o : List (List Head)) (ps : List (Head × Head)) : Decidable (Extends o ps) :=
  inferInstanceAs (Decidable (∀ p ∈ ps, _))

/-- The pairs a stated order asserts, each head of a position above each head of a lower one. -/
def pairs : List (List Head) → List (Head × Head)
  | [] => []
  | l :: rest => l.flatMap (fun a ↦ rest.flatten.map (a, ·)) ++ pairs rest

/-- The pairs of §3.6, from (71)–(94); below (95), Fula's celerative, completive, repetitive and
iterative and Navajo's repetitive above iterative; durative aspect from (30) and n. 61; perfect
above progressive aspect above Voice from (21), and prospective aspect above Voice from (93). -/
def evidence : List (Head × Head) :=
  [(moodSpeechAct, moodEvaluative), (moodEvaluative, moodEvidential),
    (moodEvidential, modEpistemic), (modEpistemic, tPast), (tPast, tFuture),
    (tFuture, moodIrrealis), (moodIrrealis, modRoot), (moodIrrealis, aspHabitual),
    (aspHabitual, tAnterior), (aspHabitual, aspPerfect), (tAnterior, aspPerfect),
    (aspPerfect, aspRetrospective), (tAnterior, aspRetrospective),
    (aspRetrospective, aspProgressive), (aspProgressive, aspProspective),
    (aspHabitual, aspDurative), (tAnterior, aspDurative), (aspDurative, aspProgressive),
    (aspPerfect, aspCelerative), (aspCelerative, aspCompletive), (aspCompletive, aspRepetitive),
    (aspCompletive, aspIterative), (aspRepetitive, aspIterative), (aspPerfect, aspProgressive),
    (aspProgressive, voice), (aspProspective, voice)]

/-- The first approximation (96). -/
def first : List (List Head) :=
  [[moodSpeechAct], [moodEvaluative], [moodEvidential], [modEpistemic], [tPast], [tFuture],
    [moodIrrealis], [aspHabitual], [tAnterior], [aspPerfect], [aspRetrospective], [aspDurative],
    [aspProgressive], [aspProspective, modRoot], [voice], [aspCelerative], [aspCompletive],
    [aspRepetitive], [aspIterative]]

/-- (96) with celerative, completive, repetitive and iterative aspect between perfect and
retrospective aspect, Voice last. -/
def firstVariant : List (List Head) :=
  [[moodSpeechAct], [moodEvaluative], [moodEvidential], [modEpistemic], [tPast], [tFuture],
    [moodIrrealis], [aspHabitual], [tAnterior], [aspPerfect], [aspCelerative], [aspCompletive],
    [aspRepetitive], [aspIterative], [aspRetrospective], [aspDurative], [aspProgressive],
    [aspProspective, modRoot], [voice]]

/-- The order of verbal suffixes (19), §3.1. -/
def suffixOrder : List (List Head) :=
  [[moodSpeechAct], [moodEvaluative], [moodEvidential], [modEpistemic], [tPast], [tFuture],
    [moodIrrealis], [modRoot, aspHabitual, tAnterior], [aspPerfect],
    [aspProgressive, aspCompletive, voice]]

theorem extends_evidence_first : Extends first evidence := by decide

theorem extends_evidence_firstVariant : Extends firstVariant evidence := by decide

theorem level_aspProspective_aspCompletive :
    level first aspProspective < level first aspCompletive ∧
      level firstVariant aspCompletive < level firstVariant aspProspective := by
  decide

theorem not_extends_suffixOrder_first : ¬ Extends first (pairs suffixOrder) := by decide

/-! ### The second approximation -/

/-- The head of (92) a head of (96) is, where (92) has one. -/
def toSecond : Head → Option Cartography.Head
  | moodSpeechAct => some .moodSpeechAct
  | moodEvaluative => some .moodEvaluative
  | moodEvidential => some .moodEvidential
  | modEpistemic => some .modEpistemic
  | tPast => some .tPast
  | tFuture => some .tFuture
  | moodIrrealis => some .moodIrrealis
  | modRoot => none
  | aspHabitual => some .aspHabitual
  | tAnterior => some .tAnterior
  | aspPerfect => some .aspPerfect
  | aspRetrospective => some .aspRetrospective
  | aspDurative => some .aspDurative
  | aspProgressive => some .aspGenericProgressive
  | aspProspective => some .aspProspective
  | voice => some .voice
  | aspCelerative => some .aspCelerativeII
  | aspCompletive => some .aspSgCompletiveII
  | aspRepetitive => some .aspRepetitiveII
  | aspIterative => some .aspFrequentativeII

/-- (92) puts the second head of a pair below the first, where it has both. -/
def SecondOrders (p : Head × Head) : Prop := ∀ a ∈ toSecond p.1, ∀ b ∈ toSecond p.2, b < a

instance (p : Head × Head) : Decidable (SecondOrders p) := by
  unfold SecondOrders; infer_instance

theorem extends_second :
    (∀ p ∈ evidence, p ∉ [(aspCompletive, aspRepetitive), (aspCompletive, aspIterative)] →
        SecondOrders p) ∧
      SecondOrders (aspRepetitive, aspCompletive) ∧ SecondOrders (aspIterative, aspCompletive) ∧
      ∀ p ∈ pairs suffixOrder, SecondOrders p := by
  decide +kernel

theorem not_chain_second :
    ∀ c ∈ [Cartography.Head.aspCelerativeI, .aspCelerativeII],
      ∀ k ∈ [Cartography.Head.aspSgCompletiveI, .aspSgCompletiveII, .aspPlCompletive],
        ∀ r ∈ [Cartography.Head.aspRepetitiveI, .aspRepetitiveII],
          ¬ (c < .aspPerfect ∧ k < c ∧ r < k) := by
  decide

end Cinque1999
