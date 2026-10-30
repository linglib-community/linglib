module

public import Linglib.Discourse.SpeechAct
public import Linglib.Data.Examples.FrancikClark1985
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Linglib.Data.Examples.Readers

/-!
# Francik and Clark (1985): How to Make Requests That Overcome Obstacles to Compliance

This file formalizes [francik-clark-1985]'s obstacle model of requests for information. The
speaker estimates the greatest potential obstacle to getting the information, a preparatory
condition of [searle-1969] that may fail, and overcomes it with a request conditional on that
condition, as *Do you remember what time the concert begins?* means "if you remember, tell me"
and is void if the answer is no. Conditions are ordered by specificity (`PreparatoryCondition`):
having read the announcement is a way of knowing the time, which is a way of being able to tell
it, so *Did you happen to read in the newspaper when the lecture is?*, *Do you know when the
lecture is?* and *Can you tell me when the lecture is?* overcome the same obstacle with
decreasing specificity. A request `Overcomes` an obstacle, the set of doubted conditions, when
each lies in the scope of its `Query`: empty for a direct request, the queried condition and
every way of satisfying it for a conditional request, and everything for the general *Can you
tell me?* and *Could you tell me?*, whose excuse is that the hearer is somehow unable or
unwilling. A direct request overcomes no obstacle (`overcomes_direct_iff`), and a request whose
scope misses the obstacle presupposes what is in doubt: *Do you happen to know your middle
name?* presupposes willingness, *Do you want to tell me what time the lecture is?* knowledge.
The speaker is as specific as the situation allows: a request `Pinpoints` the obstacle when it
is the least that overcomes it, which for a conditional request means the queried condition is
the least upper bound of the doubted ones (`pinpoints_condition_iff`) and for the general request
that no single condition bounds them (`pinpoints_general_iff`), as when a stranger asked for
directions may be unable or unwilling.

Three experiments support the model. In Experiment 1 thirty speakers formulated requests for
twenty-four scenarios in a high- and a low-obstacle version, twelve on the hearer's ability,
eight on willingness and four on the speaker's memory of having asked already; direct requests
fell from 49% to 35% with the obstacle (Table 1), and the indirect forms named the obstacle of
the scenario, *Do you know?* where knowledge was in doubt, *Do you remember?* where memory was,
*Did you see?* where the source was and *Have I asked you?* where the speaker's memory was,
while in the permission and willingness scenarios speakers preferred the general *Could you?* or
sidestepped the obstacle by asking for related information. Experiment 2 ranked the forms for
directness; Table 2 gives the nine forms for asking the time of a student with or without a
watch, the direct *What time is it?* produced only with the watch and every form produced
without it overcoming the doubt (`time_produced_overcomes`). In Experiment 3 eighteen raters
judged five forms in every scenario: each conditional form was rated higher, at either obstacle
level, in the scenario type whose obstacle it overcomes than in those whose obstacle it does not
(`ratings_crossover`), and the general forms, preferred overall, were rated lower at the high
level than at the low (`ratings_general_lt`), as forms that pinpoint no single condition. The
requests the paper discusses are predicted by `Overcomes` (`rows_predicted`), and its gradient
of specificity descends the order on queries (`gradient_antitone`).

## Implementation notes

* *Can you tell me?* and *Could you tell me?* are the general query rather than the ability
  condition, following the paper's gloss of their excuse as "somehow unable or unwilling" and its
  finding that they stay appropriate in the speaker-memory scenarios. No form in the data queries
  the bare ability condition, which describes the obstacle of a speaker unsure whether the hearer
  could find out the information, remember it or be allowed to tell it.
* Table 3 pools the knowledge, memory, source and permission scenarios as the ability type; its
  rows carry knowledge as the type's obstacle. Ratings are recorded in hundredths of a point and
  directness scores in tenths; sidestepping and politeness stay in the prose.
* The examples are `Data.Examples.FrancikClark1985`.

## References

* [francik-clark-1985]
* [searle-1969]
* [clark-1979]
-/

@[expose] public section

namespace FrancikClark1985

open Discourse.SpeechAct

/-- What a request asks about: nothing, one preparatory condition, or anything that could stand
in the way (*Can you tell me?*, *Could you tell me?*). -/
inductive Query
  | direct
  | condition (c : PreparatoryCondition)
  | general
  deriving DecidableEq, Repr

namespace Query

/-- The conditions whose failure voids the request: the queried condition and every way of
satisfying it. -/
def scope : Query → Set PreparatoryCondition
  | direct => ∅
  | condition c => Set.Iic c
  | general => Set.univ

instance : ∀ q : Query, DecidablePred (· ∈ q.scope)
  | direct, _ => .isFalse (Set.notMem_empty _)
  | condition c, d => inferInstanceAs (Decidable (d ≤ c))
  | general, _ => .isTrue (Set.mem_univ _)

theorem scope_injective : Function.Injective scope := by
  have top (c : PreparatoryCondition) : Set.Iic c ≠ Set.univ := λ h =>
    let ⟨d, hd⟩ := exists_not_le c
    hd (Set.eq_univ_iff_forall.1 h d)
  have bot (c : PreparatoryCondition) : Set.Iic c ≠ ∅ := Set.nonempty_Iic.ne_empty
  rintro (_ | c | _) (_ | d | _) h <;> simp only [scope] at h
  · rfl
  · exact absurd h.symm (bot d)
  · exact absurd h Set.empty_ne_univ
  · exact absurd h (bot c)
  · rw [Set.Iic_injective h]
  · exact absurd h (top c)
  · exact absurd h.symm Set.empty_ne_univ
  · exact absurd h.symm (top d)
  · rfl

/-- Queries are ordered by scope, the direct request at the bottom and the general at the top. -/
instance : PartialOrder Query := PartialOrder.lift scope scope_injective

theorem le_def {q q' : Query} : q ≤ q' ↔ q.scope ⊆ q'.scope := Iff.rfl

instance : DecidableLE Query := λ q q' =>
  decidable_of_iff (∀ c, c ∈ q.scope → c ∈ q'.scope) Iff.rfl

instance : BoundedOrder Query where
  bot := direct
  bot_le _ := Set.empty_subset _
  top := general
  le_top _ := Set.subset_univ _

theorem condition_le_condition {c d : PreparatoryCondition} :
    condition c ≤ condition d ↔ c ≤ d :=
  Set.Iic_subset_Iic

end Query

/-- The request overcomes the obstacle `O`, the conditions the speaker doubts, when it is
conditional on each of them. -/
def Overcomes (q : Query) (O : Set PreparatoryCondition) : Prop := O ⊆ q.scope

/-- The request pinpoints the obstacle when it is the least request that overcomes it. -/
def Pinpoints (q : Query) (O : Set PreparatoryCondition) : Prop := IsLeast {q | Overcomes q O} q

variable {q q' : Query} {O O' : Set PreparatoryCondition} {c : PreparatoryCondition}

theorem Overcomes.mono (h : Overcomes q O) (hq : q ≤ q') : Overcomes q' O := h.trans hq

theorem Overcomes.anti (h : Overcomes q O) (hO : O' ⊆ O) : Overcomes q O' := hO.trans h

theorem overcomes_direct_iff : Overcomes .direct O ↔ O = ∅ := Set.subset_empty_iff

theorem overcomes_condition_iff : Overcomes (.condition c) O ↔ c ∈ upperBounds O := Iff.rfl

theorem overcomes_general : Overcomes .general O := Set.subset_univ O

instance : Decidable (Overcomes q {c}) :=
  decidable_of_iff (c ∈ q.scope) Set.singleton_subset_iff.symm

theorem pinpoints_direct_iff : Pinpoints .direct O ↔ O = ∅ :=
  ⟨λ h => overcomes_direct_iff.1 h.1, λ h => ⟨overcomes_direct_iff.2 h, λ _ _ => bot_le⟩⟩

theorem pinpoints_condition_iff : Pinpoints (.condition c) O ↔ IsLUB O c := by
  refine ⟨λ ⟨h, hl⟩ => ⟨h, λ d hd => Query.condition_le_condition.1 (hl hd)⟩,
    λ h => ⟨h.1, ?_⟩⟩
  rintro (_ | d | _) hq
  · obtain ⟨d, hd⟩ := exists_not_ge c
    rw [overcomes_direct_iff.1 hq] at h
    exact absurd (h.2 λ _ h => (Set.notMem_empty _ h).elim) hd
  · exact Query.condition_le_condition.2 (h.2 hq)
  · exact le_top

theorem pinpoints_general_iff : Pinpoints .general O ↔ ¬ BddAbove O := by
  refine ⟨λ ⟨_, hl⟩ ⟨d, hd⟩ => ?_, λ h => ⟨overcomes_general, ?_⟩⟩
  · obtain ⟨e, he⟩ := exists_not_le d
    exact he (hl (overcomes_condition_iff.2 hd) (Set.mem_univ e))
  · rintro (_ | d | _) hq
    · rw [overcomes_direct_iff.1 hq] at h
      exact absurd bddAbove_empty h
    · exact absurd ⟨d, hq⟩ h
    · exact le_rfl

/-- *Would you mind telling me?* pinpoints doubt about willingness; *Could you tell me?* overcomes
it without pinpointing it. -/
example : Pinpoints (.condition .willingness) {.willingness} :=
  pinpoints_condition_iff.2 isLUB_singleton

example : ¬ Pinpoints .general {.willingness} :=
  λ h => pinpoints_general_iff.1 h isLUB_singleton.bddAbove

/-- A stranger asked for directions may be unable or unwilling: only the general request pinpoints
the doubt. -/
example : Pinpoints .general {.ability, .willingness} :=
  pinpoints_general_iff.2 λ ⟨d, hd⟩ => by
    have h₁ : PreparatoryCondition.ability ≤ d := hd (Set.mem_insert _ _)
    have h₂ : PreparatoryCondition.willingness ≤ d := hd (Set.mem_insert_of_mem _ rfl)
    clear hd; revert d; decide

/-! ### The paper's data -/

def queries : List (String × Query) :=
  [("direct", .direct), ("knowledge", .condition .knowledge), ("memory", .condition .memory),
   ("source", .condition .source), ("permission", .condition .permission),
   ("willingness", .condition .willingness), ("speakerMemory", .condition .speakerMemory),
   ("general", .general)]

def conditions : List (String × PreparatoryCondition) :=
  [("ability", .ability), ("knowledge", .knowledge), ("memory", .memory),
   ("source", .source), ("permission", .permission), ("willingness", .willingness),
   ("speakerMemory", .speakerMemory)]

/-- A request the paper discusses: its query, the greatest potential obstacle in its scenario,
whether the paper finds it appropriate, and whether it belongs to the gradient of specificity. -/
structure Row where
  query : Query
  obstacle : PreparatoryCondition
  appropriate : Bool
  gradient : Bool
  deriving DecidableEq

def Row.ofDatum (ex : Datum) : Option Row := do
  let q ← ex.parse? "query" queries
  let o ← ex.parse? "obstacle" conditions
  let a ← ex.parse? "appropriate" [("yes", true), ("no", false)]
  pure ⟨q, o, a, decide (ex.feature? "gradient" = some "yes")⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_predicted :
    ∀ r ∈ rows, (r.appropriate = true ↔ Overcomes r.query {r.obstacle}) := by
  decide

theorem gradient_antitone : ((rows.filter (·.gradient)).map Row.query).Pairwise (· ≥ ·) := by
  decide

/-- A form of Table 2, asking the time of a student without a watch (the high obstacle) or with
one (the low), with the number of the fifteen speakers at each level who produced it. -/
structure TimeForm where
  query : Query
  high : ℕ
  low : ℕ
  deriving DecidableEq

def TimeForm.ofDatum (ex : Datum) : Option TimeForm := do
  let q ← ex.parse? "query" queries
  let h ← ex.nat? "producedHigh"
  let l ← ex.nat? "producedLow"
  pure ⟨q, h, l⟩

def timeForms : List TimeForm := Examples.all.filterMap TimeForm.ofDatum

theorem time_produced_overcomes :
    ∀ r ∈ timeForms, 0 < r.high → Overcomes r.query {.source} := by
  decide

/-- A cell of Table 3: a form's query, the obstacle of the scenario type, and its mean
appropriateness rating at the high and low obstacle levels, in hundredths of a point. -/
structure Rating where
  query : Query
  obstacle : PreparatoryCondition
  high : ℕ
  low : ℕ
  deriving DecidableEq

def Rating.ofDatum (ex : Datum) : Option Rating := do
  let q ← ex.parse? "query" queries
  let o ← ex.parse? "obstacle" conditions
  let h ← ex.nat? "ratingHigh"
  let l ← ex.nat? "ratingLow"
  pure ⟨q, o, h, l⟩

def ratings : List Rating := Examples.all.filterMap Rating.ofDatum

theorem ratings_crossover :
    ∀ r ∈ ratings, ∀ r' ∈ ratings, r.query = r'.query →
      Overcomes r.query {r.obstacle} → ¬ Overcomes r'.query {r'.obstacle} →
        r'.high < r.high ∧ r'.low < r.low := by
  decide

theorem ratings_general_lt : ∀ r ∈ ratings, r.query = .general → r.high < r.low := by
  decide

end FrancikClark1985
