module

public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Discourse.CommonGround
public import Linglib.Fragments.English.Conditionals
public import Linglib.Fragments.Japanese.Conditionals
public import Linglib.Fragments.Mandarin.Conditionals
public import Linglib.Data.Examples.Mizuno2024
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Mizuno (2024): Strategies for Anderson Conditionals

An Anderson conditional has an observed fact as its consequent and argues for its antecedent, as
in *If Jones had taken arsenic, he would show the symptoms he is now showing*. Mizuno finds that
English must X-mark such a conditional while Japanese and Mandarin must O-mark it. Over the live
possibilities `D` the consequent is settled and the conditional is trivial, and X-marking moves to
a larger domain that leaves it open. Japanese *-ta* and Mandarin *le* signal strong
counterfactuality, that the antecedent holds at no live possibility, which the live antecedent of
an Anderson conditional contradicts. Their O-marked conditional instead shifts, like the
historical present, to an earlier time with more live possibilities. The same strong
counterfactuality excludes X-marked future-less-vivid conditionals, so X-marking is available in
both constructions or in neither.

The live possibilities at a time are the context set of the common ground then, the facts
established so far, and they shrink as time goes on. A domain makes a conditional contingent
when it has an antecedent-world and does not settle the consequent. X-marking is felicitous when
some proper extension of `D` does so and its presupposition holds; O-marking when `D` does or,
where X-marking fails, the live possibilities of an earlier time do. With the antecedent live,
X-marking is felicitous
[only without strong counterfactuality](##Mizuno2024.xFelicitous_iff_of_live), whatever the
consequent, so Anderson and future-less-vivid conditionals stand or fall together;
an O-marked Anderson conditional is felicitous
[only with it](##Mizuno2024.oFelicitous_jones_iff); and an ordinary counterfactual is
[X-marked either way](##Mizuno2024.xFelicitous_game). One parameter per language, whether its
X-marking signals strong counterfactuality, predicts
[the judgment of every row and of its alternatives](##Mizuno2024.rows_felicity).

## Implementation notes

Footnote 5 reads `D` as a proxy for the Stalnakerian context set, so a scenario's information is
a common ground at each time, the facts established by then asserted in order, and the live
possibilities are its context set. Contingency asks for an antecedent-world in the domain as well
as an open consequent: footnote 7 has X-marking suspend the falsity of the antecedent in an
ordinary counterfactual as it suspends the truth of the consequent in an Anderson conditional.
Whether the member of (1) who proposes that Jones *must* have
taken arsenic is thereby committed to the antecedent decides whether the premise reading is
felicitous too; `felicitous_iff_of_live` takes that no participant is committed to it as a
hypothesis. A row records its construction and whether its primary text is X-marked or O-marked,
in the terms of [von-fintel-iatridou-2023]; O-marking being the absence of X-marking, the
alternatives of a row carry the marking its primary text lacks.

## References

* [mizuno-2024]
* [anderson-1951]
* [stalnaker-1978]
* [iatridou-1991]
* [haegeman-2003]
* [schlenker-2004a]
* [von-fintel-iatridou-2023]
* [iatridou-2000]
* [ogihara-2014]
* [mizuno-kaufmann-2019]
* [mackay-2015]
* [mackay-2019]
-/

@[expose] public section

namespace Mizuno2024

open Conditional (Reading strictImp mem_strictImp_of_subset)

/-! ### Domains and felicity

A conditional is true when the consequent holds at every antecedent-world of its domain (§1). An
O-marked conditional quantifies over the live possibilities, and is trivial when the consequent
holds throughout them (§2). X-marking expands the domain beyond the live possibilities (§2, after
[mackay-2015] and [mackay-2019]); a strongly counterfactual X-marking further presupposes that
the antecedent holds at no live possibility (§3.2, §4.2). A language whose X-marking cannot serve
may shift the O-marked domain to an earlier time, as in the historical present
([schlenker-2004a]; §3.3), a covert option that the overt one blocks where it serves (fn. 14). -/

/-- Whether a language's X-marking only expands the domain, allowing the unlikeliness reading of
(8), or signals strong counterfactuality. -/
inductive Counterfactuality
  | weak
  | strong
  deriving DecidableEq, Repr

variable {W : Type*} {D D' A C : Set W} {κ : Counterfactuality}

/-- The common ground at a time is the trivial one with every fact dated by then asserted. -/
def commonGround (facts : List (ℤ × Set W)) (t : ℤ) : Filter W :=
  ((facts.filter (·.1 ≤ t)).map (·.2)).foldl (· ⊓ Filter.principal ·) ⊤

theorem antitone_commonGround (facts : List (ℤ × Set W)) : Antitone (commonGround facts) :=
  fun _ _ h ↦ Filter.foldl_inf_principal_anti <| List.map_subset _ fun _ hf ↦ by
    simp only [List.mem_filter, decide_eq_true_eq] at hf ⊢
    exact ⟨hf.1, hf.2.trans h⟩

/-- The live possibilities at a time, the context set of the common ground then. -/
def live (facts : List (ℤ × Set W)) (t : ℤ) : Set W := (commonGround facts t).ker

theorem mem_live {facts : List (ℤ × Set W)} {t : ℤ} {v : W} :
    v ∈ live facts t ↔ ∀ f ∈ facts, f.1 ≤ t → v ∈ f.2 := by
  simp only [live, commonGround, Filter.foldl_inf_principal_top, Filter.ker_principal,
    Set.mem_iInter, List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h f hf ht ↦ h _ ⟨f, ⟨hf, ht⟩, rfl⟩, fun h _ ⟨f, ⟨hf, ht⟩, hp⟩ ↦ hp ▸ h f hf ht⟩

-- §3.3
theorem antitone_live (facts : List (ℤ × Set W)) : Antitone (live facts) :=
  Filter.ker_mono.comp_antitone (antitone_commonGround facts)

/-- A domain makes a conditional contingent when it has an antecedent-world and does not settle
the consequent. -/
def Contingent (D A C : Set W) : Prop := (D ∩ A).Nonempty ∧ ¬ D ⊆ C

theorem Contingent.mono (h : D ⊆ D') (hD : Contingent D A C) : Contingent D' A C :=
  ⟨hD.1.mono (Set.inter_subset_inter_left _ h), fun h' ↦ hD.2 (h.trans h')⟩

theorem contingent_univ : Contingent Set.univ A C ↔ A.Nonempty ∧ C ≠ Set.univ := by
  simp [Contingent, Set.univ_subset_iff]

theorem exists_ssuperset_contingent (hD : D ≠ Set.univ) :
    (∃ D', D ⊂ D' ∧ Contingent D' A C) ↔ A.Nonempty ∧ C ≠ Set.univ :=
  ⟨fun ⟨_, _, h⟩ ↦ contingent_univ.1 (h.mono (Set.subset_univ _)),
    fun h ↦ ⟨Set.univ, Set.ssubset_univ_iff.2 hD, contingent_univ.2 h⟩⟩

/-- An X-marked conditional quantifies over a domain properly extending the live possibilities
`D`. It is felicitous when some such domain makes it contingent and, under strong
counterfactuality, the antecedent holds at no live possibility. -/
def XFelicitous (κ : Counterfactuality) (D A C : Set W) : Prop :=
  (∃ D', D ⊂ D' ∧ Contingent D' A C) ∧ (κ = .strong → Disjoint A D)

/-- An O-marked conditional quantifies over the live possibilities at the time of utterance or,
unless X-marking is felicitous, those at an earlier time. It is felicitous when one of these
domains makes it contingent. -/
def OFelicitous (κ : Counterfactuality) (live : ℤ → Set W) (t : ℤ) (A C : Set W) : Prop :=
  Contingent (live t) A C ∨
    ¬ XFelicitous κ (live t) A C ∧ ∃ t' < t, Contingent (live t') A C

/-- With the antecedent a live possibility, X-marking is felicitous exactly when it does not
signal strong counterfactuality, whatever the consequent: its availability in Anderson and in
future-less-vivid conditionals "stand or fall together" (§4.2). -/
theorem xFelicitous_iff_of_live (hA : ¬ Disjoint A D) (hX : ∃ D', D ⊂ D' ∧ Contingent D' A C) :
    XFelicitous κ D A C ↔ κ = .weak := by
  cases κ <;> simp [XFelicitous, hA, hX]

-- §2, fn. 7
theorem xFelicitous_of_disjoint (hA : Disjoint A D) (hX : ∃ D', D ⊂ D' ∧ Contingent D' A C) :
    XFelicitous κ D A C :=
  ⟨hX, fun _ ↦ hA⟩

theorem oFelicitous_iff_of_not_contingent {live : ℤ → Set W} {t : ℤ}
    (h : ¬ Contingent (live t) A C) :
    OFelicitous κ live t A C ↔
      ¬ XFelicitous κ (live t) A C ∧ ∃ t' < t, Contingent (live t') A C :=
  or_iff_right h

theorem not_decidedBy_of_live {facts : List (ℤ × Set W)} {t : ℤ}
    (h₁ : ¬ live facts t ⊆ A) (h₂ : ¬ Disjoint A (live facts t)) :
    ¬ (Question.polar A).DecidedBy (commonGround facts t) := by
  rw [Question.decidedBy_polar]
  rintro (h | h)
  · exact h₁ (Filter.subset_ker.1 subset_rfl _ h)
  · exact h₂ (Set.subset_compl_iff_disjoint_right.1 (Filter.subset_ker.1 subset_rfl _ h)).symm

theorem felicitous_iff_of_live {P : Type*} {K : Commitment.Table P W}
    {facts : List (ℤ × Set W)} {t : ℤ} (hK : K.commonGround = commonGround facts t)
    (h : ∀ a, A ∉ K.discourseCommitments a) (h₁ : ¬ live facts t ⊆ A)
    (h₂ : ¬ Disjoint A (live facts t)) {ct : Reading} :
    ct.Felicitous K A ↔ ct = .hypothetical :=
  Reading.felicitous_iff_of_not_decidedBy h (hK ▸ not_decidedBy_of_live h₁ h₂)

/-! ### Anderson conditionals (§2, §3)

The scenario of (1): Jones shows symptoms of poisoning, established at the time of utterance `1`,
and nothing establishes which poison he took. -/

/-- In a world of the Jones scenario, Jones took arsenic, a poison with the same symptoms (§3.2),
or no poison. -/
inductive Jones
  | arsenic
  | mimic
  | unpoisoned
  deriving DecidableEq, Repr

/-- The proposition that Jones shows the symptoms, the consequent of (1) and (4). -/
def symptoms : Set Jones := {w | w ≠ .unpoisoned}

/-- The facts of the Jones scenario of (1) and (4). -/
def jonesFacts : List (ℤ × Set Jones) := [(1, symptoms)]

theorem mem_live_jones {v : Jones} {t : ℤ} :
    v ∈ live jonesFacts t ↔ (1 ≤ t → v ≠ .unpoisoned) := by
  simp [jonesFacts, mem_live, symptoms]

-- §2
theorem live_jones_subset_symptoms : live jonesFacts 1 ⊆ symptoms :=
  fun _ hv ↦ mem_live_jones.1 hv le_rfl

-- (2)
theorem oMarking_trivial (A : Set Jones) : (1 : ℤ) ∈ strictImp (live jonesFacts) A symptoms :=
  mem_strictImp_of_subset live_jones_subset_symptoms

theorem unpoisoned_notMem_live_jones : Jones.unpoisoned ∉ live jonesFacts 1 :=
  fun h ↦ mem_live_jones.1 h le_rfl rfl

-- §3.3
theorem live_jones_ssubset_live_zero : live jonesFacts 1 ⊂ live jonesFacts 0 :=
  (Set.ssubset_iff_of_subset (antitone_live jonesFacts zero_le_one)).2
    ⟨.unpoisoned, mem_live_jones.2 (by decide), unpoisoned_notMem_live_jones⟩

-- §3.3
theorem contingent_live_jones_zero : Contingent (live jonesFacts 0) {.arsenic} symptoms :=
  ⟨⟨.arsenic, mem_live_jones.2 (by decide), rfl⟩,
    fun h ↦ h (mem_live_jones.2 (by decide) : Jones.unpoisoned ∈ _) rfl⟩

-- (1b)
theorem arsenic_live : ¬ Disjoint ({.arsenic} : Set Jones) (live jonesFacts 1) :=
  Set.not_disjoint_iff.2 ⟨.arsenic, rfl, mem_live_jones.2 nofun⟩

-- §2
theorem exists_ssuperset_jones :
    ∃ D', live jonesFacts 1 ⊂ D' ∧ Contingent D' {.arsenic} symptoms :=
  (exists_ssuperset_contingent (D := live jonesFacts 1) fun h ↦
      unpoisoned_notMem_live_jones (h ▸ trivial)).2
    ⟨⟨.arsenic, rfl⟩, fun h ↦ (h ▸ trivial : Jones.unpoisoned ∈ symptoms) rfl⟩

/-- An X-marked Anderson conditional is felicitous exactly when the X-marking does not signal
strong counterfactuality: English (1a) and not Japanese (4a) with *-ta* (§3.2). -/
theorem xFelicitous_jones_iff :
    XFelicitous κ (live jonesFacts 1) {.arsenic} symptoms ↔ κ = .weak :=
  xFelicitous_iff_of_live arsenic_live exists_ssuperset_jones

/-- An O-marked Anderson conditional is felicitous iff the X-marking signals strong
counterfactuality, as in Japanese (4a) but not English (2) (§3.3, fn. 14). -/
theorem oFelicitous_jones_iff :
    OFelicitous κ (live jonesFacts) 1 {.arsenic} symptoms ↔ κ = .strong := by
  rw [oFelicitous_iff_of_not_contingent fun h ↦ h.2 live_jones_subset_symptoms,
    xFelicitous_jones_iff]
  cases κ
  · simp
  · exact iff_of_true ⟨nofun, 0, zero_lt_one, contingent_live_jones_zero⟩ rfl

-- (4a), §3.2
theorem xFelicitous_strong_identified :
    XFelicitous .strong (live [(1, {Jones.mimic})] 1) {.arsenic} symptoms := by
  have hD : live [((1 : ℤ), ({.mimic} : Set Jones))] 1 = {.mimic} := by ext v; simp [mem_live]
  rw [hD]
  exact xFelicitous_of_disjoint (Set.disjoint_singleton.2 nofun)
    ((exists_ssuperset_contingent (D := {Jones.mimic}) fun h ↦
      absurd (h ▸ Set.mem_univ Jones.arsenic) nofun).2
      ⟨⟨.arsenic, rfl⟩, fun h ↦ (h ▸ trivial : Jones.unpoisoned ∈ symptoms) rfl⟩)

/-! ### Counterfactual conditionals (§3.1)

The scenario of (3): John has left the team by time `0`, and its defeat is certain by the time
of utterance `1`. -/

/-- In a world of the game scenario, John plays and the outcome is open, or he has left and the
outcome is open or the defeat certain. -/
inductive Game
  | playsOpen
  | awayOpen
  | awayLost
  deriving DecidableEq, Repr

/-- The proposition that the outcome is still uncertain, the consequent of (3). -/
def uncertain : Set Game := {.playsOpen, .awayOpen}

/-- The facts of the game scenario of (3). -/
def gameFacts : List (ℤ × Set Game) := [(0, {w | w ≠ .playsOpen}), (1, {.awayLost})]

theorem live_game : live gameFacts 1 = {.awayLost} := by
  ext v; cases v <;> simp [gameFacts, mem_live]

/-- An X-marked counterfactual conditional is felicitous whether or not the X-marking signals
strong counterfactuality, as Japanese (3) with *-ta* is. -/
theorem xFelicitous_game : XFelicitous κ (live gameFacts 1) {.playsOpen} uncertain := by
  rw [live_game]
  exact xFelicitous_of_disjoint (Set.disjoint_singleton.2 nofun)
    ((exists_ssuperset_contingent (D := {Game.awayLost}) fun h ↦
      absurd (h ▸ Set.mem_univ Game.playsOpen) nofun).2
      ⟨⟨.playsOpen, rfl⟩, fun h ↦ absurd (h ▸ Set.mem_univ Game.awayLost) (by simp [uncertain])⟩)

-- fn. 7
theorem not_oFelicitous_game : ¬ OFelicitous κ (live gameFacts) 1 {.playsOpen} uncertain := by
  rw [oFelicitous_iff_of_not_contingent fun h ↦ by simpa [live_game] using h.1]
  exact fun h ↦ h.1 xFelicitous_game

/-! ### Future-less-vivid conditionals (§4.2)

The scenario of (8): the party is set before the time of utterance `1`, and whether John comes,
and whether the party is fun, is established at time `2`. -/

/-- In a world of the party scenario, John comes and the party is fun, he stays away and the party
is fun anyway or dull, or the party is cancelled. -/
inductive Party
  | johnComes
  | funAnyway
  | dull
  | cancelled
  deriving DecidableEq, Repr

/-- The proposition that the party is fun, the consequent of (8) and (9). -/
def partyFun : Set Party := {.johnComes, .funAnyway}

/-- The facts of the party scenario of (8) and (9), in which John stays away and the party is
dull. -/
def partyFacts : List (ℤ × Set Party) := [(0, {w | w ≠ .cancelled}), (2, {.dull})]

theorem mem_live_party {v : Party} : v ∈ live partyFacts 1 ↔ v ≠ .cancelled := by
  simp [partyFacts, mem_live]

-- (8b)
theorem johnComes_live : ¬ Disjoint ({.johnComes} : Set Party) (live partyFacts 1) :=
  Set.not_disjoint_iff.2 ⟨.johnComes, rfl, mem_live_party.2 nofun⟩

theorem contingent_live_party : Contingent (live partyFacts 1) {.johnComes} partyFun :=
  ⟨⟨.johnComes, mem_live_party.2 nofun, rfl⟩,
    fun h ↦ absurd (h (mem_live_party.2 nofun : Party.dull ∈ _)) (by simp [partyFun])⟩

theorem exists_ssuperset_party :
    ∃ D', live partyFacts 1 ⊂ D' ∧ Contingent D' {.johnComes} partyFun :=
  (exists_ssuperset_contingent (D := live partyFacts 1) fun h ↦
      mem_live_party.1 (h ▸ trivial) rfl).2
    ⟨⟨.johnComes, rfl⟩, fun h ↦ absurd (h ▸ Set.mem_univ Party.dull) (by simp [partyFun])⟩

-- (8), (10), (12)
theorem xFelicitous_party_iff :
    XFelicitous κ (live partyFacts 1) {.johnComes} partyFun ↔ κ = .weak :=
  xFelicitous_iff_of_live johnComes_live exists_ssuperset_party

-- (9), (11)
theorem oFelicitous_party : OFelicitous κ (live partyFacts) 1 {.johnComes} partyFun :=
  .inl contingent_live_party

/-! ### The rows -/

/-- The felicity the account predicts for a strategy in a construction, in a language whose
X-marking has counterfactuality `κ`. -/
def Felicitous (κ : Counterfactuality) : Examples.Construction → Examples.Strategy → Prop
  | .anderson, .xMarking => XFelicitous κ (live jonesFacts 1) {.arsenic} symptoms
  | .anderson, .oMarking => OFelicitous κ (live jonesFacts) 1 {.arsenic} symptoms
  | .counterfactual, .xMarking => XFelicitous κ (live gameFacts 1) {.playsOpen} uncertain
  | .counterfactual, .oMarking => OFelicitous κ (live gameFacts) 1 {.playsOpen} uncertain
  | .flv, .xMarking => XFelicitous κ (live partyFacts 1) {.johnComes} partyFun
  | .flv, .oMarking => OFelicitous κ (live partyFacts) 1 {.johnComes} partyFun

instance (κ : Counterfactuality) : ∀ c m, Decidable (Felicitous κ c m)
  | .anderson, .xMarking => decidable_of_iff _ xFelicitous_jones_iff.symm
  | .anderson, .oMarking => decidable_of_iff _ oFelicitous_jones_iff.symm
  | .counterfactual, .xMarking => isTrue xFelicitous_game
  | .counterfactual, .oMarking => isFalse not_oFelicitous_game
  | .flv, .xMarking => decidable_of_iff _ xFelicitous_party_iff.symm
  | .flv, .oMarking => isTrue oFelicitous_party

/-- English X-marking allows the unlikeliness reading of (8), while Japanese *-ta*
([ogihara-2014], [mizuno-kaufmann-2019]) and Mandarin *le* (§4.2) signal strong
counterfactuality. -/
def counterfactuality (l : Glottocode) : Option Counterfactuality :=
  List.lookup l [(.english, .weak), (.japanese, .strong), (.mandarinChinese, .strong)]

theorem rows_parsed : ∀ e ∈ Examples.all,
    (Examples.construction e).isSome ∧ (Examples.strategy e).isSome ∧
      (counterfactuality e.language).isSome := by
  decide

/-- Every row and its alternatives are judged as predicted, in English (1a), (2) and (8), Japanese
(3), (4a), (7a) and (9), and Mandarin (11) and (13a). -/
theorem rows_felicity :
    ∀ e ∈ Examples.all, ∀ c ∈ Examples.construction e, ∀ m ∈ Examples.strategy e,
      ∀ κ ∈ counterfactuality e.language,
        (e.JudgedFelicitous ↔ Felicitous κ c m) ∧
          ∀ j ∈ e.contrasts.map Prod.snd, ∀ m' ≠ m, (j = .acceptable ↔ Felicitous κ c m') := by
  decide

/-! ### The conditional markers

Both scenarios leave the antecedent open, so with no participant committed to it a conditional
is read hypothetically, and the markers heading the rows are attested marking hypothetical
conditionals. -/

theorem felicitous_jones_iff {P : Type*} {K : Commitment.Table P Jones}
    (hK : K.commonGround = commonGround jonesFacts 1)
    (h : ∀ a, {.arsenic} ∉ K.discourseCommitments a) {ct : Reading} :
    ct.Felicitous K {.arsenic} ↔ ct = .hypothetical :=
  felicitous_iff_of_live hK h
    (fun h' ↦ absurd (h' (mem_live_jones.2 nofun : Jones.mimic ∈ _)) nofun) arsenic_live

theorem felicitous_party_iff {P : Type*} {K : Commitment.Table P Party}
    (hK : K.commonGround = commonGround partyFacts 1)
    (h : ∀ a, {.johnComes} ∉ K.discourseCommitments a) {ct : Reading} :
    ct.Felicitous K {.johnComes} ↔ ct = .hypothetical :=
  felicitous_iff_of_live hK h
    (fun h' ↦ absurd (h' (mem_live_party.2 nofun : Party.dull ∈ _)) nofun) johnComes_live

/-- The rows of each sampled language are headed by English *if*, by Japanese *-(e)ba*, to which
the paper restricts its attention (fn. 8), or by Mandarin *rúguǒ*. -/
def markerOf (l : Glottocode) : Option Conditional.Marker :=
  List.lookup l [(.english, English.Conditionals.if_), (.japanese, Japanese.Conditionals.eba),
    (.mandarinChinese, Mandarin.Conditionals.ruguo)]

theorem rows_marker_hypothetical :
    ∀ e ∈ Examples.all, ∃ m ∈ markerOf e.language, .hypothetical ∈ m.readings.fst := by
  decide

end Mizuno2024
