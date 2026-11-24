module

public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Semantics.Modality.HistoricalAlternatives
public import Linglib.Discourse.Commitment.Table
public import Linglib.Languages.English.Conditionals
public import Linglib.Languages.Japanese.Conditionals
public import Linglib.Languages.Mandarin.Conditionals
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

The live possibilities at a world and a time are the worlds that agree with it on what is
established by then, the alternatives of a T × W frame, which shrink as time goes on. A domain
makes a conditional contingent when it has an antecedent-world and does not settle the
consequent. X-marking is felicitous when some proper extension of `D` does so and its
presupposition holds; O-marking when `D` does or, where X-marking fails, the live possibilities
of an earlier time do. With the antecedent live, X-marking is felicitous
[only without strong counterfactuality](##Mizuno2024.xFelicitous_iff_of_live), whatever the
consequent, so Anderson and future-less-vivid conditionals stand or fall together;
an O-marked Anderson conditional is felicitous
[only with it](##Mizuno2024.oFelicitous_jones_iff); and an ordinary counterfactual is
[X-marked either way](##Mizuno2024.xFelicitous_game). One parameter per language, whether its
X-marking signals strong counterfactuality, predicts
[the judgment of every row and of its alternatives](##Mizuno2024.rows_felicity).

## Implementation notes

The paper writes a context as a world, a time and the domain of live possibilities at them,
says that these shrink as time develops, and reads the domain as a proxy for the Stalnakerian
context set (footnote 5). It gives the domains no further structure. They are formalized as
`TWFrame.alternatives` of a frame built from dated facts, which adds that the domains partition
the worlds; the frame's equivalence is read as agreement on what is established by a time,
whether or not the matter is historically settled, since which poison Jones took is a past event
that the scenario leaves open. Contingency asks for an antecedent-world in the domain as well
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
open Temporal (TWFrame)

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

variable {W T : Type*} [Preorder T] {D D' A C : Set W} {κ : Counterfactuality}

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

/-- An O-marked conditional quantifies over the live possibilities at its index or, unless
X-marking is felicitous, those of its world at an earlier time. It is felicitous when one of
these domains makes it contingent. -/
def OFelicitous (κ : Counterfactuality) (F : TWFrame W T) (i : Index W T) (A C : Set W) : Prop :=
  Contingent (F.alternatives i) A C ∨
    ¬ XFelicitous κ (F.alternatives i) A C ∧
      ∃ t < i.time, Contingent (F.alternatives ⟨i.world, t⟩) A C

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

theorem oFelicitous_iff_of_not_contingent {F : TWFrame W T} {i : Index W T}
    (h : ¬ Contingent (F.alternatives i) A C) :
    OFelicitous κ F i A C ↔ ¬ XFelicitous κ (F.alternatives i) A C ∧
      ∃ t < i.time, Contingent (F.alternatives ⟨i.world, t⟩) A C :=
  or_iff_right h

theorem not_decidedBy_of_live (h₁ : ¬ D ⊆ A) (h₂ : ¬ Disjoint A D) :
    ¬ (Question.polar A).DecidedBy (Filter.principal D) := by
  rw [Question.decidedBy_polar, Filter.mem_principal, Filter.mem_principal]
  exact not_or.2 ⟨h₁, fun h ↦ h₂ (Set.subset_compl_iff_disjoint_right.1 h).symm⟩

theorem felicitous_iff_of_live {P : Type*} {K : Commitment.Table P W}
    (hK : K.commonGround = Filter.principal D) (h : ∀ a, A ∉ K.discourseCommitments a)
    (h₁ : ¬ D ⊆ A) (h₂ : ¬ Disjoint A D) {ct : Reading} :
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

/-- The frame of the Jones scenario of (1) and (4): that he shows the symptoms is established at
time `1`. -/
def jonesFrame : TWFrame Jones ℤ := .ofDatedFacts (fun _ : Unit ↦ 1) fun w _ ↦ w ∈ symptoms

-- §2
theorem alternatives_jones_one : jonesFrame.alternatives ⟨.arsenic, 1⟩ = symptoms := by
  ext v; simp [jonesFrame, symptoms]

-- §3.3
theorem alternatives_jones_zero : jonesFrame.alternatives ⟨.arsenic, 0⟩ = Set.univ := by
  ext v; simp [jonesFrame]

theorem symptoms_ne_univ : symptoms ≠ Set.univ :=
  fun h ↦ (h ▸ trivial : Jones.unpoisoned ∈ symptoms) rfl

-- (2)
theorem oMarking_trivial (A : Set Jones) :
    (⟨.arsenic, 1⟩ : Index Jones ℤ) ∈ strictImp jonesFrame.alternatives A symptoms :=
  mem_strictImp_of_subset alternatives_jones_one.subset

-- (1b)
theorem arsenic_live : ¬ Disjoint ({.arsenic} : Set Jones) symptoms :=
  Set.not_disjoint_iff.2 ⟨.arsenic, rfl, nofun⟩

-- §2
theorem exists_ssuperset_jones : ∃ D', symptoms ⊂ D' ∧ Contingent D' {.arsenic} symptoms :=
  (exists_ssuperset_contingent symptoms_ne_univ).2 ⟨⟨.arsenic, rfl⟩, symptoms_ne_univ⟩

/-- An X-marked Anderson conditional is felicitous exactly when the X-marking does not signal
strong counterfactuality: English (1a) and not Japanese (4a) with *-ta* (§3.2). -/
theorem xFelicitous_jones_iff :
    XFelicitous κ (jonesFrame.alternatives ⟨.arsenic, 1⟩) {.arsenic} symptoms ↔ κ = .weak := by
  rw [alternatives_jones_one]
  exact xFelicitous_iff_of_live arsenic_live exists_ssuperset_jones

/-- An O-marked Anderson conditional is felicitous iff the X-marking signals strong
counterfactuality, as in Japanese (4a) but not English (2) (§3.3, fn. 14). -/
theorem oFelicitous_jones_iff :
    OFelicitous κ jonesFrame ⟨.arsenic, 1⟩ {.arsenic} symptoms ↔ κ = .strong := by
  rw [oFelicitous_iff_of_not_contingent fun h ↦ h.2 alternatives_jones_one.subset,
    xFelicitous_jones_iff]
  cases κ
  · simp
  · refine iff_of_true ⟨nofun, 0, zero_lt_one, ?_⟩ rfl
    rw [alternatives_jones_zero]
    exact contingent_univ.2 ⟨⟨.arsenic, rfl⟩, symptoms_ne_univ⟩

-- (4a), §3.2
theorem xFelicitous_strong_identified : XFelicitous .strong {Jones.mimic} {.arsenic} symptoms :=
  xFelicitous_of_disjoint (Set.disjoint_singleton.2 nofun)
    ((exists_ssuperset_contingent (D := {Jones.mimic}) fun h ↦
      absurd (h ▸ Set.mem_univ Jones.arsenic) nofun).2
      ⟨⟨.arsenic, rfl⟩, symptoms_ne_univ⟩)

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

/-- The frame of the game scenario of (3): that John has left is established at time `0` and
that the defeat is certain at time `1`. -/
def gameFrame : TWFrame Game ℤ :=
  .ofDatedFacts (fun b : Bool ↦ cond b 1 0) fun w b ↦ cond b (w = .awayLost) (w ≠ .playsOpen)

theorem alternatives_game : gameFrame.alternatives ⟨.awayLost, 1⟩ = {.awayLost} := by
  ext v; cases v <;> simp [gameFrame]

/-- An X-marked counterfactual conditional is felicitous whether or not the X-marking signals
strong counterfactuality, as Japanese (3) with *-ta* is. -/
theorem xFelicitous_game :
    XFelicitous κ (gameFrame.alternatives ⟨.awayLost, 1⟩) {.playsOpen} uncertain := by
  rw [alternatives_game]
  exact xFelicitous_of_disjoint (Set.disjoint_singleton.2 nofun)
    ((exists_ssuperset_contingent (D := {Game.awayLost}) fun h ↦
      absurd (h ▸ Set.mem_univ Game.playsOpen) nofun).2
      ⟨⟨.playsOpen, rfl⟩, fun h ↦ absurd (h ▸ Set.mem_univ Game.awayLost) (by simp [uncertain])⟩)

-- fn. 7
theorem not_oFelicitous_game :
    ¬ OFelicitous κ gameFrame ⟨.awayLost, 1⟩ {.playsOpen} uncertain := by
  rw [oFelicitous_iff_of_not_contingent fun h ↦ by simpa [alternatives_game] using h.1]
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

/-- The proposition that the party takes place. -/
def held : Set Party := {w | w ≠ .cancelled}

/-- The frame of the party scenario of (8) and (9): that the party takes place is established at
time `0`, and that John stays away and the party is dull at time `2`. -/
def partyFrame : TWFrame Party ℤ :=
  .ofDatedFacts (fun b : Bool ↦ cond b 2 0) fun w b ↦ cond b (w = .dull) (w ∈ held)

theorem alternatives_party : partyFrame.alternatives ⟨.dull, 1⟩ = held := by
  ext v; cases v <;> simp [partyFrame, held]

-- (8b)
theorem johnComes_live : ¬ Disjoint ({.johnComes} : Set Party) held :=
  Set.not_disjoint_iff.2 ⟨.johnComes, rfl, nofun⟩

theorem contingent_held : Contingent held {.johnComes} partyFun :=
  ⟨⟨.johnComes, nofun, rfl⟩, fun h ↦ absurd (h (show Party.dull ∈ held from nofun))
    (by simp [partyFun])⟩

theorem exists_ssuperset_party : ∃ D', held ⊂ D' ∧ Contingent D' {.johnComes} partyFun :=
  (exists_ssuperset_contingent (D := held) fun h ↦ (h ▸ trivial : Party.cancelled ∈ held) rfl).2
    ⟨⟨.johnComes, rfl⟩, fun h ↦ absurd (h ▸ Set.mem_univ Party.dull) (by simp [partyFun])⟩

-- (8), (10), (12)
theorem xFelicitous_party_iff :
    XFelicitous κ (partyFrame.alternatives ⟨.dull, 1⟩) {.johnComes} partyFun ↔ κ = .weak := by
  rw [alternatives_party]
  exact xFelicitous_iff_of_live johnComes_live exists_ssuperset_party

-- (9), (11)
theorem oFelicitous_party : OFelicitous κ partyFrame ⟨.dull, 1⟩ {.johnComes} partyFun :=
  .inl (by rw [alternatives_party]; exact contingent_held)

/-! ### The rows -/

/-- The felicity the account predicts for a strategy in a construction, in a language whose
X-marking has counterfactuality `κ`. -/
def Felicitous (κ : Counterfactuality) : Examples.Construction → Examples.Strategy → Prop
  | .anderson, .xMarking =>
    XFelicitous κ (jonesFrame.alternatives ⟨.arsenic, 1⟩) {.arsenic} symptoms
  | .anderson, .oMarking => OFelicitous κ jonesFrame ⟨.arsenic, 1⟩ {.arsenic} symptoms
  | .counterfactual, .xMarking =>
    XFelicitous κ (gameFrame.alternatives ⟨.awayLost, 1⟩) {.playsOpen} uncertain
  | .counterfactual, .oMarking => OFelicitous κ gameFrame ⟨.awayLost, 1⟩ {.playsOpen} uncertain
  | .flv, .xMarking => XFelicitous κ (partyFrame.alternatives ⟨.dull, 1⟩) {.johnComes} partyFun
  | .flv, .oMarking => OFelicitous κ partyFrame ⟨.dull, 1⟩ {.johnComes} partyFun

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
    (hK : K.commonGround = Filter.principal symptoms)
    (h : ∀ a, {.arsenic} ∉ K.discourseCommitments a) {ct : Reading} :
    ct.Felicitous K {.arsenic} ↔ ct = .hypothetical :=
  felicitous_iff_of_live hK h (fun h' ↦ absurd (h' (show Jones.mimic ∈ symptoms from nofun)) nofun)
    arsenic_live

theorem felicitous_party_iff {P : Type*} {K : Commitment.Table P Party}
    (hK : K.commonGround = Filter.principal held)
    (h : ∀ a, {.johnComes} ∉ K.discourseCommitments a) {ct : Reading} :
    ct.Felicitous K {.johnComes} ↔ ct = .hypothetical :=
  felicitous_iff_of_live hK h (fun h' ↦ absurd (h' (show Party.dull ∈ held from nofun)) nofun)
    johnComes_live

/-- The rows of each sampled language are headed by English *if*, by Japanese *-(e)ba*, to which
the paper restricts its attention (fn. 8), or by Mandarin *rúguǒ*. -/
def markerOf (l : Glottocode) : Option Conditional.Marker :=
  List.lookup l [(.english, English.Conditionals.if_), (.japanese, Japanese.Conditionals.eba),
    (.mandarinChinese, Mandarin.Conditionals.ruguo)]

theorem rows_marker_hypothetical :
    ∀ e ∈ Examples.all, ∃ m ∈ markerOf e.language, .hypothetical ∈ m.readings.fst := by
  decide

end Mizuno2024
