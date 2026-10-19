module

public import Linglib.Semantics.Modality.Exclusion
public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Semantics.Modality.HistoricalAlternatives
public import Linglib.Fragments.English.Conditionals
public import Linglib.Fragments.Japanese.Conditionals
public import Linglib.Fragments.Mandarin.Conditionals
public import Linglib.Data.Examples.Mizuno2024

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

Each construction is a `Scenario` over a T × W frame of dated facts, in which live possibilities
shrink as facts are established. The felicity of each strategy is derived in each scenario
(`xFelicitous_jones_iff`, `oFelicitous_jones_iff`, `xFelicitous_party_iff`, `oFelicitous_party`),
so the constructions stand or fall together (`xFelicitous_jones_iff_party`). One parameter per
language, whether its X-marking signals strong counterfactuality, predicts the judgment of every
row and of its alternatives (`rows_felicity`).

## Implementation notes

The live possibilities at a time are the worlds agreeing with the world of utterance on the facts
established by then; footnote 5 reads `D` as a proxy for the context set. X-marking's domain is
the set of all worlds, where the paper requires only some `D⁺ ⊃ D`. The Mandarin exponent *le* is
study-local, resting on the paper's single consultant.

## References

* [mizuno-2024]
* [anderson-1951]
* [iatridou-1991]
* [schlenker-2004a]
* [von-fintel-iatridou-2023]
* [iatridou-2000]
* [ogihara-2014]
* [mizuno-kaufmann-2019]
* [mackay-2015]
* [mackay-2019]
* [condoravdi-2002]
-/

@[expose] public section

namespace Mizuno2024

open Modality.Exclusion (MarkingStrategy XMarkingExponent)
open Conditional (strictImp mem_strictImp_of_subset not_subset_of_mem_strictImp)
open Temporal (TWFrame)

/-! ### Scenarios and felicity

A conditional is true when the consequent holds at every antecedent-world of its domain (§1). An
O-marked conditional quantifies over the live possibilities at the time of utterance, and is
trivial when the consequent holds throughout them (§2). X-marking expands the domain beyond the
live possibilities (§2, after [mackay-2015] and [mackay-2019]); a strongly counterfactual
X-marking further implies that the antecedent holds at no live possibility (§3.2, §4.2). A
language whose X-marking cannot expand the domain may shift the O-marked domain to an earlier
time, as in the historical present ([schlenker-2004a]; §3.3), a covert option blocked where the
overt one serves (fn. 14). -/

/-- A scenario of utterance for a conditional consists of a T × W frame dating the facts
established in it, the world and time of utterance, and the conditional's antecedent and
consequent. -/
structure Scenario (W : Type*) where
  /-- The frame dating the facts established in the scenario. -/
  frame : TWFrame W ℤ
  /-- The world of utterance. -/
  world : W
  /-- The time of utterance. -/
  time : ℤ
  /-- The antecedent of the conditional. -/
  antecedent : Set W
  /-- The consequent of the conditional. -/
  consequent : Set W

/-- Whether a language's X-marking only expands the domain, allowing the unlikeliness reading of
(8), or signals strong counterfactuality, that the antecedent holds at no live possibility. -/
inductive Counterfactuality
  | weak
  | strong
  deriving DecidableEq, Repr

namespace Scenario

variable {W : Type*} (S : Scenario W) (κ : Counterfactuality)

/-- The live possibilities at a time are the worlds agreeing with the world of utterance on the
facts established by then. -/
def live (t : ℤ) : Set W := S.frame.alternatives (S.world, t)

/-- The domain `D` of an O-marked conditional, the live possibilities at the time of
utterance. -/
abbrev domain : Set W := S.live S.time

/-- An X-marked conditional is felicitous when its domain, every world, leaves the consequent
open and, if the X-marking signals strong counterfactuality, the antecedent holds at no live
possibility. -/
def XFelicitous : Prop :=
  ¬ Set.univ ⊆ S.consequent ∧ (κ = .strong → Disjoint S.antecedent S.domain)

/-- An O-marked conditional is felicitous when the live possibilities leave the consequent open,
at the time of utterance or, where X-marking is not felicitous, at an earlier time. -/
def OFelicitous : Prop :=
  ¬ S.domain ⊆ S.consequent ∨ ¬ S.XFelicitous κ ∧ ∃ t < S.time, ¬ S.live t ⊆ S.consequent

variable {S κ}

/-- Where the antecedent is live and some world fails the consequent, X-marking is felicitous
exactly when it does not signal strong counterfactuality. -/
theorem xFelicitous_iff_of_live (hA : ¬ Disjoint S.antecedent S.domain)
    (hC : ¬ Set.univ ⊆ S.consequent) : S.XFelicitous κ ↔ κ = .weak := by
  cases κ <;> simp [XFelicitous, hA, hC]

/-- X-marking stands or falls together in any two scenarios whose antecedents are live and whose
consequents some world fails (§4.2). -/
theorem xFelicitous_iff_of_live_of_live {W' : Type*} {S' : Scenario W'}
    (hA : ¬ Disjoint S.antecedent S.domain) (hC : ¬ Set.univ ⊆ S.consequent)
    (hA' : ¬ Disjoint S'.antecedent S'.domain) (hC' : ¬ Set.univ ⊆ S'.consequent) :
    S.XFelicitous κ ↔ S'.XFelicitous κ := by
  rw [xFelicitous_iff_of_live hA hC, xFelicitous_iff_of_live hA' hC']

end Scenario

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

/-- The Jones scenario of (1) and (4), uttered where Jones took arsenic. The antecedent is that he
took arsenic, and the consequent that he shows the symptoms. -/
def jones : Scenario Jones where
  frame := .ofDatedFacts (fun _ : Unit ↦ 1) fun w _ ↦ w ≠ .unpoisoned
  world := .arsenic
  time := 1
  antecedent := {.arsenic}
  consequent := {w | w ≠ .unpoisoned}

theorem mem_live_jones {v : Jones} {t : ℤ} : v ∈ jones.live t ↔ (1 ≤ t → v ≠ .unpoisoned) :=
  ⟨fun h ht ↦ (h () ht).1 nofun, fun h _ ht ↦ ⟨fun _ ↦ h ht, fun _ ↦ nofun⟩⟩

/-- Over `D` the consequent is settled, since the symptoms are established (§2). -/
theorem domain_subset_consequent_jones : jones.domain ⊆ jones.consequent :=
  fun _ hv ↦ mem_live_jones.1 hv le_rfl

/-- An O-marked Anderson conditional is true for any antecedent, the triviality behind the
infelicity of (2). -/
theorem oMarking_trivial (A : Set Jones) :
    (jones.world, jones.time) ∈ strictImp jones.frame.alternatives A jones.consequent :=
  mem_strictImp_of_subset domain_subset_consequent_jones

theorem unpoisoned_not_mem_domain : Jones.unpoisoned ∉ jones.domain :=
  fun h ↦ mem_live_jones.1 h le_rfl rfl

/-- X-marking strictly expands the domain, the paper's `D ⊂ D⁺` (§2). -/
theorem domain_ssubset_univ : jones.domain ⊂ Set.univ :=
  Set.ssubset_univ_iff.2 fun h ↦ unpoisoned_not_mem_domain (h ▸ trivial)

/-- The historical-present shift to time `0` strictly expands the domain, since the live
possibilities shrink as facts are established (§3.3). -/
theorem domain_ssubset_live_zero : jones.domain ⊂ jones.live 0 :=
  (Set.ssubset_iff_of_subset (jones.frame.antitone_metaphysicalBase _ zero_le_one)).2
    ⟨.unpoisoned, mem_live_jones.2 (by decide), unpoisoned_not_mem_domain⟩

/-- After the historical-present shift the consequent is open (§3.3). -/
theorem not_live_zero_subset_consequent : ¬ jones.live 0 ⊆ jones.consequent :=
  fun h ↦ h (mem_live_jones.2 (by decide)) rfl

/-- A true Anderson conditional at the shifted index excludes a live possibility, so "one can
make a meaningful, contingent claim" (§2). -/
theorem not_live_zero_subset_of_mem_strictImp {A : Set Jones}
    (h : (jones.world, 0) ∈ strictImp jones.frame.alternatives A jones.consequent) :
    ¬ jones.live 0 ⊆ A :=
  not_subset_of_mem_strictImp h not_live_zero_subset_consequent

/-- That Jones took arsenic is a live possibility, as the follow-up (1b) requires. -/
theorem antecedent_live_jones : ¬ Disjoint jones.antecedent jones.domain :=
  Set.not_disjoint_iff.2 ⟨.arsenic, rfl, mem_live_jones.2 fun _ ↦ by decide⟩

theorem not_univ_subset_consequent_jones : ¬ Set.univ ⊆ jones.consequent :=
  fun h ↦ h (Set.mem_univ Jones.unpoisoned) rfl

/-- An X-marked Anderson conditional is felicitous exactly when the X-marking does not signal
strong counterfactuality: English (1a) and not Japanese (4a) with *-ta* (§3.2). -/
theorem xFelicitous_jones_iff {κ : Counterfactuality} : jones.XFelicitous κ ↔ κ = .weak :=
  Scenario.xFelicitous_iff_of_live antecedent_live_jones not_univ_subset_consequent_jones

/-- An O-marked Anderson conditional is felicitous exactly when the X-marking signals strong
counterfactuality, which leaves the historical-present shift open: Japanese (4a) and not English
(2) (§3.3, fn. 14). -/
theorem oFelicitous_jones_iff {κ : Counterfactuality} : jones.OFelicitous κ ↔ κ = .strong := by
  rw [Scenario.OFelicitous, xFelicitous_jones_iff]
  cases κ
  · simp [domain_subset_consequent_jones]
  · exact iff_of_true (.inr ⟨nofun, 0, zero_lt_one, not_live_zero_subset_consequent⟩) rfl

/-- An Anderson conditional takes exactly one strategy. -/
theorem oFelicitous_jones_iff_not {κ : Counterfactuality} :
    jones.OFelicitous κ ↔ ¬ jones.XFelicitous κ := by
  rw [oFelicitous_jones_iff, xFelicitous_jones_iff]
  cases κ <;> decide

/-- Once the mimic poison is identified, the arsenic antecedent is no longer live, and a strongly
counterfactual X-marking is felicitous, as §3.2 notes for (4a) with *-ta*. -/
theorem xFelicitous_strong_of_identified :
    { jones with frame := .ofDatedFacts (fun _ : Jones ↦ 1) (· = ·), world := .mimic }.XFelicitous
      .strong := by
  refine ⟨not_univ_subset_consequent_jones, fun _ ↦ Set.disjoint_left.2 ?_⟩
  rintro _ rfl h
  exact absurd ((h .mimic le_rfl).1 rfl) (by decide)

/-! ### Future-less-vivid conditionals (§4.2)

The scenario of (8): whether John comes tomorrow, and whether the party is fun, is established at
time `2`, after the time of utterance `1`. -/

/-- In a world of the party scenario, John comes and the party is fun, or he stays away and the
party is fun anyway or dull. -/
inductive Party
  | johnComes
  | funAnyway
  | dull
  deriving DecidableEq, Repr

/-- The party scenario of (8) and (9), uttered where John stays away and the party is dull. The
antecedent is that John comes, and the consequent that the party is fun. -/
def party : Scenario Party where
  frame := .ofDatedFacts (fun _ : Party ↦ 2) (· = ·)
  world := .dull
  time := 1
  antecedent := {.johnComes}
  consequent := {.johnComes, .funAnyway}

/-- Nothing about tomorrow is established at the time of utterance. -/
theorem mem_domain_party (v : Party) : v ∈ party.domain :=
  fun _ (h : (2 : ℤ) ≤ 1) ↦ absurd h (by decide)

/-- The consequent is open over `D`, so O-marking is not trivial. -/
theorem not_domain_subset_consequent_party : ¬ party.domain ⊆ party.consequent :=
  fun h ↦ absurd (h (mem_domain_party .dull)) (by simp [party])

/-- That John comes is a live possibility, as the follow-up (8b) requires. -/
theorem antecedent_live_party : ¬ Disjoint party.antecedent party.domain :=
  Set.not_disjoint_iff.2 ⟨.johnComes, rfl, mem_domain_party _⟩

/-- An X-marked future-less-vivid conditional is felicitous exactly when the X-marking does not
signal strong counterfactuality: English (8) and not Japanese (10) or Mandarin (12). -/
theorem xFelicitous_party_iff {κ : Counterfactuality} : party.XFelicitous κ ↔ κ = .weak :=
  Scenario.xFelicitous_iff_of_live antecedent_live_party
    fun h ↦ absurd (h (Set.mem_univ Party.dull)) (by simp [party])

/-- An O-marked future-less-vivid conditional is felicitous, (9) and (11). -/
theorem oFelicitous_party {κ : Counterfactuality} : party.OFelicitous κ :=
  .inl not_domain_subset_consequent_party

/-- X-marking is available for Anderson conditionals iff it is for future-less-vivid ones: they
"stand or fall together" (§4.2). -/
theorem xFelicitous_jones_iff_party {κ : Counterfactuality} :
    jones.XFelicitous κ ↔ party.XFelicitous κ := by
  rw [xFelicitous_jones_iff, xFelicitous_party_iff]

/-! ### The rows -/

/-- The constructions of the paper's examples. -/
inductive Construction
  | anderson
  | flv
  deriving DecidableEq, Repr

/-- The felicity the account predicts for a strategy in a construction, in a language whose
X-marking has counterfactuality `κ`. -/
def Felicitous (κ : Counterfactuality) : Construction → MarkingStrategy → Prop
  | .anderson, .xMarking => jones.XFelicitous κ
  | .anderson, .oMarking => jones.OFelicitous κ
  | .flv, .xMarking => party.XFelicitous κ
  | .flv, .oMarking => party.OFelicitous κ

instance (κ : Counterfactuality) : ∀ c m, Decidable (Felicitous κ c m)
  | .anderson, .xMarking => decidable_of_iff _ xFelicitous_jones_iff.symm
  | .anderson, .oMarking => decidable_of_iff _ oFelicitous_jones_iff.symm
  | .flv, .xMarking => decidable_of_iff _ xFelicitous_party_iff.symm
  | .flv, .oMarking => isTrue oFelicitous_party

/-- English X-marking allows the unlikeliness reading of (8), while Japanese *-ta*
([ogihara-2014], [mizuno-kaufmann-2019]) and Mandarin *le* (§4.2) signal strong
counterfactuality. -/
def counterfactuality : Glottocode → Option Counterfactuality
  | "stan1293" => some .weak
  | "nucl1643" => some .strong
  | "mand1415" => some .strong
  | _ => none

/-- The row's construction. -/
def constructionOf (e : Datum) : Option Construction :=
  e.parse? "construction" [("anderson", .anderson), ("flv", .flv)]

/-- The strategy of the row's primary text; its alternatives realize the other. -/
def strategyOf (e : Datum) : Option MarkingStrategy :=
  e.parse? "strategy" [("x-marking", .xMarking), ("o-marking", .oMarking)]

/-- Every Anderson and future-less-vivid row names its strategy and a sampled language. -/
theorem rows_parsed : ∀ e ∈ Examples.all, (constructionOf e).isSome →
    (strategyOf e).isSome ∧ (counterfactuality e.language).isSome := by
  decide

/-- Every row is judged as predicted, its primary text under its strategy and its alternatives
under the other: English (1a), (2) and (8), Japanese (4a), (7a) and (9), and Mandarin (11) and
(13a). -/
theorem rows_felicity :
    ∀ e ∈ Examples.all, ∀ c ∈ constructionOf e, ∀ m ∈ strategyOf e,
      ∀ κ ∈ counterfactuality e.language,
        (e.JudgedFelicitous ↔ Felicitous κ c m) ∧
          ∀ a ∈ e.alternatives, (a.2 = .acceptable ↔ Felicitous κ c m.other) := by
  decide

/-! ### The inventory (§3.1)

Every sampled language has X-marking, so the inventory alone predicts X-marked Anderson
conditionals throughout, which Japanese and Mandarin reject. -/

/-- The X-marking exponents of English and Japanese are the fragments', and that of Mandarin is
*le*, study-local since it rests on one consultant (fn. 15). -/
def xExponent : Glottocode → Option XMarkingExponent
  | "stan1293" => English.Conditionals.xMarking
  | "nucl1643" => Japanese.Conditionals.xMarking
  | "mand1415" => some ⟨"le", [.perfective]⟩
  | _ => none

/-- Every sampled language has an X-marking exponent, the Japanese one the fake past of (3). -/
theorem xExponent_isSome : (∀ e ∈ Examples.all, (xExponent e.language).isSome) ∧
    ∃ e ∈ Examples.all, e.JudgedFelicitous ∧
      e.feature? "x_exponent" = Japanese.Conditionals.xMarking.map (·.form) := by
  decide

/-! ### The conditional markers

Both scenarios leave the antecedent open, neither established nor excluded by the live
possibilities, the discourse condition of a hypothetical conditional ([iatridou-1991]), and the
markers heading the rows are attested in hypothetical conditionals. -/

theorem antecedent_open :
    (¬ Disjoint jones.antecedent jones.domain ∧ ¬ jones.domain ⊆ jones.antecedent) ∧
      ¬ Disjoint party.antecedent party.domain ∧ ¬ party.domain ⊆ party.antecedent :=
  ⟨⟨antecedent_live_jones, fun h ↦ absurd (h (mem_live_jones.2 fun _ ↦ by decide :
      Jones.mimic ∈ jones.domain)) (by simp [jones])⟩,
    antecedent_live_party, fun h ↦ absurd (h (mem_domain_party .dull)) (by simp [party])⟩

/-- The rows of each sampled language are headed by English *if*, by Japanese *-(e)ba*, to which
the paper restricts its attention (fn. 8), or by Mandarin *rúguǒ*. -/
def markerOf : Glottocode → Option Conditional.Marker
  | "stan1293" => some English.Conditionals.if_
  | "nucl1643" => some Japanese.Conditionals.eba
  | "mand1415" => some Mandarin.Conditionals.ruguo
  | _ => none

/-- Every row's marker is attested marking hypothetical conditionals. -/
theorem rows_marker_hypothetical :
    ∀ e ∈ Examples.all, ∀ m ∈ markerOf e.language, .hypothetical ∈ m.readings.fst := by
  decide

end Mizuno2024
