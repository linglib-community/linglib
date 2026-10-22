module

public import Linglib.Semantics.Modality.XMarking
public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Discourse.CommonGround
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

A `Scenario` is a common ground that grows over time, with the antecedent and consequent of a
conditional; its context set at the time of utterance is `D`. A strategy is felicitous when it
can quantify over a domain that leaves the consequent open: X-marking over any proper extension
of `D` whose presupposition holds, O-marking over `D` or, where X-marking fails, the context set of
an earlier time. Each strategy's felicity is derived in each construction (`xFelicitous_jones_iff`,
`oFelicitous_jones_iff`, `xFelicitous_party_iff`, `oFelicitous_party`), so the constructions stand
or fall together (`xFelicitous_jones_iff_party`). One parameter per language, whether its
X-marking signals strong counterfactuality, predicts the judgment of every row and of its
alternatives (`rows_felicity`).

## Implementation notes

Footnote 5 reads `D` as a proxy for the Stalnakerian context set, so a scenario's information is
a common ground at each time, the facts established by then asserted in order, and the live
possibilities are its context set. Whether the member of (1) who proposes that Jones *must* have
taken arsenic is thereby committed to the antecedent decides whether the premise reading is
felicitous too; `felicitous_iff_of_open` takes that no participant is committed to it as a
hypothesis. The Mandarin exponent *le* is study-local, resting on the paper's single consultant.

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

open Modality.XMarking (MarkingStrategy XMarkingExponent)
open Conditional (Reading strictImp mem_strictImp_of_subset not_subset_of_mem_strictImp)

/-! ### Scenarios and felicity

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

/-- An X-marking admits an antecedent over the live possibilities when its presupposition holds:
strong counterfactuality presupposes that the antecedent holds at no live possibility. -/
def Counterfactuality.Admits {W : Type*} : Counterfactuality → Set W → Set W → Prop
  | .weak, _, _ => True
  | .strong, A, D => Disjoint A D

/-- A scenario of utterance for a conditional is a common ground that only grows over time, a
time of utterance, and the conditional's antecedent and consequent. -/
structure Scenario (W : Type*) where
  /-- The common ground at each time. -/
  commonGround : ℤ → Filter W
  /-- Information only grows. -/
  antitone_commonGround : Antitone commonGround
  /-- The time of utterance. -/
  time : ℤ
  /-- The antecedent of the conditional. -/
  antecedent : Set W
  /-- The consequent of the conditional. -/
  consequent : Set W

namespace Scenario

variable {W : Type*}

/-- The scenario whose common ground at each time is the trivial one with every fact dated by then
asserted. -/
@[simps time antecedent consequent]
def ofDatedFacts (facts : List (ℤ × Set W)) (time : ℤ) (antecedent consequent : Set W) :
    Scenario W where
  commonGround t := HasCommonGround.commonGround
    (HasAssertion.play (HasAssertion.initial : Filter W) ((facts.filter (·.1 ≤ t)).map (·.2)))
  antitone_commonGround := HasAssertion.antitone_commonGround_play _ fun _ _ h ↦
    List.map_subset _ fun _ hf ↦ by
      simp only [List.mem_filter, decide_eq_true_eq] at hf ⊢
      exact ⟨hf.1, hf.2.trans h⟩
  time := time
  antecedent := antecedent
  consequent := consequent

variable (S : Scenario W) (κ : Counterfactuality)

/-- The live possibilities at a time, the context set of the common ground then. -/
def live (t : ℤ) : Set W := (S.commonGround t).ker

/-- The domain `D` of an O-marked conditional, the live possibilities at the time of
utterance. -/
abbrev domain : Set W := S.live S.time

/-- An X-marked conditional quantifies over a domain properly extending the live possibilities.
It is felicitous when some such domain leaves the consequent open and the X-marking admits the
antecedent. -/
def XFelicitous : Prop :=
  (∃ D, S.domain ⊂ D ∧ ¬ D ⊆ S.consequent) ∧ κ.Admits S.antecedent S.domain

/-- The domains an O-marked conditional can quantify over are the live possibilities at the time
of utterance and, unless X-marking is felicitous, those at an earlier time. -/
def oDomains : Set (Set W) :=
  {D | D = S.domain ∨ ¬ S.XFelicitous κ ∧ ∃ t < S.time, D = S.live t}

/-- An O-marked conditional is felicitous when one of its domains leaves the consequent open. -/
def OFelicitous : Prop := ∃ D ∈ S.oDomains κ, ¬ D ⊆ S.consequent

variable {S κ}

theorem mem_live_ofDatedFacts {facts : List (ℤ × Set W)} {time : ℤ} {A C : Set W} {t : ℤ}
    {v : W} : v ∈ (ofDatedFacts facts time A C).live t ↔ ∀ f ∈ facts, f.1 ≤ t → v ∈ f.2 := by
  simp only [live, ofDatedFacts, HasAssertion.commonGround_play_initial, Filter.ker_principal,
    Set.mem_iInter, List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h f hf ht ↦ h _ ⟨f, ⟨hf, ht⟩, rfl⟩, fun h _ ⟨f, ⟨hf, ht⟩, hp⟩ ↦ hp ▸ h f hf ht⟩

/-- The live possibilities only shrink. -/
theorem antitone_live : Antitone S.live :=
  Filter.ker_mono.comp_antitone S.antitone_commonGround

/-- An antecedent open among the live possibilities is undecided by the common ground. -/
theorem not_decidedBy_of_open (h₁ : ¬ S.domain ⊆ S.antecedent)
    (h₂ : ¬ Disjoint S.antecedent S.domain) :
    ¬ (Question.polar S.antecedent).DecidedBy (S.commonGround S.time) := by
  rw [Question.decidedBy_polar]
  rintro (h | h)
  · exact h₁ (Filter.subset_ker.1 subset_rfl _ h)
  · exact h₂ (Set.subset_compl_iff_disjoint_right.1 (Filter.subset_ker.1 subset_rfl _ h)).symm

/-- In a context leaving the antecedent open, and with no participant committed to it, only the
hypothetical reading is felicitous ([iatridou-1991], [haegeman-2003]). -/
theorem felicitous_iff_of_open {A : Type*} {K : Commitment.Table A W}
    (hK : K.commonGround = S.commonGround S.time) (h : ∀ a, S.antecedent ∉ K.discourseCommitments a)
    (h₁ : ¬ S.domain ⊆ S.antecedent) (h₂ : ¬ Disjoint S.antecedent S.domain) {ct : Reading} :
    ct.Felicitous K S.antecedent ↔ ct = .hypothetical :=
  Reading.felicitous_iff_of_not_decidedBy h (hK ▸ not_decidedBy_of_open h₁ h₂)

/-- Where the antecedent is live and the domain can be expanded so as to leave the consequent
open, X-marking is felicitous exactly when it does not signal strong counterfactuality. -/
theorem xFelicitous_iff (hA : ¬ Disjoint S.antecedent S.domain)
    (hX : ∃ D, S.domain ⊂ D ∧ ¬ D ⊆ S.consequent) : S.XFelicitous κ ↔ κ = .weak := by
  cases κ <;> simp [XFelicitous, Counterfactuality.Admits, hA, hX]

/-- X-marking stands or falls together in any two such scenarios (§4.2). -/
theorem xFelicitous_iff_xFelicitous {W' : Type*} {S' : Scenario W'}
    (hA : ¬ Disjoint S.antecedent S.domain) (hX : ∃ D, S.domain ⊂ D ∧ ¬ D ⊆ S.consequent)
    (hA' : ¬ Disjoint S'.antecedent S'.domain) (hX' : ∃ D, S'.domain ⊂ D ∧ ¬ D ⊆ S'.consequent) :
    S.XFelicitous κ ↔ S'.XFelicitous κ := by
  rw [xFelicitous_iff hA hX, xFelicitous_iff hA' hX']

/-- Where the consequent is open among the live possibilities, O-marking is felicitous. -/
theorem oFelicitous_of_not_subset (h : ¬ S.domain ⊆ S.consequent) : S.OFelicitous κ :=
  ⟨_, .inl rfl, h⟩

/-- Where the consequent is settled among the live possibilities, O-marking is felicitous exactly
when X-marking is not and the consequent was open at an earlier time. -/
theorem oFelicitous_iff_of_subset (h : S.domain ⊆ S.consequent) :
    S.OFelicitous κ ↔ ¬ S.XFelicitous κ ∧ ∃ t < S.time, ¬ S.live t ⊆ S.consequent := by
  constructor
  · rintro ⟨D, hD | ⟨hX, t, ht, rfl⟩, hC⟩
    · exact absurd (hD ▸ h) hC
    · exact ⟨hX, t, ht, hC⟩
  · rintro ⟨hX, t, ht, hC⟩
    exact ⟨_, .inr ⟨hX, t, ht, rfl⟩, hC⟩

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

/-- The proposition that Jones shows the symptoms. -/
def symptoms : Set Jones := {w | w ≠ .unpoisoned}

/-- The Jones scenario of (1) and (4). The antecedent is that Jones took arsenic, and the
consequent that he shows the symptoms. -/
def jones : Scenario Jones := .ofDatedFacts [(1, symptoms)] 1 {.arsenic} symptoms

theorem mem_live_jones {v : Jones} {t : ℤ} : v ∈ jones.live t ↔ (1 ≤ t → v ≠ .unpoisoned) := by
  simp [jones, Scenario.mem_live_ofDatedFacts, symptoms]

/-- Over `D` the consequent is settled, since the symptoms are established (§2). -/
theorem domain_subset_consequent_jones : jones.domain ⊆ jones.consequent :=
  fun _ hv ↦ mem_live_jones.1 hv le_rfl

/-- An O-marked Anderson conditional is true for any antecedent, the triviality behind the
infelicity of (2). -/
theorem oMarking_trivial (A : Set Jones) : jones.time ∈ strictImp jones.live A jones.consequent :=
  mem_strictImp_of_subset domain_subset_consequent_jones

theorem unpoisoned_not_mem_domain : Jones.unpoisoned ∉ jones.domain :=
  fun h ↦ mem_live_jones.1 h le_rfl rfl

/-- X-marking can expand the domain so as to leave the consequent open (§2). -/
theorem exists_ssuperset_jones : ∃ D, jones.domain ⊂ D ∧ ¬ D ⊆ jones.consequent :=
  ⟨Set.univ, Set.ssubset_univ_iff.2 fun h ↦ unpoisoned_not_mem_domain (h ▸ trivial),
    fun h ↦ h (Set.mem_univ Jones.unpoisoned) rfl⟩

/-- The historical-present shift to time `0` strictly expands the domain, since the live
possibilities shrink as facts are established (§3.3). -/
theorem domain_ssubset_live_zero : jones.domain ⊂ jones.live 0 :=
  (Set.ssubset_iff_of_subset (jones.antitone_live zero_le_one)).2
    ⟨.unpoisoned, mem_live_jones.2 (by decide), unpoisoned_not_mem_domain⟩

/-- After the historical-present shift the consequent is open (§3.3). -/
theorem not_live_zero_subset_consequent : ¬ jones.live 0 ⊆ jones.consequent :=
  fun h ↦ h (mem_live_jones.2 (by decide)) rfl

/-- A true Anderson conditional at the shifted time excludes a live possibility, so "one can make
a meaningful, contingent claim" (§2). -/
theorem not_live_zero_subset_of_mem_strictImp {A : Set Jones}
    (h : 0 ∈ strictImp jones.live A jones.consequent) : ¬ jones.live 0 ⊆ A :=
  not_subset_of_mem_strictImp h not_live_zero_subset_consequent

theorem mimic_mem_domain : Jones.mimic ∈ jones.domain := mem_live_jones.2 nofun

/-- That Jones took arsenic is a live possibility, as the follow-up (1b) requires. -/
theorem antecedent_live_jones : ¬ Disjoint jones.antecedent jones.domain :=
  Set.not_disjoint_iff.2 ⟨.arsenic, rfl, mem_live_jones.2 nofun⟩

/-- An X-marked Anderson conditional is felicitous exactly when the X-marking does not signal
strong counterfactuality: English (1a) and not Japanese (4a) with *-ta* (§3.2). -/
theorem xFelicitous_jones_iff {κ : Counterfactuality} : jones.XFelicitous κ ↔ κ = .weak :=
  Scenario.xFelicitous_iff antecedent_live_jones exists_ssuperset_jones

/-- An O-marked Anderson conditional is felicitous exactly when the X-marking signals strong
counterfactuality, which leaves the historical-present shift open: Japanese (4a) and not English
(2) (§3.3, fn. 14). -/
theorem oFelicitous_jones_iff {κ : Counterfactuality} : jones.OFelicitous κ ↔ κ = .strong := by
  rw [Scenario.oFelicitous_iff_of_subset domain_subset_consequent_jones, xFelicitous_jones_iff]
  cases κ
  · simp
  · exact iff_of_true ⟨nofun, 0, zero_lt_one, not_live_zero_subset_consequent⟩ rfl

/-- An Anderson conditional takes exactly one strategy. -/
theorem oFelicitous_jones_iff_not {κ : Counterfactuality} :
    jones.OFelicitous κ ↔ ¬ jones.XFelicitous κ := by
  rw [oFelicitous_jones_iff, xFelicitous_jones_iff]
  cases κ <;> decide

/-- The Jones scenario once it is established that he took the mimic poison. -/
def jonesIdentified : Scenario Jones := .ofDatedFacts [(1, {.mimic})] 1 {.arsenic} symptoms

/-- Once the mimic poison is identified, the arsenic antecedent is no longer live, and a strongly
counterfactual X-marking is felicitous, as §3.2 notes for (4a) with *-ta*. -/
theorem xFelicitous_strong_identified : jonesIdentified.XFelicitous .strong := by
  have hD : jonesIdentified.domain = {.mimic} := by
    ext v; simp [jonesIdentified, Scenario.mem_live_ofDatedFacts]
  refine ⟨⟨Set.univ, ?_, fun h ↦ h (Set.mem_univ Jones.unpoisoned) rfl⟩, ?_⟩
  · rw [hD]; exact Set.ssubset_univ_iff.2 fun h ↦ absurd (h ▸ Set.mem_univ Jones.arsenic) nofun
  · rw [hD]; exact Set.disjoint_singleton.2 nofun

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

/-- The party scenario of (8) and (9), in which John stays away and the party is dull. The
antecedent is that John comes, and the consequent that the party is fun. -/
def party : Scenario Party :=
  .ofDatedFacts [(0, {w | w ≠ .cancelled}), (2, {.dull})] 1 {.johnComes} {.johnComes, .funAnyway}

theorem mem_domain_party {v : Party} : v ∈ party.domain ↔ v ≠ .cancelled := by
  simp [party, Scenario.mem_live_ofDatedFacts]

/-- The consequent is open over `D`, so O-marking is not trivial. -/
theorem not_domain_subset_consequent_party : ¬ party.domain ⊆ party.consequent :=
  fun h ↦ absurd (h ((mem_domain_party (v := .dull)).2 nofun)) (by simp [party])

/-- That John comes is a live possibility, as the follow-up (8b) requires. -/
theorem antecedent_live_party : ¬ Disjoint party.antecedent party.domain :=
  Set.not_disjoint_iff.2 ⟨.johnComes, rfl, mem_domain_party.2 nofun⟩

/-- X-marking can expand the domain to the cancelled party, leaving the consequent open. -/
theorem exists_ssuperset_party : ∃ D, party.domain ⊂ D ∧ ¬ D ⊆ party.consequent :=
  ⟨Set.univ, Set.ssubset_univ_iff.2 fun h ↦ mem_domain_party.1 (h ▸ trivial) rfl,
    fun h ↦ absurd (h (Set.mem_univ Party.dull)) (by simp [party])⟩

/-- An X-marked future-less-vivid conditional is felicitous exactly when the X-marking does not
signal strong counterfactuality: English (8) and not Japanese (10) or Mandarin (12). -/
theorem xFelicitous_party_iff {κ : Counterfactuality} : party.XFelicitous κ ↔ κ = .weak :=
  Scenario.xFelicitous_iff antecedent_live_party exists_ssuperset_party

/-- An O-marked future-less-vivid conditional is felicitous, (9) and (11). -/
theorem oFelicitous_party {κ : Counterfactuality} : party.OFelicitous κ :=
  Scenario.oFelicitous_of_not_subset not_domain_subset_consequent_party

/-- X-marking is available for Anderson conditionals iff it is for future-less-vivid ones: they
"stand or fall together" (§4.2). -/
theorem xFelicitous_jones_iff_party {κ : Counterfactuality} :
    jones.XFelicitous κ ↔ party.XFelicitous κ :=
  Scenario.xFelicitous_iff_xFelicitous antecedent_live_jones exists_ssuperset_jones
    antecedent_live_party exists_ssuperset_party

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

Both scenarios leave the antecedent open, so with no participant committed to it a conditional
is read hypothetically, and the markers heading the rows are attested marking hypothetical
conditionals. -/

/-- Only the hypothetical reading is felicitous for the Anderson antecedent, given that no
participant is committed to it. -/
theorem felicitous_jones_iff {A : Type*} {K : Commitment.Table A Jones}
    (hK : K.commonGround = jones.commonGround jones.time)
    (h : ∀ a, jones.antecedent ∉ K.discourseCommitments a) {ct : Reading} :
    ct.Felicitous K jones.antecedent ↔ ct = .hypothetical :=
  Scenario.felicitous_iff_of_open hK h
    (fun h' ↦ absurd (h' mimic_mem_domain) nofun) antecedent_live_jones

/-- Only the hypothetical reading is felicitous for the future-less-vivid antecedent, given that
no participant is committed to it. -/
theorem felicitous_party_iff {A : Type*} {K : Commitment.Table A Party}
    (hK : K.commonGround = party.commonGround party.time)
    (h : ∀ a, party.antecedent ∉ K.discourseCommitments a) {ct : Reading} :
    ct.Felicitous K party.antecedent ↔ ct = .hypothetical :=
  Scenario.felicitous_iff_of_open hK h
    (fun h' ↦ absurd (h' (mem_domain_party.2 nofun : Party.dull ∈ party.domain)) nofun)
    antecedent_live_party

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
