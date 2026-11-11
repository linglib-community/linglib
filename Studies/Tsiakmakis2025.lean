module

public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.PolarityItem.LicensingContext
public import Linglib.Fragments.Greek.StandardModern.Negation
public import Linglib.Fragments.Greek.StandardModern.PolarityItems
public import Linglib.Data.Examples.Tsiakmakis2025
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Tsiakmakis (2025): On the Non-Homogeneity of Expletive Negation in Greek and Beyond

Greek has two sentential negators in complementary distribution: *dhen*, standard negation, and
*min*, a modal negation true when the negated proposition fails throughout the best worlds of an
ordering source. Both have uses in which they seem to negate nothing, and Tsiakmakis argues that
the two differ in kind. Expletive *dhen* is *dhen*, its negation masked at the level of the
utterance. Expletive *min* keeps the modal component and drops the negation, so that [*dhen* under
it gives back negative *min*](##Tsiakmakis2025.Negator.expletive_neg2_compl), it [conveys a bias
for the proposition](##Tsiakmakis2025.Negator.bias_of_expletive_neg2), and, being a
necessity and no negation, it [licenses no emphatic
n-word](##Tsiakmakis2025.Negator.licenses_expletive_tipota_iff). The hosts of expletive negation
across languages divide accordingly into apparent hosts and hosts proper, and [each Greek host
spells out the negator of its class](##Tsiakmakis2025.greek_negators).

## Implementation notes

* The modal component of *min* is necessity along an accessibility relation, and the results need
  only that the relation be serial. The paper's best worlds, those verifying every premise of an
  ordering source, are [the worlds accessible under it as a
  background](##Tsiakmakis2025.Negator.expletive_neg2_accessible_iff), serial when the ordering
  source is consistent; Kratzer's best worlds are the relation `Modality.bestAccessible`. The
  flavour of the modality varies by host and language, epistemic for Greek *min* and deontic for
  French fear-predicate *ne*, and is not fixed.
* The paper says that canonical negative markers license negative concord items and that
  expletive *min* does not. The licensing condition is the library's: an emphatic n-word needs an
  anti-additive licenser, the strength that negation and *xoris* 'without' share, and the
  negators are the licensers of `PolarityItem.LicensingContext`, whose strengths are proved
  there.
* The ignorance of a *min*-free question, whose speaker holds both answers equally probable, is
  rendered as the possibility of both.
* The left-periphery diagnostic and the arguments that negative exclamatives are rhetorical
  questions, that preposed and non-preposed negation questions collapse, and that conditionals
  and free relatives are tentative hosts are syntactic or descriptive, and are recorded by the
  rows of `Data.Examples.Tsiakmakis2025`.

## References

* [tsiakmakis-2025]
* [kratzer-1981]
* [giannakidou-1998]
* [giannakidou-2000]
* [zwarts-1998]
* [romero-han-2004]
* [tovena-1996]
* [tahar-2021]
-/

@[expose] public section

namespace Tsiakmakis2025

open Modality ModalLogic PolarityItem

/-- The two sentential negators, which Greek tells apart morphologically: NEG₁ is standard
negation, and NEG₂ is the modal negation that a nonveridical operator licenses. -/
inductive Negator where
  /-- Standard negation, Greek *dhen*. -/
  | neg1
  /-- Modal negation, Greek *min*. -/
  | neg2
  deriving DecidableEq, Repr

namespace Negator

/-! ### The denotations of the two negators (section 2) -/

section Denotation

variable {W : Type*} (R : SetRel W W) {p : W → Prop} {w : W}

/-- The negative use of a negator. NEG₁ returns the complementary proposition, (7). NEG₂ makes the
complementary proposition necessary, (13). -/
def negative : Negator → (W → Prop) → W → Prop
  | neg1, p => pᶜ
  | neg2, p => □[R] pᶜ

/-- The expletive use of a negator. Expletive NEG₁ is NEG₁, (37). Expletive NEG₂ keeps the modal
component of NEG₂ and drops its negation, (58), (94). -/
def expletive : Negator → (W → Prop) → W → Prop
  | neg1, p => pᶜ
  | neg2, p => □[R] p

/-- Along the worlds verifying every premise of an ordering source, the paper's best worlds,
expletive NEG₂ is its formula (58): the proposition holds at each of them, (12). -/
theorem expletive_neg2_accessible_iff {g : Background W} :
    neg2.expletive g.accessible p w ↔ ∀ v ∈ g.accessibleWorlds w, p v := .rfl

/-! ### Co-occurrence with canonical negation (section 4) -/

/-- Canonical *dhen* under expletive *min* is negative *min*, so that *min dhen* conveys a single
negation, (39), (47), (53). -/
theorem expletive_neg2_compl (p : W → Prop) : neg2.expletive R pᶜ = neg2.negative R p := rfl

theorem negative_neg2_compl (p : W → Prop) : neg2.negative R pᶜ = neg2.expletive R p :=
  congrArg □[R] (compl_compl p)

/-! ### Bias (section 4) -/

variable {R} in
/-- Expletive *min* conveys positive bias: the proposition is possible and its negation is not.
A question with expletive *min* is therefore not the question of an ignorant speaker, for whom
both are possible, (55). -/
theorem bias_of_expletive_neg2 [IsSerial R] (h : neg2.expletive R p w) :
    ◇[R] p w ∧ ¬ ◇[R] pᶜ w :=
  ⟨box_D h, fun ⟨v, hv, hn⟩ ↦ hn (h v hv)⟩

end Denotation

/-! ### Negative concord items (section 4)

Each use of a negator places one of the library's licensers over a polarity item: NEG₁ is clausal
negation, negative NEG₂ is necessity after negation over a serial relation, and expletive NEG₂ is
necessity, `ModalLogic.box_iff_mem_core`. -/

/-- The licensing context of a negator in its negative use. Necessity after negation is the
licenser the library files under verbs of denying. -/
def negativeContext : Negator → LicensingContext
  | neg1 => .negation
  | neg2 => .denyVerb

/-- The licensing context of a negator in its expletive use. -/
def expletiveContext : Negator → LicensingContext
  | neg1 => .negation
  | neg2 => .modalNecessity

theorem negative_neg2_iff_mem_core {W : Type*} {R : SetRel W W} {p : W → Prop} {w : W} :
    neg2.negative R p w ↔ w ∈ R.core {v | p v}ᶜ := .rfl

open Greek.StandardModern.PolarityItems in
/-- Of the two expletive negators only NEG₁ licenses an emphatic n-word: *TIPOTA* is out under
expletive *min*, (40), (46), (52). With canonical *dhen* added the clause denotes negative *min*,
which licenses it as *dhen* does, (41). -/
theorem licenses_expletive_tipota_iff {n : Negator} :
    n.expletiveContext.licenser.Licenses tipota ↔ n = neg1 := by
  cases n <;> decide

open Greek.StandardModern.PolarityItems in
theorem licenses_negative_tipota (n : Negator) : n.negativeContext.licenser.Licenses tipota := by
  cases n <;> decide

/-- NEG₁ is the negator of indicative clauses and NEG₂ that of subjunctive clauses. -/
def ofMood : Clause.ComplementType → Option Negator
  | .indicative => some neg1
  | .subjunctive => some neg2
  | _ => none

end Negator

/-! ### The revised host inventory (section 5) -/

/-- Apparent hosts of expletive negation, (95), whose negator is NEG₁ with its negation masked by
an independent factor. -/
inductive ApparentHost where
  /-- *Before*, *until*: the lexical aspect of an achievement makes the negated and the
  unnegated clause coincide, (69), after [tovena-1996]. -/
  | temporalExpression
  /-- *Without*, *almost*, and *unless*: negative concord with the adverbial, (73), (76). -/
  | negativeAdverbial
  /-- NEG₁ spells out the negation built into the comparative operator, (78). -/
  | comparative
  /-- A negative polar question, preposed or not, whose negation the speaker's bias may mask,
  (36); the question [romero-han-2004] call a preposed negation question. -/
  | optionallyBiasedQuestion
  /-- Rhetoricity reverses polarity, as it does without any negator, (29), (87). -/
  | rhetoricalQuestion
  /-- A negative exclamative is a rhetorical question uttered with surprise, (23)–(25). -/
  | exclamative
  deriving DecidableEq, Repr

/-- Hosts of expletive negation proper, (95), whose negator is expletive NEG₂, the spell-out of an
epistemic or deontic ordering source. -/
inductive ProperHost where
  /-- *Fear*, *hope*, (60); deontic in French, after [tahar-2021]. -/
  | emotiveDoxasticPredicate
  /-- *Forbid*, *prevent*, (63). -/
  | negativePredicate
  /-- *Doubt*, (66). -/
  | dubitativePredicate
  /-- A polar question whose negator itself conveys the bias, Greek *min* and Latin *-ne*,
  (56), (84). -/
  | biasedQuestion
  /-- Tentative: only Greek licenses the negator in a positive antecedent, (74). -/
  | conditional
  /-- Tentative: the alternatives of a Hebrew free relative are not ranked, (92). -/
  | freeRelative
  deriving DecidableEq, Repr

/-- The revised inventory, (95). -/
abbrev Host := ApparentHost ⊕ ProperHost

/-- The negator a host features, by its class. -/
def Host.negator : Host → Negator := Sum.elim (fun _ ↦ .neg1) (fun _ ↦ .neg2)

/-! ### The Greek hosts (section 2) -/

/-- The host of expletive negation a row names. -/
def host? (e : Datum) : Option Host :=
  e.parse? "host"
    [("negative exclamative", .inl .exclamative), ("rhetorical question", .inl .rhetoricalQuestion),
      ("preposed negation question", .inl .optionallyBiasedQuestion),
      ("fear-predicate complement", .inr .emotiveDoxasticPredicate),
      ("polar question", .inr .biasedQuestion), ("conditional", .inr .conditional)]

/-- The negators the account predicts in a Greek row: the negator of the host's class, followed
by canonical *dhen* where the row has one. -/
def predicted? (e : Datum) : Option (List Negator) :=
  if e.language = .modernGreek then do
    let h ← host? e
    let c ← e.parse? "use" [("expletive", []), ("expletive with canonical negation", [.neg1])]
    some (h.negator :: c)
  else none

/-- The negators among the words of a row's sentence, in order: the entries of the Greek fragment,
classed by the mood they negate. -/
def negators (e : Datum) : List Negator :=
  (Datum.wordsOf e.primaryText).filterMap fun w ↦
    (Greek.StandardModern.Negation.negators.find? fun n ↦
      n.marker.morphs.map (·.form.toList) = [w]).bind (Negator.ofMood ·.mood)

/-- Each Greek host of expletive negation spells out the negator of its class, *dhen* in the
apparent hosts and *min* in the hosts proper, (20), and canonical *dhen* follows expletive *min*
where the two co-occur, (39), (53). -/
theorem greek_negators :
    (∀ e ∈ Examples.all, ∀ ns ∈ predicted? e, negators e = ns) ∧
      Datum.ReadCount predicted? Examples.all 10 := by
  decide

end Tsiakmakis2025
