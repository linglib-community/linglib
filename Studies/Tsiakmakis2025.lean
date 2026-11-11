module

public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.PolarityItem.Licenser
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
for the proposition](##Tsiakmakis2025.Negator.bias_of_mem_expletive_neg2), and, being upward
entailing, it [licenses no emphatic
n-word](##Tsiakmakis2025.Negator.licenses_expletive_tipota_iff). The hosts of expletive negation
across languages divide accordingly into apparent hosts and hosts proper, and [each Greek host
spells out the negator of its class](##Tsiakmakis2025.greek_negators).

## Implementation notes

* The paper evaluates *min* at the worlds verifying every premise of an ordering source, a
  simplification of Kratzer's best worlds that leaves out the modal base. The negators are stated
  here over human necessity with a modal base, of which the paper's formula is [the instance with
  an empty modal base and a consistent ordering
  source](##Tsiakmakis2025.Negator.mem_expletive_neg2_bot_iff). The flavour of the ordering source
  varies by host and language, epistemic for Greek *min* and deontic for French fear-predicate
  *ne*, and is not fixed.
* The paper says that canonical negative markers license negative concord items and that
  expletive *min* does not. The licensing condition is the library's: an emphatic n-word needs an
  anti-additive licenser, the strength that negation and *xoris* 'without' share.
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

open Modality Filter PolarityItem NaturalLogic

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

variable {W : Type*} (f g : Background W) {p : Set W} {w : W}

/-- The negative use of a negator. NEG₁ returns the complementary proposition, (7). NEG₂ makes the
complementary proposition a necessity of the ordering source, (13). -/
def negative : Negator → Set W → Set W
  | neg1, p => pᶜ
  | neg2, p => {w | pᶜ ∈ humanNecessity f g w}

/-- The expletive use of a negator. Expletive NEG₁ is NEG₁, (37). Expletive NEG₂ keeps the modal
component of NEG₂ and drops its negation, (58), (94). -/
def expletive : Negator → Set W → Set W
  | neg1, p => pᶜ
  | neg2, p => {w | p ∈ humanNecessity f g w}

@[simp] theorem mem_negative_neg2 : w ∈ neg2.negative f g p ↔ pᶜ ∈ humanNecessity f g w := .rfl

@[simp] theorem mem_expletive_neg2 : w ∈ neg2.expletive f g p ↔ p ∈ humanNecessity f g w := .rfl

variable {g} in
/-- With no modal base and a consistent ordering source, expletive NEG₂ is truth at the worlds
verifying every premise of the ordering source, the paper's best worlds, (12). -/
theorem mem_expletive_neg2_bot_iff (h : (g.accessibleWorlds w).Nonempty) :
    w ∈ neg2.expletive ⊥ g p ↔ g.accessibleWorlds w ⊆ p := by
  rw [mem_expletive_neg2, humanNecessity_eq_simpleNecessity_sup (by rwa [bot_sup_eq]), bot_sup_eq,
    mem_simpleNecessity]

/-! ### Co-occurrence with canonical negation (section 4) -/

/-- Canonical *dhen* under expletive *min* is negative *min*, so that *min dhen* conveys a single
negation, (39), (47), (53). -/
theorem expletive_neg2_compl (p : Set W) : neg2.expletive f g pᶜ = neg2.negative f g p := rfl

theorem negative_neg2_compl (p : Set W) : neg2.negative f g pᶜ = neg2.expletive f g p :=
  Set.ext fun _ ↦ by rw [mem_negative_neg2, compl_compl, mem_expletive_neg2]

/-! ### Entailment properties -/

theorem isAntiAdditive_negative : ∀ n : Negator, IsAntiAdditive (n.negative f g)
  | neg1 => isAntiAdditive_compl
  | neg2 => fun p q ↦ Set.ext fun w ↦ by
    simp only [mem_negative_neg2, Set.sup_eq_union, Set.inf_eq_inter, Set.compl_union,
      inter_mem_iff, Set.mem_inter_iff]

theorem negative_empty : ∀ n : Negator, n.negative f g ∅ = Set.univ
  | neg1 => Set.compl_empty
  | neg2 => Set.eq_univ_of_forall fun w ↦ by rw [mem_negative_neg2, Set.compl_empty]; exact univ_mem

theorem monotone_expletive_neg2 : Monotone (neg2.expletive f g) :=
  fun _ _ h _ hw ↦ (mem_expletive_neg2 f g).2 (mem_of_superset ((mem_expletive_neg2 f g).1 hw) h)

variable {f}

private theorem humanNecessity_neBot (h : (f.accessibleWorlds w).Nonempty) :
    (humanNecessity f g w).NeBot :=
  letI := premisePreorder (g w); atBotOn_neBot_iff.2 h

theorem negative_univ (hf : f.IsConsistent) : ∀ n : Negator, n.negative f g Set.univ = ∅
  | neg1 => Set.compl_univ
  | neg2 => Set.eq_empty_of_forall_notMem fun w hw ↦
    (humanNecessity_neBot g (hf w)).ne <| empty_mem_iff_bot.1 <| by
      rwa [mem_negative_neg2, Set.compl_univ] at hw

theorem disjoint_expletive_negative_neg2 (hf : f.IsConsistent) (p : Set W) :
    Disjoint (neg2.expletive f g p) (neg2.negative f g p) :=
  Set.disjoint_left.2 fun w h ↦
    haveI := humanNecessity_neBot g (hf w); compl_notMem ((mem_expletive_neg2 f g).1 h)

/-! ### Bias (section 4) -/

theorem mem_expletive_neg2_iff_not_humanPossibility_compl :
    w ∈ neg2.expletive f g p ↔ ¬ humanPossibility f g w pᶜ := by
  rw [humanPossibility_iff_compl_notMem, compl_compl, not_not, mem_expletive_neg2]

/-- Expletive *min* conveys positive bias: the proposition is possible and its negation is not.
A question with expletive *min* is therefore not the question of an ignorant speaker, for whom
both are possible, (55). -/
theorem bias_of_mem_expletive_neg2 (hf : (f.accessibleWorlds w).Nonempty)
    (h : w ∈ neg2.expletive f g p) :
    humanPossibility f g w p ∧ ¬ humanPossibility f g w pᶜ :=
  ⟨haveI := humanNecessity_neBot g hf; Eventually.frequently h,
    (mem_expletive_neg2_iff_not_humanPossibility_compl g).1 h⟩

end Denotation

/-! ### Negative concord items (section 4) -/

section Licensing

open Greek.StandardModern.PolarityItems

variable {W : Type} [Nonempty W] {f : Background W} (g : Background W)

theorem carries_negative (hf : f.IsConsistent) (n : Negator) :
    (Licenser.ofOperator (n.negative f g)).Carries .antiAdditive :=
  Licenser.carries_ofOperator_iff.2
    ⟨ProjectivitySignature.holdsFor_antiAdd_iff.2
        ⟨isAntiAdditive_negative f g n, negative_univ g hf n⟩,
      fun hm ↦ Set.empty_ne_univ <| (negative_univ g hf n).symm.trans <| Set.univ_subset_iff.1 <|
        (negative_empty f g n).symm.trans_subset (hm (Set.empty_subset _))⟩

omit [Nonempty W] in
theorem not_carries_expletive_neg2 (s : Negation.Strength) :
    ¬ (Licenser.ofOperator (neg2.expletive f g)).Carries s :=
  fun h ↦ (Licenser.carries_ofOperator_iff.1 h).2 (monotone_expletive_neg2 f g)

/-- Of the two expletive negators only NEG₁ licenses an emphatic n-word: *TIPOTA* is out under
expletive *min*, (40), (46), (52). With canonical *dhen* added the clause denotes negative *min*,
which licenses it, (41). -/
theorem licenses_expletive_tipota_iff (hf : f.IsConsistent) {n : Negator} :
    (Licenser.ofOperator (n.expletive f g)).Licenses tipota ↔ n = neg1 := by
  rw [Licenser.licenses_iff_carries (r := .antiAdditive) rfl (by decide) (by decide)]
  cases n
  · exact iff_of_true (carries_negative g hf neg1) rfl
  · exact iff_of_false (not_carries_expletive_neg2 g _) (by decide)

theorem licenses_negative_tipota (hf : f.IsConsistent) (n : Negator) :
    (Licenser.ofOperator (n.negative f g)).Licenses tipota :=
  (Licenser.licenses_iff_carries rfl (by decide) (by decide)).2 (carries_negative g hf n)

end Licensing

open Greek.StandardModern.Negation in
/-- Greek spells NEG₁ *dhen* and NEG₂ *min*. -/
def greek : Negator → Negation.Marker
  | neg1 => dhen
  | neg2 => min

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

/-- The negators of Greek among the words of a row's sentence, in order. -/
def negators (e : Datum) : List Negator :=
  (Datum.wordsOf e.primaryText).filterMap fun w ↦
    [Negator.neg1, .neg2].find? fun n ↦ n.greek.morphs.map (·.form.toList) = [w]

/-- Each Greek host of expletive negation spells out the negator of its class, *dhen* in the
apparent hosts and *min* in the hosts proper, (20), and canonical *dhen* follows expletive *min*
where the two co-occur, (39), (53). -/
theorem greek_negators :
    (∀ e ∈ Examples.all, ∀ ns ∈ predicted? e, negators e = ns) ∧
      Datum.ReadCount predicted? Examples.all 10 := by
  decide

end Tsiakmakis2025
