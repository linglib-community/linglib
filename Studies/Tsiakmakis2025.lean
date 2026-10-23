module

public import Linglib.Semantics.Modality.Necessity
public import Linglib.Fragments.Greek.StandardModern.Negation
public import Linglib.Data.Examples.Tsiakmakis2025

/-!
# Tsiakmakis (2025): On the Non-Homogeneity of Expletive Negation in Greek and Beyond

This file formalizes Tsiakmakis's two kinds of expletive negation. Greek has two
sentential negators in complementary distribution by mood: indicative *dhen*, standard negation,
(7), the complement, and non-veridical *min*, (13), a modal negation, `neg2`, true when the negated
proposition holds throughout the best worlds of an ordering source in Kratzer's sense. Both have
non-negative uses, (20): *dhen* in negative exclamatives, rhetorical questions and preposed negation
questions, *min* in fear complements, conditionals and polar questions. Expletive *dhen* is *dhen*,
(37): its negation is masked by rhetoricity or by the speaker's bias at the level of the utterance.
Expletive *min* keeps the modal component and drops the negation, (58): a biased epistemic modal,
`neg2Expl`. The diagnostics follow from the semantics. Canonical *dhen* under expletive *min* yields
negative *min*, (39), (47), (53), `neg2Expl_compl`, whereas *dhen* under *dhen* cancels; expletive
*min* conveys positive bias, every best world being a p-world, so it excludes the ignorance of a
*min*-free question, in which both alternatives are possible, (55), `not_ignorant_of_mem_neg2Expl`,
and it is consistent with negative *min* only when no world is best,
`bestWorlds_eq_empty_of_mem_neg2Expl_of_mem_neg2`. The survey of section 5 sorts the host
inventory into apparent hosts, featuring NEG₁ under a masking factor, `ApparentHost` and
`ApparentHost.masking`, and hosts proper, featuring NEG₂ as the spell-out of an epistemic or
deontic ordering source, `ProperHost`, the revised inventory (95), `Host`; every Greek host of
expletive negation in the rows features the Greek spell-out of its class's negator, *dhen* in
the apparent hosts and *min* in the hosts proper, (20) (`greek_expletive_negator`).

## Implementation notes

Propositions are sets of worlds, NEG₁ is their complement, (93), and NEG₂ is the substrate's
`Modality.necessity`, the best worlds of a modal base and an ordering source. Greek spells the two
negators with the markers of its fragment (`Negator.greek`). The flavour of the ordering source
varies by host and language, epistemic for Greek *min*, deontic for French fear-predicate *ne*, and
is not fixed here. The NCI-licensing and left-periphery diagnostics, (40) and (44), are syntactic
and recorded by the rows, as are the arguments that negative exclamatives are rhetorical questions,
(23)–(24), that preposed and non-preposed negation questions collapse, (32)–(35), and that
conditionals and free relatives are tentative hosts. The examples are the rows of
`Data.Examples.Tsiakmakis2025`.

## References

* [tsiakmakis-2025]
* [kratzer-1981]
* [giannakidou-1998]
* [romero-han-2004]
* [tovena-1996]
* [tahar-2021]
* [greco-2020]
* [espinal-1992]
-/

@[expose] public section

namespace Tsiakmakis2025

open Modality Negation

variable {W : Type*} (f g : Background W)

/-! ### The two negators (section 2) -/

/-- (13): negative NEG₂, the negative *min*: the negation holds throughout the best worlds. -/
def neg2 (p : Set W) : Set W := {w | necessity f g (· ∈ pᶜ) w}

/-- (58), (94): expletive NEG₂, the expletive *min*: the modal component without the negation,
a modal biased towards the proposition. -/
def neg2Expl (p : Set W) : Set W := {w | necessity f g (· ∈ p) w}

/-- (39), (47), (53): canonical *dhen* under expletive *min* is negative *min*. -/
theorem neg2Expl_compl (p : Set W) : neg2Expl f g pᶜ = neg2 f g p := rfl

theorem neg2_compl (p : Set W) : neg2 f g pᶜ = neg2Expl f g p := by
  simp only [neg2, neg2Expl, compl_compl]

variable {f g}

theorem not_possibility_compl_of_mem_neg2Expl {p : Set W} {w : W} (h : w ∈ neg2Expl f g p) :
    ¬ possibility f g (· ∈ pᶜ) w :=
  (duality f g (· ∈ p) w).1 h

/-- The ignorance of a *min*-free question, (55b): both alternatives hold in some best world. -/
def Ignorant (p : Set W) (w : W) : Prop :=
  possibility f g (· ∈ p) w ∧ possibility f g (· ∈ pᶜ) w

/-- (55): a question with expletive *min* is not the question of an ignorant speaker. -/
theorem not_ignorant_of_mem_neg2Expl {p : Set W} {w : W} (h : w ∈ neg2Expl f g p) :
    ¬ Ignorant (f := f) (g := g) p w :=
  fun hi ↦ not_possibility_compl_of_mem_neg2Expl h hi.2

theorem bestWorlds_eq_empty_of_mem_neg2Expl_of_mem_neg2 {p : Set W} {w : W}
    (h₁ : w ∈ neg2Expl f g p) (h₂ : w ∈ neg2 f g p) : bestWorlds f g w = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun w' hw' ↦ h₂ w' hw' (h₁ w' hw')

/-! ### The revised host inventory (section 5) -/

/-- (95): apparent expletive negation hosts, whose negator is NEG₁ with its negation masked by
a factor at the level of the utterance. -/
inductive ApparentHost where
  | temporalExpression
  | negativeAdverbial
  | comparative
  | optionallyBiasedQuestion
  | rhetoricalQuestion
  | exclamative
  deriving DecidableEq, Repr

/-- The factors masking NEG₁: the lexical aspect that makes the negated and unnegated
*until*-clauses coincide, (69); negative concord with the licensing adverbial, (73); the
negation built into the comparative operator, of which NEG₁ is the spell-out, (78); the
speaker's bias towards the positive answer, (36); and rhetoricity, the polarity reversal that
rhetorical questions and negative exclamatives show without any negator, (29), (87). -/
inductive Masking where
  | lexicalAspect
  | negativeConcord
  | comparativeOperator
  | speakerBias
  | rhetoricity
  deriving DecidableEq, Repr

/-- The masking factor of each apparent host. -/
def ApparentHost.masking : ApparentHost → Masking
  | .temporalExpression => .lexicalAspect
  | .negativeAdverbial => .negativeConcord
  | .comparative => .comparativeOperator
  | .optionallyBiasedQuestion => .speakerBias
  | .rhetoricalQuestion | .exclamative => .rhetoricity

/-- (95): expletive negation hosts proper, whose negator is NEG₂, the spell-out of an ordering
source; conditionals and free relatives are tentative, the former licensing NEG₂ in a positive
antecedent only in Greek, (74), the latter ranking no worlds, (92). -/
inductive ProperHost where
  | emotiveDoxasticPredicate
  | negativePredicate
  | dubitativePredicate
  | biasedQuestion
  | conditional
  | freeRelative
  deriving DecidableEq, Repr

/-- The revised inventory. -/
abbrev Host := ApparentHost ⊕ ProperHost

/-- The two negators. -/
inductive Negator where
  | neg1
  | neg2
  deriving DecidableEq, Repr

/-- The negator a host features, by its class. -/
def Host.negator : Host → Negator := Sum.elim (fun _ ↦ .neg1) (fun _ ↦ .neg2)

/-- Greek spells NEG₁ *dhen* and NEG₂ *min*. -/
def Negator.greek : Negator → Marker
  | .neg1 => Greek.StandardModern.Negation.dhen
  | .neg2 => Greek.StandardModern.Negation.min

/-- The host of expletive negation a row names. -/
def host? (e : Datum) : Option Host :=
  e.parse? "host"
    [("negative exclamative", .inl .exclamative), ("rhetorical question", .inl .rhetoricalQuestion),
      ("preposed negation question", .inl .optionallyBiasedQuestion),
      ("fear-predicate complement", .inr .emotiveDoxasticPredicate),
      ("polar question", .inr .biasedQuestion), ("conditional", .inr .conditional)]

/-- Each Greek host of expletive negation spells out the negator its class assigns, *dhen* or *min*
(20). -/
theorem greek_expletive_negator :
    ∀ e ∈ Examples.all, e.language = "mode1248" → e.feature? "use" = some "expletive" →
      (host? e).map (·.negator.greek.morphs.map (·.form)) = (e.feature? "negator").map ([·]) := by
  decide

end Tsiakmakis2025
