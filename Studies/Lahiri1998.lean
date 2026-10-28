module

public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Fragments.HindiUrdu.PolarityItems
public import Linglib.Data.Examples.Lahiri1998

/-!
# Lahiri (1998): Focus and negative polarity in Hindi

This file formalizes the paper's account of the Hindi negative polarity items, each a weak
indefinite plus the focus particle *bhii* 'even' (`HindiUrdu.PolarityItems`). The scalar
presupposition of *even*, that the prejacent is less likely than every focus alternative,
clashes with an entailment-monotone likelihood exactly when an alternative entails the
prejacent (`Focus.Particles.not_evenPresup_of_subset`). The indefinite is the weakest
predicate, so in an upward-entailing context [every alternative entails the assertion and the
presupposition is contradictory](##ue_clash), while [a downward-entailing operator reverses the
entailments and leaves it satisfiable](##de_presup). The restriction of a generic, read as a
universal under the paper's background assumption, is such a slot, as are the
negative-expectation reading of a question and the permission reading of an imperative.
Clausemate negation takes scope over a Hindi subject indefinite, which is why Hindi licenses
subject NPIs where English does not. The judgments of the paper's survey are rows, which [the
analysis predicts](##analysis_matches_judgments) apart from the numeral and measure items *ek
bhii* and *zaraa bhii* in imperatives and with numerals, whose cardinality alternatives the paper
distinguishes from the contextual alternatives of *koii bhii* and *kuch bhii* and whose exclusion
it leaves open. The library's licensing theory [agrees with the rows wherever it names the
environment](##rows_admits) and stars every item in a positive sentence, but for the same
cardinality items and [under a necessity modal, where its free-choice route admits the items the
paper stars](##necessity_admits_starred).

## Implementation notes

A likelihood is a monotone map from propositions into a partial order, and the alternatives
an item introduces are a list of predicates, cardinalities or contextual properties, each at
most as strong as the weakest predicate `⊤`, the paper's `one`. The generic operator is read
as a universal quantifier, which the paper grants on the background assumption that the
exceptions the alternatives tolerate are exceptions the assertion tolerates too; the
permission analysis of imperatives and the two implicature sets of a question are instances of
`de_presup` and `ue_clash` and are not restated. The environments of the survey are
classified as the analysis classifies them, downward entailing, generic, or neither;
necessity modals and the episodic readings of possibility modals and the future are among
the last, which the paper reports without deriving. The oblique forms *kisii-ko*, *kisii-se*,
and *kisiike* are *koii*'s.

The library's licensing contexts realize ten of the survey's environments
(`Environment.context?`): negation, the protasis, the restrictor of a universal, adversatives
(the library's regret-based adversative standing in for *surprise*), *before*, questions, the
generics with and without a numeral, and the possibility and necessity modals and imperatives.
Prohibition verbs, which the paper counts among its adversative predicates, have no library
context, nor do the episodic and the non-licensing environments.

## TODO

* The library licenses every free choice item under a necessity modal, through the consistency of
  its antiexhaustified existential, but the paper stars the *bhii* items there and so does the
  analysis. Which free choice items survive necessity is not a property the library's free-choice
  route consults.

## References

* [lahiri-1998]
* [karttunen-peters-1979]
* [kadmon-landman-1993]
-/

@[expose] public section

namespace Lahiri1998

open Focus.Particles PolarityItem HindiUrdu.PolarityItems

/-! ### The implicature clash (§7, §8) -/

section Model

variable {World Ent α : Type*} [PartialOrder α] {μ : Set World → α}

/-- `exist P φ` is the existential assertion of an indefinite restricted by `P`, true where some
`P`-entity satisfies `φ`. -/
def exist (P : Ent → Prop) (φ : World → Ent → Prop) : Set World := {w | ∃ x, P x ∧ φ w x}

/-- `restrict P φ` is the universal reading of a generic restricted by `P`, true where every
`P`-entity satisfies `φ`. -/
def restrict (P : Ent → Prop) (φ : World → Ent → Prop) : Set World := {w | ∀ x, P x → φ w x}

variable {φ : World → Ent → Prop}

theorem exist_mono : Monotone (exist · φ) := fun _ _ h _ ⟨x, hx, hφ⟩ ↦ ⟨x, h x hx, hφ⟩

theorem restrict_anti : Antitone (restrict · φ) := fun _ _ h _ hr x hx ↦ hr x (h x hx)

theorem exist_subset_exist_top (P : Ent → Prop) : exist P φ ⊆ exist ⊤ φ := exist_mono le_top

theorem restrict_top_subset (P : Ent → Prop) : restrict ⊤ φ ⊆ restrict P φ :=
  restrict_anti le_top

/-- The focus alternatives *bhii* induces from alternative predicates. -/
def alternatives (Ps : Set (Ent → Prop)) (φ : World → Ent → Prop) : Set (Set World) :=
  (exist · φ) '' Ps

variable {Ps : Set (Ent → Prop)}

/-- In an upward-entailing context the scalar presupposition of *bhii* is contradictory, since every
alternative entails the assertion of the weakest indefinite. -/
theorem ue_clash (hμ : Monotone μ) (hPs : Ps.Nonempty) :
    ¬ evenPresup μ (exist ⊤ φ) (alternatives Ps φ) :=
  let ⟨P, hP⟩ := hPs
  not_evenPresup_of_subset hμ ⟨P, hP, rfl⟩ (exist_subset_exist_top P)

/-- Under a downward-entailing operator the scalar presupposition of *bhii* is satisfiable, holding
exactly when no alternative is as likely as the assertion. -/
theorem de_presup (hμ : Monotone μ) {Q : Set World → Set World} (hQ : Antitone Q) :
    evenPresup μ (Q (exist ⊤ φ)) (Q '' alternatives Ps φ) ↔
      ∀ P ∈ Ps, μ (Q (exist ⊤ φ)) ≠ μ (Q (exist P φ)) := by
  rw [evenPresup_iff_ne hμ]
  · simp [alternatives, Set.image_image]
  · simp only [alternatives, Set.image_image, Set.forall_mem_image]
    exact fun P _ ↦ hQ (exist_subset_exist_top P)

theorem clausemate_negation (hμ : Monotone μ) (hPs : Ps.Nonempty) :
    ¬ evenPresup μ (exist ⊤ φ) (alternatives Ps φ) ∧
      (evenPresup μ (exist ⊤ φ)ᶜ (compl '' alternatives Ps φ) ↔
        ∀ P ∈ Ps, μ (exist ⊤ φ)ᶜ ≠ μ (exist P φ)ᶜ) ∧
      ¬ evenPresup μ (exist ⊤ fun w x ↦ ¬ φ w x) (alternatives Ps fun w x ↦ ¬ φ w x) :=
  ⟨ue_clash hμ hPs, de_presup hμ compl_anti, ue_clash hμ hPs⟩

theorem generic_presup (hμ : Monotone μ) :
    evenPresup μ (restrict ⊤ φ) ((restrict · φ) '' Ps) ↔
      ∀ P ∈ Ps, μ (restrict ⊤ φ) ≠ μ (restrict P φ) := by
  rw [evenPresup_iff_ne hμ]
  · simp
  · simp only [Set.forall_mem_image]
    exact fun P _ ↦ restrict_top_subset P

end Model

/-! ### The survey (§4–§6, §8–§10) -/

/-- The environments of the survey. -/
inductive Environment where
  | positive
  | negation
  | protasis
  | apodosis
  | universalRestrictor
  | existentialRestrictor
  | adversative
  | factive
  | settleForLess
  | prohibitionComplement
  | prohibitionObject
  | before
  | after
  | question
  | generic
  | possibilityModal
  | episodicModal
  | genericFuture
  | episodicFuture
  | necessityModal
  | imperative
  | numeralGeneric
  deriving DecidableEq, Repr

/-- The analysis licenses an indefinite plus *bhii* in the downward-entailing environments, in
questions on their negative-expectation reading, and in the generic environments, which are
generics with or without a numeral, generically read possibility modals and futures, and
imperatives read as permissions. -/
def Environment.Licensed : Environment → Prop
  | .negation | .protasis | .universalRestrictor | .adversative | .settleForLess
  | .prohibitionComplement | .before | .question | .generic | .possibilityModal
  | .genericFuture | .imperative | .numeralGeneric => True
  | .positive | .apodosis | .existentialRestrictor | .factive | .prohibitionObject | .after
  | .episodicModal | .episodicFuture | .necessityModal => False

instance : DecidablePred Environment.Licensed
  | .negation | .protasis | .universalRestrictor | .adversative | .settleForLess
  | .prohibitionComplement | .before | .question | .generic | .possibilityModal
  | .genericFuture | .imperative | .numeralGeneric => isTrue trivial
  | .positive | .apodosis | .existentialRestrictor | .factive | .prohibitionObject | .after
  | .episodicModal | .episodicFuture | .necessityModal => isFalse id

/-- An indefinite plus *bhii* introduces other cardinality or measure predicates as its
alternatives for *ek* 'one' and *zaraa* 'a little', and a contextually specified set of
properties for *koii* and *kuch* (§8). -/
inductive Alternatives where
  | cardinality
  | property
  deriving DecidableEq, Repr

/-- A row is a judged example, recording its environment, the fragment entry of its item with
the alternatives it introduces, and the judgment. -/
structure Row where
  env : Environment
  item : PolarityItem
  alternatives : Alternatives
  judgment : Judgment

/-- The fragment entry of a row's item, with its alternatives; the paper does not classify
*kabhii bhii* 'ever', read here with the property alternatives of *koii* and *kuch*. -/
noncomputable def item? (r : Datum) : Option (PolarityItem × Alternatives) :=
  r.parse? "npi" [("koii bhii", (koiiBhii, .property)), ("koi bhii", (koiiBhii, .property)),
    ("kisii-ko bhii", (koiiBhii, .property)), ("kisii-se bhii", (koiiBhii, .property)),
    ("kisiike bhii", (koiiBhii, .property)), ("ek bhii", (ekBhii, .cardinality)),
    ("kuch bhii", (kuchBhii, .property)), ("kuchh bhii", (kuchBhii, .property)),
    ("zaraa bhii", (zaraaBhii, .cardinality)), ("kabhii bhii", (kabhiiBhii, .property))]

/-- A row of the survey. -/
noncomputable def Row.ofDatum (r : Datum) : Option Row :=
  match r.parse? "environment" [("positive (UE)", Environment.positive),
    ("negation", .negation), ("negation (subject NPI)", .negation),
    ("conditional protasis", .protasis), ("conditional apodosis", .apodosis),
    ("universal restrictor", .universalRestrictor),
    ("existential restrictor", .existentialRestrictor), ("adversative", .adversative),
    ("non-adversative factive", .factive), ("settle-for-less glad", .settleForLess),
    ("prohibition verb", .prohibitionComplement),
    ("outside prohibition scope", .prohibitionObject), ("before-clause", .before),
    ("after-clause", .after), ("question", .question), ("generic", .generic),
    ("possibility modal", .possibilityModal), ("episodic possibility modal", .episodicModal),
    ("generic future", .genericFuture), ("episodic future", .episodicFuture),
    ("necessity modal", .necessityModal), ("imperative", .imperative),
    ("generic, with numeral", .numeralGeneric)], item? r with
  | some env, some (item, alternatives) => some ⟨env, item, alternatives, r.judgment⟩
  | _, _ => none

/-- The survey. -/
noncomputable def data : List Row := Examples.all.filterMap Row.ofDatum

/-- Every judgment of the survey is the one the analysis predicts, apart from the cardinality
items in imperatives and generics with a numeral. -/
theorem analysis_matches_judgments :
    ∀ d ∈ data,
      d.alternatives = .property ∨
        (d.env ≠ .imperative ∧ d.env ≠ .numeralGeneric) →
      (d.judgment = .acceptable ↔ d.env.Licensed) := by
  decide +kernel

theorem cardinality_exceptions :
    ∀ d ∈ data, d.alternatives = .cardinality →
      d.env = .imperative ∨ d.env = .numeralGeneric → d.judgment ≠ .acceptable := by
  decide +kernel

/-! ### The licensing theory -/

/-- The licensing context of the library that realizes an environment of the survey, if any. -/
def Environment.context? : Environment → Option LicensingContext
  | .negation => some .negation
  | .protasis => some .conditionalAntecedent
  | .universalRestrictor => some .universalRestrictor
  | .adversative => some .adversative
  | .before => some .beforeClause
  | .question => some .question
  | .generic | .numeralGeneric => some .generic
  | .possibilityModal => some .modalPossibility
  | .necessityModal => some .modalNecessity
  | .imperative => some .imperative
  | .positive | .apodosis | .existentialRestrictor | .factive | .settleForLess
  | .prohibitionComplement | .prohibitionObject | .after | .episodicModal | .genericFuture
  | .episodicFuture => none

/-- Wherever the library names the environment, its licensing theory admits the item exactly when
the paper judges the sentence acceptable, apart from the necessity modals and the cardinality
items in imperatives and generics with a numeral. -/
theorem rows_admits :
    ∀ d ∈ data, ∀ c ∈ d.env.context?, d.env ≠ .necessityModal →
      (d.alternatives = .property ∨ (d.env ≠ .imperative ∧ d.env ≠ .numeralGeneric)) →
      (d.judgment = .acceptable ↔ c.licenser.Admits d.item) := by
  decide +kernel

-- Unembedded, under no licenser, the theory admits no polarity item, and the paper stars every
-- *bhii* item in a positive sentence.
theorem rows_positive :
    ∀ d ∈ data, d.env = .positive →
      (d.judgment = .acceptable ↔ ¬ (d.item.IsNPI ∨ d.item.IsFCI)) := by
  decide +kernel

/-- Under a necessity modal the library's free-choice route admits the *bhii* items, which the
paper stars. -/
theorem necessity_admits_starred :
    ∀ d ∈ data, d.env = .necessityModal →
      LicensingContext.modalNecessity.licenser.Admits d.item ∧ d.judgment ≠ .acceptable := by
  decide +kernel

end Lahiri1998
