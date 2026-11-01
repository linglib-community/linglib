module

public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Haspelmath2021
public import Linglib.Data.Corpus.Haspelmath2021
public import Linglib.Discourse.Givenness
public import Linglib.Semantics.Reference.Definiteness
public import Linglib.Semantics.Focus.Marking
public import Linglib.Semantics.Reference.Animacy
public import Linglib.Semantics.Reference.Nominality
public import Studies.BejarRezac2009
public import Linglib.Syntax.Clause.ArgumentRole
public import Linglib.Syntax.Clause.Scenario
public import Linglib.Syntax.Person.Basic
public import Linglib.Syntax.Person.Class
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Haspelmath (2021): Role-reference associations and the explanation of argument coding splits

This file formalizes Haspelmath's role-reference association universal, that a less usual
association of role rank and referential prominence is coded no shorter, as
`RoleReferenceUniversal` over any usualness relation. Its instances are the single-argument
universal, whose role instances are the split flagging universals; the scenario universal on
`Clause.Scenario`, whose instances are the ditransitive person-role and the relative scenario
universals; the inverse universal; and the alternation universal. Each split the paper cites is a
coding function on a prominence scale, checked against the universals and the paper's examples,
and [the anti-efficient language violates them](##Haspelmath2021.antiEfficient_violates). [On the
corpus counts the paper cites, the form-frequency correspondence universal yields the
single-argument universal](##Haspelmath2021.singleArgumentUniversal_of_frequencies), the
explanation the paper argues for.

## Implementation notes

* The scales are the binary versions of the paper's scales, the two-element bounded orders
  (`IsSimpleOrder`). On them the scenario universal says exactly that [coding is antitone in the
  order of `Clause.Scenario`](##Haspelmath2021.scenarioUniversal_iff_antitone), which the paper
  assumes tacitly for monadic splits. The binary scales are load-bearing: on a scale with three
  levels [a monadic split obeys the scenario universal only if it is
  constant](##Haspelmath2021.ScenarioUniversal.comp_high_le), since a balanced scenario of two low
  values is coded no longer than an upstream one and no shorter than a downstream one, so Kolyma
  Yukaghir's rule and [Greek's on the ternary person scale violate
  it](##Haspelmath2021.greekT_ternary_violates). Ternary scales appear only where a rule refers to
  them: the person hierarchy for Kashmiri, animacy for Sardinian, Spanish, Fore and Awtuw, and the
  nominal types for Baule.
* The universal's restriction to asymmetric coding is dropped: with coding lengths as the coding, a
  symmetric split has equal lengths and satisfies it vacuously, as Samoan's ergative flags of equal
  length do. Its "tends to" is read as exceptionless, an idealization the paper itself qualifies.
  The single-argument universal's restriction to flagging is not encoded, since the paper applies
  "longer coding" to the Georgian reinforced pronoun and the Makassarese applicative itself, and
  the index-based person-role constraint is omitted.
* `BinaryGivenness` is the scale of discourse-given over discourse-new, which the paper also calls
  topicality, so Persian's topical indefinite P counts as given.
* Coding length is an `ℕ` count of special coding elements. The universals are stated over any
  preorder, and the alternation universal is the scenario universal read with the usage rate of
  the longer alternant as the coding. The single-argument universal is stated over any partial
  order, so that [Makassarese's rule, on the definiteness and the nominality of T together, is a
  monotone coding on the product of the two scales](##Haspelmath2021.makassar_universal8).
* In the paper's taxonomy the inverse universal is an instance of the role-reference universal
  beside the scenario universal; here [it follows from the scenario universal read on verb
  coding](##Haspelmath2021.inverseUniversal_of_scenarioUniversal).
* The usual associations are a claim about frequencies in use, which the paper glosses across
  roles at a fixed value (more definite As than definite Ps), while the reduction to form-frequency
  correspondence needs it within a role across values (a definite P rarer than an indefinite P).
  The Appendix's counts bear out [the reading within
  roles](##Haspelmath2021.usualIsFrequent_frequencies) and [the reading across
  roles](##Haspelmath2021.frequencies_higherRanked) in every table; its tables are one table of the
  data, keyed by corpus and scale.
* The example rows carry the coding an example shows (`codingShown`), so a strict split reproduces
  a row when the coding shown is acceptable exactly when it is the coding the split requires, and
  a splitting alternation when the construction shown is available in the row's scenario.

## TODO

* `lummiPassive`'s availability whenever A is a full nominal is inferred from (64c) and (65b); the
  paper states only that the passive is obligatory in upstream scenarios and optional in `N > N`.
  UNVERIFIED against the source grammar.

## References

* [haspelmath-2021]
* [haspelmath-2021b]
* [bejar-rezac-2009]
-/

@[expose] public section

namespace Haspelmath2021

open Discourse
open Focus (Mark)
open OrderDual (toDual)

/-! ### Referential prominence scales (8)

Each scale is a linear order whose greater element is the more prominent. The person scale
of (8a), locuphoric above aliophoric, is `Person.Class`; the definiteness scale of (8b)
without its optional specific-indefinite level is `Definiteness`, with Eastern
Khanty's specific P (37) read at the definite end; the givenness scale is `BinaryGivenness`;
and the focus scale of (8b), background above focus, is the dual of focus marking,
`Focus.Markᵒᵈ`, its more prominent end the unfocused one. -/

/-- The nominality scale of (8a) ranks person forms, independent or index, above full nominals;
the ternary scale of (49a) is `Nominality`. -/
inductive BinaryNominality where
  | fullNominal
  | personForm
  deriving DecidableEq, Fintype, Repr

/-- Rank on the nominality scale. -/
def BinaryNominality.rank : BinaryNominality → ℕ
  | .fullNominal => 0
  | .personForm => 1

instance : LinearOrder BinaryNominality := LinearOrder.lift' BinaryNominality.rank (by decide)

/-- `⊥ = fullNominal`, `⊤ = personForm`. -/
instance : BoundedOrder BinaryNominality where
  top := .personForm
  le_top := by decide
  bot := .fullNominal
  bot_le := by decide

instance : IsSimpleOrder BinaryNominality where
  exists_pair_ne := ⟨.fullNominal, .personForm, by decide⟩
  eq_bot_or_eq_top := by decide

/-- The animacy scale of (8a) without its optional animal level, the ternary `Animacy` cut at the
animates. -/
inductive BinaryAnimacy where
  | inanimate
  | animate
  deriving DecidableEq, Fintype, Repr

/-- Rank on the binary animacy scale. -/
def BinaryAnimacy.rank : BinaryAnimacy → ℕ
  | .inanimate => 0
  | .animate => 1

instance : LinearOrder BinaryAnimacy := LinearOrder.lift' BinaryAnimacy.rank (by decide)

/-- `⊥ = inanimate`, `⊤ = animate`. -/
instance : BoundedOrder BinaryAnimacy where
  top := .animate
  le_top := by decide
  bot := .inanimate
  bot_le := by decide

instance : IsSimpleOrder BinaryAnimacy where
  exists_pair_ne := ⟨.inanimate, .animate, by decide⟩
  eq_bot_or_eq_top := by decide

/-- The cut of the ternary scale at the animates. -/
def BinaryAnimacy.ofAnimacy (a : Animacy) : BinaryAnimacy :=
  if .animate ≤ a then .animate else .inanimate

theorem BinaryAnimacy.ofAnimacy_monotone : Monotone BinaryAnimacy.ofAnimacy := by
  intro a b; revert a b; decide

/-! ### Cutoff splits

A coding split codes the values of a scale on one side of a cutoff specially, the coding length
`1` there and `0` elsewhere. -/

section Cutoff

variable {α : Type*} [LinearOrder α]

/-- The split that codes the values from `x` up specially is `1` at and above the cutoff and
`0` below it. -/
def atLeast (x y : α) : ℕ := if x ≤ y then 1 else 0

/-- The split that codes the values below `x` specially is `1` below the cutoff and `0` at and
above it. -/
def below (x y : α) : ℕ := if y < x then 1 else 0

theorem atLeast_monotone (x : α) : Monotone (atLeast x) := fun _ _ h ↦ by
  unfold atLeast
  split_ifs with h₁ h₂ <;> first | rfl | omega | exact absurd (h₁.trans h) h₂

theorem below_antitone (x : α) : Antitone (below x) := fun _ _ h ↦ by
  unfold below
  split_ifs with h₁ h₂ <;> first | rfl | omega | exact absurd (h.trans_lt h₁) h₂

end Cutoff

/-! ### Scenarios (10), (11) -/

open Clause (Scenario)

/-- `s` is a more usual scenario than `t` under the tendencies (11). -/
def Scenario.MoreUsual {α : Type*} [LinearOrder α] (s t : Scenario α) : Prop :=
  t.kind < s.kind

section Splits

variable {α L : Type*} [LinearOrder α]

/-- A scenario split is monadic (fn. 18) when only the prominence `coargument s` of the coargument
decides the coding; a dyadic split is one that is monadic in neither argument. -/
abbrev Monadic (coargument : Scenario α → α) (c : Scenario α → L) : Prop :=
  c.FactorsThrough coargument

instance (coargument : Scenario α → α) (c : Scenario α → L)
    [i : Decidable (∀ s t, coargument s = coargument t → c s = c t)] :
    Decidable (Monadic coargument c) := i

/-- A scenario split is relative (§8) when the relation between the prominence levels of the two
arguments determines the coding. On a binary scale this admits the dyadic splits of Yurok's type,
which fn. 20 allows are "just like" Kashmiri's. -/
abbrev Relative (c : Scenario α → L) : Prop :=
  c.FactorsThrough Scenario.kind

instance (c : Scenario α → L) [i : Decidable (∀ s t, s.kind = t.kind → c s = c t)] :
    Decidable (Relative c) := i

theorem relative_comp_kind (g : Scenario.Kind → L) :
    Relative (g ∘ Scenario.kind : Scenario α → L) :=
  fun _ _ h ↦ congrArg g h

end Splits

/-! ### Universal 1 and its instances -/

section Universals

variable {S L F : Type*} [Preorder L] [Preorder F]

/-- Universal 1 (5) says that a situation more usual under `r` is never coded longer by `c`. -/
def RoleReferenceUniversal (r : S → S → Prop) (c : S → L) : Prop :=
  ∀ ⦃s t⦄, r s t → c s ≤ c t

instance (r : S → S → Prop) (c : S → L) [i : Decidable (∀ s t, r s t → c s ≤ c t)] :
    Decidable (RoleReferenceUniversal r c) := i

theorem RoleReferenceUniversal.mono {r r' : S → S → Prop} {c : S → L} (hr : r ≤ r')
    (h : RoleReferenceUniversal r' c) : RoleReferenceUniversal r c :=
  fun _ _ hst ↦ h (hr _ _ hst)

/-- The grammatical form-frequency correspondence universal (68) says that a pattern more frequent
under `freq` is never coded longer by `c`. -/
def FormFrequencyCorrespondence (freq : S → F) (c : S → L) : Prop :=
  ∀ ⦃s t⦄, freq t < freq s → c s ≤ c t

/-- Universal 2 (6) says that the association more usual under `r` is the more frequent one in
language use. -/
def UsualIsFrequent (r : S → S → Prop) (freq : S → F) : Prop :=
  ∀ ⦃s t⦄, r s t → freq t < freq s

instance (r : S → S → Prop) (freq : S → F) [i : Decidable (∀ s t, r s t → freq t < freq s)] :
    Decidable (UsualIsFrequent r freq) := i

/-- Universal 1 follows from Universal 2 and the form-frequency correspondence universal (68), which
is Universal 1 for the relation of being more frequent (§11.2). -/
theorem roleReferenceUniversal_of_formFrequency {r : S → S → Prop} {freq : S → F}
    {c : S → L} (hu : UsualIsFrequent r freq) (h : FormFrequencyCorrespondence freq c) :
    RoleReferenceUniversal r c :=
  RoleReferenceUniversal.mono hu h

section SingleArgument

variable {α : Type*} [PartialOrder α]

/-- Universal 3 (13), the single-argument flagging universal, is Universal 1 for the usual
associations `ArgumentRole.MoreUsualFor` of the role `r` in (9), which are vacuous for S. -/
def SingleArgumentUniversal (r : ArgumentRole) (c : α → L) : Prop :=
  RoleReferenceUniversal r.MoreUsualFor c

instance (r : ArgumentRole) (c : α → L)
    [i : Decidable (∀ x y, r.MoreUsualFor x y → c x ≤ c y)] :
    Decidable (SingleArgumentUniversal r c) := i

-- (21), (26)
theorem singleArgumentUniversal_iff_antitone {r : ArgumentRole} (h : r.IsHigherRanked)
    {c : α → L} : SingleArgumentUniversal r c ↔ Antitone c :=
  ⟨fun H ↦ antitone_iff_forall_lt.2 fun _ _ hab ↦ H (.inl ⟨h, hab⟩),
    fun H _ _ hst ↦ hst.elim (fun h ↦ H h.2.le) fun h' ↦ (h.not_isLowerRanked h'.1).elim⟩

-- (14), (27)
theorem singleArgumentUniversal_iff_monotone {r : ArgumentRole} (h : r.IsLowerRanked)
    {c : α → L} : SingleArgumentUniversal r c ↔ Monotone c :=
  ⟨fun H ↦ monotone_iff_forall_lt.2 fun _ _ hab ↦ H (.inr ⟨h, hab⟩),
    fun H _ _ hst ↦ hst.elim (fun h' ↦ (h.not_isHigherRanked h'.1).elim) fun h ↦ H h.2.le⟩

end SingleArgument

variable {α : Type*} [LinearOrder α]

/-- Universal 5 (16), the scenario universal, says that coding is longest for upstream, shortest for
downstream and intermediate for balanced scenarios. Universal 10 (54) is its restriction to
`Relative` splits, with the same prediction. -/
def ScenarioUniversal (c : Scenario α → L) : Prop :=
  RoleReferenceUniversal Scenario.MoreUsual c

instance (c : Scenario α → L) [i : Decidable (∀ s t, t.kind < s.kind → c s ≤ c t)] :
    Decidable (ScenarioUniversal c) := i

theorem ScenarioUniversal.downstream_le {c : Scenario α → L} (h : ScenarioUniversal c)
    {s t : Scenario α} (hs : s.kind = .downstream) (ht : t.kind ≠ .downstream) :
    c s ≤ c t :=
  h (show t.kind < s.kind by rw [hs]; exact lt_top_iff_ne_top.2 ht)

theorem scenarioUniversal_iff_antitone [BoundedOrder α] [IsSimpleOrder α]
    {c : Scenario α → L} : ScenarioUniversal c ↔ Antitone c :=
  ⟨fun h ↦ antitone_iff_forall_lt.2 fun _ _ hst ↦ h (Scenario.kind_lt_kind_iff.2 hst),
    fun h _ _ hst ↦ h (Scenario.kind_lt_kind_iff.1 hst).le⟩

theorem scenarioUniversal_comp_high [BoundedOrder α] [IsSimpleOrder α] {f : α → L}
    (hf : Antitone f) : ScenarioUniversal (f ∘ Scenario.high) :=
  scenarioUniversal_iff_antitone.2 (hf.comp_monotone Scenario.high_mono)

theorem ScenarioUniversal.comp_high_le {f : α → L} (h : ScenarioUniversal (f ∘ Scenario.high))
    {a b c : α} (hab : a < b) (hbc : b < c) (x y : α) : f x ≤ f y :=
  (h (s := ⟨x, x⟩) (t := ⟨b, c⟩) (show Scenario.kind _ < Scenario.kind _ by
    rw [Scenario.kind_eq_upstream_iff.2 hbc, Scenario.kind_eq_balanced_iff.2 rfl]; decide)).trans
    (h (s := ⟨b, a⟩) (t := ⟨y, y⟩) (show Scenario.kind _ < Scenario.kind _ by
      rw [Scenario.kind_eq_balanced_iff.2 rfl, Scenario.kind_eq_downstream_iff.2 hab]; decide))

theorem ScenarioUniversal.comp_low_le {g : α → L} (h : ScenarioUniversal (g ∘ Scenario.low))
    {a b c : α} (hab : a < b) (hbc : b < c) (x y : α) : g x ≤ g y :=
  (h (s := ⟨x, x⟩) (t := ⟨a, b⟩) (show Scenario.kind _ < Scenario.kind _ by
    rw [Scenario.kind_eq_upstream_iff.2 hab, Scenario.kind_eq_balanced_iff.2 rfl]; decide)).trans
    (h (s := ⟨c, b⟩) (t := ⟨y, y⟩) (show Scenario.kind _ < Scenario.kind _ by
      rw [Scenario.kind_eq_balanced_iff.2 rfl, Scenario.kind_eq_downstream_iff.2 hbc]; decide))

theorem scenarioUniversal_comp_low [BoundedOrder α] [IsSimpleOrder α] {g : α → L}
    (hg : Monotone g) : ScenarioUniversal (g ∘ Scenario.low) :=
  scenarioUniversal_iff_antitone.2 (hg.comp_antitone Scenario.low_anti)

/-- Universal 9b (42), the ditransitive person-role universal, says that the scenario with a
locuphoric R and an aliophoric T is coded no longer than any other. -/
def PersonRoleUniversal (c : Scenario Person.Class → L) : Prop :=
  ∀ s, c ⟨.participant, .nonParticipant⟩ ≤ c s

-- §7.1
theorem personRoleUniversal_of_scenarioUniversal {c : Scenario Person.Class → L}
    (h : ScenarioUniversal c) : PersonRoleUniversal c :=
  fun _ ↦ scenarioUniversal_iff_antitone.1 h le_top

/-- Universal 11 (57), the inverse universal, says that under the verb coding `v` the inverse form
of an upstream scenario is no shorter than the direct form of a downstream one. -/
def InverseUniversal (v : Scenario α → L) : Prop :=
  ∀ ⦃s t⦄, s.kind = .downstream → t.kind = .upstream → v s ≤ v t

theorem inverseUniversal_of_scenarioUniversal {v : Scenario α → L} (h : ScenarioUniversal v) :
    InverseUniversal v :=
  fun _ _ hs ht ↦ h (show _ < _ by rw [hs, ht]; exact bot_lt_top)

/-- Universals 13 (62) and 14 (63) say that across the givenness scenarios of A and P, or of R and
T, the usage rate `rate` of the longer alternant, the passive or the dative, is lowest when the
higher-ranked argument is given and the lower-ranked one new. -/
def GivennessAlternationUniversal (rate : Scenario BinaryGivenness → F) : Prop :=
  ∀ s, rate ⟨.given, .new⟩ ≤ rate s

-- (61), §10.1
theorem givennessAlternationUniversal_of_scenarioUniversal
    {rate : Scenario BinaryGivenness → F} (h : ScenarioUniversal rate) :
    GivennessAlternationUniversal rate :=
  fun _ ↦ scenarioUniversal_iff_antitone.1 h le_top

/-- A shorter and a longer construction form a splitting alternation (§10.2) when they alternate in
some scenarios and are in complementary distribution in others. -/
def SplittingAlternation (short long : Scenario α → Prop) : Prop :=
  (∃ s, short s ∧ long s) ∧ ∃ s, Xor (short s) (long s)

instance (short long : Scenario α → Prop)
    [i : Decidable ((∃ s, short s ∧ long s) ∧ ∃ s, Xor (short s) (long s))] :
    Decidable (SplittingAlternation short long) := i

/-- The shortest coding available in a scenario is `0` where the shorter construction is available
and `1` otherwise. -/
def minimalCoding (short : Scenario α → Prop) [DecidablePred short] (s : Scenario α) : ℕ :=
  if short s then 0 else 1

/-! #### Cutoff splits

The cited splits are cutoffs on a scale (`atLeast x`, `below x`); a scenario split is a
cutoff on one argument's prominence or on the kind. -/

theorem singleArgumentUniversal_atLeast {r : ArgumentRole} (h : r.IsLowerRanked) (x : α) :
    SingleArgumentUniversal r (atLeast x) :=
  (singleArgumentUniversal_iff_monotone h).2 (atLeast_monotone x)

theorem singleArgumentUniversal_below {r : ArgumentRole} (h : r.IsHigherRanked) (x : α) :
    SingleArgumentUniversal r (below x) :=
  (singleArgumentUniversal_iff_antitone h).2 (below_antitone x)

theorem scenarioUniversal_comp_kind {g : Scenario.Kind → L} (hg : Antitone g) :
    ScenarioUniversal (g ∘ Scenario.kind : Scenario α → L) :=
  fun _ _ hst ↦ hg hst.le

end Universals

/-! ### Universal 2 in the Appendix

Each table of the Appendix counts how often the arguments of a role take the more and the less
prominent value of a binary scale, read here as `Bool` with `true` the more prominent. -/

/-- The argument role of the arguments a row of the Appendix counts. -/
def Role.toArgumentRole : Role → ArgumentRole
  | .a => .A
  | .p => .P
  | .r => .R
  | .t => .T

/-- The frequencies of a row of the Appendix on the two values of its scale. -/
def Frequency.freq (f : Frequency) : Bool → ℕ
  | true => f.prominent
  | false => f.nonProminent

-- Appendix
theorem usualIsFrequent_frequencies :
    ∀ f ∈ frequencies, UsualIsFrequent f.role.toArgumentRole.MoreUsualFor f.freq := by
  decide

-- (6), Appendix
theorem frequencies_higherRanked :
    ∀ f ∈ frequencies, ∀ g ∈ frequencies, f.corpus = g.corpus → f.scale = g.scale →
      f.role.toArgumentRole.IsHigherRanked → g.role.toArgumentRole.IsLowerRanked →
      g.prominent < f.prominent ∧ f.nonProminent < g.nonProminent := by
  decide

/-- On the frequencies of each table of the Appendix, the form-frequency correspondence universal
(68) yields Universal 3 for the table's role, as §11.2 argues: the reduction's premise about usage
holds of every corpus the paper cites. -/
theorem singleArgumentUniversal_of_frequencies {f : Frequency} (hf : f ∈ frequencies)
    {c : Bool → ℕ} (h : FormFrequencyCorrespondence f.freq c) :
    SingleArgumentUniversal f.role.toArgumentRole c :=
  roleReferenceUniversal_of_formFrequency (usualIsFrequent_frequencies f hf) h

/-! ### Single-argument splits (§4, §5) -/

/-- Sakha flags a definite P with the accusative, as in (2); Punjabi's `nũũ` (18) is alike. -/
def sakhaP : Definiteness → ℕ := atLeast .definite

/-- Nuorese Sardinian flags a human P with `a`, as in (17). -/
def sardinianP : Animacy → ℕ := atLeast .human

/-- Persian flags a topical P with `-râ`, as in (19). -/
def persianP : BinaryGivenness → ℕ := atLeast .given

/-- Abruzzese flags a locuphoric P with `a`, as in (20). -/
def abruzzeseP : Person.Class → ℕ := atLeast .participant

/-- English distinguishes P from A only on person forms (*he* ~ *him*, §4.1.3), a split in indexes
rather than flags, which fn. 12 allows may have a different explanation. -/
def englishP : BinaryNominality → ℕ := atLeast .personForm

/-- Godoberi has an ergative form only for aliophoric A, as in (22); Kham (1) is alike. -/
def godoberiA : Person.Class → ℕ := below .participant

/-- Warrgamay flags a full-nominal A with the ergative, as in (23). -/
def warrgamayA : BinaryNominality → ℕ := below .personForm

/-- Mangarrayi flags an inanimate (neuter) A with the ergative, as in (24). -/
def mangarrayiA : BinaryAnimacy → ℕ := below .animate

theorem mangarrayiA_comp_ofAnimacy :
    mangarrayiA ∘ BinaryAnimacy.ofAnimacy = below (.animate : Animacy) := by
  funext a; cases a <;> rfl

/-- Central Tibetan flags a focused A with the ergative `-ki'`, as in (25). -/
def tibetanA : Markᵒᵈ → ℕ := below (toDual .unfeatured)

/-- French dative clitics are longer than accusative ones only for aliophoric R, as in (28) (`lui` ~
`le`, `leur` ~ `les`); they are person indexes, so fn. 17 keeps the case outside split flagging
proper. -/
def frenchR : Person.Class → ℕ := below .participant

/-- Telkepe Neo-Aramaic flags a full-nominal R with `ta`, as in (29). -/
def neoAramaicR : BinaryNominality → ℕ := below .personForm

/-- Yakkha puts an inanimate R in the locative, as in (30). -/
def yakkhaR : BinaryAnimacy → ℕ := below .animate

/-- Wolof flags an indefinite R with `ci`, as in (31). -/
def wolofR : Definiteness → ℕ := below .definite

/-- Ewe flags a person-form T with the serial verb `tsɔ́`, as in (32). -/
def eweT : BinaryNominality → ℕ := atLeast .personForm

/-- Akan flags a definite T with the serial verb `de`, as in (33). -/
def akanT : Definiteness → ℕ := atLeast .definite

/-- Georgian requires the reinforced form (`šeni tavi`) for a locuphoric T, as in (34). -/
def georgianT : Person.Class → ℕ := atLeast .participant

-- §4.1
theorem universal4_splitP :
    SingleArgumentUniversal .P sakhaP ∧ SingleArgumentUniversal .P sardinianP ∧
      SingleArgumentUniversal .P persianP ∧ SingleArgumentUniversal .P abruzzeseP ∧
      SingleArgumentUniversal .P englishP :=
  ⟨singleArgumentUniversal_atLeast (by decide) _, singleArgumentUniversal_atLeast (by decide) _,
    singleArgumentUniversal_atLeast (by decide) _, singleArgumentUniversal_atLeast (by decide) _,
    singleArgumentUniversal_atLeast (by decide) _⟩

-- §4.2
theorem universal6_splitA :
    SingleArgumentUniversal .A godoberiA ∧ SingleArgumentUniversal .A warrgamayA ∧
      SingleArgumentUniversal .A mangarrayiA ∧ SingleArgumentUniversal .A tibetanA :=
  ⟨singleArgumentUniversal_below (by decide) _, singleArgumentUniversal_below (by decide) _,
    singleArgumentUniversal_below (by decide) _, singleArgumentUniversal_below (by decide) _⟩

-- §5.1
theorem universal7_splitR :
    SingleArgumentUniversal .R frenchR ∧ SingleArgumentUniversal .R neoAramaicR ∧
      SingleArgumentUniversal .R yakkhaR ∧ SingleArgumentUniversal .R wolofR :=
  ⟨singleArgumentUniversal_below (by decide) _, singleArgumentUniversal_below (by decide) _,
    singleArgumentUniversal_below (by decide) _, singleArgumentUniversal_below (by decide) _⟩

-- §5.2
theorem universal8_splitT :
    SingleArgumentUniversal .T eweT ∧ SingleArgumentUniversal .T akanT ∧
      SingleArgumentUniversal .T georgianT :=
  ⟨singleArgumentUniversal_atLeast (by decide) _, singleArgumentUniversal_atLeast (by decide) _,
    singleArgumentUniversal_atLeast (by decide) _⟩

/-! ### Scenario splits (§6, §7) -/

/-- Kolyma Yukaghir flags P with the accusative when A is aliophoric, as in (35); Teop's object
marker `ben-` (3) is alike. -/
def yukaghirP : Scenario Person.Class → ℕ := below .participant ∘ Scenario.high

/-- Yurok flags P with the accusative when A is aliophoric and P locuphoric (§6.1). -/
def yurokP (s : Scenario Person.Class) : ℕ :=
  if s.high = .nonParticipant ∧ s.low = .participant then 1 else 0

/-- Sahaptin flags A with the ergative when P is locuphoric, as in (36). -/
def sahaptinA : Scenario Person.Class → ℕ := atLeast .participant ∘ Scenario.low

/-- Eastern Khanty flags A with the ergative when P is specific, as in (37). -/
def khantyA : Scenario Definiteness → ℕ := atLeast .definite ∘ Scenario.low

/-- Spanish flags P with `a` when the construction is not animacy-downstream, as in (38), which
subsumes the human P of §4.1.1. -/
def spanishP : Scenario Animacy → ℕ := below .downstream ∘ Scenario.kind

/-- Bulgarian flags R with `na` when T is a locuphoric clitic, as in (39). -/
def bulgarianR : Scenario Person.Class → ℕ := atLeast .participant ∘ Scenario.low

/-- Shambala flags R with `kwa` when T is locuphoric, as in (40). -/
def shambalaR : Scenario Person.Class → ℕ := atLeast .participant ∘ Scenario.low

/-- English requires `to` on R in the N > pers scenario, as in (4). -/
def englishR (s : Scenario BinaryNominality) : ℕ := if s = ⟨.fullNominal, .personForm⟩ then 1 else 0

/-- The American varieties of English require `to` on R whenever T is a person form, as in (44). -/
def americanEnglishR : Scenario BinaryNominality → ℕ := atLeast .personForm ∘ Scenario.low

/-- Modern Greek has the T proclitic in downstream and aliophoric balanced scenarios and the
independent pronoun otherwise, so whenever T is locuphoric, as in (45). -/
def greekT : Scenario Person.Class → ℕ := atLeast .participant ∘ Scenario.low

/-- Icelandic flags R with `fyrir` when T is animate, as in (46). -/
def icelandicR : Scenario BinaryAnimacy → ℕ := atLeast .animate ∘ Scenario.low

-- §6, fn. 18
theorem universal5_monotransitive :
    ScenarioUniversal yukaghirP ∧ ScenarioUniversal yurokP ∧
      ScenarioUniversal sahaptinA ∧ ScenarioUniversal khantyA ∧ ScenarioUniversal spanishP :=
  ⟨scenarioUniversal_comp_high (below_antitone _), by decide,
    scenarioUniversal_comp_low (atLeast_monotone _),
    scenarioUniversal_comp_low (atLeast_monotone _),
    scenarioUniversal_comp_kind (below_antitone _)⟩

-- §7
theorem universal5_ditransitive :
    ScenarioUniversal bulgarianR ∧ ScenarioUniversal shambalaR ∧ ScenarioUniversal englishR ∧
      ScenarioUniversal americanEnglishR ∧ ScenarioUniversal greekT ∧
      ScenarioUniversal icelandicR :=
  ⟨scenarioUniversal_comp_low (atLeast_monotone _),
    scenarioUniversal_comp_low (atLeast_monotone _), by decide,
    scenarioUniversal_comp_low (atLeast_monotone _),
    scenarioUniversal_comp_low (atLeast_monotone _),
    scenarioUniversal_comp_low (atLeast_monotone _)⟩

-- (39)
theorem universal9b_bulgarian : PersonRoleUniversal bulgarianR :=
  personRoleUniversal_of_scenarioUniversal (scenarioUniversal_comp_low (atLeast_monotone _))

-- fn. 18
theorem yukaghir_monadic_yurok_dyadic :
    Monadic Scenario.high yukaghirP ∧
      ¬ Monadic Scenario.high yurokP ∧ ¬ Monadic Scenario.low yurokP :=
  ⟨fun _ _ h ↦ congrArg (below _) h, by decide, by decide⟩

theorem yukaghirP_greekT_ternary_antitone :
    Antitone (below (Person.prominence .second) ∘ Scenario.high) ∧
      Antitone (atLeast (Person.prominence .second) ∘ Scenario.low) :=
  ⟨(below_antitone _).comp_monotone Scenario.high_mono,
    (atLeast_monotone _).comp_antitone Scenario.low_anti⟩

theorem yukaghirP_ternary_violates :
    ¬ ScenarioUniversal (below (Person.prominence .second) ∘ Scenario.high) :=
  fun h ↦ absurd
    (h.comp_high_le (by decide : Person.prominence .third < Person.prominence .second)
      (by decide : Person.prominence .second < Person.prominence .first)
      (Person.prominence .third) (Person.prominence .first)) (by decide)

/-- Modern Greek's rule on the ternary person scale (47a) violates Universal 5. -/
theorem greekT_ternary_violates :
    ¬ ScenarioUniversal (atLeast (Person.prominence .second) ∘ Scenario.low) :=
  fun h ↦ absurd
    (h.comp_low_le (by decide : Person.prominence .third < Person.prominence .second)
      (by decide : Person.prominence .second < Person.prominence .first)
      (Person.prominence .first) (Person.prominence .third)) (by decide)

/-! ### Relative scenario splits (§8) -/

/-- Kashmiri puts P in the dative unless A outranks P on the person hierarchy, as in (47). -/
def kashmiriP : Scenario (WithBot Person.Feature) → ℕ := below .downstream ∘ Scenario.kind

/-- Fore flags A with the ergative only when P outranks A in animacy (§8). -/
def foreA : Scenario Animacy → ℕ := below .balanced ∘ Scenario.kind

/-- Awtuw flags P with the accusative only when P is not lower than A in animacy (§8). -/
def awtuwP : Scenario Animacy → ℕ := below .downstream ∘ Scenario.kind

/-- Baule flags T with the serial verb `fà` unless R outranks T on the scale of (49a), as in
(49). -/
def bauleT : Scenario Nominality → ℕ := below .downstream ∘ Scenario.kind

/-- The person features up to a prominence, one for each step of the hierarchy. -/
private def featuresUpTo (r : WithBot Person.Feature) : ℕ :=
  (Finset.univ.filter fun f : Person.Feature ↦ (f : WithBot Person.Feature) ≤ r).card

theorem kashmiri_rank (p : Person) : BejarRezac2009.kashmiri.rank p = p.toFeatures.card + 1 := by
  cases p <;> decide

private theorem kashmiri_rank_eq :
    BejarRezac2009.kashmiri.rank = (featuresUpTo · + 1) ∘ Person.prominence := by
  funext p; cases p <;> decide

open Minimalist.CyclicAgree in
-- (47), Table 11 [bejar-rezac-2009]
theorem kashmiriP_iff_isInverse (s : Scenario Person) :
    kashmiriP (s.map Person.prominence) = 1 ↔ BejarRezac2009.kashmiri.IsInverse s := by
  have hm : StrictMono (featuresUpTo · + 1) := by decide
  have hs : s.map ((featuresUpTo · + 1) ∘ Person.prominence) =
      (s.map Person.prominence).map (featuresUpTo · + 1) := rfl
  rw [AgreementSystem.IsInverse, AgreementSystem.isDirect_iff_kind_eq_downstream _ _
    PersonGeometry.standard_isChain, kashmiri_rank_eq, hs, Scenario.kind_map hm]
  simp only [kashmiriP, Function.comp_apply]
  generalize (s.map Person.prominence).kind = k
  revert k; decide

-- §8
theorem universal10_relative :
    (Relative kashmiriP ∧ ScenarioUniversal kashmiriP) ∧
      (Relative foreA ∧ ScenarioUniversal foreA) ∧
      (Relative awtuwP ∧ ScenarioUniversal awtuwP) ∧
      (Relative bauleT ∧ ScenarioUniversal bauleT) :=
  ⟨⟨relative_comp_kind _, scenarioUniversal_comp_kind (below_antitone _)⟩,
    ⟨relative_comp_kind _, scenarioUniversal_comp_kind (below_antitone _)⟩,
    ⟨relative_comp_kind _, scenarioUniversal_comp_kind (below_antitone _)⟩,
    ⟨relative_comp_kind _, scenarioUniversal_comp_kind (below_antitone _)⟩⟩

-- §8
theorem yukaghir_not_relative : ¬ Relative yukaghirP := by decide

/-! ### Verbal voice coding (§9) -/

/-- Itonama's inverse prefix `k'i-` appears in upstream scenarios, as in (55). -/
def itonamaV : Scenario Person.Class → ℕ := below .balanced ∘ Scenario.kind

-- (55)
theorem universal11_itonama : InverseUniversal itonamaV :=
  inverseUniversal_of_scenarioUniversal (scenarioUniversal_comp_kind (below_antitone _))

/-- Makassarese requires the applicative `-ang` on the verb when T is a definite nominal or a
person form, as in (56), a rule on the definiteness and the nominality of T together. -/
def makassarV (x : Definiteness × BinaryNominality) : ℕ :=
  max (atLeast .definite x.1) (atLeast .personForm x.2)

-- §9
theorem makassar_universal8 : SingleArgumentUniversal .T makassarV :=
  (singleArgumentUniversal_iff_monotone (by decide)).2
    (((atLeast_monotone _).comp monotone_fst).max ((atLeast_monotone _).comp monotone_snd))

/-! ### Splitting alternations (§10.2) -/

/-- Lummi's active construction is available unless the scenario is upstream, as (64) and (65)
show. -/
def lummiActive (s : Scenario BinaryNominality) : Prop := s.kind ≠ .upstream

instance : DecidablePred lummiActive := fun s ↦ inferInstanceAs (Decidable (s.kind ≠ _))

/-- Lummi's passive construction of (64) and (65) is available when A is a full nominal, the common
condition of the obligatory (64c) and optional (65b) passives. -/
def lummiPassive (s : Scenario BinaryNominality) : Prop := s.high = .fullNominal

instance : DecidablePred lummiPassive := fun s ↦ inferInstanceAs (Decidable (s.high = _))

/-- Koyra Chiini's double object construction is available only in downstream scenarios, as (66) and
(67) show; the postpositional dative construction is always available. -/
def koyraChiiniDoubleObject (s : Scenario BinaryNominality) : Prop := s.kind = .downstream

instance : DecidablePred koyraChiiniDoubleObject :=
  fun s ↦ inferInstanceAs (Decidable (s.kind = _))

/-- The English double object construction is available except in the N > pers scenario, as (4) and
(60) show; the prepositional dative construction is always available. -/
def englishDoubleObject (s : Scenario BinaryNominality) : Prop := s ≠ ⟨.fullNominal, .personForm⟩

instance : DecidablePred englishDoubleObject := fun s ↦ inferInstanceAs (Decidable (s ≠ _))

-- §10.2
theorem splittingAlternations_universal5 :
    (SplittingAlternation lummiActive lummiPassive ∧
        ScenarioUniversal (minimalCoding lummiActive)) ∧
      (SplittingAlternation koyraChiiniDoubleObject (fun _ ↦ True) ∧
        ScenarioUniversal (minimalCoding koyraChiiniDoubleObject)) ∧
      (SplittingAlternation englishDoubleObject (fun _ ↦ True) ∧
        ScenarioUniversal (minimalCoding englishDoubleObject)) := by
  decide

/-! ### The anti-efficient language (§11.3)

The hypothetical language flags the usual associations and leaves the rare ones bare, so it
has less potential ambiguity than the attested mirror image; its non-existence is the paper's
argument that efficient coding, not ambiguity avoidance, explains the splits. -/

/-- The hypothetical language of §11.3 puts the ergative on every topical A and zero coding on a
focused A. -/
def antiEfficientA : Markᵒᵈ → ℕ := atLeast (toDual .unfeatured)

/-- The hypothetical language of §11.3 puts the accusative on every indefinite P and zero coding on
a definite P. -/
def antiEfficientP : Definiteness → ℕ := below .definite

-- §11.3
theorem antiEfficient_violates :
    ¬ SingleArgumentUniversal .A antiEfficientA ∧
      ¬ SingleArgumentUniversal .P antiEfficientP := by
  decide

/-! ### The paper's examples

Each cited system is checked against the rows of its language: every row reads to a
prominence value or scenario on the system's scale, and the coding the row shows is
acceptable exactly when it is the coding the system requires, or, for a splitting
alternation, when the construction shown is available in the row's scenario. -/

section Examples

variable {α : Type*}

/-- The coding an example shows is `0` for zero coding and `1` for the special coding. -/
def codingShown (e : Datum) : Option ℕ :=
  e.parse? "coding" [("zero", 0), ("special", 1)]

/-- The rows on the split of role `role` on scale `scale` in the language with glottocode
`lang`. -/
def rows (lang : Glottocode) (role scale : String) : List Datum :=
  Examples.all.filter fun e ↦
    e.language = lang ∧ e.feature? "role" = some role ∧ e.feature? "scale" = some scale

/-- The prominence value of a single-argument row, read through `table`. -/
def prominence? (table : List (String × α)) (e : Datum) : Option α :=
  e.parse? "prominence" table

/-- The two sides of `X > Y`, by a structural scan so that `decide` can evaluate it. -/
def splitGt : List Char → Option (List Char × List Char)
  | [] => none
  | ' ' :: '>' :: ' ' :: rest => some ([], rest)
  | c :: rest => (splitGt rest).map fun p ↦ (c :: p.1, p.2)

/-- The scenario `X > Y` of a scenario row, its sides read through `table`. -/
def scenario? (table : List (String × α)) (e : Datum) : Option (Scenario α) :=
  (e.feature? "scenario").bind fun s ↦ (splitGt s.toList).bind fun (x, y) ↦
    (table.lookup (String.ofList x)).bind fun h ↦
      (table.lookup (String.ofList y)).map (⟨h, ·⟩)

/-- The rows `rs` reproduce the split `c` on the values `x?` reads off them when each row reads to a
value at which the coding it shows is acceptable exactly when it is the coding `c` requires. -/
def Reproduces (rs : List Datum) (x? : Datum → Option α)
    (c : α → ℕ) : Prop :=
  rs ≠ [] ∧ ∀ e ∈ rs, ∃ x ∈ x? e, ∃ k ∈ codingShown e,
    (e.judgment = .acceptable ↔ c x = k)

instance (rs : List Datum) (x? : Datum → Option α) (c : α → ℕ) :
    Decidable (Reproduces rs x? c) := by
  unfold Reproduces; infer_instance

/-- The rows `rs` reproduce the alternation between `short` and `long` when a row showing zero
coding is acceptable exactly when the shorter construction is available in its scenario, and one
showing the special coding exactly when the longer one is. -/
def ReproducesAlternation (rs : List Datum)
    (s? : Datum → Option (Scenario α)) (short long : Scenario α → Prop)
    [DecidablePred short] [DecidablePred long] : Prop :=
  rs ≠ [] ∧ ∀ e ∈ rs, ∃ s ∈ s? e, ∃ k ∈ codingShown e,
    (e.judgment = .acceptable ↔ if k = 0 then short s else long s)

instance (rs : List Datum) (s? : Datum → Option (Scenario α))
    (short long : Scenario α → Prop) [DecidablePred short] [DecidablePred long] :
    Decidable (ReproducesAlternation rs s? short long) := by
  unfold ReproducesAlternation; infer_instance

/-- The person tags of the rows, as the binary scale. -/
def Person.Class.table : List (String × Person.Class) :=
  [("locuphoric", .participant), ("aliophoric", .nonParticipant),
    ("1", .participant), ("2", .participant), ("3", .nonParticipant)]

/-- The person tags of the rows, as the person hierarchy. -/
def prominenceTable : List (String × WithBot Person.Feature) :=
  [("1", Person.prominence .first), ("2", Person.prominence .second),
    ("3", Person.prominence .third)]

/-- The nominality tags of the rows. -/
def BinaryNominality.table : List (String × BinaryNominality) :=
  [("personForm", .personForm), ("fullNominal", .fullNominal), ("pers", .personForm),
    ("N", .fullNominal)]

/-- The animacy tags of the rows, as the binary scale. -/
def BinaryAnimacy.table : List (String × BinaryAnimacy) :=
  [("animate", .animate), ("inanimate", .inanimate)]

/-- The animacy tags of the rows, as the ternary scale. -/
def Animacy.table : List (String × Animacy) :=
  [("human", .human), ("animate", .animate), ("inanimate", .inanimate)]

/-- The definiteness tags of the rows. -/
def Definiteness.table : List (String × Definiteness) :=
  [("definite", .definite), ("indefinite", .indefinite), ("def", .definite), ("indef", .indefinite)]

/-- The givenness tags of the rows. -/
def BinaryGivenness.table : List (String × BinaryGivenness) := [("given", .given), ("new", .new)]

/-- The focus tags of the rows lie on the focus scale of (8b), which ranks background above focus as
the dual of the focus-marking order. -/
def focusTable : List (String × Markᵒᵈ) :=
  [("background", toDual .unfeatured), ("focus", toDual .focused)]

/-- The nominal-type tags of the rows. -/
def Nominality.table : List (String × Nominality) :=
  [("pers", .pronoun), ("prop", .properName), ("common", .commonNoun)]

/-- The definiteness and the nominality of a Makassarese row's T. -/
def makassarProminence? (e : Datum) : Option (Definiteness × BinaryNominality) := do
  pure (← e.parse? "definiteness" Definiteness.table,
    ← e.parse? "nominality" BinaryNominality.table)

-- §4.1, §4.2
theorem rows_splitP_splitA :
    Reproduces (rows .sakha "P" "definiteness") (prominence? Definiteness.table) sakhaP ∧
      Reproduces (rows .nuorese "P" "animacy") (prominence? Animacy.table) sardinianP ∧
      -- Punjabi's split is Sakha's, definiteness-conditioned P flagging (§4.1.2)
      Reproduces (rows .easternPanjabi "P" "definiteness") (prominence? Definiteness.table) sakhaP ∧
      Reproduces (rows .westernFarsi "P" "givenness") (prominence? BinaryGivenness.table) persianP ∧
      Reproduces (rows .continentalSouthernItalian "P" "person") (prominence? Person.Class.table)
        abruzzeseP ∧
      Reproduces (rows .takale "A" "person") (prominence? Person.Class.table) godoberiA ∧
      Reproduces (rows .warrgamay "A" "nominality") (prominence? BinaryNominality.table)
        warrgamayA ∧
      Reproduces (rows .mangarrayi "A" "animacy") (prominence? BinaryAnimacy.table) mangarrayiA ∧
      Reproduces (rows .centralTibetan "A" "focus") (prominence? focusTable) tibetanA := by
  decide

-- §5, §9
theorem rows_splitR_splitT :
    Reproduces (rows .christianTelkepe "R" "nominality") (prominence? BinaryNominality.table)
        neoAramaicR ∧
      Reproduces (rows .yakkha "R" "animacy") (prominence? BinaryAnimacy.table) yakkhaR ∧
      Reproduces (rows .wolof "R" "definiteness") (prominence? Definiteness.table) wolofR ∧
      Reproduces (rows .ewe "T" "nominality") (prominence? BinaryNominality.table) eweT ∧
      Reproduces (rows .akan "T" "definiteness") (prominence? Definiteness.table) akanT ∧
      Reproduces (rows .georgian "T" "person") (prominence? Person.Class.table) georgianT ∧
      Reproduces (rows .makasar "T" "definiteness and nominality") makassarProminence?
        makassarV := by
  decide

-- §6, §7, §9, (43), (44)
theorem rows_scenario :
    -- Teop's split is "completely parallel" to Kolyma Yukaghir's (§6.1)
    Reproduces (rows .teop "P" "person") (scenario? Person.Class.table) yukaghirP ∧
      Reproduces (rows .southernYukaghir "P" "person") (scenario? Person.Class.table) yukaghirP ∧
      Reproduces (rows .sahaptin "A" "person") (scenario? Person.Class.table) sahaptinA ∧
      Reproduces (rows .eastKhanty "A" "definiteness") (scenario? Definiteness.table) khantyA ∧
      Reproduces (rows .spanish "P" "animacy") (scenario? Animacy.table) spanishP ∧
      Reproduces (rows .bulgarian "R" "person") (scenario? Person.Class.table) bulgarianR ∧
      Reproduces (rows .shambala "R" "person") (scenario? Person.Class.table) shambalaR ∧
      Reproduces ((rows .english "R" "nominality").filter (·.feature? "variety" = none))
        (scenario? BinaryNominality.table) englishR ∧
      Reproduces ((rows .english "R" "nominality").filter
          (·.feature? "variety" = some "American"))
        (scenario? BinaryNominality.table) americanEnglishR ∧
      Reproduces (rows .modernGreek "T" "person") (scenario? Person.Class.table) greekT ∧
      Reproduces (rows .icelandic "R" "animacy") (scenario? BinaryAnimacy.table) icelandicR ∧
      Reproduces (rows .kashmiri "P" "person") (scenario? prominenceTable) kashmiriP ∧
      Reproduces (rows .baoulé "T" "nominal type") (scenario? Nominality.table) bauleT ∧
      Reproduces (rows .itonama "verb" "person") (scenario? Person.Class.table) itonamaV := by
  decide

-- §10.2, (4)
theorem rows_alternations :
    ReproducesAlternation (rows .lummi "A" "nominality") (scenario? BinaryNominality.table)
        lummiActive lummiPassive ∧
      ReproducesAlternation (rows .koyraChiiniSonghay "R" "nominality")
        (scenario? BinaryNominality.table) koyraChiiniDoubleObject (fun _ ↦ True) ∧
      ReproducesAlternation ((rows .english "R" "nominality").filter
          (·.feature? "variety" = none))
        (scenario? BinaryNominality.table) englishDoubleObject (fun _ ↦ True) := by
  decide

end Examples

end Haspelmath2021
