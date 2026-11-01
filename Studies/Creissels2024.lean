module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Relation
public import Linglib.Syntax.Voice.System
public import Linglib.Semantics.Plurality.Reciprocal
public import Linglib.Data.Examples.Creissels2024
public import Linglib.Data.Experiments.Creissels2024
public import Linglib.Fragments.English.Verbs.Causative
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Creissels (2024): Transitivity, Valency, and Voice

A valency alternation relates two constructions of one verb, which express its participants as
nominal terms with the transitivity-related roles A, P, S or X, as dative obliques, as implied
participants, or not at all. Marked by verbal morphology it is a voice alternation, and the
oriented types are defined by nucleativization, a participant becoming a core term, and
denucleativization, a core term ceasing to be one, whether it is maintained in participant
structure or suppressed from it. Symmetrical voices select a pivot without either and fall
outside the typology. Alignment is reformulated as obligatory A-coding or P-coding, which split-S
languages violate.

## Implementation notes

* The types of voice alternation are the substrate's (`Syntax/Voice/Construction.lean`),
  predicates on a pair of `Voice.Construction`s with the participant the type singles out as a
  parameter; `Kind` names them as the book does, for the rows. The semantic conditions that separate
  causativization from the other A/S-nucleativizations are not modelled; the rows carry the
  book's label. Reflexivization and reciprocalization share their structure, and what separates
  them, an individual or a group as S, is stated for §11.3's polysemy over the reciprocity
  quantifiers of `Semantics/Plurality/Reciprocal.lean`, with "a sizeable proportion" of the
  group read as all of it.
* Frames record no dative oblique and no concernee, so D-applicativization and
  concernativization have examples but no voice.
* The Obligatory Coding Principle is stated over the flags of S in the book's intransitive
  examples; the book's principle ranges over every verb's coding frame.

## TODO

* Chapters 2 to 7, and chapters 9 to 17 beyond their definitions, are not modelled.
* The potential-participant condition on nucleativization (§8.1.6), the non-compositional
  readings of stacked markers (§8.4.3) and the diachronic scenarios are prose.

## References

* [creissels-2024]
* [bahrt-2021]
* [langendoen-1978]
-/

@[expose] public section

namespace Creissels2024

open Voice Voice.Construction

variable {ι : Type*}

/-! ### The types the book names -/

/-- The types of voice alternation the book names, symmetrical voices included. -/
inductive Kind where
  | passivization
  | impersonalPassivization
  | antipassivization
  | sDenucleativization
  | decausativization
  | causativization
  | concernativization
  | aNucleativization
  | reflexivization
  | reciprocalization
  | pApplicativization
  | dApplicativization
  | xApplicativization
  | portative
  | symmetrical
  deriving DecidableEq, Repr, Fintype

/-- Whether a pair of constructions realizes a type, given the participant the type singles
out; the three A/S-nucleativizations and the two cumulations share their structure. -/
def Kind.Realize (c d : Construction ι) : Kind → Option ι → Prop
  | .passivization, _ => c.IsPassivization d
  | .impersonalPassivization, _ => c.IsImpersonalPassivization d
  | .antipassivization, _ => c.IsAntipassivization d
  | .sDenucleativization, _ => c.IsSDenucleativization d
  | .decausativization, _ => c.IsDecausativization d
  | .causativization, some i => c.IsASNucleativization d i
  | .concernativization, some i => c.IsASNucleativization d i
  | .aNucleativization, some i => c.IsASNucleativization d i
  | .reflexivization, _ => c.IsCumulation d
  | .reciprocalization, _ => c.IsCumulation d
  | .pApplicativization, some i => c.IsPApplicativization d i
  | .dApplicativization, some i => c.IsDApplicativization d i
  | .xApplicativization, some i => c.IsXApplicativization d i
  | .portative, some i => c.IsPortative d i
  | .symmetrical, _ => c.IsSymmetrical d
  | _, none => False

instance [Fintype ι] [DecidableEq ι] (c d : Construction ι) (k : Kind) (o : Option ι) :
    Decidable (k.Realize c d o) := by
  cases k <;> cases o <;> simp only [Kind.Realize] <;> infer_instance

/-! ### The book's voices -/

open ArgumentFrame.Slot in
/-- In A/S-nucleativization of an oblique (§8.3.4.1) an instrumental oblique takes over the
role of A and the initial A is left implied, understood as non-specific. -/
def instrumentNucleativization : Voice :=
  .of .np_pp ⟨some .nominal, [.nominal, .implicit]⟩
    [some (complement 1), some (complement 0), some external]

open ArgumentFrame.Slot in
/-- In X-applicativization (§8.3.5) an applied participant is expressed as an ordinary
oblique, the initial S unchanged. -/
def obliqueApplicative : Voice := .of .intransitive .pp [some external, some (complement 0)]

open ArgumentFrame.Slot in
/-- In portative derivation (§8.3.7) an intransitive motion verb becomes transitive, its S the
A and a carried entity the P. -/
def portative : Voice := .of .intransitive .np [some external, some (complement 0)]

/-- The book's voices of §8.3.4.1, §8.3.5 and §8.3.7 realize the types they are named for. -/
theorem voices_typed :
    instrumentNucleativization.IsASNucleativization ∧
      (∃ i, obliqueApplicative.initial.construction.IsXApplicativization
        obliqueApplicative.derived.construction i) ∧
      ∃ i, portative.initial.construction.IsPortative portative.derived.construction i := by
  decide

theorem instrumentNucleativization_neutral :
    instrumentNucleativization.Nucleativizes ∧ instrumentNucleativization.Denucleativizes ∧
      ¬ instrumentNucleativization.IsValencyIncreasing ∧
      ¬ instrumentNucleativization.IsValencyDecreasing := by
  decide

theorem portative_isValencyIncreasing : portative.IsValencyIncreasing := by decide

/-- English *break* is a decausativization in the fragment's own diatheses: the intransitive
leaves the breaker out of participant structure and makes the thing broken the S, so it is not a
passivization. -/
theorem break_decausativization :
    ∃ c ∈ English.Verbs.break_.valency.basic?, ∃ d ∈ English.Verbs.break_.valency.diatheses,
      c.construction.IsDecausativization d.construction ∧
        ¬ c.construction.IsPassivization d.construction := by
  decide +kernel

/-! ### Alignment and the Obligatory Coding Principle (§1.3.4) -/

/-- A core term is flagged by the zero case, an accusative or an ergative. -/
inductive Flag where
  | zero
  | accusative
  | ergative
  deriving DecidableEq, Repr

/-- The flags of A and of P in an A/P-prominent transitive construction, which contrast. -/
structure Flagging where
  /-- The flag of A. -/
  a : Flag
  /-- The flag of P. -/
  p : Flag
  /-- A and P are flagged apart. -/
  ne : a ≠ p
  deriving DecidableEq, Repr

namespace Flagging

/-- An intransitive construction whose S carries a flag aligns with A, with P, or with
neither. -/
def alignment (t : Flagging) (s : Flag) : Option Alignment :=
  if s = t.a then some .A_alignment else if s = t.p then some .P_alignment else none

@[simp] theorem alignment_eq_A_iff {t : Flagging} {s : Flag} :
    t.alignment s = some .A_alignment ↔ s = t.a := by
  grind [alignment]

@[simp] theorem alignment_eq_P_iff {t : Flagging} {s : Flag} :
    t.alignment s = some .P_alignment ↔ s = t.p := by
  grind [alignment, Flagging.ne]

end Flagging

/-- The Obligatory Coding Principle, over the intransitive constructions of the examples:
every verb assigns a flag of the transitive construction to one of its participants, here
every intransitive verb through its S. -/
def ObligatoryCoding (t : Flagging) (ss : List Flag) (k : Flag) : Prop :=
  (k = t.a ∨ k = t.p) ∧ ∀ s ∈ ss, s = k

/-- An obligatory A-coding language, the consistently accusative type. -/
def ObligatoryACoding (t : Flagging) (ss : List Flag) : Prop := ObligatoryCoding t ss t.a

/-- An obligatory P-coding language, the consistently ergative type. -/
def ObligatoryPCoding (t : Flagging) (ss : List Flag) : Prop := ObligatoryCoding t ss t.p

/-- A language is split-S when some intransitive constructions align with A and some with
P. -/
def SplitS (t : Flagging) (ss : List Flag) : Prop :=
  (∃ s ∈ ss, t.alignment s = some .A_alignment) ∧ ∃ s ∈ ss, t.alignment s = some .P_alignment

section
variable (t : Flagging) (ss : List Flag)

instance (k : Flag) : Decidable (ObligatoryCoding t ss k) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (ObligatoryACoding t ss) := inferInstanceAs (Decidable (ObligatoryCoding ..))
instance : Decidable (ObligatoryPCoding t ss) := inferInstanceAs (Decidable (ObligatoryCoding ..))
instance : Decidable (SplitS t ss) := inferInstanceAs (Decidable (_ ∧ _))

end

variable {t : Flagging} {ss : List Flag}

theorem obligatoryACoding_iff :
    ObligatoryACoding t ss ↔ ∀ s ∈ ss, t.alignment s = some .A_alignment := by
  simp [ObligatoryACoding, ObligatoryCoding]

theorem obligatoryPCoding_iff :
    ObligatoryPCoding t ss ↔ ∀ s ∈ ss, t.alignment s = some .P_alignment := by
  simp [ObligatoryPCoding, ObligatoryCoding]

theorem SplitS.not_obligatoryACoding (h : SplitS t ss) : ¬ ObligatoryACoding t ss := by
  grind [SplitS, ObligatoryACoding, ObligatoryCoding, Flagging.alignment, Flagging.ne]

theorem SplitS.not_obligatoryPCoding (h : SplitS t ss) : ¬ ObligatoryPCoding t ss := by
  grind [SplitS, ObligatoryPCoding, ObligatoryCoding, Flagging.alignment, Flagging.ne]

/-! ### The distribution of the types (§8.3.8) -/

-- Every printed share rounds a whole number of the sample's languages.
example : ∀ t, (bahrtShares t).share.AttainablePercent bahrtSampleSize := by decide +kernel

theorem bahrtShares_extremes (t : BahrtType) :
    (bahrtShares .antipassivization).share.toRat ≤ (bahrtShares t).share.toRat ∧
      (bahrtShares t).share.toRat ≤ (bahrtShares .causativization).share.toRat := by
  cases t <;> decide +kernel

/-! ### The book's examples -/

/-- The types by name. -/
def kindNames : List (String × Kind) :=
  [("passivization", .passivization), ("impersonalPassivization", .impersonalPassivization),
    ("antipassivization", .antipassivization), ("sDenucleativization", .sDenucleativization),
    ("decausativization", .decausativization), ("causativization", .causativization),
    ("concernativization", .concernativization), ("aNucleativization", .aNucleativization),
    ("reflexivization", .reflexivization), ("reciprocalization", .reciprocalization),
    ("pApplicativization", .pApplicativization), ("dApplicativization", .dApplicativization),
    ("xApplicativization", .xApplicativization), ("portative", .portative),
    ("symmetrical", .symmetrical)]

/-- The statuses by name. -/
def statusNames : List (String × Status) :=
  [("A", .term .A), ("P", .term .P), ("S", .term .S), ("X", .term .X), ("dative", .dative),
    ("implicit", .implicit), ("absent", .absent)]

/-- The participant slots of a row by name. -/
def slotNames : List (String × Fin 5) := [("p1", 0), ("p2", 1), ("p3", 2), ("p4", 3), ("p5", 4)]

/-- The flags by name. -/
def flagNames : List (String × Flag) :=
  [("zero", .zero), ("accusative", .accusative), ("ergative", .ergative)]

/-- The codings of an alternation by name; an equipollent row codes a pair of voices, not
one. -/
def codingNames : List (String × Voice.Coding) :=
  [("synthetic", .synthetic), ("analytic", .analytic), ("uncoded", .uncoded)]

namespace Examples

/-- The construction a row describes over its five participant slots, absent where
unlisted. -/
def construction (row : Datum) : Construction (Fin 5) :=
  ![slot row "p1", slot row "p2", slot row "p3", slot row "p4", slot row "p5"]
where
  /-- The status of one slot. -/
  slot (row : Datum) (k : String) : Status := (row.parse? k statusNames).getD .absent

/-- `paired key row` is the row of the same example whose variant `row` names under `key`,
such as its initial construction or the transitive use of a flexivalent verb. -/
def paired (key : String) (row : Datum) : Option Datum :=
  match row.feature? "example", row.feature? key with
  | some e, some v =>
    all.find? fun r ↦ r.feature? "example" = some e ∧ r.feature? "variant" = some v
  | _, _ => none

/-- The S flags of a language's intransitive examples. -/
def sFlags (language : Glottocode) : List Flag :=
  (all.filter (·.language = language)).filterMap (·.parse? "S" flagNames)

/-- The A and P flags of a language's transitive example. -/
def flagging (language : Glottocode) : Option Flagging :=
  (all.filter (·.language = language)).findSome? fun r ↦ do
    let a ← r.parse? "A" flagNames
    let p ← r.parse? "P" flagNames
    if h : a ≠ p then some ⟨a, p, h⟩ else none

/-- The types a marker of a language codes across the book's examples. -/
def coExpressed (language : Glottocode) (marker : String) : List Kind :=
  (all.filter fun r ↦ r.language = language ∧ r.feature? "marker" = some marker).filterMap
    (·.parse? "alternation" kindNames)

end Examples

open Examples

theorem alternation_parses : ∀ row ∈ all,
    (row.feature? "alternation").isSome → (row.parse? "alternation" kindNames).isSome := by
  decide +kernel

theorem paired_resolves : ∀ row ∈ all, ∀ key ∈ ["initial", "transitive"],
    (row.feature? key).isSome → (paired key row).isSome := by
  decide +kernel

/-- Every derived construction of the book's examples realizes the type the book assigns
it, relative to its initial construction. -/
theorem rows_classified : ∀ row ∈ all, ∀ k ∈ row.parse? "alternation" kindNames,
    ∀ init ∈ paired "initial" row,
    k.Realize (construction init) (construction row) (row.parse? "new" slotNames) := by
  decide +kernel

theorem symmetrical_rows : ∀ row ∈ all, row.parse? "alternation" kindNames = some .symmetrical →
    ∀ init ∈ paired "initial" row, ∃ p ∈ row.parse? "pivot" slotNames,
    ∃ q ∈ init.parse? "pivot" slotNames, p ≠ q ∧ (construction row p).role.isSome := by
  decide +kernel

-- (13)
theorem mandinka_roles :
    (construction ex_1_13a).Transitive ∧ ¬ (construction ex_1_13b).Transitive := by
  decide +kernel

-- (23), (24), (22)
theorem alignment_rows :
    (∃ t ∈ flagging .russian,
      sFlags .russian ≠ [] ∧ ObligatoryACoding t (sFlags .russian)) ∧
    (∃ t ∈ flagging .avar,
      sFlags .avar ≠ [] ∧ ObligatoryPCoding t (sFlags .avar)) ∧
    ∃ t ∈ flagging .basque, SplitS t (sFlags .basque) := by
  decide +kernel

-- (2), (3), (4)
theorem ambitransitivity_rows : ∀ row ∈ all,
    row.parse? "marking" codingNames = some .uncoded → ∀ init ∈ paired "transitive" row,
    (construction init).Transitive ∧ ¬ (construction row).Transitive ∧
    (∀ i, construction init i = .term .P → construction row i = .term .S) ∧
    (∀ i, construction init i = .term .A → ¬ (construction row i).Nuclear) ∧
    ((construction init).PreservesStructure (construction row) ↔ row.language = .bambara) := by
  decide +kernel

theorem coexpression :
    [Kind.passivization, .impersonalPassivization, .sDenucleativization] ⊆
      coExpressed .tswana "-w" ∧
    [Kind.pApplicativization, .xApplicativization, .aNucleativization] ⊆
      coExpressed .tswana "-ɛl" ∧
    [Kind.causativization, .portative] ⊆ coExpressed .tswana "-is" ∧
    [Kind.causativization, .passivization] ⊆ coExpressed .koyraChiiniSonghay "-ndi" := by
  decide +kernel

/-- In Tswana (38), passivizing the applicative of the causative is the composite of the three
alternations, through (38d) and (38e). -/
theorem stacking_tswana :
    Relation.Comp (Relation.Comp (IsASNucleativization · · 2) (IsPApplicativization · · 3))
      Construction.IsPassivization (construction ex_8_38a) (construction ex_8_38h) :=
  ⟨construction ex_8_38e, ⟨construction ex_8_38d, by decide +kernel, by decide +kernel⟩,
    by decide +kernel⟩

/-- Classical Nahuatl (39) forms the passive of the antipassive of the causative, through
(39b) and (39c). -/
theorem stacking_nahuatl :
    Relation.Comp (Relation.Comp (IsASNucleativization · · 2) Construction.IsAntipassivization)
      Construction.IsPassivization (construction ex_8_39a) (construction ex_8_39e) :=
  ⟨construction ex_8_39c, ⟨construction ex_8_39b, by decide +kernel, by decide +kernel⟩,
    by decide +kernel⟩

-- (38f), (38c)
theorem passive_transitive :
    (construction ex_8_38c).IsPassivization (construction ex_8_38f) ∧
    (construction ex_8_38f).Transitive := by
  decide +kernel

-- (51)
theorem causative_valency :
    (construction ex_8_51a).Nucleativizes (construction ex_8_51b) ∧
    (construction ex_8_51a).Denucleativizes (construction ex_8_51b) ∧
    (construction ex_8_51a).valency = (construction ex_8_51b).valency := by
  decide +kernel

-- (3)
theorem portative_rows :
    ex_12_3b.judgment = .acceptable ∧ ex_12_3c.judgment = .ungrammatical ∧
    construction ex_12_3b 0 = .term .S ∧ construction ex_12_3c 1 = .term .S := by
  decide +kernel

/-! ### Symmetrical voice systems (§8.5) -/

open ArgumentFrame.Slot in
/-- The Balinese passive (49) in *ka-* makes the water, the initial P, the S and expresses the
drinker, the initial A, as an oblique flagged by *teken* 'by'. -/
def balinesePassive : Voice :=
  (Voice.of .np .pp [some (complement 0), some external]).marked [.pref "ka"]

open ArgumentFrame.Slot in
/-- The Balinese applicative (50) in *-in* makes the person, an oblique flagged by *sig*, the
first P of a double-P construction and the rice the second. -/
def balineseApplicative : Voice :=
  (Voice.of .np_pp .np_np [some external, some (complement 1), some (complement 0)]).marked
    [.suff "in"]

open ArgumentFrame.Slot in
/-- The Balinese causative (51) in *-ang* makes the causer the A, the kisser the P and the
kissed sibling an oblique flagged by *sig*. -/
def balineseCausative : Voice :=
  (Voice.of .np .np_pp [some (complement 0), some (complement 1), some external]).marked
    [.suff "ang"]

theorem balinesePassive_isPassivization : balinesePassive.IsPassivization := by
  decide

-- (50), (51)
theorem balinese_rows : ∀ i : Fin 3,
    balineseApplicative.initial.construction i = construction ex_8_50a (Fin.castLE (by omega) i) ∧
    balineseApplicative.derived.construction i = construction ex_8_50b (Fin.castLE (by omega) i) ∧
    balineseCausative.initial.construction i = construction ex_8_51a (Fin.castLE (by omega) i) ∧
    balineseCausative.derived.construction i = construction ex_8_51b (Fin.castLE (by omega) i) := by
  decide +kernel

/-- Balinese (47) has a binary symmetrical system, the patient voice bare and initial, the agent
voice marked by a nasal prefix, both keeping the taker and the shirt core terms; beside them it
has the passive (49), the applicative (50) and the causative (51) (§8.5.3). -/
def balinese : Voice.System :=
  {patientVoice, agentVoice.marked [.pref "N"], balinesePassive, balineseApplicative,
    balineseCausative}

/-- The passive, the applicative and the causative change the construction, so the symmetrical
voices of Balinese are its agent and patient voices (§8.5.3). -/
theorem balinese_symmetrical :
    balinese.symmetrical = {patientVoice, agentVoice.marked [.pref "N"]} := by
  decide

/-- Tagalog (48) has a multiple symmetrical system, every voice marked and the pivot flagged
by *ang* in place of its own flag. The agent voice is marked by the infix *-um-*, the patient
voice by *-in*, null in the realis, the locative voice, which selects the store, a spatial
oblique, by *-an*, and the conveyance and instrumental voices, which select the child and the
money, by *i-* and *ipaN-*. -/
def tagalog : Voice.System :=
  {agentVoice.marked [.infixed "um"], patientVoice.marked [.suff "in"],
    locativeVoice.marked [.suff "an"], (obliqueVoice .semantic).marked [.pref "i"],
    (obliqueVoice .semantic).marked [.pref "ipaN"]}

-- §8.1.7, §8.5.1
theorem balinese_binary :
    balinese.IsSymmetrical ∧ ¬ balinese.IsMultiple ∧ ¬ balinese.IsEquipollent := by
  decide

-- §8.5.2
theorem tagalog_pivotRoles : tagalog.symmetrical.pivotRoles = {some .A, some .P, some .X} := by
  decide

-- §8.5.2
theorem tagalog_isMultiple : tagalog.IsMultiple := by decide

theorem tagalog_synthetic : ∀ v ∈ tagalog, v.coding = .synthetic := by decide

/-! ### The reflexive–reciprocal polysemy (§11.3)

A reciprocal event has a group as S whose members fulfill both roles of a bivalent verb "in their
interaction with other members of the group" (§8.3.3); the guests greeted "another" member and
were also greeted (§11.3.1). Read for every member, this is Weak Reciprocity, and on two
participants it is the paraphrase of (30b). §11.3.3 explains the reflexive–reciprocal polysemy
two ways: a reciprocal event is a reflexive event of a plural individual, the relation lifted to
pluralities (`Set.LiftRel`) holding of the group and itself, and a reflexive event is the
borderline case of a single participant. Its wording there drops "other": the borderline case
holds for every member doing and undergoing, and fails for Weak Reciprocity, which no single
participant satisfies. -/

section Polysemy

open Reciprocal

variable {α : Type*} {R : α → α → Prop}

/-- On two participants the reciprocal event of §11.3.1 is (30b), *John greeted Peter and Peter
greeted John*. -/
theorem weakReciprocity_pair_iff [DecidableEq α] {a b : α} (hab : a ≠ b) :
    WeakReciprocity R {a, b} ↔ R a b ∧ R b a := by
  simp only [WeakReciprocity, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq, exists_eq_or_imp, ne_eq, not_true_eq_false, and_false, false_or, hab,
    Ne.symm hab, not_false_eq_true, and_true]
  tauto

/-- Reduced to a single participant, every member doing and undergoing is the reflexive event
(§11.3.3). -/
theorem liftRel_singleton_iff (x : α) :
    Set.LiftRel R ↑({x} : Finset α) ↑({x} : Finset α) ↔ R x x := by
  simp [Set.LiftRel]

/-- No single participant is a reciprocal event in the sense of §8.3.3 and §11.3.1, so the
borderline case of §11.3.3 needs that section's own wording. -/
theorem not_weakReciprocity_singleton (x : α) : ¬ WeakReciprocity R {x} := by
  rintro ⟨h, -⟩
  obtain ⟨y, hy, -, hxy⟩ := h x (Finset.mem_singleton_self x)
  exact hxy (Finset.mem_singleton.1 hy).symm

end Polysemy

end Creissels2024
