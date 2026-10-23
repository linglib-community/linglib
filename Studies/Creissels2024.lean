module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Relation
public import Linglib.Syntax.Voice.System
public import Linglib.Semantics.Plurality.Reciprocal
public import Linglib.Data.Examples.Creissels2024
public import Linglib.Data.Experiments.Creissels2024
public import Linglib.Fragments.English.Verbs.Causative

/-!
# Creissels (2024): Transitivity, Valency, and Voice

A valency alternation relates two constructions of one verb, which express its participants as
nominal terms with the transitivity-related roles A, P, S or X, as dative obliques, as implied
participants, or not at all. Marked by verbal morphology it is a voice alternation, and the
oriented types are defined by nucleativization, a participant becoming a core term, and
denucleativization, a core term ceasing to be one, by demotion within participant structure or
by suppression from it. Symmetrical voices select a pivot without either and fall outside the
typology. Alignment is reformulated as obligatory A-coding or P-coding, which split-S languages
violate.

## Main statements

* `rows_classified`: every derived construction of the book's examples realizes the type the
  book assigns it.
* `voices_typed`: the substrate's voices realize the types they are named for.
* `stacking_tswana`, `stacking_nahuatl`: stacked voice markers compose their alternations.
* `balinese_symmetrical`: beside a passive, an applicative and a causative, the symmetrical
  voices of Balinese are its agent and patient voices.
* `break_decausativization`: the English fragment's *break* is a decausativization in its own
  diatheses.
* `weakReciprocity_pair_iff`, `liftRel_singleton_iff`, `not_weakReciprocity_singleton`: the
  reciprocal event of §11.3.1 is (30b) on two participants, and §11.3.3's account of the
  reflexive–reciprocal polysemy holds for every member doing and undergoing but not for the
  reciprocity with "another member" of §8.3.3 and §11.3.1.

## Implementation notes

* An alternation is a pair of `Voice.Construction`s, a type a predicate on the pair with the
  participant the type singles out as a parameter. The semantic conditions that separate
  causativization from the other A/S-nucleativizations are not modelled; the rows carry the
  book's label. Reflexivization and reciprocalization share their structure, and what separates
  them, an individual or a group as S, is stated for §11.3's polysemy over the reciprocity
  quantifiers of `Semantics/Plurality/Reciprocal.lean`, with "a sizeable proportion" of the
  group read as all of it.
* Passivization also keeps the initial P nuclear, which footnote 1 of §8.1.3 states beside the
  three defining features of §8.3.2.1.
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

/-! ### The main types of voice alternation (§8.3) -/

/-- The two constructions imply the same participants. -/
def PreservesStructure (c d : Construction ι) : Prop := ∀ i, c i = .absent ↔ d i = .absent

/-- A participant is demoted, the common core of §8.3.2, when it is denucleativized without
leaving participant structure and no participant is nucleativized. -/
def Demoted (c d : Construction ι) (i : ι) : Prop :=
  c.Denucleativized d i ∧ d i ≠ .absent ∧ ¬ c.Nucleativizes d

/-- In passivization the initial construction is transitive and its A is demoted, and its P
remains a core term, as S in the canonical case and as P after a double-P construction. -/
def Passivization (c d : Construction ι) : Prop :=
  c.Transitive ∧ (∀ i, c i = .term .A → Demoted c d i) ∧ ∀ i, c i = .term .P → (d i).Nuclear

/-- In the impersonal variant of passivization the initial P keeps its coding, so the derived
construction has neither A nor S. -/
def ImpersonalPassivization (c d : Construction ι) : Prop := Passivization c d ∧ d.Impersonal

/-- In antipassivization the initial construction is transitive, participant structure is
unchanged, a P is demoted, and the initial A becomes the S of an intransitive construction, or
keeps the role of A after a double-P construction. -/
def Antipassivization (c d : Construction ι) : Prop :=
  c.Transitive ∧ PreservesStructure c d ∧ (∃ i, c i = .term .P ∧ Demoted c d i) ∧
    ∀ i, c i = .term .A → d i = .term .S ∨ d i = .term .A

/-- In S-denucleativization the initial construction is intransitive and its S is demoted. -/
def SDenucleativization (c d : Construction ι) : Prop :=
  ¬ c.Transitive ∧ (∃ i, c i = .term .S) ∧ ∀ i, c i = .term .S → Demoted c d i

/-- In decausativization the initial construction is transitive, its A is suppressed from
participant structure, and its P becomes the S of an intransitive construction. -/
def Decausativization (c d : Construction ι) : Prop :=
  c.Transitive ∧ (∀ i, c i = .term .A → c.Suppressed d i) ∧ ∀ i, c i = .term .P → d i = .term .S

/-- In A/S-nucleativization a participant is nucleativized and takes over the role of A or S,
the initial A or S coded as P or denucleativized. Causativization, where the new participant
instigates or controls the event, the A/S-nucleativization of an oblique, and
concernativization, where it is a concernee of the initial S or P, share this structure. -/
def ANucleativization (c d : Construction ι) (i : ι) : Prop :=
  c.Nucleativized d i ∧ (d i = .term .A ∨ d i = .term .S) ∧
    ∀ j, (c j = .term .A ∨ c j = .term .S) → d j = .term .P ∨ ¬ (d j).Nuclear

/-- In reflexivization and reciprocalization two participant roles expressed as A and P, or as
S and a dative oblique, are cumulated by the S term of the derived construction. -/
def Cumulation (c d : Construction ι) : Prop :=
  ∃ a p, a ≠ p ∧ ((c a = .term .A ∧ c p = .term .P) ∨ (c a = .term .S ∧ c p = .dative)) ∧
    d a = .term .S ∧ d p = .term .S

/-- In applicativization the initial A or S keeps the role of A or S, and the derived
construction introduces, in a role other than A or S, an applied participant. -/
def Applicativization (c d : Construction ι) (applied : ι) : Prop :=
  (∀ j, (c j = .term .A ∨ c j = .term .S) → d j = .term .A ∨ d j = .term .S) ∧
    c.Introduced d applied ∧ d applied ≠ .term .A ∧ d applied ≠ .term .S

/-- In P-applicativization the applied phrase is a P, and the initial A or S is the A of the
derived transitive construction. -/
def PApplicativization (c d : Construction ι) (applied : ι) : Prop :=
  Applicativization c d applied ∧ d applied = .term .P ∧
    ∀ j, (c j = .term .A ∨ c j = .term .S) → d j = .term .A

/-- In D-applicativization the applied phrase is a dative oblique. -/
def DApplicativization (c d : Construction ι) (applied : ι) : Prop :=
  Applicativization c d applied ∧ d applied = .dative

/-- In X-applicativization the applied phrase is an ordinary oblique. -/
def XApplicativization (c d : Construction ι) (applied : ι) : Prop :=
  Applicativization c d applied ∧ d applied = .term .X

/-- In portative derivation an intransitive verb of motion becomes transitive, its S the A of
the derived construction and a carried entity its P. -/
def Portative (c d : Construction ι) (carried : ι) : Prop :=
  ¬ c.Transitive ∧ c.Nucleativized d carried ∧ d carried = .term .P ∧
    ∀ j, c j = .term .S → d j = .term .A

section
variable [Fintype ι] [DecidableEq ι] (c d : Construction ι)

instance : Decidable (PreservesStructure c d) := inferInstanceAs (Decidable (∀ _, _))
instance (i : ι) : Decidable (Demoted c d i) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (Passivization c d) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (ImpersonalPassivization c d) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (Antipassivization c d) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (SDenucleativization c d) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (Decausativization c d) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ι) : Decidable (ANucleativization c d i) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (Cumulation c d) := inferInstanceAs (Decidable (∃ _, _))
instance (i : ι) : Decidable (Applicativization c d i) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ι) : Decidable (PApplicativization c d i) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ι) : Decidable (DApplicativization c d i) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ι) : Decidable (XApplicativization c d i) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ι) : Decidable (Portative c d i) := inferInstanceAs (Decidable (_ ∧ _))

end

variable {c d : Construction ι}

theorem Decausativization.not_preservesStructure (h : Decausativization c d) :
    ¬ PreservesStructure c d :=
  let ⟨⟨⟨a, ha⟩, _⟩, hA, _⟩ := h
  fun hp ↦ absurd ((hp a).mpr (hA a ha).2) (by simp [ha])

theorem Passivization.not_decausativization (h : Passivization c d) : ¬ Decausativization c d :=
  let ⟨⟨⟨a, ha⟩, _⟩, hA, _⟩ := h
  fun h' ↦ (hA a ha).2.1 (h'.2.1 a ha).2

theorem SDenucleativization.not_nuclear (h : SDenucleativization c d)
    (hc : ∀ i, (c i).Nuclear → c i = .term .S) (i : ι) : ¬ (d i).Nuclear := fun hd ↦ by
  by_cases hi : (c i).Nuclear
  · exact (h.2.2 i (hc i hi)).1.2 hd
  · obtain ⟨s, hs⟩ := h.2.1
    exact (h.2.2 s hs).2.2 ⟨i, hi, hd⟩

theorem Portative.not_aNucleativization {i : ι} (h : Portative c d i)
    (hS : ∃ s, c s = .term .S) (j : ι) : ¬ ANucleativization c d j := by
  grind [Portative, ANucleativization, Status.Nuclear]

theorem not_passivization_of_isSymmetrical (h : c.IsSymmetrical d) : ¬ Passivization c d :=
  fun ⟨⟨⟨a, ha⟩, _⟩, hA, _⟩ ↦ h.not_denucleativizes ⟨a, (hA a ha).1⟩

theorem not_aNucleativization_of_isSymmetrical (h : c.IsSymmetrical d) (i : ι) :
    ¬ ANucleativization c d i :=
  fun hc ↦ h.not_nucleativizes ⟨i, hc.1⟩

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
  | .passivization, _ => Passivization c d
  | .impersonalPassivization, _ => ImpersonalPassivization c d
  | .antipassivization, _ => Antipassivization c d
  | .sDenucleativization, _ => SDenucleativization c d
  | .decausativization, _ => Decausativization c d
  | .causativization, some i => ANucleativization c d i
  | .concernativization, some i => ANucleativization c d i
  | .aNucleativization, some i => ANucleativization c d i
  | .reflexivization, _ => Cumulation c d
  | .reciprocalization, _ => Cumulation c d
  | .pApplicativization, some i => PApplicativization c d i
  | .dApplicativization, some i => DApplicativization c d i
  | .xApplicativization, some i => XApplicativization c d i
  | .portative, some i => Portative c d i
  | .symmetrical, _ => c.IsSymmetrical d
  | _, none => False

instance [Fintype ι] [DecidableEq ι] (c d : Construction ι) (k : Kind) (o : Option ι) :
    Decidable (k.Realize c d o) := by
  cases k <;> cases o <;> simp only [Kind.Realize] <;> infer_instance

/-! ### The substrate's voices -/

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

/-- Each voice with the type it is named for. -/
def voiceTypes : List (Voice × Kind) :=
  [(passive, .passivization), (impersonalPassive, .impersonalPassivization),
    (impersonalPassive .intransitive, .sDenucleativization),
    (antipassive, .antipassivization), (anticausative, .decausativization),
    (causative, .causativization), (reflexive, .reflexivization),
    (reciprocal, .reciprocalization),
    (instrumentNucleativization, .aNucleativization), (applicative, .pApplicativization),
    (obliqueApplicative, .xApplicativization), (portative, .portative),
    (patientVoice, .symmetrical)]

theorem voices_typed :
    ∀ e ∈ voiceTypes, ∃ o, e.2.Realize e.1.initial.construction e.1.derived.construction o := by
  decide +kernel

theorem instrumentNucleativization_neutral :
    instrumentNucleativization.Nucleativizes ∧ instrumentNucleativization.Denucleativizes ∧
      ¬ instrumentNucleativization.IsValencyIncreasing ∧
      ¬ instrumentNucleativization.IsValencyDecreasing := by
  decide

theorem portative_isValencyIncreasing : portative.IsValencyIncreasing := by decide

theorem break_decausativization :
    ∃ c ∈ English.Verbs.break_.valency.basic?, ∃ d ∈ English.Verbs.break_.valency.diatheses,
      Decausativization c.construction d.construction ∧
        ¬ Passivization c.construction d.construction := by
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
def sFlags (language : String) : List Flag :=
  (all.filter (·.language = language)).filterMap (·.parse? "S" flagNames)

/-- The A and P flags of a language's transitive example. -/
def flagging (language : String) : Option Flagging :=
  (all.filter (·.language = language)).findSome? fun r ↦ do
    let a ← r.parse? "A" flagNames
    let p ← r.parse? "P" flagNames
    if h : a ≠ p then some ⟨a, p, h⟩ else none

/-- The types a marker of a language codes across the book's examples. -/
def coExpressed (language marker : String) : List Kind :=
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

theorem rows_classified : ∀ row ∈ all, ∀ k ∈ row.parse? "alternation" kindNames,
    ∀ init ∈ paired "initial" row,
    k.Realize (construction init) (construction row) (row.parse? "new" slotNames) := by
  decide +kernel

theorem symmetrical_rows : ∀ row ∈ all, row.parse? "alternation" kindNames = some .symmetrical →
    ∀ init ∈ paired "initial" row, ∃ p ∈ row.parse? "pivot" slotNames,
    ∃ q ∈ init.parse? "pivot" slotNames, p ≠ q ∧ (construction row p).role.isSome := by
  decide +kernel

/-- In Mandinka (13) of chapter 1, 'repair' takes A and P, and 'forget' takes S and a
postpositional oblique. -/
theorem mandinka_roles :
    (construction ex_1_13a).Transitive ∧ ¬ (construction ex_1_13b).Transitive := by
  decide +kernel

/-- Russian (23) is obligatory A-coding, Avar (24) obligatory P-coding, and Basque (22),
with an ergative S beside a zero-flagged one, split-S and neither. -/
theorem alignment_rows :
    (∃ t ∈ flagging "russ1263",
      sFlags "russ1263" ≠ [] ∧ ObligatoryACoding t (sFlags "russ1263")) ∧
    (∃ t ∈ flagging "avar1256",
      sFlags "avar1256" ≠ [] ∧ ObligatoryPCoding t (sFlags "avar1256")) ∧
    ∃ t ∈ flagging "basq1248", SplitS t (sFlags "basq1248") := by
  decide +kernel

/-- The uncoded alternations of Bambara (2), (3) and Basque (4), which the book calls
P-ambitransitivity for Basque and describes in the same terms as the Tswana passive for
Bambara, are P-ambitransitivity: the initial P is the S of an intransitive construction and
the initial A is not a core term; Bambara's preserves participant structure, with the agent
an optional oblique, and Basque's does not. -/
theorem ambitransitivity_rows : ∀ row ∈ all,
    row.parse? "marking" codingNames = some .uncoded → ∀ init ∈ paired "transitive" row,
    (construction init).Transitive ∧ ¬ (construction row).Transitive ∧
    (∀ i, construction init i = .term .P → construction row i = .term .S) ∧
    (∀ i, construction init i = .term .A → ¬ (construction row i).Nuclear) ∧
    (PreservesStructure (construction init) (construction row) ↔ row.language = "bamb1269") := by
  decide +kernel

theorem coexpression :
    [Kind.passivization, .impersonalPassivization, .sDenucleativization] ⊆
      coExpressed "tswa1253" "-w" ∧
    [Kind.pApplicativization, .xApplicativization, .aNucleativization] ⊆
      coExpressed "tswa1253" "-ɛl" ∧
    [Kind.causativization, .portative] ⊆ coExpressed "tswa1253" "-is" ∧
    [Kind.causativization, .passivization] ⊆ coExpressed "koyr1240" "-ndi" := by
  decide +kernel

/-- In Tswana (38), passivizing the applicative of the causative is the composite of the three
alternations, through (38d) and (38e). -/
theorem stacking_tswana :
    Relation.Comp (Relation.Comp (ANucleativization · · 2) (PApplicativization · · 3))
      Passivization (construction ex_8_38a) (construction ex_8_38h) :=
  ⟨construction ex_8_38e, ⟨construction ex_8_38d, by decide +kernel, by decide +kernel⟩,
    by decide +kernel⟩

/-- Classical Nahuatl (39) forms the passive of the antipassive of the causative, through
(39b) and (39c). -/
theorem stacking_nahuatl :
    Relation.Comp (Relation.Comp (ANucleativization · · 2) Antipassivization) Passivization
      (construction ex_8_39a) (construction ex_8_39e) :=
  ⟨construction ex_8_39c, ⟨construction ex_8_39b, by decide +kernel, by decide +kernel⟩,
    by decide +kernel⟩

/-- Passivization need not yield an intransitive construction: the passive (38f) of the
double-P applicative (38c) is transitive, the applied P taking A coding. -/
theorem passive_transitive :
    Passivization (construction ex_8_38c) (construction ex_8_38f) ∧
    (construction ex_8_38f).Transitive := by
  decide +kernel

/-- The Balinese causative (51) nucleativizes a causer and denucleativizes the initial P,
the initial A taking the role of P: its valency is unchanged. -/
theorem causative_valency :
    (construction ex_8_51a).Nucleativizes (construction ex_8_51b) ∧
    (construction ex_8_51a).Denucleativizes (construction ex_8_51b) ∧
    (construction ex_8_51a).valency = (construction ex_8_51b).valency := by
  decide +kernel

/-- In the portative derivation of Tswana (3) of chapter 12, the woman who brought the food
came, and the food, which cannot come, is not the initial S. -/
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

theorem balinesePassive_passivization :
    Passivization balinesePassive.initial.construction balinesePassive.derived.construction := by
  decide

/-- The applicative and the causative relate the constructions of rows (50) and (51), which list
the participants in the same order. -/
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

/-- Balinese is symmetrical and binary although morphologically oriented, so symmetry in the
book's sense does not require equipollent marking (§8.1.7, §8.5.1). -/
theorem balinese_binary :
    balinese.IsSymmetrical ∧ ¬ balinese.IsMultiple ∧ ¬ balinese.IsEquipollent := by
  decide

/-- The Tagalog voices select the agent, the patient and obliques as pivot (§8.5.2). -/
theorem tagalog_pivotRoles : tagalog.symmetrical.pivotRoles = {some .A, some .P, some .X} := by
  decide

/-- Tagalog is a multiple symmetrical system, since an oblique may be the pivot (§8.5.2). -/
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
borderline case of §11.3.3 rests on that section's own wording. -/
theorem not_weakReciprocity_singleton (x : α) : ¬ WeakReciprocity R {x} := by
  rintro ⟨h, -⟩
  obtain ⟨y, hy, -, hxy⟩ := h x (Finset.mem_singleton_self x)
  exact hxy (Finset.mem_singleton.1 hy).symm

end Polysemy

end Creissels2024
