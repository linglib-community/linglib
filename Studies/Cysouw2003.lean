module

public import Linglib.Data.Examples.Cysouw2003
public import Linglib.Core.Order.UpperLower.Finset
public import Linglib.Syntax.Number.Basic
public import Linglib.Core.Data.Setoid.Basic
public import Linglib.Syntax.Person.Features
public import Linglib.Fragments.English.Pronouns
public import Linglib.Fragments.Tagalog.Pronouns
public import Linglib.Morphology.Paradigm.Morphome
public import Linglib.Core.Order.Concept

/-!
# Cysouw (2003): The paradigmatic structure of person marking

The paradigmatic structures of [cysouw-2003]. A person paradigm fills one slot with a closed set
of markers over eight referential categories, the three singular participants and the five
attested groups, and its structure is which categories share a morpheme: a setoid on
`Person.Category`, the syncretism of the paradigm's cell-to-form map. The book's kinds of
homophony, its types of the first person complex and its named structures are properties of that
setoid.

Two of the book's generalizations are implicational hierarchies, and each is a lower set of a
chain: horizontal homophony reaches the singular persons from the third upwards, and a paradigm
gives up its oppositions from the first person complex outwards. The order of asking about the
first person complex is the order of implication among the five types, and the order of giving
up oppositions the order of implication among the common paradigms the book prints. Every paradigm the book prints
is checked against its classification and against the hierarchies, with the exceptions the
book names.

## Main definitions

* `Cysouw2003.Clusivity`: the five common marking types of the first person complex, with their
  patterns `Clusivity.toPattern`, setoids on the four speaker-including cells.
* `Clusivity.Question`, `Pattern.profile`, `Pattern.RespectsHierarchy`: the four questions that
  tell the types apart, a pattern's positive answers, and the First Person Hierarchy.
* `Cysouw2003.Structure`: a paradigmatic structure, a setoid on `Person.Category`.

## Main results

* `Clusivity.ofAttribute_profile_le_iff`: the order of asking is the order of implication among
  the five types' answers.
* `Clusivity.rung_bijective`: the types are exactly the lower sets of the questions.
* `Clusivity.le_iff_profile_subset`: the hierarchy is the order of the profiles.
* `ofAttribute_givenUp_le_iff`: the Explicitness Hierarchy is the order of implication among the
  common and semi-common paradigms the book prints.

## Implementation notes

* The typology of the first person complex is finer than the WALS chapter on clusivity
  [cysouw-2013], which collapses minimal/augmented into inclusive/exclusive and whose "no 'we'"
  value is the absence of any first-person non-singular, not `noWe`.

* Cells the book draws as one block carry the same form string, so the syncretism of the
  forms is the book's block notation; fillers such as "(demonstratives)" are kept as printed.
* The named structures are kernels of the book's letter labellings, of which only the kernel
  matters.
* The book's Table 10.3 prints the descriptions of unified-we and only-inclusive swapped;
  Table 3.2 is followed.

## TODO

* Chapter 7's dual paradigms, the Dual Explicitness Hierarchy and the Dual Homophony
  Implication need cells for restricted groups.
* The zero implications of chapter 10 need zero marking read off the forms.

## References

* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
* [M. Cysouw, *Inclusive/Exclusive Distinction in Independent Pronouns* (2013)][cysouw-2013]
-/

@[expose] public section

namespace Cysouw2003

open Person Morphology

/-! ### Marking types of the first person complex -/

/-- The five common marking types of the first person complex, the common five of the fifteen
possible patterns. -/
inductive Clusivity where
  /-- No 'we' category has a specialized morpheme, as in the English inflection (Pb). -/
  | noWe
  /-- All three 'we' categories share one specialized morpheme, as English *we* (Pa). -/
  | unifiedWe
  /-- 1+2 and 1+2+3 share a specialized morpheme and 1+3 has none, as in Maká (Pc). -/
  | onlyInclusive
  /-- 1+2 and 1+2+3 share one specialized morpheme and 1+3 has another, as in Apalai (Pd). -/
  | inclusiveExclusive
  /-- All three 'we' categories have separate specialized morphemes, as Ilocano
  *ta* ~ *tayo* ~ *mi* (Pe). -/
  | minimalAugmented
  deriving DecidableEq, Repr, Fintype

namespace Clusivity

/-- The four cells of a pattern, the categories that include the speaker. The singular speaker
stands for every singular morpheme. -/
abbrev Cell := {c : Category // c.IncludesSpeaker}

namespace Cell

/-- The singular speaker. -/
def speaker : Cell := ⟨.speaker, by decide⟩

/-- The minimal inclusive 1+2. -/
def speakerAddressee : Cell := ⟨.speakerAddressee, by decide⟩

/-- The augmented inclusive 1+2+3. -/
def speakerAddresseeOthers : Cell := ⟨.speakerAddresseeOthers, by decide⟩

/-- The exclusive 1+3. -/
def speakerOthers : Cell := ⟨.speakerOthers, by decide⟩

end Cell

/-- A marking pattern of the first person complex, the letter notation as a setoid on the
four cells. -/
abbrev Pattern := Setoid Cell

/-- The four questions that classify the patterns, in the order the hierarchy asks them. -/
inductive Question where
  /-- Is there any specialized form for 'we'? -/
  | specializedWe
  /-- Is the inclusive specialized? -/
  | specializedInclusive
  /-- Is the exclusive specialized? -/
  | specializedExclusive
  /-- Is the inclusive split? -/
  | splitInclusive
  deriving DecidableEq, Repr, Fintype

namespace Question

/-- Position in the order of asking. -/
def rank : Question → Fin 4
  | .specializedWe => 0
  | .specializedInclusive => 1
  | .specializedExclusive => 2
  | .splitInclusive => 3

instance : LinearOrder Question := LinearOrder.lift' rank (by decide)

end Question

namespace Pattern

variable (r : Pattern)

/-- Some 'we' cell is not marked like the speaker. -/
def SpecializedWe : Prop := ∃ c : Cell, c.1.IsFirstPersonComplex ∧ ¬ r c Cell.speaker

/-- Both inclusive cells are marked neither like the speaker nor like the exclusive. -/
def SpecializedInclusive : Prop :=
  ∀ c : Cell, c.1.IsInclusive → ¬ r c Cell.speaker ∧ ¬ r c Cell.speakerOthers

/-- The exclusive is marked neither like the speaker nor like an inclusive cell. -/
def SpecializedExclusive : Prop :=
  ¬ r Cell.speakerOthers Cell.speaker ∧ ∀ c : Cell, c.1.IsInclusive → ¬ r Cell.speakerOthers c

/-- Minimal and augmented inclusive are marked apart and neither like the speaker. -/
def SplitInclusive : Prop :=
  ¬ r Cell.speakerAddressee Cell.speakerAddresseeOthers ∧
    ¬ r Cell.speakerAddressee Cell.speaker ∧ ¬ r Cell.speakerAddresseeOthers Cell.speaker

/-- The pattern answers the question positively. -/
def Answers : Question → Prop
  | .specializedWe => r.SpecializedWe
  | .specializedInclusive => r.SpecializedInclusive
  | .specializedExclusive => r.SpecializedExclusive
  | .splitInclusive => r.SplitInclusive

variable [DecidableRel (⇑r)]

instance : Decidable r.SpecializedWe := by unfold SpecializedWe; infer_instance
instance : Decidable r.SpecializedInclusive := by unfold SpecializedInclusive; infer_instance
instance : Decidable r.SpecializedExclusive := by unfold SpecializedExclusive; infer_instance
instance : Decidable r.SplitInclusive := by unfold SplitInclusive; infer_instance
instance : DecidablePred r.Answers := fun q ↦ by cases q <;> unfold Answers <;> infer_instance

/-- The questions the pattern answers positively. -/
def profile : Finset Question := Finset.univ.filter r.Answers

/-- The pattern fits the hierarchy when, read as conditions, each positive answer requires the
ones before it, so that the profile is an initial segment of the questions. -/
def RespectsHierarchy : Prop := IsLowerSet (↑r.profile : Set Question)

instance : Decidable r.RespectsHierarchy := inferInstanceAs (Decidable (IsLowerSet _))

end Pattern

/-- The letters as morpheme classes, `0` being the class of the singular speaker, the dash,
in which every category outside the first person complex is placed. -/
def labels : Clusivity → Category → ℕ
  | .unifiedWe, .speakerAddressee | .unifiedWe, .speakerAddresseeOthers
  | .unifiedWe, .speakerOthers => 1
  | .onlyInclusive, .speakerAddressee | .onlyInclusive, .speakerAddresseeOthers => 1
  | .inclusiveExclusive, .speakerAddressee | .inclusiveExclusive, .speakerAddresseeOthers => 1
  | .inclusiveExclusive, .speakerOthers => 2
  | .minimalAugmented, .speakerAddressee => 1
  | .minimalAugmented, .speakerAddresseeOthers => 2
  | .minimalAugmented, .speakerOthers => 3
  | _, _ => 0

/-- The type's pattern, its column of letters as a setoid on the four cells. -/
abbrev toPattern (t : Clusivity) : Pattern := Setoid.ker (t.labels ∘ Subtype.val)

theorem toPattern_injective : Function.Injective toPattern := by
  show ∀ s t : Clusivity, _ → _; decide +kernel

/-- The questions a type answers positively. -/
abbrev profile (t : Clusivity) : Finset Question := t.toPattern.profile

/-- The order of asking is the order of implication among the five types, one question coming
before another exactly when every type that answers the second positively answers the first so. -/
theorem ofAttribute_profile_le_iff {q q' : Question} :
    Concept.ofAttribute (fun (t : Clusivity) q ↦ q ∈ t.profile) q' ≤
      Concept.ofAttribute (fun (t : Clusivity) q ↦ q ∈ t.profile) q ↔ q ≤ q' := by
  rw [Concept.ofAttribute_le_ofAttribute_iff]
  revert q q'
  decide +kernel

theorem profile_isLowerSet (t : Clusivity) : IsLowerSet (↑t.profile : Set Question) :=
  Concept.antitone_ofAttribute_iff.1 (fun _ _ h ↦ ofAttribute_profile_le_iff.2 h) t

/-- The rung of a type is its profile, a lower set of the questions. -/
def rung (t : Clusivity) : {S : Finset Question // IsLowerSet (↑S : Set Question)} :=
  ⟨t.profile, t.profile_isLowerSet⟩

/-- The common types are exactly the rungs of the hierarchy, one for each lower set of the
questions. -/
theorem rung_bijective : Function.Bijective rung := by decide +kernel

/-- In the First Person Hierarchy a type precedes another when it answers fewer of the
questions, ordering no-we, unified-we, only-inclusive, inclusive/exclusive and
minimal/augmented. -/
instance : LinearOrder Clusivity := LinearOrder.lift' (fun t ↦ t.profile.card) (by decide +kernel)

/-- Along the hierarchy each type's profile extends its predecessor's. -/
theorem le_iff_profile_subset {s t : Clusivity} : s ≤ t ↔ s.profile ⊆ t.profile := by
  revert s t; decide +kernel

theorem profile_monotone : Monotone profile := fun _ _ ↦ le_iff_profile_subset.1

theorem onlyInclusive_profile :
    onlyInclusive.profile = {.specializedWe, .specializedInclusive} := by decide +kernel

end Clusivity

/-! ### Paradigmatic structures -/

/-- A paradigmatic structure records which of the eight referential categories share a
morpheme. -/
abbrev Structure := Setoid Category

/-- The singular categories are ordered by person prominence, the order in which horizontal
homophony reaches them, the third person first and the first person last. -/
abbrev Singular := {c : Category // c.IsSingular}

instance : LinearOrder Singular := LinearOrder.lift' (fun a ↦ a.1.person.prominence) (by decide)

/-- The marking of 'we', the columns of the book's Table 4.2, opposes minimal to augmented
inclusive, or inclusive to exclusive, or has one form. -/
inductive WeMarking where
  | minimalAugmented | inclusiveExclusive | unified
  deriving DecidableEq, Repr, Fintype

/-- The oppositions a paradigm gives up, in the order the Explicitness Hierarchy says it gives
them up, are the two inside the first person complex, then one between groups, then one between
singulars. -/
inductive Opposition where
  | minimalAugmented | inclusiveExclusive | group | singular
  deriving DecidableEq, Repr, Fintype

namespace Opposition

/-- Position in the order of giving up. -/
def rank : Opposition → Fin 4
  | .minimalAugmented => 0
  | .inclusiveExclusive => 1
  | .group => 2
  | .singular => 3

instance : LinearOrder Opposition := LinearOrder.lift' rank (by decide)

end Opposition

/-- The rows of the cognitive map, the stages of the hierarchical tree of number oppositions
(Figure 10.8). -/
inductive NumberStage where
  /-- N1 paradigms do not distinguish number. -/
  | N1
  /-- N2 paradigms consistently oppose singular to group marking. -/
  | N2
  /-- N3 paradigms also mark a restricted group, the dual or the inclusive trial of the
  unit-augmented paradigm. -/
  | N3
  /-- N4 paradigms also mark a small group, the paucal. -/
  | N4
  deriving DecidableEq, Repr

namespace Structure

variable (s : Structure)

/-! ### Kinds of homophony -/

/-- Two singular categories share a morpheme. -/
def SingularHomophony : Prop := ∃ a b : Singular, a ≠ b ∧ s a b

/-- A singular category shares a morpheme with a group. -/
def HorizontalHomophony : Prop := ∃ (a : Singular) (b : Category), b.IsGroup ∧ s a b

/-- The singular `a` shares its morpheme with a group of its own person, the first person with
the exclusive or the inclusive, the second with 2+3, the third with 3+3. -/
def HorizontalHomophonyAt (a : Singular) : Prop :=
  ∃ b : Category, b.IsGroup ∧ b.person.coarsen = a.1.person ∧ s a b

/-- A singular category shares a morpheme with a group of another person. -/
def DiagonalHomophony : Prop :=
  ∃ (a : Singular) (b : Category), b.IsGroup ∧ b.person.coarsen ≠ a.1.person ∧ s a b

/-- Two groups share a morpheme, homophony inside the first person complex not counted. -/
def VerticalHomophony : Prop :=
  ∃ a b : Category, a.IsGroup ∧ b.IsGroup ∧ a ≠ b ∧
    ¬ (a.IsFirstPersonComplex ∧ b.IsFirstPersonComplex) ∧ s a b

variable {s} in
theorem DiagonalHomophony.horizontalHomophony (h : s.DiagonalHomophony) :
    s.HorizontalHomophony :=
  let ⟨a, b, hb, _, hab⟩ := h; ⟨a, b, hb, hab⟩

/-- A category is specialized when it shares no morpheme with a singular one. -/
def Specialized (c : Category) : Prop := ∀ x : Singular, ¬ s c x

variable [DecidableRel (⇑s)]

instance : Decidable s.SingularHomophony := by unfold SingularHomophony; infer_instance
instance : Decidable s.HorizontalHomophony := by unfold HorizontalHomophony; infer_instance
instance (a : Singular) : Decidable (s.HorizontalHomophonyAt a) := by
  unfold HorizontalHomophonyAt; infer_instance
instance : Decidable s.DiagonalHomophony := by unfold DiagonalHomophony; infer_instance
instance : Decidable s.VerticalHomophony := by unfold VerticalHomophony; infer_instance
instance (c : Category) : Decidable (s.Specialized c) := by unfold Specialized; infer_instance

/-! ### The first person complex -/

/-- The book's letter for a speaker cell is its morpheme class when it is specialized, and the
dash, one for every singular morpheme, when it is not. -/
def letter (a : Clusivity.Cell) : Option (Quotient s) :=
  if s.Specialized a then some (Quotient.mk s a) else none

/-- The pattern of the first person complex, the kernel of the letters. -/
abbrev wePattern : Clusivity.Pattern := Setoid.ker s.letter

/-- The structure is of the common type `t`. -/
abbrev HasClusivity (t : Clusivity) : Prop := s.wePattern = t.toPattern

variable {s} in
theorem HasClusivity.unique {t t' : Clusivity} (h : s.HasClusivity t) (h' : s.HasClusivity t') :
    t = t' :=
  Clusivity.toPattern_injective (h.symm.trans h')

/-! ### The Horizontal Homophony Hierarchy -/

/-- The singular categories showing horizontal homophony. -/
def horizontalSingulars : Finset Singular := Finset.univ.filter s.HorizontalHomophonyAt

/-- Horizontal homophony in one person entails it in every less prominent person, so it
appears first in the third person, then the second, then the first; diagonal homophony is
among the exceptions. -/
def RespectsHorizontalHierarchy : Prop :=
  ¬ s.DiagonalHomophony ∧ IsLowerSet (↑s.horizontalSingulars : Set Singular)

instance : Decidable s.RespectsHorizontalHierarchy := by
  unfold RespectsHorizontalHierarchy; infer_instance

variable {s} in
theorem mem_horizontalSingulars_iff (h : s.RespectsHorizontalHierarchy) {a : Singular} :
    a ∈ s.horizontalSingulars ↔ ↑a ≤ s.horizontalSingulars.max :=
  h.2.mem_iff_le_max

/-- A paradigm without restricted groups is at N1 with no singular/group opposition at all, at
N2 with a consistent one, and at neither on the intermediate rungs of the horizontal
hierarchy. -/
def numberStage : Option NumberStage :=
  if ∀ a, s.HorizontalHomophonyAt a then some .N1
  else if ¬ s.HorizontalHomophony then some .N2 else none

/-! ### The Explicitness Hierarchy -/

/-- The marking of 'we' in a structure, by whether the cells differ, as chapter 4's division
into paradigms with and without an inclusive/exclusive opposition goes (the Ojibwe and Huave
prefixes, whose inclusive is a singular morpheme, are filed under the opposition), and as
any 1+2 against 1+2+3 difference counts as a minimal/augmented inclusive. -/
def weMarking : WeMarking :=
  if ¬ s .speakerAddressee .speakerAddresseeOthers then .minimalAugmented
  else if ¬ s .speakerAddressee .speakerOthers then .inclusiveExclusive else .unified

/-- The structure has given up the opposition of minimal to augmented inclusive unless 'we' is
marked so, of inclusive to exclusive when 'we' is one form, one between groups when two groups
share a morpheme, and one between singulars when two singulars do. -/
def GivesUp : Opposition → Prop
  | .minimalAugmented => s.weMarking ≠ .minimalAugmented
  | .inclusiveExclusive => s.weMarking = .unified
  | .group => s.VerticalHomophony
  | .singular => s.SingularHomophony

instance : DecidablePred s.GivesUp := fun o ↦ by cases o <;> unfold GivesUp <;> infer_instance

/-- The oppositions the structure has given up. -/
def givenUp : Finset Opposition := Finset.univ.filter s.GivesUp

/-- As a constraint on which oppositions a paradigm may give up, the hierarchy requires those
given up to form an initial segment of the order, so singulars merge only where groups already
merge, and groups only once 'we' is one form. -/
def RespectsExplicitnessHierarchy : Prop := IsLowerSet (↑s.givenUp : Set Opposition)

instance : Decidable s.RespectsExplicitnessHierarchy := inferInstanceAs (Decidable (IsLowerSet _))

/-- The rung of a structure on the hierarchy is the last opposition it has given up, the
book's stages of person differentiation P4 (none given up), P3, P2, P1 and P0 (a singular
one). -/
def explicitness : WithBot Opposition := s.givenUp.max

variable {s} in
theorem mem_givenUp_iff (h : s.RespectsExplicitnessHierarchy) {o : Opposition} :
    o ∈ s.givenUp ↔ ↑o ≤ s.explicitness :=
  h.mem_iff_le_max

end Structure

/-! ### The rare patterns of the first person complex -/

/-- The five rare attested patterns of the first person complex. -/
inductive RarePattern where
  /-- A morpheme for 1+2 and another for 1+2+3 and 1+3 together (Bardi, Kunimaipa, Tiwi). -/
  | pf
  /-- A morpheme for 1+2+3 and another for 1+2 and 1+3 together (Yaouré, Gooniyandi). -/
  | pg
  /-- Minimal and augmented inclusive marked apart, the exclusive by a singular morpheme
  (Tiwi). -/
  | ph
  /-- 1+2 marked by a singular morpheme, 1+2+3 and 1+3 together (Kunimaipa). -/
  | pi
  /-- The inclusive marked by a singular morpheme, the exclusive by its own (Binandere). -/
  | pj
  deriving DecidableEq, Repr, Fintype

namespace RarePattern

/-- The book's letters as morpheme classes, `0` the singular class. -/
def labels : RarePattern → Category → ℕ
  | .pf, .speakerAddressee => 1 | .pf, .speakerAddresseeOthers => 2 | .pf, .speakerOthers => 2
  | .pg, .speakerAddressee => 1 | .pg, .speakerAddresseeOthers => 2 | .pg, .speakerOthers => 1
  | .ph, .speakerAddressee => 1 | .ph, .speakerAddresseeOthers => 2
  | .pi, .speakerAddresseeOthers => 1 | .pi, .speakerOthers => 1
  | .pj, .speakerOthers => 1
  | _, _ => 0

/-- The rare pattern as a setoid on the four cells. -/
abbrev pattern (q : RarePattern) : Clusivity.Pattern := Setoid.ker (q.labels ∘ Subtype.val)

theorem pattern_injective : Function.Injective pattern := by
  show ∀ q q' : RarePattern, _ → _; decide +kernel

theorem pattern_ne (q : RarePattern) (t : Clusivity) : q.pattern ≠ t.toPattern := by
  revert q t; decide +kernel

end RarePattern

/-! ### The named structures of chapter 4 -/

/-- Chapter 4 names eight common and five semi-common structures after an exemplar. -/
inductive Kind where
  | latin | sinhalese | berik | maricopa
  | maranao | mandara | tupiGuarani | kwakiutl | sierraPopoluca
  | slave | nezPerce | kombai | omie
  deriving DecidableEq, Repr, Fintype

namespace Kind

/-- Morpheme classes of each named structure; the wildcard covers the three 'we' cells. -/
def labels : Kind → Category → ℕ
  | .latin => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .addresseeOthers => 4 | .others => 5 | _ => 3
  | .sinhalese => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .addresseeOthers => 4 | .others => 2 | _ => 3
  | .berik => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .addresseeOthers => 1 | .others => 2 | _ => 3
  | .maricopa => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .addresseeOthers => 1 | .others => 2 | _ => 0
  | .maranao => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .speakerAddressee => 3 | .speakerAddresseeOthers => 4 | .speakerOthers => 5
    | .addresseeOthers => 6 | .others => 7
  | .mandara => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .speakerOthers => 4 | .addresseeOthers => 5 | .others => 6 | _ => 3
  | .tupiGuarani => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .speakerOthers => 4 | .addresseeOthers => 5 | .others => 2 | _ => 3
  | .kwakiutl => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .speakerOthers => 4 | .addresseeOthers => 1 | .others => 2 | _ => 3
  | .sierraPopoluca => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .speakerOthers => 0 | .addresseeOthers => 1 | .others => 2 | _ => 3
  | .slave => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .addresseeOthers => 3 | .others => 4 | _ => 3
  | .nezPerce => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .addresseeOthers => 4 | .others => 4 | _ => 3
  | .kombai => fun
    | .speaker => 0 | .addressee => 1 | .other => 1
    | .addresseeOthers => 3 | .others => 3 | _ => 2
  | .omie => fun
    | .speaker => 0 | .addressee => 1 | .other => 2
    | .addresseeOthers => 4 | .others => 3 | _ => 3

/-- The names the rows use. -/
def names : List (String × Kind) :=
  [("Latin", .latin), ("Sinhalese", .sinhalese), ("Berik", .berik), ("Maricopa", .maricopa),
   ("Maranao", .maranao), ("Mandara", .mandara), ("Tupí-Guaraní", .tupiGuarani),
   ("Kwakiutl", .kwakiutl), ("Sierra Popoluca", .sierraPopoluca), ("Slave", .slave),
   ("Nez Perce", .nezPerce), ("Kombai", .kombai), ("Omie", .omie)]

/-- The paradigmatic structure of the named kind. -/
abbrev pattern (k : Kind) : Structure := Setoid.ker k.labels

/-- The book files each named structure's first person complex by type; the Maricopa type has
no 'we', the Sierra Popoluca type only an inclusive, the Maranao type a
minimal/augmented one, the other types with an inclusive/exclusive opposition are
inclusive/exclusive and the rest unified. -/
def clusivity : Kind → Clusivity
  | .maricopa => .noWe
  | .sierraPopoluca => .onlyInclusive
  | .maranao => .minimalAugmented
  | .mandara | .tupiGuarani | .kwakiutl => .inclusiveExclusive
  | .latin | .sinhalese | .berik | .slave | .nezPerce | .kombai | .omie => .unifiedWe

theorem pattern_injective : Function.Injective pattern := by
  show ∀ k l : Kind, _ → _; decide +kernel

theorem hasClusivity_pattern (k : Kind) : k.pattern.HasClusivity k.clusivity := by
  revert k; decide +kernel

theorem respectsHorizontalHierarchy_pattern (k : Kind) :
    k.pattern.RespectsHorizontalHierarchy := by
  revert k; decide +kernel

theorem horizontalSingulars_inclusiveExclusive :
    mandara.pattern.horizontalSingulars ⊂ tupiGuarani.pattern.horizontalSingulars ∧
    tupiGuarani.pattern.horizontalSingulars ⊂ kwakiutl.pattern.horizontalSingulars ∧
    kwakiutl.pattern.horizontalSingulars ⊂ sierraPopoluca.pattern.horizontalSingulars := by
  decide +kernel

theorem horizontalSingulars_unified :
    latin.pattern.horizontalSingulars ⊂ sinhalese.pattern.horizontalSingulars ∧
    sinhalese.pattern.horizontalSingulars ⊂ berik.pattern.horizontalSingulars ∧
    berik.pattern.horizontalSingulars ⊂ maricopa.pattern.horizontalSingulars := by
  decide +kernel

theorem respectsExplicitnessHierarchy_pattern (k : Kind) :
    k.pattern.RespectsExplicitnessHierarchy := by
  revert k; decide +kernel

theorem explicitness_pattern :
    slave.pattern.explicitness = ↑Opposition.group ∧
    latin.pattern.explicitness = ↑Opposition.inclusiveExclusive ∧
    maricopa.pattern.explicitness = ↑Opposition.inclusiveExclusive ∧
    mandara.pattern.explicitness = ↑Opposition.minimalAugmented ∧
    sierraPopoluca.pattern.explicitness = ↑Opposition.minimalAugmented ∧
    maranao.pattern.explicitness = ⊥ := by
  decide +kernel

theorem numberStage_pattern :
    maricopa.pattern.numberStage = some .N1 ∧ sierraPopoluca.pattern.numberStage = some .N1 ∧
    (∀ k ∈ [slave, latin, mandara, maranao], k.pattern.numberStage = some .N2) ∧
    sinhalese.pattern.numberStage = none := by
  decide +kernel

end Kind

/-! ### The paradigms of chapters 3 and 4 -/

/-- Morphological status of a paradigm. -/
inductive Marking where
  | independent | inflectional
  deriving DecidableEq, Repr

/-- Chapter 4's frequency classes. -/
inductive Ubiquity where
  | common | semiCommon | rare
  deriving DecidableEq, Repr

/-- A paradigm the book prints, its eight forms and the book's classification of it. -/
structure Row where
  /-- The example id. -/
  id : String
  /-- The form of each cell, block by block. -/
  forms : Category → String
  /-- The chapter printing it. -/
  chapter : ℕ
  /-- Independent or inflectional, where the caption says. -/
  marking : Option Marking
  /-- The named type the book files it under. -/
  kind : Option Kind
  /-- Common, semi-common or rare. -/
  ubiquity : Ubiquity
  /-- The rare 'we' pattern it illustrates. -/
  rare : Option RarePattern

namespace Row

/-- The paradigmatic structure of the row. -/
abbrev syncretism (r : Row) : Structure := Setoid.ker r.forms

/-- The row's pattern of the first person complex. -/
abbrev wePattern (r : Row) : Clusivity.Pattern := r.syncretism.wePattern

/-- A feature that may be absent but, when present, must parse. -/
def optional? {α : Type*} (e : Datum) (key : String)
    (table : List (String × α)) : Option (Option α) :=
  match e.feature? key with
  | none => some none
  | some s => (table.lookup s).map some

/-- The row of an example. -/
def ofDatum? (e : Datum) : Option Row := do
  let s1 ← e.feature? "1"
  let s2 ← e.feature? "2"
  let s3 ← e.feature? "3"
  let minIncl ← e.feature? "1+2"
  let augIncl ← e.feature? "1+2+3"
  let excl ← e.feature? "1+3"
  let secondGrp ← e.feature? "2+3"
  let thirdGrp ← e.feature? "3+3"
  let chapter ← e.nat? "chapter"
  let ubiquity ← e.parse? "ubiquity"
    [("common", .common), ("semi-common", .semiCommon), ("rare", .rare)]
  let marking ← optional? e "marking"
    [("independent", .independent), ("inflectional", .inflectional)]
  let kind ← optional? e "kind" Kind.names
  let rare ← optional? e "fpc" [("Pf", .pf), ("Pg", .pg), ("Ph", .ph), ("Pi", .pi), ("Pj", .pj)]
  pure { id := e.id, chapter, ubiquity, marking, kind, rare
         forms := fun
           | .speaker => s1 | .addressee => s2 | .other => s3
           | .speakerAddressee => minIncl | .speakerAddresseeOthers => augIncl
           | .speakerOthers => excl | .addresseeOthers => secondGrp | .others => thirdGrp }

theorem isSome_ofDatum : ∀ e ∈ Examples.all, (ofDatum? e).isSome := by decide

end Row

/-- The printed paradigms. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum?

theorem rows_kind : ∀ r ∈ rows, ∀ k, r.kind = some k → r.syncretism = k.pattern := by
  decide +kernel

theorem rows_rare : ∀ r ∈ rows, ∀ q, r.rare = some q → r.wePattern = q.pattern := by
  decide +kernel

theorem rows_hasClusivity :
    ∀ r ∈ rows, r.chapter = 4 → ∃ t, r.syncretism.HasClusivity t := by
  decide +kernel

theorem rows_specializedInclusive_of_specializedExclusive :
    ∀ r ∈ rows, r.rare ≠ some .pj →
      r.wePattern.SpecializedExclusive → r.wePattern.SpecializedInclusive := by
  decide +kernel

theorem binandere :
    ∃ r ∈ rows, r.rare = some .pj ∧ r.wePattern.SpecializedExclusive ∧
      ¬ r.wePattern.SpecializedInclusive := by
  decide +kernel

theorem rows_specializedExclusive_of_splitInclusive :
    ∀ r ∈ rows, (r.rare = none ∨ r.rare = some .pi ∨ r.rare = some .pj) →
      r.wePattern.SplitInclusive → r.wePattern.SpecializedExclusive := by
  decide +kernel

theorem rows_splitInclusive_not_specializedExclusive :
    ∀ r ∈ rows, (r.rare = some .pf ∨ r.rare = some .pg ∨ r.rare = some .ph) →
      r.wePattern.SplitInclusive ∧ ¬ r.wePattern.SpecializedExclusive := by
  decide +kernel

theorem english_inflection_noWe :
    ∃ r ∈ rows, r.id = "cysouw2003_4_68" ∧ r.syncretism.HasClusivity .noWe := by
  decide +kernel

theorem rows_inflectional_of_singularHomophony :
    ∀ r ∈ rows, r.syncretism.SingularHomophony → r.marking = some .inflectional := by
  decide +kernel

theorem rows_rare_of_not_respectsHorizontalHierarchy :
    ∀ r ∈ rows, ¬ r.syncretism.RespectsHorizontalHierarchy → r.ubiquity = .rare := by
  decide +kernel

-- Table 4.2
theorem rows_respectsHorizontalHierarchy_of_minimalAugmented :
    ∀ r ∈ rows, r.chapter = 4 → r.syncretism.weMarking = .minimalAugmented →
      r.syncretism.RespectsHorizontalHierarchy := by
  decide +kernel

-- Table 4.2
theorem rows_unified_of_singularHomophony :
    ∀ r ∈ rows, r.chapter = 4 → r.syncretism.SingularHomophony →
      r.syncretism.weMarking = .unified := by
  decide +kernel

theorem rows_rare_of_not_respectsExplicitnessHierarchy :
    ∀ r ∈ rows, ¬ r.syncretism.RespectsExplicitnessHierarchy → r.ubiquity = .rare := by
  decide +kernel

/-- The Explicitness Hierarchy is the order of implication among the common and semi-common
printed paradigms, one opposition being given up before another exactly when every such paradigm
that gives up the second gives up the first. With the rare paradigms included, three of its steps
fail. -/
theorem ofAttribute_givenUp_le_iff {o o' : Opposition} :
    Concept.ofAttribute
        (fun (r : {r // r ∈ rows.filter (·.ubiquity ≠ .rare)}) ↦ r.1.syncretism.GivesUp) o' ≤
      Concept.ofAttribute
        (fun (r : {r // r ∈ rows.filter (·.ubiquity ≠ .rare)}) ↦ r.1.syncretism.GivesUp) o ↔
      o ≤ o' := by
  have h : ∀ o o' : Opposition, (∀ r ∈ rows.filter (·.ubiquity ≠ .rare),
      r.syncretism.GivesUp o' → r.syncretism.GivesUp o) ↔ o ≤ o' := by
    decide +kernel
  rw [Concept.ofAttribute_le_ofAttribute_iff, ← h o o']
  exact ⟨fun H r hr ↦ H (x := ⟨r, hr⟩), fun H ⦃x⦄ ↦ H x.1 x.2⟩

theorem rows_rare_of_singularHomophony_without_vertical :
    ∀ r ∈ rows, r.syncretism.SingularHomophony → ¬ r.syncretism.VerticalHomophony →
      r.ubiquity = .rare := by
  decide +kernel

theorem rows_rare_of_verticalHomophony_inclusiveExclusive :
    ∀ r ∈ rows, r.syncretism.VerticalHomophony → r.syncretism.weMarking ≠ .unified →
      r.ubiquity = .rare := by
  decide +kernel

theorem explicitness_rungs :
    ∃ waskia ∈ rows, ∃ una ∈ rows,
      waskia.id = "cysouw2003_4_66" ∧ una.id = "cysouw2003_4_64" ∧
      waskia.syncretism.explicitness = ↑Opposition.singular ∧
      una.syncretism.explicitness = ↑Opposition.group ∧
      Kind.latin.pattern.explicitness = ↑Opposition.inclusiveExclusive ∧
      Kind.mandara.pattern.explicitness = ↑Opposition.minimalAugmented ∧
      Kind.maranao.pattern.explicitness = ⊥ := by
  decide +kernel

/-! ### Two paradigms from the Fragments -/

/-- The English subject forms by referential category are the paradigm of the fragment's
nominative pronouns. -/
def englishSubject : Category → Finset String :=
  PersonalPronoun.paradigm (English.Pronouns.pronouns.filter (.nom ∈ ·.cases))

theorem english_pronouns :
    ∃ r ∈ rows, r.id = "cysouw2003_4_19" ∧ Setoid.ker englishSubject = r.syncretism := by
  decide +kernel

theorem english_not_respectsHorizontalHierarchy :
    ¬ Structure.RespectsHorizontalHierarchy (Setoid.ker englishSubject) := by decide +kernel

theorem tagalog_maranao : Setoid.ker Tagalog.ang = Kind.maranao.pattern := by decide +kernel

theorem tagalog_minimalAugmented :
    Structure.HasClusivity (Setoid.ker Tagalog.ang) .minimalAugmented := by
  decide +kernel

end Cysouw2003
