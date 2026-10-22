module

public import Studies.Chomsky2013
public import Studies.Collins2005
public import Linglib.Data.Examples.Boskovic2018
public import Linglib.Syntax.Minimalist.Locality.Transfer

/-!
# Bošković (2018): On movement out of moved elements, labels, and phases

Movement to the edge of a phase on the way out of it creates a specifier that agrees with nothing,
which leaves the phase unlabeled until the specifier moves on, and an unlabeled element cannot
move, the Unlabeled Immobility Condition. Since the cycle and the PIC make an element leave a
phase by its edge before the phase moves, the ban on movement out of moved elements follows
(`ex17`), in a revised form: what is generated at the edge, or moves there to share a feature,
leaves the phase labeled and free to move, and can then be extracted from it (`ex25a`, `ex42a`).
Remnant movement is unaffected (`ex20`), a verb-second clause, whose specifier agrees with
nothing, cannot move though nothing moves out of it (`ex22`), and Collins's smuggling passive,
which moves a non-phase, obeys the condition while violating the traditional ban (`ex58`).

## Implementation notes

* Labeling is that of Chomsky (2013): the heads minimal search finds, roots aside, label when
  there is one, or when they share a feature. The features shared are the paper's: the concord of
  a Serbo-Croatian possessive adjective with its noun, and the R-feature of a Dutch r-pronoun with
  its preposition. Successive-cyclic and verb-second specifiers share none.
* The phases are Chomsky's CP, vP and DP, and in Serbo-Croatian, which lacks DP, the noun phrase.
  Transfer seals the complement of a phase head once its phase is complete.
* Clauses are cut down to the heads each example needs, verbs in their base positions; the word
  orders of the German, Serbo-Croatian and Dutch examples are not modelled.

## TODO

* Phase Mobility (12), only phases move, from which the paper deduces the condition and by which
  Appendix A rules out Collins's passive, needs the phases of Bošković (2014), the highest
  projection of each extended projection.
* Left-branch and intensifier extraction (28)–(30), quantifier float, the Adjunct Condition, and
  the Coordinate Structure Constraint of Appendix B.

## References

* [boskovic-2018]
* [chomsky-2013]
* [collins-2005]
-/

@[expose] public section

namespace Boskovic2018

open Core.Order Minimalist Minimalist.LinearizedSyntacticObject
open Chomsky2013 (tok nominal IsRoot)

/-! ### Labeling, phases and the PIC -/

/-- The features specifier and head share in the paper's examples. -/
inductive Feature
  | phi | r
  deriving DecidableEq, Fintype

/-- The Dutch r-pronouns, which precede their preposition. -/
def rPronouns : List String := ["er", "daar", "hier", "waar"]

/-- The feature sharing the paper assumes: a possessive adjective agrees with the noun in
φ-features and case, and an r-pronoun shares the R-feature with its preposition. -/
def Shares : Feature → LexicalItem.Token → LexicalItem.Token → Prop
  | .phi, a, b => a.item.cat = .a ∧ b.item.cat = .n
  | .r, a, b => a.item.cat = .D ∧ a.item.phonForm ∈ rPronouns ∧ b.item.cat = .P

instance : ∀ f, DecidableRel (Shares f)
  | .phi => fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))
  | .r => fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Two heads agree in a feature when one shares it with the other. -/
abbrev Agreed (f : Feature) : LexicalItem.Token → LexicalItem.Token → Prop :=
  Relation.SymmGen (Shares f)

/-- The heads minimal search finds that can label `x`: roots are too weak to label. -/
def labelers (t : LinearizedSyntacticObject) (x : SyntacticObject) : Finset LexicalItem.Token :=
  (t.labels x).filter (¬ IsRoot ·)

/-- Labeling in the paper, that of [chomsky-2013]: by the one head that can label, or by a feature
the heads that can label share, when none of them is a daughter. -/
def IsLabeled (t : LinearizedSyntacticObject) (x : SyntacticObject) : Prop :=
  (∃ a ∈ labelers t x, labelers t x = {a}) ∨
    ((labelers t x).Nontrivial ∧ (∀ a ∈ labelers t x, ¬ SyntacticObject.ImmediatelyContains x ↑a) ∧
      ∃ f, (labelers t x : Set LexicalItem.Token).Pairwise (Agreed f))

instance (t : LinearizedSyntacticObject) (x : SyntacticObject) : Decidable (IsLabeled t x) :=
  haveI : Decidable (labelers t x).Nontrivial :=
    decidable_of_iff _ Finset.one_lt_card_iff_nontrivial
  inferInstanceAs (Decidable (_ ∨ _))

/-- The phase heads of a language with articles: C, v and D. -/
def IsPhaseHead (a : LexicalItem.Token) : Prop := a.item.cat ∈ [.C, .v, .D]

instance : DecidablePred IsPhaseHead := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

/-- The phase heads of Serbo-Croatian, which lacks DP: C, v and the nominalizer. -/
def IsPhaseHeadNP (a : LexicalItem.Token) : Prop := a.item.cat ∈ [.C, .v, .n]

instance : DecidablePred IsPhaseHeadNP := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

/-- The PIC on a derivation: no link of a chain in the object it derives leaves the complement of
a phase head, transferred once its phase is complete. -/
def ObeysPic (Φ : LexicalItem.Token → Prop) [DecidablePred Φ] (d : Derivation) : Prop :=
  ∀ t ∈ d.externalize?, ∀ x ∈ tokenList t.val,
    ¬ LinkLeaves t x.2 (sealed (occurrencesWith t Φ).toFinset (complementDomain t ∅) (Pic1 t))

instance (Φ : LexicalItem.Token → Prop) [DecidablePred Φ] (d : Derivation) :
    Decidable (ObeysPic Φ d) := by
  unfold ObeysPic; infer_instance

/-- A derivation converges when it obeys the PIC and moves only labeled elements. -/
def Converges (Φ : LexicalItem.Token → Prop) [DecidablePred Φ] (d : Derivation) : Prop :=
  d.ObeysUIC IsLabeled ∧ ObeysPic Φ d

instance (Φ : LexicalItem.Token → Prop) [DecidablePred Φ] (d : Derivation) :
    Decidable (Converges Φ d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Extraction from a subject (16)–(18) -/

/-- The determiner of *who*. -/
def whoD := tok 200 .D "who" (wh := true) (sel := [.n])
/-- *who*. -/
def who : LinearizedSyntacticObject := nominal whoD (tok 201 .n (sel := [.N])) (tok 202 .N)
def ofP := tok 203 .P "of" (sel := [.D])
def friends := tok 204 .N "friends" (sel := [.P])
def friendsN := tok 205 .n (sel := [.N])
def subjD := tok 206 .D (sel := [.n])
def hireV := tok 207 .v (sel := [.V])
def hired := tok 208 .V "hired" (sel := [.D])
/-- *Mary*. -/
def mary : LinearizedSyntacticObject :=
  nominal (tok 209 .D (sel := [.n])) (tok 210 .n (sel := [.N])) (tok 211 .N "Mary")
def tI := tok 212 .T (sel := [.v])
def cQ := tok 213 .C (wh := true) (sel := [.T])

/-- The subject *friends of* `x`. -/
def subject (x : LinearizedSyntacticObject) : LinearizedSyntacticObject :=
  subjD * (friendsN * (friends * (ofP * x)))

/-- *hired Mary*, built in its own workspace. -/
def hiredMary : LinearizedSyntacticObject := hireV * (hired * mary)

/-- The two ways *who* can leave the subject (16): by the subject's edge while the subject is in
situ, the cycle requiring the step before the subject moves, or directly from the moved subject. -/
inductive Route
  | edge | direct
  deriving DecidableEq, Fintype

/-- The derivation of (17) along a route: the subject built around *who*, merged with *hired
Mary*, raised over I, and *who* raised over the interrogative C. -/
def subextraction (r : Route) : Derivation :=
  ⟨tok 202 .N, [.em .left (tok 201 .n (sel := [.N])), .em .left whoD, .em .left ofP,
    .em .left friends, .em .left friendsN, .em .left subjD] ++
    (match r with | .edge => [.im who] | .direct => []) ++
    [.em .right hiredMary, .em .left tI,
      .im (match r with
        | .edge => (who * subject (.traceOf whoD) : LinearizedSyntacticObject)
        | .direct => subject who),
      .em .left cQ, .im who]⟩

/-- Both routes derive the embedded clause of (17). -/
theorem subextraction_surfacePhon (r : Route) :
    (subextraction r).surfacePhon = ["who", "friends", "of", "hired", "Mary"] := by
  cases r <;> decide +kernel

/-- (17): by the edge, *who* leaves the subject unlabeled, so that it cannot move; directly, it
crosses the subject's phase from its interior. No derivation converges: the ban on movement out of
moved elements, deduced, though both routes move *who* out of a moved subject. -/
theorem ex17 :
    ¬ (subextraction .edge).ObeysUIC IsLabeled ∧ ObeysPic IsPhaseHead (subextraction .edge) ∧
      ¬ ObeysPic IsPhaseHead (subextraction .direct) ∧
      (∀ r, ¬ (subextraction r).ObeysFreezing) ∧
      (Examples.ex17.judgment = .acceptable ↔ ∃ r, Converges IsPhaseHead (subextraction r)) := by
  decide +kernel

/-! ### Remnant movement (20)–(21) -/

def janeD := tok 220 .D (sel := [.n])
/-- *Jane*. -/
def jane : LinearizedSyntacticObject :=
  nominal janeD (tok 221 .n (sel := [.N])) (tok 222 .N "Jane")
def kiss := tok 223 .V "kiss" (sel := [.D])
def kissV := tok 224 .v (sel := [.V])
def did := tok 225 .T "did" (sel := [.v])

/-- (20): the subject raised out of vP, and the remnant vP fronted. -/
def remnantFronting : Derivation :=
  ⟨tok 211 .N "Mary", [.em .left (tok 210 .n (sel := [.N])), .em .left (tok 209 .D (sel := [.n])),
    .em .left kiss, .em .left kissV, .em .left jane, .em .left did, .im jane,
    .im (.traceOf janeD * (kissV * (kiss * mary)) : LinearizedSyntacticObject)]⟩

/-- (20): vP, its subject gone, is labeled by v and moves; remnant movement obeys even the
traditional ban. -/
theorem ex20 : remnantFronting.surfacePhon = ["kiss", "Mary", "Jane", "did"] ∧
    remnantFronting.ObeysFreezing ∧
    (Examples.ex20.judgment = .acceptable ↔ Converges IsPhaseHead remnantFronting) := by
  decide +kernel

/-! ### Verb-second clauses (22) -/

def peterD := tok 230 .D "den" (sel := [.n])
/-- *den Peter*. -/
def peter : LinearizedSyntacticObject :=
  nominal peterD (tok 231 .n (sel := [.N])) (tok 232 .N "Peter")
def mag := tok 233 .V "mag" (sel := [.D])
/-- *niemand*. -/
def niemand : LinearizedSyntacticObject :=
  nominal (tok 234 .D "niemand" (sel := [.n])) (tok 235 .n (sel := [.N])) (tok 236 .N)
def cV2 := tok 237 .C (sel := [.V])

/-- The verb-second clause *den Peter mag niemand*, the object raised to its specifier. -/
def v2Clause : LinearizedSyntacticObject := peter * (cV2 * (niemand * (mag * .traceOf peterD)))

/-- The steps that build the verb-second clause. -/
def v2Steps : List Step :=
  [.em .left (tok 231 .n (sel := [.N])), .em .left peterD, .em .left mag, .em .left niemand,
    .em .left cV2, .im peter]

def bekannt := tok 238 .A "bekannt" (sel := [.C])
def ist := tok 239 .T "ist" (sel := [.A])
def sagte := tok 240 .V "sagte" (sel := [.C])

/-- (22a): the verb-second clause raised to Spec,IP. -/
def v2Moved : Derivation :=
  ⟨tok 232 .N "Peter", v2Steps ++ [.em .left bekannt, .em .left ist, .im v2Clause]⟩

/-- (22c): the verb-second clause in situ, the complement of *sagte*. -/
def v2InSitu : Derivation := ⟨tok 232 .N "Peter", v2Steps ++ [.em .left sagte]⟩

/-- (22): a verb-second clause, its specifier sharing no feature with C, is unlabeled and cannot
move, though nothing moves out of it. -/
theorem ex22 : v2Moved.ObeysFreezing ∧
    (Examples.ex22a.judgment = .acceptable ↔ Converges IsPhaseHead v2Moved) ∧
    (Examples.ex22c.judgment = .acceptable ↔ Converges IsPhaseHead v2InSitu) := by
  decide +kernel

/-! ### Base-generated specifiers: Serbo-Croatian possessors (24)–(27) -/

def ovA := tok 250 .a "Jovanovu" (sel := [.N])
/-- The possessive adjective *Jovanovu* 'John's'. -/
def possessor : LinearizedSyntacticObject := ovA * tok 251 .N
def slikaN := tok 252 .n (sel := [.N])
def slika := tok 253 .N "sliku"
/-- The object *Jovanovu sliku* 'John's picture', the possessor at its edge. -/
def object : LinearizedSyntacticObject := possessor * (slikaN * slika)
def vidio := tok 254 .V "vidio" (sel := [.n])
def je := tok 255 .T "je" (sel := [.V])

/-- (25a), derived as (26): the object fronted, and the possessor extracted from it. -/
def possessorExtraction : Derivation :=
  ⟨slika, [.em .left slikaN, .em .left possessor, .em .left vidio, .em .left je, .im object,
    .im possessor]⟩

/-- (25a): the possessor agrees with the noun, so the object it is generated at the edge of is
labeled and moves, and the possessor then leaves it from the edge. The derivation converges though
it violates the traditional ban. -/
theorem ex25a : ¬ possessorExtraction.ObeysFreezing ∧
    (Examples.ex25a.judgment = .acceptable ↔ Converges IsPhaseHeadNP possessorExtraction) := by
  decide +kernel

/-! ### R-pronouns (37)–(42) -/

def waarD := tok 260 .D "waar" (sel := [.n])
/-- *waar*. -/
def waar : LinearizedSyntacticObject := nominal waarD (tok 261 .n (sel := [.N])) (tok 262 .N)
def mee := tok 263 .P "mee" (sel := [.D])
/-- *waar mee*, the r-pronoun in Spec,PP. -/
def pp : LinearizedSyntacticObject := waar * (mee * .traceOf waarD)
/-- *de vis snijden*. -/
def snijden : LinearizedSyntacticObject :=
  tok 264 .V "snijden" (sel := [.D]) *
    nominal (tok 265 .D "de" (sel := [.n])) (tok 266 .n (sel := [.N])) (tok 267 .N "vis")
def zou := tok 268 .T "zou" (sel := [.V])
def dat := tok 269 .C "dat" (sel := [.T])
def gedacht := tok 270 .V "gedacht" (sel := [.C])
def had := tok 271 .T "had" (sel := [.V])
def cWh := tok 272 .C (wh := true) (sel := [.T])

/-- (42a): *waar* raised to Spec,PP, the PP raised out of the embedded clause through its edge,
and *waar* extracted from it. -/
def rPronounExtraction : Derivation :=
  ⟨tok 262 .N, [.em .left (tok 261 .n (sel := [.N])), .em .left waarD, .em .left mee, .im waar,
    .em .right snijden, .em .left zou, .em .left dat, .im pp, .em .left gedacht, .im pp,
    .em .left had, .em .left cWh, .im waar]⟩

/-- (42a): *waar* moves to Spec,PP to share the R-feature, not for successive cyclicity, so the PP
is labeled and moves, and *waar* then leaves it. -/
theorem ex42a : ¬ rPronounExtraction.ObeysFreezing ∧
    (Examples.ex42a.judgment = .acceptable ↔ Converges IsPhaseHead rPronounExtraction) := by
  decide +kernel

/-! ### Smuggling (Appendix A) -/

/-- (58): in [collins-2005]'s smuggling passive PartP, labeled by its head, moves, and the object
raises out of it, which the condition allows and the traditional ban excludes. -/
theorem ex58 : Examples.ex58.judgment = .acceptable ∧
    (Collins2005.ex9.passive .partP false).ObeysUIC IsLabeled ∧
    ¬ (Collins2005.ex9.passive .partP false).ObeysFreezing := by
  decide +kernel

end Boskovic2018
