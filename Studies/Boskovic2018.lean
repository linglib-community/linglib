module

public import Studies.Chomsky2013
public import Studies.Collins2005
public import Linglib.Data.Examples.Boskovic2018
public import Linglib.Syntax.Minimalist.Phase.Transfer
public import Linglib.Syntax.Minimalist.Label.RaisingHead
public import Linglib.Syntax.Minimalist.Workspace.Merge.Phase

/-!
# Bošković (2018): On movement out of moved elements, labels, and phases

A syntactic object is labeled, as in [chomsky-2013], by the one head minimal search finds in it
or by a feature the heads it finds share (`IsLabeled`), so a specifier that shares no feature with
its host leaves the host unlabeled until it moves on. A phase is an object labeled by a phase
head (`IsPhase`). Two conditions on a derivation `d` are stated with
`Minimalist.Derivation.MovesOnly`: `d.MovesOnly (IsPhase Φ)`, only phases move, and
`d.MovesOnly IsLabeled`, unlabeled elements do not move. The first entails the second
(`movesOnly_isLabeled_of_isPhase`), and an object two of whose labeling heads share no feature
fails the second (`not_movesOnly_of_not_agreed`). A derivation `Converges` when it moves only
labeled elements and obeys the Phase Impenetrability Condition.

Since the condition makes an element leave a phase by its edge before the phase moves, extraction
from a moved subject fails either way (`ex17`): the stop at the edge leaves the subject unlabeled,
and without the stop the extraction crosses a phase. What is generated at the edge, or moves there
to share a feature, leaves the phase labeled and free to move, and can then be extracted from it
(`ex25a`, `ex42a`). A verb-second clause, whose specifier agrees with nothing, cannot move though
nothing moves out of it (`ex22`). Remnant movement is unaffected (`ex20`), and the smuggling
passive of [collins-2005] moves only labeled elements but moves a non-phase (`ex58`).

The condition is also the phase coproduct of [marcolli-chomsky-berwick-2025], which extracts no
term in the interior of a lower phase: extracted from the moved subject, *who* is such a term
(`inaccessible_who_iff`), so the unit stage of its Internal Merge vanishes
(`mergeOpUnit_who_eq_zero`).

## Implementation notes

* Roots are left out of the heads that label, and the features shared are the paper's: the concord
  of a Serbo-Croatian possessive adjective with its noun, and the R-feature of the Dutch r-pronoun
  of (42) with its preposition. Successive-cyclic and verb-second specifiers share none.
* The phases are those of [chomsky-2000], CP, vP and DP, and in Serbo-Croatian, which lacks DP,
  the noun phrase. Transfer seals the complement of a phase head once its phase is complete, the
  phase being the head's projection under `HeadFunction.raising`, so that a phase head's
  specifiers are in its phase however they are labeled. Read off labels instead
  (`HeadFunction.label`), the unlabeled verb-second clause of (22) would be complete before its
  specifier merged, and raising to Spec,CP would leave it (`v2InSitu_label_raising`): labels and
  phase edges are two notions of projection here.
* Of the derivations of (17), the two that extract from the moved subject are compared. Chain
  interleaving, where *who* leaves the edge of the subject before the subject raises, is set
  aside, as in the paper.
* Clauses are cut down to the heads each example needs, verbs in their base positions; the word
  orders of the German, Serbo-Croatian and Dutch examples are not modelled.

## TODO

* That only phases move is checked for the English examples. The moved noun phrase and possessor
  of (25a) and the moved PP of (42a) are phases only when the highest projection of each lexical
  category's extended projection is one, which `IsPhase` does not express.
* Left-branch and intensifier extraction (28)–(30), quantifier float, the Adjunct Condition, and
  the Coordinate Structure Constraint of Appendix B.

## References

* [boskovic-2018]
* [chomsky-2000]
* [chomsky-2013]
* [collins-2005]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Boskovic2018

open Minimalist Minimalist.PlanarSyntacticObject
open Chomsky2013 (tok nominal IsRoot)

variable {Φ : LexicalItem.Token → Prop} {t : PlanarSyntacticObject}
  {x : SyntacticObject} {d : Derivation}

/-! ### Labeling, phases and the PIC -/

/-- The features specifier and head share in the paper's examples. -/
inductive Feature
  | phi | r
  deriving DecidableEq, Fintype

/-- The determiner of the r-pronoun *waar*. -/
def waarD := tok 260 .D "waar" (sel := [.n])
/-- *mee* 'with', the form of the preposition an r-pronoun precedes. -/
def mee := tok 263 .P "mee" (sel := [.D])

/-- The feature sharing the paper assumes: a possessive adjective agrees with the noun in
φ-features and case, and the r-pronoun shares the R-feature with its preposition. -/
def Shares : Feature → LexicalItem.Token → LexicalItem.Token → Prop
  | .phi, a, b => a.item.cat = .a ∧ b.item.cat = .n
  | .r, a, b => a = waarD ∧ b = mee

instance : ∀ f, DecidableRel (Shares f)
  | .phi => fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))
  | .r => fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Two heads agree in a feature when one shares it with the other. -/
abbrev Agreed (f : Feature) : LexicalItem.Token → LexicalItem.Token → Prop :=
  Relation.SymmGen (Shares f)

/-- The heads minimal search finds that can label `x`: roots are too weak to label. -/
def labelers (t : PlanarSyntacticObject) (x : SyntacticObject) : Finset LexicalItem.Token :=
  (t.labels x).filter (¬ IsRoot ·)

/-- Labeling in the paper, that of [chomsky-2013]: by the one head that can label, or by a feature
the heads that can label share, when none of them is a daughter. -/
def IsLabeled (t : PlanarSyntacticObject) (x : SyntacticObject) : Prop :=
  (∃ a ∈ labelers t x, labelers t x = {a}) ∨
    ((labelers t x).Nontrivial ∧ (∀ a ∈ labelers t x, ¬ SyntacticObject.ImmediatelyContains x ↑a) ∧
      ∃ f, (labelers t x : Set LexicalItem.Token).Pairwise (Agreed f))

instance (t : PlanarSyntacticObject) (x : SyntacticObject) : Decidable (IsLabeled t x) :=
  haveI : Decidable (labelers t x).Nontrivial :=
    decidable_of_iff _ Finset.one_lt_card_iff_nontrivial
  inferInstanceAs (Decidable (_ ∨ _))

/-- A phase, given the phase heads: an object one of them labels. -/
def IsPhase (Φ : LexicalItem.Token → Prop) (t : PlanarSyntacticObject) (x : SyntacticObject) :
    Prop :=
  ∃ a ∈ labelers t x, Φ a ∧ labelers t x = {a}

instance [DecidablePred Φ] (t : PlanarSyntacticObject) (x : SyntacticObject) :
    Decidable (IsPhase Φ t x) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem IsPhase.isLabeled (h : IsPhase Φ t x) : IsLabeled t x :=
  let ⟨a, ha, _, h⟩ := h
  .inl ⟨a, ha, h⟩

/-- A derivation that moves only phases moves only labeled elements: (12) entails (33). -/
theorem movesOnly_isLabeled_of_isPhase (h : d.MovesOnly (IsPhase Φ)) : d.MovesOnly IsLabeled :=
  h.mono fun _ _ ↦ IsPhase.isLabeled

theorem not_isLabeled_of_not_agreed {a b : LexicalItem.Token} (ha : a ∈ labelers t x)
    (hb : b ∈ labelers t x) (hab : a ≠ b) (h : ∀ f, ¬ Agreed f a b) : ¬ IsLabeled t x := by
  rintro (⟨c, -, hc⟩ | ⟨-, -, f, hf⟩)
  · rw [hc, Finset.mem_singleton] at ha hb
    exact hab (ha.trans hb.symm)
  · exact h f (hf ha hb hab)

/-- An object two of whose labeling heads share no feature does not move: (32). -/
theorem not_movesOnly_of_not_agreed {a b : LexicalItem.Token} {p : PlanarSyntacticObject}
    {m : SyntacticObject} {side : Edge} (hp : p ∈ d.externalize?) (ha : a ∈ labelers p m)
    (hb : b ∈ labelers p m) (hab : a ≠ b) (h : ∀ f, ¬ Agreed f a b) :
    ¬ (d.append [.im m side]).MovesOnly IsLabeled := fun hm ↦ by
  obtain ⟨q, hq, hl⟩ := (Derivation.movesOnly_append_im_iff.1 hm).2
  obtain rfl := Option.mem_unique hq hp
  exact not_isLabeled_of_not_agreed ha hb hab h hl

/-- The phase heads of a language with articles: C, v and D. -/
def IsPhaseHead (a : LexicalItem.Token) : Prop := a.item.cat ∈ ({.C, .v, .D} : Finset Cat)

instance : DecidablePred IsPhaseHead := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

/-- The phase heads of Serbo-Croatian, which lacks DP: C, v and the nominalizer. -/
def IsPhaseHeadNP (a : LexicalItem.Token) : Prop := a.item.cat ∈ ({.C, .v, .n} : Finset Cat)

instance : DecidablePred IsPhaseHeadNP := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

/-- The cut of the PIC on an object: the complement of each phase head, sealed once its phase,
the head's projection under `hd`, is complete. -/
abbrev picCut (hd : HeadFunction) (Φ : LexicalItem.Token → Prop) [DecidablePred Φ]
    (t : PlanarSyntacticObject) : Cut :=
  sealed (occurrencesWith t Φ).toFinset complementDomain (.atCompletion hd t)

/-- The PIC on a derivation: it derives an object none of whose chain links leaves the cut. -/
abbrev ObeysPic (hd : HeadFunction) (Φ : LexicalItem.Token → Prop) [DecidablePred Φ]
    (d : Derivation) : Prop :=
  d.Respects hd (picCut hd Φ)

/-- A derivation converges when it obeys the PIC and moves only labeled elements. -/
def Converges (Φ : LexicalItem.Token → Prop) [DecidablePred Φ] (d : Derivation) : Prop :=
  d.MovesOnly IsLabeled ∧ ObeysPic .raising Φ d

instance [DecidablePred Φ] (d : Derivation) : Decidable (Converges Φ d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Extraction from a subject (16)–(18) -/

/-- The determiner of *who*. -/
def whoD := tok 200 .D "who" (features := .single .wh true) (sel := [.n])
/-- *who*. -/
def who : PlanarSyntacticObject := nominal whoD (tok 201 .n (sel := [.N])) (tok 202 .N)
def ofP := tok 203 .P "of" (sel := [.D])
def friends := tok 204 .N "friends" (sel := [.P])
def friendsN := tok 205 .n (sel := [.N])
def subjD := tok 206 .D (sel := [.n])
def hireV := tok 207 .v (sel := [.V])
def hired := tok 208 .V "hired" (sel := [.D])
/-- *Mary*. -/
def mary : PlanarSyntacticObject :=
  nominal (tok 209 .D (sel := [.n])) (tok 210 .n (sel := [.N])) (tok 211 .N "Mary")
def tI := tok 212 .T (sel := [.v])
def cQ := tok 213 .C (features := .single .wh true) (sel := [.T])

/-- The subject *friends of* `x`. -/
def subject (x : PlanarSyntacticObject) : PlanarSyntacticObject :=
  subjD * (friendsN * (friends * (ofP * x)))

/-- *hired Mary*, built in its own workspace. -/
def hiredMary : PlanarSyntacticObject := hireV * (hired * mary)

/-- The two ways *who* can leave the subject (16): by the subject's edge while the subject is in
situ, the cycle requiring the step before the subject moves, or directly from the moved subject. -/
inductive Route
  | edge | direct
  deriving DecidableEq, Fintype

/-- The derivation of (17) through the merger of I: the subject built around *who*, with *who*
raised to its edge along the edge route, and merged with *hired Mary*. -/
def subjectInSitu (r : Route) : Derivation :=
  ⟨tok 202 .N, [.em .left (tok 201 .n (sel := [.N])), .em .left whoD, .em .left ofP,
    .em .left friends, .em .left friendsN, .em .left subjD] ++
    (match r with | .edge => [.im who] | .direct => []) ++
    [.em .right hiredMary, .em .left tI]⟩

/-- What raises to Spec,IP along a route: the subject with *who* at its edge, or inside it. -/
def raisedSubject : Route → PlanarSyntacticObject
  | .edge => who * subject who.toSyntacticObject.tracePlanar
  | .direct => subject who

/-- The derivation of (17) up to the extraction of *who*: the subject raised over I, under the
interrogative C. -/
def beforeExtraction (r : Route) : Derivation :=
  ((subjectInSitu r).append [.im (raisedSubject r)]).append [.em .left cQ]

/-- The derivation of (17) along a route, *who* raised over the interrogative C. -/
def subextraction (r : Route) : Derivation := (beforeExtraction r).append [.im who]

-- (17)
theorem subextraction_surfacePhon (r : Route) :
    (subextraction r).surfacePhon = ["who", "friends", "of", "hired", "Mary"] := by
  cases r <;> decide +kernel

-- (18): with *who* at its edge, the subject has the heads of *who* and of the DP to label it
theorem not_movesOnly_edge : ¬ (subextraction .edge).MovesOnly IsLabeled := by
  obtain ⟨p, hp, ha, hb⟩ : ∃ p ∈ (subjectInSitu .edge).externalize?,
      whoD ∈ labelers p ↑(raisedSubject .edge) ∧ subjD ∈ labelers p ↑(raisedSubject .edge) := by
    decide +kernel
  exact fun h ↦ not_movesOnly_of_not_agreed hp ha hb (by decide) (by decide) h.of_append.of_append

-- (16): extracted from the moved subject, *who* crosses the phase of the subject's D
theorem not_respectsCut_direct : ∃ t ∈ (subextraction .direct).externalize?,
    ¬ RespectsCut .raising t (picCut .raising IsPhaseHead t) := by
  obtain ⟨t, ht, h, hh, ⟨q, tok⟩, hq, hD, -, h0, hproj, hc⟩ :
      ∃ t ∈ (subextraction .direct).externalize?, ∃ h ∈ occurrencesWith t IsPhaseHead,
        ∃ y ∈ tokenList t.toRoseTree, (h, subjD) ∈ tokenList t.toRoseTree ∧ y.2 = whoD ∧ h ≠ ⊥ ∧
          projectionAt .raising t h ≤ h.parent ∧ Crosses .raising t y.2 h := by
    decide +kernel
  exact ⟨t, ht, fun hr ↦ hr.not_crosses hq (List.mem_toFinset.2 hh) hD h0 hproj hc⟩

-- (1): along either route *who* leaves the raised subject
theorem not_obeysFreezing_subextraction (r : Route) : ¬ (subextraction r).ObeysFreezing :=
  fun h ↦ (Derivation.obeysFreezing_append_im_iff.1 h).2
    (by cases r <;> decide +kernel : (beforeExtraction r).Frozen ↑who)

-- extracted from the moved subject, *who* is in the interior of the subject phase when it would
-- move, and from the edge it is not
theorem inaccessible_who_iff (r : Route) :
    (beforeExtraction r).final.Inaccessible IsPhaseHead ↑who ↔ r = .direct := by
  cases r <;> decide +kernel

-- so the unit stage of the Internal Merge of *who* vanishes at the phase coproduct
theorem mergeOpUnit_who_eq_zero (cuts : _) :
    Merge.mergeOpUnitOfCuts (R := ℤ) (Merge.phaseCuts IsPhaseHead cuts)
      (who : SyntacticObject).toUnorderedTree
      (ConnesKreimer.of' {(beforeExtraction .direct).final.toUnorderedTree}) = 0 :=
  Merge.mergeOpUnitOfCuts_phaseCuts_eq_zero (by decide +kernel)
    ((inaccessible_who_iff .direct).2 rfl)

/-- In (17), neither route converges: by the edge the subject moves unlabeled, and directly *who*
crosses the subject phase. -/
theorem ex17 :
    ¬ (subextraction .edge).MovesOnly IsLabeled ∧
      ObeysPic .raising IsPhaseHead (subextraction .edge) ∧
      (∃ t ∈ (subextraction .direct).externalize?,
        ¬ RespectsCut .raising t (picCut .raising IsPhaseHead t)) ∧
      (∀ r, ¬ (subextraction r).ObeysFreezing) ∧
      (Examples.ex17.judgment = .acceptable ↔ ∃ r, Converges IsPhaseHead (subextraction r)) :=
  ⟨not_movesOnly_edge, by decide +kernel, not_respectsCut_direct, not_obeysFreezing_subextraction,
    iff_of_false (by decide) (by
      rintro ⟨_ | _, h⟩
      · exact not_movesOnly_edge h.1
      · obtain ⟨t, ht, hn⟩ := not_respectsCut_direct
        obtain ⟨t', ht', hr⟩ := h.2
        obtain rfl := Option.mem_unique ht ht'
        exact hn hr)⟩

/-! ### Remnant movement (20)–(21) -/

def janeD := tok 220 .D (sel := [.n])
/-- *Jane*. -/
def jane : PlanarSyntacticObject :=
  nominal janeD (tok 221 .n (sel := [.N])) (tok 222 .N "Jane")
def kiss := tok 223 .V "kiss" (sel := [.D])
def kissV := tok 224 .v (sel := [.V])
def did := tok 225 .T "did" (sel := [.v])

/-- (20): the subject raised out of vP, and the remnant vP fronted. -/
def remnantFronting : Derivation :=
  ⟨tok 211 .N "Mary", [.em .left (tok 210 .n (sel := [.N])), .em .left (tok 209 .D (sel := [.n])),
    .em .left kiss, .em .left kissV, .em .left jane, .em .left did, .im jane,
    .im (jane.toSyntacticObject.tracePlanar * (kissV * (kiss * mary)) : PlanarSyntacticObject)]⟩

-- (20), (21)
theorem ex20 : remnantFronting.surfacePhon = ["kiss", "Mary", "Jane", "did"] ∧
    remnantFronting.IsRemnantStep 7 janeD ∧ remnantFronting.ObeysFreezing ∧
    remnantFronting.MovesOnly (IsPhase IsPhaseHead) ∧
    (Examples.ex20.judgment = .acceptable ↔ Converges IsPhaseHead remnantFronting) := by
  decide +kernel

/-! ### Verb-second clauses (22) -/

def peterD := tok 230 .D "den" (sel := [.n])
/-- *den Peter*. -/
def peter : PlanarSyntacticObject :=
  nominal peterD (tok 231 .n (sel := [.N])) (tok 232 .N "Peter")
def mag := tok 233 .V "mag" (sel := [.D])
/-- *niemand*. -/
def niemand : PlanarSyntacticObject :=
  nominal (tok 234 .D "niemand" (sel := [.n])) (tok 235 .n (sel := [.N])) (tok 236 .N)
def cV2 := tok 237 .C (sel := [.V])

/-- The verb-second clause *den Peter mag niemand*, the object raised to its specifier. -/
def v2Clause : PlanarSyntacticObject :=
  peter * (cV2 * (niemand * (mag * peter.toSyntacticObject.tracePlanar)))

/-- The steps that build the verb-second clause. -/
def v2Steps : List Step :=
  [.em .left (tok 231 .n (sel := [.N])), .em .left peterD, .em .left mag, .em .left niemand,
    .em .left cV2, .im peter]

def bekannt := tok 238 .A "bekannt" (sel := [.C])
def ist := tok 239 .T "ist" (sel := [.A])
def sagte := tok 240 .V "sagte" (sel := [.C])

/-- The verb-second clause under *bekannt ist*. -/
def v2Embedded : Derivation :=
  ⟨tok 232 .N "Peter", v2Steps ++ [.em .left bekannt, .em .left ist]⟩

/-- (22a): the verb-second clause raised to Spec,IP. -/
def v2Moved : Derivation := v2Embedded.append [.im v2Clause]

/-- (22c): the verb-second clause in situ, the complement of *sagte*. -/
def v2InSitu : Derivation := ⟨tok 232 .N "Peter", v2Steps ++ [.em .left sagte]⟩

/-- (22): a verb-second clause, its specifier sharing no feature with C, is unlabeled and cannot
move, though nothing moves out of it. -/
theorem ex22 : v2Moved.ObeysFreezing ∧
    (Examples.ex22a.judgment = .acceptable ↔ Converges IsPhaseHead v2Moved) ∧
    (Examples.ex22c.judgment = .acceptable ↔ Converges IsPhaseHead v2InSitu) := by
  obtain ⟨p, hp, ha, hb⟩ : ∃ p ∈ v2Embedded.externalize?,
      peterD ∈ labelers p ↑v2Clause ∧ cV2 ∈ labelers p ↑v2Clause := by
    decide +kernel
  exact ⟨by decide +kernel, iff_of_false (by decide) fun h ↦
    not_movesOnly_of_not_agreed hp ha hb (by decide) (by decide) h.1, by decide +kernel⟩

-- (22c): the verb-second clause has no head daughter by labels and C′ by the raising head, and
-- with phases read off labels *Peter* raising to Spec,CP would leave C's sealed complement
theorem v2InSitu_label_raising :
    (v2InSitu.externalize?.map fun t ↦ HeadFunction.label t ⟨[1]⟩) = some none ∧
    (v2InSitu.externalize?.map fun t ↦ HeadFunction.raising t ⟨[1]⟩) = some (some 1) ∧
    ∃ t ∈ v2InSitu.externalize?, ¬ RespectsCut .label t (picCut .label IsPhaseHead t) := by
  decide +kernel

/-! ### Base-generated specifiers: Serbo-Croatian possessors (24)–(27) -/

def ovA := tok 250 .a "Jovanovu" (sel := [.N])
/-- The possessive adjective *Jovanovu* 'John's'. -/
def possessor : PlanarSyntacticObject := ovA * tok 251 .N
def slikaN := tok 252 .n (sel := [.N])
def slika := tok 253 .N "sliku"
/-- The object *Jovanovu sliku* 'John's picture', the possessor at its edge. -/
def object : PlanarSyntacticObject := possessor * (slikaN * slika)
def vidio := tok 254 .V "vidio" (sel := [.n])
def je := tok 255 .T "je" (sel := [.V])

/-- (24): the possessor extracted from the object in its base position. -/
def possessorInSitu : Derivation :=
  ⟨slika, [.em .left slikaN, .em .left possessor, .em .left vidio, .em .left je, .im possessor]⟩

/-- (27): the object fronted, the possessor in its specifier. -/
def objectFronting : Derivation :=
  ⟨slika, [.em .left slikaN, .em .left possessor, .em .left vidio, .em .left je, .im object]⟩

/-- (25a), derived as (26): the object fronted, and the possessor extracted from it. -/
def possessorExtraction : Derivation := objectFronting.append [.im possessor]

/-- The possessor leaves the object from its edge in situ (24), the object, labeled by the
concord of possessor and noun, moves (27), and the possessor then leaves the moved object (25a),
against the traditional ban. -/
theorem ex25a : possessorInSitu.ObeysFreezing ∧ ¬ possessorExtraction.ObeysFreezing ∧
    (Examples.ex24.judgment = .acceptable ↔ Converges IsPhaseHeadNP possessorInSitu) ∧
    (Examples.ex27.judgment = .acceptable ↔ Converges IsPhaseHeadNP objectFronting) ∧
    (Examples.ex25a.judgment = .acceptable ↔ Converges IsPhaseHeadNP possessorExtraction) :=
  ⟨by decide +kernel, fun h ↦ (Derivation.obeysFreezing_append_im_iff.1 h).2
    (by decide +kernel : objectFronting.Frozen ↑possessor), by decide +kernel⟩

/-! ### R-pronouns (37)–(42) -/

/-- *waar*. -/
def waar : PlanarSyntacticObject := nominal waarD (tok 261 .n (sel := [.N])) (tok 262 .N)
/-- *waar mee*, the r-pronoun in Spec,PP. -/
def pp : PlanarSyntacticObject := waar * (mee * waar.toSyntacticObject.tracePlanar)
/-- *de vis snijden*. -/
def snijden : PlanarSyntacticObject :=
  tok 264 .V "snijden" (sel := [.D]) *
    nominal (tok 265 .D "de" (sel := [.n])) (tok 266 .n (sel := [.N])) (tok 267 .N "vis")
def zou := tok 268 .T "zou" (sel := [.V])
def dat := tok 269 .C "dat" (sel := [.T])
def gedacht := tok 270 .V "gedacht" (sel := [.C])
def had := tok 271 .T "had" (sel := [.V])
def cWh := tok 272 .C (features := .single .wh true) (sel := [.T])

/-- (42a) before *waar* is extracted: *waar* raised to Spec,PP, and the PP raised out of the
embedded clause through its edge. -/
def ppFronting : Derivation :=
  ⟨tok 262 .N, [.em .left (tok 261 .n (sel := [.N])), .em .left waarD, .em .left mee, .im waar,
    .em .right snijden, .em .left zou, .em .left dat, .im pp, .em .left gedacht, .im pp,
    .em .left had, .em .left cWh]⟩

/-- (42a): *waar* extracted from the moved PP. -/
def rPronounExtraction : Derivation := ppFronting.append [.im waar]

-- (42a): *waar* shares the R-feature in Spec,PP, so the PP is labeled, moves, and *waar* leaves it
theorem ex42a : ¬ rPronounExtraction.ObeysFreezing ∧
    (Examples.ex42a.judgment = .acceptable ↔ Converges IsPhaseHead rPronounExtraction) :=
  ⟨fun h ↦ (Derivation.obeysFreezing_append_im_iff.1 h).2
    (by decide +kernel : ppFronting.Frozen ↑waar), by decide +kernel⟩

-- the specifiers that share a feature are accessible in the moved phrase
theorem not_inaccessible_specifier :
    ¬ objectFronting.final.Inaccessible IsPhaseHeadNP ↑possessor ∧
      ¬ ppFronting.final.Inaccessible IsPhaseHead ↑waar := by
  decide +kernel

/-! ### Smuggling (Appendix A) -/

-- (58): the object raises out of moved PartP, which is labeled and is not a phase
theorem ex58 : (Collins2005.ex9.passive .partP false).MovesOnly IsLabeled ∧
    ¬ (Collins2005.ex9.passive .partP false).ObeysFreezing ∧
    ¬ (Collins2005.ex9.fronted .partP false).MovesOnly (IsPhase IsPhaseHead) :=
  ⟨by decide +kernel, (Collins2005.converges_iff_not_obeysFreezing _ _ _ _ _ .partP false).1
    ((Collins2005.converges_iff _ _ _ _ _ .partP false).2 rfl), by decide +kernel⟩

end Boskovic2018
