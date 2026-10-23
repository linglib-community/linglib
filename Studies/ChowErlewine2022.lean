module

public import Linglib.Semantics.Exhaustification.Trivalent
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype

/-!
# Chow and Erlewine (2022): Restrictions on the position of exh

Chow and Erlewine argue that the covert exhaustification operator *exh* of Fox's grammatical
theory of scalar implicature is syntactically constrained: for most SI triggers *exh* must adjoin
at the lowest position where it is not vacuous (their generalization (9)), a requirement they
encode as a feature `[uexh*]` on the trigger in the style of Chierchia. The diagnostic is the
additive presupposition of *also*: whether *exh* sits below or above *also* determines whether the
additive presupposition is exhaustified, which antecedent contexts then satisfy or fail.

Parses are operator spines interpreted compositionally into trivalent propositions. *exh* is
Spector and Sudo's strong-negation EXH² (`Exhaustification.Trivalent.exh2`, the operator the
paper adopts in its footnote 4), so the presupposition of a negated alternative projects: the
parse *exh* > *also* presupposes a salient conjunctive antecedent, which is what blocks a
disjunctive one. Adjunction sites are computed from a base clause, and generalization (9) is
`BaseClause.lowestNonVacuousSite`: the deepest trigger-commanding site where inserting *exh*
changes the interpretation. Section 4's ignorance implicatures are derived over belief states with
*exh* above the covert doxastic necessity operator; the four antecedent types of Marty and Romoli
separate the two grammatical parses, and the parse needed for the plain disjunctive antecedent
places the necessity operator below surface-scope *also*, embedded, contra Meyer's Matrix K
theory.

## Implementation notes

The trigger moved to subject position, (7), reconstructs semantically, with movement
reflected only in the site calculus; the embedding verb of (28) is opaque to interpretation
and matters only to the site calculus; and the presupposition of parse (35) is taken from the
paper's display, since they defer its derivation to Marty and Romoli. The *again* data of their
section 2.4 replicate the *also* pattern and are not modeled separately.

## References

* [chow-erlewine-2022]
* [spector-sudo-2017]
* [marty-romoli-2021]
* [fox-2007]
* [chierchia-2013]
* [meyer-2013]
-/

@[expose] public section

namespace ChowErlewine2022

open Exhaustification

/-! ### Individuals and worlds

The running examples predicate teaching Arabic and teaching Basque of a focused individual
(Nina) and a salient alternative (Mira). A world fixes both teaching profiles. -/

/-- Which of the two languages an individual teaches. -/
structure Taught where
  arabic : Bool
  basque : Bool
  deriving DecidableEq, Fintype, Repr

namespace Taught

/-- Teaches Arabic or Basque. -/
def either (t : Taught) : Bool := t.arabic || t.basque

/-- Teaches Arabic and Basque. -/
def both (t : Taught) : Bool := t.arabic && t.basque

/-- Teaches exactly one of the two languages. -/
def exactlyOne (t : Taught) : Bool := t.either && !t.both

/-- Teaches neither language. -/
def neither (t : Taught) : Bool := !t.either

/-- Teaches Arabic and not Basque. -/
def onlyArabic (t : Taught) : Bool := t.arabic && !t.basque

/-- Teaches Basque and not Arabic. -/
def onlyBasque (t : Taught) : Bool := !t.arabic && t.basque

end Taught

/-- The focused individual of the prejacent and the salient antecedent individual. -/
inductive Individual where
  | nina
  | mira
  deriving DecidableEq, Fintype, Repr

/-- The salient focus alternative. -/
def Individual.other : Individual → Individual
  | .nina => .mira
  | .mira => .nina

/-- A world records both individuals' teaching profiles. -/
structure TeachWorld where
  nina : Taught
  mira : Taught
  deriving DecidableEq, Fintype, Repr

/-- The profile of an individual at a world. -/
def TeachWorld.taught (w : TeachWorld) : Individual → Taught
  | .nina => w.nina
  | .mira => w.mira

/-! ### Parses and their trivalent interpretation -/

/-- An LF parse is an operator spine over a scalar leaf. The leaf carries the denotation of the
scalar item and of its Horn-scale mate, both predicated of a focus individual `F`. -/
inductive Parse (F W : Type) where
  | lex (den alt : F → (W → SignType))
  | exh (t : Parse F W)
  | not (t : Parse F W)
  | also (t : Parse F W)

variable {F W : Type} [Fintype W] [DecidableEq W]

/-- A parse and its scale-mate are interpreted in one recursion. *exh* is EXH²
([spector-sudo-2017], the paper's footnote 4) with the scale-mate as its alternative, negation is
strong Kleene (a presupposition hole), and *also* presupposes that its scope holds of the salient
focus alternative `sal x` ([chow-erlewine-2022] section 2, following Kripke and Heim). -/
def Parse.interpWithMate (sal : F → F) :
    Parse F W → F → (W → SignType) × (W → SignType)
  | .lex den alt, x => (den x, alt x)
  | .not t, x =>
      let (p, q) := t.interpWithMate sal x
      (fun w ↦ -p w, fun w ↦ -q w)
  | .exh t, x =>
      let (p, q) := t.interpWithMate sal x
      (Trivalent.exh2 [q] p, Trivalent.exh2 [p] q)
  | .also t, x =>
      let pres := t.interpWithMate sal (sal x)
      let (p, q) := t.interpWithMate sal x
      (fun w ↦ if pres.1 w = 1 then p w else 0,
       fun w ↦ if pres.2 w = 1 then q w else 0)

/-- The trivalent interpretation of a parse, about the focus individual `x`. -/
def Parse.interp (sal : F → F) (t : Parse F W) (x : F) : (W → SignType) :=
  (t.interpWithMate sal x).1

/-- The parse's presuppositions are met throughout a context when no context world leaves it
undefined. Antecedent contexts are the worlds compatible with the antecedent sentence, including
that sentence's own implicatures. -/
def Parse.FelicitousIn (sal : F → F) (t : Parse F W) (x : F) (ctx : Finset W) : Prop :=
  ∀ w ∈ ctx, t.interp sal x w ≠ 0

instance (sal : F → F) (t : Parse F W) (x : F) (ctx : Finset W) :
    Decidable (t.FelicitousIn sal x ctx) :=
  inferInstanceAs (Decidable (∀ w ∈ ctx, t.interp sal x w ≠ 0))

/-! ### Adjunction sites and generalization (9) -/

/-- An overt operator of the base clause. The embedding verb is opaque to interpretation
(attitude semantics is out of scope) and matters only to the site calculus. -/
inductive ClauseOp where
  | alsoOp
  | notOp
  | embedOp
  deriving DecidableEq, Repr

/-- Wrap a spine of overt operators around a parse, top-down. -/
def wrapOps : List ClauseOp → Parse F W → Parse F W
  | [], t => t
  | .alsoOp :: rest, t => .also (wrapOps rest t)
  | .notOp :: rest, t => .not (wrapOps rest t)
  | .embedOp :: rest, t => wrapOps rest t

/-- A base clause carries the scalar item, the overt operators above the verb phrase (top-down),
and the number of them taking scope over the trigger's surface position. Site `i` is the
adjunction position with `i` operators above it; a site commands the trigger iff
`i ≤ triggerDepth`. The trigger interprets in its base position throughout, so movement (the
paper's (7)) shows up only in `triggerDepth`. -/
structure BaseClause (F W : Type) where
  den : F → (W → SignType)
  alt : F → (W → SignType)
  ops : List ClauseOp
  triggerDepth : ℕ

/-- The scalar leaf of the clause. -/
def BaseClause.leaf (b : BaseClause F W) : Parse F W := .lex b.den b.alt

/-- The clause with no *exh*. -/
def BaseClause.plain (b : BaseClause F W) : Parse F W := wrapOps b.ops b.leaf

/-- The clause with *exh* adjoined at site `i`. -/
def BaseClause.withExhAt (b : BaseClause F W) (i : ℕ) : Parse F W :=
  wrapOps (b.ops.take i) (.exh (wrapOps (b.ops.drop i) b.leaf))

/-- *exh* at site `i` is vacuous when inserting it does not change the interpretation. -/
def BaseClause.Vacuous (sal : F → F) (b : BaseClause F W) (i : ℕ) : Prop :=
  (b.withExhAt i).interp sal = b.plain.interp sal

instance [Fintype F] [DecidableEq F] (sal : F → F) (b : BaseClause F W) (i : ℕ) :
    Decidable (b.Vacuous sal i) :=
  decidable_of_iff ((b.withExhAt i).interp sal = b.plain.interp sal) Iff.rfl

/-- Generalization (9) of [chow-erlewine-2022] names the lowest trigger-commanding site where
*exh* is not vacuous. A `[uexh*]` trigger's *exh* must adjoin exactly here. -/
def BaseClause.lowestNonVacuousSite [Fintype F] [DecidableEq F]
    (sal : F → F) (b : BaseClause F W) : Option ℕ :=
  (List.range (b.ops.length + 1)).reverse.find?
    (fun i ↦ decide (i ≤ b.triggerDepth ∧ ¬ b.Vacuous sal i))

/-- The site just above the verb embedding the trigger's finite clause (`0` when mono-clausal)
is the highest site `[uexh]`-checking may reach ([chow-erlewine-2022] section 3.3). -/
def BaseClause.clauseEdge (b : BaseClause F W) : ℕ :=
  (((List.range b.triggerDepth).filter (fun j ↦ b.ops.getD j .alsoOp = .embedOp)).max?).getD 0

/-! ### The feature table (30) -/

/-- The exhaustification feature an SI trigger bears ([chow-erlewine-2022] (30), after
[chierchia-2013]). `strong` is `[uexh*]`, `weak` is `[uexh]`, and `none` is unmarked. -/
inductive ExhFeature where
  | strong
  | weak
  | none
  deriving DecidableEq, Repr

/-- The adjunction sites a feature makes available for the trigger's *exh* are the forced site
of generalization (9) for `[uexh*]`, any trigger-commanding site from the clause edge down for
`[uexh]`, and any trigger-commanding site for unmarked triggers. -/
def ExhFeature.allowedSites [Fintype F] [DecidableEq F]
    (f : ExhFeature) (sal : F → F) (b : BaseClause F W) : Finset ℕ :=
  match f with
  | .strong =>
      match b.lowestNonVacuousSite sal with
      | .some i => {i}
      | .none => ∅
  | .weak =>
      ((List.range (b.ops.length + 1)).filter
        (fun i ↦ b.clauseEdge ≤ i && i ≤ b.triggerDepth)).toFinset
  | .none => ((List.range (b.ops.length + 1)).filter (fun i ↦ i ≤ b.triggerDepth)).toFinset

/-- The SI triggers the paper classifies. -/
inductive SITrigger where
  | disj
  | conj
  | univAll
  | unstressedSome
  | bareNumeral
  | stressedSome
  | scalarAdj
  deriving DecidableEq, Repr

/-- In the feature specification (30), disjunction, conjunction, *all*, unstressed *sm* and
bare numerals are `[uexh*]`, stressed *SOME* is `[uexh]`, and scalar adjectives are unmarked. -/
def SITrigger.feature : SITrigger → ExhFeature
  | .stressedSome => .weak
  | .scalarAdj => .none
  | _ => .strong

/-! ### Section 2: the *also* diagnostic with disjunction -/

/-- "teaches Arabic or Basque", of the focus individual. -/
def orLex : Individual → (TeachWorld → SignType) := fun x w ↦ .ofProp (w.taught x).either

/-- "teaches Arabic and Basque", of the focus individual. -/
def andLex : Individual → (TeachWorld → SignType) := fun x w ↦ .ofProp (w.taught x).both

/-- The base clause of (3) is *[Nina]F also teaches Arabic or Basque*, with *also* above the
in-situ trigger. -/
def teachOr : BaseClause Individual TeachWorld := ⟨orLex, andLex, [.alsoOp], 1⟩

/-- The base clause of the passive (7) is *Arabic or Basque is also taught by [Nina]F*, with
the trigger moved above *also*. -/
def passiveOr : BaseClause Individual TeachWorld := { teachOr with triggerDepth := 0 }

/-- The worlds an antecedent sentence about Mira leaves open. -/
def antecedent (p : Taught → Bool) : Finset TeachWorld :=
  Finset.univ.filter (fun w ↦ p w.mira)

/-- The direct SI of disjunction, (1), makes `exh (A ∨ B)` exclusive disjunction. -/
theorem exh_or_direct :
    ∀ w, (Parse.exh teachOr.leaf).interp Individual.other .nina w = 1 ↔
      w.nina.exactlyOne := by decide

/-- The presupposition of parse (4), *also* > *exh*, is that a salient individual teaches
exactly one of the two languages. -/
theorem also_exh_presup :
    ∀ w, (teachOr.withExhAt 1).interp Individual.other .nina w ≠ 0 ↔
      w.mira.exactlyOne := by decide

/-- Under parse (5), *exh* > *also*, the presupposition requires a salient individual to teach both
languages. -/
theorem exh_over_also_presup :
    ∀ w, (teachOr.withExhAt 0).interp Individual.other .nina w ≠ 0 ↔
      w.mira.both := by decide

/-- The truth conditions of parse (5) conjoin the salient conjunctive presupposition with the
exhaustified assertion about Nina. -/
theorem exh_over_also_true_iff :
    ∀ w, (teachOr.withExhAt 0).interp Individual.other .nina w = 1 ↔
      (w.mira.both ∧ w.nina.either ∧ ¬ w.nina.both) := by decide

/-- Under the *also* > *exh* parse, the disjunctive antecedent satisfies the additive presupposition
and the conjunctive one does not, matching (3). -/
theorem also_exh_verdicts :
    (teachOr.withExhAt 1).FelicitousIn Individual.other .nina (antecedent Taught.exactlyOne)
    ∧ ¬ (teachOr.withExhAt 1).FelicitousIn Individual.other .nina (antecedent Taught.both) := by
  decide

/-- Parse (5) licenses exactly the conjunctive antecedent, felicitous in (3b)'s context and not in
(3a)'s, so the grammar must block it in (3). -/
theorem exh_over_also_verdicts :
    (teachOr.withExhAt 0).FelicitousIn Individual.other .nina (antecedent Taught.both)
    ∧ ¬ (teachOr.withExhAt 0).FelicitousIn Individual.other .nina
        (antecedent Taught.exactlyOne) := by
  decide

/-- For the attested positions (8), generalization (9) places *exh* below *also* in (3) and above it
in the passive (7), reversing the (3b) judgment. -/
theorem or_exh_sites :
    SITrigger.disj.feature.allowedSites Individual.other teachOr = {1}
    ∧ SITrigger.disj.feature.allowedSites Individual.other passiveOr = {0} := by decide

/-! ### Section 2.3: indirect scalar implicatures under negation -/

/-- The base clause of (16) is *[Nina]F also does not teach Arabic and Basque*, with *also*
over negation over the conjunctive trigger. -/
def negConj : BaseClause Individual TeachWorld := ⟨andLex, orLex, [.alsoOp, .notOp], 2⟩

/-- *exh* directly on conjunction, position 3 of (19) and parse (18c), is vacuous, since the
disjunctive alternative is entailed and nothing is excludable. -/
theorem exh_vacuous_below_negation : negConj.Vacuous Individual.other 2 := by decide

/-- At position 2 of (19), the `[uexh*]` of the conjunctive trigger forces *exh* just above
negation. -/
theorem negConj_site :
    SITrigger.conj.feature.allowedSites Individual.other negConj = {1} := by decide

/-- Under parse (18b), the indirect SI `exh ¬(A ∧ B)` is exclusive disjunction for both the salient
individual and Nina. -/
theorem si_under_also_true_iff :
    ∀ w, (negConj.withExhAt 1).interp Individual.other .nina w = 1 ↔
      (w.mira.exactlyOne ∧ w.nina.exactlyOne) := by decide

/-- By the judgments (16) under the forced parse (18b), the not-and antecedent (with its
indirect SI) is licensed and the not-or antecedent is not. -/
theorem indirect_si_contrast :
    (negConj.withExhAt 1).FelicitousIn Individual.other .nina (antecedent Taught.exactlyOne)
    ∧ ¬ (negConj.withExhAt 1).FelicitousIn Individual.other .nina
        (antecedent Taught.neither) := by
  decide

/-- Under parse (18a), *exh* above *also* licenses exactly the not-or antecedent, the reverse of the
facts. -/
theorem exh_over_also_negConj_verdicts :
    (negConj.withExhAt 0).FelicitousIn Individual.other .nina (antecedent Taught.neither)
    ∧ ¬ (negConj.withExhAt 0).FelicitousIn Individual.other .nina
        (antecedent Taught.exactlyOne) := by
  decide

/-- Under parse (18c), vacuous *exh* lets both antecedents of (16) satisfy the presupposition, a
parse the non-vacuity clause of (9) excludes. -/
theorem vacuous_parse_licenses_both :
    (negConj.withExhAt 2).FelicitousIn Individual.other .nina (antecedent Taught.exactlyOne)
    ∧ (negConj.withExhAt 2).FelicitousIn Individual.other .nina (antecedent Taught.neither) := by
  decide

/-! ### Section 3: variation by SI trigger

The scale of *sm* and *all* over a two-membered domain is the disjunction-conjunction scale, so
the (14) and (26) clauses reuse the teaching model, with `Taught` read as which of the two
students the focus individual met. -/

/-- Unstressed *sm* forces *exh* below *also* and stressed *SOME* also allows the site above it
((14), (14a), (26a); bare numerals (13)). -/
theorem sm_below_also_SOME_free :
    SITrigger.unstressedSome.feature.allowedSites Individual.other teachOr = {1}
    ∧ 0 ∈ SITrigger.stressedSome.feature.allowedSites Individual.other teachOr := by decide

/-- The base clause of (28) puts matrix *also* above the verb embedding the *SOME* clause. -/
def embeddedSome : BaseClause Individual TeachWorld :=
  { teachOr with ops := [.alsoOp, .embedOp], triggerDepth := 2 }

/-- In (28), every site `[uexh]` allows lies below the matrix *also*, so (28) is infelicitous. -/
theorem embedded_SOME_trapped :
    SITrigger.stressedSome.feature.allowedSites Individual.other embeddedSome = {1, 2} := by
  decide

/-! ### Section 3.1: scalar adjectives -/

/-- The two cities of (24a). -/
inductive City where
  | paris
  | newYork
  deriving DecidableEq, Fintype, Repr

/-- The salient focus alternative among the cities. -/
def City.other : City → City
  | .paris => .newYork
  | .newYork => .paris

/-- On the temperature scale of (24a), freezing entails cold. -/
inductive Temp where
  | mild
  | cold
  | freezing
  deriving DecidableEq, Fintype, Repr

/-- At least cold. -/
def Temp.atLeastCold : Temp → Bool
  | .mild => false
  | _ => true

/-- Freezing. -/
def Temp.isFreezing : Temp → Bool
  | .freezing => true
  | _ => false

/-- The base clause of (24a) is *it's also cold in [Paris]F*. -/
def coldClause : BaseClause City (City → Temp) :=
  ⟨fun c w ↦ .ofProp (w c).atLeastCold, fun c w ↦ .ofProp (w c).isFreezing, [.alsoOp], 1⟩

/-- Contexts where it is freezing in New York. -/
def freezingNY : Finset (City → Temp) := Finset.univ.filter (fun w ↦ w .newYork = .freezing)

/-- In (24a), scalar adjectives allow *exh* above *also*, and that parse is felicitous with the
freezing antecedent. -/
theorem scalarAdj_high_exh_ok :
    0 ∈ SITrigger.scalarAdj.feature.allowedSites City.other coldClause
    ∧ (coldClause.withExhAt 0).FelicitousIn City.other .paris freezingNY := by decide

/-- Had *cold* carried `[uexh*]`, *exh* would sit below *also* and presuppose that New York is
cold but not freezing, wrongly blocking (24a). -/
theorem low_exh_would_block :
    ¬ (coldClause.withExhAt 1).FelicitousIn City.other .paris freezingNY := by decide

/-! ### Section 4: ignorance implicatures

Ignorance implicatures arise from a second *exh* above a covert doxastic necessity operator
([chierchia-2013]; K in [meyer-2013]). The state level works with the speaker's belief state
about one individual's teaching profile; the alternatives of the higher *exh* are the
pre-exhaustified disjunct alternatives, so its prejacent `□ exh (A ∨ B)` uses the inner SI
derived in `exh_or_direct`. -/

/-- A belief state about one individual's teaching profile. -/
abbrev Doxa := Finset Taught

/-- The covert necessity operator holds when the state supports `p` throughout. -/
def Doxa.must (s : Doxa) (p : Taught → Bool) : Bool := decide (∀ t ∈ s, p t)

/-- The state leaves `p` open. -/
def Doxa.may (s : Doxa) (p : Taught → Bool) : Bool := decide (∃ t ∈ s, p t)

/-- The meaning of *exh* > □ > *exh* over disjunction is computed by innocent exclusion over
belief states, with prejacent `□ exh (A ∨ B)` and the pre-exhaustified disjuncts `□ (A ∧ ¬B)`
and `□ (B ∧ ¬A)` as alternatives. -/
def ignoranceScope : Finset Doxa :=
  innocent.exh
    (altsFromPreds [(·.must Taught.onlyArabic), (·.must Taught.onlyBasque)])
    (predToFinset (·.must Taught.exactlyOne))

/-- In (31), the derived state supports exactly-one while leaving each disjunct's falsity open. -/
theorem ignorance_scope_eq :
    ignoranceScope =
      predToFinset (fun s ↦
        s.must Taught.exactlyOne && s.may (!·.arabic) && s.may (!·.basque)) := by decide

/-- The additive presupposition of parse (34) = (37a), *also* over the full ignorance meaning,
is that some salient individual's belief-state content is the whole of (31). -/
def presup34 (salient : List Doxa) : Prop := ∃ s ∈ salient, s ∈ ignoranceScope

instance (salient : List Doxa) : Decidable (presup34 salient) :=
  inferInstanceAs (Decidable (∃ s ∈ salient, s ∈ ignoranceScope))

/-- The additive presupposition of parse (35) = (37b), from the paper's display, demands a
salient individual believed to teach exactly one, one believed to teach Arabic only, and one
believed to teach Basque only. The paper defers the derivation to [marty-romoli-2021]'s (85). -/
def presup35 (salient : List Doxa) : Prop :=
  (∃ s ∈ salient, s.must Taught.exactlyOne)
  ∧ (∃ s ∈ salient, s.must Taught.onlyArabic)
  ∧ (∃ s ∈ salient, s.must Taught.onlyBasque)

instance (salient : List Doxa) : Decidable (presup35 salient) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- In the disjunctive antecedent context of (33a), the speaker believes Mira teaches exactly
one of the two languages, without knowing which. Each context lists the speaker's belief state about
each salient individual. -/
def disjCtx : List Doxa := [{⟨true, false⟩, ⟨false, true⟩}]

/-- The conjunctive antecedent context of (33b). -/
def conjCtx : List Doxa := [{⟨true, true⟩}]

/-- In the split antecedent context of (33c), Mira teaches Arabic only and Ora Basque only. -/
def splitCtx : List Doxa := [{⟨true, false⟩}, {⟨false, true⟩}]

/-- In the simple antecedent context of (33d), Mira teaches Arabic only. -/
def simpleCtx : List Doxa := [{⟨true, false⟩}]

/-- By (33), only parse (34) licenses the disjunctive antecedent and only (35) the split one, so the
grammar must generate (37a) and (37b). -/
theorem antecedent_pattern :
    (presup34 disjCtx ∧ ¬ presup35 disjCtx)
    ∧ (¬ presup34 conjCtx ∧ ¬ presup35 conjCtx)
    ∧ (¬ presup34 splitCtx ∧ presup35 splitCtx)
    ∧ (¬ presup34 simpleCtx ∧ ¬ presup35 simpleCtx) := by decide

/-- The covert and overt operators of the (37) parses, top-down over the disjunctive leaf, are
*also*, the ignorance *exh*, the doxastic necessity operator, and the SI *exh* that checks
`[uexh*]`. -/
inductive IgnOp where
  | also
  | ignExh
  | nec
  | siExh
  deriving DecidableEq, Repr

/-- Parse (37a) is *also* > *exh* > □ > *exh*. The necessity operator sits below *also*, which
occupies its surface vP-adjoined position, so once this parse is needed the ignorance-deriving □
is available clause-medially, (38) against [meyer-2013]'s Matrix K theory. -/
def parse37a : List IgnOp := [.also, .ignExh, .nec, .siExh]

/-- Parse (37b) is *exh* > □ > *also* > *exh*. -/
def parse37b : List IgnOp := [.ignExh, .nec, .also, .siExh]

/-- Parse (37c) is *exh* > □ > *exh* > *also*. -/
def parse37c : List IgnOp := [.ignExh, .nec, .siExh, .also]

/-- The site the SI *exh* occupies is given by the number of overt operators above it. -/
def siExhSite (p : List IgnOp) : ℕ := (p.takeWhile (· != .siExh)).count .also

/-- `[uexh*]` is checked iff the SI *exh* occupies the site generalization (9) forces on the
base clause of (3) = (32). Once checked, the feature imposes nothing on the higher *exh* and □
([chow-erlewine-2022] section 3.3). -/
def ChecksUExhStar (p : List IgnOp) : Prop :=
  some (siExhSite p) = teachOr.lowestNonVacuousSite Individual.other

instance (p : List IgnOp) : Decidable (ChecksUExhStar p) :=
  inferInstanceAs
    (Decidable (some (siExhSite p) = teachOr.lowestNonVacuousSite Individual.other))

/-- In (37), (37a) and (37b) check `[uexh*]` and (37c) does not, a contrast [marty-romoli-2021] and
[spector-sudo-2017] miss without the feature. -/
theorem parse37_grammaticality :
    ChecksUExhStar parse37a ∧ ChecksUExhStar parse37b ∧ ¬ ChecksUExhStar parse37c := by decide

end ChowErlewine2022
