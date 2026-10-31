module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Linglib.Fragments.German.Verbs
public import Linglib.Fragments.Icelandic.Verbs
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole
public import Linglib.Syntax.Case.Valuation
public import Linglib.Data.Examples.ZaenenMalingThrainsson1985
public import Linglib.Data.Examples.Readers

/-!
# Zaenen, Maling and Thráinsson (1985): Case and grammatical functions

This file formalizes [zaenen-maling-thrainsson-1985]'s account of the Icelandic passive and of
its German look-alike. A verb's arguments are thematic roles, some of which the verb marks with
an idiosyncratic case (`Arg`). Association principles map the roles onto the grammatical
functions SUBJ, OBJ and 2OBJ, one function to a role; the passive is an operation on functions
that suppresses SUBJ and makes OBJ the SUBJ (`GF.passive`); and only afterwards does default
case marking give the highest function without a case the nominative and the next the
accusative (`Principles.defaultCase`), so idiosyncratic case [survives the
passive](##mem_defaultCase_of_lexicalCase). Every association principle is universal but one
(`Principles`): Icelandic links a case-marked theme to the lowest function available
(`Principles.icelandic`), German any case-marked role to 2OBJ (`Principles.german`).

That one principle separates the two languages. [*Honum var hjálpað* and *Ihm wurde
geholfen*](##helped_passives) are passives with the same lone dative, which is the subject in
Icelandic and in German is not. Icelandic gives a dative–accusative verb
[two passives](##gefa_passives), with a dative subject and a nominative retained object or the
reverse, and a case-marked theme [passivizes exactly when it is the only
object](##icelandic_theme_passive); German [allows no verb two case-marked
arguments](##german_associations_eq_empty) and never makes a case-marked argument the
subject. The subjecthood tests of both languages target SUBJ whatever its case: [each of the
paper's judgments](##rows_subject) on raising, reflexivization, inversion, extraction,
postposing, ellipsis, control, relative reduction and passive is acceptable exactly when the
argument tested is assigned SUBJ.

## Implementation notes

* The roles are the traditional labels of `ArgumentStructure.ThetaRole`, stored in the
  thematic structure rather than derived as the library's role labels are, since the paper's
  thematic level is a list of labelled roles. The paper gives no thematic structure for *þykja*,
  *finnast*, *sakna*, *vanta*, *gefallen* and *übel sein*, whose subjects or datives are
  experiencers here, nor for *abhören*, whose roles follow *biðja*'s.
* An association is an injective map from the arguments to the functions, functional
  uniqueness being injectivity. Default case marking is a step of `Case.Valuation` on the
  arguments listed highest function first, so the persistence of idiosyncratic case is
  `Case.Valuation.Extends`.
* Principle (61a) fixes no order among the objects, which gives *gefa* its two associations
  (63); it is read as giving SUBJ to the first role the language-specific principle leaves free,
  the order of the thematic structures in (58), (60) and (63).
* Default case marking assigns two cases, so a third function without idiosyncratic case
  receives none; no verb of the paper presents one. The agent phrase of (53a) is dropped, as the
  paper drops it.

## Errata

* The principles (61), with (61a) fixing no order, [also let the nominative of *þykja* be
  SUBJ](##allows_thykja) for any roles but an agentive dative, against the tests (21c), (23d),
  (25c) and (27b), though the paper says they account for (62b). Its p. 469 welcomes both
  orders for many dative–nominative verbs; §2 shows that the nominative of *þykja* is no
  subject.
* The fifth item of (83) is printed as a second (83c); (37e) prints *goðs* for *góðs* and (64a)
  *hanni* for *hana*.

## References

* [zaenen-maling-thrainsson-1985]
-/

@[expose] public section

namespace ZaenenMalingThrainsson1985

open ArgumentStructure (ThetaRole)
open ZaenenMalingThrainsson1985.Examples

/-! ### Thematic structure and grammatical functions -/

/-- An argument at thematic structure: its role and the idiosyncratic case the verb assigns
it, if any, as in (60), from the cases `C` of the language. -/
structure Arg (C : Type*) where
  role : ThetaRole
  lexicalCase : Option C := none
  deriving DecidableEq, Repr

/-- The semantically unrestricted functions of (56). -/
inductive GF
  | subj
  | obj
  | obj2
  deriving DecidableEq, Repr, Fintype

/-- The voices. -/
inductive Voice
  | active
  | passive
  deriving DecidableEq, Repr

namespace GF

/-- The functions, highest first. -/
def all : List GF := [subj, obj, obj2]

/-- The functions available to `n` arguments, highest first, (61a). -/
def available (n : ℕ) : List GF := all.take n

/-- The lowest function available to `n` arguments. -/
def lowest (n : ℕ) : Option GF := (available n).getLast?

theorem lowest_eq_some_obj_iff {n : ℕ} : lowest n = some obj ↔ n = 2 := by
  rcases n with _ | _ | _ | n <;> simp [lowest, available, all]

/-- The passive on functions, (53): SUBJ is suppressed and OBJ becomes SUBJ. -/
def passive : GF → Option GF
  | subj => none
  | obj => some subj
  | obj2 => some obj2

theorem passive_eq_some_subj_iff {g : GF} : g.passive = some subj ↔ g = obj := by
  cases g <;> simp [passive]

/-- The function an argument bearing `g` bears in a voice. -/
def inVoice (g : GF) : Voice → Option GF
  | .active => some g
  | .passive => g.passive

end GF

/-! ### Association principles -/

/-- The association principles of a language, (61) and (87): the universal (61a), (61b) and
(61d), and a language-specific principle that takes precedence over them, fixing the function
of some arguments of a verb with `n` arguments; with the nominative and accusative of the
language, which default case marking assigns. -/
structure Principles (C : Type*) where
  /-- The function the language-specific principle fixes for an argument among `n`, if any. -/
  specific : ℕ → Arg C → Option GF
  /-- The nominative. -/
  nom : C
  /-- The accusative. -/
  acc : C

namespace Principles

variable {C : Type*} (P : Principles C)

/-- An argument among `n` may bear `g`: the function the language-specific principle fixes for
it, or, if it fixes none, a function available to `n` arguments (61a), SUBJ for an agent
(61b). -/
def Fits (n : ℕ) (x : Arg C) (g : GF) : Prop :=
  P.specific n x = some g ∨
    P.specific n x = none ∧ g ∈ GF.available n ∧ (x.role = .agent → g = .subj)

/-- The association principles allow the assignment `a` of functions to the arguments `t`, in
the paper's words (p. 467): no two arguments bear one function, by functional uniqueness, and
each function fits its argument. -/
def Allows (t : List (Arg C)) (a : Fin t.length → GF) : Prop :=
  Function.Injective a ∧ ∀ i, P.Fits t.length t[i] (a i)

/-- An association of the arguments `t`: an assignment the principles allow in which the first
argument the language-specific principle leaves free bears SUBJ. -/
def IsAssociation (t : List (Arg C)) (a : Fin t.length → GF) : Prop :=
  P.Allows t a ∧ ∀ i, P.specific t.length t[i] = none →
    (∀ j < i, P.specific t.length t[j] ≠ none) → a i = .subj

instance (n : ℕ) (x : Arg C) (g : GF) : Decidable (P.Fits n x g) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (t : List (Arg C)) (a : Fin t.length → GF) : Decidable (P.Allows t a) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, _))

instance (t : List (Arg C)) (a : Fin t.length → GF) : Decidable (P.IsAssociation t a) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, _))

/-- The associations of the arguments `t`. -/
def associations (t : List (Arg C)) : Finset (Fin t.length → GF) :=
  {a | P.IsAssociation t a}

@[simp] theorem mem_associations {t : List (Arg C)} {a : Fin t.length → GF} :
    a ∈ P.associations t ↔ P.IsAssociation t a := by
  simp [associations]

/-! ### Passive and default case -/

/-- The arguments bearing a function in a voice, highest function first. -/
def realized (t : List (Arg C)) (a : Fin t.length → GF) (v : Voice) : List (Arg C) :=
  GF.all.filterMap fun g ↦
    ((List.finRange t.length).find? fun i ↦ (a i).inVoice v = some g).map (t[·])

/-- Default case marking, (61d), as a step of case valuation on arguments listed highest
function first: the highest not yet valued takes the nominative and the next the accusative. -/
def defaultCase {α : Type*} (s : Case.Valuation α C) : Case.Valuation α C :=
  s.fill fun i _ ↦
    match (s.unvalued fun _ ↦ True).idxOf i with
    | 0 => some P.nom
    | 1 => some P.acc
    | _ => none

theorem extends_defaultCase {α : Type*} (s : Case.Valuation α C) :
    s.Extends (fun c ↦ c = P.nom ∨ c = P.acc) (P.defaultCase s) :=
  Case.Valuation.extends_fill (fun _ _ c h ↦ by split at h <;> simp_all) s

theorem mem_defaultCase_of_lexicalCase {xs : List (Arg C)} {x : Arg C} {c : C} (hx : x ∈ xs)
    (hc : x.lexicalCase = some c) :
    (x, .valued c) ∈
      P.defaultCase (Case.Valuation.initial (Case.Valuation.offer ·.lexicalCase) xs) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
  have h : (Case.Valuation.initial (Case.Valuation.offer ·.lexicalCase) xs)[i]? =
      some (x, .valued c) := by
    simp [Case.Valuation.initial_getElem?, hi, hc]
  exact List.mem_of_getElem? ((P.extends_defaultCase _).getElem?_of_some h)

/-- The case array of an association in a voice: the subject's case and then the objects' in
the order of their functions, the immediately postverbal NP the OBJ. -/
def caseArray (t : List (Arg C)) (a : Fin t.length → GF) (v : Voice) : List C :=
  (P.defaultCase (Case.Valuation.initial (Case.Valuation.offer ·.lexicalCase)
    (realized t a v))).filterMap (·.2.value?)

/-- The case arrays a thematic structure yields in a voice, one per association. -/
def arrays [DecidableEq C] (t : List (Arg C)) (v : Voice) : Finset (List C) :=
  (P.associations t).image (P.caseArray t · v)

/-- The argument with a role bears SUBJ under some association in the voice. -/
def IsSubject (t : List (Arg C)) (v : Voice) (ρ : ThetaRole) : Prop :=
  ∃ a ∈ P.associations t, ∃ i, t[i].role = ρ ∧ (a i).inVoice v = some .subj

instance (t : List (Arg C)) (v : Voice) (ρ : ThetaRole) : Decidable (P.IsSubject t v ρ) :=
  inferInstanceAs (Decidable (∃ a ∈ _, _))

end Principles

/-! ### Icelandic and German -/

/-- The Icelandic association principles, (61): a case-marked theme bears the lowest function
available, (61c). -/
def icelandic : Principles Icelandic.Case where
  specific n x := if x.role = .theme ∧ x.lexicalCase.isSome then GF.lowest n else none
  nom := .nom
  acc := .acc

/-- The German association principles, (87): a case-marked role bears 2OBJ, (87c). -/
def german : Principles German.Case where
  specific _ x := if x.lexicalCase.isSome then some .obj2 else none
  nom := .nom
  acc := .acc

open Principles

/-- A case-marked theme passivizes exactly when the verb has two arguments, its lowest available
function then being OBJ, and not beside two others, (67). -/
theorem icelandic_theme_passive {t : List (Arg Icelandic.Case)} {a : Fin t.length → GF}
    (ha : icelandic.Allows t a) {i : Fin t.length} (hθ : t[i].role = .theme)
    (hc : t[i].lexicalCase.isSome) : (a i).passive = some .subj ↔ t.length = 2 := by
  have hg : GF.lowest t.length = some (a i) := by
    rcases ha.2 i with h | ⟨h, hg, -⟩ <;> simp_all [icelandic, GF.lowest]
  rw [GF.passive_eq_some_subj_iff, ← GF.lowest_eq_some_obj_iff, hg, Option.some_inj]

-- (87c), p. 479
theorem german_eq_obj2 {t : List (Arg German.Case)} {a : Fin t.length → GF}
    (ha : german.Allows t a) {i : Fin t.length} (hc : t[i].lexicalCase.isSome) :
    a i = .obj2 := by
  have := ha.2 i
  simp only [Fits, german, hc, ite_true, Option.some_inj, reduceCtorEq, false_and,
    or_false] at this
  exact this.symm

-- p. 479
theorem german_inVoice_ne_subj {t : List (Arg German.Case)} {a : Fin t.length → GF}
    (ha : german.Allows t a) {i : Fin t.length} (hc : t[i].lexicalCase.isSome) (v : Voice) :
    (a i).inVoice v ≠ some .subj := by
  rw [german_eq_obj2 ha hc]
  cases v <;> simp [GF.inVoice, GF.passive]

/-- Two case-marked roles would both bear 2OBJ, so no German verb has two: there are no
dative–dative, dative–genitive or genitive–genitive verbs (p. 479). -/
theorem german_associations_eq_empty {t : List (Arg German.Case)} {i j : Fin t.length}
    (hij : i ≠ j) (hi : t[i].lexicalCase.isSome) (hj : t[j].lexicalCase.isSome) :
    german.associations t = ∅ :=
  Finset.eq_empty_of_forall_notMem fun _ ha ↦ hij <| (german.mem_associations.1 ha).1.1 <|
    (german_eq_obj2 (german.mem_associations.1 ha).1 hi).trans
      (german_eq_obj2 (german.mem_associations.1 ha).1 hj).symm

/-! ### The verbs -/

/-! The thematic structures of the paper's verbs, (58), (60), (63), (67) and Chart I. -/

namespace Thematic

def dansa : List (Arg Icelandic.Case) := [⟨.agent, none⟩]
def kyssa : List (Arg Icelandic.Case) := [⟨.agent, none⟩, ⟨.theme, none⟩]
def hjalpa : List (Arg Icelandic.Case) := [⟨.agent, none⟩, ⟨.theme, some .dat⟩]
def sakna : List (Arg Icelandic.Case) := [⟨.experiencer, none⟩, ⟨.theme, some .gen⟩]
def thykja : List (Arg Icelandic.Case) := [⟨.experiencer, some .dat⟩, ⟨.theme, none⟩]
def vanta : List (Arg Icelandic.Case) := [⟨.experiencer, some .acc⟩, ⟨.theme, some .acc⟩]
def gefa : List (Arg Icelandic.Case) :=
  [⟨.agent, none⟩, ⟨.theme, none⟩, ⟨.goal, some .dat⟩]
def leyna : List (Arg Icelandic.Case) :=
  [⟨.agent, none⟩, ⟨.theme, some .dat⟩, ⟨.source, none⟩]
def bidja : List (Arg Icelandic.Case) :=
  [⟨.agent, none⟩, ⟨.theme, some .gen⟩, ⟨.goal, none⟩]
def lofa : List (Arg Icelandic.Case) :=
  [⟨.agent, none⟩, ⟨.theme, some .dat⟩, ⟨.goal, some .dat⟩]
def oska : List (Arg Icelandic.Case) :=
  [⟨.agent, none⟩, ⟨.theme, some .gen⟩, ⟨.goal, some .dat⟩]
/-- *óska* as a simple transitive, its goal absent, (67). -/
def oskaTransitive : List (Arg Icelandic.Case) := [⟨.agent, none⟩, ⟨.theme, some .gen⟩]

/-! The German verbs of §5; *aufnehmen* and *verhaften* share the structure of *lesen*. -/

def helfen : List (Arg German.Case) := [⟨.agent, none⟩, ⟨.theme, some .dat⟩]
def lesen : List (Arg German.Case) := [⟨.agent, none⟩, ⟨.theme, none⟩]
def gefallen : List (Arg German.Case) := [⟨.experiencer, some .dat⟩, ⟨.theme, none⟩]
def uebelSein : List (Arg German.Case) := [⟨.experiencer, some .dat⟩]
def abhoeren : List (Arg German.Case) :=
  [⟨.agent, none⟩, ⟨.theme, some .acc⟩, ⟨.goal, none⟩]

end Thematic

/-- The paper's Icelandic verbs with the fragment entries they realize. -/
def entries : List (List (Arg Icelandic.Case) × Icelandic.Verbs.Verb) :=
  open Icelandic.Verbs in
  [(Thematic.dansa, dansa), (Thematic.kyssa, kyssa), (Thematic.hjalpa, hjalpa),
   (Thematic.sakna, sakna), (Thematic.thykja, thykja), (Thematic.thykja, finnast),
   (Thematic.vanta, vanta), (Thematic.gefa, gefa), (Thematic.gefa, segja),
   (Thematic.leyna, leyna), (Thematic.leyna, svipta), (Thematic.bidja, bidja),
   (Thematic.lofa, lofa), (Thematic.lofa, skila), (Thematic.oska, oska)]

theorem fragment_cases : (∀ e ∈ entries, e.2.cases ∈ icelandic.arrays e.1 .active) ∧
    German.Verbs.helfen.cases ∈ german.arrays Thematic.helfen .active := by
  decide

-- (62b)
theorem thykja_arrays : icelandic.arrays Thematic.thykja .active = {[.dat, .nom]} := by decide

-- (9a)
theorem dansa_passive : icelandic.arrays Thematic.dansa .passive = {[]} := by decide

/-- *Honum var hjálpað* and *Ihm wurde geholfen* are passives with the same lone dative, (4),
but the Icelandic dative is the subject and the German one is not, by (61c) and (87c). -/
theorem helped_passives :
    icelandic.arrays Thematic.hjalpa .passive = {[.dat]} ∧
      german.arrays Thematic.helfen .passive = {[.dat]} ∧
      icelandic.IsSubject Thematic.hjalpa .passive .theme ∧
      ¬ german.IsSubject Thematic.helfen .passive .theme := by
  decide

/-- A dative–accusative verb has two passives: the goal as dative subject with the theme a
nominative retained object, and the theme as nominative subject, (44). -/
theorem gefa_passives : icelandic.arrays Thematic.gefa .passive = {[.dat, .nom], [.nom, .dat]} := by
  decide

-- (42)
theorem lofa_passive : icelandic.arrays Thematic.lofa .passive = {[.dat, .dat]} := by decide

-- (68)
theorem oska_passive :
    icelandic.IsSubject Thematic.oskaTransitive .passive .theme ∧
      ¬ icelandic.IsSubject Thematic.oska .passive .theme := by
  decide

-- (88)
theorem abhoeren_arrays :
    german.arrays Thematic.abhoeren .active = {[.nom, .acc, .acc]} ∧
      german.arrays Thematic.abhoeren .passive = {[.nom, .acc]} := by
  decide

-- p. 480, a gap the paper leaves to accident (fn 24)
theorem icelandic_gen_gen :
    icelandic.arrays [⟨.agent, none⟩, ⟨.theme, some .gen⟩, ⟨.goal, some .gen⟩] .active =
      {[.nom, .gen, .gen]} := by
  decide

-- (61) as printed, against (21c), (23d), (25c) and (27b)
theorem allows_thykja (ρ σ : ThetaRole) (hρ : ρ ≠ .agent) :
    icelandic.Allows [⟨ρ, some .dat⟩, ⟨σ, none⟩] ![.obj, .subj] := by
  refine ⟨show Function.Injective (![.obj, .subj] : Fin 2 → GF) by decide,
    Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩ <;> by_cases h : ρ = .theme <;>
    simp [Fits, icelandic, GF.lowest, GF.available, GF.all, h, hρ]

/-! ### The rows -/

/-- The Icelandic verbs as the rows name them. -/
def icelandicVerbs : List (String × List (Arg Icelandic.Case)) :=
  entries.map (fun e ↦ (e.2.form, e.1)) ++ [("óska (transitive)", Thematic.oskaTransitive)]

/-- The German verbs as the rows name them. -/
def germanVerbs : List (String × List (Arg German.Case)) :=
  [(German.Verbs.helfen.form, Thematic.helfen), ("aufnehmen", Thematic.lesen),
    ("verhaften", Thematic.lesen), ("lesen", Thematic.lesen),
    ("gefallen", Thematic.gefallen), ("übel sein", Thematic.uebelSein),
    ("abhören", Thematic.abhoeren)]

/-- The voices as the rows name them. -/
def voiceTable : List (String × Voice) := [("active", .active), ("passive", .passive)]

/-- The roles as the rows name them. -/
def roleTable : List (String × ThetaRole) :=
  [("agent", .agent), ("theme", .theme), ("goal", .goal), ("source", .source),
    ("experiencer", .experiencer)]

/-- The Icelandic case arrays as the rows write them. -/
def icelandicCases : List (String × List Icelandic.Case) :=
  [("", []), ("dat", [.dat]), ("gen", [.gen]), ("nom dat", [.nom, .dat]),
    ("nom gen", [.nom, .gen]), ("dat nom", [.dat, .nom]), ("acc acc", [.acc, .acc]),
    ("dat dat", [.dat, .dat]), ("dat gen", [.dat, .gen]), ("nom acc dat", [.nom, .acc, .dat]),
    ("nom acc gen", [.nom, .acc, .gen]), ("nom dat acc", [.nom, .dat, .acc]),
    ("nom dat dat", [.nom, .dat, .dat]), ("nom dat gen", [.nom, .dat, .gen])]

/-- The German case arrays as the rows write them. -/
def germanCases : List (String × List German.Case) :=
  [("dat", [.dat]), ("nom acc", [.nom, .acc]), ("nom acc acc", [.nom, .acc, .acc])]

/-- A row attesting a case array, as the thematic structure, the voice and the array, the verb
and the cases named by the tables of its language. -/
def ofCasesRow {C : Type} (verbs : List (String × List (Arg C)))
    (cases : List (String × List C)) (ex : Datum) : Option (List (Arg C) × Voice × List C) := do
  let t ← ex.parse? "verb" verbs
  let v ← ex.parse? "voice" voiceTable
  let cs ← ex.parse? "cases" cases
  pure (t, v, cs)

/-- A row applying a subjecthood test to an argument, as the thematic structure, the voice
and the role tested. -/
def ofTestRow {C : Type} (verbs : List (String × List (Arg C))) (ex : Datum) :
    Option (List (Arg C) × Voice × ThetaRole) := do
  let t ← ex.parse? "verb" verbs
  let v ← ex.parse? "voice" voiceTable
  let ρ ← ex.parse? "tested" roleTable
  pure (t, v, ρ)

theorem ofRow_isSome : ∀ ex ∈ Examples.all,
    (ex.language = "icel1247" →
      ((ex.feature? "cases").isSome → (ofCasesRow icelandicVerbs icelandicCases ex).isSome) ∧
      ((ex.feature? "tested").isSome → (ofTestRow icelandicVerbs ex).isSome)) ∧
    (ex.language = "stan1295" →
      ((ex.feature? "cases").isSome → (ofCasesRow germanVerbs germanCases ex).isSome) ∧
      ((ex.feature? "tested").isSome → (ofTestRow germanVerbs ex).isSome)) := by
  decide

theorem rows_cases :
    (∀ ex ∈ Examples.all, ∀ r ∈ ofCasesRow icelandicVerbs icelandicCases ex,
      r.2.2 ∈ icelandic.arrays r.1 r.2.1) ∧
    ∀ ex ∈ Examples.all, ∀ r ∈ ofCasesRow germanVerbs germanCases ex,
      r.2.2 ∈ german.arrays r.1 r.2.1 := by
  decide

/-- Each subjecthood judgment of either language is acceptable exactly when the argument tested
is assigned SUBJ, §§2, 3.1 and 5. -/
theorem rows_subject :
    (∀ ex ∈ Examples.all, ∀ r ∈ ofTestRow icelandicVerbs ex,
      (ex.judgment = .acceptable ↔ icelandic.IsSubject r.1 r.2.1 r.2.2)) ∧
    ∀ ex ∈ Examples.all, ∀ r ∈ ofTestRow germanVerbs ex,
      (ex.judgment = .acceptable ↔ german.IsSubject r.1 r.2.1 r.2.2) := by
  decide

end ZaenenMalingThrainsson1985
