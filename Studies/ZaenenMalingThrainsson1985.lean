module

public import Linglib.Fragments.Icelandic.Verbs
public import Linglib.Data.Examples.ZaenenMalingThrainsson1985

/-!
# Zaenen, Maling and Thráinsson (1985): Case and grammatical functions

This file formalizes [zaenen-maling-thrainsson-1985]'s account of Icelandic case. A verb's
arguments are thematic roles, some of which the verb marks with an idiosyncratic case
(`Arg`); the association principles map the roles onto the grammatical functions SUBJ, OBJ
and 2OBJ, agents to SUBJ and case-marked themes to the lowest function available, and the
functions are the linear positions (`associations`). The passive is an operation on
functions, not on cases or roles: SUBJ is suppressed and OBJ becomes SUBJ (`GF.passive`).
Only afterwards does default case marking give the highest function without a case the
nominative and the next the accusative (`surfaceCase`), so idiosyncratic case survives the
passive (`surfaceCase_lexical`) while the accusative of an object does not.

The consequences the paper draws are theorems over the fragment. Every case array of
`Fragments.Icelandic.Verbs` that the paper discusses is derived from its thematic structure
(`fragment_cases`). A dative subject leaves the nominative to its object (*þykja*), and the
passive of *hjálpa* has a dative subject and no nominative at all. A dative–accusative verb
gives its theme and its goal either function, so *gefa* has two passives, the dative subject
with a nominative retained object and the nominative subject with a dative object
(`gefa_passives`), where the other ditransitives have one (`lofa_passive`); and a genitive
theme passivizes exactly when it is the only object, since with a goal beside it the lowest
function is 2OBJ (`oska_passive`). The seven subjecthood tests of §2 target SUBJ, whatever
its case: each of the paper's judgments on raising, reflexivization, inversion, extraction,
postposing, ellipsis and control is acceptable exactly when the argument tested is assigned
SUBJ (`rows_subject`), and each attested case array is one the principles derive
(`rows_cases`).

## Implementation notes

The paper names the roles Agent, Theme, Goal and Source; the dative and accusative
subjects of *þykja*, *finnast*, *sakna* and *vanta* it calls oblique subjects without a
role, and `experiencer` is the label under which principle (61a) assigns them their
function. Principle (61a) is read as assigning the first role SUBJ and leaving the object
functions to the remaining roles in either order unless (61c) fixes them, which is the
paper's dual association for *gefa* and keeps the nominative theme of *þykja* an object,
as the tests of §2 require. A third function without idiosyncratic case receives no default
case; the paper's ditransitives never present one.

## References

* [zaenen-maling-thrainsson-1985]
-/

@[expose] public section

namespace ZaenenMalingThrainsson1985

open Icelandic.Verbs ZaenenMalingThrainsson1985.Examples

/-! ### Thematic structure and grammatical functions -/

/-- The thematic roles. -/
inductive Role
  | agent
  | theme
  | goal
  | source
  | experiencer
  deriving DecidableEq, Repr

/-- An argument at thematic structure: its role and the idiosyncratic case the verb assigns
it, if any, as in the paper's (60). -/
structure Arg where
  role : Role
  lexicalCase : Option Icelandic.Case := none
  deriving DecidableEq, Repr

/-- The grammatical functions a bare NP argument may bear. -/
inductive GF
  | subj
  | obj
  | obj2
  deriving DecidableEq, Repr

/-- The functions available to `n` arguments, highest first, (61a). -/
def GF.available (n : ℕ) : List GF := [.subj, .obj, .obj2].take n

/-- The position of a function in the hierarchy. -/
def GF.rank : GF → ℕ
  | .subj => 0
  | .obj => 1
  | .obj2 => 2

/-- The lowest function available to `n` arguments. -/
def GF.lowest (n : ℕ) : Option GF := (GF.available n).getLast?

/-- An association of the arguments, in order, with functions. -/
abbrev Association := List GF

/-- The association satisfies the principles: the first role bears SUBJ (61a), agents bear
SUBJ (61b), and a case-marked theme the lowest function available (61c). -/
def Association.Valid (t : List Arg) (a : Association) : Prop :=
  a.head? = (GF.available t.length).head? ∧
    ∀ p ∈ t.zip a, (p.1.role = .agent → p.2 = .subj) ∧
      (p.1.role = .theme → p.1.lexicalCase.isSome → some p.2 = GF.lowest t.length)

instance (t : List Arg) (a : Association) : Decidable (a.Valid t) :=
  inferInstanceAs (Decidable (_ ∧ ∀ p ∈ _, _ ∧ _))

/-- `x` inserted at each position of a list. -/
def insertions (x : GF) : List GF → List (List GF)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertions x ys).map (y :: ·)

/-- The permutations of a list, by structural recursion so that `decide` can run them. -/
def perms : List GF → List (List GF)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (insertions x)

/-- The associations the principles allow: the assignments of the available functions to
the arguments, one each (61a), that satisfy (61b) and (61c). -/
def associations (t : List Arg) : List Association :=
  (perms (GF.available t.length)).filter (·.Valid t)

/-! ### Passive and default case -/

/-- The voices. -/
inductive Voice
  | active
  | passive
  deriving DecidableEq, Repr

/-- The passive on functions, (53): SUBJ is suppressed and OBJ becomes SUBJ. -/
def GF.passive : GF → Option GF
  | .subj => none
  | .obj => some .subj
  | .obj2 => some .obj2

/-- The function an argument bears in a voice. -/
def GF.inVoice (g : GF) : Voice → Option GF
  | .active => some g
  | .passive => g.passive

/-- The arguments with the functions they bear in a voice. -/
def realize (t : List Arg) (a : Association) (v : Voice) : List (Arg × Option GF) :=
  (t.zip a).map fun p ↦ (p.1, p.2.inVoice v)

/-- The functions without idiosyncratic case that outrank `g`. -/
def unmarkedAbove (r : List (Arg × Option GF)) (g : GF) : ℕ :=
  (r.filter fun p ↦ p.1.lexicalCase.isNone ∧ ∃ h ∈ p.2, h.rank < g.rank).length

/-- The surface case of an argument bearing a function: its idiosyncratic case if it has
one, else by default the nominative if no unmarked function outranks it and the accusative
if one does, (61d). -/
def surfaceCase (r : List (Arg × Option GF)) (p : Arg × Option GF) : Option Icelandic.Case :=
  p.2.bind fun g ↦
    p.1.lexicalCase.orElse fun _ ↦
      match unmarkedAbove r g with
      | 0 => some .nom
      | 1 => some .acc
      | _ => none

theorem surfaceCase_lexical {r : List (Arg × Option GF)} {x : Arg} {g : GF} {c : Icelandic.Case}
    (h : x.lexicalCase = some c) : surfaceCase r (x, some g) = some c := by
  simp [surfaceCase, h]

/-- The case array: the subject's case and then the objects' in the order of their functions,
the immediately postverbal NP the OBJ. -/
def cases (r : List (Arg × Option GF)) : List Icelandic.Case :=
  ([GF.subj, .obj, .obj2].filterMap fun g ↦ r.find? (·.2 = some g)).filterMap (surfaceCase r)

/-- The case arrays a thematic structure yields in a voice, one per association. -/
def arrays (t : List Arg) (v : Voice) : List (List Icelandic.Case) :=
  (associations t).map fun a ↦ cases (realize t a v)

/-- The argument with a role bears SUBJ under some association in the voice. -/
def IsSubject (t : List Arg) (v : Voice) (ρ : Role) : Prop :=
  ∃ a ∈ associations t, (realize t a v).any fun p ↦ p.1.role = ρ ∧ p.2 = some .subj

instance (t : List Arg) (v : Voice) (ρ : Role) : Decidable (IsSubject t v ρ) :=
  inferInstanceAs (Decidable (∃ a ∈ _, _))

/-! ### The verbs -/

/-! The thematic structures of the paper's verbs: (58), (60), (63), (67), (76) and Table I. -/

namespace Thematic

def dansa : List Arg := [⟨.agent, none⟩]
def kyssa : List Arg := [⟨.agent, none⟩, ⟨.theme, none⟩]
def hjalpa : List Arg := [⟨.agent, none⟩, ⟨.theme, some .dat⟩]
def sakna : List Arg := [⟨.experiencer, none⟩, ⟨.theme, some .gen⟩]
def thykja : List Arg := [⟨.experiencer, some .dat⟩, ⟨.theme, none⟩]
def vanta : List Arg := [⟨.experiencer, some .acc⟩, ⟨.theme, some .acc⟩]
def gefa : List Arg := [⟨.agent, none⟩, ⟨.theme, none⟩, ⟨.goal, some .dat⟩]
def leyna : List Arg := [⟨.agent, none⟩, ⟨.theme, some .dat⟩, ⟨.source, none⟩]
def bidja : List Arg := [⟨.agent, none⟩, ⟨.theme, some .gen⟩, ⟨.goal, none⟩]
def lofa : List Arg := [⟨.agent, none⟩, ⟨.theme, some .dat⟩, ⟨.goal, some .dat⟩]
def oska : List Arg := [⟨.agent, none⟩, ⟨.theme, some .gen⟩, ⟨.goal, some .dat⟩]
/-- *óska* as a simple transitive, its goal absent, (67). -/
def oskaTransitive : List Arg := [⟨.agent, none⟩, ⟨.theme, some .gen⟩]

end Thematic

/-- The paper's verbs with the fragment entries they realize. -/
def entries : List (List Arg × Icelandic.Verbs.Verb) :=
  [(Thematic.dansa, dansa), (Thematic.kyssa, kyssa), (Thematic.hjalpa, hjalpa),
   (Thematic.sakna, sakna), (Thematic.thykja, thykja), (Thematic.thykja, finnast),
   (Thematic.vanta, vanta), (Thematic.gefa, gefa), (Thematic.gefa, segja),
   (Thematic.leyna, leyna), (Thematic.leyna, svipta), (Thematic.bidja, bidja),
   (Thematic.lofa, lofa), (Thematic.lofa, skila), (Thematic.oska, oska)]

theorem fragment_cases : ∀ e ∈ entries, e.2.cases ∈ arrays e.1 .active := by decide

-- (62b)
theorem thykja_arrays : arrays Thematic.thykja .active = [[.dat, .nom]] := by decide

-- (11a)
theorem hjalpa_passive : arrays Thematic.hjalpa .passive = [[.dat]] := by decide

/-- A dative–accusative verb has two passives: the goal as dative subject with the theme a
nominative retained object, and the theme as nominative subject, (44). -/
theorem gefa_passives :
    let ps := arrays Thematic.gefa .passive
    [.dat, .nom] ∈ ps ∧ [.nom, .dat] ∈ ps ∧ ps.length = 2 := by
  decide

/-- A dative–dative verb has one passive, its goal the subject, (42). -/
theorem lofa_passive : arrays Thematic.lofa .passive = [[.dat, .dat]] := by decide

/-- The genitive theme of *óska* passivizes as the only object and not beside a goal, (68). -/
theorem oska_passive :
    IsSubject Thematic.oskaTransitive .passive .theme ∧
      ¬ IsSubject Thematic.oska .passive .theme := by
  decide

-- (9a)
theorem dansa_passive : arrays Thematic.dansa .passive = [[]] := by decide

/-! ### The rows -/

/-- The verbs as the rows name them. -/
def verbTable : List (String × List Arg) :=
  entries.map (fun e ↦ (e.2.form, e.1)) ++ [("óska (transitive)", Thematic.oskaTransitive)]

/-- The voices as the rows name them. -/
def voiceTable : List (String × Voice) := [("active", .active), ("passive", .passive)]

/-- The roles as the rows name them. -/
def roleTable : List (String × Role) :=
  [("agent", .agent), ("theme", .theme), ("goal", .goal), ("source", .source),
    ("experiencer", .experiencer)]

/-- The case arrays as the rows write them. -/
def casesTable : List (String × List Icelandic.Case) :=
  [("", []), ("dat", [.dat]), ("gen", [.gen]), ("nom dat", [.nom, .dat]),
    ("nom gen", [.nom, .gen]), ("dat nom", [.dat, .nom]), ("acc acc", [.acc, .acc]),
    ("dat dat", [.dat, .dat]), ("dat gen", [.dat, .gen]), ("nom acc dat", [.nom, .acc, .dat]),
    ("nom acc gen", [.nom, .acc, .gen]), ("nom dat acc", [.nom, .dat, .acc]),
    ("nom dat dat", [.nom, .dat, .dat]), ("nom dat gen", [.nom, .dat, .gen])]

/-- A row attesting a case array, as the thematic structure, the voice and the array. -/
def ofCasesRow (ex : Datum) : Option (List Arg × Voice × List Icelandic.Case) := do
  let t ← ex.parse? "verb" verbTable
  let v ← ex.parse? "voice" voiceTable
  let cs ← ex.parse? "cases" casesTable
  pure (t, v, cs)

/-- A row applying a subjecthood test to an argument, as the thematic structure, the voice
and the role tested. -/
def ofTestRow (ex : Datum) : Option (List Arg × Voice × Role) := do
  let t ← ex.parse? "verb" verbTable
  let v ← ex.parse? "voice" voiceTable
  let ρ ← ex.parse? "tested" roleTable
  pure (t, v, ρ)

theorem ofCasesRow_isSome :
    ∀ ex ∈ Examples.all, (ex.feature? "cases").isSome → (ofCasesRow ex).isSome := by
  decide

theorem ofTestRow_isSome :
    ∀ ex ∈ Examples.all, (ex.feature? "tested").isSome → (ofTestRow ex).isSome := by
  decide

theorem rows_cases :
    ∀ ex ∈ Examples.all, ∀ r ∈ ofCasesRow ex, r.2.2 ∈ arrays r.1 r.2.1 := by
  decide

theorem rows_subject :
    ∀ ex ∈ Examples.all, ∀ r ∈ ofTestRow ex,
      (ex.judgment = .acceptable ↔ IsSubject r.1 r.2.1 r.2.2) := by
  decide

end ZaenenMalingThrainsson1985
