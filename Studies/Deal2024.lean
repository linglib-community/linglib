module

public import Linglib.Syntax.Agreement.PersonCaseConstraint
public import Linglib.Syntax.Minimalist.Probe.Agree
public import Linglib.Syntax.Agreement.PersonSegment
public import Studies.CoonKeine2021
public import Studies.Haspelmath2021
public import Linglib.Syntax.Clause.Scenario
public import Linglib.Syntax.Person.Class
public import Linglib.Data.Examples.Deal2024
public import Linglib.Data.Examples.Readers

/-!
# Deal (2024): Interaction, Satisfaction, and the PCC

Deal derives the Person Case Constraint from a probe specified by an interaction condition, the
features it copies from a goal, and a satisfaction condition, the feature that halts its search,
with no uninterpretable features anywhere. The probe meets the direct object first, so a direct
object that satisfies it bleeds Agree with the indirect object: satisfaction by [PART] gives the
strong PCC, by [SPKR] the me-first PCC, and an insatiable probe no PCC. Dynamic interaction lets
a feature copied from the direct object narrow the interaction condition, so that the indirect
object must bear it too, which gives the weak and the strictly descending PCC. A probe that
meets the indirect object first yields the reverse PCC of section 6.2.

## Implementation notes

The features of the geometry (7) are the person segments of `Phi.PersonSegment`, [φ] its
root `π`, [PART] `participant`, [SPKR] `speaker` and [ADDR] `addressee`, so a second person and an
inclusive first person bear [ADDR]. The interaction condition is the set of features copied so
far, a goal being visible when it bears them all, which is the set conception the paper's
footnote 10 allows; the paper's single interaction feature is the most specific one copied.
Table (1) has no reflexive cells, so the classification of grammars ranges over its six cells,
`PCC.distinctPairs`; the mechanism's verdicts on reflexive combinations are not stated.

## References

* [deal-2024]
* [haspelmath-2021]
* [pancheva-zubizarreta-2018]
* [coon-keine-2021]
-/

@[expose] public section

namespace Deal2024

open Minimalist Phi PersonSegment
open Clause (Scenario)

/-! ### Probes and their runs -/

/-- A grammar fixes the satisfaction condition, none for an insatiable probe, and the features
that interact dynamically, copied into the interaction condition when a goal bears them. -/
structure Grammar where
  satisfaction : Option PersonSegment
  dynamic : Finset PersonSegment
  deriving DecidableEq, Fintype

/-- The run of grammar `g`'s probe over goals paired with their positions. The state is the
interaction condition, the features copied into it so far, starting from [φ]. A goal is visible
when it bears them all; interacting with it copies its dynamic features into the condition, (44)
and (45); and only a visible goal bearing the satisfaction feature satisfies the probe, (8b). -/
def run (g : Grammar) (goals : List Person) :
    Probe.Result (Person × ℕ) (Finset PersonSegment) :=
  Probe.Dynamic.agree
    (fun int ↦ ⟨fun t ↦ decide (int ⊆ spec t.1),
      fun t ↦ decide (int ⊆ spec t.1) && g.satisfaction.any (· ∈ spec t.1)⟩)
    (fun t int ↦ int ∪ g.dynamic ∩ spec t.1) (fun _ int ↦ int) {.pi} goals.zipIdx

/-- A clitic combination ⟨IO, DO⟩ is licit when the probe, meeting the direct object first,
interacts with both objects, section 3.1; the reverse PCC of section 6.2, where the probe meets
the indirect object first, is licitness of the swapped pair. -/
def Licit (g : Grammar) (s : Scenario Person) : Prop :=
  (run g [s.low, s.high]).interacted.map (·.2) = [0, 1]

instance (g : Grammar) : DecidablePred (Licit g) := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-! ### The grammars -/

/-- The strong PCC is the probe [INT:φ, SAT:PART], (15). -/
def strong : Grammar := ⟨some .participant, ∅⟩

/-- The me-first PCC is the probe [INT:φ, SAT:SPKR], (33). -/
def meFirst : Grammar := ⟨some .speaker, ∅⟩

/-- The insatiable probe [INT:φ, SAT:-] of Ubykh and Moro derives no PCC. -/
def noPCC : Grammar := ⟨none, ∅⟩

/-- The weak PCC is an insatiable probe with [PART] interacting dynamically, (38). -/
def weak : Grammar := ⟨none, {.participant}⟩

/-- The strictly descending PCC is [SAT:SPKR] with [PART] interacting dynamically, (50). -/
def strictlyDescending : Grammar := ⟨some .speaker, {.participant}⟩

/-- The you-first PCC is [SAT:ADDR], section 6.1. -/
def youFirst : Grammar := ⟨some .addressee, ∅⟩

/-- The A-descending PCC is [SAT:ADDR] with [PART] interacting dynamically, section 6.1. -/
def aDescending : Grammar := ⟨some .addressee, {.participant}⟩

/-! ### The typology -/

/-- The rank of a person on the hierarchy 2 > 1 > 3 of the A-descending PCC. -/
def addresseeRank : Person → ℕ
  | .second => 2
  | .first | .firstInclusive | .firstExclusive => 1
  | .third => 0

/-- The PCC varieties are the four of table (1), the two the feature [ADDR] adds, and none. -/
inductive PCCType where
  | strong
  | weak
  | meFirst
  | strictlyDescending
  | youFirst
  | aDescending
  | none
  deriving DecidableEq, Repr, Fintype

/-- The descriptive statements of (2) and section 6.1, one per variety, say that the direct
object must be third person; that if there is a third person, the direct object must be third
person; that if there is a first person, it must be the indirect object; that the indirect object
must outrank the direct object on 1 > 2 > 3; that if there is a second person, it must be the
indirect object; that the indirect object must outrank the direct object on 2 > 1 > 3; and
nothing. -/
def PCCType.Licit : PCCType → Scenario Person → Prop
  | .strong, s => ¬ s.low.IsSAP
  | .weak, s => ¬ s.high.IsSAP → ¬ s.low.IsSAP
  | .meFirst, s => ¬ s.low.IncludesSpeaker
  | .strictlyDescending, s => s.low.prominence < s.high.prominence
  | .youFirst, s => addressee ∉ spec s.low
  | .aDescending, s => addresseeRank s.low < addresseeRank s.high
  | .none, _ => True

instance : (t : PCCType) → DecidablePred t.Licit
  | .strong, _ => inferInstanceAs (Decidable (¬ _))
  | .weak, _ => inferInstanceAs (Decidable (_ → _))
  | .meFirst, _ => inferInstanceAs (Decidable (¬ _))
  | .strictlyDescending, _ => inferInstanceAs (Decidable (_ < _))
  | .youFirst, _ => inferInstanceAs (Decidable (¬ _))
  | .aDescending, _ => inferInstanceAs (Decidable (_ < _))
  | .none, _ => inferInstanceAs (Decidable True)

/-- The strictly descending PCC holds of an IO–DO combination exactly when the scenario is
downstream on 1 > 2 > 3. -/
theorem strictlyDescending_iff_downstream (s : Scenario Person) :
    PCCType.Licit .strictlyDescending s ↔ (s.map Person.prominence).kind = .downstream :=
  (Scenario.kind_eq_downstream_iff (s := s.map Person.prominence)).symm

/-- The A-descending PCC holds exactly when the scenario is downstream on 2 > 1 > 3. -/
theorem aDescending_iff_downstream (s : Scenario Person) :
    PCCType.Licit .aDescending s ↔ (s.map addresseeRank).kind = .downstream :=
  (Scenario.kind_eq_downstream_iff (s := s.map addresseeRank)).symm

/-- A variety codes a combination as the clitic cluster where it is licit and as the longer
repair where it is not. -/
def PCCType.coding (t : PCCType) (s : Scenario Person) : ℕ :=
  if t.Licit s then 0 else 1

/-- Under a person ranking, a cell of table (1) is more usual than another when its kind is
higher. -/
def MoreUsualOn {β : Type*} [LinearOrder β] (rank : Person → β) (s t : Scenario Person) : Prop :=
  s ∈ PCC.distinctPairs ∧ t ∈ PCC.distinctPairs ∧ (t.map rank).kind < (s.map rank).kind

instance {β : Type*} [LinearOrder β] (rank : Person → β) (s t : Scenario Person) :
    Decidable (MoreUsualOn rank s t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Under 1 > 2 > 3, the varieties satisfying [haspelmath-2021]'s universal (section 7.1) over table
(1) are the strong, weak, me-first, strictly descending and absent PCCs. -/
theorem universal5_prominence (t : PCCType) :
    Haspelmath2021.RoleReferenceUniversal (MoreUsualOn Person.prominence) t.coding ↔
      t ∈ [PCCType.strong, .weak, .meFirst, .strictlyDescending, .none] := by
  revert t; decide +kernel

/-- Under the ranking 2 > 1 > 3 it is the strong, weak, you-first and A-descending varieties
that obey the scenario universal; me-first and strictly descending ban the then-downstream
`2 > 1`. -/
theorem universal5_addressee (t : PCCType) :
    Haspelmath2021.RoleReferenceUniversal (MoreUsualOn addresseeRank) t.coding ↔
      t ∈ [PCCType.strong, .weak, .youFirst, .aDescending, .none] := by
  revert t; decide +kernel

theorem participant_third_licit (t : PCCType) (io : Person) (h : io.IsSAP) :
    t.Licit ⟨io, .third⟩ := by
  revert h; cases t <;> cases io <;> decide

-- (45) [haspelmath-2021]
theorem strong_iff_greekT (s : Scenario Person) :
    PCCType.Licit .strong s ↔ Haspelmath2021.greekT (s.map Person.toClass) = 0 := by
  revert s; decide

def PCCType.all : List PCCType :=
  [.strong, .weak, .meFirst, .strictlyDescending, .youFirst, .aDescending, .none]

/-- The variety a grammar derives is the one whose statement it matches on the six cells. -/
def Grammar.pattern (g : Grammar) : Option PCCType :=
  PCCType.all.find? fun t ↦ decide (∀ s ∈ PCC.distinctPairs, Licit g s ↔ t.Licit s)

/-- Table (57), the typology by satisfaction condition and dynamic interaction features, with
table (53) as its rows and columns without [ADDR]; a probe satisfied by [φ] Agrees with the
direct object alone and derives no variety, and dynamic [φ] changes nothing. -/
def table57 (g : Grammar) : Option PCCType :=
  match g.satisfaction with
  | some .pi => none
  | some .participant => some .strong
  | some .speaker =>
      some (if .addressee ∈ g.dynamic then .strong
        else if .participant ∈ g.dynamic then .strictlyDescending else .meFirst)
  | some .addressee =>
      some (if .speaker ∈ g.dynamic then .strong
        else if .participant ∈ g.dynamic then .aDescending else .youFirst)
  | none =>
      some (if .speaker ∈ g.dynamic ∧ .addressee ∈ g.dynamic then .strong
        else if .participant ∈ g.dynamic ∧ .speaker ∈ g.dynamic then .strictlyDescending
        else if .participant ∈ g.dynamic ∧ .addressee ∈ g.dynamic then .aDescending
        else if .participant ∈ g.dynamic then .weak
        else if .speaker ∈ g.dynamic then .meFirst
        else if .addressee ∈ g.dynamic then .youFirst
        else .none)

/-- Every grammar derives the variety that table (57) gives it, so the runs derive the tables
((53)). -/
theorem typology (g : Grammar) : g.pattern = table57 g := by
  revert g
  decide +kernel

theorem licit_of_sat_part (d : Finset PersonSegment) (s : Scenario Person) :
    Licit ⟨some .participant, d⟩ s ↔ Licit strong s := by
  revert d s
  decide +kernel

theorem sd_off_diagonal_iff_outranks (s : Scenario Person)
    (h : s.high.prominence ≠ s.low.prominence) :
    Licit strictlyDescending s ↔ s.low.prominence < s.high.prominence := by
  revert s
  decide +kernel

/-! ### The competitors (section 7) -/

/-- On the six cells of table (1) the four varieties coincide with the P-Constraint grammars of
[pancheva-zubizarreta-2018], strictly descending with ultra-strong. -/
theorem agrees_with_pConstraint :
    ∀ s ∈ PCC.distinctPairs,
      (Licit strong s ↔ PCC.IsLicit PCC.strongGrammar s) ∧
        (Licit weak s ↔ PCC.IsLicit PCC.weakGrammar s) ∧
        (Licit meFirst s ↔ PCC.IsLicit PCC.meFirstGrammar s) ∧
        (Licit strictlyDescending s ↔ PCC.IsLicit PCC.ultraStrongGrammar s) := by
  decide +kernel

/-- On the six cells the four varieties coincide with the gluttony probes of
[coon-keine-2021], so a probe that stops too early and one that agrees too much draw the same
lines there. -/
theorem agrees_with_gluttony :
    ∀ s ∈ PCC.distinctPairs,
      (Licit strong s ↔ ¬ CoonKeine2021.PCCViolation CoonKeine2021.weakProbe true s) ∧
        (Licit weak s ↔ ¬ CoonKeine2021.PCCViolation CoonKeine2021.weakProbe false s) ∧
        (Licit meFirst s ↔ ¬ CoonKeine2021.PCCViolation CoonKeine2021.meFirstProbe false s) ∧
        (Licit strictlyDescending s ↔
          ¬ CoonKeine2021.PCCViolation CoonKeine2021.ultrastrongProbe false s) := by
  decide +kernel

/-! ### The rows -/

def personOf (e : Datum) (key : String) : Option Person :=
  match e.feature? key with
  | some "1" => some .first
  | some "2" => some .second
  | some "3" => some .third
  | _ => none

/-- The grammars of a row's language are listed by its pattern, Slovenian speakers having a strong
or a weak PCC. -/
def grammarsOf (e : Datum) : List Grammar :=
  match e.feature? "pattern" with
  | some "strong" => [strong]
  | some "weak" => [weak]
  | some "meFirst" => [meFirst]
  | some "strictlyDescending" => [strictlyDescending]
  | some "strongOrWeak" => [strong, weak]
  | _ => []

/-- Every clitic combination of the rows is accepted, by every speaker or, where speakers differ,
by those of the row's variety, exactly when the language's grammar licenses it, the probe meeting
the indirect object first in the reverse-PCC rows of Shapsug Adyghe and of Slovenian with the
direct object clitic first. -/
theorem rows :
    ∀ e ∈ Examples.all, ∀ g ∈ grammarsOf e, ∀ io ∈ personOf e "io", ∀ do_ ∈ personOf e "do",
      (.variable ≤ e.judgment ↔
        if e.feature? "preference" = some "io" then Licit g ⟨do_, io⟩ else Licit g ⟨io, do_⟩) := by
  decide +kernel

end Deal2024
