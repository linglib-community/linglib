module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Prod
public import Linglib.Syntax.Clause.Scenario
public import Linglib.Syntax.Person.Basic

/-!
# The Person Case Constraint

The Person Case Constraint restricts which combinations of indirect and direct object person a
clitic cluster can realize, the classic ban of French *me lui*. A combination is a scenario
(`Clause.Scenario`) of the indirect over the direct object. This file defines the four-parameter
P-Constraint grammars that generate the varieties (strong, ultra-strong, weak, super-strong,
me-first, and the predicted PG1–PG3), whose prominence thresholds are cuts on the entailment
chain [author] ⟹ [participant] ⟹ [proximate], denoting `Person.IncludesSpeaker` and
`Person.IsSAP`, so the person hierarchy enters as a theorem (`inherentlyMetBy_antitone`).
Grammars are preordered by inclusion of their licit regions (`licitFinset`).

Which mechanism enforces the constraint is left open here: a morphological filter, φ-Agree, and
perspectival semantics have all been proposed. The rival accounts are formalized in their study
files and compared cell by cell against these grammars.

## Main declarations

* `PCC.Grammar`, `PCC.IsLicit`: the P-Constraint grammars and the combinations they license.
* `PCC.cliticPairs`, `PCC.distinctPairs`: the combinations of the person tripartition, with and
  without the reflexive diagonal.

## References

* [bonet-1991]
* [nevins-2007]
* [pancheva-zubizarreta-2018]
* [bejar-rezac-2009]
* [coon-keine-2021]
* [deal-2024]
-/

@[expose] public section

namespace PCC

open Clause (Scenario)

/-! ### Prominence thresholds: cuts on the [author] ⟹ [participant] ⟹ [proximate] chain -/

/-- The prominence a grammar requires of its IO is `proximate` (the default), `participant`, or
`author`. -/
inductive ProminenceThreshold where
  | proximate | participant | author
  deriving DecidableEq, Repr, Fintype

/-- The restrictiveness chain `proximate < participant < author`. -/
instance : LinearOrder ProminenceThreshold :=
  LinearOrder.lift' (·.ctorIdx) (by decide)

/-- A person meets a prominence threshold by its own features, speech-act participants meeting
`proximate` and `participant` and the speaker `author`. A 3P meets `proximate` only
contextually (`IOSatisfiesProminence`). -/
def ProminenceThreshold.InherentlyMetBy : ProminenceThreshold → Person → Prop
  | .proximate | .participant => Person.IsSAP
  | .author => Person.IncludesSpeaker

instance : (t : ProminenceThreshold) → DecidablePred t.InherentlyMetBy
  | .proximate | .participant => inferInstanceAs (DecidablePred Person.IsSAP)
  | .author => inferInstanceAs (DecidablePred Person.IncludesSpeaker)

theorem ProminenceThreshold.inherentlyMetBy_antitone (p : Person) :
    Antitone (InherentlyMetBy · p) := fun t₁ t₂ ht hm => by
  revert ht hm
  cases p <;> cases t₁ <;> cases t₂ <;> decide

/-! ### The PCC grammar -/

/-- A PCC grammar sets the four P-Constraint parameters, the prominence threshold,
P-Uniqueness, P-Primacy, and the domain restriction. P-Primacy presupposes P-Uniqueness
(`primacy_le_uniqueness`); field defaults are the paper's defaults, so `{}` is the strong
PCC. -/
structure Grammar where
  /-- The threshold of P-Prominence, which the IO must meet. -/
  prominence : ProminenceThreshold := .proximate
  /-- Under P-Uniqueness at most one DP may bear the required prominence. -/
  uniqueness : Bool := true
  /-- Under P-Primacy a [+author] IO wins a tie. -/
  primacy : Bool := false
  /-- On a restricted domain the constraint applies only where a prominence-bearing DP is
  present. -/
  restrictedDomain : Bool := false
  /-- P-Primacy presupposes active P-Uniqueness. -/
  primacy_le_uniqueness : primacy ≤ uniqueness := by decide

/-! ### Named grammars ([pancheva-zubizarreta-2018] (31)–(34)) -/

/-- The strong PCC keeps all defaults, so the DO must be 3P. -/
def strongGrammar : Grammar := {}
/-- The ultra-strong PCC adds P-Primacy, so ⟨1,2⟩ is licit and ⟨2,1⟩ not. -/
def ultraStrongGrammar : Grammar := { primacy := true }
/-- The weak PCC drops P-Uniqueness, so SAPs may co-occur. -/
def weakGrammar : Grammar := { uniqueness := false }
/-- The super-strong PCC has `participant` prominence, so the IO must be a SAP and ⟨3,3⟩ is
banned. -/
def superStrongGrammar : Grammar := { prominence := .participant }
/-- The me-first PCC has `author` prominence on a restricted domain. -/
def meFirstGrammar : Grammar := { prominence := .author, restrictedDomain := true }
/-- The predicted PG1 has `participant` prominence with P-Primacy. -/
def pg1Grammar : Grammar := { prominence := .participant, primacy := true }
/-- The predicted PG2 has `participant` prominence without P-Uniqueness. -/
def pg2Grammar : Grammar := { prominence := .participant, uniqueness := false }
/-- The predicted PG3 has `author` prominence on the unrestricted domain. -/
def pg3Grammar : Grammar := { prominence := .author }

/-! ### Subpredicates, the four clauses of (12) -/

/-- (12b) The IO meets P-Prominence inherently, or, under a `proximate` threshold only, by
contextual marking when paired with another non-proximate 3P. -/
def IOSatisfiesProminence (g : Grammar) (s : Scenario Person) : Prop :=
  g.prominence.InherentlyMetBy s.high ∨
    (g.prominence = .proximate ∧
     ¬ g.prominence.InherentlyMetBy s.high ∧ ¬ g.prominence.InherentlyMetBy s.low)

instance (g : Grammar) : DecidablePred (IOSatisfiesProminence g) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- (12c) The DO does not also inherently meet P-Prominence. -/
def UniquenessSatisfied (g : Grammar) (do_ : Person) : Prop :=
  ¬ g.prominence.InherentlyMetBy do_

instance (g : Grammar) (do_ : Person) : Decidable (UniquenessSatisfied g do_) :=
  inferInstanceAs (Decidable (¬ _))

/-- (12d) A [+author] IO rescues an otherwise-blocking configuration when P-Primacy is on.

The rescue checks only the IO, so primacy-active grammars license ⟨1,1⟩, where the paper's
descriptive statement (14d), that the DO must be 2P or 3P, would forbid it (the paper never walks
the mechanism through ⟨1,1⟩ for the [+proximate] family). The permissive reading is deliberate:
rival probe-based accounts part ways with the P-Constraint at exactly this cell, which
[deal-2024]'s table (1) leaves out. -/
def PrimacyRescues (g : Grammar) (io : Person) : Prop :=
  g.primacy ∧ io.IncludesSpeaker

instance (g : Grammar) (io : Person) : Decidable (PrimacyRescues g io) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A person is inherently proximate iff it is a speech-act participant; a 3P is proximate only
contextually. -/
def IsInherentlyProximate (p : Person) : Prop :=
  ProminenceThreshold.proximate.InherentlyMetBy p

instance : DecidablePred IsInherentlyProximate := fun p =>
  inferInstanceAs (Decidable (ProminenceThreshold.proximate.InherentlyMetBy p))

/-- (12a) A combination is domain-exempt on a restricted domain when no DP bears the prominence
feature. The restriction presupposes an argument matching the P-Prominence value
([pancheva-zubizarreta-2018] §4.5, the restricted application "matches the feature value set in
P-Prominence"; for me-first, ApplPs with a [+author] argument). -/
def DomainExempt (g : Grammar) (s : Scenario Person) : Prop :=
  g.restrictedDomain ∧
    ¬ g.prominence.InherentlyMetBy s.high ∧ ¬ g.prominence.InherentlyMetBy s.low

instance (g : Grammar) : DecidablePred (DomainExempt g) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ### Licit person combinations -/

/-- A combination of IO over DO is licit under `g` when the domain restriction exempts it, or
the IO meets P-Prominence and, when P-Uniqueness is active, the DO does not compete or P-Primacy
rescues the tie. -/
def IsLicit (g : Grammar) (s : Scenario Person) : Prop :=
  DomainExempt g s ∨
    (IOSatisfiesProminence g s ∧
      (g.uniqueness → UniquenessSatisfied g s.low ∨ PrimacyRescues g s.high))

instance (g : Grammar) : DecidablePred (IsLicit g) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The persons of the tripartition, over which the typology is stated. -/
def persons : Finset Person := {.first, .second, .third}

/-- The prediction domain is the combinations of the tripartition. -/
def cliticPairs : Finset (Scenario Person) :=
  (persons ×ˢ persons).map Scenario.equivProd.symm.toEmbedding

/-- The combinations of distinct persons, without the reflexive diagonal. -/
def distinctPairs : Finset (Scenario Person) :=
  persons.offDiag.map Scenario.equivProd.symm.toEmbedding

/-- The person combinations `g` predicts licit. -/
def licitFinset (g : Grammar) : Finset (Scenario Person) :=
  {s ∈ cliticPairs | IsLicit g s}

@[simp] theorem mem_licitFinset (g : Grammar) (s : Scenario Person) :
    s ∈ licitFinset g ↔ s ∈ cliticPairs ∧ IsLicit g s := by simp [licitFinset]

/-! ### The typology as a preorder (entailment by licit-set inclusion)

The order is only a preorder, since distinct parameter settings can share a licit set: the
restricted-domain [+participant] grammar surfaces as the strong PCC
(`PanchevaZubizarreta2018.restricted_participant_surfaces_as_strong`). -/

instance : Preorder Grammar := Preorder.lift licitFinset

instance (g₁ g₂ : Grammar) : Decidable (g₁ ≤ g₂) :=
  inferInstanceAs (Decidable (licitFinset g₁ ⊆ licitFinset g₂))

theorem le_iff_isLicit_imp (g₁ g₂ : Grammar) :
    g₁ ≤ g₂ ↔ ∀ s ∈ cliticPairs, IsLicit g₁ s → IsLicit g₂ s := by
  show licitFinset g₁ ⊆ licitFinset g₂ ↔ _
  simp +contextual [Finset.subset_iff]

end PCC
