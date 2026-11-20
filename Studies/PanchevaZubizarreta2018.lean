module

public import Linglib.Syntax.Person.CaseConstraint
public import Linglib.Discourse.LogophoricRole
public import Linglib.Syntax.Feature.Person.Features
public import Linglib.Fragments.Romance.Italian.Pronouns
public import Linglib.Fragments.Romance.Spanish.Clitics

/-!
# Pancheva and Zubizarreta (2018): The Person Case Constraint

This file formalizes the predictions of Pancheva and Zubizarreta's P-Constraint, the
proposal that Person Case Constraint effects are the syntactic encoding of perspective: an
interpretable person feature on the applicative head marks the indirect object as the
point-of-view center of its domain, and a clitic combination is licit exactly when selecting
the indirect object as that center satisfies the constraint (`PConstraintSatisfied`, `IsLicit`).
The Person Hierarchy 1 > 2 > 3 is [derived from the count of positive person
features](##PanchevaZubizarreta2018.personHierarchy_from_features) rather than stipulated. The
constraint's four parameters, the prominence threshold, the domain of application, P-Uniqueness,
and P-Primacy, generate the five attested varieties, strong, ultra-strong, weak, super-strong,
and me-first, together with three predicted ones, and the grammars of four of them
[license the combinations of the descriptive
varieties](##PanchevaZubizarreta2018.isLicit_iff_variety). The three prominence values
correspond to Sells's logophoric roles pivot, self, and source
(`ProminenceThreshold.toLogophoricRole`), and a person meets a value by its own features when its
referents include a participant holding that role, the speaker being a source and the addressee a
self (`logophoricRole`).

## Implementation notes

The roles a participant holds are a lower set of Sells's hierarchy, recorded by its greatest
element, so the addressee, a self, is also a pivot. The paper says of the addressee that it can
be a pivot, and gives second person the feature [+proximate].

The Italian and Spanish clitic combinations are read off the Fragments, the French, Catalan,
Kambera, and Bulgarian ones off the parameter settings, since no clitic Fragment exists for
those languages. The paper's separation of the Clitic Logophoric Restriction from the PCC,
against the unification Charnavel and Mateu propose, the two phenomena sharing only
the point-of-view marking on the applicative head, is not represented: the restriction is a
semantic constraint outside this model.

## TODO

P-Primacy checks only the indirect object's [+author], so the ultra-strong grammar licenses the
⟨1, 1⟩ combination that the descriptive statement (14d) bans (`ultra_one_one_licensed`); the
paper does not walk the mechanism through that cell.

## References

* [pancheva-zubizarreta-2018]
* [sells-1987]
* [charnavel-mateu-2015]
-/

@[expose] public section

namespace PanchevaZubizarreta2018

open PCC
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

/-! ### Logophoric roles -/

/-- (46): the prominence values are the logophoric roles of [sells-1987] in the order of his
hierarchy, a `proximate` argument being at least a pivot, a `participant` at least a self, and an
`author` a source. -/
def ProminenceThreshold.toLogophoricRole : ProminenceThreshold ≃o LogophoricRole where
  toFun
    | .proximate => .pivot
    | .participant => .self
    | .author => .source
  invFun
    | .pivot => .proximate
    | .self => .participant
    | .source => .author
  left_inv := by decide
  right_inv := by decide
  map_rel_iff' := by decide

/-- The highest logophoric role a participant of the speech act holds: the speaker is a source,
and with it a self and a pivot, and the addressee is a self, and with it a pivot. -/
def logophoricRole : SpeechAct.Role → LogophoricRole
  | .speaker => .source
  | .addressee => .self

/-- A person meets a prominence threshold by its own features when every referent it covers
includes a participant holding the threshold's logophoric role. A 3P meets `proximate` only
contextually (`IOSatisfiesProminence`). -/
def ProminenceThreshold.InherentlyMetBy (t : ProminenceThreshold) (p : Person) : Prop :=
  ∀ s ∈ p.participantSets, ∃ x ∈ s, t.toLogophoricRole ≤ logophoricRole x

instance (t : ProminenceThreshold) : DecidablePred t.InherentlyMetBy := fun p ↦
  inferInstanceAs (Decidable (∀ s ∈ p.participantSets, ∃ x ∈ s, _ ≤ _))

theorem ProminenceThreshold.inherentlyMetBy_antitone (p : Person) :
    Antitone (InherentlyMetBy · p) := fun _ _ ht h s hs ↦
  let ⟨x, hx, hle⟩ := h s hs
  ⟨x, hx, (toLogophoricRole.monotone ht).trans hle⟩

-- (11): speech-act participants are [+proximate] and [+participant], the speaker [+author].
theorem ProminenceThreshold.inherentlyMetBy_iff {t : ProminenceThreshold} {p : Person} :
    t.InherentlyMetBy p ↔ if t = .author then p.IncludesSpeaker else p.IsSAP := by
  cases t <;> cases p <;> decide

/-! ### The grammars -/

/-- A grammar sets the four P-Constraint parameters, the prominence threshold, P-Uniqueness,
P-Primacy, and the domain restriction. P-Primacy presupposes P-Uniqueness
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

/-! ### The P-Constraint, the four clauses of (12) -/

/-- The applicative phase holds the indirect object introduced by Appl, the direct object inside
VP, and the argument selected as point-of-view center. -/
structure ApplDomain where
  io : Person
  do_ : Person
  povCenter : Person
  deriving DecidableEq

section PConstraint

variable (g : Grammar) (a : ApplDomain)

/-- (12b) The IO meets P-Prominence inherently, or, under a `proximate` threshold only, by
contextual marking when paired with another non-proximate 3P. -/
def IOSatisfiesProminence : Prop :=
  g.prominence.InherentlyMetBy a.io ∨
    (g.prominence = .proximate ∧
     ¬ g.prominence.InherentlyMetBy a.io ∧ ¬ g.prominence.InherentlyMetBy a.do_)

instance : Decidable (IOSatisfiesProminence g a) := inferInstanceAs (Decidable (_ ∨ _))

/-- (12c) The DO does not also inherently meet P-Prominence. -/
def UniquenessSatisfied : Prop := ¬ g.prominence.InherentlyMetBy a.do_

instance : Decidable (UniquenessSatisfied g a) := inferInstanceAs (Decidable (¬ _))

/-- (12d) A [+author] IO rescues an otherwise-blocking configuration when P-Primacy is on. The
rescue checks only the IO. -/
def PrimacyRescues : Prop := g.primacy ∧ a.io.IncludesSpeaker

instance : Decidable (PrimacyRescues g a) := inferInstanceAs (Decidable (_ ∧ _))

/-- (12a) A domain is exempt on a restricted domain when no DP bears the prominence feature. The
restriction presupposes an argument matching the P-Prominence value (§4.5, the restricted
application "matches the feature value set in P-Prominence"; for me-first, ApplPs with a
[+author] argument). -/
def DomainExempt : Prop :=
  g.restrictedDomain ∧
    ¬ g.prominence.InherentlyMetBy a.io ∧ ¬ g.prominence.InherentlyMetBy a.do_

instance : Decidable (DomainExempt g a) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The P-Constraint holds over an Appl domain when the domain is exempt, or the indirect object
is the point-of-view center, satisfies the prominence threshold, and P-Uniqueness holds or
P-Primacy rescues it. -/
def PConstraintSatisfied : Prop :=
  DomainExempt g a ∨
    (a.povCenter = a.io ∧ IOSatisfiesProminence g a ∧
      (g.uniqueness → UniquenessSatisfied g a ∨ PrimacyRescues g a))

instance : Decidable (PConstraintSatisfied g a) := inferInstanceAs (Decidable (_ ∨ _))

/-- A clitic combination is licit when the domain centered on its indirect object satisfies the
P-Constraint (§4.5). -/
def IsLicit (s : Scenario Person) : Prop := PConstraintSatisfied g ⟨s.high, s.low, s.high⟩

instance : DecidablePred (IsLicit g) :=
  fun _ ↦ inferInstanceAs (Decidable (PConstraintSatisfied ..))

/-- The person combinations `g` predicts licit. -/
def licitFinset : Finset (Scenario Person) := {s ∈ cliticPairs | IsLicit g s}

/-- Grammars are preordered by inclusion of their licit combinations. The order is only a
preorder, since distinct parameter settings can share a licit set
(`restricted_participant_surfaces_as_strong`). -/
instance : Preorder Grammar := Preorder.lift licitFinset

instance (g₁ g₂ : Grammar) : Decidable (g₁ ≤ g₂) :=
  inferInstanceAs (Decidable (licitFinset g₁ ⊆ licitFinset g₂))

end PConstraint

/-! ### The Person Hierarchy -/

/-- The positive person features of a person are the prominence values it meets by its own
features, first person bearing proximate, participant, and author, second person the first two,
and third person none (11). -/
def positiveFeatures (p : Person) : Finset ProminenceThreshold :=
  Finset.univ.filter (·.InherentlyMetBy p)

/-- The Person Hierarchy is derived, the prominence order coinciding with the order by count of
positive features (§2.1). -/
theorem personHierarchy_from_features (p q : Person) :
    p.prominence ≤ q.prominence ↔ (positiveFeatures p).card ≤ (positiveFeatures q).card := by
  cases p <;> cases q <;> decide

/-! ### The varieties (§4) -/

/-- The strong and the weak grammar license exactly the combinations of the Strong and the Weak
constraint, and on distinct persons the ultra-strong and the me-first grammar those of the
Ultrastrong and the Me-first constraint. -/
theorem isLicit_iff_variety :
    (∀ s, IsLicit strongGrammar s ↔ Strong s) ∧ (∀ s, IsLicit weakGrammar s ↔ Weak s) ∧
      ∀ s ∈ distinctPairs, (IsLicit ultraStrongGrammar s ↔ Ultrastrong s) ∧
        (IsLicit meFirstGrammar s ↔ MeFirst s) := by
  decide

/-- Under the strong PCC (14a) the direct object must be third person. -/
theorem strong_predictions :
    licitFinset strongGrammar = {⟨.first, .third⟩, ⟨.second, .third⟩, ⟨.third, .third⟩} := by
  decide

-- (14d)
theorem ultra_predictions :
    licitFinset ultraStrongGrammar =
      {⟨.first, .first⟩, ⟨.first, .second⟩, ⟨.first, .third⟩, ⟨.second, .third⟩,
        ⟨.third, .third⟩} := by
  decide

-- (14b)
theorem weak_predictions :
    licitFinset weakGrammar =
      {⟨.first, .first⟩, ⟨.first, .second⟩, ⟨.first, .third⟩, ⟨.second, .first⟩,
        ⟨.second, .second⟩, ⟨.second, .third⟩, ⟨.third, .third⟩} := by
  decide

-- (14e)
theorem super_predictions :
    licitFinset superStrongGrammar = {⟨.first, .third⟩, ⟨.second, .third⟩} := by decide

-- (14c)
theorem mefirst_predictions :
    licitFinset meFirstGrammar =
      {⟨.first, .second⟩, ⟨.first, .third⟩, ⟨.second, .second⟩, ⟨.second, .third⟩,
        ⟨.third, .second⟩, ⟨.third, .third⟩} := by
  decide

-- (32a)
theorem pg1_predictions :
    licitFinset pg1Grammar =
      {⟨.first, .first⟩, ⟨.first, .second⟩, ⟨.first, .third⟩, ⟨.second, .third⟩} := by
  decide

-- (32b)
theorem pg2_predictions :
    licitFinset pg2Grammar =
      {⟨.first, .first⟩, ⟨.first, .second⟩, ⟨.first, .third⟩, ⟨.second, .first⟩,
        ⟨.second, .second⟩, ⟨.second, .third⟩} := by
  decide

-- (33)
theorem pg3_predictions :
    licitFinset pg3Grammar = {⟨.first, .second⟩, ⟨.first, .third⟩} := by decide

-- §4.5
theorem restricted_participant_surfaces_as_strong :
    licitFinset { prominence := .participant, restrictedDomain := true } =
      licitFinset strongGrammar := by
  decide

/-! ### Containment among the attested varieties (§4.5) -/

theorem strong_le_ultra : strongGrammar ≤ ultraStrongGrammar := by decide

theorem ultra_le_weak : ultraStrongGrammar ≤ weakGrammar := by decide

theorem strong_le_weak : strongGrammar ≤ weakGrammar := strong_le_ultra.trans ultra_le_weak

theorem super_le_strong : superStrongGrammar ≤ strongGrammar := by decide

/-! ### The paper's examples (§4) -/

theorem italian_weak_glidat_tiacc :
    .dat ∈ Italian.Pronouns.gli.cases ∧ .acc ∈ Italian.Pronouns.ti.cases ∧
      ∃ io ∈ Italian.Pronouns.gli.person, ∃ do_ ∈ Italian.Pronouns.ti.person,
        ¬ IsLicit weakGrammar ⟨io, do_⟩ := by
  decide

theorem italian_weak_tidat_lacl :
    .dat ∈ Italian.Pronouns.ti.cases ∧ .acc ∈ Italian.Pronouns.la.cases ∧
      ∃ io ∈ Italian.Pronouns.ti.person, ∃ do_ ∈ Italian.Pronouns.la.person,
        IsLicit weakGrammar ⟨io, do_⟩ := by
  decide

-- (23)
theorem spanish_weak_tedat_meacc :
    .dat ∈ Spanish.Clitics.te.cases ∧ .acc ∈ Spanish.Clitics.me.cases ∧
      ∃ io ∈ Spanish.Clitics.te.person, ∃ do_ ∈ Spanish.Clitics.me.person,
        IsLicit weakGrammar ⟨io, do_⟩ := by
  decide

theorem spanish_weak_medat_teacc :
    .dat ∈ Spanish.Clitics.me.cases ∧ .acc ∈ Spanish.Clitics.te.cases ∧
      ∃ io ∈ Spanish.Clitics.me.person, ∃ do_ ∈ Spanish.Clitics.te.person,
        IsLicit weakGrammar ⟨io, do_⟩ := by
  decide

-- (24)
theorem spanish_weak_ledat_meacc_banned :
    .dat ∈ Spanish.Clitics.le.cases ∧ .acc ∈ Spanish.Clitics.me.cases ∧
      ∃ io ∈ Spanish.Clitics.le.person, ∃ do_ ∈ Spanish.Clitics.me.person,
        ¬ IsLicit weakGrammar ⟨io, do_⟩ := by
  decide

/-- In French (16), a third-person dative with a first-person accusative is out, while ⟨2, 3⟩ and
⟨3, 3⟩ are in. -/
theorem french_strong_examples :
    ¬ IsLicit strongGrammar ⟨.third, .first⟩ ∧ IsLicit strongGrammar ⟨.second, .third⟩ ∧
      IsLicit strongGrammar ⟨.third, .third⟩ := by
  decide

-- (20)
theorem catalan_ultra_strong_examples :
    IsLicit ultraStrongGrammar ⟨.first, .second⟩ ∧
      ¬ IsLicit ultraStrongGrammar ⟨.second, .first⟩ := by
  decide

-- (27)
theorem kambera_super_strong_examples :
    IsLicit superStrongGrammar ⟨.first, .third⟩ ∧ IsLicit superStrongGrammar ⟨.second, .third⟩ ∧
      ¬ IsLicit superStrongGrammar ⟨.third, .third⟩ ∧
      ¬ IsLicit superStrongGrammar ⟨.first, .second⟩ := by
  decide

-- (29)
theorem bulgarian_me_first_examples :
    IsLicit meFirstGrammar ⟨.third, .second⟩ ∧ ¬ IsLicit meFirstGrammar ⟨.second, .first⟩ := by
  decide

/-! ### The ⟨1, 1⟩ corner -/

-- §4.5
theorem mefirst_one_one_excluded : ¬ IsLicit meFirstGrammar ⟨.first, .first⟩ := by decide

/-- P-Primacy checks only the indirect object's [+author], so the ultra-strong
grammar licenses ⟨1, 1⟩ where the descriptive statement (14d) bans it. -/
theorem ultra_one_one_licensed : IsLicit ultraStrongGrammar ⟨.first, .first⟩ := by decide

-- §4.4
theorem mefirst_three_three_exempt : IsLicit meFirstGrammar ⟨.third, .third⟩ := by decide

end PanchevaZubizarreta2018
