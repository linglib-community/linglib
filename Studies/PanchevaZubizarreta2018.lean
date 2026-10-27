module

public import Linglib.Syntax.Agreement.PersonCaseConstraint
public import Linglib.Semantics.Reference.Logophoricity
public import Linglib.Syntax.Person.Features
public import Linglib.Fragments.Romance.Italian.Pronouns
public import Linglib.Fragments.Romance.Spanish.Clitics

/-!
# Pancheva and Zubizarreta (2018): The Person Case Constraint

This file formalizes the predictions of Pancheva and Zubizarreta's P-Constraint, the
proposal that Person Case Constraint effects are the syntactic encoding of perspective: an
interpretable person feature on the applicative head marks the indirect object as the
point-of-view center of its domain, and a clitic combination is licit exactly when selecting
the indirect object as that center satisfies the constraint (`ApplDomain`,
`PConstraintSatisfied`, `isLicit_iff_pConstraint`). The Person Hierarchy 1 > 2 > 3 is derived
from the count of positive person features rather than stipulated
(`personHierarchy_from_features`). The constraint's four parameters, the prominence
threshold, the domain of application, P-Uniqueness, and P-Primacy, generate the five attested
varieties, strong, ultra-strong, weak, super-strong, and me-first, together with three
predicted ones, each checked against the paper's examples (`strong_predictions` and its
siblings, `french_strong_examples` and its siblings), and the attested varieties are ordered
by containment of their licit sets (`strong_le_ultra`, `ultra_le_weak`, `super_le_strong`).
The three prominence values correspond to Sells's logophoric roles pivot, self, and source
(`prominenceToSellsRole`).

## Implementation notes

The grammars and the licitness predicate live in `Syntax/Agreement/PersonCaseConstraint`.
The Italian and Spanish clitic combinations are read off the Fragments, the French, Catalan,
Kambera, and Bulgarian ones off the parameter settings, since no clitic Fragment exists for
those languages. The paper's separation of the Clitic Logophoric Restriction from the PCC,
against the unification Charnavel and Mateu propose, the two phenomena sharing only
the point-of-view marking on the applicative head, is not represented: the restriction is a
semantic constraint outside this model.

## TODO

The substrate's P-Primacy checks only the indirect object's [+author], so the ultra-strong
grammar licenses the ⟨1, 1⟩ combination that the descriptive statement (14d) bans
(`ultra_one_one_licensed`); the paper does not walk the mechanism through that cell.

## References

* [pancheva-zubizarreta-2018]
* [sells-1987]
* [charnavel-mateu-2015]
-/

@[expose] public section

namespace PanchevaZubizarreta2018

open PCC

/-! ### The applicative domain -/

/-- The applicative phase holds the indirect object introduced by Appl, the direct object inside
VP, and the argument selected as point-of-view center. -/
structure ApplDomain where
  io : Person
  do_ : Person
  povCenter : Person
  deriving DecidableEq

/-- The P-Constraint holds over an Appl domain when the domain is exempt, or the indirect object
is the point-of-view center, satisfies the prominence threshold, and P-Uniqueness holds or
P-Primacy rescues it. -/
def PConstraintSatisfied (g : Grammar) (a : ApplDomain) : Prop :=
  DomainExempt g ⟨a.io, a.do_⟩ ∨
    (a.povCenter = a.io ∧ IOSatisfiesProminence g ⟨a.io, a.do_⟩ ∧
      (g.uniqueness → UniquenessSatisfied g a.do_ ∨ PrimacyRescues g a.io))

instance (g : Grammar) (a : ApplDomain) : Decidable (PConstraintSatisfied g a) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A clitic combination is licit exactly when the domain centered on the indirect object satisfies
the P-Constraint (§4.5). -/
theorem isLicit_iff_pConstraint (g : Grammar) (s : Clause.Scenario Person) :
    IsLicit g s ↔ PConstraintSatisfied g ⟨s.high, s.low, s.high⟩ := by
  constructor
  · rintro (h | ⟨hp, hr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, hp, hr⟩
  · rintro (h | ⟨_, hp, hr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hp, hr⟩

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

/-! ### Logophoric roles (§6.2) -/

/-- The prominence values are the logophoric roles of [sells-1987], proximate arguments being
pivots, participants selves, and authors sources. -/
def prominenceToSellsRole : ProminenceThreshold → LogophoricRole
  | .proximate => .pivot
  | .participant => .self
  | .author => .source

theorem family_logophoric_assignments :
    prominenceToSellsRole strongGrammar.prominence = .pivot ∧
      prominenceToSellsRole ultraStrongGrammar.prominence = .pivot ∧
      prominenceToSellsRole weakGrammar.prominence = .pivot ∧
      prominenceToSellsRole superStrongGrammar.prominence = .self ∧
      prominenceToSellsRole meFirstGrammar.prominence = .source ∧
      prominenceToSellsRole pg3Grammar.prominence = .source := by
  decide

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

/-- The substrate's P-Primacy checks only the indirect object's [+author], so the ultra-strong
grammar licenses ⟨1, 1⟩ where the descriptive statement (14d) bans it. -/
theorem ultra_one_one_licensed : IsLicit ultraStrongGrammar ⟨.first, .first⟩ := by decide

-- §4.4
theorem mefirst_three_three_exempt : IsLicit meFirstGrammar ⟨.third, .third⟩ := by decide

end PanchevaZubizarreta2018
