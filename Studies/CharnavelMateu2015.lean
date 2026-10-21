module

public import Mathlib.Order.Cover
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Experiments.CharnavelMateu2015
public import Linglib.Fragments.Romance.Spanish.Clitics

/-!
# Charnavel and Mateu (2015): the clitic logophoric restriction

In French and Spanish an accusative clitic clustered with a third-person dative clitic cannot
refer de se to an attitude holder. A judgment task separates this from binding. The cluster
degrades with a logophoric antecedent whether or not the antecedent c-commands the clitic, and not
with a c-commanding antecedent that is not logophoric, against the binding account the paper
replaces. Charnavel and Mateu derive the restriction, and the Person Case Constraint with it, from
a hierarchy of logophoric centers, discourse participant over empathy locus over attitude holder,
whose features make two centers share one exactly when they are identical or adjacent. A domain
has a single logophoric operator, and two of its elements sharing a feature intervene.

## Main definitions

* `LogophoricCenter`, `LogophoricCenter.features`: the hierarchy of centers and their features.
* `Licit`: a domain in which no two centers share a feature.
* `center`: the center a clitic realizes by its person and case.

## Main results

* `LogophoricCenter.not_disjoint_features_iff`: two centers share a feature exactly when they are
  identical or adjacent on the hierarchy.
* `licit_iff`: a domain is licit exactly when it holds at most one center, or a discourse
  participant and an attitude holder.
* `licit_dative_accusative_iff`, `licit_dative_attitudeHolder_iff`: over the Spanish clitics, a
  dative and an accusative are licit exactly when the accusative is third person, the strong
  Person Case Constraint, and a dative with an accusative read de se exactly when the dative is
  first or second person, the clitic logophoric restriction.
* `licit_domain_iff`: the hierarchy predicts every condition of the experiment.
* `grammaticality_eq_of_eq`, `filter_violatesBinding`: conditions differing only in c-command
  have the same result, and the binding account mispredicts conditions 3, 4 and 6.

## Implementation notes

* A domain is the list of the centers its clitics realize. Each clitic realizes the center its
  person and case assign it; the uses of a center lower on the hierarchy that the paper allows,
  a dative clitic referring to an attitude holder, are not modelled.
* Example, table and section numbers follow the authors' accepted manuscript in Harvard's DASH
  repository.

## TODO

* The French clitic fragment has only *se*; the strong Person Case Constraint and the clitic
  logophoric restriction over French await its object clitics.
* The paper's examples as `Data/Examples` rows, among them the epithet diagnostics (27)–(32),
  the non-de se reading (33), the dream report (49) in which a first person escapes the Person
  Case Constraint, and the reflexives of §3.5.3, which the paper takes to be discourse
  participants.

## References

* [charnavel-mateu-2015]
* [bhatt-simik-2009]
* [sells-1987]
* [kuno-1987]
-/

@[expose] public section

namespace CharnavelMateu2015

open scoped Function

/-! ### The hierarchy of logophoric centers -/

/-- The three kinds of logophoric center (53), in the order of the hierarchy (54), the degree to
which their perspective is integrated in the discourse. -/
inductive LogophoricCenter where
  /-- One whose discourse or thoughts are reported, the source or self of [sells-1987] but not
  the pivot (24), as a third-person accusative clitic read de se refers to. -/
  | attitudeHolder
  /-- The event participant the speaker empathizes or identifies with ([kuno-1987]), as a
  third-person dative clitic refers to. -/
  | empathyLocus
  /-- The speaker or addressee, as a first- or second-person clitic refers to. -/
  | discourseParticipant
  deriving DecidableEq, Repr, Fintype

/-- The features of logophoric centers (63). -/
inductive Feature where
  | A | B | C
  deriving DecidableEq, Repr, Fintype

namespace LogophoricCenter

instance : LinearOrder LogophoricCenter := LinearOrder.lift' (·.ctorIdx) (by decide)

instance : DecidableRel (α := LogophoricCenter) (· ⩿ ·) := fun _ _ ↦
  inferInstanceAs (Decidable (_ ∧ ∀ _, _))

/-- The features of a center (63). [B] is the speaker component that discourse participants and
empathy loci share, and [C] the perspectival distance from the speaker that empathy loci and
attitude holders share. -/
def features : LogophoricCenter → Finset Feature
  | attitudeHolder => {.C}
  | empathyLocus => {.B, .C}
  | discourseParticipant => {.A, .B}

/-- Two centers share a feature exactly when they are identical or adjacent on the hierarchy,
which is what the features are chosen for. -/
theorem not_disjoint_features_iff {x y : LogophoricCenter} :
    ¬ Disjoint x.features y.features ↔ x ⩿ y ∨ y ⩿ x := by
  cases x <;> cases y <;> decide

end LogophoricCenter

/-! ### Intervention -/

/-- A domain is licit when no two of its centers share a feature. Its one logophoric operator
checks each feature against the element bearing it, and a second bearer intervenes (64). -/
def Licit (l : List LogophoricCenter) : Prop :=
  l.Pairwise (Disjoint on LogophoricCenter.features)

instance : DecidablePred Licit := fun l ↦ inferInstanceAs (Decidable (l.Pairwise _))

/-- A domain is licit exactly when it holds at most one center, or a discourse participant and an
attitude holder, the two ends of the hierarchy. Every other pair of centers intervenes (Table 3),
and no three centers are pairwise disjoint. -/
theorem licit_iff {l : List LogophoricCenter} :
    Licit l ↔ l.length ≤ 1 ∨ l.Perm [.discourseParticipant, .attitudeHolder] := by
  match l with
  | [] | [_] => simp [Licit]
  | [x, y] => cases x <;> cases y <;> decide
  | x :: y :: z :: l =>
    have key : ∀ x y z : LogophoricCenter, Disjoint x.features y.features →
        Disjoint x.features z.features → ¬ Disjoint y.features z.features := by decide
    refine iff_of_false (fun h ↦ ?_) (not_or_intro (by simp) fun h ↦ by simpa using h.length_eq)
    simp only [Licit, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
    exact key x y z h.1.1 h.1.2.1 h.2.1.1

/-! ### Clitics as centers -/

/-- The center a clitic realizes (53). A first- or second-person clitic is a discourse participant
and a third-person dative an empathy locus, while a third-person accusative, which bears no person
feature (41), realizes none unless it is read de se. -/
def center (c : PersonalPronoun) : Option LogophoricCenter :=
  if ∃ p ∈ c.person, p.IsSAP then some .discourseParticipant
  else if .dat ∈ c.cases then some .empathyLocus else none

/-- A Spanish dative and accusative clitic are licit together exactly when the accusative is third
person, the strong Person Case Constraint (51a). A third-person accusative not read de se, as in
(33), realizes no center and so clashes with nothing. -/
theorem licit_dative_accusative_iff :
    ∀ d ∈ Spanish.Clitics.dative, ∀ a ∈ Spanish.Clitics.accusative,
      (Licit ([d, a].filterMap center) ↔ a.person = some .third) := by
  decide +kernel

/-- A Spanish dative clitic is licit with an accusative read de se, an attitude holder, exactly
when the dative is first or second person. A third-person dative gives the clitic logophoric
restriction (26), and a second-person one the licit (25). -/
theorem licit_dative_attitudeHolder_iff :
    ∀ d ∈ Spanish.Clitics.dative,
      (Licit ([d].filterMap center ++ [.attitudeHolder]) ↔ d.person ≠ some .third) := by
  decide +kernel

/-! ### The experiment -/

/-- The dative clitics a condition's coding admits, first- or second-person ones for `1/2` and
third-person ones for `3` and `bound 3`. -/
def DativePerson.Admits : DativePerson → PersonalPronoun → Prop
  | .participant, d => ∃ p ∈ d.person, p.IsSAP
  | .third, d | .boundThird, d => d.person = some .third

instance : (v : DativePerson) → DecidablePred v.Admits
  | .participant => fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))
  | .third | .boundThird => fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The domain of a condition with dative clitic `d`. The accusative clitic refers de se to its
antecedent, and so is an attitude holder when the antecedent is a logophoric center. -/
def Result.domain (r : Result) (d : PersonalPronoun) : List LogophoricCenter :=
  [d].filterMap center ++ if r.logophoricAntecedent = .yes then [.attitudeHolder] else []

/-- The hierarchy predicts the result of every condition (Table 2), whichever Spanish dative
clitic of the coded person realizes it. Whether the antecedent c-commands the accusative clitic,
and whether the dative is bound, play no part. -/
theorem licit_domain_iff :
    ∀ r ∈ results, ∀ d ∈ Spanish.Clitics.dative, r.dativePerson.Admits d →
      (Licit (r.domain d) ↔ r.grammaticality = .ok) := by
  decide +kernel

/-- Conditions differing only in whether the antecedent c-commands the accusative clitic have the
same result, so what degrades a cluster is not binding (§2.4). -/
theorem grammaticality_eq_of_eq :
    ∀ r ∈ results, ∀ s ∈ results, r.logophoricAntecedent = s.logophoricAntecedent →
      r.dativePerson = s.dativePerson → r.grammaticality = s.grammaticality := by
  decide

/-! ### The binding account

The account the paper argues against ([bhatt-simik-2009], as reviewed in §1.2) bans a bound
accusative clitic beside a third-person dative (13). A third person acquires person features when
it is bound, so on the person hierarchy it ranks above a free third person as the first and
second persons do, and a cluster must respect both that hierarchy and the argument hierarchy, on
which the indirect object outranks the direct object. A bound dative then rescues a bound
accusative, the weak effect the experiment's condition 3 tests. -/

/-- The persons of the person hierarchy, a free third person ranked below a speech-act participant
and a bound third person, which are unranked among themselves. The first and second persons rank
alike against third persons and are merged, as the experiment's coding merges them. -/
inductive Rank where
  | third | participant | boundThird
  deriving DecidableEq, Repr, Fintype

instance : PartialOrder Rank where
  le x y := x = y ∨ x = .third
  le_refl _ := .inl rfl
  le_trans x y z := by cases x <;> cases y <;> cases z <;> simp
  le_antisymm x y := by cases x <;> cases y <;> simp

instance : DecidableRel (α := Rank) (· ≤ ·) := fun x y ↦
  inferInstanceAs (Decidable (x = y ∨ x = .third))

instance : DecidableRel (α := Rank) (· < ·) := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The rank of a condition's dative clitic. -/
def DativePerson.rank : DativePerson → Rank
  | .third => .third
  | .participant => .participant
  | .boundThird => .boundThird

/-- A condition violates the binding account when its accusative clitic, bound exactly when its
antecedent c-commands it, outranks the dative on the person hierarchy. -/
def Result.ViolatesBinding (r : Result) : Prop :=
  r.dativePerson.rank < if r.cCommandingAntecedent = .yes then .boundThird else .third

instance : DecidablePred Result.ViolatesBinding := fun _ ↦
  inferInstanceAs (Decidable (_ < _))

/-- The binding account mispredicts conditions 3, 4 and 6. A bound dative does not rescue a bound
accusative, a bound accusative with a non-logophoric antecedent is fine, and an accusative with a
logophoric antecedent that does not bind it is not. -/
theorem filter_violatesBinding :
    (results.filter fun r ↦ r.ViolatesBinding ↔ r.grammaticality = .ok).map (·.condition) =
      [3, 4, 6] := by
  decide

end CharnavelMateu2015
