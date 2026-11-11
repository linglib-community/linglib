module

public import Linglib.Syntax.Minimalist.Label.RaisingHead
public import Linglib.Syntax.Minimalist.Linearization.Replay
public import Linglib.Syntax.Minimalist.Probe.Cyclic
public import Linglib.Syntax.Minimalist.Probe.CyclicExpansion
public import Studies.BejarRezac2003
public import Linglib.Fragments.Basque.Agreement
public import Linglib.Fragments.Georgian.Agreement
public import Linglib.Data.Examples.BejarRezac2009
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Béjar and Rezac 2009: Cyclic Agree

Béjar and Rezac derive person-hierarchy effects in agreement from a single articulated person
probe on v that meets the internal argument first and, with whatever segments it leaves unchecked,
the external argument from the next projection of v. A language's articulation of the probe fixes
which persons count as more specified, so the external argument controls the agreement slot only
when it can check what the internal argument left. In the remaining, inverse contexts the core
probe never reaches the external argument and its person goes unlicensed; property P adds a probe
that licenses it, spelled out as extra agreement or as a special Case on the internal argument, and
that probe converges only in inverse contexts, since in direct ones it and the core probe are
valued alike on the same projection. The Person Case Constraint, which the authors had derived from
the same licensing condition, follows from the same probes once a segment may not reach past a goal
bearing `π`.

## Main definitions

* `BejarRezac2009.swahili`, `basque`, `nishnaabemwin`, `kashmiri`: the flat, partial and two full
  articulations of the probe.
* `BejarRezac2009.Converges`: a transitive derivation, with or without property P, licenses the
  external argument and values no two probes alike on one projection.
* `BejarRezac2009.segmentProbe`: a segment of the probe searching nominals with Case.

## Implementation notes

Checking is membership of a segment in a goal's specification, and the value a probe copies is the
goal's whole specification. Third persons are not differentiated, so 3N3 is inverse; the paper's
direct 3N3 forms, with differently specified third persons, are outside the model, and the Basque
3N3 cell is inverse as in (22a). Only arguments with
structural Case establish an inverse context, which the model, without Case on the arguments of a
transitive clause, does not state. A language's choice between [speaker] and [addressee] is carried
by its probe, as in `Minimalist.CyclicAgree`.

## TODO

The Nishnaabemwin theme suffix (27) and the portmanteaus *i* and *ku* as allomorphy of the core
probe; Table 1's Georgian, Karok and Erza columns; inherent Case as invisibility to the probe,
which would bring the Kashmiri past tense (31b) into the model.

## References

* [bejar-rezac-2009]
* [bejar-rezac-2003]
* [bejar-2003]
* [harley-ritter-2002]
-/

@[expose] public section

namespace BejarRezac2009

open Minimalist Minimalist.CyclicAgree Agreement Phi Phi.PersonSegment
open Clause (Scenario)

/-! ### The systems -/

/-- Swahili has the flat probe `[u-3]`, the root alone, as in (7) and (10). -/
def swahili : Finset PersonSegment := .Iic .pi

/-- Basque and Georgian have the partially articulated probe `[u-3-2]`, as in (8). -/
def basque : Finset PersonSegment := .Iic .participant

/-- Nishnaabemwin has the fully articulated probe `[u-3-1-2]`, articulated down to [addressee], so
that second person is the most specified, as in (17) and Table 2C. -/
def nishnaabemwin : Finset PersonSegment := .Iic .addressee

/-- Mohawk and Kashmiri have the fully articulated probe `[u-3-2-1]`, articulated down to
[speaker], as in (9) and Tables 7 and 11. -/
def kashmiri : Finset PersonSegment := .Iic .speaker

/-! ### Cyclic expansion (16) -/

/-- The internal argument, the verb, v and the external argument of a transitive vP. -/
def ia : LexicalItem.Token := ⟨.of .D [], 1⟩
@[inherit_doc ia] def verb : LexicalItem.Token := ⟨.of .V [.D], 2⟩
@[inherit_doc ia] def littleV : LexicalItem.Token := ⟨.of .v [.V], 3⟩
@[inherit_doc ia] def ea : LexicalItem.Token := ⟨.of .D [], 4⟩

/-- The derivation of a transitive vP (16). -/
def transitiveVP : Derivation := ⟨verb, [.em .left ia, .em .right littleV, .em .left ea]⟩

-- (16), the order `residue` and `IsDirect` take for granted
theorem cyclicGoals_transitiveVP :
    transitiveVP.externalize?.map (fun t ↦ ((tokenList t.val).find? (·.2 == littleV)).map fun a ↦
      cyclicGoals .raising t (·.item.cat = .D) ∅ a.1) = some (some [ia, ea]) := by
  decide +kernel

/-! ### Person hierarchies (§2) -/

/-- A ranking of persons picks the controller of an agreement slot when the external argument
controls it in the scenarios downstream on the ranking and the internal one in those upstream. -/
def Ranks (r : Person → ℕ) (f : Scenario Person → Person) : Prop :=
  ∀ s, ((s.map r).kind = .downstream → f s = s.high) ∧ ((s.map r).kind = .upstream → f s = s.low)

/-- A ranking that picks Basque's controller ranks first and second person alike, so it cannot
decide (2a) and (2c) (p. 38). -/
theorem basque_ranks_first_eq_second (r : Person → ℕ) (h : Ranks r (value basque)) :
    r .first = r .second := by
  have h12 := (h ⟨.first, .second⟩).1
  have h21 := (h ⟨.second, .first⟩).1
  have v12 : value basque ⟨.first, .second⟩ = .second := by decide +kernel
  have v21 : value basque ⟨.second, .first⟩ = .first := by decide +kernel
  rw [v12, Scenario.kind_eq_downstream_iff] at h12
  rw [v21, Scenario.kind_eq_downstream_iff] at h21
  rcases lt_trichotomy (r .first) (r .second) with hlt | heq | hgt
  · exact absurd (h21 hlt) (by decide)
  · exact heq
  · exact absurd (h12 hgt) (by decide)

/-- When the segments of the probe form a chain, the number of them a person bears ranks the
controller, as in Mohawk and Algonquian (p. 38). -/
theorem ranks_rank {P : Finset PersonSegment} (hP : IsChain (· ≤ ·) (P : Set PersonSegment)) :
    Ranks (rank P) (value P) := by
  intro s
  have hd := isDirect_iff_rank_lt (s := s) hP
  simp only [value, Scenario.kind_eq_downstream_iff, Scenario.kind_eq_upstream_iff,
    Scenario.map_high, Scenario.map_low]
  constructor <;> intro hlt <;> split_ifs with hdir
  · rfl
  · exact absurd (hd.2 hlt) hdir
  · exact absurd (hd.1 hdir) (not_lt.2 hlt.le)
  · rfl

/-! ### Direct and inverse contexts (22) -/

/-- Basque's direct contexts are those of a participant over a third person (22b). -/
theorem basque_isDirect_iff (s : Scenario Person) :
    IsDirect basque s ↔ s.low = .third ∧ s.high ≠ .third := by
  revert s
  decide +kernel

/-- Nishnaabemwin's direct contexts are 2N1, 2N3 and 1N3 (22b), the inclusive patterning with the
second person (fn. 9). -/
theorem nishnaabemwin_isDirect_iff (s : Scenario Person) :
    IsDirect nishnaabemwin s ↔
      (s.high = .second ∨ s.high = .firstInclusive) ∧
          (s.low = .first ∨ s.low = .firstExclusive ∨ s.low = .third) ∨
        (s.high = .first ∨ s.high = .firstExclusive) ∧ s.low = .third := by
  revert s
  decide +kernel

/-- Every Swahili context is inverse (22a). -/
example (s : Scenario Person) : IsInverse swahili s := isInverse_Iic_bot s

-- p. 62
theorem basque_isDirect_imp_kashmiri {s : Scenario Person} (h : IsDirect basque s) :
    IsDirect kashmiri s :=
  h.mono (Finset.Iic_subset_Iic.2 (by decide))

example : IsInverse basque ⟨.first, .second⟩ ∧ IsDirect kashmiri ⟨.first, .second⟩ := by
  decide +kernel

-- (26)
theorem kashmiri_participant_direct_iff (s : Scenario Person) :
    IsDirect kashmiri s ∧ s.high.IsSAP ∧ s.low.IsSAP ↔
      (s.high = .first ∨ s.high = .firstInclusive ∨ s.high = .firstExclusive) ∧
        s.low = .second := by
  revert s
  decide +kernel

/-! ### The added probe (§4.1) -/

/-- The first projection of v, from which the core probe meets the internal argument, and the
second, from which it meets the external one. -/
inductive Locus where
  | vI
  | vII
  deriving DecidableEq, Repr

/-- The valuations of v's probes pair each probe's locus with the value it copies, the goal's whole
specification as in (12b). The core probe copies the internal argument on vI when some segment
matches and the external argument on vII in a direct context, and when the core probe has
property P the added probe copies the external argument on vII, as in (23). -/
def valuations (P : Finset PersonSegment) (hasP : Bool) (s : Scenario Person) :
    List (Locus × Finset PersonSegment) :=
  ((if ∃ x ∈ P, x ∈ spec s.low then [(.vI, spec s.low)] else []) ++
    if IsDirect P s then [(.vII, spec s.high)] else []) ++
    if hasP then [(.vII, spec s.high)] else []

/-- A derivation converges when the core probe or the added one licenses the external argument's
person, as the PLC (13) requires, and no two probes are valued alike on one projection, which
would leave them indistinguishable (p. 58). -/
def Converges (P : Finset PersonSegment) (hasP : Bool) (s : Scenario Person) : Prop :=
  (EALicensed P s ∨ hasP = true) ∧ (valuations P hasP s).Nodup

instance (P : Finset PersonSegment) (hasP : Bool) : DecidablePred (Converges P hasP) := fun _ ↦ by
  unfold Converges; infer_instance

/-- A derivation converges iff its core probe has property P exactly in an inverse context ((25),
Table 6). -/
theorem converges_iff (P : Finset PersonSegment) (hasP : Bool) (s : Scenario Person) :
    Converges P hasP s ↔ (hasP = true ↔ IsInverse P s) := by
  unfold Converges valuations
  rw [eaLicensed_iff_isDirect, ← not_isDirect]
  by_cases hd : IsDirect P s <;> cases hasP <;> split_ifs <;> simp_all

-- (25): 2N1 converges with the added probe, 1N2 does not; fn. 11: 3N3 converges, its two
-- probes valued alike on different projections.
example : Converges kashmiri true ⟨.second, .first⟩ ∧ ¬ Converges kashmiri true ⟨.first, .second⟩ ∧
    Converges kashmiri true ⟨.third, .third⟩ := by
  decide +kernel

/-- The value of the probe valued on the highest projection of v, the only probe Kashmiri spells
out by (24a). -/
def highestValue (P : Finset PersonSegment) (hasP : Bool) (s : Scenario Person) :
    Option (Finset PersonSegment) :=
  (valuations P hasP s).getLast?.map Prod.snd

/-- In a convergent derivation the probe valued last is valued by the external argument (Table 11).
-/
theorem highestValue_eq_spec {P : Finset PersonSegment} {hasP : Bool} {s : Scenario Person}
    (h : Converges P hasP s) : highestValue P hasP s = some (spec s.high) := by
  rw [converges_iff, ← not_isDirect] at h
  unfold highestValue valuations
  by_cases hd : IsDirect P s <;> cases hasP <;> split_ifs <;> simp_all

/-! ### The Person Case Constraint (14), (15) -/

/-- The segment `s` of the probe searches nominals with Case. The search halts at the closest
nominal, which bears `π` and so intervenes for every segment (fn. 6), and Agrees with it iff its
Case is unvalued and it bears the segment. -/
def segmentProbe (s : PersonSegment) : Probe BejarRezac2003.Nominal :=
  .ofInt fun n ↦ n.features.IsActive ∧ s ∈ spec n.features.agreement.person

/-- The root segment `π` is the person probe of [bejar-rezac-2003]. -/
theorem segmentProbe_pi : segmentProbe .pi = BejarRezac2003.phiProbe := by
  unfold segmentProbe BejarRezac2003.phiProbe
  congr 1
  funext n
  simp

/-- No segment reaches a nominal behind an oblique one, so a participant there goes unlicensed,
the Person Case Constraint (14). -/
theorem pcc (s : PersonSegment) (cd cn : Bundle) :
    (segmentProbe s).goal [.dat cd, .caseless cn] = none := by
  simp [segmentProbe, Probe.goal, Probe.ofInt_search]

/-- A segment searching for the closest nominal bearing it would skip a third-person dative and
reach a participant theme, the prediction fn. 6 excludes. -/
example : (Probe.relativized fun n : BejarRezac2003.Nominal ↦
    PersonSegment.participant ∈ spec n.features.agreement.person).search
      [.dat (.personNumber .third .singular), .caseless (.personNumber .first .singular)] =
    some (.caseless (.personNumber .first .singular)) := by
  decide

-- (15): a dative excludes a 1st person theme and admits a 3rd person one.
example :
    ¬ BejarRezac2003.PLC (BejarRezac2003.v.derive
      [.dat (.personNumber .third .singular), .caseless (.personNumber .first .singular)]) ∧
    BejarRezac2003.PLC (BejarRezac2003.v.derive
      [.dat (.personNumber .third .singular), .caseless (.personNumber .third .plural)]) := by
  decide

/-! ### The examples -/

/-- `person? e key` is the person an example's feature `key` names. -/
def person? (e : Datum) (key : String) : Option Person :=
  e.parse? key [("1", .first), ("2", .second), ("3", .third)]

/-- `config? e` is the probe of an example's language with the scenario of its external over its
internal argument. -/
def config? (e : Datum) : Option (Finset PersonSegment × Scenario Person) := do
  let sys ← e.byLanguage [(.basque, basque), (.georgian, basque), (.ottawa, nishnaabemwin),
    (.kashmiri, kashmiri)]
  return (sys, ⟨← person? e "ea", ← person? e "ia"⟩)

/-- The controller the paper reports for an example in (2), (3), (17) and (18) is the one cyclic
Agree gives. -/
theorem controller_rows : ∀ e ∈ Examples.all, ∀ c ∈ config? e, ∀ p ∈ person? e "controller",
    value c.1 c.2 = p := by
  decide +kernel

/-- The direct and inverse contexts of the examples in (22) and (29) are those of cyclic Agree. -/
theorem context_rows : ∀ e ∈ Examples.all, ∀ c ∈ config? e, ∀ x ∈ e.feature? "context",
    (x = "inverse" ↔ IsInverse c.1 c.2) := by
  decide +kernel

/-- Every repair example of Bizkaian Basque or Kashmiri is a convergent derivation with property P
(Table 9, (29)–(31)). -/
theorem repair_rows : ∀ e ∈ Examples.all, ∀ c ∈ config? e, ∀ _ ∈ e.feature? "repair",
    Converges c.1 true c.2 := by
  decide +kernel

/-- The first morph of an example's last word, a prefix. -/
def slotPrefix? (e : Datum) : Option Morphology.Morph :=
  e.surfaceTokens.getLast?.map fun w ↦ .pref (String.ofList (w.toList.takeWhile (· ≠ '-')))

-- (2), (2d)
theorem basque_prefix_rows : ∀ e ∈ Examples.all, e.language = .basque →
    ∀ c ∈ config? e, ∀ _ ∈ person? e "controller", ∃ n ∈ [Number.singular, .plural],
      ((if IsDirect c.1 c.2 then Basque.displacedErgative else Basque.absolutive).realize
          (.personNumber (value c.1 c.2) n)).bind (·.head?) = slotPrefix? e := by
  decide +kernel

/-- The Georgian affix set that spells the core probe in (21) is Set A when the external argument
values it on the second cycle, a direct context, and Set B when the internal argument values it
on the first. -/
def georgianSet (P : Finset PersonSegment) (s : Scenario Person) : Georgian.AffixSet :=
  if IsDirect P s then .A else .B

-- (18)
theorem georgian_prefix_rows : ∀ e ∈ Examples.all, e.language = .georgian →
    ∀ c ∈ config? e,
      ((georgianSet c.1 c.2).paradigm.realize
          (.personNumber (value c.1 c.2) .singular)).bind (·.head?) = slotPrefix? e := by
  decide +kernel

end BejarRezac2009
