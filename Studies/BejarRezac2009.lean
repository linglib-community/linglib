module

public import Linglib.Syntax.Minimalist.Probe.Cyclic
public import Studies.BejarRezac2003
public import Linglib.Fragments.Basque.Agreement
public import Linglib.Fragments.Georgian.Agreement
public import Linglib.Data.Examples.BejarRezac2009

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
direct 3N3 forms, with differently specified third persons, are outside the model, and Table 9
leaves the Basque 3N3 cell unshaded although (22a) counts it inverse. Only arguments with
structural Case establish an inverse context, which the model, without Case on the arguments of a
transitive clause, does not state. The prose on p. 37 says (2a) tracks the external argument; the
annotations and p. 38 show it is (2d).

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

open Minimalist Minimalist.CyclicAgree Agreement Phi
open Clause (Scenario)

/-! ### The systems -/

/-- Swahili has the flat system `[u-3]`, as in (7) and (10). -/
def swahili : AgreementSystem := ⟨.standard, flatProbe⟩

/-- Basque and Georgian have the partial system `[u-3-2]`, as in (8). -/
def basque : AgreementSystem := ⟨.standard, partialProbe⟩

/-- Nishnaabemwin has the full system `[u-3-1-2]`, under which second person is the most
specified, as in (17) and Table 2C. -/
def nishnaabemwin : AgreementSystem := ⟨.addressee, fullProbe .addressee⟩

/-- Mohawk and Kashmiri have the full system `[u-3-2-1]`, as in (9) and Tables 7 and 11. -/
def kashmiri : AgreementSystem := ⟨.standard, fullProbe .standard⟩

/-! ### Person hierarchies (§2) -/

/-- A ranking of persons picks the controller of an agreement slot when the external argument
controls it in the scenarios downstream on the ranking and the internal one in those upstream. -/
def Ranks (r : Person → ℕ) (f : Scenario Person → Person) : Prop :=
  ∀ s, ((s.map r).kind = .downstream → f s = s.high) ∧ ((s.map r).kind = .upstream → f s = s.low)

/-- A ranking that picks Basque's controller ranks first and second person alike, so it cannot
decide (2a) and (2c) (p. 38). -/
theorem basque_ranks_first_eq_second (r : Person → ℕ) (h : Ranks r basque.value) :
    r .first = r .second := by
  have h12 := (h ⟨.first, .second⟩).1
  have h21 := (h ⟨.second, .first⟩).1
  have v12 : basque.value ⟨.first, .second⟩ = .second := by decide +kernel
  have v21 : basque.value ⟨.second, .first⟩ = .first := by decide +kernel
  rw [v12, Scenario.kind_eq_downstream_iff] at h12
  rw [v21, Scenario.kind_eq_downstream_iff] at h21
  rcases lt_trichotomy (r .first) (r .second) with hlt | heq | hgt
  · exact absurd (h21 hlt) (by decide)
  · exact heq
  · exact absurd (h12 hgt) (by decide)

/-- Under a chain geometry, depth of specification ranks the controller of a full probe, as in
Mohawk and Algonquian (p. 38). -/
theorem full_ranks (geom : PersonGeometry) (h : geom.IsChain) :
    Ranks (fun p ↦ (personSpec geom p).length)
      (⟨geom, fullProbe geom⟩ : AgreementSystem).value := by
  intro s
  have hfull : ∀ p, (fullProbe geom).filter (· ∈ personSpec geom p) = personSpec geom p := by
    intro p
    cases geom <;> cases p <;> decide +kernel
  have hd := AgreementSystem.isDirect_iff_rank_lt ⟨geom, fullProbe geom⟩ s h
  simp only [AgreementSystem.rank, AgreementSystem.spec, hfull] at hd
  simp only [AgreementSystem.value, Scenario.kind_eq_downstream_iff,
    Scenario.kind_eq_upstream_iff, Scenario.map_high, Scenario.map_low]
  constructor <;> intro hlt <;> split_ifs with hdir
  · rfl
  · exact absurd (hd.2 hlt) hdir
  · exact absurd (hd.1 hdir) (not_lt.2 hlt.le)
  · rfl

/-! ### Direct and inverse contexts (22) -/

/-- Basque's direct contexts are those of a participant over a third person (22b). -/
theorem basque_isDirect_iff (s : Scenario Person) :
    basque.IsDirect s ↔ s.low = .third ∧ s.high ≠ .third := by
  revert s
  decide +kernel

/-- Nishnaabemwin's direct contexts are 2N1, 2N3 and 1N3 (22b), the inclusive patterning with the
second person (fn. 9). -/
theorem nishnaabemwin_isDirect_iff (s : Scenario Person) :
    nishnaabemwin.IsDirect s ↔
      (s.high = .second ∨ s.high = .firstInclusive) ∧
          (s.low = .first ∨ s.low = .firstExclusive ∨ s.low = .third) ∨
        (s.high = .first ∨ s.high = .firstExclusive) ∧ s.low = .third := by
  revert s
  decide +kernel

/-- Every Swahili context is inverse (22a). -/
example (s : Scenario Person) : swahili.IsInverse s := AgreementSystem.flat_isInverse s _

-- p. 62
theorem basque_isDirect_imp_kashmiri {s : Scenario Person} (h : basque.IsDirect s) :
    kashmiri.IsDirect s :=
  AgreementSystem.IsDirect.mono basque s rfl (by decide) h

example : basque.IsInverse ⟨.first, .second⟩ ∧ kashmiri.IsDirect ⟨.first, .second⟩ := by
  decide +kernel

-- (26)
theorem kashmiri_participant_direct_iff (s : Scenario Person) :
    kashmiri.IsDirect s ∧ PersonSegment.participant ∈ kashmiri.spec s.high ∧
        PersonSegment.participant ∈ kashmiri.spec s.low ↔
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
def valuations (sys : AgreementSystem) (hasP : Bool) (s : Scenario Person) :
    List (Locus × List PersonSegment) :=
  ((if ∃ x ∈ sys.probe, x ∈ sys.spec s.low then [(.vI, sys.spec s.low)] else []) ++
    if sys.IsDirect s then [(.vII, sys.spec s.high)] else []) ++
    if hasP then [(.vII, sys.spec s.high)] else []

/-- A derivation converges when the core probe or the added one licenses the external argument's
person, as the PLC (13) requires, and no two probes are valued alike on one projection, which
would leave them indistinguishable (p. 58). -/
def Converges (sys : AgreementSystem) (hasP : Bool) (s : Scenario Person) : Prop :=
  (sys.EALicensed s ∨ hasP = true) ∧ (valuations sys hasP s).Nodup

instance (sys : AgreementSystem) (hasP : Bool) : DecidablePred (Converges sys hasP) := fun _ ↦ by
  unfold Converges; infer_instance

/-- A derivation converges iff its core probe has property P exactly in an inverse context ((25),
Table 6). -/
theorem converges_iff (sys : AgreementSystem) (hasP : Bool) (s : Scenario Person) :
    Converges sys hasP s ↔ (hasP = true ↔ sys.IsInverse s) := by
  unfold Converges valuations AgreementSystem.IsInverse
  rw [AgreementSystem.eaLicensed_iff_isDirect]
  by_cases hd : sys.IsDirect s <;> cases hasP <;> split_ifs <;> simp_all

-- (25): 2N1 converges with the added probe, 1N2 does not; fn. 11: 3N3 converges, its two
-- probes valued alike on different projections.
example : Converges kashmiri true ⟨.second, .first⟩ ∧ ¬ Converges kashmiri true ⟨.first, .second⟩ ∧
    Converges kashmiri true ⟨.third, .third⟩ := by
  decide +kernel

/-- The value of the probe valued on the highest projection of v, the only probe Kashmiri spells
out by (24a). -/
def highestValue (sys : AgreementSystem) (hasP : Bool) (s : Scenario Person) :
    Option (List PersonSegment) :=
  (valuations sys hasP s).getLast?.map Prod.snd

/-- In a convergent derivation the probe valued last is valued by the external argument (Table 11).
-/
theorem highestValue_eq_spec {sys : AgreementSystem} {hasP : Bool} {s : Scenario Person}
    (h : Converges sys hasP s) : highestValue sys hasP s = some (sys.spec s.high) := by
  rw [converges_iff] at h
  unfold highestValue valuations AgreementSystem.IsInverse at *
  by_cases hd : sys.IsDirect s <;> cases hasP <;> split_ifs <;> simp_all

/-! ### The Person Case Constraint (14), (15) -/

/-- The segment `s` of the probe searches nominals with Case. The search halts at the closest
nominal, which bears `π` and so intervenes for every segment (fn. 6), and Agrees with it iff its
Case is unvalued and it bears the segment. -/
def segmentProbe (geom : PersonGeometry) (s : PersonSegment) : Probe BejarRezac2003.Nominal :=
  .ofInt fun n ↦ n.isActive && decide (s ∈ personSpec geom n.cell.person)

/-- The root segment `π` is the person probe of [bejar-rezac-2003]. -/
theorem segmentProbe_pi (geom : PersonGeometry) :
    segmentProbe geom .pi = BejarRezac2003.phiProbe := by
  unfold segmentProbe BejarRezac2003.phiProbe
  congr 1
  funext n
  simp [pi_mem_personSpec]

/-- No segment reaches a nominal behind an oblique one, so a participant there goes unlicensed,
the Person Case Constraint (14). -/
theorem pcc (geom : PersonGeometry) (s : PersonSegment) (cd cn : Bundle) :
    (segmentProbe geom s).goal [.dat cd, .caseless cn] = none := by
  simp [segmentProbe, Probe.goal, Probe.ofInt_search]

/-- A segment searching for the closest nominal bearing it would skip a third-person dative and
reach a participant theme, the prediction fn. 6 excludes. -/
example : (Probe.relativized fun n : BejarRezac2003.Nominal ↦
    decide (PersonSegment.participant ∈ personSpec .standard n.cell.person)).search
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

/-- `config? e` is the agreement system of an example's language with the scenario of its external
over its internal argument. -/
def config? (e : Datum) : Option (AgreementSystem × Scenario Person) := do
  let sys ← [("basq1248", basque), ("nucl1302", basque), ("otta1242", nishnaabemwin),
    ("kash1277", kashmiri)].lookup e.language
  return (sys, ⟨← person? e "ea", ← person? e "ia"⟩)

/-- The controller the paper reports for an example in (2), (3), (17) and (18) is the one cyclic
Agree gives. -/
theorem controller_rows : ∀ e ∈ Examples.all, ∀ c ∈ config? e, ∀ p ∈ person? e "controller",
    c.1.value c.2 = p := by
  decide +kernel

/-- The direct and inverse contexts of the examples in (22) and (29) are those of cyclic Agree. -/
theorem context_rows : ∀ e ∈ Examples.all, ∀ c ∈ config? e, ∀ x ∈ e.feature? "context",
    (x = "inverse" ↔ c.1.IsInverse c.2) := by
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
theorem basque_prefix_rows : ∀ e ∈ Examples.all, e.language = "basq1248" →
    ∀ c ∈ config? e, ∀ _ ∈ person? e "controller", ∃ n ∈ [Number.singular, .plural],
      ((match c.1.controller c.2 with
        | .ia => Basque.absolutive
        | .ea => Basque.displacedErgative).realize
          (.personNumber (c.1.value c.2) n)).bind (·.head?) = slotPrefix? e := by
  decide +kernel

/-- The Georgian affix set that spells the core probe in (21) is Set B when the internal argument
values it on the first cycle and Set A when the external argument values it on the second. -/
def georgianSet : Argument → Georgian.AffixSet
  | .ia => .B
  | .ea => .A

-- (18)
theorem georgian_prefix_rows : ∀ e ∈ Examples.all, e.language = "nucl1302" →
    ∀ c ∈ config? e,
      ((georgianSet (c.1.controller c.2)).paradigm.realize
          (.personNumber (c.1.value c.2) .singular)).bind (·.head?) = slotPrefix? e := by
  decide +kernel

end BejarRezac2009
