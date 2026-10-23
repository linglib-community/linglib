module

public import Linglib.Syntax.Minimalist.Probe.Phi

/-!
# Béjar and Rezac 2003: person licensing and the Person Case Constraint

Béjar and Rezac derive the Person Case Constraint, that the direct object of two weak objects
cannot be 1st or 2nd person, from the Person Licensing Condition, that an interpretable 1st/2nd
person feature must enter an Agree relation with a functional category. A φ/Case head probes for
person and then for number, each search halting at the closest nominal and Agreeing with it only
if its Case is unvalued. A dative, whose Case its own preposition has valued, absorbs the person
probe and displaces, so the number probe reaches the theme and values its Case while the theme's
person goes unlicensed. Every repair adds a person probe: a theme above a prepositional dative, or
in a dative–nominative construction the projection of T, once the nominative's φ-features have
risen above the dative, as in French and Spanish but not in Icelandic.

## Main definitions

* `BejarRezac2003.Nominal`: a φ-goal with whether its person feature is licensed.
* `BejarRezac2003.Head`: a φ/Case head, with the Case it assigns, its EPP, and whether its
  nominative's φ-features rise as a head.
* `BejarRezac2003.Head.derive`: the derivation of a head's domain.
* `BejarRezac2003.PLC`: the Person Licensing Condition.

## Main results

* `BejarRezac2003.applicative_derive`: a dative is what its own preposition's derivation yields.
* `BejarRezac2003.doc_plc_iff`: the constraint in a double object construction.
* `BejarRezac2003.pp_plc`: the prepositional construction escapes it.
* `BejarRezac2003.dnc_plc_iff`: a dative–nominative construction obeys it iff the dative satisfies
  the EPP and the nominative's φ-features stay below it.

## Implementation notes

The number probe values Case after the projection's person probe has searched, where the paper
orders it before: valued Case would make the nominative inactive for that later search, which
(17) requires to reach it, and in every configuration of the paper the number probe finds the same
nominal either way. The displacement of the nominal that absorbs the person probe is taken as
given, so the crash of (4), where the dative cannot displace, is not modelled. The prose on p. 55
swaps the two constructions of (11); the diagram, which agrees with the low prepositional dative of
§2, is followed.

## TODO

The general form of the conclusion, that a nominal with unvalued Case is licensed iff it is the
closest match of the head's first or reprojected person probe, is stated only configuration by
configuration. Causatives and restructuring (2), nominalizations, and focused pronouns (§4) are not
modelled.

## References

* [bejar-rezac-2003]
* [bonet-1991]
* [chomsky-2000]
* [anagnostopoulou-2003]
* [harley-ritter-2002]
* [zaenen-maling-thrainsson-1985]
* [taraldsen-1995]
* [sigurdsson-1996]
-/

@[expose] public section

namespace BejarRezac2003

open Minimalist Agreement

/-- A nominal in the domain of a φ/Case head is a φ-goal together with whether its person feature
has entered an Agree relation with a functional category. -/
structure Nominal extends PhiGoal where
  licensed : Bool
  deriving DecidableEq, Repr

namespace Nominal

/-- `Nominal.caseless c` is a nominal with φ-cell `c`, unvalued Case, and unlicensed person. -/
def caseless (c : Bundle) : Nominal := ⟨.unvalued c, false⟩

/-- `Nominal.dat c` is a dative, whose Case and person its own preposition has valued and
licensed (§4). -/
def dat (c : Bundle) : Nominal := ⟨.valued .dat c, true⟩

@[simp] theorem isActive_caseless (c : Bundle) : (caseless c).isActive = true := rfl
@[simp] theorem isActive_dat (c : Bundle) : (dat c).isActive = false := rfl
@[simp] theorem cell_caseless (c : Bundle) : (caseless c).cell = c := rfl
@[simp] theorem cell_dat (c : Bundle) : (dat c).cell = c := rfl
@[simp] theorem licensed_caseless (c : Bundle) : (caseless c).licensed = false := rfl
@[simp] theorem licensed_dat (c : Bundle) : (dat c).licensed = true := rfl

end Nominal

open Nominal

/-! ### Agree -/

/-- The person and the number probe of a φ/Case head halt at the closest nominal, since every
nominal bears person and number ((8)), and Agree with it iff its Case is unvalued (§2). -/
def phiProbe : Probe Nominal := .ofInt (·.isActive)

/-- `agreeWith f ns` applies `f` to the goal `phiProbe` Agrees with in `ns`, the closest nominal
if its Case is unvalued; an inactive closest nominal absorbs the probe ((9)). -/
def agreeWith (f : Nominal → Nominal) (ns : List Nominal) : List Nominal :=
  ns.modifyHead fun n ↦ if n.isActive then f n else n

theorem agreeWith_eq (f : Nominal → Nominal) (ns : List Nominal) :
    agreeWith f ns = match phiProbe.goal ns with
      | some n => f n :: ns.tail
      | none => ns := by
  cases ns with
  | nil => rfl
  | cons n ns =>
    simp only [agreeWith, List.modifyHead_cons, Probe.goal, phiProbe, Probe.ofInt_search,
      List.head?_cons, Option.filter_some, Probe.ofInt_int, List.tail_cons]
    by_cases h : n.isActive <;> simp [h]

theorem agreeWith_eq_map (f : Nominal → Nominal) {ns : List Nominal} (hns : ns.Nodup) :
    agreeWith f ns = ns.map fun n ↦ if phiProbe.goal ns = some n then f n else n := by
  cases ns with
  | nil => rfl
  | cons n ns =>
    obtain ⟨hn, -⟩ := List.nodup_cons.mp hns
    rw [agreeWith_eq, List.map_cons]
    cases hg : phiProbe.goal (n :: ns) with
    | none => simp
    | some m =>
      have hm : n = m := by
        simpa [Probe.goal, phiProbe] using (Probe.goal_eq_some_iff.mp hg).1
      subst hm
      simp only [ite_true, List.tail_cons, List.cons.injEq, true_and]
      refine ((List.map_congr_left fun r hr ↦ ?_).trans (List.map_id' ns)).symm
      exact ite_eq_right fun he ↦ hn (by rwa [Option.some.inj he])

/-- Agree for person licenses its goal's person feature. -/
def piAgree : List Nominal → List Nominal := agreeWith fun n ↦ { n with licensed := true }

/-- Agree for number values its goal's Case with `c`. The inactive nominal that absorbed the
person probe has displaced, cliticized or raised, and the number probe looks past its trace
((10), (16b)). -/
def numAgree (c : Case) : List Nominal → List Nominal
  | [] => []
  | n :: ns =>
    if n.isActive then agreeWith (fun m ↦ { m with valuedCase := some c }) (n :: ns)
    else n :: agreeWith (fun m ↦ { m with valuedCase := some c }) ns

/-- `raise can ns` moves the closest nominal of `ns` satisfying `can` to the top (§5). -/
def raise (can : Nominal → Bool) (ns : List Nominal) : List Nominal :=
  ((Probe.relativized (can ·)).search ns).toList ++ ns.eraseP can

/-! ### Heads and their derivations -/

/-- A φ/Case head assigns a Case, may bear an EPP feature satisfied by the closest nominal for
which `epp` holds, and, in a language with pro-drop, has a nominative whose φ-features rise as a
head above everything else (§5, §6). -/
structure Head where
  case : Case
  epp : Option (Nominal → Bool) := none
  agrX0 : Bool := false

/-- The derivation of a head's domain. The person probe searches the base order; if the head has
an EPP feature, the nominal satisfying it raises, a rising nominative φ-head raises above it, and
the projection of the head probes again for person; the number probe values the head's Case last
((8)–(10), (16)–(17), (25)). -/
def Head.derive (F : Head) (ns : List Nominal) : List Nominal :=
  numAgree F.case <| match F.epp with
    | none => piAgree ns
    | some can =>
      piAgree <| (if F.agrX0 then raise (·.isActive) else id) (raise can (piAgree ns))

/-- The Person Licensing Condition holds of a domain when every nominal with an interpretable
1st/2nd person feature has had it licensed (§3). -/
def PLC (ns : List Nominal) : Prop := ∀ n ∈ ns, n.cell.IsSAP → n.licensed = true

instance : DecidablePred PLC := fun ns ↦
  inferInstanceAs (Decidable (∀ n ∈ ns, n.cell.IsSAP → n.licensed = true))

/-- The applicative preposition assigns dative to its complement (§4). -/
def applicative : Head := { case := .dat }

/-- v assigns accusative (§3). -/
def v : Head := { case := .acc }

/-- Icelandic T has an EPP feature that a dative can satisfy (§5). -/
def icelandicT : Head := { case := .nom, epp := some fun _ ↦ true }

/-- French T has an EPP feature that a dative cannot satisfy (§5). -/
def frenchT : Head := { case := .nom, epp := some (·.valuedCase != some .dat) }

/-- Spanish T has an EPP feature that a dative can satisfy, and its nominative's φ-features rise
as a head above the dative (§6). -/
def spanishT : Head := { case := .nom, epp := some fun _ ↦ true, agrX0 := true }

/-! ### The preposition's own domain -/

/-- A dative is the nominal its own preposition's derivation yields, inherent Case being
structural Case valued under Agree with the preposition (§4). -/
theorem applicative_derive (c : Bundle) : applicative.derive [caseless c] = [dat c] := rfl

/-! ### The double object and prepositional constructions -/

/-- In a double object construction the dative absorbs v's person probe and the number probe
values accusative on the theme, whose person stays unlicensed ((8)–(10)). -/
theorem v_derive_doc (cd ca : Bundle) :
    v.derive [dat cd, caseless ca] = [dat cd, ⟨.valued .acc ca, false⟩] := rfl

/-- The double object construction obeys the condition iff its theme is 3rd person, whatever the
dative ((1), (7)). -/
theorem doc_plc_iff (cd ca : Bundle) :
    PLC (v.derive [dat cd, caseless ca]) ↔ ¬ ca.IsSAP := by
  rw [v_derive_doc]
  simp [PLC]

-- (1), (7): *le lui* licit, *te lui* excluded.
example :
    PLC (v.derive [dat (.personNumber .third .singular),
      caseless (.personNumber .third .singular)]) ∧
    ¬ PLC (v.derive [dat (.personNumber .third .singular),
      caseless (.personNumber .second .singular)]) := by
  decide

/-- In the prepositional construction the theme is v's closest nominal and both its probes reach
it ((11a)). -/
theorem v_derive_pp (ct cg : Bundle) :
    v.derive [caseless ct, dat cg] = [⟨.valued .acc ct, true⟩, dat cg] := rfl

/-- The prepositional construction obeys the condition whatever the theme's person ((3)). -/
theorem pp_plc (ct cg : Bundle) : PLC (v.derive [caseless ct, dat cg]) := by
  rw [v_derive_pp]
  simp [PLC]

/-- One search licenses one nominal, so two caseless participants never both obey the condition. -/
example : ¬ PLC (v.derive [caseless (.personNumber .first .singular),
    caseless (.personNumber .first .singular)]) := by
  decide

/-! ### Dative–nominative constructions -/

/-- In Icelandic the dative stays the highest φ-bearer, absorbing both of T's person probes, and
the nominative gets only T's number ((12), (25c)). -/
theorem icelandicT_derive (cd cn : Bundle) :
    icelandicT.derive [dat cd, caseless cn] = [dat cd, ⟨.valued .nom cn, false⟩] := rfl

/-- In French the nominative moves over the dative to Spec,TP, and the projection of T licenses
its person ((16), (17), (25b)). -/
theorem frenchT_derive (cd cn : Bundle) :
    frenchT.derive [dat cd, caseless cn] = [⟨.valued .nom cn, true⟩, dat cd] := rfl

/-- In Spanish the nominative's φ-features rise as a head above the dative in Spec,TP, and T
licenses its person ((25a)). -/
theorem spanishT_derive (cd cn : Bundle) :
    spanishT.derive [dat cd, caseless cn] = [⟨.valued .nom cn, true⟩, dat cd] := rfl

/-- A dative–nominative construction obeys the condition iff its nominative is 3rd person or its
φ-features end up above the dative (§5, §6). -/
theorem dnc_plc_iff (can : Nominal → Bool) (hcan : ∀ c, can (caseless c) = true) (x0 : Bool)
    (cd cn : Bundle) :
    PLC (({ case := .nom, epp := some can, agrX0 := x0 } : Head).derive [dat cd, caseless cn]) ↔
      (can (dat cd) = true ∧ x0 = false → ¬ cn.IsSAP) := by
  cases h : can (dat cd) <;> cases x0 <;>
    simp [Head.derive, raise, piAgree, numAgree, agreeWith, Probe.search, Probe.relativized, h,
      hcan, PLC]

-- (12) Icelandic *þið* excluded; (13) French *je lui fus présenté* and (18) Spanish
-- *(yo) le fui presentado* licit.
example :
    ¬ PLC (icelandicT.derive [dat (.personNumber .third .singular),
        caseless (.personNumber .second .plural)]) ∧
    PLC (frenchT.derive [dat (.personNumber .third .singular),
        caseless (.personNumber .first .singular)]) ∧
    PLC (spanishT.derive [dat (.personNumber .third .singular),
        caseless (.personNumber .first .singular)]) := by
  decide

end BejarRezac2003
