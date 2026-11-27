module

public import Linglib.Syntax.Minimalist.Probe.Minimal
public import Linglib.Syntax.Minimalist.Probe.Phi
public import Linglib.Syntax.Minimalist.Feature.Valuation

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

* `BejarRezac2003.Nominal`: the feature bundle of a nominal, with whether its person feature is
  licensed.
* `BejarRezac2003.Head`: a φ/Case head, with the Case it assigns, its EPP, and whether its
  nominative's φ-features rise as a head.
* `BejarRezac2003.Head.reproject`: the order in which the projection of a head meets its domain.
* `BejarRezac2003.Head.derive`: the derivation of a head's domain.
* `BejarRezac2003.PLC`: the Person Licensing Condition.

## Implementation notes

The number probe values Case after the projection's person probe has searched, where the paper
orders it before: valued Case would make the nominative inactive for that later search, which
(17) requires to reach it, and in every configuration of the paper the number probe finds the same
nominal either way. The displacement of the nominal that absorbs the person probe is taken as
given, so the crash of (4), where the dative cannot displace, is not modelled. The prose on p. 55
swaps the two constructions of (11); the diagram, which agrees with the low prepositional dative of
§2, is followed.

## TODO

The general form of the conclusion is proved cycle by cycle: a domain obeys the condition iff
the head's last person probe Agrees with every nominal still unlicensed in the order it searches.
The form on the positions of the base order, that the probe agrees with each such position under
the base closeness or under the closeness after movement, is not proved; it needs an EPP that
does not read licensing. Causatives and restructuring (2), nominalizations, and focused pronouns
(§4) are not modelled.

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

/-- A nominal in the domain of a φ/Case head has a feature bundle, with its φ-cell and its case
slot, and its person feature has or has not entered an Agree relation with a functional category. -/
structure Nominal where
  features : FeatureBundle
  licensed : Bool
  deriving DecidableEq, Repr

namespace Nominal

/-- `Nominal.caseless c` is a nominal with φ-cell `c`, unvalued Case, and unlicensed person. -/
def caseless (c : Bundle) : Nominal := ⟨.nominal c .unvalued, false⟩

/-- `Nominal.dat c` is a dative, whose Case and person its own preposition has valued and
licensed (§4). -/
def dat (c : Bundle) : Nominal := ⟨.nominal c (.valued .dat), true⟩

/-- The nominal with its Case valued `c`. -/
def valueCase (c : Case) (n : Nominal) : Nominal :=
  { n with features := (FeatureBundle.valueAt n.features .case c).untopD n.features }

/-- A bundle bears a 1st/2nd person feature. -/
def HasFirstOrSecond (b : Bundle) : Prop := ∃ p : Person, b.person = ↑p ∧ p ≠ .third

instance : DecidablePred HasFirstOrSecond := fun b ↦
  inferInstanceAs (Decidable (∃ p : Person, b.person = ↑p ∧ p ≠ .third))

@[simp] theorem hasFirstOrSecond_update_case {c : Bundle} {x : Flat Case} :
    HasFirstOrSecond (Function.update c .case x) ↔ HasFirstOrSecond c := by
  simp [HasFirstOrSecond, Agreement.Bundle.person]

/-- A nominal needs licensing when it bears an unlicensed 1st/2nd person feature (§3). -/
def Needs (n : Nominal) : Prop := HasFirstOrSecond n.features.agreement ∧ n.licensed = false

instance : DecidablePred Needs := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem features_caseless (c : Bundle) : (caseless c).features = .nominal c .unvalued :=
  rfl
@[simp] theorem features_dat (c : Bundle) : (dat c).features = .nominal c (.valued .dat) := rfl
@[simp] theorem licensed_caseless (c : Bundle) : (caseless c).licensed = false := rfl
@[simp] theorem licensed_dat (c : Bundle) : (dat c).licensed = true := rfl

@[simp] theorem valueCase_nominal (k : Case) (c : Bundle) (l : Bool) :
    valueCase k ⟨.nominal c .unvalued, l⟩ = ⟨.nominal c (.valued k), l⟩ := by
  rw [valueCase, FeatureBundle.valueAt,
    FeatureBundle.unifyAt_of_eq_coe_bot (FeatureBundle.nominal_case ..), WithTop.untopD_coe]
  exact congrArg (Nominal.mk · l) (FeatureBundle.update_case_nominal (c := c) (.valued k))

@[simp] theorem valueCase_caseless (k : Case) (c : Bundle) :
    valueCase k (caseless c) = ⟨.nominal c (.valued k), false⟩ :=
  valueCase_nominal k c false

end Nominal

open Nominal

/-! ### Agree -/

/-- The person and the number probe of a φ/Case head halt at the closest nominal, since every
nominal bears person and number ((8)), and Agree with it iff its Case is unvalued (§2). -/
def phiProbe : Probe Nominal := .ofInt (·.features.IsActive)

/-- `agreeWith f ns` is Agree of `phiProbe` over `ns`, copying by `f`: it applies `f` to the closest
nominal if its Case is unvalued, and an inactive closest nominal absorbs the probe ((9)). -/
def agreeWith (f : Nominal → Nominal) (ns : List Nominal) : List Nominal :=
  phiProbe.agreeList f ns

@[simp] theorem agreeWith_nil (f : Nominal → Nominal) : agreeWith f [] = [] := rfl

@[simp] theorem agreeWith_cons (f : Nominal → Nominal) (n : Nominal) (ns : List Nominal) :
    agreeWith f (n :: ns) = (if n.features.IsActive then f n else n) :: ns := by
  rw [agreeWith, Probe.agreeList_cons]
  simp [phiProbe]

theorem agreeWith_eq (f : Nominal → Nominal) (ns : List Nominal) :
    agreeWith f ns = match phiProbe.goal ns with
      | some n => f n :: ns.tail
      | none => ns := by
  cases ns with
  | nil => rfl
  | cons n ns =>
    simp only [agreeWith_cons, Probe.goal, phiProbe, Probe.ofInt_search, List.head?_cons,
      Option.filter_some, Probe.ofInt_int, List.tail_cons]
    by_cases h : n.features.IsActive <;> simp [h]

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
    if n.features.IsActive then agreeWith (valueCase c) (n :: ns)
    else n :: agreeWith (valueCase c) ns

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

/-- The order in which the projection of a head meets its domain: the nominal satisfying the EPP
has raised, and a rising nominative φ-head has raised above it ((16), (25)). -/
def Head.reproject (F : Head) (can : Nominal → Bool) (ns : List Nominal) : List Nominal :=
  (if F.agrX0 then raise (decide ·.features.IsActive) else id) (raise can ns)

/-- The derivation of a head's domain. The person probe searches the base order; if the head has
an EPP feature, the projection of the head probes again for person in the order `Head.reproject`
gives; the number probe values the head's Case last ((8)–(10), (16)–(17), (25)). -/
def Head.derive (F : Head) (ns : List Nominal) : List Nominal :=
  numAgree F.case <| match F.epp with
    | none => piAgree ns
    | some can => piAgree (F.reproject can (piAgree ns))

/-- The Person Licensing Condition holds of a domain when every nominal with an interpretable
1st/2nd person feature has had it licensed (§3). -/
def PLC (ns : List Nominal) : Prop :=
  ∀ n ∈ ns, HasFirstOrSecond n.features.agreement → n.licensed = true

instance : DecidablePred PLC := fun ns ↦
  inferInstanceAs (Decidable (∀ n ∈ ns, HasFirstOrSecond n.features.agreement → n.licensed = true))

private theorem hasFirstOrSecond_valueCase (k : Case) (n : Nominal) :
    HasFirstOrSecond (valueCase k n).features.agreement ↔
      HasFirstOrSecond n.features.agreement := by
  rw [valueCase, FeatureBundle.valueAt, FeatureBundle.unifyAt]
  cases (n.features FeatureType.case).unifyWith _ _ <;> simp [FeatureBundle.agreement_update_agr]

private theorem plc_cons {n : Nominal} {ns : List Nominal} :
    PLC (n :: ns) ↔ (HasFirstOrSecond n.features.agreement → n.licensed = true) ∧ PLC ns :=
  List.forall_mem_cons

private theorem plc_agreeWith_valueCase (k : Case) (ns : List Nominal) :
    PLC (agreeWith (valueCase k) ns) ↔ PLC ns := by
  cases ns with
  | nil => rfl
  | cons n ns =>
    rw [agreeWith_cons, plc_cons, plc_cons]
    split_ifs
    · exact and_congr_left' (imp_congr_left (hasFirstOrSecond_valueCase k n))
    · rfl

private theorem plc_numAgree (k : Case) (ns : List Nominal) :
    PLC (numAgree k ns) ↔ PLC ns := by
  cases ns with
  | nil => rfl
  | cons n ns =>
    rw [numAgree]
    split_ifs
    · exact plc_agreeWith_valueCase k _
    · rw [plc_cons, plc_cons, plc_agreeWith_valueCase]

private theorem allLicensed_phiProbe_cons {needs : Nominal → Prop} {n : Nominal}
    {ns : List Nominal} :
    phiProbe.AllLicensed needs (n :: ns) ↔
      (needs n → n.features.IsActive) ∧ ∀ m ∈ ns, ¬ needs m := by
  rw [Probe.allLicensed_cons]
  simp only [phiProbe, Probe.ofInt_int, Probe.ofInt_sat, not_true_eq_false, imp_false]
  exact and_congr_right' ⟨And.left, fun h ↦ ⟨h, Probe.allLicensed_of_forall_not h⟩⟩

private theorem plc_piAgree (ns : List Nominal) :
    PLC (piAgree ns) ↔ phiProbe.AllLicensed Needs ns := by
  cases ns with
  | nil => simp [piAgree, PLC]
  | cons n ns =>
    rw [piAgree, agreeWith_cons, plc_cons, allLicensed_phiProbe_cons]
    by_cases h : n.features.IsActive <;> simp [h, PLC, Needs]

-- A head without an EPP feature has one person probe, which searches the base order.
theorem plc_derive_iff (F : Head) (hF : F.epp = none) (ns : List Nominal) :
    PLC (F.derive ns) ↔ phiProbe.AllLicensed Needs ns := by
  rw [Head.derive, hF, plc_numAgree, plc_piAgree]

/-- A head with an EPP feature derives a domain that obeys the condition exactly when the person
probe of its projection Agrees with every nominal the first cycle left unlicensed. -/
theorem plc_derive_iff_of_epp (F : Head) {can : Nominal → Bool} (hF : F.epp = some can)
    (ns : List Nominal) :
    PLC (F.derive ns) ↔ phiProbe.AllLicensed Needs (F.reproject can (piAgree ns)) := by
  rw [Head.derive, hF, plc_numAgree, plc_piAgree]

/-- The applicative preposition assigns dative to its complement (§4). -/
def applicative : Head := { case := .dat }

/-- v assigns accusative (§3). -/
def v : Head := { case := .acc }

/-- Icelandic T has an EPP feature that a dative can satisfy (§5). -/
def icelandicT : Head := { case := .nom, epp := some fun _ ↦ true }

/-- French T has an EPP feature that a dative cannot satisfy (§5). -/
def frenchT : Head :=
  { case := .nom, epp := some fun n ↦ decide (n.features .case ≠ .valued .dat) }

/-- Spanish T has an EPP feature that a dative can satisfy, and its nominative's φ-features rise
as a head above the dative (§6). -/
def spanishT : Head := { case := .nom, epp := some fun _ ↦ true, agrX0 := true }

/-! ### The preposition's own domain -/

/-- A dative is the nominal its own preposition's derivation yields, inherent Case being
structural Case valued under Agree with the preposition (§4). -/
theorem applicative_derive (c : Bundle) : applicative.derive [caseless c] = [dat c] :=
  by simp [Head.derive, numAgree, piAgree, applicative, caseless, dat]

/-! ### The double object and prepositional constructions -/

-- (8), (10)
theorem v_derive_doc (cd ca : Bundle) :
    v.derive [dat cd, caseless ca] = [dat cd, ⟨.nominal ca (.valued .acc), false⟩] :=
  by simp [Head.derive, numAgree, piAgree, v, caseless, dat]

/-- The double object construction obeys the condition iff its theme is 3rd person, whatever the
dative ((1), (7)). -/
theorem doc_plc_iff (cd ca : Bundle) :
    PLC (v.derive [dat cd, caseless ca]) ↔ ¬ HasFirstOrSecond ca := by
  rw [v_derive_doc]
  simp [PLC]

-- (1), (7): *le lui* licit, *te lui* excluded.
example :
    PLC (v.derive [dat (.personNumber .third .singular),
      caseless (.personNumber .third .singular)]) ∧
    ¬ PLC (v.derive [dat (.personNumber .third .singular),
      caseless (.personNumber .second .singular)]) := by
  decide

-- (11a)
theorem v_derive_pp (ct cg : Bundle) :
    v.derive [caseless ct, dat cg] = [⟨.nominal ct (.valued .acc), true⟩, dat cg] :=
  by simp [Head.derive, numAgree, piAgree, v, caseless, dat]

/-- The prepositional construction obeys the condition whatever the theme's person ((3)). -/
theorem pp_plc (ct cg : Bundle) : PLC (v.derive [caseless ct, dat cg]) := by
  rw [v_derive_pp]
  simp [PLC]

/-- One search licenses one nominal, so two caseless participants never both obey the condition. -/
example : ¬ PLC (v.derive [caseless (.personNumber .first .singular),
    caseless (.personNumber .first .singular)]) := by
  decide

/-! ### Dative–nominative constructions -/

-- (12), (25c)
theorem icelandicT_derive (cd cn : Bundle) :
    icelandicT.derive [dat cd, caseless cn] = [dat cd, ⟨.nominal cn (.valued .nom), false⟩] :=
  by simp [Head.derive, Head.reproject, numAgree, piAgree, raise, Probe.search, Probe.relativized,
      icelandicT, caseless, dat]

-- (16), (17), (25b)
theorem frenchT_derive (cd cn : Bundle) :
    frenchT.derive [dat cd, caseless cn] = [⟨.nominal cn (.valued .nom), true⟩, dat cd] :=
  by simp [Head.derive, Head.reproject, numAgree, piAgree, raise, Probe.search, Probe.relativized,
      frenchT, caseless, dat]

-- (25a)
theorem spanishT_derive (cd cn : Bundle) :
    spanishT.derive [dat cd, caseless cn] = [⟨.nominal cn (.valued .nom), true⟩, dat cd] :=
  by simp [Head.derive, Head.reproject, numAgree, piAgree, raise, Probe.search, Probe.relativized,
      spanishT, caseless, dat]

/-- A dative–nominative construction obeys the condition iff its nominative is 3rd person or its
φ-features end up above the dative (§5, §6). -/
theorem dnc_plc_iff (can : Nominal → Bool) (hcan : ∀ c, can (caseless c) = true) (x0 : Bool)
    (cd cn : Bundle) :
    PLC (({ case := .nom, epp := some can, agrX0 := x0 } : Head).derive [dat cd, caseless cn]) ↔
      (can (dat cd) = true ∧ x0 = false → ¬ HasFirstOrSecond cn) := by
  cases h : can (dat cd) <;> cases x0 <;>
    simp [Head.derive, Head.reproject, raise, piAgree, numAgree, Probe.search, Probe.relativized, h,
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
