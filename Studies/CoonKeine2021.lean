module

public import Linglib.Syntax.Minimalist.Probe.Cyclic
public import Linglib.Syntax.Agreement.PersonCaseConstraint
public import Linglib.Morphology.Exponence.Select
public import Studies.BejarRezac2003
public import Linglib.Data.Examples.CoonKeine2021

/-!
# Coon and Keine 2021: feature gluttony

Coon and Keine argue that hierarchy effects, the Person Case Constraint on clitic clusters,
the person restriction on Icelandic dative-nominative agreement and the person and number
restrictions on German assumed-identity copulas, come not from failed Agree but from too much
of it. A probe is a hierarchy of segments, each of which agrees on its own with the closest
accessible DP bearing it and copies that DP's whole geometry back, so when the lower of two DPs
bears segments the higher lacks, distinct segments agree with distinct DPs and the probe is
gluttonous, which happens in inverse configurations only. Gluttony is harmless in itself: a
clitic-doubling probe crashes because every DP it agreed with must cliticize and binary Merge
cannot move two heads at once, while an agreement probe crashes only if the values it carries
demand different Vocabulary items, so syncretism or the absence of an item lets a gluttonous
probe converge. Articulating the person probe further along the speaker and addressee leaves of
the person geometry derives the Weak, Ultrastrong and Me-First constraints, datives that expose
their person node alone turn the Weak pattern into the Strong one, and since a nonfinite clause
has no probe and a PP, a strong pronoun or absolutive displacement leaves no second goal, the
absence of the effects there follows without the caveats a Person Licensing Condition needs.

## Implementation notes

Goals are position-indexed so that two DPs with the same features stay distinct, and a
segment's Agree is the relativized search of the probe substrate over that list, so the
two-goal characterization of gluttony rests on the substrate's search. Person geometries are
the branching geometry of the cyclic-Agree substrate and number the two-segment geometry of the
paper; the model pairs a number probe with every person probe, one direction of the paper's
probe-specification hierarchy. A K-encapsulated dative exposes its person node and no number:
the paper leaves the dative's number open in a footnote and says a quirky DP externally bears
at most a person feature, and the choice is what puts the nominative's number in the context
the paper's diagrams caption. The crash of a gluttonous clitic-doubling probe is taken as the
paper argues it, from its cliticization requirement, binary Merge and a Markovian derivation,
rather than derived. A paradigm holds the forms the paper glosses, with German present *bin*
added since the past-tense improvement the paper reports presupposes it, and is undefined in
number contexts the paper does not gloss, so that an unglossed cell cannot converge by
accident; the item a value demands is the score selection of the exponence substrate with the
segment count as specificity, and a value demanding no item, the Kichean singular, competes
with nothing. The person-case-constraint grammars of the substrate parametrize the descriptive
table the probes derive; the Ultrastrong probe parts from that parametrization at 2 > 2 and the
Me-First probe from the table itself at 1 > 1, a cell the paper does not remark on. The
comparison with the Person Licensing Condition is the paper's own argument from probeless
clauses, and the restricted condition keeps the escape through a Case-valuing head that the
substrate formalization of the original condition has. Examples the paper records without an
account, the Icelandic copulas, default agreement, participle agreement and the expletive, carry
no configuration and enter no theorem.

## TODO

- Fission and portmanteau realization of a gluttonous agreement probe (§5.2) are not modelled.

## References

* [coon-keine-2021]
* [S. Béjar and M. Rezac, *Cyclic Agree* (2009)][bejar-rezac-2009]
* [H. Harley and E. Ritter, *Person and number in pronouns: A feature-geometric analysis*
  (2002)][harley-ritter-2002]
* [S. Béjar and M. Rezac, *Person licensing and the derivation of PCC effects*
  (2003)][bejar-rezac-2003]
* [O. Preminger, *Asymmetries between person and number in syntax* (2011)][preminger-2011]
* [O. Preminger, *Agreement and Its Failures* (2014)][preminger-2014]
* [O. Preminger, *What the PCC tells us about "abstract" agreement, head movement, and
  locality* (2019)][preminger-2019]
* [A. R. Deal, *Interaction and satisfaction in φ-agreement* (2015)][deal-2015a-nels]
* [R. Pancheva and M. L. Zubizarreta, *The Person Case Constraint: The syntactic encoding of
  perspective* (2018)][pancheva-zubizarreta-2018]
* [A. Stegovec, *Taking case out of the Person-Case Constraint* (2020)][stegovec-2020]
* [H. Á. Sigurðsson and A. Holmberg, *Icelandic dative intervention: Person and number are
  separate probes* (2008)][sigurdsson-holmberg-2008]
* [C. T. Schütze, *Syncretism and double agreement with Icelandic nominative objects*
  (2003)][schutze-2003]
* [J. Coon, S. Keine and M. Wagner, *Hierarchy effects in copular constructions: The PCC corner
  of German* (2017)][coon-keine-wagner-2017]
* [S. Keine, M. Wagner and J. Coon, *Hierarchy effects in copula constructions*
  (2019)][keine-wagner-coon-2019]
* [H. Thráinsson, *Icelandic* (1994)][thrainsson-1994]
-/

@[expose] public section

namespace CoonKeine2021

open Minimalist Minimalist.CyclicAgree Morphology.Exponence Phi

/-! ### Goals and their visible geometries -/

/-- The goals' languages distinguish the singular and the plural. -/
def numberSystem : Number.System := { values := {.singular, .plural} }

/-- A goal DP may sit in the K(ase) shell that encapsulates a dative, so that only its person node
is visible from outside, as with Basque and Icelandic datives (§3.4.1). -/
structure Goal where
  /-- The DP's person. -/
  person : Person
  /-- The DP's number. -/
  number : numberSystem.values := numberSystem.value .singular
  /-- Whether a K shell hides everything but the person node. -/
  encapsulated : Bool := false
  deriving DecidableEq, Repr

/-- A φ-transparent goal. -/
def dp (p : Person) : Goal := { person := p }

/-- A φ-transparent plural goal. -/
def dpPl (p : Person) : Goal := { person := p, number := numberSystem.value .plural }

/-- A K-encapsulated dative goal. -/
def dat (p : Person) : Goal := { person := p, encapsulated := true }

/-- A goal exposes the person segments of its geometry under (11), or its person node alone. -/
def Goal.personSegments (g : Goal) : List PersonSegment :=
  if g.encapsulated then [.pi] else personSpec .branching g.person

/-- Number geometry (12). -/
inductive NumberSegment where
  /-- [NUM], borne by every DP. -/
  | num
  /-- [PL], borne by plurals. -/
  | pl
  deriving DecidableEq, Repr

/-- The number segments a goal exposes; an encapsulated goal exposes none. -/
def Goal.numberSegments (g : Goal) : List NumberSegment :=
  if g.encapsulated then [] else numberSystem.elim [.num] [.num, .pl] (n := g.number)

theorem pi_mem_personSegments (g : Goal) : PersonSegment.pi ∈ g.personSegments := by
  unfold Goal.personSegments
  split <;> [exact .head _; exact pi_mem_personSpec _ _]

/-- A goal read as a nominal of [bejar-rezac-2003] has its Case valued and its person licensed by
its own head when it is an encapsulated dative, and neither when it is transparent. -/
def Goal.toNominal (g : Goal) : BejarRezac2003.Nominal :=
  let cell := Agreement.Bundle.personNumber g.person g.number.1
  if g.encapsulated then .dat cell else .caseless cell

/-! ### Segment-based Agree and gluttony (14)–(16) -/

section Agree

variable {σ : Type*} [DecidableEq σ]

/-- A probe segment is the relativized probe over position-indexed goals that sees the goals
whose geometry bears it. -/
def segmentProbe (geo : Goal → List σ) (s : σ) : Probe (Goal × ℕ) :=
  .relativized fun t ↦ decide (s ∈ geo t.1)

/-- Agree (14) for one probe segment finds the closest accessible goal whose geometry bears it. -/
def segmentAgree (geo : Goal → List σ) (s : σ) (goals : List Goal) : Option (Goal × ℕ) :=
  (segmentProbe geo s).search goals.zipIdx

/-- The goals some segment of the probe has agreed with. -/
def agreed (geo : Goal → List σ) (P : List σ) (goals : List Goal) : List (Goal × ℕ) :=
  goals.zipIdx.filter fun t ↦ P.any fun s ↦ segmentAgree geo s goals == some t

/-- Feature gluttony (16) is the probe's having agreed with more than one DP. -/
def Gluttonous (geo : Goal → List σ) (P : List σ) (goals : List Goal) : Prop :=
  ∃ t ∈ agreed geo P goals, ∃ u ∈ agreed geo P goals, t ≠ u

instance (geo : Goal → List σ) (P : List σ) (goals : List Goal) :
    Decidable (Gluttonous geo P goals) := by
  unfold Gluttonous; infer_instance

/-- The values the probe carries after Agree, one whole geometry per agreed goal ((16),
(58)). -/
def values (geo : Goal → List σ) (P : List σ) (goals : List Goal) : List (List σ) :=
  (agreed geo P goals).map (geo ·.1)

variable {geo : Goal → List σ} {P : List σ} {goals : List Goal} {s : σ}

theorem mem_agreed {t : Goal × ℕ} :
    t ∈ agreed geo P goals ↔
      t ∈ goals.zipIdx ∧ ∃ s ∈ P, segmentAgree geo s goals = some t := by
  simp [agreed]

/-- Agree over two goals finds the higher if it bears the segment, else the lower if it does. -/
theorem segmentAgree_pair {hi lo : Goal} :
    segmentAgree geo s [hi, lo] =
      if s ∈ geo hi then some (hi, 0) else if s ∈ geo lo then some (lo, 1) else none := by
  by_cases h₁ : s ∈ geo hi <;> by_cases h₂ : s ∈ geo lo <;>
    simp [segmentAgree, segmentProbe, Probe.search, Probe.relativized, h₁, h₂]

theorem segmentAgree_pair_eq_higher_iff {hi lo : Goal} :
    segmentAgree geo s [hi, lo] = some (hi, 0) ↔ s ∈ geo hi := by
  rw [segmentAgree_pair]; split_ifs <;> simp_all

theorem segmentAgree_pair_eq_lower_iff {hi lo : Goal} :
    segmentAgree geo s [hi, lo] = some (lo, 1) ↔ s ∉ geo hi ∧ s ∈ geo lo := by
  rw [segmentAgree_pair]; split_ifs <;> simp_all

/-- Gluttony over two goals is an inverse configuration, in which some segment finds the higher
goal and some segment the higher goal lacks finds the lower. -/
theorem gluttonous_pair_iff {hi lo : Goal} :
    Gluttonous geo P [hi, lo] ↔
      (∃ s ∈ P, s ∈ geo hi) ∧ ∃ s ∈ P, s ∉ geo hi ∧ s ∈ geo lo := by
  constructor
  · rintro ⟨t, ht, u, hu, hne⟩
    obtain ⟨ht₀, s₁, hs₁, h₁⟩ := mem_agreed.1 ht
    obtain ⟨hu₀, s₂, hs₂, h₂⟩ := mem_agreed.1 hu
    simp only [List.zipIdx_cons, List.zipIdx_nil, zero_add, List.mem_cons, List.not_mem_nil,
      or_false] at ht₀ hu₀
    rcases ht₀ with rfl | rfl <;> rcases hu₀ with rfl | rfl
    · exact absurd rfl hne
    · exact ⟨⟨s₁, hs₁, segmentAgree_pair_eq_higher_iff.1 h₁⟩,
        s₂, hs₂, segmentAgree_pair_eq_lower_iff.1 h₂⟩
    · exact ⟨⟨s₂, hs₂, segmentAgree_pair_eq_higher_iff.1 h₂⟩,
        s₁, hs₁, segmentAgree_pair_eq_lower_iff.1 h₁⟩
    · exact absurd rfl hne
  · rintro ⟨⟨s, hs, hsh⟩, s', hs', hs'h, hs'l⟩
    exact ⟨(hi, 0), mem_agreed.2 ⟨by simp, s, hs, segmentAgree_pair_eq_higher_iff.2 hsh⟩,
      (lo, 1), mem_agreed.2 ⟨by simp, s', hs', segmentAgree_pair_eq_lower_iff.2 ⟨hs'h, hs'l⟩⟩,
      by simp⟩

/-- Gluttony arises only in inverse configurations, so when the lower goal bears no segment the
higher lacks, no probe gluttons over them. -/
theorem not_gluttonous_of_subset {hi lo : Goal} (h : geo lo ⊆ geo hi) :
    ¬ Gluttonous geo P [hi, lo] :=
  fun hg ↦ let ⟨_, _, _, hsh, hsl⟩ := gluttonous_pair_iff.1 hg; hsh (h hsl)

/-- A probe over at most one goal never gluttons, as in the repairs of §3.5 and with the multiply
agreed-with DP of (86). -/
theorem not_gluttonous_of_length_le_one (h : goals.length ≤ 1) : ¬ Gluttonous geo P goals := by
  rintro ⟨t, ht, u, hu, hne⟩
  have ht' := (mem_agreed.1 ht).1
  have hu' := (mem_agreed.1 hu).1
  rcases goals with _ | ⟨_, _ | ⟨_, _⟩⟩
  · exact nomatch ht'
  · exact hne ((List.mem_singleton.1 ht').trans (List.mem_singleton.1 hu').symm)
  · simp at h

/-- A single-segment probe never gluttons (fn. 21). -/
theorem not_gluttonous_singleton : ¬ Gluttonous geo [s] goals := by
  rintro ⟨t, ht, u, hu, hne⟩
  simp only [mem_agreed, List.mem_singleton, exists_eq_left] at ht hu
  exact hne (Option.some.inj (ht.2.symm.trans hu.2))

end Agree

/-- Gluttony over a higher goal transfers to a bare 3rd person one, since whichever segment
reached the lower goal past the higher reaches it past a lone person node. -/
theorem gluttonous_third_of_gluttonous {P : Articulation} {hi lo : Goal}
    (hpi : PersonSegment.pi ∈ P) (h : Gluttonous Goal.personSegments P [hi, lo]) :
    Gluttonous Goal.personSegments P [dp .third, lo] := by
  obtain ⟨-, s, hs, hsh, hsl⟩ := gluttonous_pair_iff.1 h
  refine gluttonous_pair_iff.2 ⟨⟨.pi, hpi, pi_mem_personSegments _⟩, s, hs, fun hmem ↦ ?_, hsl⟩
  rw [show (dp .third).personSegments = [.pi] from rfl, List.mem_singleton] at hmem
  exact hsh (hmem ▸ pi_mem_personSegments hi)

/-! ### The Person Case Constraint from probe articulation (§3) -/

/-- The PCC configuration is a clitic-doubling probe over IO > DO, the IO optionally K-encapsulated.
By (30) each agreed-with DP must cliticize, which a gluttonous probe cannot satisfy, so gluttony is
the violation. -/
def PCCViolation (P : Articulation) (ioOpaque : Bool) (s : Clause.Scenario Person) : Prop :=
  Gluttonous Goal.personSegments P [{ person := s.high, encapsulated := ioOpaque }, dp s.low]

instance (P : Articulation) (b : Bool) : DecidablePred (PCCViolation P b) :=
  fun _ ↦ inferInstanceAs (Decidable (Gluttonous _ _ _))

/-- The probe [uPERS [uPART]] of (39a) yields the Weak PCC, and is the person probe of German and
Icelandic T ((55), (79)). -/
abbrev weakProbe : Articulation := partialProbe

/-- The probe [uPERS [uPART [uSPKR]]] of (39b) yields the Ultrastrong PCC. -/
abbrev ultrastrongProbe : Articulation := fullProbe .standard

/-- The probe [uPERS [uSPKR]] of (39c) yields the Me-First PCC, with a missing intermediate segment.
-/
def meFirstProbe : Articulation := [.pi, .speaker]

/-- The probe [uPERS [uPART [uSPKR] [uADDR]]] of fn. 22 (i) yields the Strong PCC over transparent
datives, and Slovenian's reversible Strong PCC (fn. 26). -/
def branchingProbe : Articulation := [.pi, .participant, .speaker, .addressee]

/-- The Weak PCC (22) bans *3 > 1/2. -/
theorem weak_pcc : ∀ s ∈ PCC.cliticPairs,
    PCCViolation weakProbe false s ↔ s.high = .third ∧ s.low ≠ .third := by
  decide +kernel

/-- Datives that expose their person node alone yield the Strong PCC, *1/2/3 > 1/2 (§3.4.1). -/
theorem strong_pcc : ∀ s ∈ PCC.cliticPairs, PCCViolation weakProbe true s ↔ s.low ≠ .third := by
  decide +kernel

/-- The Ultrastrong PCC (39b) has the Weak bans and *2 > 1. -/
theorem ultrastrong_pcc : ∀ s ∈ PCC.cliticPairs,
    PCCViolation ultrastrongProbe false s ↔
      s.high = .third ∧ s.low ≠ .third ∨ s.high = .second ∧ s.low = .first := by
  decide +kernel

/-- The Me-First probe (39c) bans a 1st person direct object under a 2nd or 3rd person
indirect object; the 1 > 1 cell of table 1 is beyond it. -/
theorem meFirst_pcc : ∀ s ∈ PCC.cliticPairs,
    PCCViolation meFirstProbe false s ↔ s.low = .first ∧ s.high ≠ .first := by
  decide +kernel

/-- The branching probe over transparent datives bans every distinct-person cluster with a
1st or 2nd person direct object. -/
theorem branching_pcc : ∀ s ∈ PCC.cliticPairs,
    PCCViolation branchingProbe false s ↔ s.low ≠ .third ∧ s.high ≠ s.low := by
  decide +kernel

/-- No probe bans a direct or balanced configuration (§3.4.2), since a 3rd person direct object
exposes nothing the indirect object lacks. -/
theorem direct_never_banned (P : Articulation) (b : Bool) (io : Person) :
    ¬ PCCViolation P b ⟨io, .third⟩ :=
  not_gluttonous_of_subset fun s hs ↦ by
    rw [show (dp .third).personSegments = [.pi] from rfl, List.mem_singleton] at hs
    exact hs ▸ pi_mem_personSegments _

/-- A probe rooted in [uPERS] that bans a cluster bans its direct object under a 3rd person
indirect object (§3.4.2), so a ban on [PART] > [PART] entails the ban on 3 > [PART]. -/
theorem pccViolation_third_of_pccViolation {P : Articulation} (hpi : PersonSegment.pi ∈ P)
    {b : Bool} {s : Clause.Scenario Person} (h : PCCViolation P b s) :
    PCCViolation P false ⟨.third, s.low⟩ :=
  gluttonous_third_of_gluttonous hpi h

section Typology

open PCC

/-- The Weak and Strong probes against the descriptive typology of table 1 as
[pancheva-zubizarreta-2018] parametrize it, cell for cell. -/
theorem weak_strong_typology :
    (∀ s ∈ cliticPairs, PCCViolation weakProbe false s ↔ ¬ IsLicit weakGrammar s) ∧
      ∀ s ∈ cliticPairs, PCCViolation weakProbe true s ↔ ¬ IsLicit strongGrammar s := by
  decide +kernel

/-- Against that parametrization the Ultrastrong probe bans every cell but 2 > 2, on which table 1
is silent, P-Uniqueness bans it, and the probe, matched throughout by the indirect object, permits
it. -/
theorem ultrastrong_typology :
    (∀ s ∈ cliticPairs, s ≠ ⟨.second, .second⟩ →
      (PCCViolation ultrastrongProbe false s ↔ ¬ IsLicit ultraStrongGrammar s)) ∧
    ¬ PCCViolation ultrastrongProbe false ⟨.second, .second⟩ ∧
      ¬ IsLicit ultraStrongGrammar ⟨.second, .second⟩ := by
  decide +kernel

/-- The Me-First probe matches the typology in every cell but 1 > 1, which table 1 bans and the
probe, whose [uSPKR] the indirect object matches, permits. -/
theorem meFirst_typology :
    (∀ s ∈ cliticPairs, s ≠ ⟨.first, .first⟩ →
      (PCCViolation meFirstProbe false s ↔ ¬ IsLicit meFirstGrammar s)) ∧
    ¬ PCCViolation meFirstProbe false ⟨.first, .first⟩ ∧
      ¬ IsLicit meFirstGrammar ⟨.first, .first⟩ := by
  decide +kernel

end Typology

/-- In the Reverse PCC (44)–(45) and its diagnosis (fn. 26), the branching probe over transparent
goals bans the lower [PART] DP whichever object it is, while a dative exposing its person node alone
cannot be banned when it is the lower one, so Slovenian's Strong PCC is the branching probe. -/
theorem reverse_pcc :
    Gluttonous Goal.personSegments branchingProbe [dp .third, dp .second] ∧
    Gluttonous Goal.personSegments branchingProbe [dp .second, dp .first] ∧
    Gluttonous Goal.personSegments branchingProbe [dp .first, dp .second] ∧
    ¬ Gluttonous Goal.personSegments weakProbe [dp .second, dat .first] := by
  decide

/-! ### Against licensing (§2.3) -/

/-- The Person Licensing Condition of [preminger-2011], (9), is the condition of
[bejar-rezac-2003] restricted to clauses with a φ-probing head `F?`. -/
def RevisedPLC (F? : Option BejarRezac2003.Head) (ns : List BejarRezac2003.Nominal) : Prop :=
  ∀ F ∈ F?, BejarRezac2003.PLC (F.derive ns)

instance (F? : Option BejarRezac2003.Head) (ns : List BejarRezac2003.Nominal) :
    Decidable (RevisedPLC F? ns) := by
  unfold RevisedPLC; infer_instance

/-- Basque (10) is the paper's argument against the original condition. The 3DAT > 1ABS cluster is
gluttonous in a finite clause and has no probe to glutton in a nonfinite one, whereas the original
condition leaves the 1st person object unlicensed in both and needs the restriction of (9) to exempt
the probeless clause. -/
theorem nonfinite_obviation :
    PCCViolation weakProbe true ⟨.third, .first⟩ ∧
    ¬ Gluttonous Goal.personSegments [] [dat .third, dp .first] ∧
    ¬ BejarRezac2003.PLC (BejarRezac2003.v.derive ([dat .third, dp .first].map Goal.toNominal)) ∧
    ¬ BejarRezac2003.PLC [(dp .first).toNominal] ∧
    RevisedPLC none [(dp .first).toNominal] := by
  decide

/-! ### Number and clitic doubling (§3.4.3, §4.1.3) -/

/-- The articulated number probe [uNUM [uPL]] of (23) and (55) comes paired with a person probe,
since the probe-specification hierarchy (40) makes a number probe entail a person one. -/
def numberProbe (P : Articulation) : List NumberSegment :=
  if P = [] then [] else [.num, .pl]

/-- Clitic doubling removes the doubled DP from later probing (§3.2), which fixes what the number
probe sees after the person probe. -/
def afterDoubling (P : Articulation) (goals : List Goal) : List Goal :=
  (goals.zipIdx.filter (· ∉ agreed Goal.personSegments P goals)).map (·.1)

/-- There is no Number Case Constraint ((40)–(42)). Over two clitic-doubled objects the person
probe, rooted in [uPERS], doubles the higher one, so the number probe sees one goal. -/
theorem no_number_case_constraint {P : Articulation} (hpi : PersonSegment.pi ∈ P)
    {goals : List Goal} (h : goals.length ≤ 2) :
    ¬ Gluttonous Goal.numberSegments (numberProbe P) (afterDoubling P goals) := by
  apply not_gluttonous_of_length_le_one
  rcases goals with _ | ⟨g, rest⟩
  · simp [afterDoubling]
  · have hg : (g, 0) ∈ agreed Goal.personSegments P (g :: rest) :=
      mem_agreed.2 ⟨List.mem_cons_self, .pi, hpi, by
        simp [segmentAgree, segmentProbe, Probe.search, Probe.relativized, pi_mem_personSegments]⟩
    simp only [afterDoubling, List.zipIdx_cons, List.filter_cons, hg, not_true_eq_false,
      decide_false, Bool.false_eq_true, ↓reduceIte, List.length_map]
    exact (List.length_filter_le _ _).trans (by simpa using h)

/-- With a third accessible DP (43), the number probe sees two goals after doubling and gluttons
over SG > PL. -/
theorem three_goal_number :
    Gluttonous Goal.numberSegments (numberProbe weakProbe)
      (afterDoubling weakProbe [dp .third, dp .third, dpPl .third]) := by
  decide

/-- German copulas double nothing, so the number probe sees both nominatives (67), with gluttony
in SG > PL (64) but not in PL > SG. -/
theorem copula_number :
    Gluttonous Goal.numberSegments (numberProbe weakProbe) [dp .third, dpPl .third] ∧
    ¬ Gluttonous Goal.numberSegments (numberProbe weakProbe) [dpPl .third, dp .third] := by
  decide

/-! ### Gluttony and Vocabulary insertion (§4, §5.2) -/

/-- A Vocabulary item for an agreement head. -/
structure VI (σ : Type*) where
  /-- The geometry the item is specified for; `[]` is the elsewhere item. -/
  spec : List σ
  /-- The form inserted. -/
  exponent : String
  deriving DecidableEq, Repr

section RuleSet

variable {σ : Type*} [DecidableEq σ]

/-- An item applies to a value when its specification is a subset of the value. -/
instance : Rule (VI σ) (List σ) String where
  exponent := VI.exponent
  Applies vi value := vi.spec ⊆ value

instance : DecidableRel (Applies : VI σ → List σ → Prop) := fun vi value ↦
  inferInstanceAs (Decidable (vi.spec ⊆ value))

/-- A value demands the most specific applicable item. -/
abbrev demand (vocab : RuleSet (VI σ)) (value : List σ) : Option (VI σ) :=
  vocab.selectBy (·.spec.length) value

/-- The values a probe carries are resolvable when the items they demand are all the same one
(85); a value that demands no item, as in (88), competes with nothing. -/
def Resolvable (vocab : RuleSet (VI σ)) (vals : List (List σ)) : Prop :=
  (vals.filterMap (demand vocab)).Pairwise (· = ·)

instance (vocab : RuleSet (VI σ)) (vals : List (List σ)) : Decidable (Resolvable vocab vals) :=
  inferInstanceAs (Decidable (List.Pairwise _ _))

/-- The exponent inserted for resolvable values. -/
def realization (vocab : RuleSet (VI σ)) (vals : List (List σ)) : Option String :=
  (vals.filterMap (demand vocab)).head?.map (·.exponent)

end RuleSet

/-- The paper realizes gluttonous probes in these paradigms, each holding the forms it glosses,
the Icelandic past mediopassive (81), *líka* and *þykja* of (76b) and (78), the German present
and past copula ((51), (52), fn. 32), the Hindi-Urdu present and past copula ((68), (69),
fn. 34) and the Brazilian Portuguese copula (70). -/
inductive Paradigm where
  /-- Icelandic past mediopassive, (81). -/
  | icelandicMediopassivePast
  /-- Icelandic *líka* 'like' in the past, (73) and (76b). -/
  | icelandicLikaPast
  /-- Icelandic *þykja* 'think' in the present, (78). -/
  | icelandicThykjaPresent
  /-- German present copula, (51)–(52). -/
  | germanPresent
  /-- German past copula, fn. 32. -/
  | germanPast
  /-- Hindi-Urdu present copula, (68)–(69). -/
  | hindiPresent
  /-- Hindi-Urdu past copula, fn. 34. -/
  | hindiPast
  /-- Brazilian Portuguese present copula, (70). -/
  | portuguesePresent
  deriving DecidableEq, Repr

def spkr : List PersonSegment := [.pi, .participant, .speaker]

def addr : List PersonSegment := [.pi, .participant, .addressee]

/-- The person items of a paradigm in the context of the number probe's value (82), undefined
where the paper glosses no forms. -/
def Paradigm.person (par : Paradigm) (n : numberSystem.values) :
    Option (RuleSet (VI PersonSegment)) :=
  match par with
  | .icelandicMediopassivePast =>
    numberSystem.elim (some [⟨[], "-ist"⟩]) (some [⟨[], "-ust"⟩, ⟨spkr, "-umst"⟩]) (n := n)
  | .icelandicLikaPast => numberSystem.elim (some [⟨[], "líkaði"⟩, ⟨addr, "líkaðir"⟩]) none (n := n)
  | .icelandicThykjaPresent =>
    numberSystem.elim (some [⟨[], "þykir"⟩, ⟨spkr, "þyki"⟩]) (some [⟨[], "þykja"⟩]) (n := n)
  | .germanPresent =>
    numberSystem.elim (some [⟨[], "ist"⟩, ⟨spkr, "bin"⟩, ⟨addr, "bist"⟩]) (some [⟨[], "sind"⟩])
      (n := n)
  | .germanPast => numberSystem.elim (some [⟨[], "war"⟩]) none (n := n)
  | .hindiPresent =>
    numberSystem.elim (some [⟨[], "hai"⟩, ⟨spkr, "hũ:"⟩]) (some [⟨[], "hẼ"⟩]) (n := n)
  | .hindiPast => numberSystem.elim (some [⟨[], "tha:"⟩]) none (n := n)
  | .portuguesePresent => numberSystem.elim (some [⟨[], "é"⟩, ⟨spkr, "sou"⟩]) none (n := n)

/-- The number items of a paradigm, where the paper gives them. -/
def Paradigm.number : Paradigm → RuleSet (VI NumberSegment)
  | .germanPresent => [⟨[.num], "ist"⟩, ⟨[.num, .pl], "sind"⟩]
  | .hindiPresent => [⟨[.num], "hai"⟩, ⟨[.num, .pl], "hẼ"⟩]
  | _ => []

/-- The number context of person insertion is the plural when the number probe's first value is
plural, and the singular otherwise. -/
def numberContext (P : Articulation) (goals : List Goal) : numberSystem.values :=
  if ∃ v ∈ (values Goal.numberSegments (numberProbe P) goals).head?, NumberSegment.pl ∈ v then
    (numberSystem.value .plural)
  else numberSystem.value .singular

/-- After Agree a probe either cliticizes what it agreed with (30) or undergoes Vocabulary insertion
in a paradigm. -/
inductive Aftermath where
  /-- Each agreed-with DP cliticizes onto the probe's host. -/
  | cliticize
  /-- The probe is realized by one item of the paradigm. -/
  | realize (paradigm : Paradigm)
  deriving DecidableEq, Repr

/-- A person probe converges over its goals when a clitic-doubling probe does not glutton, and when
an agreement probe's person and number demands are resolvable in a glossed number context. -/
def Aftermath.Converges : Aftermath → Articulation → List Goal → Prop
  | .cliticize, P, goals => ¬ Gluttonous Goal.personSegments P goals
  | .realize par, P, goals =>
      (∃ vocab ∈ par.person (numberContext P goals),
        Resolvable vocab (values Goal.personSegments P goals)) ∧
        Resolvable par.number (values Goal.numberSegments (numberProbe P) goals)

instance (a : Aftermath) (P : Articulation) (goals : List Goal) :
    Decidable (a.Converges P goals) := by
  cases a <;> simp only [Aftermath.Converges] <;> infer_instance

/-- In Icelandic dative-nominative agreement (76)–(85) in the past mediopassive, a 1st person
plural nominative crashes on *-ust* against *-umst* (83), a 2nd person plural one converges on
*-ust* (85), and in the singular, where every cell is *-ist*, the restriction is lifted. -/
theorem icelandic_syncretism :
    ¬ (Aftermath.realize .icelandicMediopassivePast).Converges weakProbe
        [dat .third, dpPl .first] ∧
    (Aftermath.realize .icelandicMediopassivePast).Converges weakProbe
        [dat .third, dpPl .second] ∧
    ∀ p ∈ PCC.persons,
      (Aftermath.realize .icelandicMediopassivePast).Converges weakProbe [dat .third, dp p] := by
  decide +kernel

/-- Kichean Agent Focus number agreement (88) has one item, realizing plural. -/
def kicheanAgentFocus : RuleSet (VI NumberSegment) := [⟨[.num, .pl], "-e"⟩]

/-- Two 3rd person goals of the given numbers, the cells of (88). -/
def kicheanGoals (s o : numberSystem.values) : List Goal :=
  [⟨.third, s, false⟩, ⟨.third, o, false⟩]

/-- In omnivorous number (§5.2), with no singular item, a number probe gluttonous over SG > PL
converges on the plural item, and the table of (88) follows. -/
theorem kichean_omnivorous :
    Gluttonous Goal.numberSegments (numberProbe weakProbe)
      (kicheanGoals (numberSystem.value .singular) (numberSystem.value .plural)) ∧
    ∀ s o,
      Resolvable kicheanAgentFocus
        (values Goal.numberSegments (numberProbe weakProbe) (kicheanGoals s o)) ∧
      realization kicheanAgentFocus
          (values Goal.numberSegments (numberProbe weakProbe) (kicheanGoals s o)) =
        if s = numberSystem.value .plural ∨ o = numberSystem.value .plural then some "-e"
        else none := by
  decide

/-! ### The paper's examples -/

/-- A configuration the paper assigns an example. -/
structure Config where
  /-- The person probe, empty when the clause has none. -/
  probe : Articulation
  /-- The accessible goals from higher to lower. -/
  goals : List Goal
  /-- What follows Agree. -/
  aftermath : Aftermath
  deriving DecidableEq

/-- The configuration converges. -/
def Config.Converges (c : Config) : Prop := c.aftermath.Converges c.probe c.goals

instance (c : Config) : Decidable c.Converges :=
  inferInstanceAs (Decidable (Aftermath.Converges _ _ _))

def probes : List (String × Articulation) :=
  [("weak", weakProbe), ("branching", branchingProbe), ("none", [])]

def paradigms : List (String × Paradigm) :=
  [("icelandicMediopassivePast", .icelandicMediopassivePast),
    ("icelandicLikaPast", .icelandicLikaPast),
    ("icelandicThykjaPresent", .icelandicThykjaPresent), ("germanPresent", .germanPresent),
    ("germanPast", .germanPast), ("hindiPresent", .hindiPresent), ("hindiPast", .hindiPast),
    ("portuguesePresent", .portuguesePresent)]

/-- The goal a row's `higher` or `lower` features describe, absent when shielded from the
probe. -/
def rowGoal (row : Datum) (k : String) : Option (List Goal) := do
  let p ← row.parse? k [("1", Person.first), ("2", .second), ("3", .third)]
  return if row.feature? (k ++ "Shielded") = some "yes" then []
    else [⟨p,
      if row.feature? (k ++ "Number") = some "pl" then numberSystem.value .plural
      else numberSystem.value .singular,
      decide (row.feature? (k ++ "Opaque") = some "yes")⟩]

/-- The configuration of a row that the paper analyses. -/
def Config.ofRow (row : Datum) : Option Config := do
  let aftermath ← match ← row.feature? "aftermath" with
    | "clitic" => some Aftermath.cliticize
    | "agreement" => (row.parse? "paradigm" paradigms).map .realize
    | _ => none
  return ⟨← row.parse? "probe" probes, (← rowGoal row "higher") ++ (← rowGoal row "lower"),
    aftermath⟩

/-- A row counts as grammatical when the paper judges it acceptable or marginal. Its `?` examples,
(77) and fn. 32, it calls quite acceptable and much improved, while `*?` and `??` carry its star. -/
def Grammatical (row : Datum) : Prop :=
  row.judgment = .acceptable ∨ row.judgment = .marginal

instance : DecidablePred Grammatical := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Every analysed example is grammatical exactly when its configuration converges. -/
theorem analysed_rows : ∀ row ∈ Examples.all, (row.feature? "aftermath").isSome = true →
    ∃ c ∈ Config.ofRow row, (Grammatical row ↔ c.Converges) := by
  decide +kernel

end CoonKeine2021
