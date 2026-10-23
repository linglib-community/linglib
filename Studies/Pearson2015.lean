module

public import Linglib.Semantics.Attitudes.Acquaintance
public import Mathlib.Data.Set.Image

/-!
# Pearson (2015): The Interpretation of the Logophoric Pronoun in Ewe

Pearson gives a semantics for the Ewe logophoric pronoun *yè*. On the view of Heim and von
Stechow, after Chierchia, an attitude verb binds *yè* through the individual abstractor it
introduces, so the pronoun has the attitude holder as antecedent and must be read de se. Her
fieldwork finds it read de se or de re. She keeps the binding and lets *yè* also sit in a covert
constituent with a concept generator, a map from a res to an individual concept. A generator is
suitable when it is reliable, returning the res in the actual world or the holder for one of the
holder's epistemic alternatives, and acquaintance-based, the concept's value at each center being
what the center bears an acquaintance relation to uniquely, the same relation picking out the
holder's own concept when the res is an epistemic alternative.

## Main statements

* `AcquaintanceBased.eqOn_of_mem_epiAlt`: a suitable generator gives an epistemic alternative the
  holder's own concept, as Pearson derives from (82).
* `sayDeRe_of_sayDeSe`: the de se reading is the de re reading through identity, so it entails
  the de re reading when identity is among the holder's acquaintance relations.
* `ClaimDeRe.exists_relatum_eq`: a de re claim about a res other than an epistemic alternative
  needs an acquaintance relation the holder actually bears uniquely to it.
* `ye_de_se_de_re_ambiguous`: when John praises a paper he does not recognize as his own, the de
  se reading is false and the de re reading true.
* `napoleon_contrast`: when John believes himself Napoleon and calls the patient he sees on
  television delusional, *John claims he is delusional* is true and *John claims Napoleon is
  delusional* false.

## Implementation notes

* Concepts are functions from centered worlds, the attitude alternatives of Lewis, to
  individuals, and acquaintance is `Semantics/Attitudes/Acquaintance`: the holder's acquaintance
  relations are a set of relations between individuals and centers, the salient ones.
* The domain of each concept a generator returns is the actual center together with the attitude
  alternatives, as in Pearson's footnote 14.
* Each scenario is a finite model with one attitude alternative, whose center is the holder
  himself; the world-bound individuals of Section 6 are not modelled.
* The contrast between *yè* and PRO, a minimal pronoun that takes no long-distance antecedent, is
  not formalized.

## References

* [pearson-2015]
* [chierchia-1990]
* [percus-sauerland-2003]
* [charlow-sharvit-2014]
* [lewis-1979-attitudes]
* [kratzer-2009]
-/

@[expose] public section

namespace Pearson2015

open Acquaintance

/-! ### Concept generators -/

/-- A centered attitude alternative is a world with the individual the attitude holder identifies as
herself there. -/
abbrev Centered (W E : Type*) := W × E

/-- An individual concept is a function from centered worlds to individuals. -/
abbrev Concept (W E : Type*) := Centered W E → E

/-- A concept generator takes a res to an individual concept. -/
abbrev ConceptGenerator (W E : Type*) := E → Concept W E

/-- A centered property holds of an individual at a world. -/
abbrev CProp (W E : Type*) := E → W → Prop

variable {W E : Type*} {Acq : Set (E → Centered W E → Prop)} {alts : Set (Centered W E)}
  {G : ConceptGenerator W E} {P : CProp W E} {x u res : E} {w : W} {dom : Set E}

/-- The epistemic alternatives of the attitude holder are the centers of her attitude
alternatives. -/
def epiAlt (alts : Set (Centered W E)) : Set E := Prod.snd '' alts

/-- The self concept returns the center of each alternative. -/
def selfConcept : Concept W E := Prod.snd

/-- On the de se denotation of *say* (76), the embedded property holds of the center at each
attitude alternative. -/
def SayDeSe (alts : Set (Centered W E)) (P : CProp W E) : Prop := ∀ p ∈ alts, P p.2 p.1

/-- A generator is reliable for holder `x` in `w` over the res domain `dom` (82)(i) when for each
res `u` its concept returns `u` in the actual world, or `u` is an epistemic alternative of `x` and
the concept returns `x`. -/
def Reliable (alts : Set (Centered W E)) (G : ConceptGenerator W E) (x : E) (w : W)
    (dom : Set E) : Prop :=
  ∀ u ∈ dom, G u (w, x) = u ∨ (u ∈ epiAlt alts ∧ G u (w, x) = x)

/-- A generator is acquaintance-based for `x` in `w` (82)(ii) when for each res `u` one of the
holder's acquaintance relations `Acq` is borne, at the actual center and at every attitude
alternative, uniquely to the value of the concept of `u`, and, if `u` is an epistemic alternative,
uniquely to the value of the concept of `x` as well. -/
def AcquaintanceBased (Acq : Set (E → Centered W E → Prop)) (alts : Set (Centered W E))
    (G : ConceptGenerator W E) (x : E) (w : W) (dom : Set E) : Prop :=
  ∀ u ∈ dom, ∃ R ∈ Acq, ∀ p ∈ insert (w, x) alts,
    relatum R p = some (G u p) ∧ (u ∈ epiAlt alts → relatum R p = some (G x p))

/-- A generator is suitable for `x` in `w` (82) when it is reliable and acquaintance-based. -/
def Suitable (Acq : Set (E → Centered W E → Prop)) (alts : Set (Centered W E))
    (G : ConceptGenerator W E) (x : E) (w : W) (dom : Set E) : Prop :=
  Reliable alts G x w dom ∧ AcquaintanceBased Acq alts G x w dom

/-- On the de re denotation of *say* for a pronoun res (77), (79), some suitable generator, fed the
center as res, picks an individual with the property at each alternative. -/
def SayDeRe (Acq : Set (E → Centered W E → Prop)) (alts : Set (Centered W E)) (P : CProp W E)
    (x : E) (w : W) (dom : Set E) : Prop :=
  ∃ G : ConceptGenerator W E, Suitable Acq alts G x w dom ∧ ∀ p ∈ alts, P (G p.2 p) p.1

/-- On the de re denotation for a name res (81b), the generator is fed the fixed individual `res`
rather than the center. -/
def ClaimDeRe (Acq : Set (E → Centered W E → Prop)) (alts : Set (Centered W E)) (P : CProp W E)
    (res x : E) (w : W) (dom : Set E) : Prop :=
  ∃ G : ConceptGenerator W E, Suitable Acq alts G x w dom ∧ ∀ p ∈ alts, P (G res p) p.1

/-! ### General consequences -/

/-- An acquaintance-based generator gives each epistemic alternative in its domain the holder's own
concept ((82); cf. (83), (84)). -/
theorem AcquaintanceBased.eqOn_of_mem_epiAlt (h : AcquaintanceBased Acq alts G x w dom)
    (hu : u ∈ dom) (he : u ∈ epiAlt alts) : Set.EqOn (G u) (G x) (insert (w, x) alts) := by
  obtain ⟨R, -, hR⟩ := h u hu
  exact fun p hp ↦ Option.some_inj.1 ((hR p hp).1.symm.trans ((hR p hp).2 he))

/-- The de se reading is the de re reading through the self concept, whose relation is identity,
Lewis's relation of acquaintance par excellence. When identity is among the holder's acquaintance
relations and every res in the domain is the holder or one of her epistemic alternatives, the de
se reading entails the de re reading. -/
theorem sayDeRe_of_sayDeSe (hself : (fun y p ↦ y = selfConcept p) ∈ Acq)
    (hdom : ∀ u ∈ dom, u = x ∨ u ∈ epiAlt alts) (h : SayDeSe alts P) :
    SayDeRe Acq alts P x w dom :=
  ⟨fun _ ↦ selfConcept,
    ⟨fun u hu ↦ (hdom u hu).elim (fun e ↦ Or.inl e.symm) (fun e ↦ Or.inr ⟨e, rfl⟩),
      fun _ _ ↦ ⟨_, hself, fun p _ ↦
        ⟨congrFun (relatum_eq _) p, fun _ ↦ congrFun (relatum_eq _) p⟩⟩⟩,
    h⟩

/-- A de re claim about a res in the domain that is not an epistemic alternative of the holder
needs an acquaintance relation she bears uniquely to the res in the actual world, the base
condition of [lewis-1979-attitudes]. -/
theorem ClaimDeRe.exists_relatum_eq (h : ClaimDeRe Acq alts P res x w dom) (hres : res ∈ dom)
    (hne : res ∉ epiAlt alts) : ∃ R ∈ Acq, relatum R (w, x) = some res := by
  obtain ⟨G, ⟨hrel, hacq⟩, -⟩ := h
  obtain ⟨R, hR, hb⟩ := hacq res hres
  have hG : G res (w, x) = res := (hrel res hres).resolve_right fun h ↦ hne h.1
  exact ⟨R, hR, hG ▸ (hb (w, x) (Set.mem_insert _ _)).1⟩

/-! ### Scenario 1: the de se / de re ambiguity (75), §5.3

John has found an old paper he wrote but does not recognize as his own; impressed, he says
"Whoever wrote this is clever". *John be yè le cleva*, 'John said that *yè* was clever', is
judged true, yet John never self-ascribes cleverness. -/

/-- The worlds are the actual world and John's say-alternative. -/
abbrev Wld := Fin 2

/-- The individuals are John and the author John takes to be someone else. -/
abbrev Ind := Fin 2

def actual : Wld := 0
def bel : Wld := 1
def john : Ind := 0
def auth : Ind := 1

/-- John's single say-alternative is the belief world centered on John. -/
def sayAlts : Set (Centered Wld Ind) := {(bel, john)}

/-- In the belief world the author is clever and John is not. -/
def cleverP : CProp Wld Ind := fun y w ↦ w = bel ∧ y = auth

/-- The concept "the author of the paper" returns John in the actual world and the believed author
in John's belief world. -/
def authorConcept : Concept Wld Ind := fun p ↦ if p.1 = actual then john else auth

/-- The generator carrying the author concept for every res. -/
def authorGen : ConceptGenerator Wld Ind := fun _ ↦ authorConcept

/-- John's salient acquaintance relation is reading the paper of its author. -/
def s1Acq : Set (Ind → Centered Wld Ind → Prop) := {fun y p ↦ y = authorConcept p}

theorem deSe_false : ¬ SayDeSe sayAlts cleverP := by
  simp [SayDeSe, sayAlts, cleverP, john, auth]

theorem authorGen_suitable : Suitable s1Acq sayAlts authorGen john actual {john} :=
  ⟨by simp [Reliable, authorGen, authorConcept],
    fun _ _ ↦ ⟨_, rfl, fun p _ ↦
      ⟨congrFun (relatum_eq _) p, fun _ ↦ congrFun (relatum_eq _) p⟩⟩⟩

theorem deRe_true : SayDeRe s1Acq sayAlts cleverP john actual {john} :=
  ⟨authorGen, authorGen_suitable, by
    simp [sayAlts, cleverP, authorGen, authorConcept, actual, bel, auth]⟩

/-- On the de se LF (78) the *yè* sentence is false, and on the de re LF (79) it is true. -/
theorem ye_de_se_de_re_ambiguous :
    ¬ SayDeSe sayAlts cleverP ∧ SayDeRe s1Acq sayAlts cleverP john actual {john} :=
  ⟨deSe_false, deRe_true⟩

/-! ### Scenario 2: the Napoleon contrast (80) to (85), §6

John believes he is Napoleon; watching a report he does not recognize himself and says the
patient he sees is delusional. *John claims he is delusional*, with *yè* read de re, is true;
*John claims Napoleon is delusional* is false, though John believes he is Napoleon: the bound
pronoun ranges over John's epistemic alternatives and is overwritten with John, whom he
identifies through the patient he sees on television, while the name denotes the actual Napoleon,
to whom John bears no acquaintance relation. -/

namespace Napoleon

/-- The worlds are the actual world and John's claim-alternative. -/
abbrev Wld := Fin 2

/-- The individuals are John, the patient John sees on television, and Napoleon. -/
abbrev Ind := Fin 3

def actualN : Wld := 0
def belN : Wld := 1
def john : Ind := 0
def patient : Ind := 1
def napoleon : Ind := 2

/-- John's claim-alternative is the belief world centered on John. -/
def claimAlts : Set (Centered Wld Ind) := {(belN, john)}

/-- In the belief world the patient is delusional. -/
def delusionalP : CProp Wld Ind := fun y w ↦ w = belN ∧ y = patient

/-- The concept "the patient I saw on television" returns John in the actual world and the patient
in John's belief world. -/
def patientConcept : Concept Wld Ind := fun p ↦ if p.1 = actualN then john else patient

/-- The generator carrying the patient concept for every res. -/
def patientGen : ConceptGenerator Wld Ind := fun _ ↦ patientConcept

/-- John's salient acquaintance relation is seeing on television, which in the actual world he
bears to himself. -/
def johnAcq : Set (Ind → Centered Wld Ind → Prop) := {fun y p ↦ y = patientConcept p}

theorem claimsHe_true : SayDeRe johnAcq claimAlts delusionalP john actualN {john} :=
  ⟨patientGen, ⟨by simp [Reliable, patientGen, patientConcept],
    fun _ _ ↦ ⟨_, rfl, fun p _ ↦
      ⟨congrFun (relatum_eq _) p, fun _ ↦ congrFun (relatum_eq _) p⟩⟩⟩,
    by simp [claimAlts, delusionalP, patientGen, patientConcept, actualN, belN, patient]⟩

theorem claimsNapoleon_false :
    ¬ ClaimDeRe johnAcq claimAlts delusionalP napoleon john actualN {napoleon} := by
  intro h
  obtain ⟨R, hR, hb⟩ := h.exists_relatum_eq rfl (by simp [epiAlt, claimAlts, john, napoleon])
  rw [johnAcq, Set.mem_singleton_iff] at hR
  subst hR
  rw [relatum_eq] at hb
  exact absurd (Option.some_inj.1 hb) (by decide)

/-- In the Napoleon contrast the bound-pronoun reading is true and the name reading false. -/
theorem napoleon_contrast :
    SayDeRe johnAcq claimAlts delusionalP john actualN {john} ∧
      ¬ ClaimDeRe johnAcq claimAlts delusionalP napoleon john actualN {napoleon} :=
  ⟨claimsHe_true, claimsNapoleon_false⟩

end Napoleon

end Pearson2015
