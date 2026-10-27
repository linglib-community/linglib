module

public import Linglib.Fragments.Indonesian.Verbs
public import Linglib.Syntax.Minimalist.Verbal.Voice
public import Studies.BeaversZubair2013
public import Linglib.Data.Examples.BeaversUdayana2022

/-!
# Beavers and Udayana (2022): Middle voice as generalized argument suppression

This file formalizes Beavers and Udayana's analysis of the Indonesian middle prefix *ber-*, which
saturates the first open argument of its VP with a free variable. *ber-* checks no accusative, so
a DP object raises for Case and *ber-* suppresses the agent, while an incorporated noun needs no
Case, a subject DP satisfies the EPP, and *ber-* suppresses the patient. The free variable is read
as the subject, as something other than the subject, or left unspecified, and the anticausative
*ter-* is *ber-* with the variable left unspecified. The diagnostics of §2 and §5 follow from what
each voice form entails and from the weak implicit argument of *di-*.

## Main definitions

* `Converges`: the Case and EPP conditions on a clause whose light verb is a Voice head (§3.2).
* `ber`, `incorporate`, `Reading.resolve`, `MiddleType.denote`: the semantics of the middles.
* `Form`, `Form.EntailsExternalCauser`, `Form.EntailsAgentSubject`, `Form.Passes`: the voice
  forms, what they entail, and the diagnostics they pass.
* `RootClass.middles`: the middles that *ber-* and *ter-* spell for a class of root.

## Main results

* `converges_ber_iff`: *ber-* projects its agent exactly when the object incorporates.
* `Form.entailsExternalCauser_iff`, `Form.entailsAgentSubject_iff`: the forms with an external
  causer and the forms whose subject is the agent.
* `passes_sendirinya_and_not_rationale_iff`: the anticausative alone passes *dengan sendiri=nya*
  and fails the rationale clause.
* `judgments`: a sentence is acceptable exactly when a form its word denotes passes its
  diagnostic.
* `denote_anticausative_iff_resolve`: *ter-* is Beavers and Zubair's existential resolution.
* `compat_berParams_iff`, `berNonActive_params`: *ber-* is compatible exactly with the thematic
  Voice heads, and its non-active head, unlike the passive, has no implicit agent.

## Implementation notes

The event variable is closed off, and the disjointness that (39b) makes a presupposition of *di-*
is part of its truth conditions.

## References

* [beavers-udayana-2022]
* [beavers-zubair-2013]
* [alexiadou-anagnostopoulou-schaefer-2015]
-/

@[expose] public section

namespace BeaversUdayana2022

open Minimalist.Voice (Params Head agentive passive)

/-! ### Argument realization (§3.2)

The voice prefixes are light verbs that license the arguments of the verb. Each is the clause's
only light verb, so a head checks accusative exactly when it `ChecksCase`. -/

/-- How the object of the base verb is realized, as a DP or as an incorporated NP (33). -/
inductive ObjectRealization where
  | dp
  | incorporated
  deriving DecidableEq, Repr, Fintype

/-- *meN-*, which projects its agent and checks accusative (35a). -/
def meN : Head := { agentive with checksCase := true }

/-- *ber-* with its agent projected (38a): thematic active, with no accusative. -/
def berActive : Head := agentive

/-- *ber-* without it (38b): thematic with no specifier, its agent saturated by the free
variable of the semantics rather than implicit. -/
def berNonActive : Head := { thematic := some .agent, hasD := false }

/-- The heads that *ber-* spells out. -/
def berHeads : Finset Head := {berActive, berNonActive}

/-- A clause converges when exactly one DP needs nominative: every DP needs Case, and T checks
nominative on the one that raises to satisfy the EPP. The external argument needs it if the head
projects it, and a DP object if the head checks no accusative. -/
def Converges (v : Head) (o : ObjectRealization) : Prop := Xor v.HasD (o = .dp ∧ ¬ v.ChecksCase)

instance (v : Head) (o : ObjectRealization) : Decidable (Converges v o) :=
  inferInstanceAs (Decidable (Xor _ _))

-- (37a)
theorem converges_meN (o : ObjectRealization) : Converges meN o := by decide +revert

-- (37b)
theorem converges_passive_iff (o : ObjectRealization) : Converges passive o ↔ o = .dp := by
  decide +revert

/-- *ber-* projects its agent iff the object incorporates, since a DP object raises for Case (38).
-/
theorem converges_ber_iff {v : Head} (hv : v ∈ berHeads) (o : ObjectRealization) :
    Converges v o ↔ (v.HasD ↔ o = .incorporated) := by
  simp only [berHeads, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> decide +revert

/-! ### The middles (§3.3–§3.5)

A dyadic root is a relation `V patient agent`. -/

section Middles

variable {E : Type*}

/-- *ber-* saturates the first open argument of its VP with the free variable `z` (43). -/
def ber {α : Sort*} (z : E) (vp : E → α) : α := vp z

@[simp] theorem ber_apply {α : Sort*} (z : E) (vp : E → α) : ber z vp = vp z := rfl

/-- An incorporating verb predicates the noun of its patient and keeps the patient as an
argument (49). -/
def incorporate (V : E → E → Prop) (P : E → Prop) : E → E → Prop := fun x y ↦ V x y ∧ P x

@[simp] theorem incorporate_apply (V : E → E → Prop) (P : E → Prop) (x y : E) :
    incorporate V P x y ↔ V x y ∧ P x :=
  Iff.rfl

/-- The VP of a middle with subject `s` before *ber-* applies, as a function of its first open
argument. The verb combines first with the trace of a DP object, leaving the agent open, and an
incorporated noun leaves the patient open. -/
@[simp] def vp (V : E → E → Prop) (P : E → Prop) (s : E) : ObjectRealization → E → Prop
  | .dp => V s
  | .incorporated => fun x ↦ incorporate V P x s

/-- How the free variable is read: as the subject, as something other than the subject, or left
unspecified, the existential default that lexical and contextual knowledge narrows (§3.3). -/
inductive Reading where
  | coreferent
  | disjoint
  | unspecified
  deriving DecidableEq, Repr, Fintype

namespace Reading

variable (s : E) {φ : E → Prop}

/-- The values a reading leaves the free variable, given the subject `s`. -/
def values : Reading → Set E
  | coreferent => {s}
  | disjoint => {s}ᶜ
  | unspecified => Set.univ

/-- A reading resolves the free variable of `φ` to one of its values. -/
def resolve (r : Reading) (φ : E → Prop) : Prop := ∃ z ∈ r.values s, φ z

variable {s}

@[simp] theorem resolve_coreferent : coreferent.resolve s φ ↔ φ s := by simp [resolve, values]

@[simp] theorem resolve_disjoint : disjoint.resolve s φ ↔ ∃ z, z ≠ s ∧ φ z := by
  simp [resolve, values]

@[simp] theorem resolve_unspecified : unspecified.resolve s φ ↔ ∃ z, φ z := by
  simp [resolve, values]

theorem resolve_unspecified_of_resolve {r : Reading} (h : r.resolve s φ) :
    unspecified.resolve s φ :=
  let ⟨z, _, hz⟩ := h; ⟨z, trivial, hz⟩

end Reading

/-- A middle, by how its object is realized and how its free variable is read. -/
structure MiddleType where
  object : ObjectRealization
  reading : Reading
  deriving DecidableEq, Repr, Fintype

/-- The truth conditions of a middle with subject `s`: *ber-* applied to the VP, with the free
variable resolved by the reading. -/
def MiddleType.denote (m : MiddleType) (V : E → E → Prop) (P : E → Prop) (s : E) : Prop :=
  m.reading.resolve s fun z ↦ ber z (vp V P s m.object)

@[simp] theorem MiddleType.denote_mk (o : ObjectRealization) (r : Reading) (V : E → E → Prop)
    (P : E → Prop) (s : E) : MiddleType.denote ⟨o, r⟩ V P s ↔ r.resolve s (vp V P s o) :=
  Iff.rfl

/-- The head of a middle, the one of `berHeads` that converges with its object
(`converges_ber_iff`). -/
def MiddleType.head (m : MiddleType) : Head :=
  match m.object with
  | .dp => berNonActive
  | .incorporated => berActive

/-- The dispositional or passive middle, as in *Mobil itu berjual dengan mudah* 'The car sells
easily'. -/
def dispositional : MiddleType := ⟨.dp, .disjoint⟩

/-- The inherent reflexive, as in *Ali berdandan* 'Ali dressed'. -/
def reflexive : MiddleType := ⟨.dp, .coreferent⟩

/-- The incorporation middle, as in *Orang itu bercuci mata* 'The man washed his eyes'. -/
def incorporation : MiddleType := ⟨.incorporated, .disjoint⟩

/-- The incorporated reflexive, as in *Orang itu berjual diri* 'The man sold himself'. -/
def incorporationReflexive : MiddleType := ⟨.incorporated, .coreferent⟩

/-- The anticausative, as in *Pintu itu terbuka* 'The door opened', which *ter-* spells (§5). -/
def anticausative : MiddleType := ⟨.dp, .unspecified⟩

variable (V : E → E → Prop) (P : E → Prop) (s : E)

-- (55)
theorem denote_dispositional : dispositional.denote V P s ↔ ∃ z, z ≠ s ∧ V s z :=
  Reading.resolve_disjoint

-- (56)
theorem denote_reflexive : reflexive.denote V P s ↔ V s s := Reading.resolve_coreferent

-- (52)
theorem denote_incorporation : incorporation.denote V P s ↔ ∃ z, z ≠ s ∧ V z s ∧ P z :=
  Reading.resolve_disjoint

-- (53)
theorem denote_incorporationReflexive : incorporationReflexive.denote V P s ↔ V s s ∧ P s :=
  Reading.resolve_coreferent

theorem denote_anticausative : anticausative.denote V P s ↔ ∃ z, V s z :=
  Reading.resolve_unspecified

/-- As an incorporated noun *diri* 'self' is semantically vacuous. -/
def diri : E → Prop := fun x ↦ ∃ y, y = x

theorem denote_incorporationReflexive_iff_reflexive :
    incorporationReflexive.denote V diri s ↔ reflexive.denote V P s := by
  simp [denote_incorporationReflexive, denote_reflexive, diri]

end Middles

/-! ### Causer suppression (§3.3)

*ber-* generalizes the causer suppression of Beavers and Zubair, which applies to a causer of the
individual sort alone. Their verbs take the causer first. (42b) restates their existential
resolution with a disjointness conjunct that their own (78b) lacks: theirs is the unspecified
reading. -/

section CauserSuppression

open BeaversZubair2013 (CauserSort causerSuppress)

variable {E : Type} {c : CauserSort} (h : CauserSort.individual ≤ c) (V : E → E → Prop)
  (P : E → Prop) (s : E)

theorem causerSuppress_eq_ber {α : Type} (z : E) (vp : E → α) :
    causerSuppress c h z vp = ber z vp :=
  rfl

theorem denote_reflexive_iff_resolve :
    reflexive.denote V P s ↔ BeaversZubair2013.Reading.reflexive.resolve h (flip V) s :=
  denote_reflexive V P s

/-- An anticausative is the existential resolution of a suppressed causer. -/
theorem denote_anticausative_iff_resolve :
    anticausative.denote V P s ↔ BeaversZubair2013.Reading.existential.resolve h (flip V) s :=
  denote_anticausative V P s

theorem resolve_existential_of_dispositional (hs : dispositional.denote V P s) :
    BeaversZubair2013.Reading.existential.resolve h (flip V) s :=
  (denote_anticausative_iff_resolve h V P s).1 (Reading.resolve_unspecified_of_resolve hs)

end CauserSuppression

/-! ### The diagnostics (§2, §5) -/

/-- A voice form of a dyadic root: the active in *meN-*, the passive in *di-*, or a middle. -/
inductive Form where
  | meN
  | di
  | middle (m : MiddleType)
  deriving DecidableEq, Repr, Fintype

namespace Form

/-- The head of a form: *di-* is `passive`, with no specifier and an implicit agent (35c). -/
def head : Form → Head
  | .meN => BeaversUdayana2022.meN
  | .di => passive
  | .middle m => m.head

/-- The truth conditions of a form with object `o` and subject `s`: *meN-* is the identity
(39a), and *di-* binds an agent other than the subject (39b). -/
@[simp] def denote {E : Type*} (V : E → E → Prop) (P : E → Prop) (o s : E) : Form → Prop
  | .meN => V o s
  | .di => ∃ y, y ≠ s ∧ V s y
  | .middle m => m.denote V P s

/-- A form entails that something other than its subject acted on the subject. -/
def EntailsExternalCauser (f : Form) : Prop :=
  ∀ (E : Type) (V : E → E → Prop) (P : E → Prop) (o s : E),
    f.denote V P o s → ∃ z, z ≠ s ∧ V s z

/-- A form entails that its subject is the agent. -/
def EntailsAgentSubject (f : Form) : Prop :=
  ∀ (E : Type) (V : E → E → Prop) (P : E → Prop) (o s : E), f.denote V P o s → ∃ x, V x s

/-- The passive and the dispositional middle alone entail an external causer. -/
theorem entailsExternalCauser_iff (f : Form) :
    f.EntailsExternalCauser ↔ f = .di ∨ f = .middle dispositional := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · -- the model where the subject alone acts
    have := hf Bool (fun _ y ↦ y = true) (fun _ ↦ True) true true
    rcases f with _ | _ | ⟨_ | _, _ | _ | _⟩ <;> simp_all [dispositional]
  · rintro (rfl | rfl) _ _ _ _ _ h <;> simpa [dispositional] using h

/-- The subject is the agent in the active and in the middles that keep the agent in place, with
an incorporated object or the coreferent reading. -/
theorem entailsAgentSubject_iff (f : Form) :
    f.EntailsAgentSubject ↔
      f = .meN ∨ ∃ m, f = .middle m ∧ (m.object = .incorporated ∨ m.reading = .coreferent) := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · -- the model where something other than the subject acts on it
    have := hf Bool (fun x y ↦ x = true ∧ y = false) (fun _ ↦ True) true true
    rcases f with _ | _ | ⟨_ | _, _ | _ | _⟩ <;> simp_all
  · rintro (rfl | ⟨⟨_ | _, _ | _ | _⟩, rfl, hm⟩) _ _ _ _ _ h <;> simp_all <;> grind

instance : DecidablePred EntailsExternalCauser :=
  fun f ↦ decidable_of_iff _ (entailsExternalCauser_iff f).symm

instance : DecidablePred EntailsAgentSubject :=
  fun f ↦ decidable_of_iff _ (entailsAgentSubject_iff f).symm

end Form

/-- The diagnostics of §2 and §5. -/
inductive Diagnostic where
  /-- An *oleh* 'by' phrase, which realizes the weak implicit argument of the head. -/
  | oleh
  /-- A rationale clause, whose null subject an agentive subject or the weak implicit argument
  of the head controls; *ber-*'s free variable, in the semantics alone, controls nothing. -/
  | rationale
  /-- *dengan sendiri=nya* 'by itself', which says that nothing acted on the subject before it
  did. -/
  | sendirinya
  /-- The denial that anyone else acted on the subject. -/
  | causerDenial
  deriving DecidableEq, Repr

/-- A form passes a diagnostic. *dengan sendiri=nya* and the denial of a causer both contradict
an entailed external causer. -/
def Form.Passes (f : Form) : Diagnostic → Prop
  | .oleh => f.head.ExternalImplicit
  | .rationale => f.EntailsAgentSubject ∨ f.head.ExternalImplicit
  | .sendirinya | .causerDenial => ¬ f.EntailsExternalCauser

instance : ∀ f d, Decidable (Form.Passes f d)
  | _, .oleh | _, .rationale | _, .sendirinya | _, .causerDenial => by
    unfold Form.Passes; infer_instance

-- §2.1
theorem not_passes_dispositional (d : Diagnostic) : ¬ (Form.middle dispositional).Passes d := by
  cases d <;> decide

/-- The anticausative alone passes *dengan sendiri=nya* and fails the rationale clause (67). -/
theorem passes_sendirinya_and_not_rationale_iff (f : Form) :
    f.Passes .sendirinya ∧ ¬ f.Passes .rationale ↔ f = .middle anticausative := by
  rcases f with _ | _ | ⟨_ | _, _ | _ | _⟩ <;> decide

/-! ### Root classes (§3.5, §5) -/

/-- The classes of dyadic root. -/
inductive RootClass where
  /-- The conventional expectation is self-action, as with verbs of body care. -/
  | naturallyReflexive
  /-- The conventional expectation is disjoint reference, as with every other dyadic root. -/
  | obviative
  /-- A change of state whose root entails no external causer. -/
  | causerUnspecified
  deriving DecidableEq, Repr

/-- The two allomorphs of the middle prefix (§5). -/
inductive Allomorph where
  | ber
  | ter
  deriving DecidableEq, Repr

/-- The form of a root in an allomorph, if it has one. -/
def Allomorph.form? : Allomorph → Indonesian.Verb → Option (List Phonology.Segment)
  | .ber, v => v.ber?
  | .ter, v => v.ter?

namespace RootClass

/-- The paper's roots of each class: the body-care verbs of (15) and *cuci* 'wash' (56), the
other roots of (4), and *buka* 'open' and *pecah* 'break' of §5. -/
def roots : RootClass → List Indonesian.Verb
  | .naturallyReflexive =>
    [Indonesian.dandan, Indonesian.cukur, Indonesian.jemur, Indonesian.sisir, Indonesian.cuci]
  | .obviative => [Indonesian.masak, Indonesian.jual, Indonesian.tambat]
  | .causerUnspecified => [Indonesian.buka, Indonesian.pecah]

/-- The plain middles that an allomorph spells for a root of the class. A naturally reflexive
root expects self-action and allows the disjoint reading in context (57). An obviative root
expects disjoint reference, its reflexive blocked by the marked *ber-V=diri*. A causer-unspecified
root leaves the variable open, and *ter-* spells its middle unless the reading is disjoint (74). -/
def middles : RootClass → Allomorph → Finset MiddleType
  | .naturallyReflexive, .ber => {reflexive, dispositional}
  | .obviative, .ber | .causerUnspecified, .ber => {dispositional}
  | .causerUnspecified, .ter => {reflexive, anticausative}
  | .naturallyReflexive, .ter | .obviative, .ter => ∅

/-- The forms that a plain middle of a root of the class denotes in an allomorph. -/
def forms (c : RootClass) (a : Allomorph) : Finset Form := (c.middles a).image .middle

theorem middles_nonempty (c : RootClass) (a : Allomorph) :
    ∀ v ∈ c.roots, (a.form? v).isSome → (c.middles a).Nonempty := by
  cases c <;> cases a <;> decide

end RootClass

/-! ### The judgments -/

/-- A judgment of the paper on a word in a diagnostic, with the forms the word denotes. -/
structure Test where
  datum : Datum
  forms : Finset Form
  diagnostic : Diagnostic

open Examples RootClass in
/-- The paper's judgments on the diagnostics: *dijual* with *oleh* (11); *berjual* with the
denial of a causer, *dengan sendiri=nya* and a rationale clause (9a), (10c), (13); *berdandan*
with *dengan sendiri=nya* (17b); and *terpecah* and *berpecah* with the denial of a causer (67a),
(74). -/
def tests : List Test :=
  [⟨bu2022_11, {.di}, .oleh⟩,
   ⟨bu2022_9a, obviative.forms .ber, .causerDenial⟩,
   ⟨bu2022_10c, obviative.forms .ber, .sendirinya⟩,
   ⟨bu2022_13, obviative.forms .ber, .rationale⟩,
   ⟨bu2022_17b, naturallyReflexive.forms .ber, .sendirinya⟩,
   ⟨bu2022_67a, causerUnspecified.forms .ter, .causerDenial⟩,
   ⟨bu2022_74, causerUnspecified.forms .ber, .causerDenial⟩]

/-- A sentence is acceptable exactly when one of the forms its word denotes passes its
diagnostic. -/
theorem judgments :
    ∀ t ∈ tests, t.datum.judgment = .acceptable ↔ ∃ f ∈ t.forms, f.Passes t.diagnostic := by
  decide

/-! ### A model

Tono sold the car, and Ali dressed himself. -/

/-- The individuals of the model. -/
inductive Entity where
  | tono | ali | car
  deriving DecidableEq, Repr, Fintype

open Entity in
/-- The selling and dressing events of the model, as one relation of patient and agent. -/
def acted : Entity → Entity → Prop
  | car, tono | ali, ali => True
  | _, _ => False

instance : DecidableRel acted := fun x y ↦ by
  cases x <;> cases y <;> unfold acted <;> infer_instance

theorem model :
    dispositional.denote acted diri .car ∧ ¬ reflexive.denote acted diri .car ∧
      reflexive.denote acted diri .ali ∧ ¬ dispositional.denote acted diri .ali ∧
      incorporation.denote acted (· = .car) .tono ∧
      ¬ incorporation.denote acted (· = .car) .ali := by
  simp only [denote_dispositional, denote_reflexive, denote_incorporation]
  decide

/-! ### Relational nouns (§4) -/

-- (65)
theorem denote_relationalNoun {E : Type*} (π : E → E → Prop) (N : E → Prop) (s : E) :
    incorporation.denote (flip π) N s ↔ ∃ z, z ≠ s ∧ π s z ∧ N z :=
  denote_incorporation _ _ _

/-! ### The voice typology of Alexiadou, Anagnostopoulou and Schäfer (§7.3)

Beavers and Udayana align *meN-* with thematic active Voice and *di-* with the English passive.
The heads of *ber-* realize thematic active and thematic non-active Voice. -/

/-- *ber-* as one Voice head underspecified for what its heads differ on: the meet of their
cells. -/
def berParams : Params := berHeads.inf' ⟨berActive, by simp [berHeads]⟩ Head.params

theorem berParams_eq : berParams = (⊥, (true : Flat Bool)) := by decide

/-- *ber-* is compatible with the thematic Voice heads alone. -/
theorem compat_berParams_iff (v : Head) : Compat berParams v.params ↔ v.IsThematic := by
  simp [berParams_eq, Head.params, Head.IsThematic, compat_prod_iff, bot_compat]

/-- The non-active head of *ber-* has the passive's parameters but, unlike the passive, no implicit
agent (§2.1). -/
theorem berNonActive_params :
    berNonActive.params = passive.params ∧ ¬ berNonActive.ExternalImplicit ∧
      ¬ berNonActive.DCoherent ∧ passive.ExternalImplicit ∧ passive.DCoherent := by
  decide

end BeaversUdayana2022
