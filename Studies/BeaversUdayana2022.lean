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

* `LightVerb.Converges`: the Case and EPP conditions on a clause (§3.2).
* `ber`, `incorporate`, `Reading.resolve`, `MiddleType.denote`: the semantics of the middles.
* `Form`, `Form.EntailsExternalCauser`, `Form.EntailsAgentSubject`, `Form.Passes`: the voice
  forms, what they entail, and the diagnostics they pass.
* `RootClass.middles`: the middles that *ber-* and *ter-* spell for a class of root.

## Main results

* `LightVerb.ber_converges_iff`: *ber-* projects an external argument exactly when the object
  incorporates.
* `Form.entailsExternalCauser_iff`, `Form.entailsAgentSubject_iff`: the forms with an external
  causer and the forms whose subject is the agent.
* `passes_sendirinya_and_not_rationale_iff`: the anticausative alone passes *dengan sendiri=nya*
  and fails the rationale clause.
* `judgments`: a sentence is acceptable exactly when its word passes its diagnostic.
* `denote_anticausative_iff_resolve`: *ter-* is Beavers and Zubair's existential resolution.
* `compat_berParams_iff`: *ber-* is compatible exactly with the thematic Voice heads.

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

/-! ### Argument realization (§3.2) -/

/-- What a light verb puts in its specifier (35). -/
inductive Specifier where
  /-- A DP, as *meN-* does. -/
  | dp
  /-- A DP or nothing, as *ber-* does. -/
  | optional
  /-- The weak implicit argument `e[-D]` of *di-*, which needs no Case. -/
  | weakImplicit
  deriving DecidableEq, Repr

/-- Whether a specifier holds a DP. -/
def Specifier.Allows : Specifier → Bool → Prop
  | .dp, d => d = true
  | .optional, _ => True
  | .weakImplicit, d => d = false

instance : ∀ s d, Decidable (Specifier.Allows s d)
  | .dp, _ | .optional, _ | .weakImplicit, _ => by unfold Specifier.Allows; infer_instance

/-- A voice prefix as a light verb, with its specifier and whether it checks accusative (35). -/
structure LightVerb where
  spec : Specifier
  checksAcc : Bool
  deriving DecidableEq, Repr

namespace LightVerb

/-- The light verb of *meN-*. -/
def meN : LightVerb := ⟨.dp, true⟩

/-- The light verb of *di-*. -/
def di : LightVerb := ⟨.weakImplicit, false⟩

/-- The light verb of *ber-*, and of its allomorph *ter-*. -/
def ber : LightVerb := ⟨.optional, false⟩

end LightVerb

/-- How the object of the base verb is realized, as a DP or as an incorporated NP (33). -/
inductive ObjectRealization where
  | dp
  | incorporated
  deriving DecidableEq, Repr, Fintype

/-- A DP object that the light verb checks no accusative on needs nominative. -/
def ObjectRealization.NeedsNominative (v : LightVerb) (o : ObjectRealization) : Prop :=
  o = .dp ∧ v.checksAcc = false

instance (v : LightVerb) : DecidablePred (ObjectRealization.NeedsNominative v) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- A clause converges when the specifier allows `d`, whether it holds a DP, and exactly one of
that DP and the object needs nominative: every DP needs Case, and T checks nominative on the one
DP that raises to satisfy the EPP. That DP is the subject. -/
def LightVerb.Converges (v : LightVerb) (o : ObjectRealization) (d : Bool) : Prop :=
  v.spec.Allows d ∧ Xor (d = true) (o.NeedsNominative v)

instance (v : LightVerb) (o : ObjectRealization) (d : Bool) : Decidable (v.Converges o d) :=
  inferInstanceAs (Decidable (_ ∧ _))

namespace LightVerb

/-- *meN-* projects its external argument, and its object stays in situ (37a). -/
theorem meN_converges_iff (o : ObjectRealization) (d : Bool) : meN.Converges o d ↔ d = true := by
  cases o <;> cases d <;> decide

/-- *di-* needs a DP object, which raises to subject (37b). -/
theorem di_converges_iff (o : ObjectRealization) (d : Bool) :
    di.Converges o d ↔ o = .dp ∧ d = false := by
  cases o <;> cases d <;> decide

/-- *ber-* projects an external argument exactly when the object incorporates: an incorporated
noun leaves the EPP to a subject DP, and a DP object raises for Case (38). -/
theorem ber_converges_iff (o : ObjectRealization) (d : Bool) :
    ber.Converges o d ↔ (d = true ↔ o = .incorporated) := by
  cases o <;> cases d <;> decide

end LightVerb

/-! ### The middles (§3.3–§3.5)

A dyadic root is a relation `V patient agent`. -/

section Middles

variable {E : Type*}

/-- *ber-* saturates the first open argument of its VP with the free variable `z` (43). -/
def ber {α : Sort*} (z : E) (vp : E → α) : α := vp z

/-- An incorporating verb predicates the noun of its patient and keeps the patient as an
argument (49). -/
def incorporate (V : E → E → Prop) (P : E → Prop) : E → E → Prop := fun x y ↦ V x y ∧ P x

/-- The VP of a middle with subject `s` before *ber-* applies, as a function of its first open
argument. The verb combines first with the trace of a DP object, leaving the agent open, and an
incorporated noun leaves the patient open. -/
def vp (V : E → E → Prop) (P : E → Prop) (s : E) : ObjectRealization → E → Prop
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

/-- Every resolution entails the unspecified one. -/
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

/-- A dispositional middle says that something other than the subject acted on it (55). -/
theorem denote_dispositional : dispositional.denote V P s ↔ ∃ z, z ≠ s ∧ V s z :=
  Reading.resolve_disjoint

/-- An inherent reflexive says that the subject acted on itself (56). -/
theorem denote_reflexive : reflexive.denote V P s ↔ V s s := Reading.resolve_coreferent

/-- An incorporation middle says that the subject acted on something else that the noun
describes (52). -/
theorem denote_incorporation : incorporation.denote V P s ↔ ∃ z, z ≠ s ∧ V z s ∧ P z :=
  Reading.resolve_disjoint

/-- An incorporated reflexive says that the subject acted on itself and that the noun describes
it (53). -/
theorem denote_incorporationReflexive : incorporationReflexive.denote V P s ↔ V s s ∧ P s :=
  Reading.resolve_coreferent

/-- An anticausative says that something, perhaps the subject itself, acted on the subject. -/
theorem denote_anticausative : anticausative.denote V P s ↔ ∃ z, V s z :=
  Reading.resolve_unspecified

/-- As an incorporated noun *diri* 'self' is semantically vacuous. -/
def diri : E → Prop := fun x ↦ ∃ y, y = x

/-- With *diri* incorporated, the reflexive incorporation middle has the truth conditions of an
inherent reflexive. -/
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

/-- Causer suppression is *ber-* under a condition on the sort of the causer. -/
theorem causerSuppress_eq_ber {α : Type} (z : E) (vp : E → α) :
    causerSuppress c h z vp = ber z vp :=
  rfl

/-- An inherent reflexive is the reflexive resolution of a suppressed causer. -/
theorem denote_reflexive_iff_resolve :
    reflexive.denote V P s ↔ BeaversZubair2013.Reading.reflexive.resolve h (flip V) s :=
  denote_reflexive V P s

/-- An anticausative is the existential resolution of a suppressed causer. -/
theorem denote_anticausative_iff_resolve :
    anticausative.denote V P s ↔ BeaversZubair2013.Reading.existential.resolve h (flip V) s :=
  denote_anticausative V P s

/-- A dispositional middle entails the existential resolution of a suppressed causer, to which
it adds that the causer is not the subject. -/
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

/-- The light verb of a form. -/
def lightVerb : Form → LightVerb
  | .meN => .meN
  | .di => .di
  | .middle _ => .ber

/-- The truth conditions of a form with object `o` and subject `s`: *meN-* is the identity
(39a), and *di-* binds an agent other than the subject (39b). -/
def denote {E : Type*} (V : E → E → Prop) (P : E → Prop) (o s : E) : Form → Prop
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
    rcases f with _ | _ | ⟨_ | _, _ | _ | _⟩ <;> simp_all [denote, MiddleType.denote, vp, ber,
      incorporate, dispositional]
  · rintro (rfl | rfl) _ _ _ _ _ h <;> simpa [denote, MiddleType.denote, dispositional, vp, ber]
      using h

/-- The subject is the agent in the active and in the middles that keep the agent in place, with
an incorporated object or the coreferent reading. -/
theorem entailsAgentSubject_iff (f : Form) :
    f.EntailsAgentSubject ↔
      f = .meN ∨ ∃ m, f = .middle m ∧ (m.object = .incorporated ∨ m.reading = .coreferent) := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · -- the model where something other than the subject acts on it
    have := hf Bool (fun x y ↦ x = true ∧ y = false) (fun _ ↦ True) true true
    rcases f with _ | _ | ⟨_ | _, _ | _ | _⟩ <;> simp_all [denote, MiddleType.denote, vp, ber,
      incorporate]
  · rintro (rfl | ⟨⟨_ | _, _ | _ | _⟩, rfl, hm⟩) _ _ _ _ _ h <;>
      simp_all [denote, MiddleType.denote, vp, ber, incorporate] <;> grind

instance : DecidablePred EntailsExternalCauser :=
  fun f ↦ decidable_of_iff _ (entailsExternalCauser_iff f).symm

instance : DecidablePred EntailsAgentSubject :=
  fun f ↦ decidable_of_iff _ (entailsAgentSubject_iff f).symm

end Form

/-- The diagnostics of §2 and §5. -/
inductive Diagnostic where
  /-- An *oleh* 'by' phrase, which realizes the weak implicit argument of the light verb. -/
  | oleh
  /-- A rationale clause, whose null subject an agentive subject or the weak implicit argument
  of the light verb controls; *ber-*'s free variable, in the semantics alone, controls nothing. -/
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
  | .oleh => f.lightVerb.spec = .weakImplicit
  | .rationale => f.EntailsAgentSubject ∨ f.lightVerb.spec = .weakImplicit
  | .sendirinya | .causerDenial => ¬ f.EntailsExternalCauser

instance : ∀ f d, Decidable (Form.Passes f d)
  | _, .oleh | _, .rationale | _, .sendirinya | _, .causerDenial => by
    unfold Form.Passes; infer_instance

/-- The dispositional middle fails every diagnostic (§2.1). -/
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

/-- Every form of the paper's roots in the fragment has a reading. -/
theorem middles_nonempty (c : RootClass) (a : Allomorph) :
    ∀ v ∈ c.roots, (a.form? v).isSome → (c.middles a).Nonempty := by
  cases c <;> cases a <;> decide

end RootClass

/-- An obviative root gets its reflexive reading from incorporated *diri* 'self', as in
*berjual diri* (26b), the marked form that blocks the reading for the plain *ber-* form. -/
theorem jual_incorporatesDiri : Indonesian.jual.IncorporatesDiri := by decide

/-! ### The judgments -/

/-- A word: the active or the passive of a root, or a plain middle of a root of a class in one
of the allomorphs. -/
inductive Word where
  | meN
  | di
  | middle (a : Allomorph) (c : RootClass)
  deriving DecidableEq, Repr

/-- The forms a word denotes, a plain middle each middle its allomorph spells. -/
def Word.forms : Word → Finset Form
  | .meN => {.meN}
  | .di => {.di}
  | .middle a c => (c.middles a).image .middle

/-- A word passes a diagnostic when one of the forms it denotes does. -/
def Word.Passes (w : Word) (d : Diagnostic) : Prop := ∃ f ∈ w.forms, f.Passes d

instance (w : Word) (d : Diagnostic) : Decidable (w.Passes d) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A judgment of the paper on a word in a diagnostic. -/
structure Test where
  datum : Datum
  word : Word
  diagnostic : Diagnostic

open Examples in
/-- The paper's judgments on the diagnostics: *dijual* with *oleh* (11); *berjual* with the
denial of a causer, *dengan sendiri=nya* and a rationale clause (9a), (10c), (13); *berdandan*
with *dengan sendiri=nya* (17b); and *terpecah* and *berpecah* with the denial of a causer (67a),
(74). -/
def tests : List Test :=
  [⟨bu2022_11, .di, .oleh⟩,
   ⟨bu2022_9a, .middle .ber .obviative, .causerDenial⟩,
   ⟨bu2022_10c, .middle .ber .obviative, .sendirinya⟩,
   ⟨bu2022_13, .middle .ber .obviative, .rationale⟩,
   ⟨bu2022_17b, .middle .ber .naturallyReflexive, .sendirinya⟩,
   ⟨bu2022_67a, .middle .ter .causerUnspecified, .causerDenial⟩,
   ⟨bu2022_74, .middle .ber .causerUnspecified, .causerDenial⟩]

/-- A sentence is acceptable exactly when its word passes its diagnostic. -/
theorem judgments : ∀ t ∈ tests, t.datum.judgment = .acceptable ↔ t.word.Passes t.diagnostic := by
  decide

/-! ### A model

Tono sold the car, and Ali dressed himself. -/

/-- The individuals of the model. -/
inductive Entity where
  | tono | ali | car
  deriving DecidableEq, Repr

open Entity in
/-- The selling and dressing events of the model, as one relation of patient and agent. -/
def acted : Entity → Entity → Prop
  | car, tono | ali, ali => True
  | _, _ => False

instance : Fintype Entity := ⟨{.tono, .ali, .car}, fun x ↦ by cases x <;> decide⟩

instance : DecidableRel acted := fun x y ↦ by
  cases x <;> cases y <;> unfold acted <;> infer_instance

/-- The car has a dispositional middle and no reflexive one, Ali a reflexive one and no
dispositional one, and Tono the incorporation middle with a noun true of the car. -/
theorem model :
    dispositional.denote acted diri .car ∧ ¬ reflexive.denote acted diri .car ∧
      reflexive.denote acted diri .ali ∧ ¬ dispositional.denote acted diri .ali ∧
      incorporation.denote acted (· = .car) .tono ∧
      ¬ incorporation.denote acted (· = .car) .ali := by
  simp only [denote_dispositional, denote_reflexive, denote_incorporation]
  decide

/-! ### Relational nouns (§4) -/

/-- A relational noun such as *topi* 'hat' contributes a possession relation `π` of possessor and
possessum and the sort `N` of the possessum. *ber-* suppresses the possessum with disjoint
reference, as in an incorporation middle over the relation of possessum to possessor, so that
*Tono bertopi* says that Tono has some hat on (65). -/
theorem denote_relationalNoun {E : Type*} (π : E → E → Prop) (N : E → Prop) (s : E) :
    incorporation.denote (flip π) N s ↔ ∃ z, z ≠ s ∧ π s z ∧ N z :=
  denote_incorporation _ _ _

/-! ### The voice typology of Alexiadou, Anagnostopoulou and Schäfer (§7.3)

*meN-* corresponds to their thematic active Voice and *di-* to their English passive, which sits
above it. *ber-* entails an agent in every middle but projects it only with an incorporated
object, so its middles realize two of their cells. -/

/-- The cell of a middle: thematic, as *ber-* saturates the agent rather than removing it, and
with a specifier exactly when the object incorporates (`LightVerb.ber_converges_iff`). -/
def MiddleType.params (m : MiddleType) : Params := (decide (m.object = .incorporated), true)

/-- A middle realizes thematic active Voice with an incorporated object and thematic non-active
Voice otherwise. -/
theorem MiddleType.params_eq (m : MiddleType) :
    m.params = if m.object = .incorporated then agentive.params else passive.params := by
  obtain ⟨_ | _, _⟩ := m <;> rfl

/-- *ber-* as one Voice head underspecified for what its middles differ on: the meet of their
cells. -/
def berParams : Params := Finset.univ.inf' ⟨dispositional, Finset.mem_univ _⟩ MiddleType.params

/-- *ber-* is thematic and leaves open whether it projects a specifier. -/
theorem berParams_eq : berParams = (⊥, (true : Flat Bool)) := by decide

/-- *ber-* is compatible with the thematic Voice heads alone. -/
theorem compat_berParams_iff (v : Head) : Compat berParams v.params ↔ v.IsThematic := by
  simp [berParams_eq, Head.params, Head.IsThematic, compat_prod_iff, bot_compat]

end BeaversUdayana2022
