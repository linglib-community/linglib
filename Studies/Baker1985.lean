module

public import Linglib.Data.Examples.Baker1985
public import Linglib.Morphology.Word.Tree
public import Linglib.Syntax.Voice.Derivation
public import Linglib.Data.Examples.Readers

/-!
# Baker 1985: the Mirror Principle

[baker-1985]'s Mirror Principle (4): morphological derivations must directly reflect syntactic
derivations. Passive, causative, applicative and reciprocal formation each add an affix to the
verb and rearrange the grammatical functions of its arguments, so the order of the affixes
outward from the root is the order in which the syntactic components applied. Given the
independently known behaviour of each process, this explains why Chamorro's plural agreement
*fan-* registers the surface subject outside the passive marker, the semantic subject inside
the causative marker, and an intermediate subject between the two; why a reciprocal inside a
causative links the root's agent and patient while a causative inside a reciprocal links the
causer to the patient in Quechua but to the agent in Bemba, whose causative makes the old
subject the object; and why an applied argument becomes the passive subject only with the
applied affix inside the passive affix, so that the patient-subject reading is out in
Chi-Mwi:ni and in only in Kinyarwanda, whose passive reaches a second object independently.

Baker argues (§6) that the principle should not be stipulated but follow from an architecture
in which the morphological and the syntactic effect of a process are one thing. A
`Derivation` here is that one thing, a list of processes each with the affix it adds, from
which the word (`word`, a `Word.Tree` of morphs) and the grammatical functions (`outcomes`, a
run of voices moving the participants) are both read. The word determines the sequence of processes
(`word_injective`), and the universal restriction on agreement (27) holds by construction
(`registered_agree_apply`, `registered_apply_agree`).

## Main definitions

* `passiveAt`, `causativeChamorro`, `causativeQuechua`, `applicativeOf`, `reciprocalOf`: the
  GF-rules as the voice of each frame, Baker's schemas with the remaining material carried
  along.
* `Stage`: the substrate's `Voice.Stage` over the paper's participants.
* `Process`, `Grammar`, `outcomes`: the paper's processes, a language's settings, and the stages
  a sequence of processes reaches.
* `Derivation`, `word`: a derivation and the word it builds.
* `derivation`, `processes`, `initialOf`: a row's derivation, read off its segmentation.

## Implementation notes

* A row's derivation is read off its segmentation: the prefixes from the root outward and then
  the suffixes, each a morph bound on its side (§2.1). The Chamorro passive *-in-* is an infix;
  the paper treats it as a prefix in a generalized sense (§3.1, §5) and the rows list it
  before the root, so it is a `Morph.pref` here.
* Baker's passive (12) keeps the demoted subject as an oblique where [creissels-2024]'s
  `Voice.passive` records it as implicit; the two agree on the fate of every core term
  (`passiveAt_fateOfRole`). His applicative (53) promotes an initial oblique where
  `Voice.applicative` introduces the applied participant.

## References

* [baker-1985]
* [gibson-1980] — Chamorro
* [muysken-1981] — Quechua
* [givon-1976] — Bemba
* [comrie-1982], [kisseberth-abasheikh-1977], [kimenyi-1980] — Huichol, Chi-Mwi:ni,
  Kinyarwanda
* [creissels-2024]
-/

@[expose] public section

namespace Baker1985

open Morphology Morphology.Word
open ArgumentFrame (Slot Position)

/-! ### Grammatical-function rules

Each rule is the voice of the frame it applies to, Baker's schema with the "…" material
carried along ([baker-1985] §2.2): the subject is the external argument, the objects are the
nominal complements and the obliques the adpositional ones. -/

/-- A nominal position demoted to an oblique. -/
def demote : Position → Position
  | .nominal => .adpositional
  | p => p

/-- Passive (12) promoting the `j`-th complement, if nominal: it becomes the subject and the old
subject an oblique after the remaining complements. -/
def passiveAt (j : ℕ) (fr : ArgumentFrame) : Option Voice :=
  if fr.complements[j]? = some .nominal then some <|
    .of fr ⟨some .nominal, fr.complements.eraseIdx j ++ [.adpositional]⟩ <|
      some (.complement (fr.complements.length - 1)) ::
        (List.range fr.complements.length).map fun i ↦
          some (if i = j then .external else .complement (if i < j then i else i - 1))
  else none

/-- The Chamorro-type causative (18), (50): a causer is the new subject, the old subject becomes
the object and the old objects become obliques. -/
def causativeChamorro (fr : ArgumentFrame) : Voice :=
  .of fr ⟨some .nominal, .nominal :: fr.complements.map demote⟩ <|
    some (.complement 0) :: (List.range fr.complements.length).map (fun i ↦
      some (.complement (i + 1))) ++ [some .external]

/-- The Quechua-type causative (42): of a transitive, the objects stay and the old subject
becomes an oblique; of an intransitive, the Chamorro type. -/
def causativeQuechua (fr : ArgumentFrame) : Voice :=
  if fr.HasNominal then
    .of fr ⟨some .nominal, fr.complements ++ [.adpositional]⟩ <|
      some (.complement fr.complements.length) ::
        (List.range fr.complements.length).map (some ∘ .complement) ++ [some .external]
  else causativeChamorro fr

/-- The applicative (53) makes the first oblique the object and the old object a second object
after it. -/
def applicativeOf (fr : ArgumentFrame) : Option Voice :=
  (fr.complements.findIdx? fun p ↦ decide p.IsAdpositional).map fun j ↦
    .of fr ⟨some .nominal, .nominal :: fr.complements.eraseIdx j⟩ <|
      some .external :: (List.range fr.complements.length).map fun i ↦
        some (.complement (if i = j then 0 else if i < j then i + 1 else i))

/-- Reflexive-reciprocal formation (44): the object is bound to the subject and becomes the
subject. -/
def reciprocalOf (fr : ArgumentFrame) : Option Voice :=
  (fr.complements.findIdx? fun p ↦ decide p.IsNominal).map fun j ↦
    .of fr ⟨some .nominal, fr.complements.eraseIdx j⟩ <|
      some .external :: (List.range fr.complements.length).map fun i ↦
        some (if i = j then .external else .complement (if i < j then i else i - 1))

/-- Both causative types treat an intransitive alike (§4.1), as [creissels-2024]'s causative. -/
theorem causativeChamorro_intransitive : causativeChamorro .intransitive = Voice.causative := by
  decide

theorem causativeQuechua_intransitive : causativeQuechua .intransitive = Voice.causative := by
  decide

/-- Of a transitive, reflexive-reciprocal formation cumulates the A and the P as
[creissels-2024]'s reflexive and reciprocal do, though it links both to the subject where they
leave the object implicit. -/
theorem reciprocalOf_np_fateOfRole (r : Voice.TermRole) :
    ∀ v ∈ reciprocalOf .np, v.fateOfRole r = Voice.reflexive.fateOfRole r ∧
      v.fateOfRole r = Voice.reciprocal.fateOfRole r := by
  cases r <;> decide

/-- Baker's passive and [creissels-2024]'s agree on the fate of every core term. -/
theorem passiveAt_fateOfRole (r : Voice.TermRole) :
    ∀ v ∈ passiveAt 0 .np, v.fateOfRole r = Voice.passive.fateOfRole r := by
  cases r <;> decide

/-- Baker's applicative is valency-increasing, as [creissels-2024]'s. -/
theorem applicativeOf_isValencyIncreasing :
    ∀ v ∈ applicativeOf .np_pp, v.IsValencyIncreasing := by
  decide

/-! ### Participants and stages -/

/-- The nominals a clause may host are the root's agent and patient, NP1 and NP2 of the paper's
schemas, the oblique an applicative promotes, NP3, and the causer a causative introduces. -/
inductive Arg
  | agent
  | patient
  | applied
  | causer
  deriving DecidableEq, Repr

/-- A derivational stage over the paper's participants. -/
abbrev Stage := Voice.Stage Arg

/-! ### The universal restriction on agreement

Of the four combinations of an agreement morpheme's position relative to a GF-rule morpheme
with the level of grammatical functions it references, (27), only two occur: agreement inside
the GF-rule morpheme references semantic functions and agreement outside it surface functions.
With the morphological and the syntactic effect of a process one thing, the restriction holds
by construction ([baker-1985] §6): agreement attached before a GF-rule registers the subject
before the rule applied, and agreement attached after it the subject after. -/

/-- Agreement inside the GF-rule morpheme registers the semantic subject (27a). -/
theorem registered_agree_apply (s : Stage) (v : Voice) (a : Option Arg) :
    (s.agree.apply v a).registered = s.registered ++ s.subjects :=
  rfl

/-- Agreement outside the GF-rule morpheme registers the surface subject (27d). -/
theorem registered_apply_agree (s : Stage) (v : Voice) (a : Option Arg) :
    (s.apply v a).agree.registered = s.registered ++ (s.apply v a).subjects :=
  rfl

/-! ### Processes and grammars -/

/-- The paper's processes are the GF-rules (§2.2) and number agreement (§3.1). -/
inductive Process
  | passive
  | causative
  | applicative
  | reciprocal
  | agreement
  deriving DecidableEq, Repr

/-- Of the two causative types (§4.1), the Quechua type leaves a transitive root's object in
place and demotes its subject, and the Chamorro type makes the old subject the object. -/
inductive CausativeType
  | quechua
  | chamorro
  deriving DecidableEq, Repr

/-- A language's settings are its causative type and whether its passive can promote the second
of two objects (58). -/
structure Grammar where
  causative : CausativeType
  passiveSecond : Bool := false
  deriving DecidableEq, Repr

/-- The causative voice of a frame under the grammar. -/
def Grammar.causativeOf : Grammar → ArgumentFrame → Voice
  | ⟨.chamorro, _⟩ => causativeChamorro
  | ⟨.quechua, _⟩ => causativeQuechua

/-- The passive voices of a frame under the grammar. -/
def Grammar.passivesOf (g : Grammar) (fr : ArgumentFrame) : List Voice :=
  (passiveAt 0 fr).toList ++ if g.passiveSecond then (passiveAt 1 fr).toList else []

/-- A process derives stages from a stage: the GF-rules apply their voices, the causative
introducing the causer, and number agreement applies to a clause with no object (16). -/
def Process.apply (g : Grammar) : Process → Stage → List Stage
  | .passive, s => (g.passivesOf s.frame).map (s.apply · none)
  | .causative, s => [s.apply (g.causativeOf s.frame) (some .causer)]
  | .applicative, s => (applicativeOf s.frame).toList.map (s.apply · none)
  | .reciprocal, s => (reciprocalOf s.frame).toList.map (s.apply · none)
  | .agreement, s => if s.frame.HasNominal then [] else [s.agree]

/-- The stages a sequence of processes can reach from a stage. -/
def outcomes (g : Grammar) (ps : List Process) (s : Stage) : List Stage :=
  ps.foldl (fun ss p ↦ ss.flatMap (p.apply g)) [s]

/-- The initial stage of a root has the agent as subject, the patient as object if transitive,
and the oblique an applicative will promote. -/
def initial (transitive applied : Bool) : Stage where
  frame := ⟨some .nominal,
    (if transitive then [.nominal] else []) ++ if applied then [.adpositional] else []⟩
  slots := (.agent, .external) :: (if transitive then [(.patient, .complement 0)] else []) ++
    if applied then [(.applied, .complement (if transitive then 1 else 0))] else []

/-- An applied argument becomes subject only with the applicative affix inside the passive (§4.2).
-/
theorem applied_subject_needs_applicative_first (g : Grammar) (transitive applied : Bool) :
    ∀ st ∈ outcomes g [.passive, .applicative] (initial transitive applied),
      .applied ∉ st.subjects := by
  rcases g with ⟨c, ps⟩
  cases c <;> cases ps <;> cases transitive <;> cases applied <;> decide +kernel

/-- With the applied affix inside the passive affix, the applied argument is the subject. -/
theorem applied_subject_of_applicative_first (g : Grammar) :
    ∃ st ∈ outcomes g [.applicative, .passive] (initial true true),
      st.subjects = [.applied] := by
  rcases g with ⟨c, ps⟩
  cases c <;> cases ps <;> decide +kernel

/-! ### Derivations and words -/

/-- A derivation lists the processes with the affix each adds, in order of application; it is the
single object whose two projections are the word and the grammatical functions
([baker-1985] §6). -/
abbrev Derivation := List (Process × Morph)

/-- The word a derivation builds on a root attaches each affix on its side, in order of
application (§2.1). -/
def word (root : Morph) (d : Derivation) : Tree Morph := Tree.attachMorphs root (d.map (·.2))

/-- When each process has its own morph on a fixed side, the word determines the sequence of
processes (§2.1). -/
theorem word_injective (root : Morph) {μ : Process → Morph} (hμ : Function.Injective μ)
    (hside : ∀ p, (μ p).kind.side?.isSome) :
    Function.Injective fun ps : List Process ↦ word root (ps.map fun p ↦ (p, μ p)) := by
  intro ps₁ ps₂ h
  have key (ps : List Process) : ∀ m ∈ ps.map μ, m.kind.side?.isSome := by simp [hside]
  have := Tree.attachMorphs_injOn root (key ps₁) (key ps₂)
    (by simpa only [word, List.map_map, Function.comp_def] using h)
  exact List.map_injective_iff.mpr hμ this

/-! ### The paper's examples -/

/-- The keys of a row's segmentation name the gloss label and the form of each morph. -/
def morphKeys : List (String × String) :=
  [("m1", "f1"), ("m2", "f2"), ("m3", "f3"), ("m4", "f4"), ("m5", "f5"), ("m6", "f6")]

/-- A row's segmentation lists the gloss label and form of each morph in surface order. -/
def segmentation (r : Datum) : List (String × String) :=
  morphKeys.filterMap fun k ↦ (r.feature? k.1).bind fun l ↦ (r.feature? k.2).map (l, ·)

/-- The gloss label of a row's root. -/
def rootLabel (r : Datum) : String := (r.feature? "root").getD ""

/-- The morphs before the root, outermost first. -/
def prefixes (r : Datum) : List (String × String) :=
  (segmentation r).takeWhile (·.1 ≠ rootLabel r)

/-- The morphs after the root, innermost first. -/
def suffixes (r : Datum) : List (String × String) :=
  ((segmentation r).dropWhile (·.1 ≠ rootLabel r)).drop 1

/-- A row's root morph. -/
def rootMorph (r : Datum) : Morph :=
  .root ((((segmentation r).find? (·.1 = rootLabel r)).map (·.2)).getD "")

/-- A row's morphs are its prefixes, root and suffixes in surface order. -/
def morphs (r : Datum) : List Morph :=
  (prefixes r).map (Morph.pref ·.2) ++ rootMorph r :: (suffixes r).map (Morph.suff ·.2)

/-- The process a gloss label marks. -/
def process? : String → Option Process
  | "PASS" => some .passive
  | "CAUS" => some .causative
  | "APPL" | "BEN" | "INSTR" => some .applicative
  | "RECP" | "REFL" => some .reciprocal
  | "PL" => some .agreement
  | _ => none

/-- A row's derivation lists its process-marking affixes in order of application, the prefixes from
the root outward and then the suffixes, each bound on its side. -/
def derivation (r : Datum) : Derivation :=
  ((prefixes r).reverse.filterMap fun m ↦ (process? m.1).map (·, Morph.pref m.2)) ++
    (suffixes r).filterMap fun m ↦ (process? m.1).map (·, Morph.suff m.2)

/-- A row's processes in order of application. -/
def processes (r : Datum) : List Process := (derivation r).map (·.1)

/-- A row's initial stage is transitive as recorded, with an oblique when an applicative
applies. -/
def initialOf (r : Datum) : Stage :=
  initial (r.feature? "valence" = some "transitive") (.applicative ∈ processes r)

/-- In a row's language settings, Chamorro, Bemba, Huichol and Chi-Mwi:ni have the Chamorro
causative and Quechua its own, and Kinyarwanda's passive reaches a second object. -/
def grammar? (r : Datum) : Option Grammar :=
  match r.language with
  | "cham1312" | "bemb1257" | "huic1243" | "chim1312" => some ⟨.chamorro, false⟩
  | "quec1387" => some ⟨.quechua, false⟩
  | "kiny1244" => some ⟨.chamorro, true⟩
  | _ => none

/-- The word a row's derivation builds linearizes to its process-marking morphs around the root
in the row's order. -/
theorem rows_word :
    ∀ r ∈ Examples.all, (word (rootMorph r) (derivation r)).toList.Sublist (morphs r) := by
  decide +kernel

/-- The level of grammatical functions an agreement references is the surface subject, the
semantic subject, or an intermediate one. -/
inductive Level
  | surface
  | semantic
  | intermediate
  deriving DecidableEq, Repr

/-- The subject a row reports its agreement registering. -/
def level? (r : Datum) : Option Level :=
  r.parse? "agreesWith" [("surface subject", .surface), ("semantic subject", .semantic),
    ("intermediate subject", .intermediate)]

/-- The level of a single registration is the surface subject, the semantic subject, or
neither. -/
def level (start final : Stage) : Option Level :=
  match final.registered with
  | [a] => some (if a ∈ final.subjects then .surface
      else if a ∈ start.subjects then .semantic else .intermediate)
  | _ => none

/-- Every Chamorro row's *fan-* registers the subject the paper says it does: the surface
subject outside the passive, the semantic subject inside the causative, and the subject
between passive and causative in their combination. -/
theorem rows_agreement :
    ∀ r ∈ Examples.all, ∀ g ∈ grammar? r, ∀ w ∈ level? r,
      ∀ st ∈ outcomes g (processes r) (initialOf r), level (initialOf r) st = some w := by
  decide +kernel

/-- The dependency a row's translation records. -/
def links? (r : Datum) : Option (Arg × Arg) :=
  r.parse? "links" [("agent-patient", (.agent, .patient)), ("causer-patient", (.causer, .patient)),
    ("causer-agent", (.causer, .agent))]

/-- Reciprocal formation links the root's agent and patient when it applies before the
causative, and the causer to the patient (Quechua) or the agent (Bemba) when after. -/
theorem rows_links :
    ∀ r ∈ Examples.all, ∀ g ∈ grammar? r, ∀ l ∈ links? r,
      ∀ st ∈ outcomes g (processes r) (initialOf r), st.links = [l] := by
  decide +kernel

/-- The surface subject a row reports. -/
def surfaceSubject? (r : Datum) : Option Arg :=
  r.parse? "surfaceSubject" [("applied object", .applied), ("patient", .patient)]

/-- A passive of an applicative is acceptable exactly when some run of the affix order makes
the reported argument the subject: the applied object everywhere, the patient only in
Kinyarwanda. -/
theorem rows_subject :
    ∀ r ∈ Examples.all, ∀ g ∈ grammar? r, ∀ a ∈ surfaceSubject? r,
      (r.judgment = .acceptable ↔
        ∃ st ∈ outcomes g (processes r) (initialOf r), st.subjects = [a]) := by
  decide +kernel

end Baker1985
