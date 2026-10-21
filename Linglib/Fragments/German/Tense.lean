module

public import Linglib.Fragments.German.Verbs
public import Linglib.Syntax.Category.Verb.Tense
public import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
public import Linglib.Semantics.ArgumentStructure.Unaccusativity
public import Linglib.Pragmatics.SocialMeaning.Register

/-!
# German tense forms

This file describes the tense forms of German, following Durrell's reference grammar. German has
six tenses. Two are simple, the present *kauft* and the past *kaufte*, and four are compound.
The perfect *hat gekauft* and the pluperfect *hatte gekauft* put the past participle under the
present and the past of *haben* or *sein*, and the future *wird kaufen* and the future perfect
*wird gekauft haben* put an infinitive under the present of *werden*. German has no progressive
forms. A verb forms its perfect with *sein* when it is an intransitive verb of motion or of
change of state, and with *haben* otherwise; the auxiliaries *sein* and *haben* each form their
own perfect with themselves.

The past and the perfect overlap in meaning, and the choice between them is largely one of
register: narration is in the past in written German and in the perfect in speech. In South
Germany, Austria and Switzerland the past is practically never used in everyday speech. Colloquial
speech, in the South and now more widely, forms the pluperfect with the perfect of the auxiliary,
the double perfect *hat gesehen gehabt*, and sometimes with its pluperfect, *hatte gesehen
gehabt*; these complex pluperfects are not accepted as standard.

## Main declarations

* `German.PrincipalParts`: the infinitive, third person singular present and past, and past
  participle of a verb, with its perfect auxiliary.
* `German.haben`, `German.sein`, `German.werden`: the tense auxiliaries.
* `German.perfectAuxiliary`: the auxiliary of the perfect of a verb on a frame, by the rule of
  §12.3.2.
* `German.TenseVerb`: a lexical verb, a perfect auxiliary, the auxiliary of a complex pluperfect,
  or the future auxiliary *werden*.
* `German.periphrasis`, `German.PrincipalParts.tenseForm`: the means by which German builds its
  tense forms, and the words of a tense form of a verb, finite verb first.
* `German.tenseForms`, `German.complexPluperfects`, `German.southernTenseForms`: the forms of the
  standard language, the colloquial complex pluperfects, and the forms of southern speech;
  `German.PrincipalParts.tenseForm_isSome_iff` shows that the first two are exactly the forms
  that German realizes.
* `German.register`: the register of a form as a narrative tense.

## Implementation notes

`PrincipalParts.tenseForm` gives the third person singular, the finite verb first and the
nonfinite verbs in their clause-final order, the lexical verb before the auxiliaries it stands
under. Every verb has all its nonfinite forms; which of them a tense form uses is a matter of
government, so German lacks a progressive although its verbs have present participles. The
auxiliary of a complex pluperfect is a role of its own, `TenseVerb.doublePerfect`, which nothing
governs, so that the perfect doubles once and no more.

The perfect auxiliary follows from the meaning of the verb on a frame, as Durrell's rule has it,
not from the verb alone: an accusative object, a path of motion, the continuation of a
state and a change the subject undergoes are what the rule reads. So *rennen* 'run' takes *sein*
as a verb of motion although it is not unaccusative, *tanzen* 'dance' takes *sein* only with a
directional phrase (`German.perfect_withPath_intransitive`), and impersonal *frieren*, *es hat
gefroren* 'there was a frost', takes *haben*, its subject an expletive that undergoes nothing. A
change of state is read off the entry's aspect, telic or along a scale. The compounds of *gehen*
and *werden* that take *sein* with an accusative object (*die Strecke abgegangen*) are exceptions
the rule does not cover.

## References

* [durrell-2011]
-/

@[expose] public section

namespace German

open _root_.Verb (PerfectAuxiliary)

/-- The principal parts of a verb are its stem, the infinitive, the third person singular present
and past and the past participle, with the auxiliary of its perfect. -/
structure PrincipalParts extends Conjugation.Stem where
  /-- The auxiliary of the perfect. -/
  perfectAuxiliary : PerfectAuxiliary
  deriving DecidableEq, Repr

/-- The auxiliary *haben* forms the perfect of most verbs, and its own. -/
def haben : PrincipalParts := ⟨Conjugation.strong "haben" "hat" "hatte" "gehabt", .have⟩

/-- The auxiliary *sein* forms the perfect of intransitive verbs of motion and change of state,
and its own. Its present participle is *seiend*. -/
def sein : PrincipalParts :=
  ⟨{ Conjugation.strong "sein" "ist" "war" "gewesen" with presentParticiple := "seiend" }, .be⟩

/-- The auxiliary *werden* forms the future with the infinitive. -/
def werden : PrincipalParts := ⟨Conjugation.strong "werden" "wird" "wurde" "geworden", .be⟩

/-- The verb of a perfect auxiliary. -/
def perfectVerb : PerfectAuxiliary → PrincipalParts
  | .be => sein
  | .have => haben

/-- The auxiliary of the perfect of `v` on the frame `fr` ([durrell-2011] §12.3.2): *haben* on a
frame with an accusative object (b.i); *sein* for a verb of motion and for the continuation of a
state, *bleiben* (a.i, a.iv), and for an intransitive verb whose subject undergoes a change of
state or to which something happens, to an endpoint or along a scale (a.ii, a.iii); and *haben*
otherwise (b.iii–v). -/
def perfectAuxiliary (v : Verb) (fr : ArgumentFrame) : PerfectAuxiliary :=
  if fr.HasNominal ∧ .acc ∈ v.objects then .have
  else if v.direction.isSome ∨ v.phasal = some .continuation ∨ fr.argumentRole .external = some .S ∧
      (v.vendlerClass.any (·.telicity == .telic) ∨ v.scaleDimension.isSome) then .be
  else .have

/-- A directional phrase gives an intransitive verb *sein*: the verbs of motion that name the
activity as such, *tanzen* 'dance' and *segeln* 'sail', take *sein* when they express movement
from one place to another (§12.3.2c). -/
theorem perfect_withPath_intransitive (v : Verb) {p : Adposition.SpatialReading}
    (hv : v.TakesSpatial) (hp : p.direction ≠ .place) :
    perfectAuxiliary (v.withPath p) .intransitive = .be := by
  simp [perfectAuxiliary, _root_.Verb.direction_withPath hv hp, ArgumentFrame.intransitive,
    ArgumentFrame.HasNominal]

/-- The verbs of manner of motion select a directional phrase: every entry that displaces its
subject with no direction takes a spatial complement (§12.3.2c). -/
theorem takesSpatial_of_direction_eq_place :
    ∀ v ∈ Verbs.allVerbs, v.direction = some .place → v.TakesSpatial := by
  decide

/-- The principal parts of a verb entry on a frame, its basic frame by default, are its stem
with the auxiliary of its perfect there. -/
def Verb.principalParts (v : Verb) (fr : ArgumentFrame := v.valency.frames.headD .intransitive) :
    PrincipalParts :=
  ⟨v.stem, perfectAuxiliary v fr⟩

/-- A verb in a tense form is a lexical verb, a perfect auxiliary, the auxiliary of the perfect of
a perfect auxiliary in a complex pluperfect, or the future auxiliary *werden*. -/
inductive TenseVerb where
  | lexical (v : PrincipalParts)
  | perfect (a : PerfectAuxiliary)
  | doublePerfect (a : PerfectAuxiliary)
  | future

/-- The verb whose forms a verb in a tense form takes: a perfect auxiliary and the auxiliary of its
perfect are the same verb, *haben* or *sein*, and the future auxiliary is *werden*. -/
def TenseVerb.verb : TenseVerb → PrincipalParts
  | .lexical v => v
  | .perfect a | .doublePerfect a => perfectVerb a
  | .future => werden

/-- German builds its tense forms with the past participle under the verb's perfect auxiliary and
the infinitive under the present of *werden* (§12.3.1, §14.4). A perfect auxiliary stands in the
infinitive under *werden* in the future perfect and, in colloquial speech, in the past participle
under its own perfect auxiliary in a complex pluperfect (§14.5.3). Every verb has all its
nonfinite forms, but nothing governs the auxiliary of a complex pluperfect, *werden* or a present
participle, so German has no progressive (§14.1.3). -/
def periphrasis : Tense.Periphrasis TenseVerb where
  finite
    | .future, .past => none
    | u, .present => some u.verb.present
    | u, .past => some u.verb.past
    | _, .future => none
  nonfinite u
    | .infinitive => some u.verb.infinitive
    | .pastParticiple => some u.verb.pastParticiple
    | .presentParticiple => some u.verb.presentParticiple
  auxiliary
    | .lexical v, .pastParticiple => some (.perfect v.perfectAuxiliary)
    | .lexical _, .infinitive | .perfect _, .infinitive => some .future
    | .perfect a, .pastParticiple => some (.doublePerfect a)
    | _, _ => none

/-- The chains German builds over a lexical verb are the empty one, the perfect, the future, the
future of the perfect and the perfect of the perfect, and each leaves the lexical verb, its
perfect auxiliary, *werden*, *werden* and the auxiliary of a complex pluperfect to be
inflected. -/
theorem chain_eq_some {v : PrincipalParts} :
    ∀ {ns : List Tense.Form.Nonfinite} {ws : List String} {u : TenseVerb},
      periphrasis.chain (.lexical v) ns = some (ws, u) →
        ns = [] ∧ u = .lexical v ∨ ns = [.pastParticiple] ∧ u = .perfect v.perfectAuxiliary ∨
          ns = [.infinitive] ∧ u = .future ∨ ns = [.infinitive, .pastParticiple] ∧ u = .future ∨
          ns = [.pastParticiple, .pastParticiple] ∧ u = .doublePerfect v.perfectAuxiliary
  | [], ws, u, h => by
    obtain ⟨-, rfl⟩ : [] = ws ∧ TenseVerb.lexical v = u := by
      simpa [Tense.Periphrasis.chain] using h
    exact .inl ⟨rfl, rfl⟩
  | n :: ns, ws, u, h => by
    unfold Tense.Periphrasis.chain at h
    split at h
    · exact absurd h (by simp)
    · next ws' u' h' =>
      rcases chain_eq_some h' with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        cases n <;> simp_all [periphrasis]

/-- `v.tenseForm f` gives the words of the tense form `f` of `v` in the third person singular, the
finite verb first and then the nonfinite verbs in their clause-final order, the lexical verb
before the auxiliaries it stands under. -/
def PrincipalParts.tenseForm (v : PrincipalParts) (f : Tense.Form) : Option (List String) :=
  (periphrasis.realize (.lexical v) f).map fun x ↦ x.1 :: x.2

/-- A realized tense form has one word for its finite verb and one for each nonfinite form. -/
theorem PrincipalParts.length_of_mem_tenseForm {v : PrincipalParts} {f : Tense.Form}
    {ws : List String} (h : ws ∈ v.tenseForm f) : ws.length = f.nonfinite.length + 1 := by
  obtain ⟨x, hx, rfl⟩ := Option.mem_map.1 h
  simp [periphrasis.length_of_mem_realize hx]

/-- Standard German has the present, the past, the perfect, the pluperfect, the future and the
future perfect. -/
def tenseForms : List Tense.Form :=
  [.simplePresent, .simplePast, .presentPerfect, .pastPerfect, .future, .futurePerfect]

/-- Colloquial speech has the complex pluperfects, the double perfect and the pluperfect of the
auxiliary over the past participle (§14.5.3). -/
def complexPluperfects : List Tense.Form := [.doublePerfect, Tense.Form.pastPerfect.perfect]

/-- Southern speech lacks the past, and with it the standard pluperfect, and has the double
perfect. -/
def southernTenseForms : List Tense.Form :=
  [.simplePresent, .presentPerfect, .doublePerfect, .future, .futurePerfect]

/-- The standard tense forms and the complex pluperfects are exactly the forms that German
realizes. -/
theorem PrincipalParts.tenseForm_isSome_iff (v : PrincipalParts) (f : Tense.Form) :
    (v.tenseForm f).isSome ↔ f ∈ tenseForms ∨ f ∈ complexPluperfects := by
  constructor
  · obtain ⟨t, ns⟩ := f
    intro h
    simp only [PrincipalParts.tenseForm, Option.isSome_map, Tense.Periphrasis.realize] at h
    split at h
    · exact absurd h (by simp)
    · next ws u h' =>
      rcases chain_eq_some h' with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        cases t <;> first | decide | exact absurd h (by simp [periphrasis])
  · simp only [tenseForms, complexPluperfects, List.mem_cons, List.not_mem_nil, or_false]
    rintro ((rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) <;> rfl

/-- Every form of southern speech is a standard form or a complex pluperfect, and so is
realized. -/
theorem southernTenseForms_subset : southernTenseForms ⊆ tenseForms ++ complexPluperfects := by
  decide

/-- As a narrative tense the past belongs to written German and the complex pluperfects to
colloquial speech, and the other forms are unmarked. -/
def register (f : Tense.Form) : SocialMeaning.Register :=
  if f = .simplePast then .formal else if f ∈ complexPluperfects then .informal else .neutral

open Verbs in
/-- The rule gives every entry on its basic frame an auxiliary its perfect takes: *sein* for the
verbs of motion *rennen*, *laufen* and *ankommen*, for *frieren* as a change of state and for
*bleiben*, and *haben* for *arbeiten* and *tanzen*, which denote an activity as such, and for the
state *liegen*. -/
theorem perfectAuxiliary_mem : ∀ v ∈ allVerbs, v.perfectAuxiliaries.Nonempty →
    perfectAuxiliary v (v.valency.frames.headD .intransitive) ∈ v.perfectAuxiliaries := by
  decide

open Verbs in
/-- *Frieren* takes *haben* impersonally, *es hat gefroren*, and *tanzen* takes *sein* with a
directional phrase, which it selects, while *arbeiten*, which selects none, keeps *haben*
(§12.3.2). -/
example :
    perfectAuxiliary frieren .impersonal = .have ∧
    perfectAuxiliary (tanzen.withPath Adposition.into) .intransitive = .be ∧
    perfectAuxiliary (arbeiten.withPath Adposition.into) .intransitive = .have := by
  decide

open Verbs in
/-- *zerbrechen* 'break', a transitive verb, forms its perfect with *haben*, and the unaccusative
*frieren* 'freeze' and *rennen* 'run', a verb of motion, with *sein*. -/
example :
    zerbrechen.principalParts.tenseForm .presentPerfect = some ["hat", "zerbrochen"] ∧
      zerbrechen.principalParts.tenseForm .doublePerfect = some ["hat", "zerbrochen", "gehabt"] ∧
      zerbrechen.principalParts.tenseForm .futurePerfect = some ["wird", "zerbrochen", "haben"] ∧
      frieren.principalParts.tenseForm .pastPerfect = some ["war", "gefroren"] ∧
      frieren.principalParts.tenseForm Tense.Form.pastPerfect.perfect =
        some ["war", "gefroren", "gewesen"] ∧
      frieren.principalParts.tenseForm .futurePerfect = some ["wird", "gefroren", "sein"] ∧
      rennen.principalParts.tenseForm .presentPerfect = some ["ist", "gerannt"] := by
  decide

open Verbs in
/-- *rennen* has a present participle, but no auxiliary governs it, so there is no progressive;
nor is there a past of the future, a future of the future or a perfect of a complex
pluperfect. -/
example :
    periphrasis.nonfinite (.lexical rennen.principalParts) .presentParticiple = some "rennend" ∧
      rennen.principalParts.tenseForm .presentProgressive = none ∧
      rennen.principalParts.tenseForm { finite := .past, nonfinite := [.infinitive] } = none ∧
      rennen.principalParts.tenseForm (Tense.Form.future.under .infinitive) = none ∧
      rennen.principalParts.tenseForm Tense.Form.doublePerfect.perfect = none := by
  decide

end German
