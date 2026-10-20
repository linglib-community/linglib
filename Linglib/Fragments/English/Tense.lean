module

public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Fragments.English.Verbs.Basic
public import Linglib.Syntax.Category.Verb.Tense

/-!
# English tense forms

This file describes the tense forms of English, following Huddleston's chapter on the verb in
the Cambridge grammar. English marks one tense contrast by inflection, the present *takes*
against the preterite *took*, and the rest by auxiliaries. The perfect, a secondary past tense,
puts the past participle under *have*, as in *has taken*, and the progressive aspect puts the
gerund-participle under *be*, as in *is taking*. The auxiliaries come in a fixed order, the
perfect before the progressive, so that *has been taking* is a form and *is having taken* is
not, and neither auxiliary combines with itself. The eight tense forms are therefore the
present and the preterite of the simple, progressive, perfect and perfect progressive
constructions. The grammar treats *will* as a modal auxiliary, a marker of mood, so *will take*
is not among the tense forms.

## Main declarations

* `English.Tense.TenseVerb`: a lexical verb or one of the tense auxiliaries *have* and *be*.
* `English.Tense.periphrasis`, `English.Verbs.Verb.tenseForm`: the means by which English builds
  its tense forms, and the words of a tense form of a verb, finite verb first.
* `English.Tense.tenseForms`: the eight tense forms; `Verb.tenseForm_isSome_iff` shows that they are
  exactly the forms that English realizes.

## Implementation notes

`Verb.tenseForm` gives the third person singular, the finite *have* and *be* being the entries of
`English.Auxiliaries`. The fixed order of the auxiliaries is not stipulated on forms: it follows
from which auxiliary may govern which verb, *have* governing a lexical verb or *be*, and *be*
governing a lexical verb only.

## References

* [huddleston-pullum-2002]
-/

@[expose] public section

namespace English.Tense

open English.Verbs

/-- A verb in a tense form is a lexical verb or one of the tense auxiliaries *have* and *be*. -/
inductive TenseVerb where
  | lexical (v : Verbs.Verb)
  | have
  | be

open Tense.Form in
/-- English builds its tense forms with the past participle under *have* and the present
participle under *be*. The auxiliary *have* governs a lexical verb or *be*, the auxiliary *be*
governs a lexical verb only, and no tense auxiliary governs an infinitive. -/
def periphrasis : Tense.Periphrasis TenseVerb where
  finite
    | .lexical v, .present => some (v.realize .thirdSg)
    | .lexical v, .past => some (v.realize .past)
    | .have, .present => some Auxiliaries.has.form
    | .have, .past => some Auxiliaries.had.form
    | .be, .present => some Auxiliaries.is_.form
    | .be, .past => some Auxiliaries.was.form
    | _, .future => none
  nonfinite
    | .lexical v, .pastParticiple => some (v.realize .pastParticiple)
    | .lexical v, .presentParticiple => some (v.realize .presentParticiple)
    | .be, .pastParticiple => some "been"
    | _, _ => none
  auxiliary
    | .lexical _, .pastParticiple | .be, .pastParticiple => some .have
    | .lexical _, .presentParticiple => some .be
    | _, _ => none

/-- English has the present and the preterite of the simple, progressive, perfect and perfect
progressive constructions. -/
def tenseForms : List Tense.Form :=
  [.simplePresent, .simplePast, .presentProgressive, .pastProgressive, .presentPerfect,
    .pastPerfect, Tense.Form.presentProgressive.perfect, Tense.Form.pastProgressive.perfect]

/-- The chains English builds over a lexical verb are the empty one, the perfect, the
progressive, and the perfect of the progressive, and each leaves the lexical verb, *have*, *be*
and *have* to be inflected. -/
theorem chain_eq_some {v : Verbs.Verb} :
    ∀ {ns : List Tense.Form.Nonfinite} {ws : List String} {u : TenseVerb},
      periphrasis.chain (.lexical v) ns = some (ws, u) →
        ns = [] ∧ u = .lexical v ∨ ns = [.pastParticiple] ∧ u = .have ∨
          ns = [.presentParticiple] ∧ u = .be ∨
          ns = [.pastParticiple, .presentParticiple] ∧ u = .have
  | [], ws, u, h => by
    obtain ⟨-, rfl⟩ : [] = ws ∧ TenseVerb.lexical v = u := by
      simpa [Tense.Periphrasis.chain] using h
    exact .inl ⟨rfl, rfl⟩
  | n :: ns, ws, u, h => by
    unfold Tense.Periphrasis.chain at h
    split at h
    · exact absurd h (by simp)
    · next ws' u' h' =>
      rcases chain_eq_some h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        cases n <;> simp_all [periphrasis]

end English.Tense

namespace English.Verbs

open English.Tense

/-- `v.tenseForm f` gives the words of the tense form `f` of `v` in the third person singular, the
finite verb first and then the nonfinite verbs, the lexical verb last. -/
def Verb.tenseForm (v : Verbs.Verb) (f : Tense.Form) : Option (List String) :=
  (periphrasis.realize (.lexical v) f).map fun x ↦ x.1 :: x.2.reverse

/-- The tense forms are exactly the forms that English realizes. -/
theorem Verb.tenseForm_isSome_iff (v : Verbs.Verb) (f : Tense.Form) :
    (v.tenseForm f).isSome ↔ f ∈ tenseForms := by
  constructor
  · obtain ⟨t, ns⟩ := f
    intro h
    simp only [Verb.tenseForm, Option.isSome_map, Tense.Periphrasis.realize] at h
    split at h
    · exact absurd h (by simp)
    · next ws u h' =>
      rcases chain_eq_some h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        cases t <;> first | decide | exact absurd h (by simp [periphrasis])
  · intro h
    simp only [tenseForms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The forms of *build*, among them the perfect progressive; the progressive of the perfect and
the *will* future are not tense forms. -/
example :
    build.tenseForm .simplePast = some ["built"] ∧
      build.tenseForm .presentPerfect = some ["has", "built"] ∧
      build.tenseForm .pastProgressive = some ["was", "building"] ∧
      build.tenseForm Tense.Form.presentProgressive.perfect = some ["has", "been", "building"] ∧
      build.tenseForm Tense.Form.presentPerfect.progressive = none ∧
      build.tenseForm .future = none := by
  decide

end English.Verbs
