module

public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Fragments.English.Verbs.Basic
public import Linglib.Syntax.Category.Verb.Tense

/-!
# English tense forms

This file describes the tense forms of English, following Huddleston's chapter on the verb in
the Cambridge grammar. English has two systems of tense and one of aspect. The primary tense is
inflectional, the present *takes* against the preterite *took*. The secondary tense, the perfect,
puts the past participle under *have*, as in *has taken*, and the progressive aspect puts the
gerund-participle under *be*, as in *is taking*. The auxiliaries are optional but each has a
fixed position in a sequence of auxiliaries, the perfect before the progressive, and each
determines the form of the verb after it. So *has been taking* is a form and *is having taken*
is not, and as perfect *have* has no past participle there is no perfect of a perfect. The
tense forms are therefore the present and the preterite of the simple, progressive, perfect and
perfect progressive constructions. The grammar treats *will* as a modal auxiliary, a marker of
mood, so *will take* is not among the tense forms.

## Main declarations

* `English.Tense.TenseVerb`: a lexical verb or one of the tense auxiliaries *have* and *be*.
* `English.Tense.periphrasis`, `English.Verbs.Verb.tenseForm`: the means by which English builds
  the tense forms of a verb for a subject, and the words of a tense form, finite verb first.
* `English.Tense.tenseForms`: the tense forms, whose auxiliaries come in their fixed order
  (`English.Tense.mem_tenseForms`); `Verb.tenseForm_isSome_iff` shows that they are exactly the
  forms that English realizes.

## Implementation notes

The grammar's gerund-participle is the present participle of `Tense.Form.Nonfinite`. The order
of the auxiliaries is not stipulated on forms: an auxiliary governs a verb in the form it
determines when it comes before that verb in the sequence (`TenseVerb.position`,
`TenseVerb.complementForm`). The finite verb agrees with the subject, *have* and *be* by their
agreement targets in `English.Auxiliaries` and a lexical verb by `English.Auxiliaries.presentForm`
in the present.

## References

* [huddleston-pullum-2002]
-/

@[expose] public section

namespace English.Tense

open English.Verbs English.Auxiliaries
open scoped List

/-- A verb in a tense form is a lexical verb or one of the tense auxiliaries, perfect *have* and
progressive *be*. -/
inductive TenseVerb where
  | lexical (v : Verbs.Verb)
  | have
  | be

namespace TenseVerb

/-- The position of a verb in a sequence of auxiliaries ([huddleston-pullum-2002] ch. 3 §2.3,
p. 105): the modal first, perfect *have* second, progressive *be* third and passive *be* fourth,
and the lexical verb last. -/
def position : TenseVerb → ℕ
  | .have => 2
  | .be => 3
  | .lexical _ => 5

/-- The form a tense auxiliary determines in the next verb ([huddleston-pullum-2002] ch. 3 §2.3,
p. 106): perfect *have* the past participle and progressive *be* the gerund-participle. -/
def complementForm : TenseVerb → Option Tense.Form.Nonfinite
  | .have => some .pastParticiple
  | .be => some .presentParticiple
  | .lexical _ => none

end TenseVerb

/-- English builds the tense forms of a verb for a subject in the cell `c`. A lexical verb has
all its nonfinite forms; *be* has the plain form *be*, the gerund-participle *being* and the past
participle *been*; and perfect *have* has *have* and *having* but no past participle
([huddleston-pullum-2002] ch. 3 §1.1, p. 75, §2.5.6, p. 111). The auxiliary governing a verb in
a nonfinite form is the tense auxiliary that determines that form and comes before the verb, so
that *have* governs *be* and a lexical verb and *be* a lexical verb only, and no tense auxiliary
governs the plain form, which a modal determines. -/
def periphrasis (c : Cell) : Tense.Periphrasis TenseVerb where
  finite
    | .lexical v, .present =>
      some (presentForm (v.realize .thirdSg) (v.realize .plainPresent) (c .person) (c .number))
    | .lexical v, .past => some (v.realize .past)
    | .have, .present => some (havePresent.form c)
    | .have, .past => some had.form
    | .be, .present => some (bePresent.form c)
    | .be, .past => some (bePreterite.form c)
    | _, .future => none
  nonfinite
    | .lexical v, .infinitive => some (v.realize .base)
    | .lexical v, .pastParticiple => some (v.realize .pastParticiple)
    | .lexical v, .presentParticiple => some (v.realize .presentParticiple)
    | .have, .infinitive => some "have"
    | .have, .presentParticiple => some "having"
    | .have, .pastParticiple => none
    | .be, .infinitive => some "be"
    | .be, .presentParticiple => some "being"
    | .be, .pastParticiple => some "been"
  auxiliary u n :=
    [TenseVerb.have, .be].find? fun a ↦ a.complementForm = some n ∧ a.position < u.position

/-- The tense forms are the present and the preterite of the forms with neither, either or both
of the tense auxiliaries in their fixed order. -/
def tenseForms : List Tense.Form :=
  [Tense.present, .past].flatMap fun t ↦
    [Tense.Form.Nonfinite.pastParticiple, .presentParticiple].sublists.map (⟨t, ·⟩)

/-- A tense form is a present or a preterite whose nonfinite forms are a sublist of the past
participle of the perfect followed by the gerund-participle of the progressive. -/
theorem mem_tenseForms {f : Tense.Form} :
    f ∈ tenseForms ↔
      f.finite ≠ .future ∧ f.nonfinite <+ [.pastParticiple, .presentParticiple] := by
  obtain ⟨t, ns⟩ := f
  cases t <;> simp [tenseForms, ← List.mem_sublists]

/-- The tense forms are those of the simple, progressive, perfect and perfect progressive
constructions. -/
example : tenseForms.Perm
    [.simplePresent, .simplePast, .presentProgressive, .pastProgressive, .presentPerfect,
      .pastPerfect, Tense.Form.presentProgressive.perfect, Tense.Form.pastProgressive.perfect] := by
  decide

/-- The chains English builds over a lexical verb are the empty one, the perfect, the
progressive, and the perfect of the progressive, and each leaves the lexical verb, *have*, *be*
and *have* to be inflected. -/
theorem chain_eq_some {c : Cell} {v : Verbs.Verb} :
    ∀ {ns : List Tense.Form.Nonfinite} {ws : List String} {u : TenseVerb},
      (periphrasis c).chain (.lexical v) ns = some (ws, u) →
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
        cases n <;> simp_all [periphrasis, TenseVerb.complementForm, TenseVerb.position]

end English.Tense

namespace English.Verbs

open English.Tense English.Auxiliaries

/-- `v.tenseForm c f` gives the words of the tense form `f` of `v` for a subject in the cell `c`,
the finite verb first and then the nonfinite verbs, the lexical verb last. -/
def Verb.tenseForm (v : Verbs.Verb) (c : Auxiliaries.Cell) (f : Tense.Form) :
    Option (List String) :=
  ((periphrasis c).realize (.lexical v) f).map fun x ↦ x.1 :: x.2.reverse

/-- The tense forms are exactly the forms that English realizes. -/
theorem Verb.tenseForm_isSome_iff (v : Verbs.Verb) (c : Auxiliaries.Cell) (f : Tense.Form) :
    (v.tenseForm c f).isSome ↔ f ∈ tenseForms := by
  constructor
  · obtain ⟨t, ns⟩ := f
    intro h
    simp only [Verb.tenseForm, Option.isSome_map, Tense.Periphrasis.realize] at h
    split at h
    · exact absurd h (by simp)
    · next ws u h' =>
      rcases chain_eq_some h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        cases t <;> first | decide | exact absurd h (by simp [periphrasis])
  · obtain ⟨t, ns⟩ := f
    rw [mem_tenseForms, ← List.mem_sublists]
    rintro ⟨ht, hns⟩
    obtain rfl | rfl | rfl | rfl : ns = [] ∨ ns = [.pastParticiple] ∨ ns = [.presentParticiple] ∨
        ns = [.pastParticiple, .presentParticiple] := by simpa [List.sublists] using hns
    all_goals cases t <;> first | rfl | exact absurd rfl ht

/-- The forms of *build*: the finite verb agrees with the subject, the perfect progressive is a
form, and the progressive of the perfect, the perfect of the perfect and the *will* future are
not. -/
example :
    build.tenseForm (cell .third .singular) .simplePast = some ["built"] ∧
      build.tenseForm (cell .first .singular) .presentProgressive = some ["am", "building"] ∧
      build.tenseForm (cell .third .plural) .presentPerfect = some ["have", "built"] ∧
      build.tenseForm (cell .second .singular) .pastProgressive = some ["were", "building"] ∧
      build.tenseForm (cell .third .singular) Tense.Form.presentProgressive.perfect =
        some ["has", "been", "building"] ∧
      build.tenseForm (cell .third .singular) Tense.Form.presentPerfect.progressive = none ∧
      build.tenseForm (cell .third .singular) Tense.Form.presentPerfect.perfect = none ∧
      build.tenseForm (cell .third .singular) .future = none := by
  decide

end English.Verbs
