/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Tense and tense forms

This file defines the grammatical tenses and the tense forms of a verb. A tense is past, present
or future (`Tense`); the cell of times it denotes is the matter of `Semantics/Tense/Defs.lean`. A
tense form of a verb, in the sense of the traditional grammars, is a member of the verb's tense
paradigm, such as the simple past or the present perfect. It is described here by its make-up, the
tense inflection of its finite verb and the nonfinite forms stacked under that verb. A synthetic
form has a finite lexical verb and nothing else. A periphrastic form is built from another form by
putting its verb, in a nonfinite form, under an auxiliary that takes over the tense inflection, so
that the perfect of the simple present *builds* is the present perfect *has built*, and the
perfect of that is the double perfect *has had built* of the South German dialects. Two languages
whose forms have the same make-up share the form, and which tense and which aspect it expresses in
each is a matter of analysis left to studies.

## Main declarations

* `Tense`: the grammatical tenses.
* `Tense.Form.Nonfinite`: the nonfinite verb forms that build periphrastic tense forms.
* `Tense.Form`: a tense form, by the inflection of its finite verb and its nonfinite chain.
* `Tense.Form.under`, `Tense.Form.perfect`, `Tense.Form.progressive`: the periphrastic form
  built on a form.
* `Tense.Form.simplePresent`, `Tense.Form.simplePast` and the forms built on them, among them
  `Tense.Form.presentPerfect`, `Tense.Form.doublePerfect` and `Tense.Form.future`.
* `Tense.Form.IsPerfect`: the form is the perfect of some form.
* `Tense.Periphrasis`, `Tense.Periphrasis.realize`: a language's means of building tense forms
  over its verbs, and the words of a form of a verb.

## References

* [huddleston-pullum-2002]
* [durrell-2011]
-/

@[expose] public section

/-- A grammatical tense is past, present or future. -/
inductive Tense where
  | past
  | present
  | future
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Tense

/-- A nonfinite verb form in a periphrastic tense form. -/
inductive Form.Nonfinite where
  /-- The infinitive, as German *bauen* under *werden*. -/
  | infinitive
  /-- The present participle, as English *building* under *be*. -/
  | presentParticiple
  /-- The past participle, as English *built* under *have* and German *gebaut* under *haben*. -/
  | pastParticiple
  deriving DecidableEq, Repr, Inhabited

/-- A tense form of a verb consists of the tense inflection of its finite verb and the nonfinite
forms under the finite verb, outermost first, so that the lexical verb is the last of them, or
the finite verb itself when there are none. -/
@[ext]
structure Form where
  /-- The tense inflection of the finite verb. -/
  finite : Tense
  /-- The nonfinite forms under the finite verb, outermost first. -/
  nonfinite : List Form.Nonfinite := []
  deriving DecidableEq, Repr

namespace Form

/-- The periphrastic form built on `f` puts the verb of `f` in the nonfinite form `n` under an
auxiliary with the tense inflection of `f`. -/
def under (n : Nonfinite) (f : Form) : Form := { f with nonfinite := n :: f.nonfinite }

/-- The perfect of a form puts its verb in the past participle under an auxiliary. -/
def perfect : Form → Form := under .pastParticiple

/-- The progressive of a form puts its verb in the present participle under an auxiliary. -/
def progressive : Form → Form := under .presentParticiple

@[simp] theorem under_finite (n : Nonfinite) (f : Form) : (f.under n).finite = f.finite := rfl

@[simp] theorem under_nonfinite (n : Nonfinite) (f : Form) :
    (f.under n).nonfinite = n :: f.nonfinite := rfl

theorem under_injective (n : Nonfinite) : Function.Injective (under n) := fun _ _ h ↦
  Form.ext (congrArg finite h :) (List.cons_injective (congrArg nonfinite h :))

@[simp] theorem perfect_inj {f g : Form} : f.perfect = g.perfect ↔ f = g :=
  (under_injective _).eq_iff

/-- The simple present is the synthetic present, as *builds*. -/
def simplePresent : Form := { finite := .present }

/-- The simple past is the synthetic past, as *built*. -/
def simplePast : Form := { finite := .past }

/-- The present progressive is the progressive of the simple present, as *is building*. -/
def presentProgressive : Form := simplePresent.progressive

/-- The past progressive is the progressive of the simple past, as *was building*. -/
def pastProgressive : Form := simplePast.progressive

/-- The present perfect is the perfect of the simple present, as *has built*. -/
def presentPerfect : Form := simplePresent.perfect

/-- The past perfect is the perfect of the simple past, as *had built*. -/
def pastPerfect : Form := simplePast.perfect

/-- The double perfect is the perfect of the present perfect. -/
def doublePerfect : Form := presentPerfect.perfect

/-- The future is the simple present of an auxiliary over the infinitive, as *will build*. -/
def future : Form := simplePresent.under .infinitive

/-- The future perfect is the future of the perfect, as *will have built*. -/
def futurePerfect : Form := presentPerfect.under .infinitive

/-- A form is a perfect when it is the perfect of some form. -/
def IsPerfect (f : Form) : Prop := ∃ g : Form, f = g.perfect

theorem isPerfect_iff {f : Form} : f.IsPerfect ↔ f.nonfinite.head? = some .pastParticiple := by
  refine ⟨fun ⟨g, h⟩ ↦ h ▸ rfl, fun h ↦ ?_⟩
  obtain ⟨t, _ | ⟨n, l⟩⟩ := f
  · simp at h
  · obtain rfl : n = .pastParticiple := by simpa using h
    exact ⟨⟨t, l⟩, rfl⟩

instance : DecidablePred IsPerfect := fun _ ↦ decidable_of_iff _ isPerfect_iff.symm

end Form

/-- A periphrasis is the means by which a language builds tense forms over its verbs `V`. It
gives the finite form of a verb in each tense, its nonfinite forms, and the auxiliary under
which a verb stands when it is in a given nonfinite form. Each is partial, since a language may
lack an inflection, as German lacks a future inflection, or a construction, as German lacks a
progressive. -/
structure Periphrasis (V : Type*) where
  /-- The finite form of a verb in a tense. -/
  finite : V → Tense → Option String
  /-- A nonfinite form of a verb. -/
  nonfinite : V → Form.Nonfinite → Option String
  /-- The auxiliary that governs a verb in a nonfinite form. -/
  auxiliary : V → Form.Nonfinite → Option V

namespace Periphrasis

variable {V : Type*} (L : Periphrasis V)

/-- `L.chain v ns` gives the nonfinite verbs of a tense form of `v` with nonfinite chain `ns`,
innermost first, and the verb left to be inflected. Each nonfinite form is taken by the verb
below it, and the auxiliary that governs it is the next verb up. -/
def chain (v : V) : List Form.Nonfinite → Option (List String × V)
  | [] => some ([], v)
  | n :: ns =>
    match chain v ns with
    | none => none
    | some (ws, u) =>
      match L.nonfinite u n, L.auxiliary u n with
      | some w, some a => some (ws ++ [w], a)
      | _, _ => none

/-- `L.realize v f` gives the finite verb of the tense form `f` of `v` and its nonfinite verbs,
innermost first. -/
def realize (v : V) (f : Form) : Option (String × List String) :=
  match L.chain v f.nonfinite with
  | none => none
  | some (ws, u) => (L.finite u f.finite).map (·, ws)

theorem length_of_chain (v : V) :
    ∀ (ns : List Form.Nonfinite) {ws : List String} {u : V},
      L.chain v ns = some (ws, u) → ws.length = ns.length
  | [], ws, u, h => by
    obtain ⟨rfl, -⟩ : [] = ws ∧ v = u := by simpa [chain] using h
    rfl
  | n :: ns, ws, u, h => by
    unfold chain at h
    split at h
    · exact absurd h (by simp)
    · next ws' u' h' =>
      split at h
      · obtain ⟨rfl, -⟩ : ws' ++ [_] = ws ∧ _ = u := by simpa using h
        simp [length_of_chain v ns h']
      · exact absurd h (by simp)

/-- A realized tense form has one nonfinite verb for each nonfinite form in its make-up. -/
theorem length_of_mem_realize {v : V} {f : Form} {x : String × List String}
    (h : x ∈ L.realize v f) : x.2.length = f.nonfinite.length := by
  unfold realize at h
  split at h
  · exact absurd h (by simp)
  · next ws u h' =>
    obtain ⟨w, -, rfl⟩ := Option.mem_map.1 h
    exact L.length_of_chain v _ h'

end Periphrasis

end Tense
