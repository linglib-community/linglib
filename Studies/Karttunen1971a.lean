module

public import Linglib.Semantics.Presupposition.Implicative
public import Linglib.Semantics.Presupposition.Verb
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.English.Verbs.Copular

/-!
# Karttunen (1971)

Karttunen identifies the implicative verbs, *manage*, *remember*, *bother*, *dare*, *happen* and
the others listed in (2), whose assertion commits the speaker to the complement and whose
negation commits the speaker to its negation. He analyzes such a sentence as a
presupposition–proposition pair: the proposition `v(S)` is what is asserted, negated or
questioned, and the presupposition says what condition `v(S)` is for the complement. Schema (37)
makes `v(S)` necessary and sufficient for `S` (*manage*), (41) necessary and sufficient for `¬S`
(*fail*, *forget*), (54) necessary only (*be able*, *be possible*), and (59) sufficient only
(the positive verbs of (56), *cause*, *make*, *have* and *force*); the non-implicatives *hope*,
*want* and *try* carry no such presupposition.

Each schema fixes an implication signature: (37) is `+/−`, (41) `−/+`, (54) `◦/−` and (59) `+/◦`,
and the negative verbs of (56), *prevent* and *dissuade*, are `−/◦`. The analysis is
`Implicative.sentence` under the material interpretation of the conditions
(`Implicative.Interpretation.material`), which gives the paper's entailment facts: double negation
cancels as in (13) (`manage_neg_neg_imp`), and the one-way schemas and the non-implicatives leave
the other direction open (`force_neg_not_entails`, `beAble_not_entails`,
`nonImplicative_not_entails`). The English fragment's entries for the verbs of (2), (38), (44) and
(56) carry the signatures of their schemas (`implicative_eq`) and so are presupposition triggers
(`isTrigger_of_mem_english`), while its entries for the non-implicatives of (2) carry `◦/◦`
(`implicative_eq_bot`).

## Implementation notes

Karttunen states (59) for the positive verbs of (56) only. The negative ones are read with the
matching presupposition, `v(S)` sufficient for `¬S`.

## References

* [karttunen-1971]
-/

@[expose] public section

namespace Karttunen1971a

open Presupposition Implicative NaturalLogic

/-- Double negation cancels, so that *John didn't remember not to lock his door* commits the
speaker to *John locked his door* (13). -/
theorem manage_neg_neg_imp {W : Type*} {v S : W → Prop} {w : W}
    (hs : (-sentence (Interpretation.material W) ⟨.some .positive, .some .negative⟩ v
      fun w ↦ ¬ S w) w = 1) : S w :=
  not_not.mp (holds_signed_of_implied_eq (m := .negative) (q := .negative) rfl (by simpa using hs))

/-- (58) *John didn't force Mary to stay home* leaves open whether she stayed. -/
theorem force_neg_not_entails : ∃ (v S : Unit → Prop),
    (-sentence (Interpretation.material Unit) ⟨.some .positive, ⊥⟩ v S) () = 1 ∧ S () :=
  ⟨fun _ ↦ False, fun _ ↦ True, by simp [sentence, Interpretation.material, Flat.bot_ne_coe],
    trivial⟩

/-- (55) *John was able to come* leaves open whether he came. -/
theorem beAble_not_entails : ∃ (v S : Unit → Prop),
    sentence (Interpretation.material Unit) ⟨⊥, .some .negative⟩ v S () = 1 ∧ ¬ S () :=
  ⟨fun _ ↦ True, fun _ ↦ False, by simp [sentence, Interpretation.material, Flat.bot_ne_coe], id⟩

/-- A non-implicative, whose signature `◦/◦` gives it no presupposition, commits the speaker to
nothing about its complement in either polarity (5). -/
theorem nonImplicative_not_entails :
    (∃ (v S : Unit → Prop), sentence (Interpretation.material Unit) ⊥ v S () = 1 ∧ ¬ S ()) ∧
      ∃ (v S : Unit → Prop), (-sentence (Interpretation.material Unit) ⊥ v S) () = 1 ∧ S () :=
  ⟨⟨fun _ ↦ True, fun _ ↦ False, by simp [sentence, Interpretation.material, Flat.bot_ne_coe], id⟩,
   ⟨fun _ ↦ False, fun _ ↦ True, by simp [sentence, Interpretation.material, Flat.bot_ne_coe],
    trivial⟩⟩

/-! ### The English lexicon -/

section Lexicon

open English.Verbs hiding Verb

/-- The English fragment's entries for the implicatives of (2), with the signature of schema
(37), for the negative implicatives of (38), with that of (41), for *be able* of (44), with that
of (54), and for the verbs of (56), with that of (59) or its negative counterpart, as far as the
fragment covers the lists. Its *get* is the causative sense, its *avoid* takes a noun phrase, and
it has no *dissuade*. -/
def english : List (Verb × ImplicationSignature) :=
  [(manage.toVerb, ⟨.some .positive, .some .negative⟩),
    (remember.toVerb, ⟨.some .positive, .some .negative⟩),
    (bother.toVerb, ⟨.some .positive, .some .negative⟩),
    (dare.toVerb, ⟨.some .positive, .some .negative⟩),
    (venture.toVerb, ⟨.some .positive, .some .negative⟩),
    (condescend.toVerb, ⟨.some .positive, .some .negative⟩),
    (happen.toVerb, ⟨.some .positive, .some .negative⟩),
    (fail.toVerb, ⟨.some .negative, .some .positive⟩),
    (forget.toVerb, ⟨.some .negative, .some .positive⟩),
    (neglect.toVerb, ⟨.some .negative, .some .positive⟩),
    (Copular.beAble, ⟨⊥, .some .negative⟩),
    (cause.toVerb, ⟨.some .positive, ⊥⟩),
    (make.toVerb, ⟨.some .positive, ⊥⟩),
    (have_caus.toVerb, ⟨.some .positive, ⊥⟩),
    (force.toVerb, ⟨.some .positive, ⊥⟩),
    (prevent.toVerb, ⟨.some .negative, ⊥⟩)]

/-- Each entry carries the signature of its schema. -/
theorem implicative_eq : ∀ p ∈ english, p.1.implicative = p.2 := by
  decide

/-- Every entry is a presupposition trigger, as (37), (41), (54) and (59) each pair the
proposition with a presupposition. -/
theorem isTrigger_of_mem_english : ∀ p ∈ english, p.1.IsTrigger := by
  decide

/-- The fragment's entries for the non-implicatives of (2). -/
def nonImplicative : List Verb :=
  [try_.toVerb, promise.toVerb, want.toVerb, intend.toVerb, decide_.toVerb, hope.toVerb]

/-- The non-implicatives of (2) carry the signature `◦/◦`, implying nothing. -/
theorem implicative_eq_bot : ∀ v ∈ nonImplicative, v.implicative = ⊥ := by
  decide

end Lexicon

end Karttunen1971a
