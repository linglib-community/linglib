module

public import Linglib.Core.Algebra.Group.Action.Prod
public import Linglib.Semantics.Questions.Highlighting
public import Linglib.Semantics.Questions.Hamblin
public import Studies.FarkasBruce2010
public import Linglib.Data.Examples.RoelofsenFarkas2015

/-!
# Roelofsen and Farkas (2015): Polarity particle responses as a window onto the interpretation of questions and assertions

This file formalizes Roelofsen and Farkas's account of polarity particle responses. A response
carries a relative feature, [agree] or [reverse], and an absolute feature, [+] or [−], each
presupposing something of the possibilities its prejacent and its antecedent highlight; together
they fix what the response expresses (`absolutePresup_and_relativePresup_iff`). So *yes, it is*
conveys the even answer after *Is it even?* and the odd one after *Is it odd?*
(`presup_query_ofPolarity`), and on a response sharing its antecedent's radical the relative
feature is Farkas and Bruce's relative polarity (`relativePresup_smul_iff`).

Languages differ in which particles realize which features, and a particle dedicated to a
combination blocks the others. English *yes* and *no* each realize a natural class of features,
so both occur in responses to a negative antecedent (`english_usable`), while French *si* and
German *doch* realize [reverse, +] alone. The account agrees with what Farkas and Bruce say the
English particles mark (`usable_english_iff_mem`).

## Implementation notes

* The most salient antecedent possibility is the one the antecedent formula highlights; the
  discourse context of the paper is not modelled.
* The features are `Discourse.Response.Feature`, whose [same] is the paper's [agree]. A feature
  is unmarked when its value is positive, as [agree] and [+] are (78), (80), and the prejacent
  of a relative feature `r` highlights `r • β` for the antecedent possibility `β`.
* In the planets examples *odd* is the complement of *even*, so each proposition is recorded as
  the polarity whose action yields it from *even*.
* French (9) prints its French sentences in the opposite order to their glosses; the French rows
  are (119)–(122).

## TODO

* The Romanian and Hungarian systems of §5.1, and the preferences among realizable particles,
  which rest on markedness, are not formalized.

## References

* [roelofsen-farkas-2015]
* [farkas-bruce-2010]
* [roelofsen-vangool-2010]
-/

@[expose] public section

namespace RoelofsenFarkas2015

open Discourse

variable {W : Type*}

/-! ### Polarity features (§4.1) -/

/-- The absolute feature `s` presupposes that the prejacent expresses a proposition `q` with a
single possibility, which it highlights with polarity `s` (68), (69). -/
def AbsolutePresup (s : Polarity) (q : Question W) (H : Set (Polarity × Set W)) : Prop :=
  ∃ α, q = Question.ofSet α ∧ H = {(s, α)}

/-- The relative feature `r`, [agree] when positive and [reverse] when negative, presupposes
that the antecedent highlights a unique possibility and that the prejacent highlights its image
under `r`, the same possibility with the same polarity or its complement with the opposite
polarity (70), (71). -/
def RelativePresup (r : Polarity) (H ant : Set (Polarity × Set W)) : Prop :=
  ∃ β, ant = {β} ∧ H = {r • β}

/-- An absolute feature `s` and a relative feature `r` presuppose a single antecedent possibility of
polarity `r * s` and a prejacent expressing its image under `r` ((72)–(75)). -/
theorem absolutePresup_and_relativePresup_iff {r s : Polarity} {q : Question W}
    {H ant : Set (Polarity × Set W)} :
    AbsolutePresup s q H ∧ RelativePresup r H ant ↔
      ∃ α, ant = {(r * s, α)} ∧ q = Question.ofSet (r • α) ∧ H = {(s, r • α)} := by
  constructor
  · rintro ⟨⟨α', hq, hα'⟩, ⟨t, β⟩, hant, hH⟩
    rw [hα', Prod.smul_mk, Set.singleton_eq_singleton_iff, Prod.mk.injEq] at hH
    obtain ⟨hs, hβ⟩ := hH
    refine ⟨β, ?_, hβ ▸ hq, hβ ▸ hα'⟩
    rw [hant, hs, smul_eq_mul, ← mul_assoc, Polarity.mul_self, Polarity.positive_mul]
  · rintro ⟨α, hant, hq, hH⟩
    refine ⟨⟨_, hq, hH⟩, (r * s, α), hant, ?_⟩
    rw [hH, Prod.smul_mk, smul_eq_mul, ← mul_assoc, Polarity.mul_self, Polarity.positive_mul]

theorem relativePresup_smul_iff {r : Polarity} (x : Response) (β : Polarity × Set W) :
    RelativePresup r {x.polarity • β} {x.antecedent • β} ↔ r = x.relative := by
  simp only [RelativePresup, Set.singleton_eq_singleton_iff, exists_eq_left']
  exact (Response.eq_relative_iff_smul_eq β).trans eq_comm |>.symm

/-! ### The questions of §3.3 -/

section Questions

open Highlighting Highlighting.Formula

variable {A : Type*} (v : A → Set W) {e o : A}

theorem proposition_query_even_eq_odd (hodd : v o = (v e)ᶜ) :
    (query (atom e)).proposition v = (query (atom o)).proposition v := by
  simp only [proposition, Question.query_ofSet, hodd, Question.polar_compl]

/-- A response of polarity `s` to a polar question of polarity `t` on `a` expresses `s • v a` with
relative feature `s / t` ((49), (50), (52), (53)). -/
theorem presup_query_ofPolarity {r s t : Polarity} (a : A) {q : Question W}
    {H : Set (Polarity × Set W)}
    (h : AbsolutePresup s q H ∧ RelativePresup r H ((query (ofPolarity t a)).highlights v)) :
    q = Question.ofSet (s • v a) ∧ r = s / t := by
  obtain ⟨α, hant, hq, -⟩ := absolutePresup_and_relativePresup_iff.1 h
  simp only [highlights, highlights_ofPolarity, Highlighting.project_singleton, Prod.smul_mk,
    smul_eq_mul, Polarity.mul_positive, Set.singleton_eq_singleton_iff, Prod.mk.injEq] at hant
  obtain ⟨rfl, rfl⟩ := hant
  refine ⟨?_, by cases r <;> cases s <;> decide⟩
  rw [hq, smul_smul, ← mul_assoc, Polarity.mul_self, Polarity.positive_mul]

/-- The alternative question *Is it even↑, or odd↓?* highlights two possibilities, so no
relative feature, and no particle response, is licensed after it (51). -/
theorem not_relativePresup_disj [Nonempty W] (hodd : v o = (v e)ᶜ) (r : Polarity)
    (H : Set (Polarity × Set W)) :
    ¬ RelativePresup r H ((inqDisj (atom e) (atom o)).highlights v) := by
  rintro ⟨β, hant, -⟩
  simp only [highlights, hodd] at hant
  have h₁ : ((.positive, v e) : Polarity × Set W) ∈ ({β} : Set _) := hant ▸ Or.inl rfl
  have h₂ : ((.positive, (v e)ᶜ) : Polarity × Set W) ∈ ({β} : Set _) := hant ▸ Or.inr rfl
  rw [Set.mem_singleton_iff] at h₁ h₂
  exact ne_compl_self (congrArg Prod.snd (h₁.trans h₂.symm))

end Questions

/-! ### Realization (§4.2, §5.2) -/

open Response (Feature)

/-- A particle realizes features, or a feature combination [r, s] as a whole. -/
inductive Target where
  | feature (f : Feature)
  | combination (r s : Polarity)
  deriving DecidableEq, Repr

/-- An English particle realizes the relative and the absolute feature of its polarity, *yes*
[agree] and [+], and *no* [reverse] and [−] (76). -/
def english (p : English.PolarityParticle) : List Target :=
  [.feature (.relative p.polarity), .feature (.absolute p.polarity)]

/-- French *oui* realizes [+], *non* [−], and *si* the combination [reverse, +] (118). -/
def french : French.PolarityParticle → List Target
  | .oui => [.feature (.absolute .positive)]
  | .non => [.feature (.absolute .negative)]
  | .si => [.combination .negative .positive]

/-- German *ja* realizes [agree] and [+], *nein* [reverse] and [−], and *doch* the combination
[reverse, +] (123). -/
def german : German.PolarityParticle → List Target
  | .ja => [.feature (.relative .positive), .feature (.absolute .positive)]
  | .nein => [.feature (.relative .negative), .feature (.absolute .negative)]
  | .doch => [.combination .negative .positive]

section Usable

variable {P : Type*} (R : P → List Target)

/-- A particle can realize the combination [r, s] when it realizes one of its features or the
combination itself. -/
def Realizes (p : P) (r s : Polarity) : Prop :=
  .feature (.relative r) ∈ R p ∨ .feature (.absolute s) ∈ R p ∨ .combination r s ∈ R p

/-- A particle is usable in an [r, s] response when it can realize it and no particle dedicated
to the combination blocks it. -/
def Usable (p : P) (r s : Polarity) : Prop :=
  Realizes R p r s ∧ ∀ q, .combination r s ∈ R q → .combination r s ∈ R p

instance (p : P) (r s : Polarity) : Decidable (Realizes R p r s) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

instance [Fintype P] [DecidableEq P] (p : P) (r s : Polarity) : Decidable (Usable R p r s) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Usable

/-- In English, [agree, +] responses take *yes*, [reverse, −] responses *no*, and [agree, −]
and [reverse, +] responses either particle (77). -/
theorem english_usable (p : English.PolarityParticle) :
    (Usable english p .positive .positive ↔ p = .yes) ∧
      (Usable english p .negative .negative ↔ p = .no) ∧
      Usable english p .positive .negative ∧ Usable english p .negative .positive := by
  cases p <;> decide

/-- French [agree, +] responses take *oui*, [reverse, +] responses *si*, and [agree, −] and
[reverse, −] responses *non* (119)–(122). -/
theorem french_usable (p : French.PolarityParticle) :
    (Usable french p .positive .positive ↔ p = .oui) ∧
      (Usable french p .negative .positive ↔ p = .si) ∧
      (Usable french p .positive .negative ↔ p = .non) ∧
      (Usable french p .negative .negative ↔ p = .non) := by
  cases p <;> decide

/-- German [agree, +] responses take *ja*, [reverse, +] responses *doch*, [reverse, −]
responses *nein*, and [agree, −] responses *ja* or *nein* (124)–(127). -/
theorem german_usable (p : German.PolarityParticle) :
    (Usable german p .positive .positive ↔ p = .ja) ∧
      (Usable german p .negative .positive ↔ p = .doch) ∧
      (Usable german p .negative .negative ↔ p = .nein) ∧
      (Usable german p .positive .negative ↔ p ≠ .doch) := by
  cases p <;> decide

/-- Each English particle realizes a natural class of features, those of its polarity, *yes*
the unmarked ones and *no* the marked ones (80). -/
theorem mem_english_iff {p : English.PolarityParticle} {f : Feature} :
    Target.feature f ∈ english p ↔ f.value = p.polarity := by
  cases f <;> simp [english, Response.Feature.value]

theorem combination_notMem_english (p : English.PolarityParticle) (r s : Polarity) :
    Target.combination r s ∉ english p := by
  simp [english]

theorem usable_english_iff_mem (p : English.PolarityParticle) (x : Response) :
    Usable english p x.relative x.polarity ↔ x ∈ FarkasBruce2010.english p := by
  simp [Usable, Realizes, mem_english_iff, combination_notMem_english, Response.Feature.value,
    FarkasBruce2010.mem_english_iff]

theorem usable_si_iff_mem_reversePositive (x : Response) :
    Usable french .si x.relative x.polarity ↔ x ∈ FarkasBruce2010.reversePositive := by
  obtain ⟨m, a, s⟩ := x
  cases m <;> cases a <;> cases s <;> decide

/-! ### The examples -/

/-- The particles of the examples. -/
inductive Particle where
  | en (p : English.PolarityParticle)
  | fr (p : French.PolarityParticle)
  | de (p : German.PolarityParticle)
  deriving DecidableEq, Repr

/-- A particle is usable in an [r, s] response in its language. -/
def Particle.Usable : Particle → Polarity → Polarity → Prop
  | .en p, r, s => RoelofsenFarkas2015.Usable english p r s
  | .fr p, r, s => RoelofsenFarkas2015.Usable french p r s
  | .de p, r, s => RoelofsenFarkas2015.Usable german p r s

instance (p : Particle) (r s : Polarity) : Decidable (p.Usable r s) := by
  cases p <;> unfold Particle.Usable <;> infer_instance

/-- The particles of each language, by Glottocode and spelling. -/
def particleTable : List (String × List (String × Particle)) :=
  [("stan1293", [English.PolarityParticle.yes, .no].map fun p ↦ (p.form, .en p)),
    ("stan1290", [French.PolarityParticle.oui, .non, .si].map fun p ↦ (p.form, .fr p)),
    ("stan1295", [German.PolarityParticle.ja, .nein, .doch].map fun p ↦ (p.form, .de p))]

def polarityTable : List (String × Polarity) := [("positive", .positive), ("negative", .negative)]

/-- A row records a particle response to an assertion, with the polarities of the antecedent
and of the response, the relative feature the paper assigns it, the particle, and the judgment. -/
structure Row where
  response : Response
  relative : Polarity
  particle : Particle
  judgment : Judgment
  deriving DecidableEq, Repr

def relativeTable : List (String × Polarity) := [("agree", .positive), ("reverse", .negative)]

def Row.ofDatum (ex : Datum) : Option Row := do
  guard (ex.feature? "reaction" = some "assertion")
  let table ← List.lookup ex.language particleTable
  let antecedent ← ex.parse? "antecedent" polarityTable
  let polarity ← ex.parse? "response" polarityTable
  let relative ← ex.parse? "relative" relativeTable
  let particle ← ex.parse? "particle" table
  pure ⟨⟨.assertion, antecedent, polarity⟩, relative, particle, ex.judgment⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem relative_eq : ∀ r ∈ rows, r.response.relative = r.relative := by
  decide

theorem judgment_iff_usable :
    ∀ r ∈ rows, (r.judgment = .acceptable ↔
      r.particle.Usable r.response.relative r.response.polarity) := by
  decide

/-- The propositions of the planets examples are *even* and its complement *odd*, each recorded
as the polarity whose action yields it from *even*. -/
def planetTable : List (String × Polarity) :=
  [("even", .positive), ("odd", .negative), ("not even", .negative), ("not odd", .positive)]

/-- A question row records a response by an English particle to a question about the number of
planets: the polarity and radical of a polar question, or none for the alternative question, the
polarity of the response, its particle, what it conveys, and the judgment. -/
structure QuestionRow where
  question : Option (Polarity × Polarity)
  response : Polarity
  particle : English.PolarityParticle
  conveys : Option Polarity
  judgment : Judgment
  deriving DecidableEq, Repr

def QuestionRow.ofDatum (ex : Datum) : Option QuestionRow := do
  let particle ← ex.parse? "particle" [("yes", English.PolarityParticle.yes), ("no", .no)]
  let response ← ex.parse? "response" polarityTable
  if ex.feature? "reaction" = some "question" then
    let t ← ex.parse? "antecedent" polarityTable
    let radical ← ex.parse? "radical" planetTable
    pure ⟨some (t, radical), response, particle, ex.parse? "conveys" planetTable, ex.judgment⟩
  else if ex.feature? "reaction" = some "alternativeQuestion" then
    pure ⟨none, response, particle, none, ex.judgment⟩
  else none

def questionRows : List QuestionRow := Examples.all.filterMap QuestionRow.ofDatum

theorem ofDatum_isSome :
    ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome ∨ (QuestionRow.ofDatum ex).isSome := by
  decide

/-- A question row is predicted when a response of polarity `s` to a polar question of polarity
`t` is acceptable just when its particle is usable with the relative feature `s / t` and conveys
`s` applied to the radical (`presup_query_ofPolarity`), and when no particle response to the
alternative question is acceptable (`not_relativePresup_disj`). -/
def QuestionRow.Predicted : QuestionRow → Prop
  | ⟨some (t, a), s, p, c, j⟩ => (j = .acceptable ↔ Usable english p (s / t) s) ∧ c = some (s * a)
  | ⟨none, _, _, _, j⟩ => j ≠ .acceptable

instance : DecidablePred QuestionRow.Predicted := fun r ↦ by
  obtain ⟨_ | ⟨t, a⟩, s, p, c, j⟩ := r <;> unfold QuestionRow.Predicted <;> infer_instance

/-- The account predicts the judgment and the conveyed proposition of every response to the
questions of (49)–(53). -/
theorem questionRows_predicted : ∀ r ∈ questionRows, r.Predicted := by
  decide

end RoelofsenFarkas2015
