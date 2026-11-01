module

public import Linglib.Core.Algebra.Group.Action.Prod
public import Linglib.Semantics.Questions.Highlighting
public import Linglib.Semantics.Questions.Polar
public import Studies.FarkasBruce2010
public import Linglib.Data.Examples.RoelofsenFarkas2015
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Roelofsen and Farkas (2015): Polarity particle responses as a window onto the interpretation of questions and assertions

This file formalizes Roelofsen and Farkas's account of polarity particle responses. A response
carries a relative feature, [agree] or [reverse], and an absolute feature, [+] or [−], each
presupposing something of the possibilities its prejacent and its antecedent highlight; together
they fix what the response expresses (`absolutePresup_and_relativePresup_iff`). So *yes, it is*
conveys the even answer after *Is it even?* and the odd one after *Is it odd?*
(`presup_query_ofPolarity`), and on a response sharing its antecedent's radical the relative
feature is Farkas and Bruce's relative polarity (`relativePresup_smul_iff`).

Languages differ in which particles realize which features (`PolarityParticle.targets`), and a
particle dedicated to a combination blocks the others of its language. English *yes* and *no*
each realize a natural class of features (`english_natural_class`), so both occur in responses to
a negative antecedent (`english_usable`), while French *si* and German *doch* realize
[reverse, +] alone. The account agrees with what Farkas and Bruce say the English particles, *si*
and *doch* mark (`usable_iff_mem_marks`).

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

-- (51)
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

/-- The polarity particles of the paper's examples. -/
inductive PolarityParticle where
  | yes | no | oui | non | si | ja | nein | doch
  deriving DecidableEq, Repr, Fintype

/-- The fragment entry of a particle. -/
def PolarityParticle.entry : PolarityParticle → Particle
  | .yes => English.PolarityParticles.yes
  | .no => English.PolarityParticles.no
  | .oui => French.PolarityParticles.oui
  | .non => French.PolarityParticles.non
  | .si => French.PolarityParticles.si
  | .ja => German.PolarityParticles.ja
  | .nein => German.PolarityParticles.nein
  | .doch => German.PolarityParticles.doch

/-- The English particles. -/
def english : List PolarityParticle := [.yes, .no]

/-- The French particles. -/
def french : List PolarityParticle := [.oui, .non, .si]

/-- The German particles. -/
def german : List PolarityParticle := [.ja, .nein, .doch]

example : english.map PolarityParticle.entry = English.PolarityParticles.all := rfl

example : french.map PolarityParticle.entry = French.PolarityParticles.all := rfl

example : german.map PolarityParticle.entry = German.PolarityParticles.all := rfl

namespace PolarityParticle

/-- The particles of the language of `p`, which compete with it. -/
def inventory : PolarityParticle → List PolarityParticle
  | .yes | .no => english
  | .oui | .non | .si => french
  | .ja | .nein | .doch => german

/-- What a particle realizes: English *yes* [agree] and [+] and *no* [reverse] and [−] (76),
French *oui* [+], *non* [−] and *si* the combination [reverse, +] (118), and German *ja* [agree]
and [+], *nein* [reverse] and [−] and *doch* the combination [reverse, +] (123). -/
def targets : PolarityParticle → List Target
  | .yes | .ja => [.feature (.relative .positive), .feature (.absolute .positive)]
  | .no | .nein => [.feature (.relative .negative), .feature (.absolute .negative)]
  | .oui => [.feature (.absolute .positive)]
  | .non => [.feature (.absolute .negative)]
  | .si | .doch => [.combination .negative .positive]

/-- A particle can realize the combination [r, s] when it realizes one of its features or the
combination itself. -/
def Realizes (p : PolarityParticle) (r s : Polarity) : Prop :=
  .feature (.relative r) ∈ p.targets ∨ .feature (.absolute s) ∈ p.targets ∨
    .combination r s ∈ p.targets

/-- A particle is usable in an [r, s] response when it can realize it and no particle of its
language dedicated to the combination blocks it. -/
def Usable (p : PolarityParticle) (r s : Polarity) : Prop :=
  p.Realizes r s ∧ ∀ q ∈ p.inventory, .combination r s ∈ q.targets → .combination r s ∈ p.targets

instance (p : PolarityParticle) (r s : Polarity) : Decidable (p.Realizes r s) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

instance (p : PolarityParticle) (r s : Polarity) : Decidable (p.Usable r s) :=
  inferInstanceAs (Decidable (_ ∧ _))

end PolarityParticle

/-- In English, [agree, +] responses take *yes*, [reverse, −] responses *no*, and [agree, −]
and [reverse, +] responses either particle (77). -/
theorem english_usable : ∀ p ∈ english,
    (p.Usable .positive .positive ↔ p = .yes) ∧ (p.Usable .negative .negative ↔ p = .no) ∧
      p.Usable .positive .negative ∧ p.Usable .negative .positive := by
  decide

-- (119), (122)
theorem french_usable : ∀ p ∈ french,
    (p.Usable .positive .positive ↔ p = .oui) ∧ (p.Usable .negative .positive ↔ p = .si) ∧
      (p.Usable .positive .negative ↔ p = .non) ∧ (p.Usable .negative .negative ↔ p = .non) := by
  decide

-- (124), (127)
theorem german_usable : ∀ p ∈ german,
    (p.Usable .positive .positive ↔ p = .ja) ∧ (p.Usable .negative .positive ↔ p = .doch) ∧
      (p.Usable .negative .negative ↔ p = .nein) ∧ (p.Usable .positive .negative ↔ p ≠ .doch) := by
  decide

/-- Each English particle realizes a natural class of features, those of one value, *yes* the
unmarked ones and *no* the marked ones (80). -/
theorem english_natural_class :
    ∀ p ∈ english, ∃ v : Polarity, ∀ f : Feature, .feature f ∈ p.targets ↔ f.value = v := by
  decide

/-- The account agrees with what Farkas and Bruce say the English particles, *si* and *doch*
mark. -/
theorem usable_iff_mem_marks (x : Response) :
    (PolarityParticle.yes.Usable x.relative x.polarity ↔
        x ∈ FarkasBruce2010.PolarityParticle.yes.marks) ∧
      (PolarityParticle.no.Usable x.relative x.polarity ↔
        x ∈ FarkasBruce2010.PolarityParticle.no.marks) ∧
      (PolarityParticle.si.Usable x.relative x.polarity ↔
        x ∈ FarkasBruce2010.PolarityParticle.si.marks) ∧
      (PolarityParticle.doch.Usable x.relative x.polarity ↔
        x ∈ FarkasBruce2010.PolarityParticle.doch.marks) := by
  obtain ⟨m, a, s⟩ := x
  cases m <;> cases a <;> cases s <;> decide

/-! ### The examples -/

/-- The particles of each language's examples, by Glottocode. -/
def particlesOf : List (Glottocode × List PolarityParticle) :=
  [(.english, english), (.french, french), (.german, german)]

/-- The particle of a row, by its spelling among the particles of the row's language. -/
def particleOf? (ex : Datum) : Option PolarityParticle := do
  ex.parse? "particle" ((← ex.byLanguage particlesOf).map fun p ↦ (p.entry.form, p))

def polarityTable : List (String × Polarity) := [("positive", .positive), ("negative", .negative)]

/-- A row records a particle response to an assertion, with the polarities of the antecedent
and of the response, the relative feature the paper assigns it, the particle, and the judgment. -/
structure Row where
  response : Response
  relative : Polarity
  particle : PolarityParticle
  judgment : Judgment
  deriving DecidableEq, Repr

def relativeTable : List (String × Polarity) := [("agree", .positive), ("reverse", .negative)]

def Row.ofDatum (ex : Datum) : Option Row := do
  guard (ex.feature? "reaction" = some "assertion")
  let antecedent ← ex.parse? "antecedent" polarityTable
  let polarity ← ex.parse? "response" polarityTable
  let relative ← ex.parse? "relative" relativeTable
  let particle ← particleOf? ex
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
  particle : PolarityParticle
  conveys : Option Polarity
  judgment : Judgment
  deriving DecidableEq, Repr

def QuestionRow.ofDatum (ex : Datum) : Option QuestionRow := do
  let particle ← particleOf? ex
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
  | ⟨some (t, a), s, p, c, j⟩ => (j = .acceptable ↔ p.Usable (s / t) s) ∧ c = some (s * a)
  | ⟨none, _, _, _, j⟩ => j ≠ .acceptable

instance : DecidablePred QuestionRow.Predicted := fun r ↦ by
  obtain ⟨_ | ⟨t, a⟩, s, p, c, j⟩ := r <;> unfold QuestionRow.Predicted <;> infer_instance

-- (49), (53)
theorem questionRows_predicted : ∀ r ∈ questionRows, r.Predicted := by
  decide

end RoelofsenFarkas2015
