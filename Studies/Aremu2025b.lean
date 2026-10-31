module

public import Linglib.Core.Order.TreePath
public import Linglib.Data.Examples.Aremu2025b
public import Linglib.Fragments.Yoruba.Focus
public import Linglib.Fragments.Yoruba.Pronouns
public import Linglib.Semantics.Focus.Marking
public import Linglib.Syntax.Reflex
public import Linglib.Data.Examples.Readers

/-!
# Aremu (2025): the syntax of focus in Ìkálẹ̀

Ìkálẹ̀, a south-eastern dialect of Yorùbá, focuses a constituent in place with no marking, or
fronts it and closes the clause with *rín*: *Tolú Adé rí rín* 'Adé saw TOLÚ', against Standard
Yorùbá *ni* right after the focus. A focused subject must front and leaves the resumptive *ó*,
a focused verb phrase stays in place, and only a fronted focus is contrastive. Aremu takes *rín*
to head a head-final focus phrase whose specifier holds the fronted focus, so that it marks the
focus itself, against an antisymmetric analysis that pied-pipes a phrase containing the focus.

## Main definitions

* `Aremu2025b.Answer`: an answer by its focus and whether it fronts it.
* `Aremu2025b.Answer.reflexes`, `Aremu2025b.Answer.Licensed`: its overt marking, and the
  conditions on fronting.

## Implementation notes

Constituents are positions in the clause `[subject [verb object adjunct]]` with the containment
order on `TreePath`, as in `Aremu2025a`, which this file does not import: the two works appeared
a month apart and neither cites the other. The rows (2b), (16a) and (16b) are Standard Yorùbá.

## TODO

* Embedded focus, the island tests by which subject and object focus both move, and the
  exclusive particle *nùkàn*, which pied-pipes with an argument associate.

## References

* [aremu-2025b]
* [branan-erlewine-2023]
-/

@[expose] public section

namespace Aremu2025b

open Core.Order Reflex OrderDual

/-! ### Constituents -/

/-- The clause, the root of `[subject [verb object adjunct]]`. -/
def clause : TreePath := ⟨[]⟩

/-- The subject. -/
def subject : TreePath := ⟨[0]⟩

/-- The verb phrase. -/
def vp : TreePath := ⟨[1]⟩

/-- The verb. -/
def verb : TreePath := ⟨[1, 0]⟩

/-- The direct object. -/
def object : TreePath := ⟨[1, 1]⟩

/-- The adjunct. -/
def adjunct : TreePath := ⟨[1, 2]⟩

/-! ### Answers and their reflexes -/

/-- An answer records the focused constituent and whether it stays in place or is fronted. -/
structure Answer where
  focus : TreePath
  strategy : Focus.Strategy

namespace Answer

variable {a : Answer}

/-- The overt reflexes of an answer. In place there are none; a fronted focus is displaced and
marked by *rín*, and a fronted subject is resumed by *ó*. -/
def reflexes (a : Answer) : Finset (Reflex TreePathᵒᵈ) :=
  match a.strategy with
  | .inSitu => ∅
  | .exSitu => {.displacement (toDual a.focus), .morpheme (toDual a.focus) [.free Yoruba.rin.form]}
      ∪ if a.focus = subject then {.morpheme (toDual subject) [.free Yoruba.Pronouns.«ó».form]}
        else ∅

/-- *rín* heads the focus phrase whose specifier holds the fronted focus, so every reflex is
hosted by the focus itself. -/
theorem exactlyTargets_reflexes : ExactlyTargets a.reflexes (toDual a.focus) := by
  intro ρ hρ
  cases h : a.strategy <;> simp only [reflexes, h] at hρ
  · simp at hρ
  · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hρ
    obtain (rfl | rfl) | hρ := hρ
    · rfl
    · rfl
    · split_ifs at hρ with hs
      · rw [Finset.mem_singleton.1 hρ, hs]
        rfl
      · simp at hρ

/-- Fronted focus is contrastive and focus in place is new information. -/
def Contrastive (a : Answer) : Prop := a.strategy = .exSitu

instance : Decidable a.Contrastive := inferInstanceAs (Decidable (_ = _))

/-- A focused subject fronts, a focused verb phrase stays in place, and the focus is a proper
part of the clause. -/
def Licensed (a : Answer) : Prop :=
  clause < a.focus ∧ (a.focus = subject → a.strategy = .exSitu) ∧
    (a.focus = vp → a.strategy = .inSitu)

instance : Decidable a.Licensed := inferInstanceAs (Decidable (_ ∧ _))

end Answer

open Answer

/-- A focus in place has no reflex in any channel, as *Adé rí Tolú* 'Adé saw TOLÚ' has none. -/
theorem not_perceptible : ¬ Perceptible fun a : {a : Answer // a.Licensed} ↦ a.1.reflexes :=
  fun h ↦ Finset.not_nonempty_empty (h ⟨⟨object, .inSitu⟩, by decide⟩)

/-! ### The rows -/

/-- The positions the rows name. -/
def positions : List (String × TreePath) :=
  [("subject", subject), ("vp", vp), ("verb", verb), ("object", object), ("adjunct", adjunct)]

/-- The answer a row records, by its focus and whether it fronts it. -/
def Answer.ofRow? (r : Datum) : Option Answer :=
  (r.parse? "focus" positions).map fun focus ↦
    ⟨focus, if r.feature? "fronted" = none then .inSitu else .exSitu⟩

/-- A row carries *rín*, a word glossed as the focus marker. -/
def Marked (r : Datum) : Prop := (Yoruba.rin.form, "FOC") ∈ r.glossedTokens

instance (r : Datum) : Decidable (Marked r) := inferInstanceAs (Decidable (_ ∈ _))

/-- A row carries the resumptive *ó*. -/
def Resumed (r : Datum) : Prop := (Yoruba.Pronouns.«ó».form, "RP") ∈ r.glossedTokens

instance (r : Datum) : Decidable (Resumed r) := inferInstanceAs (Decidable (_ ∈ _))

/-- The model accepts a row when its answer is licensed, carries *rín* exactly when it fronts,
carries *ó* exactly when it fronts the subject, and is contrasted only when it is contrastive. -/
def Accepts (a : Answer) (r : Datum) : Prop :=
  a.Licensed ∧ (Marked r ↔ a.strategy = .exSitu) ∧
    (Resumed r ↔ a.strategy = .exSitu ∧ a.focus = subject) ∧
    (r.feature? "continuation" = some "contrastive" → a.Contrastive)

instance (a : Answer) (r : Datum) : Decidable (Accepts a r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The Ìkálẹ̀ rows. -/
def ikaleRows : List Datum := Examples.all.filter (·.language = "ikal1241")

/-- Every Ìkálẹ̀ row records an answer, which the model accepts exactly when the chapter judges
the row felicitous. -/
theorem judgedFelicitous_iff :
    ∀ r ∈ ikaleRows, ∃ a ∈ Answer.ofRow? r, (Accepts a r ↔ r.JudgedFelicitous) := by
  decide

/-- *rín* is the last word of every clause it marks, whatever has been fronted. -/
theorem rin_last :
    ∀ r ∈ ikaleRows, Marked r → r.feature? "continuation" = none →
      r.surfaceTokens.getLast? = some Yoruba.rin.form := by
  decide

/-- In the Standard Yorùbá (2b) *ni* follows the fronted *eku*. -/
theorem ni_second : Examples.ex_2b.surfaceTokens[1]? = some Yoruba.ni.form := by
  decide

/-- The person of a focused subject the row records, third unless it says otherwise. -/
def person (r : Datum) : Person :=
  (r.parse? "person" [("first", Person.first), ("second", .second)]).getD .third

/-- A fronted subject is resumed by the singular subject pronoun of its person ((10b), (16a),
(16b)). -/
theorem resumptive_mem :
    ∀ r ∈ [Examples.ex_10b, Examples.ex_16a, Examples.ex_16b],
      ∃ p ∈ Yoruba.Pronouns.subject (person r) .singular, p.form ∈ r.surfaceTokens := by
  decide

end Aremu2025b
