module

public import Linglib.Core.Order.TreePath
public import Linglib.Data.Examples.Aremu2025a
public import Linglib.Fragments.Yoruba.Focus
public import Linglib.Fragments.Yoruba.Pronouns
public import Linglib.Fragments.Yoruba.Relativization
public import Linglib.Syntax.Reflex

/-!
# Aremu (2025): focus realization in Yorùbá

In Yorùbá a focus either stays in place, with no particle and no prosodic prominence, or a
constituent is fronted and followed by *ni*. The fronted constituent need not be the logical
focus, the part of the answer the question asks for: asked *what happened?*, *Tolú ni ó jẹ iṣu*
'TOLÚ ATE YAM' fronts the subject of a focused clause, which Branan and Erlewine call
anti-pied-piping, but a focused verb phrase cannot be answered by fronting its object. Aremu's
dissertation also shows that a focused subject must front, leaving a resumptive pronoun, and
that only a fronted focus is exhaustive.

## Main definitions

* `Aremu2025a.Answer`: an answer by its logical focus and the constituent it fronts.
* `Aremu2025a.Answer.reflexes`, `Aremu2025a.Answer.Licensed`: its overt marking, and the
  conditions on what it may front.

## Implementation notes

Constituents are positions in the clause `[subject [verb object adjunct]]`, ordered by
containment, the dual of the prefix order on `TreePath`. Resumptives are the subject pronouns of
`Yoruba.Pronouns`, in Awobuluyi's forms (*wọn* where (188a) prints *wọ́n*). Awobuluyi gives the
clause after *ni* the changes of a relative clause, which `relTi_realize_eq_vacated` checks.

## TODO

* Long-distance focus, the island tests separating base-generated subject focus from moved
  object focus, and the argument from extraction that the construction is mono-clausal.

## References

* [aremu-2025a]
* [awobuluyi-1978]
* [branan-erlewine-2023]
-/

@[expose] public section

namespace Aremu2025a

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

/-- An answer records its logical focus, the constituent the question asks for, the constituent
it fronts before *ni*, if any, and the person and number of the focus, which a resumptive agrees
with. -/
structure Answer where
  focus : TreePath
  fronted : Option TreePath
  person : Person := .third
  number : Number := .singular

variable {a : Answer} {m : TreePath}

/-- A fronted subject leaves a resumptive pronoun in its position, and anything else leaves a
gap. -/
def vacated (m : TreePath) : Relativization.NPRel := if m = subject then .resumptive else .gap

@[simp] theorem vacated_eq_resumptive : vacated m = .resumptive ↔ m = subject := by
  unfold vacated
  split_ifs with h <;> simp [h]

namespace Answer

/-- The resumptive of a fronted subject, at the subject position. -/
def resumptive (a : Answer) : Finset (Reflex TreePathᵒᵈ) :=
  ((Yoruba.Pronouns.subject a.person a.number).map fun r ↦
    .morpheme (toDual subject) [.free r.form]).toFinset

/-- The overt reflexes of an answer. In place there are none; a fronted constituent is displaced
and followed by *ni*, and a fronted subject is resumed. -/
def reflexes (a : Answer) : Finset (Reflex TreePathᵒᵈ) :=
  match a.fronted with
  | none => ∅
  | some m => {.displacement (toDual m), .morpheme (toDual m) [.free Yoruba.ni.form]} ∪
      if vacated m = .resumptive then a.resumptive else ∅

theorem reflexes_eq_empty (h : a.fronted = none) : a.reflexes = ∅ := by
  simp [reflexes, h]

theorem exactlyTargets_reflexes (h : a.fronted = some m) :
    ExactlyTargets a.reflexes (toDual m) := by
  intro ρ hρ
  simp only [reflexes, h, vacated_eq_resumptive, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at hρ
  obtain (rfl | rfl) | hρ := hρ
  · rfl
  · rfl
  · split_ifs at hρ with hm
    · simp only [resumptive, Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff] at hρ
      obtain ⟨r, -, rfl⟩ := hρ
      simp [hm]
    · simp at hρ

theorem reflexes_nonempty (h : a.fronted = some m) : a.reflexes.Nonempty :=
  ⟨.displacement (toDual m), by simp [reflexes, h]⟩

/-- An answer anti-pied-pipes its focus exactly when what it fronts lies properly inside it. -/
theorem antiPiedPipes_iff : AntiPiedPipes a.reflexes (toDual a.focus) ↔ ∃ m ∈ a.fronted,
    a.focus < m := by
  cases h : a.fronted with
  | none => simp [reflexes_eq_empty h, AntiPiedPipes]
  | some m =>
    rw [(exactlyTargets_reflexes h).antiPiedPipes_iff (reflexes_nonempty h)]
    simp

/-- A fronted focus is exhaustive and a focus in place is not. -/
def Exhaustive (a : Answer) : Prop := a.fronted ≠ none

instance : Decidable a.Exhaustive := inferInstanceAs (Decidable (_ ≠ _))

/-- A focused subject fronts, and a fronted constituent is a proper part of the clause that is
the focus itself or a part of a focused clause. -/
def Licensed (a : Answer) : Prop :=
  (a.focus = subject → a.fronted = some subject) ∧
    ∀ m ∈ a.fronted, clause < m ∧ (m = a.focus ∨ a.focus = clause)

instance : Decidable a.Licensed := inferInstanceAs (Decidable (_ ∧ _))

/-- Only a focused clause is marked on a proper part. -/
theorem focus_eq_clause_of_antiPiedPipes (h : a.Licensed)
    (hap : AntiPiedPipes a.reflexes (toDual a.focus)) : a.focus = clause := by
  obtain ⟨m, hm, hlt⟩ := antiPiedPipes_iff.1 hap
  rcases (h.2 m hm).2 with rfl | h
  · exact absurd hlt (lt_irrefl _)
  · exact h

end Answer

open Answer

theorem antiPiedPipes_clause :
    ({ focus := clause, fronted := some subject } : Answer).Licensed ∧
      AntiPiedPipes ({ focus := clause, fronted := some subject } : Answer).reflexes
        (toDual clause) :=
  ⟨by decide, antiPiedPipes_iff.2 ⟨subject, rfl, by decide⟩⟩

theorem not_antiPiedPipes_vp (h : a.Licensed) (hvp : a.focus = vp) :
    ¬ AntiPiedPipes a.reflexes (toDual a.focus) :=
  fun hap ↦ absurd ((focus_eq_clause_of_antiPiedPipes h hap).symm.trans hvp) (by decide)

theorem not_licensed_vp_object :
    ¬ ({ focus := vp, fronted := some object } : Answer).Licensed := by
  decide

theorem not_licensed_subject_inSitu :
    ¬ ({ focus := subject, fronted := none } : Answer).Licensed := by
  decide

/-- A focus in place has no reflex in any channel, as *Adé ra bàtà* 'Adé bought A SHOE' has
neither particle nor prominence. -/
theorem not_perceptible : ¬ Perceptible fun a : {a : Answer // a.Licensed} ↦ a.1.reflexes :=
  fun h ↦ Finset.not_nonempty_empty (h ⟨{ focus := object, fronted := none }, by decide⟩)

/-! ### Relativization -/

/-- The relativizable position of a constituent, the adjunct an oblique. -/
def relativePosition (m : TreePath) : Option Relativization.Position :=
  if m = subject then some .subject
  else if m = object then some .directObject
  else if m = adjunct then some .oblique
  else none

/-- A fronted subject is resumed and a fronted object or adjunct leaves a gap, as relativization
with *tí* treats them, which Awobuluyi's grammar gives to the clause after *ni*. -/
theorem relTi_realize_eq_vacated {p : Relativization.Position}
    (h : relativePosition m = some p) : Yoruba.relTi.realize p = {vacated m} := by
  unfold relativePosition at h
  split_ifs at h with h₁ h₂ h₃ <;> cases h <;> subst_vars <;> decide

/-! ### The rows -/

/-- The positions the rows name. -/
def positions : List (String × TreePath) :=
  [("clause", clause), ("subject", subject), ("vp", vp), ("verb", verb), ("object", object),
    ("adjunct", adjunct)]

/-- The answer a row records, by its focus, what it fronts and the number of the focus. -/
def Answer.ofRow? (r : Datum) : Option Answer :=
  (r.parse? "focus" positions).map fun focus ↦
    { focus, fronted := r.parse? "fronted" positions
      number := (r.parse? "number" [("plural", Number.plural)]).getD .singular }

/-- A row carries *ni*, a word glossed as the focus marker. -/
def Marked (r : Datum) : Prop := (Yoruba.ni.form, "FOC") ∈ r.glossedTokens

instance (r : Datum) : Decidable (Marked r) := inferInstanceAs (Decidable (_ ∈ _))

/-- The model accepts a row when its answer is licensed, carries *ni* exactly when it fronts, and
is followed by an additive only when it is not exhaustive. -/
def Accepts (a : Answer) (r : Datum) : Prop :=
  a.Licensed ∧ (Marked r ↔ a.fronted ≠ none) ∧
    (r.feature? "continuation" = some "additive" → ¬ a.Exhaustive)

instance (a : Answer) (r : Datum) : Decidable (Accepts a r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Every row records an answer, which the model accepts exactly when the chapter judges the row
felicitous. -/
theorem judgedFelicitous_iff :
    ∀ r ∈ Examples.all, ∃ a ∈ Answer.ofRow? r, (Accepts a r ↔ r.JudgedFelicitous) := by
  decide

end Aremu2025a
