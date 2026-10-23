module

public import Linglib.Syntax.WordOrder
public import Studies.BrueningAlKhalaf2020
public import Linglib.Data.Examples.Schwarzer2026
public import Linglib.Data.Experiments.Schwarzer2026
public import Linglib.Fragments.German.Verbs

/-!
# Schwarzer 2026: the law and order of selection-violating coordination

Schwarzer tests three analyses of a clause coordinated with a noun phrase where only the noun
phrase is selected on German, where complements follow the verb in a root clause and precede it in
an embedded one. The bottom-up analyses (Sag, Gazdar, Wasow and Weisler; Munn) make the first
conjunct prominent, so they check `List.take 1`; the linear closeness analysis (Bruening and Al
Khalaf; Bruening) and the temporal one (Kim and Lu) check the conjunct next to the verb,
`checkedOnce`. They part company before the verb, where only the bottom-up analyses admit the noun
phrase first. Experiment 1 shows that German allows the construction, and in Experiment 2 the noun
phrase first is preferred before the verb as much as after it, against both closeness analyses.

## Main results

* `exp1_predictions`, `exp1_rows`: the grammar admits every condition of Experiment 1 but a bare
  clause after a verb whose fragment entry takes none, and decides the paper's samples.
* `accounts_diverge_embedded`: the analyses differ before the verb and agree after it.
* `choices_refute_closeness`, `choices_match_structural`: the order preferred before the verb is
  one the closeness analyses exclude and the bottom-up ones admit.

## Implementation notes

* The verbs' c-selection is read off their entries in `Fragments/German/Verbs`. The results are
  `Data/Experiments/Schwarzer2026`; the mixed model and the logistic regression are not
  formalized, and the preferred order is the one chosen more often.
* The bottom-up analyses are given the noun-phrase shell over the clause of the 2020 study; their
  variant that licenses only the first conjunct makes the same predictions here.

## References

* [schwarzer-2026]
* [bruening-alkhalaf-2020]
* [bruening-2025]
* [kim-lu-2024]
* [munn-1993]
* [sag-etal-1985]
-/

@[expose] public section

namespace Schwarzer2026

open BrueningAlKhalaf2020
open PhraseStructure (Cat)
open PhraseStructure.Cat (N)

/-! ### The analyses -/

/-- In a German root declarative the verb in second position precedes its complements, the
configuration of (17). -/
abbrev rootPosition : HeadDirection := .headInitial

/-- In an embedded finite clause the verb is clause-final, so the coordination precedes it, the
configuration of (16). -/
abbrev embeddedPosition : HeadDirection := .headFinal

/-- `o.phrases` lists the categories of the conjuncts of a coordination in the order `o`. -/
def Order.phrases : Order → List Cat
  | .dpFirst => [N, .C]
  | .cpFirst => [.C, N]

/-- The bottom-up analyses admit the selected noun phrase first, after a verb that does not select
a clause, whatever the verb's position, (10b). -/
theorem structural_admits_iff (o : Order) :
    Admits (Licensed (List.take 1) {N}) o.phrases ↔ o = .dpFirst := by
  cases o <;> decide

/-- The closeness analyses admit the clause first before the verb, (10a). -/
theorem closeness_embedded_iff (o : Order) :
    Admits (Licensed (checkedOnce embeddedPosition) {N}) o.phrases ↔ o = .cpFirst := by
  cases o <;> decide

/-- The analyses differ before the verb only, which is what makes German the test case, since
after it the closeness analyses check the first conjunct too. -/
theorem accounts_diverge_embedded :
    (∃ o : Order, ¬ (Admits (Licensed (List.take 1) {N}) o.phrases ↔
        Admits (Licensed (checkedOnce embeddedPosition) {N}) o.phrases)) ∧
      checkedOnce rootPosition = List.take 1 :=
  ⟨⟨.dpFirst, by decide⟩, funext fun cs ↦ by cases cs <;> rfl⟩

/-! ### Experiment 1 -/

/-- `selects v` is the set of categories the verb `v` c-selects for its object, read off its
entry, which has a noun phrase if a frame takes one and a clause if a frame takes a
*dass*-clause. -/
def selects (v : German.Verb) : Finset Cat :=
  (if v.toVerb.TakesNominal then {N} else ∅) ∪ (if v.toVerb.TakesClausal then {.C} else ∅)

/-- `s.verbs` lists the four predicates of Experiment 1 that do or do not select a clause. -/
def Selection.verbs : Selection → List German.Verb
  | .yes => [German.Verbs.veranlassen, German.Verbs.vergessen, German.Verbs.erwarten,
      German.Verbs.beschliessen]
  | .no => [German.Verbs.beenden, German.Verbs.streichen, German.Verbs.uebereilen,
      German.Verbs.entwickeln]

/-- Each predicate's entry takes a noun phrase, and a clause exactly when the paper classes it as
selecting one (p. 7). -/
theorem selects_verbs (s : Selection) :
    ∀ v ∈ s.verbs, selects v = if s = .yes then {N, .C} else {N} := by
  cases s <;> decide

/-- `c.phrases` lists the categories of the conjuncts of a complement of Experiment 1, a bare
clause or a coordination with the noun phrase first. -/
def Complement.phrases : Complement → List Cat
  | .dass => [.C]
  | .coord => [N, .C]

/-- After the verb, the grammar admits every condition of Experiment 1 except a bare clause after a
non-selecting verb (table (14), p. 9). -/
theorem exp1_predictions (s : Selection) (c : Complement) : ∀ v ∈ s.verbs,
    (Admits (Licensed (checkedOnce rootPosition) (selects v)) c.phrases ↔
      c = .coord ∨ s = .yes) := by
  cases s <;> cases c <;> decide

/-- `entryOf form` is the fragment entry of the verb a row names. -/
def entryOf (form : String) : Option German.Verb :=
  German.Verbs.allVerbs.find? (·.form = form)

/-- `complementOf? e` is the complement of a row of Experiment 1. -/
def complementOf? (e : Datum) : Option Complement :=
  e.parse? "complement" [("dass", .dass), ("coord", .coord)]

/-- The grammar, with each verb's c-selection read off its entry, decides the paper's samples of
Experiment 1, (11) and (12). -/
theorem exp1_rows : ∀ e ∈ Examples.all, ∃ v ∈ (e.feature? "verb").bind entryOf,
    ∃ c ∈ complementOf? e,
      (Admits (Licensed (checkedOnce rootPosition) (selects v)) c.phrases ↔
        e.judgment = .acceptable) := by
  decide

theorem rows_selectsCP :
    ∀ e ∈ Examples.all, ∀ v ∈ (e.feature? "verb").bind entryOf,
      (e.feature? "selectsCP" = some "yes" ↔ v.toVerb.TakesClausal) := by
  decide

/-! ### Experiment 2 -/

/-- The head direction of a position of Experiment 2. -/
def Position.direction : Position → HeadDirection
  | .preverbal => embeddedPosition
  | .postverbal => rootPosition

/-- The order chosen more often in a position of Experiment 2. -/
def preferred (p : Position) : Order :=
  if (choices p .cpFirst).count < (choices p .dpFirst).count then .dpFirst else .cpFirst

/-- The noun phrase first is preferred in both positions, chosen 23 times of 30 (p. 13). -/
theorem preferred_eq (p : Position) : preferred p = .dpFirst := by
  cases p <;> decide

/-- **Experiment 2 refutes the linear and temporal closeness analyses**, since the order
preferred before the verb is one they exclude. -/
theorem choices_refute_closeness :
    ¬ Admits (Licensed (checkedOnce Position.preverbal.direction) {N})
      (preferred .preverbal).phrases := by
  rw [preferred_eq]
  decide

/-- The bottom-up analyses admit exactly the preferred order in both positions, which the squib
takes to support them only indirectly (p. 15). -/
theorem choices_match_structural (p : Position) (o : Order) :
    Admits (Licensed (List.take 1) {N}) o.phrases ↔ o = preferred p := by
  rw [preferred_eq, structural_admits_iff]

end Schwarzer2026
