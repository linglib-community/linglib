/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Linearization.Spellout
public import Mathlib.Data.Finset.Union
public import Linglib.Syntax.Minimalist.Label.RaisingHead

/-!
# Citko and Gračanin-Yuksek (2020): Conjunction saves multiple sluicing: How *(and) why?

English cannot sluice two wh-phrases (*who what*), but it can sluice them coordinated (*who or
what*). Citko and Gračanin-Yuksek argue that a coordinated sluice is neither a multiple sluice nor
an elided coordinated wh-question. It coordinates two clauses, each with one fronted wh-phrase and
its own elided TP, and the second TP holds an E-type pronoun anaphoric to the first wh-phrase's
trace, which gives the sluice its it reading (*what John sang and where he sang it*). A coordinated
wh-question shares everything but its wh-phrases, so each wh-phrase stands in one conjunct and the
question has only the at-all reading. Its structure cannot underlie a sluice: the shared
complementizer would elide both TPs, and the second ellipsis would silence nothing new, which
economy bans.

## Main statements

* `csFromCWH_vacuous`: a coordinated sluice cannot have the structure of a coordinated
  wh-question, whose shared [E] complementizer would elide its second TP vacuously.
* `cs_noVacuousEllipsis`, `cs_itReading`: in the biclausal sluice each ellipsis silences a string
  of its own, and the E-type pronoun gives the it reading.

## Implementation notes

* A structure is a linearized syntactic object spelled out by `Linearization/Spellout.lean`: a token
  at two positions is shared and pronounced at its last occurrence, a fronted wh-phrase leaves a
  deleted copy, and the coordinator is left out, so a string is its conjuncts' words.
* The E-type pronoun of the second conjunct is a deleted copy of the first wh-phrase without an
  antecedent in its conjunct, Merchant's pronominal correlate of the wh-trace.

## TODO

* The paper excludes the sluice structure as a source for coordinated wh-questions by scope
  parallelism without the pronoun, and with it by the overt E-type pronoun's need for an unelided
  antecedent. Neither condition is stated here.
* Coordination of arguments, obligatorily transitive verbs and subject wh-phrases follows from the
  pronoun saturating the verb in the second conjunct; the selection check of
  `Label/Selection.lean` is undefined at the adjunction and specifier nodes involved.
* The independence of the two ellipses, which needs an overt pronoun when the second TP survives,
  and the absence of the clause-mate condition and of the category restriction of multiple
  sluicing.

## References

* [B. Citko and M. Gračanin-Yuksek, *Conjunction saves multiple sluicing: How \*(and) why?*
  (2020)][citko-gracanin-yuksek-2020]
* [J. Merchant, *E-type traces under sluicing* (1999)][merchant-1999]
* [J. Merchant, *The Syntax of Silence* (2001)][merchant-2001]
* [D. Fox, *Economy and Semantic Interpretation* (2000)][fox-2000]
-/

@[expose] public section

namespace CitkoGracaninYuksek2020

open Minimalist Minimalist.LinearizedSyntacticObject Core.Order

/-! ### The lexicon -/

/-- `tok` builds a token from a category, its selection, its form, and the wh and [E] features. -/
def tok (id : ℕ) (cat : Cat) (sel : SelStack := []) (phon : String := "") (wh : Bool := false)
    (ellipsis : Bool := false) : LexicalItem.Token :=
  ⟨LexicalItem.of cat sel phon wh ellipsis, id⟩

def what := tok 1 .D (phon := "what") (wh := true)
def «where» := tok 2 .P (phon := "where") (wh := true)
def john := tok 3 .D (phon := "John")
def T := tok 4 .T [.V]
def sang := tok 5 .V [.D] "sang"
/-- The null complementizer, the one bearing [E], and a second one bearing [E]. -/
def c := tok 6 .C [.T]
def cE := tok 7 .C [.T] (ellipsis := true)
def cE' := tok 8 .C [.T] (ellipsis := true)
/-- The tokens of a second, separately built clause. -/
def john' := tok 9 .D (phon := "John")
def T' := tok 10 .T [.V]
def sang' := tok 11 .V [.D] "sang"

/-! ### The structures -/

/-- `nonBulk c` is the structure of the coordinated wh-question (13b): the two CPs share their
complementizer `c`, subject, T and verb, and each holds one wh-phrase, *what* as the verb's object
in the first and *where* adjoined to the verb phrase in the second. -/
def nonBulk (c : LexicalItem.Token) : LinearizedSyntacticObject :=
  (what * (c * (john * (T * (sang * traceOf what))))) *
    («where» * (c * (john * (T * (traceOf «where» * (sang : LinearizedSyntacticObject))))))

/-- The coordinated wh-question (13b). -/
abbrev cwh := nonBulk c
/-- A coordinated sluice with the structure of the coordinated wh-question, its shared
complementizer bearing [E] ((14b), (69b)). -/
abbrev csFromCWH := nonBulk cE

/-- The coordinated sluice (70b) coordinates two clauses, each with its own [E] complementizer and
TP; the second TP holds the E-type pronoun, a deleted copy of *what*. -/
def cs : LinearizedSyntacticObject :=
  (what * (cE * (john * (T * (sang * traceOf what))))) *
    («where» * (cE' * (john' * (T' * (traceOf «where» * (sang' * traceOf what))))))

/-! ### Readings -/

/-- A coordination has the it reading when its second conjunct holds a deleted copy, without an
antecedent there, of a token pronounced in the first, which it reads as an E-type pronoun ((41),
(54)). -/
def ItReading (t : LinearizedSyntacticObject) : Prop :=
  ∃ x ∈ orphanTraces .raising t, (⟨[1]⟩ : TreePath) ≤ x.1 ∧
    ∃ p ∈ occurrences t x.2, (⟨[0]⟩ : TreePath) ≤ p

instance : DecidablePred ItReading := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-! ### Vacuous ellipsis -/

/-- The tokens of `t`, each once. -/
def tokens (t : LinearizedSyntacticObject) : Finset LexicalItem.Token :=
  ((tokenList t.val).map (·.2)).toFinset

/-- The pronounceable tokens the application of ellipsis at the domain `K` silences. -/
def silencedBy (t : LinearizedSyntacticObject) (K : TreePath) : Finset LexicalItem.Token :=
  (tokens t).filter fun s ↦ s.item.phonForm?.isSome ∧ (occurrences t s).any (decide <| K ≤ ·)

/-- The application at `K` is vacuous when the earlier applications already silenced every token
it silences. -/
def IsVacuous (t : LinearizedSyntacticObject) (K : TreePath) : Prop :=
  silencedBy t K ⊆ ((elidedDomains t).takeWhile (· ≠ K)).toFinset.biUnion (silencedBy t)

instance (t : LinearizedSyntacticObject) (K : TreePath) : Decidable (IsVacuous t K) :=
  inferInstanceAs (Decidable (silencedBy t K ⊆ _))

/-- Economy bans vacuous ellipsis, since an operation applies only when it affects pronunciation or
interpretation, as Fox's Scope Economy bans vacuous scope shifting, and ellipsis affects only
pronunciation. -/
def NoVacuousEllipsis (t : LinearizedSyntacticObject) : Prop :=
  ∀ K ∈ elidedDomains t, ¬ IsVacuous t K

instance (t : LinearizedSyntacticObject) : Decidable (NoVacuousEllipsis t) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-! ### Coordinated wh-questions and coordinated sluices -/

theorem cwh_pf : pfPhon cwh = ["what", "where", "John", "sang"] := by decide
theorem cs_pf : pfPhon cs = ["what", "where"] := by decide
theorem csFromCWH_pf : pfPhon csFromCWH = pfPhon cs := by decide

/-- Each wh-phrase of the coordinated wh-question is interpreted only in its own conjunct, so the
second conjunct's verb is intransitive: the at-all reading (12). -/
theorem cwh_atAll : orphanTraces .raising cwh = [] := by decide

/-- Built on the wh-question, a sluice would have the at-all reading coordinated sluices lack
(19). -/
theorem csFromCWH_not_itReading : ¬ ItReading csFromCWH := by decide

/-- The shared [E] complementizer elides both TPs, and the second deletion silences nothing the
first did not (69b). -/
theorem csFromCWH_vacuous : ¬ NoVacuousEllipsis csFromCWH := by decide

/-- In the biclausal sluice each TP dominates a string of its own, so neither ellipsis is vacuous
(70b). -/
theorem cs_noVacuousEllipsis : NoVacuousEllipsis cs := by decide

/-- The E-type pronoun gives the coordinated sluice the it reading (56). -/
theorem cs_itReading : ItReading cs := by decide

end CitkoGracaninYuksek2020
