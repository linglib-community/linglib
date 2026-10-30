module

public import Linglib.Semantics.Reference.ChoiceFunction
public import Linglib.Fragments.Akan.Determiners
public import Linglib.Data.Examples.Owusu2022
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype

/-!
# Owusu (2022): the Akan indefinite *bí*

Owusu analyses the Akan indefinite *bí* as a choice function skolemized to a situation. Her
entry (67) maps a situation `s` and a property `P` to `f s (P s)`, presupposing that `f s` is a
choice function. The function is free, fixed by the context as in Kratzer's analysis of *a
certain*, and never existentially closed. A *bí* phrase scopes only above negation and, as a
subject, above *biara* 'every', but as an object it also scopes below *biara*, while a bare noun
scopes only below either. Owusu argues that closing the function freely, after Reinhart and
Winter, derives the narrow reading under negation that *bí* lacks; that closing it only at the
top, after Matthewson, derives no narrow reading of a conditional; and that the reading below
*biara* is functional, the function's individual index being bound by the quantifier.

## Implementation notes

* The presupposition of (67) is the type of `f`, a family `S → ChoiceFunction E`.
* The situation index and the individual index of (67) are taken one at a time, as the index
  type `S`.
* A construal holds in some context when some choice function makes it true.
* An example counts as a *bí* example when one of its words is the form of
  `Akan.Determiners.bi`.
* Owusu takes the world variable from a 2019 manuscript by Mirrazi; [mirrazi-2024] develops
  the analysis from the same example.

## TODO

* The weak crossover asymmetry of (54)–(56), after [chierchia-2001]: an index bound by
  *biara* in subject position would cross over it. It needs binding over syntax trees.
* The world variable of §3.3.3 in conditionals, (66), and under *pɛ* 'want', (65), with the
  existential entailment and substitution diagnostics of §3.2.3. The bound construal of (66b)
  is entailed by the narrow reading but is weaker than it unless the function picks an elder who
  comes wherever one does; the chapter does not discuss this.
* §3.4: *bí nó*, *nó bí*, and the ignorance inference of *bí*.
* The second chapter's analysis of *nó*.

## References

* [owusu-2022]
* [kratzer-1998-pseudoscope]
* [reinhart-1997]
* [winter-1997]
* [matthewson-1999]
* [chierchia-2001]
* [mirrazi-2024]
-/

@[expose] public section

namespace Owusu2022

open Quantifier

variable {S E ι : Type*}

/-! ### Negation -/

/-- Closing the choice function below negation, as free existential closure must allow for
(51), gives the narrow reading (50). -/
theorem closure_below_negation_iff {N VP : E → Prop} (hN : ∃ x, N x) :
    (¬ ∃ f : ChoiceFunction E, VP (f N)) ↔ ¬ Det.some N VP :=
  not_congr (ChoiceFunction.exists_apply_iff_some hN VP)

/-- Under negation, the free function of (67) gives the narrow reading for every predicate iff its
pick is the restrictor's only member at the situation. -/
theorem negation_narrow_iff (f : S → ChoiceFunction E) {s : S} {P : S → E → Prop}
    (hP : ∃ x, P s x) :
    (∀ VP : E → Prop, ¬ VP (f s (P s)) ↔ ¬ Det.some (P s) VP) ↔ ∀ x, P s x → x = f s (P s) :=
  (forall_congr' fun _ ↦ not_iff_not).trans ((f s).forall_apply_iff_some_iff hP)

/-! ### Conditionals -/

/-- Closing the choice function above a conditional gives the wide reading of (60). -/
theorem closure_above_conditional_iff {N A : E → Prop} {p : Prop} (hN : ∃ x, N x) :
    (∃ f : ChoiceFunction E, A (f N) → p) ↔ ∃ x, N x ∧ (A x → p) :=
  ChoiceFunction.exists_apply_iff_some hN fun x ↦ A x → p

/-! ### *biara* -/

section Every

variable {B : E → Prop} {R : ι → E → Prop}

/-- With the individual index free, some function makes (55a) true exactly when one book was
read by every woman. -/
theorem wide_iff (hB : ∃ x, B x) :
    (∃ f : ChoiceFunction E, ∀ z, R z (f B)) ↔ Det.some B fun x ↦ ∀ z, R z x :=
  ChoiceFunction.exists_apply_iff_some hB fun x ↦ ∀ z, R z x

/-- With the individual index bound by *biara*, some function makes (55b) true iff every woman read
a book (24). -/
theorem functional_iff (hB : ∃ x, B x) :
    (∃ F : ι → ChoiceFunction E, ∀ z, R z (F z B)) ↔ ∀ z, Det.some B (R z) :=
  ChoiceFunction.exists_pi_apply_iff (fun _ ↦ hB) R

end Every

/-! ### The scenario (57)–(58) -/

section DownwardEntailing

variable {Wrote Submitted : ι → E → Prop}

/-- With the index free, some function makes (57a) true iff every student wrote a paper they did not
submit, given distinct papers. -/
theorem ex57_free_iff [Nonempty E] (hW : ∀ x, ∃ y, Wrote x y)
    (hinj : Function.Injective Wrote) :
    (∃ f : ChoiceFunction E, ∀ x, ¬ Submitted x (f (Wrote x))) ↔
      ∀ x, Det.some (Wrote x) (¬ Submitted x ·) :=
  ChoiceFunction.exists_forall_apply_iff_of_injective hinj hW fun x y ↦ ¬ Submitted x y

/-- With the index bound by *biara*, some function makes (57b) true exactly when every student
wrote a paper they did not submit. -/
theorem ex57_bound_iff (hW : ∀ x, ∃ y, Wrote x y) :
    (∃ F : ι → ChoiceFunction E, ∀ x, ¬ Submitted x (F x (Wrote x))) ↔
      ∀ x, Det.some (Wrote x) (¬ Submitted x ·) :=
  ChoiceFunction.exists_pi_apply_iff hW fun x y ↦ ¬ Submitted x y

end DownwardEntailing

namespace Scenario58

/-- The students of (58) are Alan, Bob and Carl. -/
inductive Student where
  | alan
  | bob
  | carl
  deriving DecidableEq, Fintype, Inhabited

/-- Each student has three papers. -/
abbrev Paper := Student × Fin 3

/-- A student wrote their own three papers. -/
def Wrote (x : Student) (p : Paper) : Prop := p.1 = x

/-- Each student submitted two of their papers, all but the last. -/
def Submitted (x : Student) (p : Paper) : Prop := p.1 = x ∧ p.2 ≠ 2

instance : DecidableRel Wrote := fun _ _ ↦ inferInstanceAs (Decidable (_ = _))

instance : DecidableRel Submitted := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

private theorem wrote_nonempty (x : Student) : ∃ p, Wrote x p := ⟨(x, 0), rfl⟩

private theorem wrote_injective : Function.Injective Wrote :=
  fun x _ h ↦ (congrFun h (x, 0)).mp rfl

private theorem kept : ∀ x, Det.some (Wrote x) (¬ Submitted x ·) :=
  fun x ↦ ⟨(x, 2), rfl, fun h ↦ h.2 rfl⟩

/-- In (58), some function makes (57a) true. -/
theorem free : ∃ f : ChoiceFunction Paper, ∀ x, ¬ Submitted x (f (Wrote x)) :=
  (ex57_free_iff wrote_nonempty wrote_injective).mpr kept

/-- In (58), some function makes (57b) true. -/
theorem bound :
    ∃ F : Student → ChoiceFunction Paper, ∀ x, ¬ Submitted x (F x (Wrote x)) :=
  (ex57_bound_iff wrote_nonempty).mpr kept

/-- In (58) the narrow reading of (57), that no student submitted any paper they wrote, is
false. -/
theorem not_narrow : ¬ ∀ x, ¬ Det.some (Wrote x) (Submitted x) :=
  fun h ↦ h .alan ⟨(.alan, 0), rfl, rfl, by decide⟩

end Scenario58

/-! ### The examples -/

/-- Under negation no *bí* example has the narrow reading, (21), (22) and (57). -/
theorem bi_not_narrow_under_negation :
    ∀ e ∈ Examples.all, Akan.Determiners.bi.form ∈ e.surfaceTokens →
      e.feature? "operator" = some "negation" →
      e.readings.lookup "narrow" ≠ some .acceptable := by
  decide

/-- Under negation the bare examples have the narrow reading and not the wide one, (29) and
(30). -/
theorem bare_narrow_under_negation :
    ∀ e ∈ Examples.all, Akan.Determiners.bi.form ∉ e.surfaceTokens →
      e.feature? "operator" = some "negation" →
      e.readings.lookup "narrow" = some .acceptable ∧
        e.readings.lookup "wide" ≠ some .acceptable := by
  decide

/-- Under *biara* a *bí* example has the narrow reading exactly when it is the object, (23)
and (24). -/
theorem bi_narrow_under_every_iff :
    ∀ e ∈ Examples.all, Akan.Determiners.bi.form ∈ e.surfaceTokens →
      e.feature? "operator" = some "every" →
      (e.readings.lookup "narrow" = some .acceptable ↔ e.feature? "position" = some "object") := by
  decide

/-- Under *biara* the bare examples have only the narrow reading, (31) and (32). -/
theorem bare_narrow_under_every :
    ∀ e ∈ Examples.all, Akan.Determiners.bi.form ∉ e.surfaceTokens →
      e.feature? "operator" = some "every" →
      e.readings.lookup "narrow" = some .acceptable ∧
        e.readings.lookup "wide" = some .unacceptable := by
  decide

end Owusu2022
