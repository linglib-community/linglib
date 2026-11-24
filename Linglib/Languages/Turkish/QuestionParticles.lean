module

public import Linglib.Languages.Turkish.Morphotactics
public import Linglib.Syntax.Clause.Marker

/-!
# Turkish question particles

Turkish forms yes/no and alternative questions with the clitic *mI*, written as a separate word
and harmonizing as an I-type suffix does. It follows the questioned phrase, which is the
predicate when the whole proposition is questioned.

`mi` is the particle with its distribution over clause types. On a predicate *mI* stands among
the markers: `mi.Precedes` holds of the clitics among them other than the third-person plural,
and `mi.insert` puts *mI* immediately before the first marker it precedes
(`mi.insert_append_cons`), or after the last if it precedes none
(`mi.insert_of_forall_not_precedes`). So *Gidiyor musun?* 'Are you going?' contrasts with
*Gördün mü?* 'Did you see?'.

## Implementation notes

The distribution follows [turk-hirsch-2026], for whom *mI* is obligatory in polar questions, and
[goksel-kerslake-2005]. A quoted question keeps *mI* and so does a question under *diye*, while
a noun clause keeps it only after alternatives other than the negation of the predicate, so it
is optional in subordinated clauses. Echo questions, adverbial clauses after -DI and doubled
forms also take *mI*, so the constituent and declarative cells are not recorded. The colloquial
contractions of -(y)AcAK with a person marker are not represented, and the conditional copula
-(y)sA has no example with *mI*.

## References

* [goksel-kerslake-2005]
* [turk-hirsch-2026]
* [qing-uegaki-2025]
-/

@[expose] public section

namespace Turkish.QuestionParticles

/-- *mI*, the enclitic that forms yes/no and alternative questions. -/
def mi : Clause.Marker where
  morphs := [.encl "mI"]
  anchor := .focus .after
  distribution
    | (.polar, .matrix) | (.polar, .quotation) | (.alternative, .matrix) => some .obligatory
    | (.polar, .subordinated) | (.alternative, .subordinated) => some .optional
    | _ => none

open Turkish.Phonology in
/-- The segments of *mI*, which attach as a suffix does (§3.2). -/
def mi.suffix : Suffix := ⟨none, [m, I]⟩

/-- *mI* precedes the clitics among the predicate markers but the third-person plural -lAr
(§11.1.1.5). -/
def mi.Precedes (x : Σ σ, Verb.Exponent σ) : Prop := x.2.IsClitic ∧ ¬ x.2.IsThirdPlural

instance : DecidablePred mi.Precedes := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The forms of the markers of a predicate with *mI* before the first marker it precedes, or
after the last. -/
def mi.insert (xs : List (Σ σ, Verb.Exponent σ)) : List Suffix :=
  Verb.forms (xs.takeWhile (!mi.Precedes ·)) ++
    mi.suffix :: Verb.forms (xs.dropWhile (!mi.Precedes ·))

variable {x : Σ σ, Verb.Exponent σ} {xs pre post : List (Σ σ, Verb.Exponent σ)}

@[simp] theorem mi.insert_nil : mi.insert [] = [mi.suffix] := rfl

/-- *mI* immediately precedes the first marker it precedes (§11.1.1.5). -/
theorem mi.insert_append_cons (hpre : ∀ y ∈ pre, ¬ mi.Precedes y) (hx : mi.Precedes x) :
    mi.insert (pre ++ x :: post) = Verb.forms pre ++ mi.suffix :: Verb.forms (x :: post) := by
  have h : ∀ y ∈ pre, (!mi.Precedes y) = true := by simpa using hpre
  have hx : (!mi.Precedes x) = false := by simpa using hx
  rw [mi.insert, List.takeWhile_append_of_pos h, List.dropWhile_append_of_pos h,
    List.takeWhile_cons_of_neg (by simp [hx]), List.dropWhile_cons_of_neg (by simp [hx]),
    List.append_nil]

/-- *mI* follows the last marker of a predicate if it precedes none of them (§11.1.1.5). -/
theorem mi.insert_of_forall_not_precedes (h : ∀ y ∈ xs, ¬ mi.Precedes y) :
    mi.insert xs = Verb.forms xs ++ [mi.suffix] := by
  have h' : ∀ y ∈ xs, (!mi.Precedes y) = true := by simpa using h
  rw [mi.insert, List.takeWhile_eq_self_iff.2 h', List.dropWhile_eq_nil_iff.2 h']
  rfl

end Turkish.QuestionParticles
