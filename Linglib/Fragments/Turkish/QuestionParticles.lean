module

public import Linglib.Fragments.Turkish.Morphotactics
public import Linglib.Syntax.Category.Particle.Basic

/-!
# Turkish question particles

Turkish forms yes/no and alternative questions with the clitic *mI*, written as a separate word
and harmonizing as an I-type suffix does, as *mı*, *mi*, *mu* or *mü* (§3.2, §11.1.1.5). It
follows the questioned phrase, which is the predicate when the whole proposition is questioned,
and each alternative of an alternative question (§19.1). On the predicate it stands among the
markers, immediately before the first clitic, a copular marker, -DIr or a group-2 person marker
other than the third-person plural, and after every other marker, so that *Gidiyor musun?*
'Are you going?' contrasts with *Gördün mü?* 'Did you see?'. The markers after it attach to it,
as in *bil-iyor mu-ydu-nuz* (§6.3 (5)).

## Main definitions

* `Turkish.QuestionParticles.mi`: the particle.
* `mi.suffix`, `mi.Precedes`, `mi.insert`: the segments of *mI*, the markers it precedes, and
  the markers of a predicate with *mI* among them.

## Main results

* `mi.insert_append_cons`, `mi.insert_of_forall_not_precedes`: *mI* immediately precedes the
  first marker it precedes, and follows the last marker if it precedes none.

## Implementation notes

The distribution follows Türk and Hirsch, for whom *mI* is obligatory in polar questions, and
the grammar. A quoted question keeps it (§24.3.1 (16)), and so does a question under *diye*, as
in Türk and Hirsch's (14) and Qing et al.'s examples, while a noun clause expresses 'whether (or
not)' with -(y)Ip…-mA and keeps *mI* only after alternatives other than the negation of the
predicate (§24.4.3.2). Echo questions (§19.3), adverbial clauses after -DI and doubled forms
(§11.1.1.5) also take *mI*, so the constituent and declarative cells are not recorded. The
colloquial contractions of -(y)AcAK with a person marker (§11.1.1.5 (e)) are not represented,
and the conditional copula -(y)sA has no example with *mI*.

## References

* [goksel-kerslake-2005]
* [turk-hirsch-2026]
* [qing-uegaki-2025]
-/

@[expose] public section

namespace Turkish.QuestionParticles

/-- *mI*, the enclitic that forms yes/no and alternative questions. -/
def mi : Particle where
  form := "mI"
  position := some .postHost
  distribution
    | .polar, .matrix | .polar, .quotation | .alternative, .matrix => some .obligatory
    | .polar, .subordinated | .alternative, .subordinated => some .optional
    | _, _ => none

open Turkish.Phonology in
/-- The segments of *mI*, which attach as a suffix does (§3.2). -/
def mi.suffix : Suffix := ⟨none, [m, I]⟩

/-- *mI* precedes the clitics among the predicate markers but the third-person plural -lAr
(§11.1.1.5). -/
def mi.Precedes (x : Σ σ, Verb.Exponent σ) : Prop :=
  x.2.IsClitic ∧ x ≠ ⟨_, .person .two (.personNumber .third .plural)⟩

instance : DecidablePred mi.Precedes := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The forms of the markers of a predicate with *mI* before the first marker it precedes, or
after the last. -/
def mi.insert : List (Σ σ, Verb.Exponent σ) → List Suffix
  | [] => [mi.suffix]
  | x :: xs =>
    if mi.Precedes x then mi.suffix :: (x :: xs).map (·.2.form) else x.2.form :: mi.insert xs

variable {x : Σ σ, Verb.Exponent σ} {xs pre post : List (Σ σ, Verb.Exponent σ)}

@[simp] theorem mi.insert_nil : mi.insert [] = [mi.suffix] := rfl

@[simp] theorem mi.insert_cons_of_precedes (h : mi.Precedes x) :
    mi.insert (x :: xs) = mi.suffix :: (x :: xs).map (·.2.form) :=
  ite_eq_left h

@[simp] theorem mi.insert_cons_of_not_precedes (h : ¬ mi.Precedes x) :
    mi.insert (x :: xs) = x.2.form :: mi.insert xs :=
  ite_eq_right h

/-- *mI* immediately precedes the first marker it precedes (§11.1.1.5). -/
theorem mi.insert_append_cons (hpre : ∀ y ∈ pre, ¬ mi.Precedes y) (hx : mi.Precedes x) :
    mi.insert (pre ++ x :: post) =
      pre.map (·.2.form) ++ mi.suffix :: (x :: post).map (·.2.form) := by
  induction pre with
  | nil => exact mi.insert_cons_of_precedes hx
  | cons y pre ih =>
    rw [List.forall_mem_cons] at hpre
    rw [List.cons_append, mi.insert_cons_of_not_precedes hpre.1, ih hpre.2]
    rfl

/-- *mI* follows the last marker of a predicate if it precedes none of them (§11.1.1.5). -/
theorem mi.insert_of_forall_not_precedes (h : ∀ y ∈ xs, ¬ mi.Precedes y) :
    mi.insert xs = xs.map (·.2.form) ++ [mi.suffix] := by
  induction xs with
  | nil => rfl
  | cons y xs ih =>
    rw [List.forall_mem_cons] at h
    rw [mi.insert_cons_of_not_precedes h.1, ih h.2]
    rfl

end Turkish.QuestionParticles
