module

public import Linglib.Syntax.Negation
public import Linglib.Fragments.Arabic.ModernStandard.Verbs

/-!
# Modern Standard Arabic negation

Modern Standard Arabic negates a verb with a particle chosen by tense: *laa* for the present, *lam*
for the past with the verb in the jussive, and *lan* for the future with the verb in the
subjunctive. The particle *maa* negates a verb that keeps its own tense. The verb *lays-a* 'not
be' takes the person markers of the past tense but negates the present, and gives a verbless
clause a finite verb whose predicate is in the accusative.

## Main definitions

* `laa`, `lam`, `lan`, `maa`: the negative particles.
* `laysa`, `laysaForms`: the negative verb *lays-a* and its forms by person, number and
  gender.

## Implementation notes

Benmamoun's verbal pairs and Ryding's equational pairs are rows of `Data.Examples.Benmamoun2000` and
`Data.Examples.Ryding2005`. Ryding gives *maa* only with a past-tense verb and finds it rare in
writing. Benmamoun also gives it with a present-tense verb, and gives *lays-a* negating a
present-tense verbal clause in free variation with *laa*.

## TODO

Benmamoun derives the distribution of the negatives from a single negative head: *lam* and *lan*
are *laa* carrying past and future tense, and *lays-a* is *laa* carrying agreement. That analysis
belongs in a study, which would also check that each negative equational row of Ryding's begins
with a form of `laysaForms`. An imperfective paradigm with its moods would let the moods the
particles govern be read off the verb forms.

## References

* [benmamoun-2000]
* [ryding-2005]
-/

@[expose] public section

open Morphology Negation

namespace Arabic.ModernStandard.Negation

/-- The particle *laa* negates a present-tense verb, which stays in the indicative
([ryding-2005] p. 644). It also negates the second person of the jussive in a prohibition
(p. 645) and a noun in categorical negation (pp. 645–646). -/
def laa : Marker := { pieces := [[.free "laa"]] }

/-- The particle *lam* negates the past, with the verb in the jussive ([ryding-2005] p. 647). -/
def lam : Marker := { pieces := [[.free "lam"]] }

/-- The particle *lan* negates the future, with the verb in the subjunctive ([ryding-2005]
p. 648). -/
def lan : Marker := { pieces := [[.free "lan"]] }

/-- The particle *maa* negates a verb that keeps its tense, a past ([ryding-2005] p. 647) or a
present ([benmamoun-2000] (41), pp. 107–108). -/
def maa : Marker := { pieces := [[.free "maa"]] }

/-- The negative verb *lays-a* 'not be', cited by its long stem ([ryding-2005] p. 641). -/
def laysa : Marker := { pieces := [[.root "lays"]] }

/-- The stem *lays-a* takes before a person marker is *las-* when the marker starts with a
consonant and *lays-* when it starts with a vowel ([ryding-2005] p. 641). -/
def laysaStem (s : Morph) : Morph :=
  if s.form.front ∈ ['a', 'i', 'u'] then .root "lays" else .root "las"

/-- The forms of *lays-a* are its stem with the person markers of the past tense
([ryding-2005] p. 641). -/
def laysaForms : Agreement.Paradigm (List Morph) :=
  pastSuffix.map fun (c, s) ↦ (c, [laysaStem s, s])

theorem cells_laysaForms : laysaForms.cells = pastSuffix.cells := by
  simp [laysaForms, Agreement.Paradigm.cells]

/-- *lays-a* conjugates as in Ryding's chart (p. 642) and in [benmamoun-2000]'s (25) (p. 102),
which misprints *las-ti* as *lasti-ti*. It has no first person dual. -/
example :
    laysaForms.map (·.2) =
      [[.root "las", .suff "tu"], [.root "las", .suff "ta"], [.root "las", .suff "ti"],
       [.root "lays", .suff "a"], [.root "lays", .suff "at"], [.root "las", .suff "tumaa"],
       [.root "lays", .suff "aa"], [.root "lays", .suff "ataa"], [.root "las", .suff "naa"],
       [.root "las", .suff "tum"], [.root "las", .suff "tunna"], [.root "lays", .suff "uu"],
       [.root "las", .suff "na"]] ∧
    laysaForms.realize (.personNumber .first .dual) = none := by
  decide

end Arabic.ModernStandard.Negation
