module

public import Linglib.Syntax.Clause.Relative
public import Linglib.Syntax.Gender.Basic
public import Linglib.Syntax.Number.Basic
public import Linglib.Fragments.Arabic.ModernStandard.Case

/-!
# Modern Standard Arabic relative clauses

Modern Standard Arabic relative clauses are definite or indefinite with their antecedent
([ryding-2005] ch. 14, pp. 322–325). A definite clause is introduced by the definite relative
pronoun *alladhii*, which agrees with the antecedent in number and gender and, in the dual, in
case; an indefinite clause has no relative pronoun. In both, a relativized subject is left
unfilled, and the object of a verb or a preposition is resumed by a personal pronoun, the
*ʿaaʾid* 'returner'.

## Main declarations

* `Arabic.ModernStandard.relativePronoun`: the nine forms of the definite relative pronoun.
* `Arabic.ModernStandard.relativePronoun_ne_iff_dual`, `relativePronoun_inj`: only the dual
  distinguishes case, and every form marks number and gender.
* `Arabic.ModernStandard.relativePronoun_dual_syncretism`: the dual relative pronoun has the
  case syncretism of the dual declension.
* `Arabic.ModernStandard.relativizer`: the relativizer, the same after a definite and an
  indefinite antecedent.

## Implementation notes

The forms are Ryding's transliterations. One relativizer serves both antecedents, which differ
only in whether *alladhii* introduces the clause, since resumption occurs "in definite and
indefinite relative clauses" alike (p. 324). The relative pronoun agrees with the antecedent, not
with the relativized position, so a relativized subject is a gap whichever form the pronoun
takes.

Ryding states the resumptive rule for the object of a verb or a preposition (p. 324), which
covers the direct object, the indirect object, a second accusative or the object of *li-* or
*ʾilaa* (p. 70), the oblique, and the object of comparison, the object of the preposition *min*
'than' (p. 246, p. 378). The genitive is recorded with a resumptive on [keenan-comrie-1977]'s
Tables 1 and 2 (pp. 76, 93), whose Arabic rows, Classical Arabic in Table 1, agree with Ryding's
rule at every position the rule covers.

The free relatives with *maa* and *man* (§5, pp. 325–327) have no head noun and are not
recorded.

## TODO

Ryding does not treat relativization of a possessor; the genitive wants a page in a grammar of
Modern Standard Arabic.

## References

* [keenan-comrie-1977]
* [ryding-2005]
-/

@[expose] public section

namespace Arabic.ModernStandard

/-! ### The definite relative pronoun -/

/-- The definite relative pronoun, by the number and gender of its antecedent and by case
([ryding-2005] p. 322), with the feminine plural's variants *allaatii* and *allawaatii*; empty
outside the singular, dual and plural and the two genders. The plural is used only of human
referents (p. 323). -/
def relativePronoun : Number → Gender.Label → Case → List String
  | .singular, .masculine, _ => ["alladhii"]
  | .singular, .feminine, _ => ["allatii"]
  | .dual, .masculine, .nom => ["alladhaani"]
  | .dual, .masculine, _ => ["alladhayni"]
  | .dual, .feminine, .nom => ["allataani"]
  | .dual, .feminine, _ => ["allatayni"]
  | .plural, .masculine, _ => ["alladhiina"]
  | .plural, .feminine, _ => ["allaatii", "allawaatii"]
  | _, _, _ => []

/-- "Only the dual form of the definite relative pronoun shows difference in case" (p. 322). -/
theorem relativePronoun_ne_iff_dual :
    ∀ n ∈ [Number.singular, .dual, .plural], ∀ g ∈ [Gender.Label.masculine, .feminine],
      (∃ c c', relativePronoun n g c ≠ relativePronoun n g c') ↔ n = .dual := by
  decide

/-- The forms "are marked for number and gender" (p. 322): in each case, distinct numbers or
genders have distinct forms. -/
theorem relativePronoun_inj :
    ∀ c, ∀ n ∈ [Number.singular, .dual, .plural], ∀ n' ∈ [Number.singular, .dual, .plural],
      ∀ g ∈ [Gender.Label.masculine, .feminine], ∀ g' ∈ [Gender.Label.masculine, .feminine],
        relativePronoun n g c = relativePronoun n' g' c ↔ n = n' ∧ g = g' := by
  decide

/-- The dual relative pronoun merges the genitive and the accusative against the nominative, as
the dual declension does (p. 188). -/
theorem relativePronoun_dual_syncretism :
    ∀ g ∈ [Gender.Label.masculine, .feminine], ∀ s c c',
      relativePronoun .dual g c = relativePronoun .dual g c' ↔
        Declension.dual s c = Declension.dual s c' := by
  decide

/-! ### The relativizer -/

/-- The relativizer, introduced by the definite relative pronoun after a definite antecedent (§2,
p. 323) and by nothing after an indefinite one (§3, p. 324). A relativized subject is left
unfilled, the verb agreeing with it: *hiya llatii ʾarsal-at-i l-duktuur-a* 'she is the one who
sent the doctor' (p. 323), *fii ziyaarat-in li-dimashq-a ta-staghriq-u ʾusbuuʿ-an* 'on a visit
to Damascus [which] lasts a week' (p. 324).
In the dual the pronoun takes the antecedent's case, not the relativized position's: in
*li-l-zawj-ayni lladh-ayni ya-ntaZir-aani* 'for the couple who are awaiting' the antecedent is
genitive and the relativized position the subject (p. 323). Every lower position is resumed by
a personal pronoun, the *ʿaaʾid*, which "must be inserted" (p. 324): *al-kitaab-u lladhii
qaraʾ-naa-hu* 'the book that we read (it)' (p. 324), *wa-qaal-a fii muʾtamar-in SiHaafiyy-in
ʿaqad-a-hu ʾams-i* 'he said in a press conference [which] he held (it) yesterday' (p. 325). -/
def relativizer : Relativizer where
  placement := .postNominal
  realize
    | .subject => {.gap}
    | _ => {.resumptive}

end Arabic.ModernStandard
