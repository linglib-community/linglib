module

public import Linglib.Morphology.DistributedMorphology.Gender
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Data.UD.Features
public import Linglib.Data.Examples.Kramer2015
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Kramer (2015): The Morphosyntax of Gender

This file formalizes the book's account of nominals with more than one n. Kramer's Highest Gender
Hypothesis says that such a nominal [agrees as its highest n would over a bare
root](##Kramer2015.highestGender). She derives it from cyclicity: each n is a cyclic head that
sends the nPs below it to spell-out, so a gender probe above the nominal searches its last cycle
alone. On a hierarchical alternative the probe searches down for the highest n bearing a gender.
The two [differ exactly where the cyclic probe fails above a gendered
n](##Kramer2015.cyclicGender_ne_hierarchicalGender_iff), as [when a plain n tops a gendered
one](##Kramer2015.plain_over_gendered). A failed probe is spelled out by the Vocabulary Item that
mentions no gender, the default gender of the language, and [the nominals of the chapter show that
gender](##Kramer2015.cyclicGender_rows) where the analyses part, as in Amharic *ɨnnat-ɨnnät*
'motherhood', masculine, and German *Städt-chen* 'little town', neuter. A diminutive that keeps
the gender of its base [is not an n](##Kramer2015.cyclicGender_concat_dim).

## Implementation notes

* A head is a categorizer or a diminutive head adjoined to the nominal. The cyclic heads are the
  category-defining ones, `Minimalist.Cat.IsCategorizer`, and the diminutive head is neither
  cyclic nor gendered.
* A row lists the heads of its nominal innermost first, as the book's trees give them; the Spanish
  base nouns have the n the book's analysis of Spanish assigns them.
* The gender a target shows is the exponent of the features its probe copied. The vocabularies
  mention [±FEM] alone, for the languages of the rows.

## TODO

* The book's sketch of Spanish declension class, a Theme node inserted at n by rules ordered by
  specificity, is not formalized.

## References

* [kramer-2015]
-/

@[expose] public section

namespace Kramer2015

open DistributedMorphology

/-- A head of a nominal, a categorizer or a diminutive head adjoined to the nominal. -/
inductive Head where
  | cat (h : Categorizer)
  | dim
  deriving DecidableEq

/-- A head is cyclic when it is a category-defining head, n, v or a; the adjoined diminutive head
is not. -/
def Head.Cyclic : Head → Prop
  | .cat h => h.cat.IsCategorizer
  | .dim => False

instance : DecidablePred Head.Cyclic
  | .cat h => inferInstanceAs (Decidable h.cat.IsCategorizer)
  | .dim => isFalse id

/-- The gender feature a probe copies from a head, if the head bears one. -/
def Head.gender : Head → Option GenderValue
  | .cat h => h.gender.map (·.val)
  | .dim => none

/-- The gender feature a probe above the nominal copies on the cyclicity analysis, where it
searches the last cycle. -/
def cyclicGender (s : ComplexHead Root Head) : Option GenderValue :=
  agreeingGender Head.gender (s.lastCycle Head.Cyclic)

/-- The gender feature a probe above the nominal copies on the hierarchical analysis, where it
searches every head from the top. -/
def hierarchicalGender (s : ComplexHead Root Head) : Option GenderValue :=
  agreeingGender Head.gender s.heads.reverse

variable (r r' : Root) (hs : List Head) (s : ComplexHead Root Head)

/-- The Highest Gender Hypothesis (32): a nominal agrees as its highest n would over a bare
root. -/
theorem highestGender (h : Categorizer) :
    cyclicGender ⟨r, hs ++ [.cat h]⟩ = cyclicGender ⟨r', [.cat h]⟩ :=
  have hc : Head.Cyclic (.cat h) := h.isCategorizer
  (agreeingGender_lastCycle_concat_of_cyclic hc).trans
    (agreeingGender_lastCycle_concat_of_cyclic (hs := []) hc).symm

/-- The two analyses differ exactly when the cyclic probe fails over a nominal one of whose heads
bears a gender. -/
theorem cyclicGender_ne_hierarchicalGender_iff :
    cyclicGender s ≠ hierarchicalGender s ↔
      cyclicGender s = none ∧ ∃ h ∈ s.heads, h.gender.isSome :=
  agreeingGender_lastCycle_ne_iff

/-- The predictions (19) for the structure (18): over a plain n that tops an n of gender `v`, the
cyclic probe fails and the hierarchical probe copies `v`. -/
theorem plain_over_gendered (i : Minimalist.Interpretability) (v : GenderValue) :
    cyclicGender ⟨r, hs ++ [.cat (.gendered i v), .cat .n_plain]⟩ = none ∧
      hierarchicalGender ⟨r, hs ++ [.cat (.gendered i v), .cat .n_plain]⟩ = some v := by
  refine ⟨?_, by simp [hierarchicalGender, Head.gender, Categorizer.gendered,
    Categorizer.n_plain]⟩
  rw [List.append_cons]
  exact agreeingGender_lastCycle_concat_of_cyclic (h := Head.cat .n_plain) trivial

/-- A diminutive head that is not an n leaves the gender of the nominal it adjoins to. -/
theorem cyclicGender_concat_dim : cyclicGender ⟨r, hs ++ [.dim]⟩ = cyclicGender ⟨r, hs⟩ :=
  agreeingGender_lastCycle_concat_of_not_cyclic id rfl

/-! ### The gender agreement shows -/

/-- The gender forms of an agreeing target in a language whose masculine is the default, as in
Amharic, Somali and Spanish. -/
def masculineDefault : List (VocabularyItem GenderValue UD.Gender) :=
  [{⟨.fem, .pos⟩} ⟷ .Fem, ∅ ⟷ .Masc]

/-- The gender forms of an agreeing target in a language whose neuter is the default, as in
German and Serbian-Croatian. -/
def neuterDefault : List (VocabularyItem GenderValue UD.Gender) :=
  [{⟨.fem, .pos⟩} ⟷ .Fem, {⟨.fem, .neg⟩} ⟷ .Masc, ∅ ⟷ .Neut]

/-- The gender a target shows when its probe has copied `v`, by the Subset Principle. -/
def shown (vocabulary : List (VocabularyItem GenderValue UD.Gender)) (v : Option GenderValue) :
    Option UD.Gender :=
  subsetPrinciple vocabulary (v.toFinset : Finset GenderValue)

/-- The agreement vocabulary of each language of the rows. -/
def vocabularies : List (Glottocode × List (VocabularyItem GenderValue UD.Gender)) :=
  [(.amharic, masculineDefault), (.somali, masculineDefault), (.spanish, masculineDefault),
    (.german, neuterDefault), (.serbianCroatianBosnian, neuterDefault)]

/-- The heads the rows name. -/
def heads : List (String × Head) :=
  [("i[+fem]", .cat .n_iFem), ("i[-fem]", .cat .n_iMasc), ("u[+fem]", .cat .n_uFem),
    ("u[-fem]", .cat .n_uMasc), ("plain", .cat .n_plain), ("a", .cat { cat := .a }),
    ("dim", .dim)]

/-- The genders the rows' agreement targets show. -/
def genders : List (String × UD.Gender) :=
  [("masculine", .Masc), ("feminine", .Fem), ("neuter", .Neut)]

/-- Every nominal of the chapter shows the gender the cyclicity analysis predicts, and the
hierarchical analysis predicts that gender only for the nominals where its probe copies what the
cyclic probe does. -/
theorem cyclicGender_rows : ∀ e ∈ Examples.all,
    ∃ vocabulary ∈ e.byLanguage vocabularies, ∃ hs ∈ e.parseAll? "head" heads,
      ∃ g ∈ e.parse? "gender" genders,
        shown vocabulary (cyclicGender ⟨r, hs⟩) = some g ∧
          (shown vocabulary (hierarchicalGender ⟨r, hs⟩) = some g ↔
            hierarchicalGender ⟨r, hs⟩ = cyclicGender ⟨r, hs⟩) := by
  simp only [cyclicGender, hierarchicalGender, ComplexHead.lastCycle]
  decide

end Kramer2015
