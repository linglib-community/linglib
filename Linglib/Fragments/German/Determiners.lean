module

public import Linglib.Fragments.German.Case
public import Linglib.Fragments.German.Gender
public import Linglib.Syntax.Category.Determiner.Basic

/-!
# German determiners

This file defines the declensions of the German determiners and the German determiner inventory.
A determiner declines for the case, number and gender of its noun, and its forms are the main way
these categories are shown. A paradigm has sixteen cells, the four cases in each of the three
genders of the singular and in the plural, where the genders fall together. Many determiners take
one set of endings, the strong endings of *dieser* 'this'. The indefinite article *ein*, its
negative *kein* and the possessives take them too, except in the nominative singular masculine and
the nominative and accusative singular neuter, where they have none, and *ein* has no plural. The
definite article *der* has forms of its own. The paradigms are Durrell's.

No paradigm distinguishes all sixteen cells. The definite article keeps the four cases apart in
the masculine singular only: the nominative and the accusative fall together in the other genders
and in the plural, and the genitive and the dative in the feminine singular. In the singular it
keeps the three genders apart in the nominative and the accusative but not in the genitive and the
dative, and that is the agreement evidence for the three-gender carrier of `German.Gender`.

The definite article contracts with some prepositions, *im* for *in dem* and *zur* for *zu der*.
Durrell notes that the full form is used where the article is stressed, refers back to something
just mentioned or has the force of a demonstrative, as in *Er ging zu der Hütte* 'he went to the
hut (just mentioned)' against *Er ging zur Hütte* 'he went to the hut (we all know)'. Schwarz takes
the contracted and the full form for a weak article of uniqueness and a strong article of
familiarity, and Moroney classes a language by how its articles mark the two.

## Main declarations

* `German.Determiners.GenderNumber`: the gender and number a determiner agrees in.
* `German.Determiners.strongEnding`: the strong endings.
* `German.Determiners.dieser`, `German.Determiners.einWord`, `German.Determiners.kein`,
  `German.Determiners.ein`, `German.Determiners.definite`: the declensions.
* `German.Determiners.Endingless`: the three cells where *ein* and *kein* have no ending.
* `German.Determiners.injective_definite_sg_masc`, `German.Determiners.definite_nom_eq_acc_iff`,
  `German.Determiners.definite_gen_eq_dat_iff`: the case syncretisms of the definite article.
* `German.Determiners.faithful`: the three-gender carrier is faithful to the definite article.
* `German.Determiners.contracted`, `German.Determiners.nonContracted`: the definite article
  contracted with a preposition and its full form.
* `German.Determiners.inventory`, `German.Determiners.strengths_inventory`: the inventory, whose
  two definite articles mark the two strengths.

## References

* [durrell-2011]
* [schwarz-2009]
* [moroney-2021]
* [diessel-2013b]
-/

@[expose] public section

namespace German.Determiners

open German.Case (forms)

/-- A determiner agrees with its noun in a gender in the singular, and only in number in the plural,
where the genders fall together. -/
inductive GenderNumber where
  | sg (g : Gender.Value)
  | pl
  deriving DecidableEq, Repr, Fintype

/-! ### Declensions -/

/-- `strongEnding x c` is the strong ending of the cell, the ending *dieser* takes there. -/
def strongEnding : GenderNumber → Case → String
  | .sg .masc => forms "er" "en" "es" "em"
  | .sg .fem => forms "e" "e" "er" "er"
  | .sg .neut => forms "es" "es" "es" "em"
  | .pl => forms "e" "e" "er" "en"

/-- *dieser* 'this' declines with the strong endings on the stem *dies-*, and *jener* 'that'
declines like it. -/
def dieser (x : GenderNumber) (c : Case) : String := "dies" ++ strongEnding x c

/-- `Endingless x c` holds of the nominative singular masculine and the nominative and accusative
singular neuter, the cells where *ein*, *kein* and the possessives have no ending. -/
def Endingless (x : GenderNumber) (c : Case) : Prop :=
  x = .sg .masc ∧ c = .nom ∨ x = .sg .neut ∧ (c = .nom ∨ c = .acc)

instance (x : GenderNumber) (c : Case) : Decidable (Endingless x c) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- `einWord stem` declines an *ein*-word, such as *kein* or the possessive *mein*, on the stem
`stem`, with the strong endings except in the endingless cells, where it has none. -/
def einWord (stem : String) (x : GenderNumber) (c : Case) : String :=
  if Endingless x c then stem else stem ++ strongEnding x c

/-- *kein* 'no' is an *ein*-word. -/
def kein : GenderNumber → Case → String := einWord "kein"

/-- The indefinite article *ein* is an *ein*-word in the singular and has no plural. -/
def ein : GenderNumber → Case → Option String
  | .pl, _ => none
  | x, c => some (einWord "ein" x c)

/-- `definite x c` is the form of the definite article in the cell. -/
def definite : GenderNumber → Case → String
  | .sg .masc => forms "der" "den" "des" "dem"
  | .sg .fem => forms "die" "die" "der" "der"
  | .sg .neut => forms "das" "das" "des" "dem"
  | .pl => forms "die" "die" "der" "den"

/-! ### Syncretism -/

/-- The masculine singular of the definite article keeps the four cases apart. -/
theorem injective_definite_sg_masc : Function.Injective (definite (.sg .masc)) := by decide

/-- The nominative and the accusative of the definite article fall together everywhere but in the
masculine singular. -/
theorem definite_nom_eq_acc_iff (x : GenderNumber) :
    definite x .nom = definite x .acc ↔ x ≠ .sg .masc := by
  revert x; decide

/-- The genitive and the dative of the definite article fall together in the feminine singular
only. -/
theorem definite_gen_eq_dat_iff (x : GenderNumber) :
    definite x .gen = definite x .dat ↔ x = .sg .fem := by
  revert x; decide

/-! ### Gender agreement -/

/-- The nominative singular of the definite article keeps the three genders apart. -/
theorem injective_definite_sg_nom : Function.Injective fun g ↦ definite (.sg g) .nom := by
  decide

/-- The dative singular does not, the masculine and the neuter both being *dem*. -/
theorem not_injective_definite_sg_dat :
    ¬ Function.Injective fun g ↦ definite (.sg g) .dat := by
  decide

/-- The three-gender carrier is faithful to the definite article. -/
theorem faithful : Gender.Faithful fun g ↦ definite (.sg g) :=
  fun _ _ h ↦ injective_definite_sg_nom (congrFun h .nom)

/-! ### The inventory -/

/-- The definite article contracted with a preposition, as in *im* for *in dem*, expones the uses
on which its referent is unique in the situation. -/
def contracted : Article :=
  { form := "im", definiteness := .definite, exponent := .dedicatedMorpheme,
    uses := {.immediateSituation, .largerSituation} }

/-- The non-contracted definite article, as *dem* in *in dem*, expones the uses on which it refers
back to an antecedent. -/
def nonContracted : Article :=
  { form := definite (.sg .masc) .dat, definiteness := .definite, exponent := .dedicatedMorpheme,
    uses := {.anaphoric} }

/-- The inventory lists the two definite articles, the contracted and the non-contracted form; the
indefinite article; the demonstrative *dieser*, which no longer contrasts with *jener* and is
distance-neutral, so it covers every participant set; and the possessive *mein*. -/
def inventory : Determiner.Inventory :=
  [ .article contracted,
    .article nonContracted,
    .article { form := "ein", definiteness := .indefinite, exponent := .dedicatedMorpheme },
    .demonstrative { form := dieser (.sg .masc) .nom, deixis := Finset.univ },
    .possessive { form := "mein" } ]

/-- Both strengths are marked, by distinct articles. -/
theorem strengths_inventory : inventory.strengths = Finset.univ := by decide

theorem not_isSyncretic_inventory : ¬ inventory.IsSyncretic := by decide

end German.Determiners
