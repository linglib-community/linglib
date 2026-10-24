module

public import Mathlib.Order.Basic
public import Linglib.Morphology.DistributedMorphology.Gender
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Morphology.DistributedMorphology.Impoverishment
public import Linglib.Fragments.Teop.Nouns
public import Linglib.Syntax.Agreement.Classes
public import Linglib.Fragments.Jarawara.PossessedNouns
public import Linglib.Fragments.Romance.Italian.NumberGender
public import Linglib.Fragments.Yanyuwa.Gender
public import Linglib.Fragments.CoastalMarind.Gender
public import Linglib.Semantics.Possession.Relationalizer
public import Linglib.Data.Examples.Adamson2024

/-!
# Gender assignment is local

Adamson's gender locality hypothesis says that the gender feature on a nominalizer n is valued
within nP (`GenderLocal`), so an inalienable possessor in
Spec,nP can bear on a noun's gender while an alienable possessor in Spec,PossP cannot
(`possession_asymmetry`). Possession bears on gender in two ways. Under *possessee gender* the
nominalizer that licenses a possessor carries a gender of its own: Teop body-part roots take a
gender I nominalizer that introduces the body-part relation with or without the selectional
feature licensing a possessor, and the possessor-less variant is renominalized by a gender II
alienator that closes the possessor slot (`Teop.relationalN`, `Teop.alienatorN`,
`Teop.freeDenot_iff`), so *a bina-naa* 'my spleen' is gender I and *o bina* 'the spleen' gender
II (`Teop.switch`, `Teop.rows_class`). The alienator is a plain n over a gendered one, so the
default gender II is what the cyclic explanation of Kramer's Highest Gender Hypothesis predicts
and not the hierarchical one (`Teop.free_cyclic`). Mosel and Spriggs's gender I-E is gender I with a
proprial feature. The article vocabulary derives the article of every class
(`Teop.article_eq_headArticle`), and agreeing adjectives and numerals distinguish only gender
(`Teop.agreementClasses_targetArticle`). Jarawara's possessed nouns are the unmarked
feminine, and the *mano* ~ *mani* alternation is agreement with the possessor: gender
impoverishment next to a plural or participant feature bleeds the masculine exponent
(`Jarawara.decl_masc_only`, `Jarawara.agreeingForm_eq_form`), and a monomoraic possessor prefix
forms one word with the noun it possesses and is invisible beyond it, so in *o-mano baki* the
outer noun agrees with the possessed noun's own feminine (`Jarawara.complex_match`,
`Jarawara.complex_mismatch`).

Under *inherited gender* the nominalizer is unvalued and probes its possessor
(`inheritedGender`): Yanyuwa *wini* 'name' and Coastal Marind *igih* 'name'
and *nanVh* 'face' take the gender of an inalienable possessor on their agreement targets and, for
*nanVh*, in their own form (`Yanyuwa.name_agreement`, `CoastalMarind.name_demonstrative`,
`CoastalMarind.face_inherits`), and an alienable possessor leaves them unvalued
(`Yanyuwa.name_alienable`). The hypothesis extends beyond possession: Standard Italian plurals in
*-a* carry number on n and change gender, regular plurals carry number on Num and do not
(`Italian.gender_change_iff_local`).

## Implementation notes

* An inalienable possessor sits in Spec,nP, following Myler; Alexiadou makes it the complement
  of the noun. Both places are within nP, which is all the locality hypothesis uses.
* A Teop nominal's class is the gender a probe finds in the last cycle of its spine, Kramer's
  derivation of the Highest Gender Hypothesis from cyclicity.

## References

* [adamson-2024]
* [kramer-2015]
* [alexiadou-2003]
* [mosel-spriggs-2000]
* [dixon-2004]
* [myler-2016]
-/

@[expose] public section

namespace Adamson2024

open DistributedMorphology
open DistributedMorphology.Categorizer (Head)

/-! ### The gender locality hypothesis -/

/-- The layers of the nominal projection, from the root up. -/
inductive Layer where
  | root
  | n
  | poss
  | num
  | d
  deriving DecidableEq, Repr, Fintype

/-- The height of a layer. -/
def Layer.height : Layer → ℕ
  | .root => 0
  | .n => 1
  | .poss => 2
  | .num => 3
  | .d => 4

instance : LinearOrder Layer := LinearOrder.lift' Layer.height (by decide)

/-- The positions of a possessor or of a number feature. -/
inductive Position where
  | nHead
  | specN
  | specPoss
  | num
  deriving DecidableEq, Repr, Fintype

/-- The layer a position attaches at. -/
def Position.layer : Position → Layer
  | .nHead | .specN => .n
  | .specPoss => .poss
  | .num => .num

/-- A position is local to gender when it attaches within nP. The gender locality hypothesis says
that only local positions can value gender on n. -/
def GenderLocal (p : Position) : Prop := p.layer ≤ .n

instance : DecidablePred GenderLocal := fun _ ↦ inferInstanceAs (Decidable (_ ≤ _))

/-- Inalienable and alienable possession. -/
inductive PossessionType where
  | inalienable
  | alienable
  deriving DecidableEq, Repr, Fintype

/-- An inalienable possessor sits in Spec,nP and an alienable one in Spec,PossP. -/
def PossessionType.possessorPosition : PossessionType → Position
  | .inalienable => .specN
  | .alienable => .specPoss

theorem possession_asymmetry :
    GenderLocal PossessionType.inalienable.possessorPosition ∧
      ¬ GenderLocal PossessionType.alienable.possessorPosition := by
  decide

/-- The gender an unvalued n acquires from a possessor of gender `g` at `pos`, when the
possessor is local. -/
def inheritedGender {G : Type*} (pos : Position) (g : G) : Option G :=
  if GenderLocal pos then some g else none

/-! ### Teop: possessee gender -/

namespace Teop

open _root_.Teop

/-- The nominalizer of a body-part or kinship root, bearing u[animate] and, when `selectsD`,
the feature {D} that licenses a possessor. -/
def relationalN (selectsD : Bool) : Head := { Head.n_uAnim with selectsD }

/-- The alienator, a gender II n that closes the possessor slot. -/
def alienatorN : Head := Head.n_plain

/-- The class a head gives a nominal, the a-class for the gender I feature [+ANIM] and none
otherwise. -/
def headClass (h : Head) : Option NounClass :=
  if h.gender.map (·.val) = some ⟨.anim, .pos⟩ then some .a else none

/-- The n's of a possessed body-part noun, the {D} nominalizer. -/
def ipossessed : List Head := [relationalN true]

/-- The n's of an unpossessed body-part noun, the {D}-less nominalizer under the alienator,
innermost first. Alienably possessed and compounded body-part nouns have the same n's. -/
def free : List Head := [relationalN false, alienatorN]

/-- The class of a nominal over the root `r` with the n's `hs`, the gender a probe finds in its
last cycle, which is the o-class (gender II) by default. Every categorizer is a cyclic head. -/
def classOf (r : Root) (hs : List Head) : NounClass :=
  agreeingGender headClass .o ((⟨r, hs⟩ : ComplexHead Root Head).lastCycle fun _ ↦ True)

theorem switch (r : Root) : classOf r ipossessed = .a ∧ classOf r free = .o := by
  simp only [classOf, ComplexHead.lastCycle]
  decide

theorem free_cyclic (r : Root) :
    classOf r free = .o ∧ agreeingGender headClass .o free.reverse = .a :=
  agreeingGender_lastCycle_plain (hs := []) trivial (by decide) (by decide)

theorem bodyPartTerms_free (r : Root) : ∀ n ∈ bodyPartTerms, n.gender = classOf r free := by
  simp only [classOf, ComplexHead.lastCycle]
  decide

/-- The n's of a body-part or kinship noun, by how it is possessed. -/
def possession : List (String × List Head) :=
  [("inalienable", ipossessed), ("alienable", free), ("none", free)]

/-- The analysis predicts the class of every attested body-part and kinship phrase from how its
noun is possessed, (39), (40), (44), (45), (48) and (51). -/
theorem rows_class (r : Root) : ∀ e ∈ Examples.all, e.language = "teop1238" →
    ∀ s ∈ e.parse? "possession" possession,
      ∀ c ∈ e.parse? "gender" [("I", NounClass.a), ("II", .o)],
        classOf r s = c := by
  simp only [classOf, ComplexHead.lastCycle]
  decide

/-- The features of the article, copied from DP by concord. -/
inductive ArticleFeature where
  | animate
  | pl
  | proper
  deriving DecidableEq, Repr

/-- The article vocabulary (32). -/
def articles : List (VocabularyItem ArticleFeature Article) :=
  [{.animate, .pl} ⟷ .o, {.pl} ⟷ .a, {.animate, .proper} ⟷ .e, {.animate} ⟷ .a, ∅ ⟷ .o]

/-- The article features of each class. Gender I-E is gender I with [proper]. -/
def classFeatures : NounClass → Finset ArticleFeature
  | .e => {.animate, .proper}
  | .a => {.animate}
  | .o => ∅

/-- The article inserted by the Subset Principle, by class and number. -/
def article (c : NounClass) (n : numberSystem.values) : Option Article :=
  subsetPrinciple articles
    (classFeatures c ∪ numberSystem.elim ∅ {.pl} (n := n) : Finset ArticleFeature)

theorem article_eq_headArticle : ∀ c pl, article c pl = some (headArticle c pl) := by decide

theorem agreementClasses_targetArticle :
    Gender.agreementClasses targetArticle =
      Setoid.ker fun c ↦ decide (ArticleFeature.animate ∈ classFeatures c) := by
  ext c c'
  simp only [Setoid.ker_def]
  cases c <;> cases c' <;> decide

/-- A possessed kinship term takes the proprial article *e*, (50), and one under the alienator
takes *o*, (51). -/
theorem kinship (r : Root) :
    subsetPrinciple articles (insert .proper (classFeatures (classOf r ipossessed)) :
        Finset ArticleFeature) = some .e ∧
      subsetPrinciple articles (insert .proper (classFeatures (classOf r free)) :
        Finset ArticleFeature) = some .o := by
  simp only [classOf, ComplexHead.lastCycle]
  decide

section Denotation

open Possession

variable {E S : Type*} (isSpleen : E → S → Prop) (bodyPartOf : E → E → S → Prop)

/-- The possessed body-part noun, the root relationalized by the body-part-of relation. -/
def ipossessedDenot : E → E → S → Prop := π isSpleen bodyPartOf

/-- The unpossessed body-part noun, whose possessor slot the alienator closes. -/
def freeDenot : E → S → Prop := ⨆ x, ipossessedDenot isSpleen bodyPartOf x

theorem freeDenot_iff (y : E) (s : S) :
    freeDenot isSpleen bodyPartOf y s ↔ isSpleen y s ∧ ∃ x, bodyPartOf x y s := by
  rw [freeDenot, ipossessedDenot, iSup_π]; simp

end Denotation

end Teop

/-! ### Jarawara: possessee gender and possessor agreement -/

namespace Jarawara

open _root_.Jarawara

/-- The privative φ-features are [masc], [pl], and [participant] for first and second person. -/
inductive Phi where
  | masc
  | pl
  | participant
  deriving DecidableEq, Repr

/-- The features a possessor contributes to agreement. -/
def possessorPhi : Possessor → Finset Phi
  | .sg1 | .sg2 => {.participant}
  | .incl | .excl | .nsg2 => {.participant, .pl}
  | .sg3 g => if g = .masc then {.masc} else ∅
  | .nsg3 g => insert .pl (if g = .masc then {.masc} else ∅)

/-- Gender impoverishment deletes [masc] next to [pl] and next to [participant]. -/
def impoverishment : List (ImpoverishmentRule (Finset Phi) Phi) :=
  [.ofFocus (.pl ∈ ·) .masc, .ofFocus (.participant ∈ ·) .masc]

/-- The φ-bundle after impoverishment. -/
def impoverish (φ : Finset Phi) : Finset Phi :=
  runChain (ImpoverishmentRule.apply Finset.erase) impoverishment (Neighborhood.ofBundle φ)

/-- The declarative marker is *ka* for [masc] and *ke* elsewhere. -/
def declarative : List (VocabularyItem Phi String) := [{.masc} ⟷ "ka", ∅ ⟷ "ke"]

/-- The declarative marker agreeing with a nominal of features `φ`. -/
def decl (φ : Finset Phi) : Option String := subsetPrinciple declarative (impoverish φ)

theorem decl_masc_only :
    decl {.masc} = some "ka" ∧ decl ∅ = some "ke" ∧ decl {.participant} = some "ke" ∧
      decl {.masc, .pl} = some "ke" := by
  decide

/-- A possessed noun takes its marked form for [participant] or a surviving [masc] and its
unmarked form elsewhere. -/
def possessedItems (marked unmarked : String) : List (VocabularyItem Phi String) :=
  [{.participant} ⟷ marked, {.masc} ⟷ marked, ∅ ⟷ unmarked]

/-- The form of a possessed noun agreeing with a possessor of features `φ`. -/
def agreeingForm (n : PossessedNoun) (φ : Finset Phi) : Option String :=
  subsetPrinciple (possessedItems n.mForm n.fForm) (impoverish φ)

theorem agreeingForm_eq_form :
    ∀ n ∈ possessedNouns, ∀ p, agreeingForm n (possessorPhi p) = some (n.form p) := by
  decide

/-- A possessor makes its features visible outside the word of the noun it possesses unless it
is a prefix, a pronoun below the two-mora minimal word that forms one word with that noun. -/
def visibleOutside (p : Possessor) : Finset Phi := if p.IsPrefix then ∅ else possessorPhi p

/-- *bako* 'inside' in `[[p mano] bako]`, agreeing with the possessor when its features
percolate and with the feminine possessed noun otherwise. -/
def inside (p : Possessor) : Option String := agreeingForm bako (visibleOutside p)

theorem complex_match : ∀ p, ¬ p.IsPrefix → inside p = some (bako.form p) := by
  decide

theorem complex_mismatch :
    ∀ p, p.IsPrefix →
      agreeingForm mano (possessorPhi p) = some "mano" ∧ inside p = some "baki" := by
  decide

end Jarawara

/-! ### Yanyuwa and Coastal Marind: inherited gender -/

namespace Yanyuwa

open _root_.Yanyuwa

theorem name_agreement (s : Speaker) (g : _root_.Yanyuwa.Gender) :
    (inheritedGender PossessionType.inalienable.possessorPosition g).map (classPrefix s) =
      some (classPrefix s g) :=
  rfl

theorem classes_separated (s : Speaker) :
    ¬ Function.Injective (classPrefix s) ∧ _root_.Gender.Faithful (agreementPrefix s) := by
  cases s <;> decide

theorem name_alienable (g : _root_.Yanyuwa.Gender) :
    inheritedGender PossessionType.alienable.possessorPosition g = none :=
  rfl

end Yanyuwa

namespace CoastalMarind

open _root_.CoastalMarind

theorem name_demonstrative (g : _root_.CoastalMarind.Gender) :
    (inheritedGender PossessionType.inalienable.possessorPosition g).map
        (demonstrative · (numberSystem.value .singular)) =
      some (demonstrative g (numberSystem.value .singular)) :=
  rfl

theorem face_inherits :
    (inheritedGender PossessionType.inalienable.possessorPosition .gI).map
        (face · (numberSystem.value .singular)) =
        some "nanih" ∧
      (inheritedGender PossessionType.inalienable.possessorPosition .gII).map
          (face · (numberSystem.value .singular)) =
        some "nanuh" ∧
      similative .gI (numberSystem.value .singular) = "hi" ∧
      similative .gII (numberSystem.value .singular) = "hu" := by
  decide

end CoastalMarind

/-! ### Number on n -/

namespace Italian

open _root_.Italian.NumberGender

/-- A plural class's number feature sits on n for the *-a* plurals and on Num for regular
plurals. -/
def numberPosition : PluralClass → Position
  | .aPlural => .nHead
  | .regular => .num

theorem gender_change_iff_local :
    ∀ n ∈ aPlurals ++ regulars,
      n.gender ≠ n.plGender ↔
        GenderLocal (numberPosition n.pluralClass) := by
  decide

end Italian

end Adamson2024
