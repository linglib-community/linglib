module

public import Linglib.Data.Examples.Svenonius2026
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.InsideOut

/-!
# Svenonius (2026): Structural implications of late insertion

Chapter 27 of the Cambridge handbook argues from outward-sensitive phonologically conditioned
suppletive allomorphy to the timing of Vocabulary Insertion. Fulfulde incompletive aspect is -Vt
before a vowel-initial exponent, the copy vowel matching the following vowel, and -ay elsewhere
(13), so the incompletive's allomorph depends on the exponent chosen for the subject suffix
outside it. Insertion from the inside out has not made that choice yet — the outer morpheme is
still bare and shows its features only (`ComplexHead.visible_of_exp_none`) — so it realizes (13b)
as *ndur-ay-on-ɗi. If root and affixes are instead spelled out simultaneously, the pattern is
stateable: `IsJointSpellout` asks every morpheme's exponent to win the Subset Principle in the
context of the fully realized word, the attested (13a) and (13b) are such fixed points, and the
word inside-out insertion builds is not. Limbu shows the same pattern at the root (fn. 7): nuːks-
before the vowel-initial nonsingular -i, nuːŋ- elsewhere, with the unalternating hiŋ- 'live' as
the control.

## Implementation notes

* `IsJointSpellout` is the chapter's simultaneous spell-out, stated over the realized word's
  morphemes in hierarchical order: the context at each position is
  `ComplexHead.contextAt` under hierarchical locality, except that the other exponents are
  present. It stays study-local until a second study consumes it.
* The copy vowel of -Vt is written into the exponent `.ot`, -on being the only vowel-initial
  suffix in (13); vowel-initiality is the morphophonological feature `vInit` that `Exp.phon`
  exposes to insertion elsewhere in the word.
* Root allomorphy puts the root in the same morpheme list as the affixes, which inside-out
  insertion cannot do: a `ComplexHead`'s root exponent is present from the start.

## References

* [svenonius-2026]
* [carstairs-1988]
* [kager-1996]
* [mcintosh-1982]
* [van-driem-1987]
-/

@[expose] public section

namespace Svenonius2026

open DistributedMorphology
open Morphology.Exponence

/-- Joint spell-out: every morpheme of the fully realized word bears the exponent that wins the
Subset Principle in the context of that very word, so realization is a fixed point of Vocabulary
Insertion rather than an inside-out pass ([kager-1996] via [svenonius-2026]). -/
def IsJointSpellout {F E : Type*} [DecidableEq F] (vocab : RuleSet (VocabularyItem F E))
    (expFeatures : E → Finset F) (ms : List (Morpheme F E)) : Prop :=
  ∀ i < ms.length,
    (winner? vocab (.around (ms.map (ComplexHead.visible expFeatures)) i
      ((ms[i]?.map (·.feats)).getD ∅))).map (·.exponent) = ms[i]?.bind (·.exp)

instance {F E : Type*} [DecidableEq F] [DecidableEq E] (vocab : RuleSet (VocabularyItem F E))
    (expFeatures : E → Finset F) (ms : List (Morpheme F E)) :
    Decidable (IsJointSpellout vocab expFeatures ms) := by
  unfold IsJointSpellout; infer_instance

/-! ### Fulfulde incompletive aspect (13) -/

namespace Fulfulde

/-- The features of the Fulfulde verb forms in (13): the two roots, the extension, the
incompletive, the subject and object suffixes, and the morphophonological feature `vInit` a
vowel-initial exponent exposes. -/
inductive Feat where
  | cook | graze | ext | inc | sub1sg | sub2pl | objSg | objPl | vInit
  deriving DecidableEq, Repr

/-- The exponents of (13). -/
inductive Exp where
  | ndef | ndur | ir | ot | ay | mi | on | ndi | «ɗi»
  deriving DecidableEq, Repr

/-- The form of an exponent. -/
def Exp.form : Exp → String
  | .ndef => "ndef" | .ndur => "ndur" | .ir => "ir" | .ot => "ot" | .ay => "ay"
  | .mi => "mi" | .on => "on" | .ndi => "ndi" | .«ɗi» => "ɗi"

/-- The morphophonological features a realized exponent shows the rest of the word: `vInit` on
the vowel-initial exponents, read off `Exp.form`. -/
def Exp.phon : Exp → Finset Feat
  | .ir | .ot | .ay | .on => {.vInit}
  | _ => ∅

/-- The Vocabulary of (13): the incompletive is -Vt before a vowel-initial exponent, the copy
vowel written in, and -ay elsewhere, the case [carstairs-1988] noted; every other morpheme has
one context-free item. -/
def vocabulary : RuleSet (VocabularyItem Feat Exp) :=
  [⟨{(0, .inc), (1, .vInit)}, .ot⟩,
   {Feat.inc} ⟷ .ay,
   {Feat.cook} ⟷ .ndef, {Feat.graze} ⟷ .ndur, {Feat.ext} ⟷ .ir,
   {Feat.sub1sg} ⟷ .mi, {Feat.sub2pl} ⟷ .on,
   {Feat.objSg} ⟷ .ndi, {Feat.objPl} ⟷ .«ɗi»]

/-- (13a) ndef-ir-ay-mi-ndi 'cook-EXT-INC-I-it': the elsewhere -ay before the consonant-initial
subject suffix -mi. -/
def word13a : List (Morpheme Feat Exp) :=
  [⟨{.cook}, some .ndef, .after⟩, ⟨{.ext}, some .ir, .after⟩, ⟨{.inc}, some .ay, .after⟩,
   ⟨{.sub1sg}, some .mi, .after⟩, ⟨{.objSg}, some .ndi, .after⟩]

/-- (13b) ndur-ot-on-ɗi 'graze-INC-you-them': the prevocalic -ot before the vowel-initial subject
suffix -on. -/
def word13b : List (Morpheme Feat Exp) :=
  [⟨{.graze}, some .ndur, .after⟩, ⟨{.inc}, some .ot, .after⟩, ⟨{.sub2pl}, some .on, .after⟩,
   ⟨{.objPl}, some .«ɗi», .after⟩]

/-- The modelled words are the rows' verbs. -/
example : Examples.ex13a.glossedTokens.map (·.1) = ["Raa", "no", "ndef-ir-ay-mi-ndi"] := rfl
example : (word13a.filterMap (·.exp)).map Exp.form = ["ndef", "ir", "ay", "mi", "ndi"] := by
  simp [word13a, Exp.form]
example : Examples.ex13b.glossedTokens.map (·.1) = ["Walaa", "to", "ndur-ot-on-ɗi"] := rfl
example : (word13b.filterMap (·.exp)).map Exp.form = ["ndur", "ot", "on", "ɗi"] := by
  simp [word13b, Exp.form]

-- (13a)
theorem joint_word13a : IsJointSpellout vocabulary Exp.phon word13a := by decide

-- (13b)
theorem joint_word13b : IsJointSpellout vocabulary Exp.phon word13b := by decide

/-- (13b) as a complex head before insertion: the root realized, the suffixes bare. -/
def head13b : ComplexHead (Morpheme Feat Exp) (Morpheme Feat Exp) :=
  ⟨⟨{.graze}, some .ndur, .after⟩,
   [⟨{.inc}, none, .after⟩, ⟨{.sub2pl}, none, .after⟩, ⟨{.objPl}, none, .after⟩]⟩

/-- The word Vocabulary Insertion from the inside out makes of (13b). -/
def insideOut13b : ComplexHead (Morpheme Feat Exp) (Morpheme Feat Exp) :=
  head13b.insertAll (fun _ ↦ False) vocabulary .hierarchical Exp.phon .nondeletion

-- (13b)
theorem exponents_insideOut13b : insideOut13b.exponents = [.ndur, .ay, .on, .«ɗi»] := by decide

theorem not_joint_insideOut13b :
    ¬ IsJointSpellout vocabulary Exp.phon (insideOut13b.root :: insideOut13b.heads) := by decide

end Fulfulde

/-! ### Limbu root allomorphy (fn. 7) -/

namespace Limbu

/-- The features of the Limbu verb forms in fn. 7: the two roots, the dual -s, the nonsingular
-i, the first person exclusive -ge, and `vInit`. -/
inductive Feat where
  | ret | live | du | nsg | exc | vInit
  deriving DecidableEq, Repr

/-- The exponents of fn. 7. -/
inductive Exp where
  | nung | nuks | hing | s | i | ge
  deriving DecidableEq, Repr

/-- The form of an exponent. -/
def Exp.form : Exp → String
  | .nung => "nuːŋ" | .nuks => "nuːks" | .hing => "hiŋ" | .s => "s" | .i => "i" | .ge => "ge"

/-- `vInit` on the vowel-initial exponents, read off `Exp.form`. -/
def Exp.phon : Exp → Finset Feat
  | .i => {.vInit}
  | _ => ∅

/-- The Vocabulary of fn. 7: 'return' is nuːks- before a vowel-initial exponent and nuːŋ-
elsewhere, while 'live' is hiŋ- throughout. -/
def vocabulary : RuleSet (VocabularyItem Feat Exp) :=
  [⟨{(0, .ret), (1, .vInit)}, .nuks⟩,
   {Feat.ret} ⟷ .nung, {Feat.live} ⟷ .hing,
   {Feat.du} ⟷ .s, {Feat.nsg} ⟷ .i, {Feat.exc} ⟷ .ge]

/-- nuːŋ-s-i-ge 'return', first person exclusive dual: the elsewhere root before the dual -s. -/
def returnDual : List (Morpheme Feat Exp) :=
  [⟨{.ret}, some .nung, .after⟩, ⟨{.du}, some .s, .after⟩, ⟨{.nsg}, some .i, .after⟩,
   ⟨{.exc}, some .ge, .after⟩]

/-- nuːks-i-ge 'return', first person exclusive plural: the prevocalic root before the
nonsingular -i. -/
def returnPlural : List (Morpheme Feat Exp) :=
  [⟨{.ret}, some .nuks, .after⟩, ⟨{.nsg}, some .i, .after⟩, ⟨{.exc}, some .ge, .after⟩]

/-- hiŋ-s-i-ge and hiŋ-i-ge 'live': the control root, unchanged in both environments. -/
def liveDual : List (Morpheme Feat Exp) :=
  [⟨{.live}, some .hing, .after⟩, ⟨{.du}, some .s, .after⟩, ⟨{.nsg}, some .i, .after⟩,
   ⟨{.exc}, some .ge, .after⟩]

/-- hiŋ-i-ge 'live', first person exclusive plural. -/
def livePlural : List (Morpheme Feat Exp) :=
  [⟨{.live}, some .hing, .after⟩, ⟨{.nsg}, some .i, .after⟩, ⟨{.exc}, some .ge, .after⟩]

/-- The modelled words are the rows' forms. -/
example : Examples.fn7return.primaryText = "nuːŋ-s-i-ge~nuːks-i-ge" := rfl
example : (returnDual.filterMap (·.exp)).map Exp.form = ["nuːŋ", "s", "i", "ge"] := by
  simp [returnDual, Exp.form]
example : (returnPlural.filterMap (·.exp)).map Exp.form = ["nuːks", "i", "ge"] := by
  simp [returnPlural, Exp.form]

-- fn. 7
theorem joint_return :
    IsJointSpellout vocabulary Exp.phon returnDual ∧
      IsJointSpellout vocabulary Exp.phon returnPlural := by decide

theorem not_joint_return_elsewhere :
    ¬ IsJointSpellout vocabulary Exp.phon
      [⟨{.ret}, some .nung, .after⟩, ⟨{.nsg}, some .i, .after⟩, ⟨{.exc}, some .ge, .after⟩] := by
  decide

theorem joint_live :
    IsJointSpellout vocabulary Exp.phon liveDual ∧
      IsJointSpellout vocabulary Exp.phon livePlural := by decide

end Limbu

end Svenonius2026
