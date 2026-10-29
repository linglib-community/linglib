/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Word.Features

/-!
# Leipzig category labels of tokens

The Leipzig Glossing Rules render the grammatical categories of a morph by labels in capitals,
drawn from a list of standard abbreviations, and separate the labels of one morph by periods,
except that a person and a number that cooccur in this order are written together, as `3SG`.
This file reads the labels that name a value of a token feature into the token's features: the
persons `1`, `2` and `3`, the first refined by `INCL` and `EXCL`, the numbers `SG`, `DU` and `PL`,
the genders `M`, `F` and `N`, the cases, definiteness, the infinitive, participle and converb, the
tenses, the moods and negation. A label whose category is no feature value, as `FOC` or `PASS`,
names nothing.

## Main definitions

* `Morphology.Feature.labels`: the standard abbreviations of the values of a feature.
* `Morphology.Features.ofLabels`: the features a list of labels names.

## Implementation notes

* The genders are also read in the spellings `MASC`, `FEM` and `NEUT`, which the rules' licence
  to deviate from the list (Rule 3) covers and which Corbett's books use.
* Aspect and voice are not read: the list's perfective `PFV` and perfect `PRF` would both be the
  annotation's `Perf`, and its causative and antipassive are derivations.
* Labels are lists of characters, as `Gloss.labels` produces them from a gloss, so that the
  reading is consumed by `decide`.

## References

* [comrie-haspelmath-bickel-2008]
-/

@[expose] public section

namespace Morphology

/-- The standard abbreviations of the Leipzig Glossing Rules that name a value of the feature,
with the value each names. -/
def Feature.labels : (f : Feature) → List (List Char × f.Value)
  | .person => [("1".toList, .first), ("2".toList, .second), ("3".toList, .third),
      ("INCL".toList, .firstInclusive), ("EXCL".toList, .firstExclusive)]
  | .number => [("SG".toList, .singular), ("DU".toList, .dual), ("PL".toList, .plural)]
  | .gender => [("M".toList, .Masc), ("F".toList, .Fem), ("N".toList, .Neut),
      ("MASC".toList, .Masc), ("FEM".toList, .Fem), ("NEUT".toList, .Neut)]
  | .case => [("NOM".toList, .nom), ("ACC".toList, .acc), ("GEN".toList, .gen),
      ("DAT".toList, .dat), ("INS".toList, .inst), ("LOC".toList, .loc), ("VOC".toList, .voc),
      ("ABL".toList, .abl), ("ALL".toList, .all), ("ERG".toList, .erg), ("ABS".toList, .abs),
      ("OBL".toList, .obl), ("COM".toList, .com), ("BEN".toList, .ben)]
  | .definiteness => [("DEF".toList, .Def), ("INDF".toList, .Ind)]
  | .verbForm => [("INF".toList, .Inf), ("PTCP".toList, .Part), ("CVB".toList, .Conv)]
  | .tense => [("PST".toList, .Past), ("PRS".toList, .Pres), ("FUT".toList, .Fut)]
  | .mood => [("IMP".toList, .Imp), ("IND".toList, .Ind), ("SBJV".toList, .Sub),
      ("COND".toList, .Cnd)]
  | .polarity => [("NEG".toList, .Neg)]
  | _ => []

/-- No abbreviation names two values of a feature, so a label's reading does not depend on the
order of the list. -/
theorem Feature.nodup_labels (f : Feature) : (f.labels.map Prod.fst).Nodup := by
  cases f <;> decide

namespace Features

/-- The features the category labels `ls` name. A person is read from a label `INCL` or `EXCL`,
else from the digit that begins a label, and a number from a label after its person digit, a
person and a number being written together (Rule 5). -/
def ofLabels (ls : List (List Char)) : Features
  | .person => (ls.findSome? fun l ↦ (Feature.labels .person).lookup l |>.filter
      (· ∈ [Person.firstInclusive, .firstExclusive])).orElse fun _ ↦
        ls.findSome? fun l ↦ l.head?.bind fun c ↦ (Feature.labels .person).lookup [c]
  | .number => ls.findSome? fun l ↦
      (Feature.labels .number).lookup (l.dropWhile (· ∈ ['1', '2', '3']))
  | f => ls.findSome? ((Feature.labels f).lookup ·)

end Features

end Morphology
