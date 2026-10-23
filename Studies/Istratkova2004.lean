module

public import Linglib.Data.Examples.Istratkova2004
public import Linglib.Data.Wordlist.Istratkova2004
public import Studies.Svenonius2004

/-!
# Istratkova (2004): On Multiple Prefixation in Bulgarian

Istratkova analyses Bulgarian verbs carrying up to seven prefixes. Prefixes quantize rather than
perfectivize: the simplex homogeneous verbs of (2) are aspectless, and a prefix or the
semelfactive suffix quantizes them so that the aspectual head can project. In a stack only the
innermost prefix is lexical, Svenonius's generalization, and the superlexical prefixes merge above
AspP in the fixed order of the hierarchy (32): attenuative *po-*, inceptive *za-*, terminative
*do-*, completive *iz-*, distributive *po-*, cumulative *na-*, excessive *raz-*, repetitive
*pre-*.

## Main definitions

* `homogeneous`, `quantized`: the simplex verbs of (2) and (4).
* `hierarchy`, `Ordered`: the order (32) and stacks that conform to it.
* `WellFormed`: a stack is well-stacked and ordered, distributive *po-* occurs only under
  completive *iz-*, (29), and delimitative *po-* stands alone, (26).

## Main results

* `homogeneous_imperfective`, `quantized_perfective`: each aspectless verb is a dictionary
  imperfective and each quantized one a dictionary perfective.
* `attested_wellFormed`, `starred_not_wellFormed`: the attested stacks of Sections 1, 4 and 5
  conform, and the starred stacks that reverse two heads of the hierarchy do not.
* `spells`, `judgments`: each analysis spells out its form, accepted or rejected.
* `attenuative_outermost`: attenuative *po-* is outermost in any ordered stack.
* `phaseTests_necessary`: the phase-verb test admits the imperfective complements of (17), and
  is a necessary condition only, since (17b) is excluded by its meaning.

## Implementation notes

* The surface prefix *po-* is classified as distributive under completive *iz-* and attenuative
  otherwise, following the paper's glosses; a starred stack with *po-* below another head is
  excluded on either classification, the distributive one for want of *iz-*.
* The hierarchy places excessive *raz-* above repetitive *pre-*, but the paper accepts the
  flipped order in (25c) and (30b) with a different scope reading; the flipped forms are rows,
  not analyses. The starred stacks the paper attributes to meaning incompatibility, (18d),
  (20e), (20f) and the *na-pre-* cells of Table 2, conform to the hierarchy and are not derived.
* The selection of high inceptive *za-* for an imperfective output, (24a), is recorded in the
  rows; the analyses carry no outer aspect.

## References

* [istratkova-2004]
* [svenonius-2004]
-/

@[expose] public section

namespace Istratkova2004

open Morphology (Morph)
open Svenonius2004
open Bulgarian.Verbs

/-- The simplex homogeneous verbs of (2) in the fragment, with *peja*, which (24b), (25g) and (26a)
treat as homogeneous; the paper analyses them as aspectless. -/
def homogeneous : List Verb := [misla, obicham, znam, blesta, pisha, cheta, peja]

/-- The simplex quantized verbs of (4). -/
def quantized : List Verb := [kupja, dam]

/-- Each aspectless homogeneous verb is one the dictionary calls imperfective, the default value
it shows. -/
theorem homogeneous_imperfective : ∀ v ∈ homogeneous, v.perfectivity = some .imperfective := by
  decide

/-- Each quantized simplex verb is one the dictionary calls perfective. -/
theorem quantized_perfective : ∀ v ∈ quantized, v.perfectivity = some .perfective := by
  decide

/-! ### The hierarchy -/

/-- The hierarchy (32) of superlexical heads above AspP, highest first; delimitative *po-*
merges low and does not stack. -/
def hierarchy : List SuperlexicalSubtype :=
  [.attenuative, .inceptive, .terminative, .completive, .distributive, .cumulative, .excessive,
   .repetitive]

/-- `s` is merged above `t`. -/
def Above (s t : SuperlexicalSubtype) : Prop := hierarchy.idxOf s < hierarchy.idxOf t

instance (s t : SuperlexicalSubtype) : Decidable (Above s t) := inferInstanceAs (Decidable (_ < _))

/-- The superlexical heads of a classified prefix sequence, outermost first. -/
def superlexicals (ps : List (Morph × PrefixClass)) : List SuperlexicalSubtype :=
  ps.filterMap fun p ↦ match p.2 with
    | .superlexical s => some s
    | .lexical => none

/-- The stack conforms to the hierarchy: every superlexical prefix is merged above the ones
inside it. -/
def Ordered (ps : List (Morph × PrefixClass)) : Prop := (superlexicals ps).Pairwise Above

/-- Distributive *po-* occurs only with completive *iz-* outside, (21) and (29). -/
def DistributiveLicensed (ps : List (Morph × PrefixClass)) : Prop :=
  .distributive ∈ superlexicals ps → .completive ∈ superlexicals ps

/-- Delimitative *po-* does not stack, (26). -/
def DelimitativeAlone (ps : List (Morph × PrefixClass)) : Prop :=
  .delimitative ∈ superlexicals ps → superlexicals ps = [.delimitative]

/-- A well-formed stack has its superlexicals outside its lexicals and in hierarchy order, with
distributive *po-* licensed and delimitative *po-* alone. -/
def WellFormed (ps : List (Morph × PrefixClass)) : Prop :=
  WellStacked ps ∧ Ordered ps ∧ DistributiveLicensed ps ∧ DelimitativeAlone ps

instance (ps : List (Morph × PrefixClass)) : Decidable (WellFormed ps) := by
  unfold WellFormed Ordered DistributiveLicensed DelimitativeAlone; infer_instance

/-- Nothing stacks on top of attenuative *po-*: in an ordered stack it is outermost. -/
theorem attenuative_outermost {l : List SuperlexicalSubtype} (h : l.Pairwise Above)
    (hm : .attenuative ∈ l) : l.head? = some .attenuative := by
  cases l with
  | nil => simp at hm
  | cons a t =>
    rcases List.mem_cons.1 hm with rfl | hm
    · rfl
    · have ha := (List.pairwise_cons.1 h).1 _ hm
      have h0 : hierarchy.idxOf SuperlexicalSubtype.attenuative = 0 := rfl
      simp [Above, h0] at ha

/-! ### The attested stacks -/

/-- (1a) *za-piša* 'put down in writing' has lexical *za-* on *piša*. -/
def a1a : Analysis := ⟨Wordlist.f_1a, pisha, [(za, .lexical)]⟩

/-- (3a) *iz-misl'a* 'make up (a story)' has lexical *iz-*. -/
def a3a : Analysis := ⟨Wordlist.f_3a, misla, [(iz, .lexical)]⟩

/-- (3b) *za-običam* 'start to love' has low inceptive *za-* on a homogeneous verb. -/
def a3b : Analysis := ⟨Wordlist.f_3b, obicham, [(za, .superlexical .inceptive)]⟩

/-- (3c) *po-znam* 'guess' has lexical *po-*. -/
def a3c : Analysis := ⟨Wordlist.f_3c, znam, [(po, .lexical)]⟩

/-- (3d) *za-blest'a* 'start to glitter' has low inceptive *za-*. -/
def a3d : Analysis := ⟨Wordlist.f_3d, blesta, [(za, .superlexical .inceptive)]⟩

/-- (3i) *pro-četa* 'read completely' has lexical *pro-*. -/
def a3i : Analysis := ⟨Wordlist.f_3i, cheta, [(pro, .lexical)]⟩

/-- (11) *iz-po-na-raz-pro-dam* 'sell completely many things in excess one by one'. -/
def a11 : Analysis :=
  ⟨Wordlist.f_11, dam, [(iz, .superlexical .completive), (po, .superlexical .distributive),
    (na, .superlexical .cumulative), (raz, .superlexical .excessive), (pro, .lexical)]⟩

/-- (13a) *iz-raz-kaža* 'narrate completely' has completive *iz-* outside lexical *raz-*. -/
def a13a : Analysis :=
  ⟨Wordlist.f_13a, kazha, [(iz, .superlexical .completive), (raz, .lexical)]⟩

/-- (15) *iz-po-na-kaža* has the innermost prefix read as lexical out of context. -/
def a15 : Analysis :=
  ⟨Wordlist.f_15, kazha,
    [(iz, .superlexical .completive), (po, .superlexical .distributive), (na, .lexical)]⟩

/-- (18a) *raz-pre-pro-dam* 'sell again in excess'. -/
def a18a : Analysis :=
  ⟨Wordlist.f_18a, dam,
    [(raz, .superlexical .excessive), (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (18b) *po-pre-pro-dam* 'sell again a little bit'. -/
def a18b : Analysis :=
  ⟨Wordlist.f_18b, dam,
    [(po, .superlexical .attenuative), (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (19a) *po-raz-pre-pro-dam* has attenuative *po-* lowering the intensity of *raz-*. -/
def a19a : Analysis :=
  ⟨Wordlist.f_19a, dam, [(po, .superlexical .attenuative), (raz, .superlexical .excessive),
    (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (19b) *iz-raz-pre-pro-dam* 'completely sell again to the very end'. -/
def a19b : Analysis :=
  ⟨Wordlist.f_19b, dam, [(iz, .superlexical .completive), (raz, .superlexical .excessive),
    (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (20b) *na-pre-pro-dam* 'sell again a lot of things'. -/
def a20b : Analysis :=
  ⟨Wordlist.f_20b, dam,
    [(na, .superlexical .cumulative), (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (20c) *na-pro-dam* 'sell a lot'. -/
def a20c : Analysis := ⟨Wordlist.f_20c, dam, [(na, .superlexical .cumulative), (pro, .lexical)]⟩

/-- (20d) *po-na-pro-dam* 'sell a little' has attenuative *po-* modifying cumulative *na-*. -/
def a20d : Analysis :=
  ⟨Wordlist.f_20d, dam,
    [(po, .superlexical .attenuative), (na, .superlexical .cumulative), (pro, .lexical)]⟩

/-- (21a) *iz-po-na-pro-dam* has distributive *po-* under completive *iz-*. -/
def a21a : Analysis :=
  ⟨Wordlist.f_21a, dam, [(iz, .superlexical .completive), (po, .superlexical .distributive),
    (na, .superlexical .cumulative), (pro, .lexical)]⟩

/-- (21b) *iz-po-raz-pro-dam*. -/
def a21b : Analysis :=
  ⟨Wordlist.f_21b, dam, [(iz, .superlexical .completive), (po, .superlexical .distributive),
    (raz, .superlexical .excessive), (pro, .lexical)]⟩

/-- (21c) *iz-po-pre-pro-dam*. -/
def a21c : Analysis :=
  ⟨Wordlist.f_21c, dam, [(iz, .superlexical .completive), (po, .superlexical .distributive),
    (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (23b) *po-raz-pro-dam* 'sell almost everything'. -/
def a23b : Analysis :=
  ⟨Wordlist.f_23b, dam,
    [(po, .superlexical .attenuative), (raz, .superlexical .excessive), (pro, .lexical)]⟩

/-- (23d) *po-iz-pro-dam* 'sell almost completely'. -/
def a23d : Analysis :=
  ⟨Wordlist.f_23d, dam,
    [(po, .superlexical .attenuative), (iz, .superlexical .completive), (pro, .lexical)]⟩

/-- (23e) *po-pro-dam* 'sell a little bit'. -/
def a23e : Analysis := ⟨Wordlist.f_23e, dam, [(po, .superlexical .attenuative), (pro, .lexical)]⟩

/-- (25a) *do-pro-dam* 'finish selling'. -/
def a25a : Analysis := ⟨Wordlist.f_25a, dam, [(do_, .superlexical .terminative), (pro, .lexical)]⟩

/-- (25b) *do-pre-pro-dam* 'finish selling again'. -/
def a25b : Analysis :=
  ⟨Wordlist.f_25b, dam,
    [(do_, .superlexical .terminative), (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (25c) *do-raz-pre-pro-dam* 'finish selling again to the very end'. -/
def a25c : Analysis :=
  ⟨Wordlist.f_25c1, dam, [(do_, .superlexical .terminative), (raz, .superlexical .excessive),
    (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (25d) *do-iz-po-raz-pre-pro-dam* 'finish re-selling everything to the end'. -/
def a25d : Analysis :=
  ⟨Wordlist.f_25d, dam, [(do_, .superlexical .terminative), (iz, .superlexical .completive),
    (po, .superlexical .distributive), (raz, .superlexical .excessive),
    (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (25e) *po-do-iz-raz-pro-dam* 'almost finish reselling to the end'. -/
def a25e : Analysis :=
  ⟨Wordlist.f_25e, dam, [(po, .superlexical .attenuative), (do_, .superlexical .terminative),
    (iz, .superlexical .completive), (raz, .superlexical .excessive), (pro, .lexical)]⟩

/-- (25g) *do-peja* 'finish singing' has low terminative *do-* on a homogeneous verb. -/
def a25g : Analysis := ⟨Wordlist.f_25g, peja, [(do_, .superlexical .terminative)]⟩

/-- (26a) *po-peja* 'sing for a while' has delimitative *po-* on a simplex atelic verb. -/
def a26a : Analysis := ⟨Wordlist.f_26a, peja, [(po, .superlexical .delimitative)]⟩

/-- (27c) *iz-po-pro-dam* 'sell completely one by one'. -/
def a27c : Analysis :=
  ⟨Wordlist.f_27c, dam,
    [(iz, .superlexical .completive), (po, .superlexical .distributive), (pro, .lexical)]⟩

/-- (28c) *iz-po-raz-kaža* 'narrate completely one by one'. -/
def a28c : Analysis :=
  ⟨Wordlist.f_28c, kazha,
    [(iz, .superlexical .completive), (po, .superlexical .distributive), (raz, .lexical)]⟩

/-- (28d) *iz-po-na-raz-kaža* 'narrate completely many stories one by one'. -/
def a28d : Analysis :=
  ⟨Wordlist.f_28d, kazha, [(iz, .superlexical .completive), (po, .superlexical .distributive),
    (na, .superlexical .cumulative), (raz, .lexical)]⟩

/-- (29) *za-iz-po-na-raz-kaža* 'start narrating many stories one by one'. -/
def a29 : Analysis :=
  ⟨Wordlist.f_29, kazha, [(za, .superlexical .inceptive), (iz, .superlexical .completive),
    (po, .superlexical .distributive), (na, .superlexical .cumulative), (raz, .lexical)]⟩

/-- (33a) *iz-po-pro-četa* 'read through completely little by little'. -/
def a33a : Analysis :=
  ⟨Wordlist.f_33a, cheta,
    [(iz, .superlexical .completive), (po, .superlexical .distributive), (pro, .lexical)]⟩

/-- (34a) *po-za-peja* 'start singing a bit' has attenuative *po-* over low inceptive *za-*. -/
def a34a : Analysis :=
  ⟨Wordlist.f_34a, peja, [(po, .superlexical .attenuative), (za, .superlexical .inceptive)]⟩

/-- (35a) *iz-po-na-reža* 'cut completely into many pieces little by little'. -/
def a35a : Analysis :=
  ⟨Wordlist.f_35a, rezha, [(iz, .superlexical .completive), (po, .superlexical .distributive),
    (na, .superlexical .cumulative)]⟩

/-- The attested stacks. -/
def attested : List Analysis :=
  [a1a, a3a, a3b, a3c, a3d, a3i, a11, a13a, a15, a18a, a18b, a19a, a19b, a20b, a20c, a20d,
   a21a, a21b, a21c, a23b, a23d, a23e, a25a, a25b, a25c, a25d, a25e, a25g, a26a, a27c, a28c,
   a28d, a29, a33a, a34a, a35a]

/-! ### The starred stacks -/

/-- The starred (25b) *pre-do-prodam*, segmented *pre-do-pro-dam*, has repetitive *pre-* above
terminative *do-*. -/
def s25b : Analysis :=
  ⟨Wordlist.f_25b_alt, dam,
    [(pre, .superlexical .repetitive), (do_, .superlexical .terminative), (pro, .lexical)]⟩

/-- Table 3 *na-po-pro-dam* has cumulative *na-* above *po-*. -/
def sNaPo : Analysis :=
  ⟨Wordlist.t3_na_po_pro_dam, dam,
    [(na, .superlexical .cumulative), (po, .superlexical .attenuative), (pro, .lexical)]⟩

/-- Table 3 *raz-po-pro-dam* has excessive *raz-* above *po-*. -/
def sRazPo : Analysis :=
  ⟨Wordlist.t3_raz_po_pro_dam, dam,
    [(raz, .superlexical .excessive), (po, .superlexical .attenuative), (pro, .lexical)]⟩

/-- (29) without *iz-*, *za-po-na-raz-kaža*, has inceptive *za-* above *po-*. -/
def s29 : Analysis :=
  ⟨Wordlist.f_29_alt, kazha, [(za, .superlexical .inceptive), (po, .superlexical .attenuative),
    (na, .superlexical .cumulative), (raz, .lexical)]⟩

/-- Table 2 *pre-na-raz-dam* has repetitive *pre-* above cumulative *na-*. -/
def sPreNa : Analysis :=
  ⟨Wordlist.t2_pre_na_raz_dam, dam,
    [(pre, .superlexical .repetitive), (na, .superlexical .cumulative), (raz, .lexical)]⟩

/-- Table 2 *po-pre-na-raz-dam*. -/
def sPoPreNa : Analysis :=
  ⟨Wordlist.t2_po_pre_na_raz_dam, dam, [(po, .superlexical .attenuative),
    (pre, .superlexical .repetitive), (na, .superlexical .cumulative), (raz, .lexical)]⟩

/-- The starred stacks that reverse two heads of the hierarchy, or place *po-* below another
head without *iz-* above. -/
def starred : List Analysis := [s25b, sNaPo, sRazPo, s29, sPreNa, sPoPreNa]

/-- Every analysis spells out its form: the attested stacks the forms the paper accepts, the
starred ones the forms it rejects. -/
theorem spells : ∀ a ∈ attested ++ starred, Spells a.morphs a.form.form := by decide

/-- The attested stacks are accepted forms and the starred ones rejected forms. -/
theorem judgments :
    (∀ a ∈ attested, a.form.judgment = .acceptable) ∧
      ∀ a ∈ starred, a.form.judgment = .ungrammatical := by
  decide

/-- Every attested stack is well-formed. -/
theorem attested_wellFormed : ∀ a ∈ attested, WellFormed a.prefixes := by decide

/-- The starred stacks are ill-formed. -/
theorem starred_not_wellFormed : ∀ a ∈ starred, ¬ WellFormed a.prefixes := by decide

theorem starred_distributive_not_wellFormed :
    ¬ WellFormed [(na, .superlexical .cumulative), (po, .superlexical .distributive),
      (pro, .lexical)] ∧
    ¬ WellFormed [(raz, .superlexical .excessive), (po, .superlexical .distributive),
      (pro, .lexical)] ∧
    ¬ WellFormed [(za, .superlexical .inceptive), (po, .superlexical .distributive),
      (na, .superlexical .cumulative), (raz, .lexical)] := by
  decide

/-! ### The phase-verb test, (17) -/

/-- A gloss marks the imperfective, *-IMPF*. -/
def GlossesImperfective (g : String) : Prop := "IMPF".toList <:+ g.toList

instance : DecidablePred GlossesImperfective := fun _ ↦ inferInstanceAs (Decidable (_ <:+ _))

/-- The perfectivity of the complement of a phase verb, imperfective where the paper glosses the
last word of the sentence *-IMPF*. -/
def complementPerfectivity (d : Datum) : Option Aspect.Perfectivity :=
  if ∃ g ∈ d.glossLine.getLast?, GlossesImperfective g then some .imperfective else none

/-- The sentences (17), *započna* 'started' with a complement in *-va-*. -/
def phaseTests : List Datum := [Examples.ex_17a, Examples.ex_17b]

/-- The phase-verb test is necessary for (17) but not sufficient, since it also admits the rejected
(17b). -/
theorem phaseTests_necessary :
    (∀ d ∈ phaseTests, d.judgment = .acceptable →
      (complementPerfectivity d).map Aspect.viewpointPrediction = some .accept) ∧
    ∃ d ∈ phaseTests, (complementPerfectivity d).map Aspect.viewpointPrediction = some .accept ∧
      d.judgment = .ungrammatical := by
  decide

end Istratkova2004
