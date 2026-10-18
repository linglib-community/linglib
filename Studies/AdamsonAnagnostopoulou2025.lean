module

public import Linglib.Syntax.Minimalist.Agree.Coordination
public import Mathlib.Data.List.Iterate
public import Linglib.Syntax.WordOrder
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Fragments.Greek.StandardModern.Gender
public import Linglib.Fragments.Icelandic.Nouns
public import Linglib.Fragments.Slavic.Serbian.Gender
public import Linglib.Data.Examples.AdamsonAnagnostopoulou2025
public import Studies.Corbett1991
public import Mathlib.Tactic.DeriveFintype

/-!
# Adamson and Anagnostopoulou (2025): Gender Features and Coordination Resolution in Greek and Other Three-Gendered Languages

Adamson and Anagnostopoulou derive the resolution of gender on coordinated nominals in Greek,
Icelandic, and Bosnian/Croatian/Serbian from three components and no default insertion: a
language-particular geometry of privative gender features, a dual-feature system in which
interpretable features go to LF and uninterpretable ones to PF, and the universal mechanism of
percolation and conversion (`Minimalist.Coordination.resolve`). A system (`System`) fixes the
geometry, the node each referent type and each grammatical gender contributes, and the vocabulary of
inflectional exponents; every derivation is then a computation. A nominal (`System.nominal`) bears
the interpretable features of its referent and, unless its noun's gender is its referents', the
uninterpretable features of that gender, and conversion reads the referents alone
(`System.converted_nominal`). In Greek, where FEM entails MASC, mismatched humans keep MASC and
resolve masculine while inanimates, whose only interpretable feature is CLASS, resolve neuter
(`Greek.human_mismatch`, `Greek.inanimate_mismatch`), and the fixed-gender nouns *koritsi*,
*megalofiia* and *thima* resolve by their referents while their determiners agree with their gender
(`Greek.woman_girl`, `Greek.genius_sister`, `Greek.victim_mother`). Uninterpretable features are
realized set by set: uniform inanimates converge on their shared exponent
(`Greek.inanimate_uniform`), mismatched ones do not (`Greek.inanimate_clash`), and a human
coordinated with an inanimate is grammatical exactly when the human's interpretable features and the
inanimate's uninterpretable ones receive the same exponent (`Greek.human_inanimate_match`,
`Greek.human_inanimate_crash`, `Greek.victim_painting`). Neuter is the least specified gender, so it
realizes clausal subjects (`Greek.clausal`), and the vocabulary's containment rules out a
neuter–feminine syncretism that excludes the masculine (`Greek.no_aba`, from
`RuleSet.Realizes.of_realizes`).

Icelandic differs only in its geometry, with MASC meaning male and FEM independent of it, so
mismatched humans resolve neuter (`Icelandic.human_mismatch`) while fixed-gender *skáld* still
resolves by its referent (`Icelandic.poet_jon`). Corbett's resolution rule for Icelandic reads
the genders alone and takes the neuter for any mixture; the geometry agrees with it on his
coordinations (`Icelandic.corbett_rows`) and parts from it on *skáld*, which the rule resolves
by its neuter gender and the geometry by its referent (`Icelandic.corbett_skald_jon`). In
Bosnian/Croatian/Serbian MASC sits under INDIV, ANIM under MASC, and neuter is mass; a plural
coordination bears GRP and hence INDIV (`System.plural`), so every coordination realizes
masculine, even of two neuters (`BCS.human_mismatch`, `BCS.inanimate_mismatch`,
`BCS.neuter_pair`). Every node of the three geometries entails CLASS, so they satisfy mismatch
resolution (`mismatchResolution`), and Table 2 follows from the geometries alone (`table2`).

## Implementation notes

A geometry is given by its parent map on the six gender nodes, rooted in CLASS; the nodes a
language does not use hang from CLASS and are never contributed.

A nominal pairs a fragment noun with the referent the paper's example gives it, the man, woman or
inanimate its margin notation marks. Each theorem names the derivation it computes, so the paper's
percolation generalization, that humans percolate interpretable features and inanimates either
kind, is respected in the choice of derivation rather than derived.

## References

* [adamson-anagnostopoulou-2025]
* [smith-2015]
* [harley-ritter-2002]
* [kramer-2015]
* [halle-1997]
* [harbour-2016]
* [bobaljik-2012]
* [corbett-1991]
-/

@[expose] public section

namespace AdamsonAnagnostopoulou2025

open Minimalist.Coordination DistributedMorphology Morphology.Exponence

/-- The privative gender nodes of the three geometries. -/
inductive Node where
  | cls
  | masc
  | fem
  | indiv
  | grp
  | anim
  deriving DecidableEq, Repr, Fintype

/-- The nodes in a fixed order, the listing a feature set takes to the list-based vocabulary
sites. -/
def Node.all : List Node := [.cls, .masc, .fem, .indiv, .grp, .anim]

/-- What a nominal refers to, a man, a woman, an individuated inanimate, or a mass. -/
inductive Referent where
  | man
  | woman
  | thing
  | mass
  deriving DecidableEq, Repr

/-- A three-gender system is a geometry, given by the node each node depends on directly, the node
a referent contributes as interpretable gender and a grammatical gender contributes as
uninterpretable gender, the features a plural coordination adds, and a vocabulary. -/
structure System where
  parent : Node → Node
  iNode : Referent → Node
  uNode : Gender → Node
  plural : Finset Node := ∅
  vocabulary : RuleSet (VocabularyItem Node Gender)

namespace System

variable (L : System)

/-- A node entails itself and the nodes it depends on, read up the parent map. -/
def entailments (n : Node) : Finset Node := (List.iterate L.parent n (Fintype.card Node)).toFinset

/-- The interpretable features of a nominal with referent `r`. -/
def conceptual (r : Referent) : Bundle Node := .ofInterp (L.entailments (L.iNode r))

/-- The uninterpretable features of a nominal of grammatical gender `g`. -/
def arbitrary (g : Gender) : Bundle Node := .ofUninterp (L.entailments (L.uNode g))

/-- A nominal headed by `n` and referring to `r` bears the interpretable features of `r` and,
unless the gender of `n` is its referents', the uninterpretable features of that gender. -/
def nominal (n : GenderedNoun Gender) (r : Referent) : Bundle Node :=
  if n.IsNaturalGender id then L.conceptual r else L.conceptual r ∪ L.arbitrary n.gender

/-- The exponent of a feature set under the Subset Principle. -/
def realize (fs : Finset Node) : Option Gender :=
  subsetPrinciple L.vocabulary fs

/-- The exponent of a nominal's own gender, as on its determiner, its features at PF
realized. -/
def exponent (b : Bundle Node) : Option Gender := L.realize b.toPF

/-- Resolution through conversion, the percolated interpretable features intersected and the
result, with the coordination's plural features, realized; the intersection is nonempty by
mismatch resolution. -/
def converted (a b : Bundle Node) : Option Gender := L.realize (resolve a b ∪ L.plural)

/-- Resolution of two nominals by their referents. -/
def resolved (r₁ r₂ : Referent) : Option Gender := L.converted (L.conceptual r₁) (L.conceptual r₂)

/-- Resolution through uninterpretable features, each conjunct's set realized, converging on
one exponent or crashing. -/
def formal (a b : Bundle Node) : Option Gender := realizeAll L.realize [a.uninterp, b.uninterp]

/-- A human's percolated interpretable features beside an inanimate's uninterpretable ones. The
redundancy rule copies the former to PF, and both sets are realized. -/
def mixed (human inan : Bundle Node) : Option Gender :=
  realizeAll L.realize [human.interp, inan.uninterp]

@[simp] theorem interp_nominal (n : GenderedNoun Gender) (r : Referent) :
    (L.nominal n r).interp = (L.conceptual r).interp := by
  unfold nominal; split_ifs <;> simp [conceptual, arbitrary]

/-- Conversion reads the referents alone, so two nominals resolve as their referents do whatever
their nouns' genders. -/
theorem converted_nominal (n₁ n₂ : GenderedNoun Gender) (r₁ r₂ : Referent) :
    L.converted (L.nominal n₁ r₁) (L.nominal n₂ r₂) = L.resolved r₁ r₂ := by
  simp only [converted, resolved, resolve, interp_nominal]

end System

/-- The three-way vocabulary shared by Greek and Icelandic. -/
def threeWay : RuleSet (VocabularyItem Node Gender) :=
  [{.fem, .masc} ⟷ .feminine, {.masc} ⟷ .masculine, ∅ ⟷ .neuter]

/-! ### Greek -/

namespace Greek

open _root_.Greek.StandardModern.Gender

/-- CLASS > MASC > FEM. -/
def system : System where
  parent
    | .fem => .masc
    | _ => .cls
  iNode
    | .man => .masc
    | .woman => .fem
    | _ => .cls
  uNode
    | .masculine => .masc
    | .feminine => .fem
    | _ => .cls
  vocabulary := threeWay

theorem masc_mem_entailments_fem : .masc ∈ system.entailments .fem := by decide

/-- Uniform humans resolve to their shared gender, as in *i Maria ke i Giota* and *o Petros ke o
Kostas*. -/
theorem human_uniform :
    system.converted (system.nominal maria .woman) (system.nominal giota .woman) =
        some .feminine ∧
      system.converted (system.nominal petros .man) (system.nominal kostas .man) =
        some .masculine := by
  decide

/-- In *o andras ke i gineka ine eksipni* FEM is lost and MASC kept. -/
theorem human_mismatch :
    system.converted (system.nominal andras .man) (system.nominal gineka .woman) =
      some .masculine := by
  decide

/-- *I gineka ke to koritsi ine eksipnes*, where the neuter *koritsi* resolves by its female
referent. -/
theorem woman_girl :
    system.exponent (system.nominal koritsi .woman) = some .neuter ∧
      system.converted (system.nominal gineka .woman) (system.nominal koritsi .woman) =
        some .feminine := by
  decide

/-- *I megalofiia ke i adherfi tu ine charumeni*, where two grammatically feminine nouns resolve
masculine because the genius is a man. -/
theorem genius_sister :
    system.exponent (system.nominal megalofiia .man) = some .feminine ∧
      system.exponent (system.nominal adherfi .woman) = some .feminine ∧
      system.converted (system.nominal megalofiia .man) (system.nominal adherfi .woman) =
        some .masculine := by
  decide

/-- *To thima ke i mitera tis ine charumenes*, where the neuter *thima* resolves feminine for a
woman. -/
theorem victim_mother :
    system.exponent (system.nominal thima .woman) = some .neuter ∧
      system.converted (system.nominal thima .woman) (system.nominal mitera .woman) =
        some .feminine := by
  decide

/-- Uniform inanimates realize their shared arbitrary gender. -/
theorem inanimate_uniform :
    system.formal (system.nominal fusta .thing) (system.nominal bluza .thing) = some .feminine ∧
      system.formal (system.nominal anaptiras .thing) (system.nominal fakos .thing) =
        some .masculine ∧
      system.formal (system.nominal piruni .thing) (system.nominal kutali .thing) =
        some .neuter := by
  decide

/-- Mismatched inanimates resolve neuter through their interpretable CLASS. -/
theorem inanimate_mismatch :
    system.converted (system.nominal pinakas .thing) (system.nominal karekla .thing) =
        some .neuter ∧
      system.converted (system.nominal scholio .thing) (system.nominal ekklisia .thing) =
        some .neuter ∧
      system.converted (system.nominal balkoni .thing) (system.nominal dhiadhromos .thing) =
        some .neuter := by
  decide

/-- Percolating their uninterpretable features instead clashes at PF. -/
theorem inanimate_clash :
    system.formal (system.nominal pinakas .thing) (system.nominal karekla .thing) = none ∧
      system.formal (system.nominal scholio .thing) (system.nominal ekklisia .thing) = none := by
  decide

/-- Uniform inanimates may also percolate CLASS and resolve neuter. -/
theorem inanimate_uniform_neuter :
    system.converted (system.nominal fusta .thing) (system.nominal bluza .thing) =
      some .neuter := by
  decide

/-- Closest conjunct agreement is with the PF features of the conjunct next to the predicate,
which precedes the subject, so it is feminine for *i megalofiia ke o filos tu* whatever the
genius's referent ((45)) and masculine, not the neuter of CLASS, for *o pinakas ke i karekla*
((46)). -/
theorem closest_conjunct :
    (HeadDirection.headInitial.nearest
        [system.nominal megalofiia .man, system.nominal filos .man]).bind system.exponent =
      some .feminine ∧
    (HeadDirection.headInitial.nearest
        [system.nominal pinakas .thing, system.nominal karekla .thing]).bind system.exponent =
      some .masculine := by
  decide

/-- *O kleftis ke to daxtilidi* and *o Giorgos ke to pukamiso tu*, where the man's MASC and the
neuter's CLASS clash at PF; the paper excludes the remaining, all-interpretable option at LF. -/
theorem human_inanimate_crash :
    system.mixed (system.nominal kleftis .man) (system.nominal daxtilidi .thing) = none ∧
      system.mixed (system.nominal giorgos .man) (system.nominal pukamiso .thing) = none ∧
      resolve (system.nominal kleftis .man) (system.nominal daxtilidi .thing) = {.cls} := by
  decide

/-- Matched humans and inanimates converge, as in *o kleftis ke o pinakas* and *i gineka ke i
ombrela*. -/
theorem human_inanimate_match :
    system.mixed (system.nominal kleftis .man) (system.nominal pinakas .thing) =
        some .masculine ∧
      system.mixed (system.nominal gineka .woman) (system.nominal ombrela .thing) =
        some .feminine := by
  decide

/-- The fixed-gender *megalofiia* and *thima* match an inanimate by their referents, as in
*i megalofiia ke o pinakas tu*, *to thima ke o pinakas tu* and *to thima ke i fotografia tis*,
and a victim who is a man does not match a feminine inanimate. -/
theorem victim_painting :
    system.mixed (system.nominal megalofiia .man) (system.nominal pinakas .thing) =
        some .masculine ∧
      system.mixed (system.nominal thima .man) (system.nominal pinakas .thing) =
        some .masculine ∧
      system.mixed (system.nominal thima .woman) (system.nominal fotografia .thing) =
        some .feminine ∧
      system.mixed (system.nominal thima .man) (system.nominal fotografia .thing) = none := by
  decide

/-- Clausal subjects bear no gender features and are realized neuter. -/
theorem clausal : system.realize ∅ = some .neuter := by decide

/-- No neuter–feminine syncretism to the exclusion of masculine, for any vocabulary with one
item per exponent over the Greek feature sets. -/
theorem no_aba (v : RuleSet (VocabularyItem Node Gender)) (hv : v.Antihomophonous) {φ : Gender}
    (hn : v.Realizes (Neighborhood.ofBundle {.cls}) φ)
    (hf : v.Realizes (Neighborhood.ofBundle {.fem, .masc, .cls}) φ) :
    v.Realizes (Neighborhood.ofBundle {.masc, .cls}) φ :=
  RuleSet.Realizes.of_realizes hv (fun _ _ h ↦ VocabularyItem.applies_mono h (by decide))
    (fun _ _ h ↦ VocabularyItem.applies_mono h (by decide)) hn hf

end Greek

/-! ### Icelandic -/

namespace Icelandic

open _root_.Icelandic.Nouns

/-- CLASS above independent MASC and FEM. -/
def system : System where
  parent _ := .cls
  iNode
    | .man => .masc
    | .woman => .fem
    | _ => .cls
  uNode
    | .masculine => .masc
    | .feminine => .fem
    | _ => .cls
  vocabulary := threeWay

theorem masc_not_mem_entailments_fem : .masc ∉ system.entailments .fem := by decide

/-- *Maðurinn og konan eru þreytt*, where only CLASS survives. -/
theorem human_mismatch :
    system.converted (system.nominal madur .man) (system.nominal kona .woman) =
      some .neuter := by
  decide

/-- *Skáldið og Jón eru frægir*, where the neuter *skáld* resolves masculine for a man. -/
theorem poet_jon :
    system.exponent (system.nominal skald .man) = some .neuter ∧
      system.converted (system.nominal skald .man) (system.nominal jon .man) =
        some .masculine := by
  decide

/-- *Frægð og frami eru tvíeggjuð*. -/
theorem inanimate_mismatch :
    system.converted (system.nominal fraegd .thing) (system.nominal frami .thing) =
        some .neuter ∧
      system.formal (system.nominal fraegd .thing) (system.nominal frami .thing) = none := by
  decide

/-! #### Corbett's rule

[corbett-1991]'s rule for Icelandic reads the conjuncts' genders alone
(`Corbett1991.Icelandic.rules`): homogeneous masculines or feminines keep their gender and any
mixture takes the neuter. The geometry reads referents instead, so the two agree wherever the
gender is the referent's and part where it is not. -/

/-- On Corbett's coordinations the rule and the geometry agree. The boy and the girl resolve
neuter as mismatched humans, and the ewe and the lamb, which contribute CLASS alone as the
paper's inanimates do, resolve neuter through it. -/
theorem corbett_rows :
    Agreement.ResolutionRule.resolve Corbett1991.Icelandic.rules [drengur.gender, telpa.gender] =
        some .neuter ∧
      system.converted (system.nominal drengur .man) (system.nominal telpa .woman) =
        some .neuter ∧
      Agreement.ResolutionRule.resolve Corbett1991.Icelandic.rules [aer.gender, lamb.gender] =
        some .neuter ∧
      system.converted (system.nominal aer .thing) (system.nominal lamb .thing) =
        some .neuter := by
  decide

/-- In *skáldið og Jón eru frægir* the rule resolves the neuter *skáld* and the masculine *Jón*
to the neuter, and the geometry to the masculine of the two men. -/
theorem corbett_skald_jon :
    Agreement.ResolutionRule.resolve Corbett1991.Icelandic.rules [skald.gender, jon.gender] =
        some .neuter ∧
      system.converted (system.nominal skald .man) (system.nominal jon .man) =
        some .masculine := by
  decide

end Icelandic

/-! ### Bosnian/Croatian/Serbian -/

namespace BCS

open _root_.Serbian.Gender

/-- CLASS > INDIV > {GRP, MASC > ANIM > FEM}; a plural coordination bears GRP, and with it
INDIV. -/
def system : System where
  parent
    | .fem => .anim
    | .anim => .masc
    | .masc | .grp => .indiv
    | _ => .cls
  iNode
    | .man => .anim
    | .woman => .fem
    | .thing => .masc
    | .mass => .cls
  uNode
    | .masculine => .masc
    | .feminine => .fem
    | _ => .cls
  plural := {.grp, .indiv, .cls}
  vocabulary :=
    [{.fem, .anim, .masc, .indiv} ⟷ .feminine, {.anim, .masc, .indiv} ⟷ .masculine,
      {.indiv} ⟷ .masculine, ∅ ⟷ .neuter]

/-- An inanimate refers as a mass when it is neuter, the neuter being the mass gender, and as an
individuated thing otherwise. -/
def inanimate (n : GenderedNoun Gender) : Bundle Node :=
  system.nominal n (if n.gender = .neuter then .mass else .thing)

/-- *Muškarac i žena su sretni*. -/
theorem human_mismatch :
    system.converted (system.nominal muskarac .man) (system.nominal zena .woman) =
      some .masculine := by
  decide

/-- Uniform women still resolve feminine. -/
theorem women : system.resolved .woman .woman = some .feminine := by decide

/-- In *znanje i intuicija su saradivali* the INDIV from the coordination's GRP realizes
masculine. -/
theorem inanimate_mismatch :
    system.converted (inanimate znanje) (inanimate intuicija) = some .masculine := by
  decide

/-- *Naše selo i celo jedno brdo su izgoreli*, where two neuters resolve masculine. -/
theorem neuter_pair : system.converted (inanimate selo) (inanimate brdo) = some .masculine := by
  decide

/-- Neuter alone is mass, so without GRP it stays neuter. -/
theorem neuter_mass : system.realize (system.entailments .cls) = some .neuter := by decide

end BCS

/-! ### The geometries -/

/-- Every node of the three geometries entails CLASS. -/
theorem cls_mem_entailments :
    ∀ L ∈ [Greek.system, Icelandic.system, BCS.system], ∀ n, .cls ∈ L.entailments n := by
  decide

/-- All three geometries satisfy mismatch resolution, since any two nodes share CLASS and so no
pair of nodes needs a default. -/
theorem mismatchResolution :
    ∀ L ∈ [Greek.system, Icelandic.system, BCS.system], ∀ a b,
      (L.entailments a ∩ L.entailments b).Nonempty := fun L hL a b ↦
  ⟨.cls, Finset.mem_inter.2 ⟨cls_mem_entailments L hL a, cls_mem_entailments L hL b⟩⟩

/-- The resolution of mismatched humans and of mismatched inanimates in Greek, Icelandic, and
Bosnian/Croatian/Serbian (Table 2). -/
theorem table2 :
    [Greek.system, Icelandic.system, BCS.system].map
        (fun L ↦ (L.resolved .man .woman, L.resolved .thing .thing)) =
      [(some .masculine, some .neuter), (some .neuter, some .neuter),
        (some .masculine, some .masculine)] := by
  decide

end AdamsonAnagnostopoulou2025
