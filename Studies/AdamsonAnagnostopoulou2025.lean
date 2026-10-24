module

public import Linglib.Syntax.Minimalist.Feature.DualFeature
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
percolation and conversion (`Minimalist.DualFeature.resolve`). A system (`System`) fixes the
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

open Minimalist.DualFeature DistributedMorphology Morphology.Exponence

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

/-- A three-gender system over a language's genders `G` is a geometry, given by the node each
node depends on directly, the node a referent contributes as interpretable gender and a
grammatical gender contributes as uninterpretable gender, the features a plural coordination
adds, a vocabulary, and the comparative label of each gender. -/
structure System (G : Type*) where
  parent : Node → Node
  iNode : Referent → Node
  uNode : G → Node
  plural : Finset Node := ∅
  vocabulary : RuleSet (VocabularyItem Node G)
  label : G → Gender

namespace System

variable {G : Type*} (L : System G)

/-- A node entails itself and the nodes it depends on, read up the parent map. -/
def entailments (n : Node) : Finset Node := (List.iterate L.parent n (Fintype.card Node)).toFinset

/-- The interpretable features of a nominal with referent `r`. -/
def conceptual (r : Referent) : Bundle Node := .ofInterp (L.entailments (L.iNode r))

/-- The uninterpretable features of a nominal of grammatical gender `g`. -/
def arbitrary (g : G) : Bundle Node := .ofUninterp (L.entailments (L.uNode g))

/-- A nominal headed by `n` and referring to `r` bears the interpretable features of `r` and,
unless the gender of `n` is its referents', the uninterpretable features of that gender. -/
def nominal (n : GenderedNoun G) (r : Referent) : Bundle Node :=
  if n.IsNaturalGender L.label then L.conceptual r else L.conceptual r ∪ L.arbitrary n.gender

/-- The exponent of a feature set under the Subset Principle. -/
def realize (fs : Finset Node) : Option G :=
  subsetPrinciple L.vocabulary fs

/-- The exponent of a nominal's own gender, as on its determiner, its features at PF
realized. -/
def exponent (b : Bundle Node) : Option G := L.realize b.toPF

/-- Resolution through conversion, the percolated interpretable features intersected and the
result, with the coordination's plural features, realized; the intersection is nonempty by
mismatch resolution. -/
def converted (a b : Bundle Node) : Option G := L.realize (resolve a b ∪ L.plural)

/-- Resolution of two nominals by their referents. -/
def resolved (r₁ r₂ : Referent) : Option G := L.converted (L.conceptual r₁) (L.conceptual r₂)

/-- The comparative label of the resolution of two nominals by their referents, the terms in
which languages' resolutions compare. -/
def resolvedLabel (r₁ r₂ : Referent) : Option Gender := (L.resolved r₁ r₂).map L.label

/-- Resolution through uninterpretable features, each conjunct's set realized, converging on
one exponent or crashing. -/
def formal [DecidableEq G] (a b : Bundle Node) : Option G :=
  realizeAll L.realize [a.uninterp, b.uninterp]

/-- A human's percolated interpretable features beside an inanimate's uninterpretable ones. The
redundancy rule copies the former to PF, and both sets are realized. -/
def mixed [DecidableEq G] (human inan : Bundle Node) : Option G :=
  realizeAll L.realize [human.interp, inan.uninterp]

@[simp] theorem interp_nominal (n : GenderedNoun G) (r : Referent) :
    (L.nominal n r).interp = (L.conceptual r).interp := by
  unfold nominal; split_ifs <;> simp [conceptual, arbitrary]

theorem converted_nominal (n₁ n₂ : GenderedNoun G) (r₁ r₂ : Referent) :
    L.converted (L.nominal n₁ r₁) (L.nominal n₂ r₂) = L.resolved r₁ r₂ := by
  simp only [converted, resolved, resolve, interp_nominal]

end System

/-- The three-way vocabulary shared by Greek and Icelandic, over a language's masculine,
feminine and neuter. -/
def threeWay {G : Type*} (masculine feminine neuter : G) : RuleSet (VocabularyItem Node G) :=
  [{.fem, .masc} ⟷ feminine, {.masc} ⟷ masculine, ∅ ⟷ neuter]

/-! ### Greek -/

namespace Greek

open _root_.Greek.StandardModern.Gender

/-- CLASS > MASC > FEM. -/
def system : System Value where
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
  vocabulary := threeWay .masculine .feminine .neuter
  label := Value.toLabel

theorem masc_mem_entailments_fem : .masc ∈ system.entailments .fem := by decide

theorem human_uniform :
    system.converted (system.nominal maria .woman) (system.nominal giota .woman) =
        some .feminine ∧
      system.converted (system.nominal petros .man) (system.nominal kostas .man) =
        some .masculine := by
  decide

theorem human_mismatch :
    system.converted (system.nominal andras .man) (system.nominal gineka .woman) =
      some .masculine := by
  decide

theorem woman_girl :
    system.exponent (system.nominal koritsi .woman) = some .neuter ∧
      system.converted (system.nominal gineka .woman) (system.nominal koritsi .woman) =
        some .feminine := by
  decide

theorem genius_sister :
    system.exponent (system.nominal megalofiia .man) = some .feminine ∧
      system.exponent (system.nominal adherfi .woman) = some .feminine ∧
      system.converted (system.nominal megalofiia .man) (system.nominal adherfi .woman) =
        some .masculine := by
  decide

theorem victim_mother :
    system.exponent (system.nominal thima .woman) = some .neuter ∧
      system.converted (system.nominal thima .woman) (system.nominal mitera .woman) =
        some .feminine := by
  decide

theorem inanimate_uniform :
    system.formal (system.nominal fusta .thing) (system.nominal bluza .thing) = some .feminine ∧
      system.formal (system.nominal anaptiras .thing) (system.nominal fakos .thing) =
        some .masculine ∧
      system.formal (system.nominal piruni .thing) (system.nominal kutali .thing) =
        some .neuter := by
  decide

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

theorem inanimate_uniform_neuter :
    system.converted (system.nominal fusta .thing) (system.nominal bluza .thing) =
      some .neuter := by
  decide

/-- Closest conjunct agreement takes the PF features of the conjunct next to the predicate ((45),
(46)). -/
theorem closest_conjunct :
    (HeadDirection.headInitial.nearest
        [system.nominal megalofiia .man, system.nominal filos .man]).bind system.exponent =
      some .feminine ∧
    (HeadDirection.headInitial.nearest
        [system.nominal pinakas .thing, system.nominal karekla .thing]).bind system.exponent =
      some .masculine := by
  decide

theorem human_inanimate_crash :
    system.mixed (system.nominal kleftis .man) (system.nominal daxtilidi .thing) = none ∧
      system.mixed (system.nominal giorgos .man) (system.nominal pukamiso .thing) = none ∧
      resolve (system.nominal kleftis .man) (system.nominal daxtilidi .thing) = {.cls} := by
  decide

theorem human_inanimate_match :
    system.mixed (system.nominal kleftis .man) (system.nominal pinakas .thing) =
        some .masculine ∧
      system.mixed (system.nominal gineka .woman) (system.nominal ombrela .thing) =
        some .feminine := by
  decide

theorem victim_painting :
    system.mixed (system.nominal megalofiia .man) (system.nominal pinakas .thing) =
        some .masculine ∧
      system.mixed (system.nominal thima .man) (system.nominal pinakas .thing) =
        some .masculine ∧
      system.mixed (system.nominal thima .woman) (system.nominal fotografia .thing) =
        some .feminine ∧
      system.mixed (system.nominal thima .man) (system.nominal fotografia .thing) = none := by
  decide

theorem clausal : system.realize ∅ = some .neuter := by decide

theorem no_aba (v : RuleSet (VocabularyItem Node Value)) (hv : v.Antihomophonous) {φ : Value}
    (hn : v.Realizes applySet (Neighborhood.ofBundle {.cls}) φ)
    (hf : v.Realizes applySet (Neighborhood.ofBundle {.fem, .masc, .cls}) φ) :
    v.Realizes applySet (Neighborhood.ofBundle {.masc, .cls}) φ :=
  RuleSet.Realizes.of_realizes hv (fun _ _ h ↦ VocabularyItem.applies_mono h (by decide))
    (fun _ _ h ↦ VocabularyItem.applies_mono h (by decide)) hn hf

end Greek

/-! ### Icelandic -/

namespace Icelandic

open _root_.Icelandic.Nouns

/-- CLASS above independent MASC and FEM. -/
def system : System _root_.Icelandic.Gender.Value where
  parent _ := .cls
  iNode
    | .man => .masc
    | .woman => .fem
    | _ => .cls
  uNode
    | .masculine => .masc
    | .feminine => .fem
    | _ => .cls
  vocabulary := threeWay .masculine .feminine .neuter
  label := _root_.Icelandic.Gender.Value.toLabel

theorem masc_not_mem_entailments_fem : .masc ∉ system.entailments .fem := by decide

theorem human_mismatch :
    system.converted (system.nominal madur .man) (system.nominal kona .woman) =
      some .neuter := by
  decide

theorem poet_jon :
    system.exponent (system.nominal skald .man) = some .neuter ∧
      system.converted (system.nominal skald .man) (system.nominal jon .man) =
        some .masculine := by
  decide

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
def system : System Value where
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
  label := Value.toLabel

/-- An inanimate refers as a mass when it is neuter, the neuter being the mass gender, and as an
individuated thing otherwise. -/
def inanimate (n : GenderedNoun Value) : Bundle Node :=
  system.nominal n (if n.gender = .neuter then .mass else .thing)

theorem human_mismatch :
    system.converted (system.nominal muskarac .man) (system.nominal zena .woman) =
      some .masculine := by
  decide

theorem women : system.resolved .woman .woman = some .feminine := by decide

theorem inanimate_mismatch :
    system.converted (inanimate znanje) (inanimate intuicija) = some .masculine := by
  decide

theorem neuter_pair : system.converted (inanimate selo) (inanimate brdo) = some .masculine := by
  decide

theorem neuter_mass : system.realize (system.entailments .cls) = some .neuter := by decide

end BCS

/-! ### The geometries -/

theorem cls_mem_entailments :
    ∀ e ∈ [Greek.system.entailments, Icelandic.system.entailments, BCS.system.entailments], ∀ n,
      .cls ∈ e n := by
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  decide

theorem mismatchResolution :
    ∀ e ∈ [Greek.system.entailments, Icelandic.system.entailments, BCS.system.entailments],
      ∀ a b, (e a ∩ e b).Nonempty := fun e he a b ↦
  ⟨.cls, Finset.mem_inter.2 ⟨cls_mem_entailments e he a, cls_mem_entailments e he b⟩⟩

/-- The resolution of mismatched humans and of mismatched inanimates in Greek, Icelandic, and
Bosnian/Croatian/Serbian (Table 2). -/
theorem table2 :
    [Greek.system.resolvedLabel, Icelandic.system.resolvedLabel, BCS.system.resolvedLabel].map
        (fun f ↦ (f .man .woman, f .thing .thing)) =
      [(some .masculine, some .neuter), (some .neuter, some .neuter),
        (some .masculine, some .masculine)] := by
  decide

end AdamsonAnagnostopoulou2025
