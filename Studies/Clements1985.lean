module

public import Linglib.Fragments.English.Phonology
public import Linglib.Core.Data.Fintype.Order
public import Mathlib.Data.Fintype.Card
public import Linglib.Phonology.FeatureGeometry
public import Mathlib.Data.List.Iterate
public import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Clements (1985): the geometry of phonological features

Clements replaces the SPE feature matrix by a tree of class nodes, his (3): a root node linked to
the CV tier, a laryngeal and a supralaryngeal node below it, and a manner and a place node below
supralaryngeal, with each terminal feature hanging from one class node (§4). Assimilation spreads
a single node ((5), after Mohanan), so it is total (the root), partial (a class node) or
single-feature. A rule that reaches a manner feature and a place feature therefore assimilates
the whole supralaryngeal class. This is why the SPE rule (14) for English coronal place
assimilation ((10)–(13)) is ordinary and its variant with `[αnasal]` for `[αanterior]` is
unattested, and why the Kikuyu and palatalisation rules of §5 have to be decomposed. Icelandic
preaspiration ((6)–(7), after Thráinsson), Klamath ((8)–(9), after Barker) and Sierra Popoluca
((15)–(20), after Elson, with Steriade's Shared Features Convention) are the evidence for the
supralaryngeal node. §4 splits the place features into a primary set P, present in consonants
and vowels, and a secondary set S, normally absent from plain consonants. The tree is an instance
of `Phonology/FeatureGeometry.lean`; its manner node, which the paper flags as possibly
superfluous, is dropped by the later geometries formalized here (`Studies/Sagey1986.lean`,
`Studies/HalleVauxWolfe2000.lean`).

## Main definitions

* `Node`, `Node.pred`, `classNode?` — the five class nodes of (3), the tree, and the class
  node each terminal feature hangs from (§4); together the `FeatureGeometry` instance.
* `PlaceSet`, `placeSet?`, `PlaceSet.features` — the primary/secondary split of the place
  features (§4).
* `Spreading`, `Spreading.features`, `Spreading.apply` — what one rule may spread, the
  root, a class node or one feature ((5)), and the assimilation it effects.
* `r` — the English /r/ of table (10).
* `rule12`, `rule14`, `rule14Nasal` — the English rule (12) as a local rewrite rule spreading
  the place node, its SPE statement (14) copying `[anterior]` and `[distributed]`, and the
  `[αnasal]` variant the paper contrasts with it.

## Main results

* `supralaryngeal_subset_of_manner_of_place`, `eq_root_of_manner_of_laryngeal` — a spreading
  that reaches a manner and a place feature carries the whole supralaryngeal class, and one that
  reaches a manner and a laryngeal feature is the root; `no_spreading_nasal_distributed` (the
  `[αnasal]` variant of (14)), `eq_root_of_continuant_of_voice` (Kikuyu, §5.1) and
  `supralaryngeal_subset_of_anterior_of_continuant` (palatalisation, §5.2) are instances.
* `naturalClass_rule12_target`, `rule12_θ`, `rule12_esh`, `rule12_r` — the targets of (12) are
  /t d n/, and the three rows of table (11): before /θ/, /ʃ/ and /r/ they take the trigger's
  place features and nothing else, becoming interdental, postalveolar and retroflex;
  `rule12_n_p` and `rule12_s_θ` are the non-sites.
* `rule14_eq_rule12`, `rule14Nasal_n_θ` — (14) agrees with (12) on table (11), while its
  `[αnasal]` variant is a rule of the same form that applies, making /n/ an oral dental.
* `preaspiration` — spreading the vowel's supralaryngeal node onto the delinked first half
  of an aspirated geminate keeps the stop's laryngeal features ((7)), by the substrate's
  disjointness of sister classes.
* `mem_place_featureClass_iff`, `primary_separates_stops` — the place features are P ∪ S,
  and P alone separates /p t k/, as in table (22).

## Implementation notes

`classNode?` is defined on the features the paper names and is `none` elsewhere, so the
root's feature class is the paper's inventory rather than all of Hayes's; `[labial]`
counts as primary by table (22). Spreading is `Finset.piecewise` on a node's feature class,
so the trigger's unspecified features under the node replace the target's, as the delinking
convention of (13) requires; single-feature spreading is `Function.update`
(`Spreading.apply_feature`). The English segments are the Fragment's, except /r/: the
Fragment's /ɹ/ is PHOIBLE's, [−consonantal, −anterior, +distributed], where table (10) makes /r/
[−distributed] and (11) makes it a trigger of (12), whose trigger is [+consonantal], as liquids
are in SPE. The SPE rule (14) is `Effect.copyRight` on the two-feature set and (12) the same
effect on the place class, so the comparison is between the sets a rule may copy, not between
formalisms.

## TODO

* The Sierra Popoluca release argument ((17)–(20)): the Shared Features Convention merges
  the two `[−continuant]` nodes of a homorganic cluster into one doubly linked node, so
  the insertion rule (18), which needs two such nodes, is blocked. This needs
  feature-level linking (`Autosegmental/AR.lean`), not the segment-wise spreading here.
* §4's consonant–vowel asymmetries follow from plain consonants lacking S features
  underlyingly while vowels always carry them. The Fragment's segments are PHOIBLE's surface
  specifications, in which every consonant carries `[round]` and /k/ carries `[high]` and
  `[back]`, so stating them needs the underspecified consonants.

## References

* [G. N. Clements, *The Geometry of Phonological Features* (1985)][clements-1985]
* [K. P. Mohanan, *The Structure of the Melody* (1983)][mohanan-1983]
* [H. Thráinsson, *On the Phonology of Icelandic Preaspiration* (1978)][thrainsson-1978]
* [M. A. R. Barker, *Klamath Grammar* (1964)][barker-1964]
* [B. Elson, *Sierra Popoluca Syllable Structure* (1947)][elson-1947]
* [D. Steriade, *Greek Prosodies and the Nature of Syllabification* (1982)][steriade-1982]
* [B. P. Hayes, *Introductory Phonology* (2009)][hayes-2009]
* [N. Chomsky and M. Halle, *The Sound Pattern of English* (1968)][chomsky-halle-1968]
-/

@[expose] public section

namespace Clements1985

open Phonology Phonology.FeatureGeometry English Subregular.LocalRewrite English.Phonology

/-! ### Class nodes -/

/-- The class nodes of (3) are the root, linked to the CV tier, with laryngeal and
supralaryngeal below it, and manner and place below supralaryngeal. -/
inductive Node where
  | root | laryngeal | supralaryngeal | manner | place
  deriving DecidableEq, Repr, Fintype

namespace Node

/-- The node immediately dominating each node, the root fixed. -/
def pred : Node → Node
  | .root => .root
  | .laryngeal | .supralaryngeal => .root
  | .manner | .place => .supralaryngeal

/-- `a ≤ b` when `a` lies on the walk from `b` up to the root, so the root is `⊥` and the parent
is `Order.pred`. -/
instance : PartialOrder Node where
  le a b := a ∈ List.iterate pred b (Fintype.card Node)
  le_refl := by decide
  le_trans := by decide +kernel
  le_antisymm := by decide

instance : DecidableLE Node := fun a b ↦ inferInstanceAs (Decidable (a ∈ List.iterate pred b _))

instance : DecidableLT Node := decidableLTOfDecidableLE

instance : OrderBot Node where
  bot := .root
  bot_le := by decide

/-- The parent as the predecessor. -/
instance : PredOrder Node where
  pred := pred
  pred_le := by decide
  min_of_le_pred := by decide
  le_pred_of_lt := by decide

end Node

/-! ### Terminal features (§4) -/

/-- The class node a terminal feature hangs from. It is laryngeal for `[spread]`,
`[constricted]` and `[voiced]`, manner for `[consonantal]`, `[sonorant]`, `[continuant]`,
`[lateral]`, `[strident]` and, tentatively, `[nasal]`, and place for the place features.
Features the paper does not place have none. -/
def classNode? : Feature → Option Node
  | .voice | .spreadGlottis | .constrGlottis => some .laryngeal
  | .consonantal | .sonorant | .continuant | .lateral | .strident | .nasal => some .manner
  | .labial | .coronal | .anterior | .distributed | .high | .back | .round => some .place
  | _ => none

/-- The two sets of place features are P, distinguishing place in consonants, and S,
distinguishing place in vowels (§4). -/
inductive PlaceSet where
  | primary | secondary
  deriving DecidableEq, Repr

/-- `[coronal]`, `[anterior]`, `[distributed]` and, by table (22), `[labial]` are primary;
`[high]`, `[back]` and `[round]` are secondary. -/
def placeSet? : Feature → Option PlaceSet
  | .labial | .coronal | .anterior | .distributed => some .primary
  | .high | .back | .round => some .secondary
  | _ => none

/-- The features of a place set. -/
def PlaceSet.features (π : PlaceSet) : Finset Feature :=
  Finset.univ.filter (placeSet? · = some π)

/-- The place features are exactly P ∪ S. -/
theorem mem_place_featureClass_iff (f : Feature) :
    f ∈ featureClass classNode? Node.place ↔ (placeSet? f).isSome := by
  cases f <;> decide

/-! ### Assimilation as spreading ((5)) -/

/-- An assimilation rule spreads the root node (total assimilation), a class node (partial
assimilation) or a single feature (single-feature assimilation), after Mohanan. A rule
spreading more than one node costs more. -/
inductive Spreading where
  | node (a : Node)
  | feature (f : Feature)
  deriving DecidableEq, Repr, Fintype

namespace Spreading

variable (σ : Spreading) (src tgt : Segment)

/-- The features a spreading carries. -/
def features : Spreading → Finset Feature
  | .node a => featureClass classNode? a
  | .feature f => {f}

/-- Spreading from `src` onto `tgt` gives the carried features the values of `src`, specified
or not, the target's own being delinked ((13)), and leaves every other feature of `tgt`. -/
def apply : Segment := σ.features.piecewise src tgt

theorem apply_eqOn : Set.EqOn (σ.apply src tgt) src ↑σ.features :=
  fun _ hf ↦ Finset.piecewise_eq_of_mem _ _ _ hf

/-- Single-feature spreading overwrites the target's value at the feature with the source's. -/
theorem apply_feature (f : Feature) :
    (feature f).apply src tgt = Function.update tgt f (src f) :=
  Finset.piecewise_singleton _ _ _

variable {σ} {f g : Feature} {b c : Node}

/-- A spreading that carries two features hanging from distinct class nodes spreads a node
dominating both. -/
theorem exists_eq_node (hf : classNode? f = some b) (hg : classNode? g = some c) (hbc : b ≠ c)
    (h₁ : f ∈ σ.features) (h₂ : g ∈ σ.features) : ∃ a, σ = .node a ∧ a ≤ b ∧ a ≤ c := by
  cases σ with
  | node a => exact ⟨a, rfl, le_of_mem_featureClass h₁ hf, le_of_mem_featureClass h₂ hg⟩
  | feature f' =>
    rw [features, Finset.mem_singleton] at h₁ h₂
    subst h₁ h₂
    exact absurd (Option.some.inj (hf.symm.trans hg)) hbc

end Spreading

/-! ### Single-node spreading ((5), §3, §5) -/

variable {σ : Spreading} {f g : Feature}

/-- Place spreading carries `[anterior]` and `[distributed]` together and leaves `[nasal]`
alone, so (12) is a single-node rule while the `[αnasal]` variant of (14) is not. -/
theorem anterior_distributed_subset_place :
    {Feature.anterior, Feature.distributed} ⊆ featureClass classNode? Node.place := by
  decide

theorem nasal_notMem_place : Feature.nasal ∉ featureClass classNode? Node.place := by decide

/-- A spreading that reaches a manner feature and a place feature carries the whole
supralaryngeal class, the lowest node above both (§3). -/
theorem supralaryngeal_subset_of_manner_of_place (hf : classNode? f = some .manner)
    (hg : classNode? g = some .place) (h₁ : f ∈ σ.features) (h₂ : g ∈ σ.features) :
    featureClass classNode? Node.supralaryngeal ⊆ σ.features := by
  obtain ⟨a, rfl, ha, ha'⟩ := Spreading.exists_eq_node hf hg (by decide) h₁ h₂
  clear h₁ h₂
  exact antitone_featureClass (by revert a; decide)

/-- A spreading that reaches a manner feature and a laryngeal feature is the root's. -/
theorem eq_root_of_manner_of_laryngeal (hf : classNode? f = some .manner)
    (hg : classNode? g = some .laryngeal) (h₁ : f ∈ σ.features) (h₂ : g ∈ σ.features) :
    σ = .node .root := by
  obtain ⟨a, rfl, ha, ha'⟩ := Spreading.exists_eq_node hf hg (by decide) h₁ h₂
  clear h₁ h₂
  exact congrArg _ (by revert a; decide)

/-- No spreading carries exactly `[nasal]` and `[distributed]`, the set the `[αnasal]` variant of
(14) copies (§3). -/
theorem no_spreading_nasal_distributed (σ : Spreading) :
    σ.features ≠ {Feature.nasal, Feature.distributed} := fun h ↦ by
  have := supralaryngeal_subset_of_manner_of_place (σ := σ) (f := .nasal) (g := .distributed)
    rfl rfl (by simp [h]) (by simp [h])
  rw [h] at this
  simpa using this (show Feature.continuant ∈ featureClass classNode? .supralaryngeal by decide)

/-- Only the root reaches both `[continuant]` and `[voice]`, so Kikuyu's postnasal `[−continuant,
+voiced]` makes `[voiced]` redundant (§5.1, (24)). -/
theorem eq_root_of_continuant_of_voice (h₁ : Feature.continuant ∈ σ.features)
    (h₂ : Feature.voice ∈ σ.features) : σ = .node .root :=
  eq_root_of_manner_of_laryngeal rfl rfl h₁ h₂

/-- A spreading that assigns `[anterior]` and `[+continuant]` at once spreads the supralaryngeal
node, as English palatalisation would need (§5.2, (25)). -/
theorem supralaryngeal_subset_of_anterior_of_continuant (h₁ : Feature.anterior ∈ σ.features)
    (h₂ : Feature.continuant ∈ σ.features) :
    featureClass classNode? Node.supralaryngeal ⊆ σ.features :=
  supralaryngeal_subset_of_manner_of_place rfl rfl h₂ h₁

/-! ### English coronal place assimilation ((10)–(14)) -/

/-- In rule (12) as a local rewrite rule, a `[−continuant, +coronal, +anterior]` target takes
the place node of a following `[+consonantal, +coronal]` segment. -/
def rule12 : Rule where
  target := Segment.ofSpecs [(.continuant, false), (.coronal, true), (.anterior, true)]
  effect := .copyRight (Spreading.node .place).features
  rightContext := [.seg (Segment.ofSpecs [(.consonantal, true), (.coronal, true)])]

/-- In the SPE statement (14), the same target before a `[+coronal]` segment copies that
segment's `[anterior]` and `[distributed]` by alpha-variables. -/
def rule14 : Rule where
  target := Segment.ofSpecs [(.coronal, true), (.anterior, true), (.continuant, false)]
  effect := .copyRight {Feature.anterior, Feature.distributed}
  rightContext := [.seg (Segment.ofSpecs [(.coronal, true)])]

/-- The variant of (14) with `[αnasal]` for `[αanterior]` is "no more and no less ordinary" as
an SPE rule, and unattested. -/
def rule14Nasal : Rule := { rule14 with effect := .copyRight {Feature.nasal, Feature.distributed} }

/-- The English /r/ of table (10), `[+coronal, −anterior, −distributed]`, and `[+consonantal]`
as the trigger of (12) in table (11). -/
def r : Segment := (turnedR.setFeature .distributed false).setFeature .consonantal true

/-- The targets of (12) among the English phonemes are the stops /t d n/. -/
theorem naturalClass_rule12_target : rule12.target.naturalClass inventory = {t, d, n} := by
  decide

/-- Before /θ/, in *eighth*, *hundredth* and *tenth*, /t d n/ take `[+distributed]` and nothing
else, becoming interdental. -/
theorem rule12_θ : ∀ x ∈ rule12.target.naturalClass inventory,
    rule12.apply [x, θ] = [x.setFeature .distributed true, θ] := by
  decide

/-- Before /ʃ/, as in *each*, *insure* and *hundred shoes*, /t d n/ take `[−anterior,
+distributed]`, becoming postalveolar; /n/ stays a non-strident nasal, `[strident]` and
`[nasal]` being manner features. -/
theorem rule12_esh : ∀ x ∈ rule12.target.naturalClass inventory,
    rule12.apply [x, esh] = [(x.setFeature .anterior false).setFeature .distributed true, esh] := by
  decide

/-- Before /r/, in *tree*, *dream* and *enrol*, /t d n/ take `[−anterior]`, becoming
retroflex. -/
theorem rule12_r : ∀ x ∈ rule12.target.naturalClass inventory,
    rule12.apply [x, r] = [x.setFeature .anterior false, r] := by
  decide

/-- A labial trigger is no site, and *impossible* falls to the separate nasal assimilation
rule. -/
theorem rule12_n_p : rule12.apply [n, p] = [n, p] := by decide

/-- A fricative target is no site, since the rule affects the stops /t d n/ only. -/
theorem rule12_s_θ : rule12.apply [s, θ] = [s, θ] := by decide

/-- On table (11), (14) is not distinguishable from (12). -/
theorem rule14_eq_rule12 :
    ∀ x ∈ rule12.target.naturalClass inventory, ∀ y ∈ [θ, esh, r],
      rule14.apply [x, y] = rule12.apply [x, y] := by
  decide

/-- The `[αnasal]` variant of (14) makes /n/ before /θ/ an oral dental, though no single spreading
carries what it copies. -/
theorem rule14Nasal_n_θ :
    rule14Nasal.apply [n, θ] = [(n.setFeature .nasal false).setFeature .distributed true, θ] := by
  decide

/-! ### Supralaryngeal spreading: Icelandic preaspiration ((6)–(7)) -/

/-- Supralaryngeal spreading yields preaspiration (7), sharing the vowel's supralaryngeal and the
stop's laryngeal features, as also in Klamath (9a) and Sierra Popoluca (16). -/
theorem preaspiration (v c : Segment) :
    Set.EqOn ((Spreading.node .supralaryngeal).apply v c) v
        ↑(featureClass classNode? Node.supralaryngeal) ∧
      Set.EqOn ((Spreading.node .supralaryngeal).apply v c) c
        ↑(featureClass classNode? Node.laryngeal) :=
  ⟨Spreading.apply_eqOn _ v c, eqOn_piecewise_of_incompRel v c ⟨by decide, by decide⟩⟩

/-! ### Primary and secondary place features (§4) -/

/-- The primary place features alone separate /p t k/, as table (22) shows for /p t c k/. -/
theorem primary_separates_stops :
    ∀ x ∈ [p, t, k], ∀ y ∈ [p, t, k],
      Set.EqOn x y ↑PlaceSet.primary.features → x = y := by
  decide

end Clements1985
