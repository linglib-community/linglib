module

public import Linglib.Data.Examples.Stassen1985
public import Linglib.Fragments.Arabic.ModernStandard.Comparison
public import Linglib.Fragments.Finnish.Comparison
public import Linglib.Fragments.HindiUrdu.Comparison
public import Linglib.Fragments.Japanese.Comparison
public import Linglib.Fragments.Korean.Clause
public import Linglib.Fragments.Korean.Comparison
public import Linglib.Fragments.Mandarin.Comparison
public import Linglib.Fragments.Romance.French.Comparison
public import Linglib.Fragments.Slavic.Russian.Comparison
public import Linglib.Fragments.Swahili.Comparison
public import Linglib.Fragments.Turkish.Clause
public import Linglib.Fragments.Turkish.Comparison
public import Linglib.Fragments.Yoruba.Comparison
public import Linglib.Syntax.Feature.Case.Spatial
public import Mathlib.Basic.Rel

/-!
# Stassen (1985): Comparison and Universal Grammar

Stassen classifies comparative constructions by the encoding of the standard of comparison. A
standard whose case is derived from the comparee's belongs to a conjoined comparative, two
independent clauses, or to a particle comparative. A standard in a fixed case is the direct
object of a verb of exceeding, the exceed comparative, or part of an adverbial phrase, and the
adverbial comparative is separative, allative or locative as the phrase is one of source, of
goal or of location.

A temporal chain expresses two events as consecutive or as simultaneous. It is balanced, both
predicates keeping their rank, or deranked, one predicate reduced, either only under identity
of subjects or absolutely, and an absolutely deranked predicate is anterior to, posterior to or
simultaneous with the other.

The three adverbial comparatives and the three absolutely deranked chains are indexed by one
type, `Ordering`, read as the comparison `cmp ground figure` of a ground with a figure along a
line. For a comparative the ground is the standard and the line a path: the standard is where
the path starts, `lt`, where it ends, `gt`, or where the comparee is, `eq`. For a chain the
ground is the deranked predicate and the line is time: it is before the main predicate, after
it or simultaneous with it.

The book's hypothesis is that a comparative is modelled on a chaining construction of its
language. `Models c t` holds when a comparative of type `t` is modelled on a chain of type `c`:
a particle comparative on a balanced chain, a conjoined one on the balanced simultaneous chain,
an exceed comparative on a conditionally deranked chain, and an adverbial comparative on the
absolutely deranked chain with the same order of ground and figure. Modelling is invariant
under the reversal of the line, which exchanges the separative with the allative and the
anterior with the posterior. For a language with the chaining constructions `C` and the
comparatives `T` we state the book's chaining-based universals as `Universals C T`, and prove
that they hold exactly when every comparative of the language is modelled on one of its
chains, `T ⊆ models.image C`. Every type of chain models some comparative and every type of
comparative is modelled on some chain.

The examples are comparatives of the book whose construction a fragment records. The type each
fragment construction has by the encoding of its standard is the type the book classes the
example under, for every recorded example but the Finnish partitive.

## Main definitions

* `Stassen1985.ComparativeType`, `Stassen1985.typeOf`: the types of comparative and the type
  of a construction
* `Stassen1985.ChainType`: the types of temporal chaining
* `Stassen1985.groundOrder?`: the order of ground and figure a spatial direction expresses
* `Stassen1985.Models`, `Stassen1985.models`: the modelling relation between chains and
  comparatives
* `Stassen1985.Universals`: the chaining-based universals of a language

## Implementation notes

* The two typologies are inductive types with one constructor for each way of encoding the
  standard and for each chaining option, so that the universals on case assignment and on
  conditionality say that modelling preserves the constructor, and the three universals on the
  adverbial types are one statement over `Ordering`. The book's flat lists are the six and the
  seven values of these types. `Ordering` is used and not a type of spatial relations with a
  bijection to a type of relative times, since the bijection would be stipulated, while the
  comparison of ground and figure is what both sets of labels classify.
* A language is a set of chaining constructions and a set of comparatives, since the book
  allows a language several of each. A universal whose consequent is that the language is
  balancing or deranking, or has conditional or absolute deranking, is read as saying that the
  language has a chain of that kind, the reading under which the book takes a chaining type to
  be a necessary and not a sufficient condition for a comparative type.
* An adverbial standard is classed by the direction of its case, `Case.dirOf`, extended to the
  non-spatial cases the book classes by the localist analysis. The partitive is none of these,
  so the Finnish partitive standard, which the book lists as a secondary separative
  comparative, gets no type.
* The rows name the fragment's construction by a lexeme. The transcriptions of the book's
  sources are not compared with the fragments' forms.

## TODO

* The language types of the Principle of Parallel Chaining and the word orders the book
  associates with each type of deranking are not formalized, nor are the mixed comparatives,
  the chaining data of the sample that Part Two tests the universals against, and the
  procedure-based universals of Part Three.
* The Korean separative of the book marks the standard with *-eso*, which the fragment does
  not record.

## References

* [L. Stassen, *Comparison and Universal Grammar* (1985)][stassen-1985]
* [L. Stassen, *Comparative Constructions* (2013)][stassen-2013]
-/

@[expose] public section

namespace Stassen1985

open Comparative
open scoped SetRel

/-! ### The types of comparative -/

/-- The order of the ground and the figure along a path of a direction, `cmp ground figure`:
the ground comes first on a path from it, last on a path to it, and coincides with the figure
located at it. A route, past the ground, compares the two in no one way. -/
def groundOrder? : Spatial.Path.Direction → Option Ordering
  | .source => some .lt
  | .goal => some .gt
  | .place => some .eq
  | .route => none

-- Reversing a path swaps the order of the ground and the figure.
theorem groundOrder?_reverse (d : Spatial.Path.Direction) :
    groundOrder? d.reverse = (groundOrder? d).map Ordering.swap := by
  cases d <;> rfl

/-- The types of comparative construction, by the encoding of the standard. -/
inductive ComparativeType
  /-- Two independent clauses, one for the comparee and one for the standard. -/
  | conjoined
  /-- A standard in a derived case, flagged by a comparative particle. -/
  | particle
  /-- The standard is the direct object of a verb of exceeding. -/
  | exceed
  /-- The standard is in an adverbial phrase, with `o` the order of the standard and the
  comparee along the path the phrase expresses: the separative comparative, `lt`, for a source,
  the allative, `gt`, for a goal and the locative, `eq`, for a location. -/
  | adverbial (o : Ordering)
  deriving DecidableEq, Repr, Fintype

namespace ComparativeType

/-- The type of the atlas, which collapses the three adverbial types into one. -/
def toWALS : ComparativeType → Data.WALS.F121A.ComparativeType
  | conjoined => .conjoined
  | particle => .particle
  | exceed => .exceed
  | adverbial _ => .locational

/-- The standard of a conjoined or a particle comparative takes its case from the comparee;
the other types fix the case of the standard. -/
def IsDerivedCase : ComparativeType → Prop
  | conjoined | particle => True
  | _ => False

instance : DecidablePred IsDerivedCase := fun t ↦ by
  cases t <;> unfold IsDerivedCase <;> infer_instance

/-- The type with the line reversed: the separative and the allative are exchanged. -/
def swap : ComparativeType → ComparativeType
  | adverbial o => adverbial o.swap
  | t => t

@[simp] theorem swap_swap (t : ComparativeType) : t.swap.swap = t := by
  cases t <;> simp [swap, Ordering.swap_swap]

end ComparativeType

/-- The order of the standard and the comparee for an adverbial standard in the case `k`:
that of the direction of a spatial case and, by the localist analysis, that of a source for an
instrumental, of a goal for a dative or a benefactive and of a location for a comitative. -/
def standardOrder? (k : Case) : Option Ordering :=
  k.dirOf.bind groundOrder? <|> match k with
    | .inst => some .lt
    | .dat | .ben => some .gt
    | .com => some .eq
    | _ => none

theorem standardOrder?_of_dirOf {k : Case} {d : Spatial.Path.Direction} {o : Ordering}
    (hd : k.dirOf = some d) (ho : groundOrder? d = some o) : standardOrder? k = some o := by
  simp [standardOrder?, hd, ho]

/-- The type of a construction, by the encoding of its standard. A derived-case standard gives
a particle comparative when a marker flags it and a conjoined one otherwise, a direct object an
exceed comparative, and an adverbial standard the adverbial comparative of the order its case
expresses, if it expresses one. -/
def typeOf (c : Comparative) : Option ComparativeType :=
  match c.standard with
  | .derived => some (if c.standardMarker = [] then .conjoined else .particle)
  | .directObject => some .exceed
  | .adverbial k => (k.bind standardOrder?).map .adverbial

variable {c : Comparative} {t : ComparativeType}

/-- The type of a construction collapses to its type in the atlas. -/
theorem toWALS_of_mem_typeOf (h : t ∈ typeOf c) : t.toWALS = c.type := by
  cases hs : c.standard <;> simp only [typeOf, Comparative.type, hs] at h ⊢
  · obtain rfl := Option.mem_some_iff.mp h
    split <;> rfl
  · obtain rfl := Option.mem_some_iff.mp h
    rfl
  · obtain ⟨o, -, rfl⟩ := Option.mem_map.mp h
    rfl

theorem isDerivedCase_iff_of_mem_typeOf (h : t ∈ typeOf c) :
    t.IsDerivedCase ↔ c.standard = .derived := by
  cases hs : c.standard <;> simp only [typeOf, hs] at h
  · obtain rfl := Option.mem_some_iff.mp h
    split <;> simp [ComparativeType.IsDerivedCase]
  · obtain rfl := Option.mem_some_iff.mp h
    simp [ComparativeType.IsDerivedCase]
  · obtain ⟨o, -, rfl⟩ := Option.mem_map.mp h
    simp [ComparativeType.IsDerivedCase]

theorem typeOf_eq_some_adverbial_iff {o : Ordering} :
    typeOf c = some (.adverbial o) ↔
      ∃ k, c.standard = .adverbial (some k) ∧ standardOrder? k = some o := by
  cases hs : c.standard with
  | derived => simp only [typeOf, hs]; split <;> simp
  | directObject => simp [typeOf, hs]
  | adverbial k => cases k <;> simp [typeOf, hs]

/-! ### Temporal chaining -/

/-- A chain is consecutive, one event after the other, or simultaneous. -/
inductive Temporality
  | consecutive
  | simultaneous
  deriving DecidableEq, Repr, Fintype

/-- The syntactic types of temporal chaining. -/
inductive ChainType
  /-- Both predicates keep their structural rank. -/
  | balanced (τ : Temporality)
  /-- One predicate is reduced, and only under identity of the subjects; in a consecutive
  chain it is the posterior one. -/
  | conditional (τ : Temporality)
  /-- One predicate is reduced whether or not the subjects are identical, with `o` the order
  in time of the deranked predicate and the other: anterior, `lt`, or posterior, `gt`, in a
  consecutive chain, or simultaneous, `eq`. -/
  | absolute (o : Ordering)
  deriving DecidableEq, Repr, Fintype

namespace ChainType

/-- The temporality of a chain type. -/
def temporality : ChainType → Temporality
  | balanced τ | conditional τ => τ
  | absolute .eq => .simultaneous
  | absolute _ => .consecutive

/-- A chain is balanced when neither predicate is deranked. -/
def IsBalanced : ChainType → Prop
  | balanced _ => True
  | _ => False

instance : DecidablePred IsBalanced := fun c ↦ by
  cases c <;> unfold IsBalanced <;> infer_instance

/-- The chain type with time reversed: the anterior and the posterior are exchanged. -/
def swap : ChainType → ChainType
  | absolute o => absolute o.swap
  | c => c

@[simp] theorem swap_swap (c : ChainType) : c.swap.swap = c := by
  cases c <;> simp [swap, Ordering.swap_swap]

-- The typology has the seven types of the book's summary.
theorem card_eq : Fintype.card ChainType = 7 := by decide

end ChainType

/-! ### The modelling of comparatives on chains -/

/-- `Models c t` holds when a comparative of type `t` is modelled on a chain of type `c`. -/
inductive Models : ChainType → ComparativeType → Prop
  /-- A particle comparative is modelled on a balanced chain of either temporality. -/
  | particle (τ : Temporality) : Models (.balanced τ) .particle
  /-- A conjoined comparative is modelled on the balanced simultaneous chain. -/
  | conjoined : Models (.balanced .simultaneous) .conjoined
  /-- An exceed comparative is modelled on a conditionally deranked chain. -/
  | exceed (τ : Temporality) : Models (.conditional τ) .exceed
  /-- An adverbial comparative is modelled on the absolutely deranked chain with the same
  order of ground and figure. -/
  | adverbial (o : Ordering) : Models (.absolute o) (.adverbial o)

/-- The modelling relation as a set of pairs. -/
def models : SetRel ChainType ComparativeType := {(c, t) | Models c t}

variable {ct : ChainType}

@[simp] theorem mem_models : ct ~[models] t ↔ Models ct t := .rfl

@[simp] theorem models_particle_iff : Models ct .particle ↔ ct.IsBalanced :=
  ⟨fun | .particle _ => trivial, fun h ↦ by cases ct <;> first | exact .particle _ | cases h⟩

@[simp] theorem models_conjoined_iff : Models ct .conjoined ↔ ct = .balanced .simultaneous :=
  ⟨fun | .conjoined => rfl, fun h ↦ h ▸ .conjoined⟩

@[simp] theorem models_exceed_iff : Models ct .exceed ↔ ∃ τ, ct = .conditional τ :=
  ⟨fun | .exceed τ => ⟨τ, rfl⟩, fun ⟨τ, h⟩ ↦ h ▸ .exceed τ⟩

@[simp] theorem models_adverbial_iff {o : Ordering} :
    Models ct (.adverbial o) ↔ ct = .absolute o :=
  ⟨fun | .adverbial _ => rfl, fun h ↦ h ▸ .adverbial o⟩

/-- Modelling is invariant under the reversal of the line: the allative is modelled on the
mirror image of the chain the separative is modelled on. -/
theorem models_swap_iff : Models ct.swap t.swap ↔ Models ct t := by
  have key : ∀ {c : ChainType} {t : ComparativeType}, Models c t → Models c.swap t.swap := by
    rintro _ _ (τ | _ | τ | o)
    exacts [.particle τ, .conjoined, .exceed τ, .adverbial o.swap]
  exact ⟨fun h ↦ by simpa using key h, key⟩

-- A chain is balanced exactly when the comparatives modelled on it have a derived-case standard.
theorem Models.isBalanced_iff (h : Models ct t) : ct.IsBalanced ↔ t.IsDerivedCase := by
  cases h <;> simp [ChainType.IsBalanced, ComparativeType.IsDerivedCase]

-- Every type of chain models some comparative.
theorem dom_models : models.dom = Set.univ :=
  Set.eq_univ_of_forall fun
    | .balanced τ => ⟨_, .particle τ⟩
    | .conditional τ => ⟨_, .exceed τ⟩
    | .absolute o => ⟨_, .adverbial o⟩

-- Every type of comparative is modelled on some chain.
theorem cod_models : models.cod = Set.univ :=
  Set.eq_univ_of_forall fun
    | .conjoined => ⟨_, .conjoined⟩
    | .particle => ⟨_, .particle .simultaneous⟩
    | .exceed => ⟨_, .exceed .simultaneous⟩
    | .adverbial o => ⟨_, .adverbial o⟩

variable {C : Set ChainType} {T : Set ComparativeType}

/-- The chaining-based universals of a language with the chaining constructions `C` and the
comparatives `T`. -/
@[mk_iff]
structure Universals (C : Set ChainType) (T : Set ComparativeType) : Prop where
  /-- Universal 1A: a language with a derived-case comparative is balancing. -/
  balancing_of_derivedCase : ∀ t ∈ T, t.IsDerivedCase → ∃ c ∈ C, c.IsBalanced
  /-- Universal 1B: a language with a fixed-case comparative is deranking. -/
  deranking_of_fixedCase : ∀ t ∈ T, ¬ t.IsDerivedCase → ∃ c ∈ C, ¬ c.IsBalanced
  /-- Universal 2A: a language with an exceed comparative has conditional deranking. -/
  conditional_of_exceed : .exceed ∈ T → ∃ τ, .conditional τ ∈ C
  /-- Universal 2B: a language with an adverbial comparative has absolute deranking. -/
  absolute_of_adverbial : ∀ o, .adverbial o ∈ T → ∃ o', .absolute o' ∈ C
  /-- Universals 3A to 3C: a language with a separative, an allative or a locative comparative
  has an absolutely deranked anterior consecutive, posterior consecutive or simultaneous
  construction. -/
  absolute_of_adverbial_same : ∀ o, .adverbial o ∈ T → .absolute o ∈ C
  /-- Universal 4: a language with a conjoined comparative has a balanced simultaneous
  construction. -/
  balanced_of_conjoined : .conjoined ∈ T → .balanced .simultaneous ∈ C

/-- The chaining-based universals hold of a language exactly when each of its comparatives is
modelled on one of its chaining constructions. -/
theorem universals_iff_subset_image : Universals C T ↔ T ⊆ models.image C := by
  refine ⟨fun h t ht ↦ ?_, fun h ↦ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · cases t with
    | conjoined => exact ⟨_, h.balanced_of_conjoined ht, .conjoined⟩
    | particle =>
      obtain ⟨c, hc, hb⟩ := h.balancing_of_derivedCase _ ht trivial
      exact ⟨c, hc, models_particle_iff.mpr hb⟩
    | exceed =>
      obtain ⟨τ, hτ⟩ := h.conditional_of_exceed ht
      exact ⟨_, hτ, .exceed τ⟩
    | adverbial o => exact ⟨_, h.absolute_of_adverbial_same o ht, .adverbial o⟩
  · rintro t ht hd
    obtain ⟨c, hc, hm⟩ := h ht
    exact ⟨c, hc, hm.isBalanced_iff.mpr hd⟩
  · rintro t ht hd
    obtain ⟨c, hc, hm⟩ := h ht
    exact ⟨c, hc, hm.isBalanced_iff.not.mpr hd⟩
  · intro ht
    obtain ⟨c, hc, hm⟩ := h ht
    obtain ⟨τ, rfl⟩ := models_exceed_iff.mp hm
    exact ⟨τ, hc⟩
  · intro o ht
    obtain ⟨c, hc, hm⟩ := h ht
    obtain rfl := models_adverbial_iff.mp hm
    exact ⟨_, hc⟩
  · intro o ht
    obtain ⟨c, hc, hm⟩ := h ht
    obtain rfl := models_adverbial_iff.mp hm
    exact hc
  · intro ht
    obtain ⟨c, hc, hm⟩ := h ht
    obtain rfl := models_conjoined_iff.mp hm
    exact hc

-- The universals of a language hold of any language with more chaining constructions and
-- fewer comparatives.
theorem Universals.mono {C' : Set ChainType} {T' : Set ComparativeType} (h : Universals C T)
    (hC : C ⊆ C') (hT : T' ⊆ T) : Universals C' T' :=
  universals_iff_subset_image.mpr <|
    hT.trans <| (universals_iff_subset_image.mp h).trans <| SetRel.image_mono hC

/-! ### The examples -/

/-- The type of each class of the rows. -/
def Examples.ComparativeClass.toType : Examples.ComparativeClass → ComparativeType
  | .separative => .adverbial .lt
  | .allative => .adverbial .gt
  | .locative => .adverbial .eq
  | .exceed => .exceed
  | .conjoined => .conjoined
  | .particle => .particle

/-- The fragment's construction for each lexeme of the rows. -/
def Examples.Lexeme.entry : Examples.Lexeme → Comparative
  | .dan => Turkish.Comparison.dan
  | .se => HindiUrdu.Comparison.se
  | .yori => Japanese.Comparison.yori
  | .min => Arabic.ModernStandard.Comparison.min
  | .bi => Mandarin.Comparison.bi
  | .ju => Yoruba.Comparison.ju
  | .kushinda => Swahili.Comparison.kushinda
  | .kuliko => Swahili.Comparison.kuliko
  | .chem => Russian.Comparison.chem
  | .que => French.Comparison.que
  | .kuin => Finnish.Comparison.kuin
  | .juxtaposition => Swahili.Comparison.conjoined
  | .partitive => Finnish.Comparison.partitive

/-- The type of the fragment's construction is the type the book classes the example under, for
each example but that of the Finnish partitive standard, which the book classes as separative
and whose case expresses no order of standard and comparee. -/
theorem typeOf_entry :
    ∀ x : Examples.Example, ∀ l ∈ x.lexemes .standard,
      (typeOf l.entry = x.comparativeClass.map (·.toType) ↔ x ≠ .ex_10_54a) := by
  decide

-- Korean and Turkish have a fixed-case comparative and, as Universal 1B requires of them,
-- medial verb forms that are not finite.
theorem deranking_fragments :
    (∀ c ∈ [Korean.Comparison.boda, Turkish.Comparison.dan], ∀ t ∈ typeOf c, ¬ t.IsDerivedCase) ∧
      (∃ m : Korean.Converb, m.verbForm ≠ .Fin) ∧ ∃ m : Turkish.Converb, m.verbForm ≠ .Fin := by
  decide

end Stassen1985
