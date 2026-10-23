module

public import Linglib.Fragments.Dutch.Adpositions
public import Linglib.Syntax.WordOrder
public import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
public import Studies.Helmantel2002

/-!
# Broekhuis and Corver 2026: Dutch adpositions

Dutch adpositions are traditionally sorted into four classes by where they stand relative to their
complement: prepositions, postpositions, circumpositions, and intransitive adpositions. This file
formalizes the argument that the classification is epiphenomenal. Each class is the surface effect
of one movement rule inside the adpositional phrase. A complement is selected below the adposition
and raises to the specifier of a phrase-internal functional projection when the rule says so: a
nominal complement stays where it is selected unless the phrase is directional, while a
prepositional complement or an R-pronoun raises. A raised complement precedes the adposition, so
the phrase is head-final; an in-situ one follows it. Postpositions are then directional
prepositions with a raised complement, and circumpositions are postpositions whose complement is
itself a prepositional phrase, so that the first part of a circumposition is the head of the
raised complement and the second part is the head of the whole.

The same head direction settles extraction. Dutch resists preposition stranding, but an element
that precedes the adpositional head can leave the phrase, and precisely the complements that
raise precede it: R-pronouns and the complements of directional postpositions can be extracted,
ordinary nominal complements of prepositions cannot, and the complement of a circumposition
patterns with the prepositional case because it sits inside the raised prepositional phrase. An
R-pronoun never yields the postpositional order, since *de wandeling er op* 'the hike on it' has
only the locational reading, so a circumpositional phrase R-pronominalizes through its
prepositional complement, and under wh-movement the first part of a circumposition pied-pipes
alone, which shows that it heads a phrase.

The lexical generalizations are checked against the Dutch adposition fragment, which follows the
authors' grammar: the rule reproduces every recorded postpositional use from the path it denotes,
every circumposition of the grammar is a listed preposition followed by a listed postposition or
particle, every postposition but *af* is also a preposition, an adposition with both uses is
locational before its complement unless it is one of the grammar's directional prepositions,
circumpositions take only nominal complements, and the morphologically complex prepositions
resist R-pronominalization. The chapter itself notes that *af* and *heen*, the second parts of
*van … af* and *over … heen*, are not commonly used as prepositions, although they once were,
and remain postpositions or particles with a directional meaning.

The chapter says that the raising of a nominal complement is semantically conditioned and does
not state the condition. Helmantel's analysis, which the chapter names as a starting point,
supplies one: the complement raises when the phrase is directional and the adposition is not
inherently directional, since an inherently directional adposition such as *naar* 'to' checks
the directionality itself. That condition entails the chapter's rule and keeps the grammar's
inherently directional prepositions out of the postpositional order.

## Main definitions

* `ComplementKind`, `Raises`: what a phrase-internal complement is, and when it raises to the
  specifier of the functional projection.
* `position`, `headDirection`: where the complement is pronounced, and the head direction of
  the phrase that results.
* `linearization`: the traditional four-way classification, read off the head direction.
* `Extractable`: extraction requires the extracted element to precede the adpositional head.
* `verbClass`: the transitivity class of a verb of motion with a spatial complementive.

## Main results

* `linearization_eq_post_iff`, `linearization_eq_circum_iff`: each surface class is the
  effect of one complement kind and directionality, not a lexical property.
* `linearization_rPronoun`: an R-pronoun complement never gives the postpositional order.
* `range_linearization`: the rule derives every class of the traditional classification and
  no other order.
* `extractable_iff_raises`, `extractable_iff_of_linearization_eq_pre`,
  `extractable_of_linearization_ne_pre`: extraction is raising, so from a prepositional phrase
  only an R-pronoun leaves and from any other phrase the complement does.
* `raises_nominal_of_dpRaises`, `pointLocative_not_postP`: Helmantel's condition on nominal
  raising entails the chapter's rule, and under it the inherently directional prepositions have
  no postpositional use.
* `linearization_direction_post`, `circumP_parts`: the rule reproduces every postpositional
  use of the fragment and every circumposition decomposes into listed parts.
* `postP_subset_preP`, `circumP_complement_nominal`, `no_rPron_not_postP`: the lexical
  restrictions the analysis predicts.
* `perfect_op`, `postP_selects_zijn`: a postpositional phrase denotes a path and its verb takes
  *zijn* 'be', while the prepositional phrase of the same adposition takes *hebben* 'have'.

## Implementation notes

* The chapter's extraction evidence is modelled over complement kinds only, one level deep. The
  extraction of modifiers such as measure phrases from a prepositional phrase, the pied-piping
  of the first part of a circumposition alone under wh-movement, and the restriction of
  pronominal complements to human referents, which R-pronouns lift, are described in the
  chapter and not formalized. The raised prepositional phrase inside a circumposition is taken
  to be a plain prepositional phrase whose complement stays in situ.
* The chapter offers the raising analysis as a hypothesis that idealizes away the exceptional
  prepositional phrases with a prepositional complement, such as *van na de oorlog* 'from
  after the war'.
* The perfect auxiliary follows the chapter's account of the contrast between *heeft op de
  heuvel gereden* and *is de heuvel op gereden*: a path complementive makes the verb of motion
  telic and unaccusative. `verbClass` records that account, and the auxiliary is then the
  selection rule's, whichever way the language treats its reflexives.

## TODO

`Raises` idealizes the chapter's semantic condition to directionality, so
`linearization_eq_post_iff` predicts a postpositional order for every directional preposition.
Helmantel's condition removes *naar*, *tot* and *van*, but *vanaf*, *vanuit* and *via*, which
she does not classify, still come out postpositional although the grammar records no such use,
and the prepositional phrase inside *van het dak af* 'off the roof' is read as locational
although *van* denotes a source path.

## References

* [H. Broekhuis and N. Corver, *Adpositions and Adpositional Phrases: A Syntactic View from
  Dutch* (2026)][broekhuis-corver-2026a]
* [H. Broekhuis and N. Corver, *Syntax of Dutch, Volume VII: Adpositions and Adpositional
  Phrases* (2026)][broekhuis-corver-2026c]
* [M. Helmantel, *Interactions in the Dutch Adpositional Domain* (2002)][helmantel-2002]
-/

@[expose] public section

namespace BroekhuisCorver2026

open Dutch.Adpositions
open ArgumentStructure (TransitivityClass)
open Verb (PerfectAuxiliary)

/-! ### The internal structure of an adpositional phrase -/

/-- A transitive adposition selects a noun phrase, a prepositional phrase, or an R-pronoun, the
proform of a locational prepositional phrase. An intransitive adposition selects nothing,
`Option.none`. -/
inductive ComplementKind where
  | nominal
  | prePP
  | rPronoun
  deriving DecidableEq, Repr, Fintype

/-- By the raising rule, a prepositional phrase or an R-pronoun raises to the specifier of the
phrase-internal functional projection, and a nominal complement only when the phrase is
directional, under a semantic condition the chapter leaves open and this file idealizes to
directionality. -/
def Raises : ComplementKind → Spatial.Path.Direction → Prop
  | .nominal, d => d ≠ .place
  | .prePP, _ => True
  | .rPronoun, _ => True

instance : ∀ k, DecidablePred (Raises k)
  | .nominal, d => inferInstanceAs (Decidable (d ≠ .place))
  | .prePP, _ => inferInstanceAs (Decidable True)
  | .rPronoun, _ => inferInstanceAs (Decidable True)

section Phrase

variable (k : ComplementKind) (d : Spatial.Path.Direction)

/-- The phrase has three positions, the specifier of the functional projection, the adposition,
and the complement's base position, and the complement is pronounced in the specifier when it
raises and in its base position otherwise. -/
def position : Fin 3 := if Raises k d then 0 else 2

/-- The adposition's position. -/
def headPosition : Fin 3 := 1

/-- The head direction of the phrase is read off the positions of the adposition and its
complement, head-final exactly when the complement has raised. -/
def headDirection : HeadDirection := .ofLT headPosition (position k d)

/-- Extraction from an adpositional phrase requires the extracted element to precede the
adpositional head. -/
def Extractable : Prop := position k d < headPosition

instance : Decidable (Extractable k d) := inferInstanceAs (Decidable (_ < _))

variable {k d}

theorem headDirection_eq_headFinal : headDirection k d = .headFinal ↔ Raises k d := by
  unfold headDirection headPosition position; split <;> simp [*]

theorem headDirection_eq_headInitial : headDirection k d = .headInitial ↔ ¬ Raises k d := by
  unfold headDirection headPosition position; split <;> simp [*]

theorem extractable_iff_raises : Extractable k d ↔ Raises k d := by
  unfold Extractable headPosition position; split <;> simp [*]

end Phrase

/-- The traditional classification, read off the head direction and the complement. The head
precedes an in-situ complement and follows a raised one; a raised prepositional phrase carries
its own head before the noun phrase, so the whole is a circumposition; and *er op* counts as a use
of the preposition, since an R-pronoun proforms the locational prepositional phrase. -/
def linearization : Option ComplementKind → Spatial.Path.Direction → Option Adposition.Linearization
  | none, _ => none
  | some k, d =>
    some <| match k, headDirection k d with
      | .nominal, .headFinal => .post
      | .prePP, .headFinal => .circum
      | _, _ => .pre

theorem linearization_eq_post_iff (k : ComplementKind) (d : Spatial.Path.Direction) :
    linearization (some k) d = some .post ↔ k = .nominal ∧ d ≠ .place := by
  cases k <;> cases d <;> decide

theorem linearization_eq_circum_iff (k : ComplementKind) (d : Spatial.Path.Direction) :
    linearization (some k) d = some .circum ↔ k = .prePP := by
  cases k <;> cases d <;> decide

theorem linearization_rPronoun (d : Spatial.Path.Direction) :
    linearization (some .rPronoun) d = some .pre := by
  cases d <;> rfl

theorem range_linearization :
    Set.range (Function.uncurry linearization) = {some .inposition}ᶜ := by
  ext o
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨⟨k, d⟩, rfl⟩
    cases k with
    | none => cases d <;> decide
    | some k => cases k <;> cases d <;> decide
  · rcases o with _ | _ | _ | _ | _
    exacts [⟨(none, .place), rfl⟩, ⟨(some .nominal, .place), rfl⟩,
      ⟨(some .nominal, .goal), rfl⟩, ⟨(some .prePP, .place), rfl⟩, absurd rfl h]

/-! ### Extraction -/

theorem extractable_nominal_iff (d : Spatial.Path.Direction) : Extractable .nominal d ↔ d ≠ .place :=
  extractable_iff_raises

theorem extractable_rPronoun (d : Spatial.Path.Direction) : Extractable .rPronoun d :=
  extractable_iff_raises.2 trivial

theorem extractable_iff_of_linearization_eq_pre {k : ComplementKind} {d : Spatial.Path.Direction}
    (h : linearization (some k) d = some .pre) : Extractable k d ↔ k = .rPronoun := by
  revert h; cases k <;> cases d <;> decide

theorem extractable_of_linearization_ne_pre {k : ComplementKind} {d : Spatial.Path.Direction}
    (h : linearization (some k) d ≠ some .pre) : Extractable k d := by
  revert h; cases k <;> cases d <;> decide

theorem circumP_patterns_with_preP :
    ¬ Extractable .nominal .place ∧ Extractable .rPronoun .place :=
  ⟨fun h ↦ (extractable_nominal_iff _).1 h rfl, extractable_rPronoun _⟩

/-! ### The condition on nominal raising -/

theorem raises_nominal_of_dpRaises {inherent : Prop} {d : Spatial.Path.Direction}
    (h : Helmantel2002.DPRaises (d ≠ .place) inherent) : Raises .nominal d :=
  h.1

theorem pointLocative_not_postP :
    ∀ a ∈ Helmantel2002.pointLocatives, ¬ a.IsPostposition :=
  fun a ha h ↦ by
    simp [Adposition.IsPostposition, Helmantel2002.pointLocative_linearization a ha] at h

/-! ### The Dutch lexicon -/

theorem linearization_direction_post :
    ∀ a ∈ inventory, a.IsPostposition →
      linearization (some .nominal) (a.direction .post) = some .post :=
  fun a ha h ↦ (linearization_eq_post_iff _ _).2 ⟨rfl, direction_post_ne_place a ha h⟩

theorem circumP_parts :
    ∀ a ∈ inventory, a.IsComplex →
      ∃ b ∈ inventory, ∃ c ∈ inventory, a.morphs = b.morphs ++ c.morphs ∧
        b.IsPreposition ∧ (c.IsPostposition ∨ c.IsIntransitive) := by
  decide

theorem postP_subset_preP :
    ∀ a ∈ inventory, a.IsPostposition → a.IsPreposition ∨ a.toAdposition = af.toAdposition :=
  pre_of_post

theorem circumP_parts_not_preP : ¬ af.IsPreposition ∧ ¬ heen.IsPreposition := by
  decide

theorem postP_has_both_readings :
    ∀ a ∈ inventory, a.IsAmbiposition →
      a.direction .pre = .place ∨ a.toAdposition = over₁.toAdposition ∨
        a.toAdposition = voorbij.toAdposition := by
  decide

theorem circumP_complement_nominal :
    ∀ a ∈ inventory, a.IsCircumposition → a.complements = {some .np} :=
  complements_of_circum

theorem postP_complement_np :
    ∀ a ∈ inventory, a.IsPostposition → a.Takes .np := by
  decide

theorem complex_no_rPron :
    tijdens.rPronoun = false ∧ ondanks.rPronoun = false ∧ zonder.rPronoun = false :=
  ⟨rfl, rfl, rfl⟩

theorem no_rPron_not_postP :
    ∀ a ∈ inventory, a.rPronoun = false → .post ∉ a.linearization := by
  decide

/-! ### Directional phrases and the perfect auxiliary -/

theorem op_van_paths : op.direction .post = .goal ∧ van.direction .pre = .source := ⟨rfl, rfl⟩

/-- A path complementive makes the event of a verb of motion a change of location and the verb
unaccusative, and a location complementive leaves it unergative. -/
def verbClass (d : Spatial.Path.Direction) : TransitivityClass :=
  if d = .place then .unergative else .unaccusative

theorem selection_verbClass_eq_be_iff (r : PerfectAuxiliary) (d : Spatial.Path.Direction) :
    (verbClass d).selection r = .be ↔ d ≠ .place := by
  unfold verbClass; split <;> simp [*, TransitivityClass.selection]

theorem perfect_op (r : PerfectAuxiliary) :
    (verbClass (op.direction .pre)).selection r = .have ∧
      (verbClass (op.direction .post)).selection r = .be :=
  ⟨rfl, rfl⟩

theorem postP_selects_zijn (r : PerfectAuxiliary) :
    ∀ a ∈ inventory, .post ∈ a.linearization → (verbClass (a.direction .post)).selection r = .be :=
  fun a ha h ↦ (selection_verbClass_eq_be_iff r _).2 (direction_post_ne_place a ha h)

end BroekhuisCorver2026
