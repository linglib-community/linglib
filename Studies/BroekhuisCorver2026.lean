module

public import Linglib.Data.Examples.BroekhuisCorver2026
public import Linglib.Data.Examples.Readers
public import Linglib.Fragments.Dutch.Adpositions
public import Linglib.Syntax.WordOrder
public import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
public import Studies.Helmantel2002

/-!
# Broekhuis and Corver 2026: Dutch adpositions

Broekhuis and Corver argue that the traditional classes of Dutch adpositions are epiphenomenal: a
complement follows the adposition or is raised before it, and [the order yields the four classes
and no other](##range_linearization). A prepositional phrase and an R-pronoun raise, and a noun
phrase raises to be read as a path, a condition Helmantel's analysis makes precise. Then [every
spatial use the grammar records sits where its order puts it](##reads_uses), [an R-pronoun keeps
the prepositional reading](##reads_rPronoun_iff), and since only a raised complement can leave the
phrase, [the noun phrase of a circumposition stays inside](##circumposition_extraction). A [path
complementive makes a verb of motion take *zijn*](##perfect_op).

## Implementation notes

* `Reads` takes Helmantel's condition, which the chapter names among its starting points: a noun
  phrase in the specifier is read as a path, which the object of a point locative cannot be, and a
  phrase otherwise has the readings of its adposition's class. Her classes are lists of the
  fragment's entries; *af*, *heen*, *toe* and the locational *over* are not among them.
* `Reads` licenses a site without forcing one: an extended locative such as *over* is directional
  with its noun phrase in either site, and the grammar records which narrow locatives have a
  postpositional use.
* The prepositional phrase a circumposition raises is taken to denote a location, as the chapter
  says the prepositional complements of *van* and *tot* do, unless its adposition is a point
  locative, which has none.
* The idealization leaves out the prepositional phrases whose prepositional complement stays in its
  base position, *van na de oorlog* 'from after the war', and the R-words that follow *van* and
  *tot*, *van hier tot daar* 'from here to there'. The extraction of modifiers such as measure
  phrases and the restriction of pronominal complements to human referents are not formalized.
* A row is linked to the fragment entry whose phrase its element leaves, and to the element's
  kind; the class is Helmantel's, the judgment is predicted from it, and the linked adposition is
  checked against the row's words.
* The perfect auxiliary follows the chapter's account of *heeft op de heuvel gereden* against *is de
  heuvel op gereden*: a path complementive makes the verb of motion telic and unaccusative.
  `verbClass` records that account, and the auxiliary is then the selection rule's, whichever way
  the language treats its reflexives.

## Errata

* The gloss of the raising rule, that a noun phrase stays in its base position unless the phrase is
  directional, mispredicts the chapter's own *naar de garage* 'to the garage' and *van Utrecht*
  'from Utrecht' when read as stated; it holds as a necessary condition.

## TODO

* The extraction pairs with the selected *op* of *wachten op* 'wait for' need a non-spatial reading,
  which Helmantel's classes lack, and are not rows; nor are the auxiliary judgments, whose
  auxiliary would need a link to a Dutch verb entry.
* The exclusion of postpositional phrases from verbs incompatible with a change of location,
  *zitten* 'sit', is not formalized.

## References

* [broekhuis-corver-2026a]
* [broekhuis-corver-2026c]
* [helmantel-2002]
-/

@[expose] public section

namespace BroekhuisCorver2026

open Dutch.Adpositions Helmantel2002 ArgumentStructure Verb

/-! ### The internal structure of an adpositional phrase -/

/-- The complement of a transitive adposition: a noun phrase, a prepositional phrase, or an
R-pronoun, the proform of a locational prepositional phrase. -/
inductive ComplementKind where
  | nominal
  | prePP
  | rPronoun
  deriving DecidableEq, Repr, Fintype

/-- Where a complement is pronounced in `[FP _ F [P _]]`: in its base position after the
adposition, or in the specifier of the functional projection FP above it. -/
inductive Site where
  | base
  | spec
  deriving DecidableEq, Repr, Fintype

/-- The adposition's position among the three of the phrase; the head of FP is silent. -/
def headPosition : Fin 3 := 1

namespace Site

/-- The position of a site: the specifier precedes the adposition, the base position follows it. -/
def position : Site → Fin 3
  | spec => 0
  | base => 2

/-- The head direction of the phrase, read off the positions of the adposition and its
complement. -/
def headDirection (s : Site) : HeadDirection := .ofLT headPosition s.position

/-- Extraction from an adpositional phrase requires the extracted element to precede the
adpositional head. -/
def Extractable (s : Site) : Prop := s.position < headPosition

instance : DecidablePred Extractable := fun s ↦
  inferInstanceAs (Decidable (s.position < headPosition))

theorem headDirection_eq_headFinal {s : Site} : s.headDirection = .headFinal ↔ s = .spec := by
  cases s <;> decide

theorem extractable_iff {s : Site} : s.Extractable ↔ s = .spec := by
  cases s <;> decide

end Site

/-- The traditional class, read off the head direction of the phrase: the adposition precedes a
complement in its base position and follows a raised one, and a raised prepositional phrase brings
its own head before the noun phrase, so that the whole is a circumposition. An R-pronoun counts
with the prepositions, whose readings it keeps, and an adposition with no complement has no
class. -/
def linearization : Option ComplementKind → Site → Option Adposition.Linearization
  | none, _ => none
  | some k, s =>
    some <| match k, s.headDirection with
      | .nominal, .headFinal => .post
      | .prePP, .headFinal => .circum
      | _, _ => .pre

theorem linearization_eq_post_iff {k : ComplementKind} {s : Site} :
    linearization (some k) s = some .post ↔ k = .nominal ∧ s = .spec := by
  cases k <;> cases s <;> decide

theorem linearization_eq_circum_iff {k : ComplementKind} {s : Site} :
    linearization (some k) s = some .circum ↔ k = .prePP ∧ s = .spec := by
  cases k <;> cases s <;> decide

/-- The structure derives each of the four traditional classes, so none of them need be listed in
the lexicon, and no other order: an adposition never surfaces inside its complement. -/
theorem range_linearization :
    Set.range (Function.uncurry linearization) = {some .inposition}ᶜ := by
  ext o
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨⟨k, s⟩, rfl⟩
    cases k with
    | none => cases s <;> decide
    | some k => cases k <;> cases s <;> decide
  · rcases o with _ | _ | _ | _ | _
    exacts [⟨(none, .base), rfl⟩, ⟨(some .nominal, .base), rfl⟩,
      ⟨(some .nominal, .spec), rfl⟩, ⟨(some .prePP, .spec), rfl⟩, absurd rfl h]

/-! ### The condition on raising -/

/-- `Reads c k s r`: a phrase whose adposition has Helmantel's class `c`, with a complement of
kind `k` at site `s`, has reading `r`. A noun phrase raises to be read as a path in the specifier,
which the object of a point locative cannot be; otherwise the reading is the adposition's own, with
the noun phrase in its base position, or with a prepositional phrase or an R-pronoun, which denote
locations, raised. -/
def Reads (c : LocativeClass) : ComplementKind → Site → Reading → Prop
  | .nominal, .spec, r => r = .path ∧ c ≠ .point
  | .nominal, .base, r => c.Has r
  | _, .spec, r => c.Has r
  | _, .base, _ => False

instance (c : LocativeClass) (k : ComplementKind) (s : Site) (r : Reading) :
    Decidable (Reads c k s r) := by
  cases k <;> cases s <;> unfold Reads <;> infer_instance

variable {c : LocativeClass} {k : ComplementKind} {s : Site} {r : Reading}

-- (21), (26a,b)
theorem reads_path_of_linearization_eq_post (h : Reads c k s r)
    (hl : linearization (some k) s = some .post) : r = .path := by
  obtain ⟨rfl, rfl⟩ := linearization_eq_post_iff.1 hl
  exact h.1

/-- R-pronominalization is confined to prepositional phrases: an R-pronoun is never read as a path,
so its phrase has exactly the readings of the adposition's prepositional phrase, and *de wandeling
er op* 'the hike on it' has only the locational reading of *op de berg* 'on the mountain'. -/
theorem reads_rPronoun_iff : Reads c .rPronoun s r ↔ s = .spec ∧ Reads c .nominal .base r := by
  cases s <;> simp [Reads]

/-! ### Extraction -/

-- (53), (54)
theorem extractable_iff_of_linearization_eq_pre (h : Reads c k s r)
    (hl : linearization (some k) s = some .pre) : s.Extractable ↔ k = .rPronoun := by
  cases k <;> cases s <;> simp only [Reads] at h <;> revert hl <;> decide

-- (58), (60b): a postposition lets its noun phrase go, a circumposition its prepositional phrase
theorem extractable_of_linearization_ne_pre (hl : linearization (some k) s ≠ some .pre) :
    s.Extractable := by
  revert hl; cases k <;> cases s <;> decide

/-- The reading of the prepositional phrase a circumposition raises: a location, as a
prepositional complement denotes, unless its adposition is a point locative and has none. -/
def complementReading (c : LocativeClass) : Reading := if c = .point then .path else .location

theorem not_extractable_of_reads_complementReading
    (h : Reads c .nominal s (complementReading c)) : ¬ s.Extractable := by
  revert h; cases c <;> cases s <;> decide

/-! ### The Dutch lexicon -/

/-- Helmantel's spatial prepositions in the fragment, with their classes. -/
def classed : List (Dutch.Adposition × LocativeClass) :=
  narrowLocatives.map (·, .narrow) ++ pointLocatives.map (·, .point) ++
    extendedLocatives.map (·, .extended)

/-- The reading of a use whose path has direction `d`. -/
def reading (d : Spatial.Path.Direction) : Reading := if d = .place then .location else .path

/-- Every spatial use of Helmantel's prepositions that the grammar records is read at the site its
order shows, a prepositional use with the noun phrase in its base position and a postpositional one
with it raised. No point locative such as *naar* 'to' is then a postposition, a narrow locative
such as *op* is postpositional exactly in its directional use, and an extended locative such as
*over* 'across' can be directional in either order. -/
theorem reads_uses : ∀ p ∈ classed, ∀ l, ∀ d ∈ p.1.direction l,
    ∃ s, linearization (some .nominal) s = some l ∧ Reads p.2 .nominal s (reading d) := by
  decide

private theorem circumposition_parts :
    ∀ a ∈ inventory, a.IsCircumposition → ∃ p ∈ classed, ∃ b ∈ inventory,
      a.morphs = p.1.morphs ++ b.morphs ∧ (b.IsPostposition ∨ b.IsParticle) := by
  decide

/-- A circumposition patterns with a preposition under extraction. Every circumposition of the
grammar is one of Helmantel's prepositions followed by a postposition or a particle, and the
prepositional phrase it raises keeps its noun phrase in its base position, so that the noun phrase
cannot leave the circumpositional phrase while an R-pronoun in its place can: *Jan is daar
gisteren van af gesprongen* 'Jan jumped off it yesterday', but not with *het dak* 'the roof'. -/
theorem circumposition_extraction :
    ∀ a ∈ inventory, a.IsCircumposition → ∃ p ∈ classed, ∃ b ∈ inventory,
      a.morphs = p.1.morphs ++ b.morphs ∧ (b.IsPostposition ∨ b.IsParticle) ∧
        (∀ s, Reads p.2 .nominal s (complementReading p.2) → ¬ s.Extractable) ∧
        Reads p.2 .rPronoun .spec (complementReading p.2) ∧ Site.spec.Extractable :=
  fun a ha hc ↦ (circumposition_parts a ha hc).imp fun p ⟨hp, b, hb, hm, hb'⟩ ↦
    ⟨hp, b, hb, hm, hb', fun _ ↦ not_extractable_of_reads_complementReading,
      by cases p.2 <;> decide, by decide⟩

-- p. 1, p. 9: each simple adposition is a preposition but *af*, *heen*, *toe*, once prepositions
theorem isPreposition_of_isSimple : ∀ a ∈ inventory, a.IsSimple →
    a.IsPreposition ∨ a.toAdposition ∈ [af, heen, toe].map (·.toAdposition) := by
  decide

/-! ### The rows -/

/-- Helmantel's class of an entry, if she classifies it. -/
def locativeClass? (a : Dutch.Adposition) : Option LocativeClass :=
  (classed.find? fun p ↦ p.1.toAdposition = a.toAdposition).map (·.2)

/-- An element of kind `k` can leave the phrase of an adposition of class `c` when some reading
licenses it at a site before the adposition. -/
def Leaves (c : LocativeClass) (k : ComplementKind) : Prop :=
  ∃ s r, Reads c k s r ∧ s.Extractable

instance (c : LocativeClass) (k : ComplementKind) : Decidable (Leaves c k) := by
  unfold Leaves; infer_instance

/-- The extraction rows, each with the adposition whose phrase the element leaves and the kind of
the element. -/
def extractions : List (Datum × Dutch.Adposition × ComplementKind) :=
  [(Examples.ex_56b, naast, .rPronoun), (Examples.ex_57b, boven, .rPronoun),
    (Examples.ex_58b, in_, .nominal), (Examples.ex_58c, in_, .nominal),
    (Examples.ex_59b_daar, van, .rPronoun), (Examples.ex_59b_dak, van, .nominal),
    (Examples.ex_59c_waar, van, .rPronoun), (Examples.ex_59c_dak, van, .nominal)]

-- (56b)-(59c): each row's adposition is one of its words, and `Leaves` gives its judgment
theorem extraction_rows : ∀ x ∈ extractions,
    (∃ t ∈ x.1.glossedTokens, x.2.1.morphs = [.free t.1]) ∧
      ∃ c ∈ locativeClass? x.2.1, x.1.judgment.band = .ofProp (Leaves c x.2.2) := by
  decide +kernel

/-- The readings of *de wandeling er op* 'the hike on it', in the order the chapter prints them. -/
def erOpReadings : List Reading := [.location, .path]

-- (26c)
theorem erOp_rows : Examples.ex_26c.readings.length = erOpReadings.length ∧
    (∃ t ∈ Examples.ex_26c.glossedTokens, op.morphs = [.free t.1]) ∧
      ∃ c ∈ locativeClass? op, ∀ x ∈ Examples.ex_26c.readings.zip erOpReadings,
        x.1.2.band = .ofProp (∃ s, Reads c .rPronoun s x.2) := by
  decide +kernel

theorem rows_covered :
    Examples.all.map (·.id) = Examples.ex_26c.id :: extractions.map (·.1.id) := by
  decide +kernel

/-! ### Directional phrases and the perfect auxiliary -/

/-- A path complementive makes the event of a verb of motion a change of location and the verb
unaccusative, and a location complementive leaves it unergative. -/
def verbClass : Reading → TransitivityClass
  | .location => .unergative
  | .path => .unaccusative

theorem selection_verbClass_eq_be_iff (aux : PerfectAuxiliary) (x : Reading) :
    (verbClass x).selection aux = .be ↔ x = .path := by
  cases x <;> simp [verbClass, TransitivityClass.selection]

/-- In *de fietser heeft op de heuvel gereden* 'the cyclist rode on the hill' the prepositional
phrase of *op* is locational and its verb takes *hebben* 'have', and in *de fietser is de heuvel
op gereden* 'the cyclist rode up the hill' the postpositional phrase denotes a goal path and its
verb takes *zijn* 'be'. -/
theorem perfect_op (aux : PerfectAuxiliary) :
    (op.direction .pre).map (fun d ↦ (verbClass (reading d)).selection aux) = some .have ∧
      (op.direction .post).map (fun d ↦ (verbClass (reading d)).selection aux) = some .be :=
  ⟨rfl, rfl⟩

-- (22): every postpositional phrase is a path complementive and its verb of motion takes *zijn*
theorem postP_selects_zijn (aux : PerfectAuxiliary) :
    ∀ a ∈ inventory, a.IsPostposition →
      ∃ d ∈ a.direction .post, (verbClass (reading d)).selection aux = .be :=
  fun a ha h ↦ (exists_direction_post_ne_place a ha h).imp fun _ ⟨hd, hne⟩ ↦
    ⟨hd, (selection_verbClass_eq_be_iff aux _).2 (by simp [reading, hne])⟩

end BroekhuisCorver2026
