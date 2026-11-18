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
spatial use the grammar records sits where its order
puts it](##exists_reads_of_mem_direction), [an R-pronoun keeps the prepositional
reading](##reads_rPronoun_iff), and since only a raised complement can leave the phrase, [the noun
phrase of a circumposition stays inside](##circumposition_extraction). A [path
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

/-- A complement that denotes a location: a prepositional phrase, and an R-pronoun, the proform of
one. A noun phrase does not, and the specifier can read it as a path. -/
def ComplementKind.IsLocational : ComplementKind → Prop
  | nominal => False
  | prePP | rPronoun => True

instance : DecidablePred ComplementKind.IsLocational := fun k ↦ by
  cases k <;> unfold ComplementKind.IsLocational <;> infer_instance

@[simp] theorem ComplementKind.not_isLocational_nominal : ¬ nominal.IsLocational := id

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

end Site

/-- The traditional class, read off the head direction of the phrase: the adposition precedes a
complement in its base position and follows a raised noun phrase, and a raised prepositional phrase
brings its own head before the noun phrase, so that the whole is a circumposition. A raised
R-pronoun counts with the prepositions, whose readings it keeps, as would a prepositional phrase
left in its base position; an adposition with no complement has no class. -/
def linearization : Option ComplementKind → Site → Option Adposition.Linearization
  | none, _ => none
  | some k, s =>
    some <| match k, s.headDirection with
      | .nominal, .headInitial => .pre
      | .nominal, .headFinal => .post
      | .prePP, .headFinal => .circum
      | .rPronoun, .headFinal => .pre
      | .prePP, .headInitial | .rPronoun, .headInitial => .pre

theorem linearization_eq_post_iff {k : ComplementKind} {s : Site} :
    linearization (some k) s = some .post ↔ k = .nominal ∧ s = .spec := by
  cases k <;> cases s <;> decide

-- (62c)
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
kind `k` at site `s`, has reading `r`. A locational complement raises and leaves the reading to the
adposition. A noun phrase either stays in its base position with the adposition's reading or raises
to be read as a path, which the object of a point locative cannot be. -/
def Reads (c : LocativeClass) (k : ComplementKind) : Site → Reading → Prop
  | .base, r => ¬ k.IsLocational ∧ c.Has r
  | .spec, r => if k.IsLocational then c.Has r else r = .path ∧ c ≠ .point

instance (c : LocativeClass) (k : ComplementKind) (s : Site) (r : Reading) :
    Decidable (Reads c k s r) := by
  cases s <;> unfold Reads <;> infer_instance

variable {c : LocativeClass} {k : ComplementKind} {s : Site} {r : Reading}

-- (21), (26a,b)
theorem reads_path_of_linearization_eq_post (h : Reads c k s r)
    (hl : linearization (some k) s = some .post) : r = .path := by
  obtain ⟨rfl, rfl⟩ := linearization_eq_post_iff.1 hl
  exact h.1

theorem reads_iff_of_isLocational (hk : k.IsLocational) :
    Reads c k s r ↔ s = .spec ∧ Reads c .nominal .base r := by
  cases s <;> simp [Reads, hk]

/-- R-pronominalization is confined to prepositional phrases: an R-pronoun is locational and never
read as a path, so its phrase has exactly the readings of the adposition's prepositional phrase,
and *de wandeling er op* 'the hike on it' has only the locational reading of *op de berg* 'on the
mountain'. -/
theorem reads_rPronoun_iff : Reads c .rPronoun s r ↔ s = .spec ∧ Reads c .nominal .base r :=
  reads_iff_of_isLocational trivial

/-! ### Extraction -/

/-- An element of kind `k` can leave the phrase of an adposition of class `c` in reading `r` when
it can stand before the adposition. -/
def Leaves (c : LocativeClass) (k : ComplementKind) (r : Reading) : Prop :=
  ∃ s, Reads c k s r ∧ s.Extractable

instance (c : LocativeClass) (k : ComplementKind) (r : Reading) : Decidable (Leaves c k r) := by
  unfold Leaves; infer_instance

-- (53), (54)
theorem extractable_iff_of_linearization_eq_pre (h : Reads c k s r)
    (hl : linearization (some k) s = some .pre) : s.Extractable ↔ k = .rPronoun := by
  cases k <;> cases s <;> simp [Reads, ComplementKind.IsLocational] at h <;> revert hl <;> decide

-- (58), (60b): a postposition lets its noun phrase go, a circumposition its prepositional phrase
theorem extractable_of_linearization_ne_pre (hl : linearization (some k) s ≠ some .pre) :
    s.Extractable := by
  revert hl; cases k <;> cases s <;> decide

/-- The reading of the prepositional phrase a circumposition raises: a location, as a
prepositional complement denotes, unless its adposition is a point locative and has none. -/
def complementReading : LocativeClass → Reading
  | .point => .path
  | .narrow | .extended => .location

/-- A circumposition patterns with a preposition under extraction: the prepositional phrase it
raises keeps its noun phrase in its base position, whatever the class of its adposition, so the
noun phrase cannot leave the circumpositional phrase while an R-pronoun in its place can. *Jan is
daar gisteren van af gesprongen* 'Jan jumped off it yesterday' is good, and with *het dak* 'the
roof' bad. -/
theorem circumposition_extraction (c : LocativeClass) :
    ¬ Leaves c .nominal (complementReading c) ∧ Leaves c .rPronoun (complementReading c) := by
  cases c <;> decide

/-! ### The Dutch lexicon -/

/-- Helmantel's spatial prepositions in the fragment, with their classes. -/
def classed : List (Dutch.Adposition × LocativeClass) :=
  narrowLocatives.map (·, .narrow) ++ pointLocatives.map (·, .point) ++
    extendedLocatives.map (·, .extended)

/-- The reading of a use whose path has direction `d`. -/
def reading : Spatial.Path.Direction → Reading
  | .place => .location
  | .goal | .source | .route => .path

/-- Every spatial use of Helmantel's prepositions that the grammar records is read at the site its
order shows, a prepositional use with the noun phrase in its base position and a postpositional one
with it raised. No point locative such as *naar* 'to' is then a postposition, a narrow locative
such as *op* is postpositional exactly in its directional use, and an extended locative such as
*over* 'across' can be directional in either order. -/
theorem exists_reads_of_mem_direction : ∀ p ∈ classed, ∀ l, ∀ d ∈ p.1.direction l,
    ∃ s, linearization (some .nominal) s = some l ∧ Reads p.2 .nominal s (reading d) := by
  decide

-- (61): every circumposition is one of Helmantel's prepositions and a postposition or particle
theorem circumposition_parts :
    ∀ a ∈ inventory, a.IsCircumposition → ∃ p ∈ classed, ∃ b ∈ inventory,
      a.morphs = p.1.morphs ++ b.morphs ∧ (b.IsPostposition ∨ b.IsParticle) := by
  decide

-- p. 1, p. 9: each simple adposition is a preposition but *af*, *heen*, *toe*, once prepositions
theorem isPreposition_of_isSimple : ∀ a ∈ inventory, a.IsSimple →
    a.IsPreposition ∨ a.toAdposition ∈ [af, heen, toe].map (·.toAdposition) := by
  decide

/-! ### The rows -/

/-- Helmantel's class of an entry, if she classifies it. -/
def locativeClass? (a : Dutch.Adposition) : Option LocativeClass :=
  (classed.find? fun p ↦ p.1.toAdposition = a.toAdposition).map (·.2)

/-- An extraction a row judges. -/
structure Extraction where
  /-- The row. -/
  row : Datum
  /-- The adposition whose phrase the element leaves. -/
  adposition : Dutch.Adposition
  /-- The kind of the element. -/
  kind : ComplementKind

/-- The extraction rows. -/
def extractions : List Extraction :=
  [⟨Examples.ex_56b, naast, .rPronoun⟩, ⟨Examples.ex_57b, boven, .rPronoun⟩,
    ⟨Examples.ex_58b, in_, .nominal⟩, ⟨Examples.ex_58c, in_, .nominal⟩,
    ⟨Examples.ex_59b_daar, van, .rPronoun⟩, ⟨Examples.ex_59b_dak, van, .nominal⟩,
    ⟨Examples.ex_59c_waar, van, .rPronoun⟩, ⟨Examples.ex_59c_dak, van, .nominal⟩]

-- (56b)-(59c): each row's adposition is one of its words, and `Leaves` gives its judgment
theorem extraction_rows : ∀ x ∈ extractions,
    (∃ t ∈ x.row.glossedTokens, x.adposition.morphs = [.free t.1]) ∧
      ∃ c ∈ locativeClass? x.adposition,
        x.row.judgment.band = .ofProp (∃ r, Leaves c x.kind r) := by
  decide +kernel

/-- The readings the chapter prints for *de wandeling er op* 'the hike on it'. -/
def erOpReadings : List (String × Reading) := [("on it", .location), ("up it", .path)]

-- (26c)
theorem erOp_rows : (∃ t ∈ Examples.ex_26c.glossedTokens, op.morphs = [.free t.1]) ∧
    ∃ c ∈ locativeClass? op, ∀ x ∈ Examples.ex_26c.readings,
      ∃ r ∈ erOpReadings.lookup x.1, x.2.band = .ofProp (∃ s, Reads c .rPronoun s r) := by
  decide +kernel

theorem rows_covered :
    Examples.all.map (·.id) = Examples.ex_26c.id :: extractions.map (·.row.id) := by
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
theorem selection_eq_be_of_isPostposition (aux : PerfectAuxiliary) :
    ∀ a ∈ inventory, a.IsPostposition →
      ∃ d ∈ a.direction .post, (verbClass (reading d)).selection aux = .be :=
  fun a ha h ↦ (exists_direction_post_ne_place a ha h).imp fun d ⟨hd, hne⟩ ↦
    ⟨hd, (selection_verbClass_eq_be_iff aux _).2 (by cases d <;> simp_all [reading])⟩

end BroekhuisCorver2026
