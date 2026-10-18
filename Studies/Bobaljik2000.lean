module

public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.InsideOut
public import Linglib.Data.Examples.Bobaljik2000

/-!
# Bobaljik (2000): The ins and outs of contextual allomorphy

Bobaljik argues that Vocabulary Insertion proceeds from the root outward and rewrites each
morpheme as its exponent, so that an allomorph can look outward only at bare morphosyntactic
features and inward only at diacritics and inserted vocabulary items. In Itelmen the Class II
marker sees the root's class diacritic inward and both agreement nodes outward, while the subject
prefix, inserted last, sees nothing of the object. In Chukchi the third-person subject prefix
*ne-* is absent exactly when the object suffix is *-nin* or *-ninet*; since a third-singular
object presents the same features whatever its subject, the trigger is the inserted item, an
inward sensitivity.

## Main statements

* `Itelmen.rows_morphs`, `Chukchi.rows_morphs`: the Itelmen verbs and the Chukchi Past I
  paradigm derive from one Vocabulary each.
* `Itelmen.prefix_sees_no_object`: when the subject prefix is inserted, nothing of the object
  agreement remains for it to be conditioned by; under non-deletion it would remain.
* `Chukchi.object_features_cannot_bleed`: a deletion of *ne-* keyed to the object's features
  overapplies under non-deletion and never applies under rewriting.
* `Chukchi.ditransitive_retains_prefix`: when the verb agrees with a second-person dative, a
  third-singular subject acting on a third-singular direct object keeps *ne-*.

## Implementation notes

* Context is hierarchical. Mood is omitted, every form being realis or indicative, and the
  Chukchi Past I has no overt tense, so its T node is omitted.
* Every Itelmen verb has the class position, which the paper allows to be syntactic or added
  after syntax; in Class I it is null.
* Third-person objects carry person and number, as the paper's Chukchi trees and vocabulary
  write them, not the personless third person of its Itelmen agreement analysis.
* The rows list the paper's citation forms of the subject prefix *t-* and the present *-s-*,
  which two Itelmen examples print as *t’* and *z*.

## References

* [J. D. Bobaljik, *The ins and outs of contextual allomorphy*][bobaljik-2000]
* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
-/

@[expose] public section

namespace Bobaljik2000

open DistributedMorphology ComplexHead

/-- A terminal carries present tense, the class position, the Class II diacritic, or an agreement
node with person and number; an inserted vocabulary item is a morphophonological feature. -/
inductive Feature where
  | pres | classII | classMarker | agrO | agrS | first | second | third | sg | pl
  | item (e : String)
  deriving DecidableEq, Repr

open Feature

/-- An inserted exponent presents its identity. -/
def itemFeatures (e : String) : List Feature := [item e]

/-- The surface exponents after inside-out insertion under hierarchical locality, null exponents
dropped. -/
def morphs (dis : Discharge) (voc : List (VocabularyItem Feature String))
    (w : ComplexHead (Morpheme Feature String) (Morpheme Feature String)) : List String :=
  (w.insertAll (· = "") voc .hierarchical itemFeatures dis).exponents.filter (· ≠ "")

/-- The context head `i` presents when inside-out insertion reaches it. -/
def stepContext (voc : List (VocabularyItem Feature String))
    (w : ComplexHead (Morpheme Feature String) (Morpheme Feature String)) (dis : Discharge)
    (i : ℕ) : Neighborhood (List Feature) :=
  (w.insertUpTo (· = "") voc .hierarchical itemFeatures dis i).contextAt
    (· = "") .hierarchical itemFeatures i

/-- The person and number of an argument, as the rows name them. -/
def phi : String → Option (List Feature)
  | "1sg" => some [first, sg] | "2sg" => some [second, sg] | "3sg" => some [third, sg]
  | "1pl" => some [first, pl] | "2pl" => some [second, pl] | "3pl" => some [third, pl]
  | _ => none

/-- A row's exponents, in linear order. -/
def exponents (ex : Datum) : List String :=
  ["m1", "m2", "m3", "m4", "m5"].filterMap ex.feature?

/-! ### Itelmen -/

namespace Itelmen

/-- Present *-s-*. The Class II marker is conditioned inward by the root's class diacritic, past
the tense suffix, and outward by both agreement nodes, *-ki-* marking a first-person subject
acting on a third-person object and *-čŋ-* a second-singular subject; Class I is null. Third-person
object agreement (8) is *-čen*, plural *-čeʔn*, under a first-person subject and *-in*, plural
*-iʔn*, under a second-singular one. The subject prefix is *t-* for first singular and null for
second singular. -/
def vocab : List (VocabularyItem Feature String) :=
  [{pres} ⟷ "s",
   ⟨{(0, classMarker), (-2, classII), (1, agrO), (1, third), (2, agrS), (2, first)}, "ki"⟩,
   ⟨{(0, classMarker), (-2, classII), (1, agrO), (1, third), (2, agrS), (2, second), (2, sg)},
     "čŋ"⟩,
   {classMarker} ⟷ "",
   ⟨{(0, agrO), (0, third), (0, sg), (1, agrS), (1, first)}, "čen"⟩,
   ⟨{(0, agrO), (0, third), (0, pl), (1, agrS), (1, first)}, "čeʔn"⟩,
   ⟨{(0, agrO), (0, third), (0, sg), (1, agrS), (1, second), (1, sg)}, "in"⟩,
   ⟨{(0, agrO), (0, third), (0, pl), (1, agrS), (1, second), (1, sg)}, "iʔn"⟩,
   {agrS, first, sg} ⟷ "t", {agrS, second, sg} ⟷ ""]

/-- The verb is the root with its class diacritics, then present tense, the class position, and
the object and subject agreement nodes, as in (16). -/
def word (r : String) (cls subj obj : List Feature) :
    ComplexHead (Morpheme Feature String) (Morpheme Feature String) :=
  ⟨⟨cls, some r, .after⟩,
   [⟨[pres], none, .after⟩, ⟨[classMarker], none, .after⟩, ⟨agrO :: obj, none, .after⟩,
    ⟨agrS :: subj, none, .before⟩]⟩

/-- The class diacritics of a root, as the rows name its class. -/
def rootClass : String → Option (List Feature)
  | "I" => some []
  | "II" => some [classII]
  | _ => none

/-- The verb of an Itelmen row. -/
def ofRow (ex : Datum) :
    Option (ComplexHead (Morpheme Feature String) (Morpheme Feature String)) := do
  word (← ex.feature? "root") (← rootClass (← ex.feature? "rootClass"))
    (← phi (← ex.feature? "subj")) (← phi (← ex.feature? "obj"))

/-- In the forms (9) and (10) the Class II marker appears where insertion finds the class
diacritic inward, in the shape the agreement outward selects. -/
theorem rows_morphs :
    ∀ ex ∈ Examples.all, ex.language = "itel1242" →
      (ofRow ex).map (morphs .rewriting vocab) = some (exponents ex) := by
  decide

/-- The verb of (9b), *t-tɸ-s-ki-čeʔn*, is 'bring' with a first-singular subject and a
third-plural object. -/
def bring : ComplexHead (Morpheme Feature String) (Morpheme Feature String) :=
  word "tɸ" [classII] [first, sg] [third, pl]

/-- In (9b) the Class II marker sees the root's diacritic inward, past the tense suffix already
rewritten as *-s-*, and both agreement nodes outward, bare. -/
theorem class_marker_context :
    stepContext vocab bring .rewriting 1 =
      ⟨[classMarker], [[item "s"], [classII, item "tɸ"]],
        [[agrO, third, pl], [agrS, first, sg]]⟩ := by
  decide

/-- When the subject prefix of (9b) is reached, every morpheme inside it has been rewritten as its
exponent, and nothing of the object agreement remains for the prefix to be conditioned by. Under
the non-deletion of [halle-marantz-1993] the object's features would remain. -/
theorem prefix_sees_no_object :
    (stepContext vocab bring .rewriting 3).leftCtx =
        [[item "čeʔn"], [item "ki"], [item "s"], [classII, item "tɸ"]] ∧
      (stepContext vocab bring .nondeletion 3).leftCtx.head? =
        some [agrO, third, pl, item "čeʔn"] := by
  decide

end Itelmen

/-! ### Chukchi -/

namespace Chukchi

/-- The Past I object suffixes (20) are *-nin* and *-ninet* under a third-singular subject (24),
otherwise *-ɣʔen* and *-net* for a third-person object, and the first- and second-person
suffixes. -/
def objectVocab : List (VocabularyItem Feature String) :=
  [⟨{(0, agrO), (0, third), (0, sg), (1, agrS), (1, third), (1, sg)}, "nin"⟩,
   ⟨{(0, agrO), (0, third), (0, pl), (1, agrS), (1, third), (1, sg)}, "ninet"⟩,
   {agrO, third, sg} ⟷ "ɣʔen", {agrO, third, pl} ⟷ "net",
   {agrO, first, sg} ⟷ "ɣəm", {agrO, first, pl} ⟷ "mək",
   {agrO, second, sg} ⟷ "ɣət", {agrO, second, pl} ⟷ "tək"]

/-- The object suffixes, and the third-person subject prefix *ne-*, impoverished to zero inward of
the item *-nin* or *-ninet*. -/
def vocab : List (VocabularyItem Feature String) :=
  objectVocab ++
    [⟨{(0, agrS), (0, third), (-1, item "nin")}, ""⟩,
     ⟨{(0, agrS), (0, third), (-1, item "ninet")}, ""⟩, {agrS, third} ⟷ "ne"]

/-- The Past I verb is the root with the object and subject agreement nodes. -/
def word (r : String) (subj obj : List Feature) :
    ComplexHead (Morpheme Feature String) (Morpheme Feature String) :=
  ⟨⟨[], some r, .after⟩, [⟨agrO :: obj, none, .after⟩, ⟨agrS :: subj, none, .before⟩]⟩

/-- Object agreement targets a first- or second-person indirect object over a third-person direct
object, by the person hierarchy of §3.2.2, and otherwise the direct object. -/
def agreesWith (dObj : List Feature) : Option (List Feature) → List Feature
  | some io => if third ∈ dObj ∧ third ∉ io then io else dObj
  | none => dObj

/-- The verb of a Chukchi row. -/
def ofRow (ex : Datum) :
    Option (ComplexHead (Morpheme Feature String) (Morpheme Feature String)) := do
  let io ← match ex.feature? "io" with
    | some s => (phi s).map some
    | none => some none
  word (← ex.feature? "root") (← phi (← ex.feature? "subj"))
    (agreesWith (← phi (← ex.feature? "obj")) io)

/-- Across the Past I paradigm (19) and the ditransitive (27), *ne-* is absent exactly where
*-nin* or *-ninet* is inserted. -/
theorem rows_morphs :
    ∀ ex ∈ Examples.all, ex.language = "chuk1273" →
      (ofRow ex).map (morphs .rewriting vocab) = some (exponents ex) := by
  decide

/-- The impossible Pseudo-Chukchi rule (28a), deleting *ne-* in the context of a third-singular
object rather than of the item *-nin*. -/
def pseudoVocab : List (VocabularyItem Feature String) :=
  objectVocab ++
    [⟨{(0, agrS), (0, third), (-1, agrO), (-1, third), (-1, sg)}, ""⟩, {agrS, third} ⟷ "ne"]

/-- A third-singular object presents the same features under a third-singular subject, where it
is spelled out *-nin*, and under a third-plural one, where it is *-ɣʔen* (23). Keyed to those
features, as in (28a), the deletion of *ne-* overapplies under non-deletion, removing the prefix
of (19i). Under rewriting the features are gone when the prefix is inserted, so the deletion
never applies, leaving the prefix of (19c). -/
theorem object_features_cannot_bleed :
    morphs .nondeletion pseudoVocab (word "ɬʔu" [third, pl] [third, sg]) = ["ɬʔu", "ɣʔen"] ∧
      morphs .rewriting pseudoVocab (word "ɬʔu" [third, sg] [third, sg]) =
        ["ne", "ɬʔu", "nin"] := by
  decide

/-- In both (19c) and (27) a third-singular subject acts on a third-singular direct object. In
(27) the verb agrees with the second-person dative instead, *-nin* is not inserted, and *ne-*
stays, so the prefix tracks the item, not the syntactic configuration. -/
theorem ditransitive_retains_prefix :
    morphs .rewriting vocab (word "ɬʔu" [third, sg] (agreesWith [third, sg] none)) =
        ["ɬʔu", "nin"] ∧
      morphs .rewriting vocab (word "jəl" [third, sg] (agreesWith [third, sg] (some [second, sg])))
        = ["ne", "jəl", "ɣət"] := by
  decide

end Chukchi

end Bobaljik2000
