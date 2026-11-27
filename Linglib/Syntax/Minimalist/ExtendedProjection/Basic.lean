/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Cartography
public import Linglib.Syntax.Minimalist.Category
public import Linglib.Syntax.Spine.ExtendedProjection
public import Linglib.Syntax.Spine.Hierarchy
public import Mathlib.Order.Comparable

/-!
# The extended projections of the categories

Which functional head stands above which? The categories are not numbered here. This file takes the
spines that the literature draws and orders the categories by the hierarchy of those spines: a
category is **no higher than** another, written `c ≤ d`, when steps of the cited spines lead from
it up to the other.

Harley's clause runs from the verb up to tense, and Rizzi's from tense up to Force. So the verb
comes out lower than Force, though neither source draws both.

Since the order pools many sources, it shows where they agree and where they do not. Two categories
that the sources order in both ways come out **level**, each no higher than the other. Rizzi's
topics stand on both sides of the focus, so topic and focus are level. Cinque interleaves the
tenses, moods, modalities and aspects, Zanuttini finds negation on both sides of tense, and Laka
places polarity below tense in English and above it in Basque, so all these heads are level with
tense. Where the sources agree, one category is lower than the next: the verb, little v, Voice,
tense, finiteness, focus and Force rise in that order, and so do the noun, the dividing head, the
counting head, the determiner and the case shell. Where no source relates two categories they are
unrelated, as Keine's nominalized clause and the CP are: neither contains the other.

The order never crosses from one family of categories to another, since no cited spine does, and
the lexical head of a family is the lowest category of the family. A spine of categories that
ascends in the order is therefore an extended projection: its heads are of one family, and each is
no higher than the next head up.

The order holds exactly what the sources require. Give each category a height so that heights
never drop going up a cited spine. A category that is no higher than another then gets a height no
greater, and one category is no higher than another only if every such choice of heights says so.
No choice of heights that respects every source tells tense from negation. Such a height is what
Grimshaw calls the functional value of a head.

## Implementation notes

`Minimalist.citedSequences` holds the cited spines, and `Minimalist.citedIdentifications` the pairs
of categories that a source takes to be one head. `Minimalist.citedSpines` is the set whose
hierarchy is the order: the cited sequences, and each identified pair as a two-head spine in both
orders, which makes the pair level. The general statements about a hierarchy are in
`Linglib/Syntax/Spine/Hierarchy.lean`, and the definition of an extended projection is in
`Linglib/Syntax/Spine/ExtendedProjection.lean`.

The order is an order instance, so that a category lower than another is related to it by `<`, two
level categories by `AntisymmRel (· ≤ ·)`, two unrelated ones by `IncompRel (· ≤ ·)`, and a map that
respects the order is `Monotone`. The instance is scoped. The categories themselves carry no order,
and a file that orders them adopts this one with `open scoped Minimalist.ExtendedProjection`. An
account in which heads are ordered by selection alone uses the categories without it.

That the cited spines ascend is `Minimalist.Cat.isChain_le`, the statements about heights are
`Minimalist.Cat.monotone_iff` and `Minimalist.Cat.le_iff_forall_le`, and `Cartography.Head.catHom`
sends Cinque's order into this one.

Citing a further structure can only add to the order. A statement that one category is no higher
than another therefore survives every later citation, while a statement that one is lower than
another, or that two are unrelated, holds of the structures cited so far.

Grimshaw leaves open whether the functional value must rise from each head to the next or may also
stay the same. Here it may stay the same, since a cited spine can repeat a head. For her the
adposition is the highest head of the nominal projection, as the complementizer is of the verbal
one. Here it is the lexical head of a family of its own.

A structure is transcribed as follows. A root, a VP or NP and the verb or noun are the lexical head,
an IP is `T`, Cinque's heads are read through `Cartography.Head.cat`, and the heads of a structure
that are not categories here (Agr, Cause, Deg, Laka's English AP) are left out, its other heads kept
in order. A spine stops where a head takes a complement of another family, as where Thoms and
colleagues' little v takes a noun phrase or Arregi and Pietraszko's determiner takes a clause, and a
modifier of another family, such as the adjective of Cinque's noun phrase, is left out. For Grimshaw
only a lexical head takes a complement it forms no extended projection with; in these two structures
the head that does so is not the lexical one. Cinque's demonstrative and numeral are specifiers,
taken as heads as his footnote allows; Zanuttini's numbered negations are all `Neg`; Laka's Σ is
`Pol`. Keine leaves open whether his nominalizer belongs to the extended projection of the clause it
selects, and it is taken to. Only the high applicative is cited: Pylkkänen's low applicative sits
below the verb, and with one `Appl` category citing both would make the verb, v and the applicative
one level.

`Cartography.Head.cat` sends Cinque's four aspect heads below Voice to inner aspect, the aspect of
the v shell, the other aspect heads to outer aspect, the speech-act mood to the speech-act head,
as Speas and Tenny project their speech-act phrase from Cinque's speech-act mood head, and the
other moods but the evidential to `Cat.Mood`.

The unsplit complementizer is identified with Force, the position of Rizzi's finite *che*. His
nonfinite *di* is in the finiteness position, so an infinitival complementizer is `Fin`.

## TODO

Inner aspect is placed by Liu and Yip's clause sizes, which follow Travis; Travis's own
structure, Kratzer's Voice and Svenonius's adpositional heads are not yet read from the sources.
No cited structure relates little n to the dividing head or D to the demonstrative, so those pairs
are incomparable.

## References

* [grimshaw-2000]
* [panagiotidis-2015]
* [harley-2013]
* [harley-2017]
* [pylkkanen-2008]
* [liu-yip-2026]
* [pollock-1989]
* [zanuttini-1997]
* [laka-1990]
* [keine-2020]
* [cinque-1999]
* [rizzi-1997]
* [egressy-2026]
* [speas-tenny-2003]
* [borer-2005]
* [cinque-2005]
* [newman-2024]
* [dendikken-2010]
* [arregi-pietraszko-2021]
* [thoms-etal-2026]
* [elkins-torrence-brown-2026]
-/

@[expose] public section

namespace Cartography.Head

/-- The **category** of one of Cinque's heads is the category it is an instance of: a tense is
`T`, a modality is `Mod`, and an aspect is inner aspect below Voice and outer aspect above it. -/
def cat : Head → Minimalist.Cat
  | voice => .Voice
  | aspSgCompletiveII | aspFrequentativeII | aspRepetitiveII | aspCelerativeII => .InnerAsp
  | tAnterior | tFuture | tPast => .T
  | modVolitional | modPossibility | modNecessity | modEpistemic => .Mod
  | moodEvidential => .Evid
  | moodSpeechAct => .SA
  | moodIrrealis | moodEvaluative => .Mood
  | _ => .Asp

@[simp] theorem family_cat (h : Head) : h.cat.family = .verbal := by
  cases h <;> rfl

end Cartography.Head

namespace Minimalist

/-!
### The cited structures

A **cited sequence** is the spine of a structure some source draws, its heads listed from the bottom
up. A **cited identification** is a pair of categories that a source takes to be one head.
-/

/-- The **cited sequences** are the spines the sources draw, each from the bottom up. The first is
Cinque's hierarchy of clausal heads. -/
def citedSequences : List (List Cat) :=
  [Cartography.Head.hierarchy.map Cartography.Head.cat,  -- [cinque-1999]
    [.V, .v], [.N, .n], [.A, .a],                 -- [panagiotidis-2015] (11), p. 18
    [.V, .v, .Voice, .T],                         -- [harley-2013] (2), p. 35
    [.V, .Appl, .Voice],                          -- [pylkkanen-2008] (6a), p. 14
    [.V, .v, .Appl, .Voice],                      -- [harley-2017] (18), p. 13
    [.V, .InnerAsp, .v, .Asp, .T, .C],            -- [liu-yip-2026] (1a), p. 3
    [.V, .Neg, .T, .C],                           -- [pollock-1989] (77), p. 397
    [.Mod, .Mood, .Neg, .T, .Mod, .Mod],          -- [zanuttini-1997] (106), p. 141
    [.Neg, .Asp, .Asp, .Neg, .T, .Neg],           -- [zanuttini-1997] (139), p. 99
    [.V, .Pol, .T], [.V, .T, .Pol],               -- [laka-1990] (16), p. 101
    [.T, .Pol, .C],                               -- [laka-1990] (46)–(47), p. 127
    [.v, .T, .Nmlz],                              -- [keine-2020] (106), p. 74
    [.V, .v, .T, .C],                             -- [keine-2020] (238), p. 156
    [.V, .v, .Voice, .Dir, .C],                   -- [elkins-torrence-brown-2026] (8), p. 6
    [.T, .Fin, .Top, .Foc, .Top, .Force],         -- [rizzi-1997] (41), p. 297
    [.T, .Foc, .Say],                             -- [egressy-2026] p. 13
    [.Mood, .SA],                                 -- [speas-tenny-2003] p. 332
    [.N, .Q, .Num, .D],                           -- [borer-2005] (8a), p. 96
    [.N, .Num, .Dem],                             -- [cinque-2005] (7a), p. 321
    [.n, .Poss, .Num],                            -- [thoms-etal-2026] (38), p. 22
    [.N, .D, .K],                                 -- [newman-2024] (217), p. 129
    [.D, .Lnk],                                   -- [arregi-pietraszko-2021] (14), p. 250
    [.P, .Place, .Path]]                          -- [dendikken-2010] (20c), p. 81

/-- The **cited identifications** are the pairs of categories a source takes to be one head.
Rizzi's *che* is in the force position, and Speas and Tenny's speech-act phrase is the projection
that encodes force. -/
def citedIdentifications : List (Cat × Cat) :=
  [(.C, .Force),                                  -- [rizzi-1997] p. 288
    (.SA, .Force)]                                -- [speas-tenny-2003] p. 317

/-- The **cited spines** are the cited sequences, together with a two-head spine in each order for
every cited identification, which makes the identified heads level. -/
def citedSpines : List (Spine Cat) :=
  citedSequences.map Spine.mk ++
    citedIdentifications.flatMap fun p ↦ [⟨[p.1, p.2]⟩, ⟨[p.2, p.1]⟩]

namespace Cat

variable {c d : Cat} {l : List Cat}

/-!
### The order of the categories

One category is **no higher than** another when steps of the cited spines lead from the first up
to the second. Two categories are **level** when each is no higher than the other, and one is
**lower than** another when it is no higher and the two are not level.
-/

/-- A category is **no higher than** another, written `c ≤ d`, when steps of the cited spines lead
from it up to the other, so that the other can head a higher phrase of its extended projection.
The order is adopted with `open scoped Minimalist.ExtendedProjection`. -/
@[instance_reducible]
protected def preorder : Preorder Cat where
  le := Relation.ReflTransGen (Spine.Step {s | s ∈ citedSpines})
  le_refl _ := .refl
  le_trans _ _ _ := .trans

namespace _root_.Minimalist.ExtendedProjection

scoped[Minimalist.ExtendedProjection] attribute [instance] Minimalist.Cat.preorder

end _root_.Minimalist.ExtendedProjection

open scoped ExtendedProjection

theorem le_iff_reflTransGen :
    c ≤ d ↔ Relation.ReflTransGen (Spine.Step {s | s ∈ citedSpines}) c d := Iff.rfl

/-- Whether one category is no higher than another is decided by searching along the steps of the
cited spines. The search is irreducible, so that elaboration never runs it; `decide +kernel`
does. -/
@[irreducible] protected def decidableLE : DecidableLE Cat :=
  Spine.decidableReflTransGenStep citedSpines

@[instance_reducible]
protected def decidableLT : DecidableLT Cat := @decidableLTOfDecidableLE _ _ Cat.decidableLE

namespace _root_.Minimalist.ExtendedProjection

scoped[Minimalist.ExtendedProjection] attribute [instance] Minimalist.Cat.decidableLE
  Minimalist.Cat.decidableLT

end _root_.Minimalist.ExtendedProjection

/-- The heads of a cited sequence ascend. -/
theorem isChain_le (hl : l ∈ citedSequences) : l.IsChain (· ≤ ·) :=
  Spine.isChain_reflTransGen_step (s := ⟨l⟩) (List.mem_append_left _ (List.mem_map_of_mem hl))

/-- Each head of a cited sequence is no higher than any head above it in the sequence. -/
theorem pairwise_le (hl : l ∈ citedSequences) : l.Pairwise (· ≤ ·) :=
  List.isChain_iff_pairwise.1 (isChain_le hl)

/-- Two categories that a source takes to be one head are level. -/
theorem antisymmRel_of_mem_citedIdentifications (h : (c, d) ∈ citedIdentifications) :
    AntisymmRel (· ≤ ·) c d :=
  ⟨List.isChain_pair.1 <| Spine.isChain_reflTransGen_step (s := ⟨[c, d]⟩) <|
      List.mem_append_right _ <| List.mem_flatMap.2 ⟨_, h, by simp⟩,
    List.isChain_pair.1 <| Spine.isChain_reflTransGen_step (s := ⟨[d, c]⟩) <|
      List.mem_append_right _ <| List.mem_flatMap.2 ⟨_, h, by simp⟩⟩

/-- A map under which the cited spines are chains for a reflexive and transitive relation sends a
category and one above it to related values. -/
theorem rel_of_le {β : Type*} {r : β → β → Prop} [Std.Refl r] [IsTrans β r] (f : Cat → β)
    (hf : ∀ s ∈ citedSpines, (s.map f).heads.IsChain r) (h : c ≤ d) : r (f c) (f d) :=
  Spine.forall_reflTransGen_step_iff.2 hf c d h

/-- The order of the categories is the least preorder in which the cited spines ascend: a map into
a preorder is monotone exactly when it never drops going up a cited spine. -/
theorem monotone_iff {β : Type*} [Preorder β] {f : Cat → β} :
    Monotone f ↔ ∀ s ∈ citedSpines, (s.map f).heads.IsChain (· ≤ ·) :=
  ⟨fun hf ↦ Spine.forall_reflTransGen_step_iff.1 fun _ _ h ↦ hf h,
    fun h _ _ hcd ↦ rel_of_le _ h hcd⟩

/-- A category is no higher than another exactly when every assignment of heights that never drops
going up a cited spine gives it a height no greater than the other's. -/
theorem le_iff_forall_le :
    c ≤ d ↔ ∀ f : Cat → ℕ, (∀ s ∈ citedSpines, (s.map f).heads.IsChain (· ≤ ·)) → f c ≤ f d :=
  Spine.reflTransGen_step_iff_forall_le

/-!
### Families

A cited sequence never leaves the family of its lexical head, so the order keeps the four families
apart, and each family has its lexical head at the foot.
-/

/-- A category is no higher than another only if the two are of one family. -/
theorem family_eq_of_le (h : c ≤ d) : c.family = d.family :=
  rel_of_le family (r := (· = ·)) (by decide +kernel) h

/-- The lexical head of a family is no higher than any category of the family. -/
theorem lexical_le (c : Cat) : c.family.lexical ≤ c := by
  cases c <;> decide +kernel

/-- A category has the lexical head of a family beneath it exactly when it is of that family. -/
theorem lexical_le_iff {f : CatFamily} : f.lexical ≤ c ↔ c.family = f :=
  ⟨fun h ↦ by simpa using (family_eq_of_le h).symm, fun h ↦ h ▸ lexical_le c⟩

/-!
### Where the sources agree and where they differ
-/

/-- Aspect, modality, mood, the evidential, negation and polarity are each level with tense. -/
theorem antisymmRel_T : ∀ c ∈ [Cat.Asp, .Mod, .Mood, .Evid, .Neg, .Pol],
    AntisymmRel (· ≤ ·) c .T := by
  decide +kernel

/-- Topic and focus are level, since Rizzi's topics stand on both sides of the focus. -/
theorem antisymmRel_Top_Foc : AntisymmRel (· ≤ ·) Cat.Top .Foc := by decide +kernel

/-- The verbal spine rises strictly from the verb through little v, Voice, tense, finiteness and
focus to Force, and the nominal spine from the noun through the dividing head, the counting head and
the determiner to the case shell. -/
theorem isChain_lt :
    [Cat.V, .v, .Voice, .T, .Fin, .Foc, .Force].IsChain (· < ·) ∧
      [Cat.N, .Q, .Num, .D, .K].IsChain (· < ·) := by
  decide +kernel

/-- Keine's nominalized clause and the CP are unrelated: no chain of cited steps leads from either
category up to the other. -/
theorem incompRel_Nmlz_C : IncompRel (· ≤ ·) Cat.Nmlz .C := by decide +kernel

end Cat

end Minimalist

namespace Cartography.Head

open Minimalist

open scoped Minimalist.ExtendedProjection

/-- Cinque's order is kept by the categories: when one of his heads is below another in his
hierarchy, its category is no higher than the category of the other. -/
theorem cat_mono : Monotone cat := fun x y h ↦ by
  have hp : hierarchy.Pairwise fun x y ↦ x.cat ≤ y.cat :=
    List.pairwise_map.1 (Cat.pairwise_le List.mem_cons_self)
  exact List.Pairwise.forall_of_forall_of_flip (R := fun x y ↦ x ≤ y → x.cat ≤ y.cat)
    (fun _ _ _ ↦ le_rfl) (hp.imp (S := fun x y : Head ↦ x ≤ y → x.cat ≤ y.cat) fun h _ ↦ h)
    (pairwise_hierarchy.imp fun hlt hle ↦ absurd hlt hle.not_gt) (mem_hierarchy x)
    (mem_hierarchy y) h

/-- The category of a head, as an order homomorphism from Cinque's hierarchy to the categories. -/
def catHom : Head →o Cat := ⟨cat, cat_mono⟩

@[simp] theorem coe_catHom : ⇑catHom = cat := rfl

end Cartography.Head

namespace Spine

open Minimalist

open scoped Minimalist.ExtendedProjection

variable {s : Spine Cat} {l : List Cat}

/-!
### Extended projections of the categories

A spine of categories is an extended projection, in the sense of
`Linglib/Syntax/Spine/ExtendedProjection.lean`, for the families of the categories and their order.
A determiner over a clause is of two families, whatever order the categories are given. In the
order of the cited structures a spine that ascends is already of one family, since no cited
sequence leaves the family of its lexical head.
-/

/-- For the order of the cited structures, a spine of categories that ascends is an extended
projection: its heads are then of one family. -/
theorem isExtendedProjection_family_iff_isChain :
    s.IsExtendedProjection Cat.family (· ≤ ·) ↔ s.heads.IsChain (· ≤ ·) :=
  isExtendedProjection_iff_isChain fun _ _ ↦ Cat.family_eq_of_le

/-- The spine of a cited structure is an extended projection. -/
theorem isExtendedProjection_of_mem_citedSequences (hl : l ∈ citedSequences) :
    IsExtendedProjection Cat.family (· ≤ ·) ⟨l⟩ :=
  isExtendedProjection_family_iff_isChain.2 (Cat.isChain_le hl)

end Spine
