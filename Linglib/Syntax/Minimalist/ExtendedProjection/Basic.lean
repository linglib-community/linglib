/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Syntax.Cartography
public import Linglib.Syntax.Minimalist.Category
public import Linglib.Syntax.Spine.Label
public import Mathlib.Order.Comparable

/-!
# Extended projections

A clause is built on a verb, but most of its structure is not the verb's: tense, negation and the
complementizer each head a phrase of their own above it. Grimshaw takes these phrases to form one
**extended projection**, a lexical head together with the functional heads above it, all of the
category of the lexical head, each at a functional level no lower than the one beneath it. A noun
phrase is built the same way, with number and the determiner above the noun.

Which functional head stands above which? The heads are not numbered here. Their order is read off
the structures that the literature draws. Each cited structure gives a spine, its heads from the
bottom up, such as the verb, little v, Voice and tense. A head is one **step** above another when
some cited spine places it directly above the other, or when a source takes the two to be one
head, and a category is **at most** another, written `c ≤ d`, when a chain of steps leads from the
first up to the second. Every cited spine ascends in this order, and the order holds between two
categories only where the cited structures force it to: a map on categories is monotone as soon as
it never drops going up a cited spine. So assign each category a height, in any way that never
drops going up a cited spine. One category is at most another exactly when every such assignment
places it no higher.

A spine of categories is then an extended projection when it ascends in this order. All its heads
are of one family, since no cited spine leaves the family of its lexical head, and the lexical
head of a family is below every category of the family and below nothing else.

Since the order pools the structures of many sources, it shows where they disagree. Two heads that
one source orders one way and another source the other way come out **level**, each at most the
other. Cinque interleaves the tenses, moods, modalities and aspects, Zanuttini finds negation on
both sides of tense, and Laka places polarity below tense in English and above it in Basque. All of
these heads are therefore level with tense, and no assignment of heights that respects every source
tells them apart. Rizzi's topics stand on both sides of the focus, so topic and focus are level too.
Where the sources agree the order is strict: the verb, little v, Voice, tense, finiteness, focus and
Force rise in that order, and so do the noun, the dividing head, the counting head, the determiner
and the case shell. Where no source relates two heads they are incomparable, as Keine's nominalized
clause and the CP are: neither contains the other.

## Implementation notes

`Minimalist.citedSequences` and `Minimalist.citedIdentifications` hold the cited structures, and
`Minimalist.citedSteps` lists their steps as pairs, which is what the decision procedure runs on.
The order is the reflexive-transitive closure of `Minimalist.Cat.Step`. It is an order instance,
so that a strict step is `<`, two level heads are related by `AntisymmRel (· ≤ ·)`, two unrelated
ones by `IncompRel (· ≤ ·)`, and a map that respects the order is `Monotone`. The instance is
scoped: the categories themselves carry no order, and a file that orders them adopts this one with
`open scoped Minimalist.ExtendedProjection`. An account in which heads are ordered by selection
alone uses the categories without it.

That every cited spine ascends is `Minimalist.Cat.isChain_le`, that the order is the least such is
`Minimalist.Cat.monotone_iff`, and the statement about heights is
`Minimalist.Cat.le_iff_forall_le`. `Cartography.Head.catHom` sends Cinque's order into it.

Citing a further structure can only add to the order. A statement that one category is at most
another therefore survives every later citation, while a statement that two categories are strictly
ordered or incomparable holds of the structures cited so far.

A structure is transcribed as follows. A root, a VP or NP and the verb or noun are the lexical head,
an IP is `T`, Cinque's heads are read through `Cartography.Head.cat`, and the heads of a structure
that are not categories here (Agr, Cause, Deg, Laka's English AP) are left out, its other heads kept
in order. A spine stops where a head takes a complement of another family, as where Thoms and
colleagues' little v takes a noun phrase or Arregi and Pietraszko's determiner takes a clause, and
a modifier of another family, such as the adjective of Cinque's noun phrase, is left out. Cinque's
demonstrative and numeral are specifiers, taken as heads as his footnote allows; Zanuttini's
numbered negations are all `Neg`; Laka's Σ is `Pol`. Keine leaves open whether his nominalizer
belongs to the extended projection of the clause it selects, and it is taken to. Only the high
applicative is cited: Pylkkänen's low applicative sits below the verb, and with one `Appl` category
citing both would make the verb, v and the applicative one level.

`Cartography.Head.cat` sends Cinque's four aspect heads below Voice to inner aspect, the aspect of
the v shell, the other aspect heads to outer aspect, the speech-act mood to the speech-act head,
as Speas and Tenny project their speech-act phrase from Cinque's speech-act mood head, and the
other moods but the evidential to `Cat.Mood`.

The unsplit complementizer is identified with Force, the position of Rizzi's finite *che*. His
nonfinite *di* is in the finiteness position, so an infinitival complementizer is `Fin`.

## TODO

Inner aspect is placed by Liu and Yip's clause sizes, which follow Travis; Travis's own
structure, Kratzer's Voice, Svenonius's adpositional heads and Grimshaw's definitions are not
yet read from the sources. No cited structure relates little n to the dividing head or D to the
demonstrative, so those pairs are incomparable.

## References

* [grimshaw-2005]
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

/-- The **cited steps** are the pairs of a head and the next head up in a cited sequence, together
with each cited identification in both directions. -/
def citedSteps : List (Cat × Cat) :=
  citedSequences.flatMap (fun l ↦ l.zip l.tail) ++ citedIdentifications.flatMap fun p ↦ [p, p.swap]

namespace Cat

variable {c d : Cat} {l : List Cat}

/-!
### The order of the categories

One category is **at most** another when cited steps lead from the first up to the second. Two
categories are **level** when each is at most the other.
-/

/-- A category is one **step** below another when a source merges the other directly above it or
takes the two to be one head. -/
def Step (c d : Cat) : Prop := (c, d) ∈ citedSteps

instance : DecidableRel Step := fun c d ↦ inferInstanceAs (Decidable ((c, d) ∈ citedSteps))

/-- A category is **at most** another, written `c ≤ d`, when a chain of cited steps leads from it
up to the other, so that the other can head a higher phrase of its extended projection. The order
is adopted with `open scoped Minimalist.ExtendedProjection`. -/
@[instance_reducible]
protected def preorder : Preorder Cat where
  le := Relation.ReflTransGen Step
  le_refl _ := .refl
  le_trans _ _ _ := .trans

namespace _root_.Minimalist.ExtendedProjection

scoped[Minimalist.ExtendedProjection] attribute [instance] Minimalist.Cat.preorder

end _root_.Minimalist.ExtendedProjection

open scoped ExtendedProjection

theorem le_iff_reflTransGen : c ≤ d ↔ Relation.ReflTransGen Step c d := Iff.rfl

/-- Whether one category is at most another is decided by searching along the cited steps. The
search is irreducible, so that elaboration never runs it; `decide +kernel` does. -/
@[irreducible] protected def decidableLE : DecidableLE Cat := fun c d ↦
  Relation.ReflTransGen.decidable_of_finite_step
    (fun x ↦ (citedSteps.filter (·.1 == x)).map (·.2)) (citedSteps.map (·.2))
    (fun x y ↦ by simp [Step]) (fun _ _ h ↦ by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      exact List.mem_map_of_mem (List.mem_filter.1 hp).1) c d

@[instance_reducible]
protected def decidableLT : DecidableLT Cat := @decidableLTOfDecidableLE _ _ Cat.decidableLE

namespace _root_.Minimalist.ExtendedProjection

scoped[Minimalist.ExtendedProjection] attribute [instance] Minimalist.Cat.decidableLE
  Minimalist.Cat.decidableLT

end _root_.Minimalist.ExtendedProjection

theorem Step.le (h : c.Step d) : c ≤ d := Relation.ReflTransGen.single h

private theorem isChain_iff_forall_mem_zip_tail {α : Type*} {r : α → α → Prop} :
    ∀ {l : List α}, l.IsChain r ↔ ∀ x y, (x, y) ∈ l.zip l.tail → r x y
  | [] => by simp
  | [_] => by simp
  | x :: y :: l => by
    rw [List.isChain_cons_cons, isChain_iff_forall_mem_zip_tail (l := y :: l)]
    simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq]
    exact ⟨fun h _ _ hxy ↦ hxy.elim (fun e ↦ e.1 ▸ e.2 ▸ h.1) (h.2 _ _),
      fun h ↦ ⟨h _ _ (.inl ⟨rfl, rfl⟩), fun _ _ hxy ↦ h _ _ (.inr hxy)⟩⟩

/-- The heads of a cited sequence ascend. -/
theorem isChain_le (hl : l ∈ citedSequences) : l.IsChain (· ≤ ·) :=
  isChain_iff_forall_mem_zip_tail.2 fun _ _ h ↦ Step.le <|
    List.mem_append_left _ <| List.mem_flatMap.2 ⟨l, hl, h⟩

/-- Each head of a cited sequence is at most every head above it in the sequence. -/
theorem pairwise_le (hl : l ∈ citedSequences) : l.Pairwise (· ≤ ·) :=
  List.isChain_iff_pairwise.1 (isChain_le hl)

/-- Two categories that a source takes to be one head are level. -/
theorem antisymmRel_of_mem_citedIdentifications (h : (c, d) ∈ citedIdentifications) :
    AntisymmRel (· ≤ ·) c d :=
  ⟨Step.le <| List.mem_append_right _ <| List.mem_flatMap.2 ⟨_, h, by simp⟩,
    Step.le <| List.mem_append_right _ <| List.mem_flatMap.2 ⟨_, h, by simp⟩⟩

/-- A map under which the cited sequences ascend and the identified heads are level, for a
reflexive and transitive relation, sends a category and one above it to related values. -/
theorem rel_of_le {β : Type*} {r : β → β → Prop} [Std.Refl r] [IsTrans β r] (f : Cat → β)
    (hseq : ∀ l ∈ citedSequences, (l.map f).IsChain r)
    (hid : ∀ x y, (x, y) ∈ citedIdentifications → AntisymmRel r (f x) (f y))
    (h : c ≤ d) : r (f c) (f d) := by
  replace h := le_iff_reflTransGen.1 h
  induction h with
  | refl => exact refl _
  | tail _ hs ih =>
    refine _root_.trans ih ?_
    obtain hs | hs := List.mem_append.1 hs
    · obtain ⟨l, hl, hp⟩ := List.mem_flatMap.1 hs
      exact isChain_iff_forall_mem_zip_tail.1 ((List.isChain_map f).1 (hseq l hl)) _ _ hp
    · obtain ⟨⟨x, y⟩, hp, hm⟩ := List.mem_flatMap.1 hs
      obtain h | h : (_, _) = (x, y) ∨ (_, _) = (y, x) := by simpa using hm
      · exact (Prod.mk.inj h).1 ▸ (Prod.mk.inj h).2 ▸ (hid x y hp).1
      · exact (Prod.mk.inj h).1 ▸ (Prod.mk.inj h).2 ▸ (hid x y hp).2

/-- The order of the categories is the least preorder in which the cited sequences ascend and the
identified heads are level: a map into a preorder is monotone exactly when it never drops going up
a cited sequence and sends identified heads to level values. -/
theorem monotone_iff {β : Type*} [Preorder β] {f : Cat → β} :
    Monotone f ↔ (∀ l ∈ citedSequences, (l.map f).IsChain (· ≤ ·)) ∧
      ∀ x y, (x, y) ∈ citedIdentifications → AntisymmRel (· ≤ ·) (f x) (f y) :=
  ⟨fun hf ↦ ⟨fun _ hl ↦ (List.isChain_map f).2 ((isChain_le hl).imp fun _ _ h ↦ hf h), fun _ _ h ↦
      (antisymmRel_of_mem_citedIdentifications h).imp (hf ·) (hf ·)⟩,
    fun h _ _ hcd ↦ rel_of_le f h.1 h.2 hcd⟩

/-- A category is at most another exactly when every assignment of heights that never drops going
up a cited sequence, and gives identified heads one height, places it no higher than the other. -/
theorem le_iff_forall_le :
    c ≤ d ↔ ∀ f : Cat → ℕ, (∀ l ∈ citedSequences, (l.map f).IsChain (· ≤ ·)) →
      (∀ x y, (x, y) ∈ citedIdentifications → f x = f y) → f c ≤ f d := by
  refine ⟨fun h f hseq hid ↦ monotone_iff.2 ⟨hseq, fun x y hxy ↦ (hid x y hxy).antisymmRel⟩ h,
    fun h ↦ ?_⟩
  have hc := h (fun x ↦ if c ≤ x then 1 else 0)
    (fun l hl ↦ (List.isChain_map _).2 <| (isChain_le hl).imp fun {x y} hxy ↦ by
      by_cases hx : c ≤ x
      · simp [hx, hx.trans hxy]
      · simp [hx])
    (fun x y hxy ↦ by
      have hl := antisymmRel_of_mem_citedIdentifications hxy
      simp only [show c ≤ x ↔ c ≤ y from ⟨(·.trans hl.1), (·.trans hl.2)⟩])
  by_contra hcd
  simp [hcd] at hc

/-!
### Families

A cited sequence never leaves the family of its lexical head, so the order keeps the four families
apart, and each family has its lexical head at the foot.
-/

/-- A category is at most only categories of its own family. -/
theorem family_eq_of_le (h : c ≤ d) : c.family = d.family :=
  rel_of_le family (r := (· = ·)) (by decide +kernel) (fun x y hxy ↦
    ((by decide : ∀ p ∈ citedIdentifications, p.1.family = p.2.family) (x, y) hxy).antisymmRel) h

/-- The lexical head of a family is at most every category of the family. -/
theorem lexical_le (c : Cat) : c.family.lexical ≤ c := by
  cases c <;> decide +kernel

/-- The lexical head of a family is below the categories of that family and below no others. -/
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

/-- Keine's nominalized clause and the CP are incomparable: neither category is at most the
other. -/
theorem incompRel_Nmlz_C : IncompRel (· ≤ ·) Cat.Nmlz .C := by decide +kernel

end Cat

end Minimalist

namespace Cartography.Head

open Minimalist

open scoped Minimalist.ExtendedProjection

/-- Cinque's order is kept by the categories: when one of his heads is below another, its category
is at most the category of the other. -/
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

variable {s : Spine Cat} {c d : Cat} {l : List Cat}

/-!
### Extended projections

A spine of categories is an **extended projection** when it ascends: each of its heads is at most
the next one up.
-/

/-- A spine of categories is an **extended projection** when each of its heads is at most the next
head up. -/
def IsExtendedProjection (s : Spine Cat) : Prop := s.heads.IsChain (· ≤ ·)

instance (s : Spine Cat) : Decidable s.IsExtendedProjection :=
  inferInstanceAs (Decidable (List.IsChain _ _))

/-- The spine of a cited structure is an extended projection. -/
theorem isExtendedProjection_of_mem_citedSequences (hl : l ∈ citedSequences) :
    IsExtendedProjection ⟨l⟩ :=
  Cat.isChain_le hl

/-- In an extended projection every head is at most each head above it. -/
theorem IsExtendedProjection.pairwise (h : s.IsExtendedProjection) : s.heads.Pairwise (· ≤ ·) :=
  List.isChain_iff_pairwise.1 h

/-- The heads of an extended projection are of one family. -/
theorem IsExtendedProjection.family_eq (hs : s.IsExtendedProjection) (hc : c ∈ s) (hd : d ∈ s) :
    c.family = d.family :=
  List.Pairwise.forall_of_forall_of_flip (R := fun x y : Cat ↦ x.family = y.family)
    (fun _ _ ↦ rfl) (hs.pairwise.imp Cat.family_eq_of_le)
    (hs.pairwise.imp fun h ↦ (Cat.family_eq_of_le h).symm) hc hd

/-- In an extended projection a head lies in the complement of another or is at least it. -/
theorem IsExtendedProjection.mem_below_or_le (hs : s.IsExtendedProjection) (hc : c ∈ s)
    (hd : d ∈ s) : d ∈ s.below c ∨ c ≤ d :=
  mem_below_or_rel hs.pairwise hc hd

/-- In an extended projection the heads in the complement of a head are at most it. -/
theorem IsExtendedProjection.le_of_mem_below (hs : s.IsExtendedProjection) (hc : c ∈ s)
    (hd : d ∈ s.below c) : d ≤ c :=
  rel_of_mem_below hs.pairwise hc hd

end Spine
