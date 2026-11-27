/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Cartography
public import Linglib.Syntax.Minimalist.Category
public import Linglib.Syntax.Spine.Basic

/-!
# The cited structures

This file lists the structures of functional heads that the cited sources draw. Each structure
gives one or more spines of categories, listed from the bottom up. A source that takes two
categories to be one head gives the two-head spine in both orders.

## Main definitions

* `Minimalist.CitedStructure`: the cited structures.
* `Minimalist.CitedStructure.spines`: the spines of a cited structure.
* `Minimalist.citedSpines`: the spines of all cited structures.
* `Cartography.Head.cat`: the category of a head of Cinque's hierarchy.

## Implementation notes

A structure is transcribed as follows. A root, a VP or NP and the verb or noun are the lexical head,
an IP is `T`, Cinque's heads are read through `Cartography.Head.cat`, and the heads of a structure
that are not categories here (Agr, Cause, Deg, Laka's English AP) are left out, its other heads kept
in order. A spine stops where a head takes a complement of another family, as where Thoms and
colleagues' little v takes a noun phrase or Arregi and Pietraszko's determiner takes a clause, and
a modifier of another family, such as the adjective of Cinque's noun phrase, is left out. For
Grimshaw only a lexical head takes a complement with which it forms no extended projection; in
these two structures the head that does so is not the lexical one.

Cinque's demonstrative and numeral are specifiers, taken as heads as his footnote allows.
Zanuttini's numbered negations are all `Neg`, and Laka's Σ is `Pol`. Keine leaves open whether his
nominalizer belongs to the extended projection of the clause it selects, and it is taken to. Only
the high applicative is cited: Pylkkänen's low applicative is below the verb, and with one `Appl`
category citing both would relate the verb, v and the applicative in both directions.

`Cartography.Head.cat` sends Cinque's four aspect heads below Voice to inner aspect, his other
aspect heads to outer aspect, his speech-act mood to the speech-act head, as Speas and Tenny
project their speech-act phrase from it, and his other moods except the evidential to `Cat.Mood`.

The unsplit complementizer is identified with Force, the position of Rizzi's finite *che*. His
nonfinite *di* is in the finiteness position, so an infinitival complementizer is `Fin`.

## TODO

Inner aspect is placed by Liu and Yip's clause sizes, which follow Travis. Travis's own structure,
Kratzer's Voice and Svenonius's adpositional heads are not yet read from the sources.

## References

* [cinque-1999]
* [panagiotidis-2015]
* [harley-2013]
* [pylkkanen-2008]
* [harley-2017]
* [liu-yip-2026]
* [pollock-1989]
* [zanuttini-1997]
* [laka-1990]
* [keine-2020]
* [elkins-torrence-brown-2026]
* [rizzi-1997]
* [egressy-2026]
* [speas-tenny-2003]
* [borer-2005]
* [cinque-2005]
* [thoms-etal-2026]
* [newman-2024]
* [arregi-pietraszko-2021]
* [dendikken-2010]
* [grimshaw-2000]
-/

@[expose] public section

namespace Cartography.Head

/-- The **category** of a head of Cinque's hierarchy is the category that the head is an instance
of. -/
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

/-- A **cited structure** is a structure of functional heads that a source draws, or an
identification of two categories that a source makes. -/
inductive CitedStructure
  /-- [cinque-1999] orders the clausal functional heads in one hierarchy. -/
  | cinque1999
  /-- [panagiotidis-2015] draws a categorizer above a root ((11), p. 18). -/
  | panagiotidis2015
  /-- [harley-2013] draws tense above Voice above little v above the root ((2), p. 35). -/
  | harley2013
  /-- [pylkkanen-2008] draws Voice above the high applicative above the verb ((6a), p. 14). -/
  | pylkkanen2008
  /-- [harley-2017] draws Voice above the applicative above little v above the root ((18),
  p. 13). -/
  | harley2017
  /-- [liu-yip-2026] draw the finite clause with outer aspect above little v and inner aspect below
  it ((1a), p. 3). -/
  | liuYip2026
  /-- [pollock-1989] draws the complementizer above tense above negation above the verb ((77),
  p. 397). -/
  | pollock1989
  /-- [zanuttini-1997] draws the clause with preverbal negation between tense and mood ((106),
  p. 141). -/
  | zanuttini1997Preverbal
  /-- [zanuttini-1997] draws the postverbal negations above and below tense and aspect ((139),
  p. 99). -/
  | zanuttini1997Postverbal
  /-- [laka-1990] draws Σ below inflection in English and above it in Basque ((16), p. 101). -/
  | laka1990Sigma
  /-- [laka-1990] draws Σ above inflection and below the complementizer in Spanish ((46)–(47),
  p. 127). -/
  | laka1990Spanish
  /-- [keine-2020] draws the gerund as a nominalizer above tense above little v ((106), p. 74). -/
  | keine2020Gerund
  /-- [keine-2020] draws the finite clause that embeds a gerund ((238), p. 156). -/
  | keine2020Finite
  /-- [elkins-torrence-brown-2026] draw the directional above Voice in the Mam clause ((8),
  p. 6). -/
  | elkinsTorrenceBrown2026
  /-- [rizzi-1997] draws the complementizer system as Force, a topic, the focus, a topic and
  finiteness above the IP ((41), p. 297). -/
  | rizzi1997
  /-- [rizzi-1997] takes the finite complementizer *che* to be in the force position (p. 288). -/
  | rizzi1997Che
  /-- [egressy-2026] orders the say layer above focus above tense (p. 13). -/
  | egressy2026
  /-- [speas-tenny-2003] place the evaluative projection just below the speech-act phrase
  (p. 332). -/
  | speasTenny2003
  /-- [speas-tenny-2003] take the speech-act phrase to be the projection that encodes
  illocutionary force (p. 317). -/
  | speasTenny2003Force
  /-- [borer-2005] draws the determiner above the counting head above the dividing head above the
  noun ((8a), p. 96). -/
  | borer2005
  /-- [cinque-2005] orders the demonstrative above the numeral above the noun ((7a), p. 321). -/
  | cinque2005
  /-- [thoms-etal-2026] draw number above the possessive head above little n ((38), p. 22). -/
  | thomsEtAl2026
  /-- [newman-2024] draws the case shell above the determiner above the noun ((217), p. 129). -/
  | newman2024
  /-- [arregi-pietraszko-2021] draw the linker above the determiner ((14), p. 250). -/
  | arregiPietraszko2021
  /-- [dendikken-2010] draws Path above Place above the adposition ((20c), p. 81). -/
  | dendikken2010
  deriving DecidableEq, Repr

namespace CitedStructure

/-- The **spines** of a cited structure are its sequences of heads, each from the bottom up. An
identification of two categories has the two-head spine in both orders. -/
def spines : CitedStructure → List (Spine Cat)
  | cinque1999 => [⟨Cartography.Head.hierarchy.map Cartography.Head.cat⟩]
  | panagiotidis2015 => [⟨[.V, .v]⟩, ⟨[.N, .n]⟩, ⟨[.A, .a]⟩]
  | harley2013 => [⟨[.V, .v, .Voice, .T]⟩]
  | pylkkanen2008 => [⟨[.V, .Appl, .Voice]⟩]
  | harley2017 => [⟨[.V, .v, .Appl, .Voice]⟩]
  | liuYip2026 => [⟨[.V, .InnerAsp, .v, .Asp, .T, .C]⟩]
  | pollock1989 => [⟨[.V, .Neg, .T, .C]⟩]
  | zanuttini1997Preverbal => [⟨[.Mod, .Mood, .Neg, .T, .Mod, .Mod]⟩]
  | zanuttini1997Postverbal => [⟨[.Neg, .Asp, .Asp, .Neg, .T, .Neg]⟩]
  | laka1990Sigma => [⟨[.V, .Pol, .T]⟩, ⟨[.V, .T, .Pol]⟩]
  | laka1990Spanish => [⟨[.T, .Pol, .C]⟩]
  | keine2020Gerund => [⟨[.v, .T, .Nmlz]⟩]
  | keine2020Finite => [⟨[.V, .v, .T, .C]⟩]
  | elkinsTorrenceBrown2026 => [⟨[.V, .v, .Voice, .Dir, .C]⟩]
  | rizzi1997 => [⟨[.T, .Fin, .Top, .Foc, .Top, .Force]⟩]
  | rizzi1997Che => [⟨[.C, .Force]⟩, ⟨[.Force, .C]⟩]
  | egressy2026 => [⟨[.T, .Foc, .Say]⟩]
  | speasTenny2003 => [⟨[.Mood, .SA]⟩]
  | speasTenny2003Force => [⟨[.SA, .Force]⟩, ⟨[.Force, .SA]⟩]
  | borer2005 => [⟨[.N, .Q, .Num, .D]⟩]
  | cinque2005 => [⟨[.N, .Num, .Dem]⟩]
  | thomsEtAl2026 => [⟨[.n, .Poss, .Num]⟩]
  | newman2024 => [⟨[.N, .D, .K]⟩]
  | arregiPietraszko2021 => [⟨[.D, .Lnk]⟩]
  | dendikken2010 => [⟨[.P, .Place, .Path]⟩]

/-- The list `CitedStructure.all` contains every cited structure. -/
def all : List CitedStructure := (List.range 25).map CitedStructure.ofNat

theorem mem_all (x : CitedStructure) : x ∈ all := by cases x <;> decide

end CitedStructure

/-- The **cited spines** are the spines of all cited structures. -/
def citedSpines : List (Spine Cat) := CitedStructure.all.flatMap CitedStructure.spines

theorem mem_citedSpines {x : CitedStructure} {s : Spine Cat} (hs : s ∈ x.spines) :
    s ∈ citedSpines :=
  List.mem_flatMap.2 ⟨x, x.mem_all, hs⟩

end Minimalist
