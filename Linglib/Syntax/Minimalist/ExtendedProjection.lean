module

public import Linglib.Core.Order.Antisymmetrization
public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Syntax.Cartography
public import Linglib.Syntax.Minimalist.Category
public import Mathlib.Order.RelClasses

/-!
# Extended projections

Grimshaw takes a clause or a noun phrase to be one extended projection: a lexical head together
with the functional heads above it, all sharing the categorial features of the lexical head, each
at a functional level no lower than the one below it. The order of the levels is read off here
from the structures the sources draw rather than assigned head by head. Each cited structure is a
sequence of heads, bottom-up, and a source may also take two categories to be one head; a category
extends to another when a chain of cited steps leads from the first to the second. Every cited step
stays within one family, so [a category extends only to categories of its
family](##Minimalist.Cat.ExtendsTo.family_eq), and every category is reached from the lexical head
of its family, so [it extends that head](##Minimalist.Cat.lexical_extendsTo).

Since the order collects the structures of several sources, a category one source places above
another and another source below it comes out level with it. Cinque interleaves tense, mood,
modality and aspect, Zanuttini places negation on both sides of tense and Laka places polarity
below tense in English and above it in Basque, so [these heads are mutually
level](##Minimalist.Cat.antisymmRel_T); Rizzi's topics recur on both sides of the focus, so [topic
and focus are level](##Minimalist.Cat.antisymmRel_Top_Foc). Where the sources agree the order is
strict, as along the verbal spine from the verb to Force and the nominal spine from the noun to K,
and where no source relates two heads they are incomparable: Keine's nominalized clause [neither
contains nor is contained in a CP](##Minimalist.Cat.not_extendsTo_Nmlz_C). The heads of any one
cited sequence extend one another in its order (`Minimalist.Cat.pairwise_extendsTo`), and that
stays true as further sequences are cited, so a claim about the heads a source draws is stated
over that sequence.

## Main definitions

* `Cartography.Head.cat`: the category of a head of Cinque's hierarchy.
* `Minimalist.citedSequences`, `Minimalist.citedIdentifications`: the structures the sources draw.
* `Minimalist.Cat.Step`: a cited step, from a head to the one a source merges directly above it.
* `Minimalist.Cat.ExtendsTo`: the extension order, the reflexive-transitive closure of the steps.

## Implementation notes

`Cartography.Head.cat` sends Cinque's four aspect heads below Voice to inner aspect, the aspect of
the v shell, the other aspect heads to outer aspect, the speech-act mood to the speech-act head,
as Speas and Tenny project their speech-act phrase from Cinque's speech-act mood head, and the
other moods but the evidential to `Cat.Mood`.

A root, a VP and the verb of a cited structure are its lexical head, an IP is `T`, Cinque's heads
are read through `Cartography.Head.cat`, and the heads of a structure that are not categories here
(Agr, Cause, Deg, Laka's English AP) are left out, its other heads kept in order. Cinque's
demonstrative and numeral are specifiers, taken as heads as his footnote allows; Zanuttini's
numbered negations are all `Neg`; Laka's Σ is `Pol`. Only the high applicative is cited:
Pylkkänen's low applicative sits below the verb, and with one `Appl` category citing both would
make the verb, v and the applicative one level.

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

/-- The category of a head among the categorial features. -/
def cat : Head → Minimalist.Cat
  | voice => .Voice
  | aspSgCompletiveII | aspFrequentativeII | aspRepetitiveII | aspCelerativeII => .InnerAsp
  | tAnterior | tFuture | tPast => .T
  | modVolitional | modPossibility | modNecessity | modEpistemic => .Mod
  | moodEvidential => .Evid
  | moodSpeechAct => .SA
  | moodIrrealis | moodEvaluative => .Mood
  | _ => .Asp

theorem family_cat (h : Head) : h.cat.family = .verbal := by
  cases h <;> rfl

end Cartography.Head

namespace Minimalist

/-! ### The cited structures -/

/-- The sequences of heads the sources draw, each bottom-up. -/
def citedSequences : List (List Cat) :=
  [[.V, .v], [.N, .n], [.A, .a],                  -- [panagiotidis-2015] (11), p. 18
    [.V, .v, .Voice, .T],                         -- [harley-2013] (2), p. 35
    [.V, .Appl, .Voice],                          -- [pylkkanen-2008] (6a), pp. 13–14
    [.v, .Appl, .Voice],                          -- [harley-2017] (18), p. 13
    [.V, .InnerAsp, .v, .Asp, .T, .C],            -- [liu-yip-2026] (1a), p. 25
    [.V, .Neg, .T, .C],                           -- [pollock-1989] (77), p. 397
    [.Mod, .Mood, .Neg, .T, .Mod, .Mod],          -- [zanuttini-1997] (106), p. 141
    [.Neg, .Asp, .Asp, .Neg, .T, .Neg],           -- [zanuttini-1997] (139), p. 99
    [.V, .Pol, .T], [.V, .T, .Pol],               -- [laka-1990] (16), p. 101
    [.T, .Pol, .C],                               -- [laka-1990] (46)–(47), p. 127
    [.v, .T, .Nmlz],                              -- [keine-2020] (106), p. 74
    [.v, .T, .C],                                 -- [keine-2020] (238), p. 156
    [.V, .v, .Voice, .Dir, .C],                   -- [elkins-torrence-brown-2026] (8), p. 6
    [.T, .Fin, .Top, .Foc, .Top, .Force],         -- [rizzi-1997] (41), p. 297
    [.T, .Foc, .Say],                             -- [egressy-2026] p. 14
    [.Mood, .SA],                                 -- [speas-tenny-2003] p. 332
    [.N, .Q, .Num, .D],                           -- [borer-2005] (8a), p. 96
    [.N, .Num, .Dem],                             -- [cinque-2005] (7a), p. 321
    [.n, .Poss, .Num],                            -- [thoms-etal-2026] (38), p. 22
    [.D, .K],                                     -- [newman-2024] (217), p. 129
    [.D, .Lnk],                                   -- [arregi-pietraszko-2021] (14), p. 250
    [.P, .Place, .Path]]                          -- [dendikken-2010] (20c), p. 81

/-- The pairs of categories a source takes to be one head: Rizzi's *che* manifests the force
position, and Speas and Tenny's speech-act phrase is the projection that encodes force. -/
def citedIdentifications : List (Cat × Cat) :=
  [(.C, .Force),                                  -- [rizzi-1997] p. 288
    (.SA, .Force)]                                -- [speas-tenny-2003] p. 317

/-- The cited steps: each head of Cinque's hierarchy or of a cited sequence to the next one up,
and each cited identification in both directions. -/
def citedSteps : List (Cat × Cat) :=
  ((Cartography.Head.hierarchy.map Cartography.Head.cat) :: citedSequences).flatMap
      (fun l ↦ l.zip l.tail) ++
    citedIdentifications.flatMap fun p ↦ [p, p.swap]

namespace Cat

variable {c d : Cat}

/-- `c.Step d` holds when a source merges `d` directly above `c` or takes the two to be one
head. -/
def Step (c d : Cat) : Prop := (c, d) ∈ citedSteps

instance : DecidableRel Step := fun c d ↦ inferInstanceAs (Decidable ((c, d) ∈ citedSteps))

/-- `c.ExtendsTo d` holds when a chain of cited steps leads from `c` to `d`, so that `d` can
extend the projection of `c`. -/
def ExtendsTo : Cat → Cat → Prop := Relation.ReflTransGen Step

/-- Reachability along the cited steps, irreducible so that elaboration never computes the
closure; `decide +kernel` evaluates it. -/
@[irreducible] def decidableExtendsTo : DecidableRel ExtendsTo := fun c d ↦
  Relation.ReflTransGen.decidable_of_finite_step
    (fun x ↦ (citedSteps.filter (·.1 == x)).map (·.2)) (citedSteps.map (·.2))
    (fun x y ↦ by simp [Step]) (fun _ _ h ↦ by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      exact List.mem_map_of_mem (List.mem_filter.1 hp).1) c d

instance : DecidableRel ExtendsTo := decidableExtendsTo

instance : IsPreorder Cat ExtendsTo where
  refl _ := .refl
  trans _ _ _ := .trans

theorem Step.extendsTo (h : c.Step d) : c.ExtendsTo d := .single h

theorem Step.family_eq (h : c.Step d) : c.family = d.family :=
  (by decide +kernel : ∀ p ∈ citedSteps, p.1.family = p.2.family) _ h

private theorem isChain_of_forall_mem_zip_tail {r : Cat → Cat → Prop} :
    ∀ {l : List Cat}, (∀ p ∈ l.zip l.tail, r p.1 p.2) → l.IsChain r
  | [], _ => .nil
  | [_], _ => .singleton _
  | x :: y :: _, h =>
    List.isChain_cons_cons.2 ⟨h (x, y) List.mem_cons_self,
      isChain_of_forall_mem_zip_tail fun p hp ↦ h p (List.mem_cons_of_mem _ hp)⟩

/-- The heads of a cited sequence extend one another in its order: a source's own hierarchy
embeds in the order that collects them all. -/
theorem pairwise_extendsTo {l : List Cat} (hl : l ∈ citedSequences) : l.Pairwise ExtendsTo :=
  List.isChain_iff_pairwise.1 <| isChain_of_forall_mem_zip_tail fun p hp ↦
    Step.extendsTo (c := p.1) (d := p.2) <| List.mem_append_left _ <|
      List.mem_flatMap.2 ⟨l, List.mem_cons_of_mem _ hl, hp⟩

/-- Two heads of one cited sequence are comparable, whatever other sequences are cited. -/
theorem extendsTo_or_extendsTo {l : List Cat} (hl : l ∈ citedSequences) (hc : c ∈ l)
    (hd : d ∈ l) : c.ExtendsTo d ∨ d.ExtendsTo c :=
  have h := pairwise_extendsTo hl
  List.Pairwise.forall_of_forall_of_flip (R := fun x y ↦ x.ExtendsTo y ∨ y.ExtendsTo x)
    (fun _ _ ↦ .inl .refl) (h.imp Or.inl) (h.imp Or.inr) hc hd

/-- A category extends only to categories of its family. -/
theorem ExtendsTo.family_eq (h : c.ExtendsTo d) : c.family = d.family := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans hs.family_eq

/-- Every category extends the lexical head of its family. -/
theorem lexical_extendsTo (c : Cat) : c.family.lexical.ExtendsTo c := by
  cases c <;> decide +kernel

/-- Tense, aspect, modality, mood, the evidential, negation and polarity are mutually level. -/
theorem antisymmRel_T : ∀ c ∈ [Cat.Asp, .Mod, .Mood, .Evid, .Neg, .Pol],
    AntisymmRel ExtendsTo c .T := by
  decide +kernel

/-- Topic and focus are level, since Rizzi's topics recur on both sides of the focus. -/
theorem antisymmRel_Top_Foc : AntisymmRel ExtendsTo .Top .Foc := by decide +kernel

/-- The complementizer, Force and the speech-act head are one level. -/
theorem antisymmRel_Force : ∀ c ∈ [Cat.C, .SA], AntisymmRel ExtendsTo c .Force := by decide +kernel

/-- The verbal spine rises strictly from the verb through v, Voice, tense, finiteness and focus to
Force, and the nominal spine from the noun through the dividing and counting heads and D to K. -/
theorem isChain_asymmRel :
    [Cat.V, .v, .Voice, .T, .Fin, .Foc, .Force].IsChain (AsymmRel ExtendsTo) ∧
      [Cat.N, .Q, .Num, .D, .K].IsChain (AsymmRel ExtendsTo) := by
  decide +kernel

/-- Keine's nominalized clause and the CP are incomparable. -/
theorem not_extendsTo_Nmlz_C : ¬ ExtendsTo .Nmlz .C ∧ ¬ ExtendsTo .C .Nmlz := by decide +kernel

end Cat

end Minimalist
