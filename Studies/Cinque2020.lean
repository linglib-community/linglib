module

public import Studies.Cinque2005
public import Linglib.Fragments.English.Relativization
public import Linglib.Fragments.Hebrew.Relativization

/-!
# Cinque (2020): The Syntax of Relative Clauses

Cinque derives every type of relative clause from one double-headed structure: the clause is merged
in a specifier of the nominal extended projection, the part of that projection below it is the
external Head, and the clause contains an internal Head. Movement, deletion under identity and
replacement by a proform do the rest (Introduction, §1.5). In a raising derivation the internal Head
raises to Spec,CP and deletes the external one, so the overt Head reconstructs into the clause; in a
matching derivation the external Head is overt and the internal one is deleted or replaced. Which
options a relative clause has depends on its type, through the height at which the type is merged,
and on whether the two Heads match (Introduction): a type merged higher has a bigger external Head
(`externalHead_mono`), and a Head is deleted only under identity with the other, so an internal Head
bigger than the external one is neither a gap nor raised (`RC.WellFormed.not_reconstructs_of_lt`).

`RCType.externalHead` reads the external Head off the order of external Merge (205): the
indefinite `dP` for restrictives, merged between the demonstrative and the cardinal numeral, a
full DP for non-restrictives, merged above the demonstrative. A restrictive with a relative
pronoun, a DP, is therefore derived by matching and does not reconstruct
(`RC.WellFormed.not_reconstructs_of_relativePronoun`), and maximalizing relatives, which force
raising, take no relative pronoun (`RC.WellFormed.strategy_ne_relativePronoun_of_maximalizing`).
The derivations of Universal 20 in `Cinque2005` linearize (205), before the noun without
movement and after it in the mirror order when the noun's phrase raises past each modifier,
which gives the orders of the rigid head-final and head-initial languages of §3.5
(`unmarkedOrders_restrictive`, `unmarkedOrders_participial`).

## Implementation notes

* A DP with or without its case layer is one size of Head, as in Chapter 4; a DP inside an
  adposition's or a possessor's phrase is bigger.
* (205) is taken without the universal quantifier; the non-integrated non-restrictives above it
  belong to discourse grammar (§3.1) and are left out.
* Verb-coding is not a strategy for the internal Head: §4.6 analyses it as marking on the verb
  alongside deletion or pronoun retention, under the same size condition.

## TODO

* Chapter 2 derives each syntactic type (internally headed, double-headed, headless,
  correlative) from which Heads are pronounced and where they move; only the two derivations of
  externally headed relatives are modelled.
* The ordering contrasts between stacked relatives that motivate (205), (176)–(177) and
  (183)–(191), are not rows, and §2.2.3's account of the absence of relative pronouns in
  prenominal relatives, by R-binding under the linear correspondence axiom, needs a
  linearization the substrate lacks.

## References

* [cinque-2020]
* [cinque-2005]
-/

@[expose] public section

namespace Cinque2020

open Relativization Cinque2005

/-! ### The order of external Merge (§3.5) -/

/-- The types of relative clause, by the position of their external Merge. -/
inductive RCType
  /-- Participial, of an individual-level property (§3.5.7). -/
  | participialIndividual
  /-- Participial, of a stage-level property. -/
  | participialStage
  | infinitival
  /-- Amount and other maximalizing relatives, whose Head is interpreted inside the clause
  (§1.2). -/
  | maximalizing
  /-- Finite restrictive, with Italian *che* or *cui*. -/
  | restrictive
  /-- Finite restrictive with Italian *il quale*, merged above the unmarked one (§3.5.4). -/
  | restrictiveMarked
  | kindDefining
  /-- Integrated non-restrictive (§3.1). -/
  | nonRestrictive
  deriving DecidableEq, Repr, Fintype

/-- A position in the nominal extended projection, held by the noun, one of its modifiers of
Universal 20 or a relative clause. -/
inductive Slot
  | N | A | Num | Dem
  | rc (t : RCType)
  deriving DecidableEq, Repr

/-- The order of external Merge (205), bottom up from the noun, without the universal
quantifier. -/
def hierarchy : List Slot :=
  [.A, .rc .participialIndividual, .rc .participialStage, .Num, .rc .infinitival,
    .rc .maximalizing, .rc .restrictive, .rc .restrictiveMarked, .rc .kindDefining, .Dem,
    .rc .nonRestrictive]

/-- The height of a type's external Merge. -/
def RCType.height (t : RCType) : ℕ := hierarchy.idxOf (.rc t)

/-- A type is below another when it is merged lower. -/
instance : LinearOrder RCType := LinearOrder.lift' RCType.height (by decide)

/-! ### Linearization (§1.4, §3.5) -/

/-- The lexical item at a slot in the derivations of `Cinque2005`, a relative clause being a
`C`. -/
def Slot.token : Slot → Minimalist.LexicalItem.Token
  | .N => tokN
  | .A => tokA
  | .Num => tokNum
  | .Dem => tokDem
  | .rc t => ⟨.of .C [], t.height + 5⟩

/-- The surface orders of the unmarked derivations of `Cinque2005`, without movement or raising
the noun's phrase past each modifier with whose-picture pied-piping, from the noun and the slots
`s` merged in the order of (205). -/
def unmarkedOrders (s : List Slot) : List (List Minimalist.LexicalItem.Token) :=
  (((stagesOf ((hierarchy.filter (· ∈ s)).map Slot.token)).filter (·.marked = [])).map
    (·.derivation.surfaceTokens)).eraseDups

/-- A finite restrictive surfaces as Dem RC Num A N in rigid head-final languages (181) and N A Num
RC Dem in rigid head-initial ones (182). -/
theorem unmarkedOrders_restrictive :
    unmarkedOrders [.A, .Num, .rc .restrictive, .Dem] =
      [[.Dem, .rc .restrictive, .Num, .A, .N], [.N, .A, .Num, .rc .restrictive, .Dem]].map
        (·.map Slot.token) := by
  decide +kernel

/-- A relative merged between numeral and adjectives surfaces as Dem Num RC A N (200a–b),
(192)–(197) or as N A RC Num Dem (200c). -/
theorem unmarkedOrders_participial :
    unmarkedOrders [.A, .Num, .rc .participialStage, .Dem] =
      [[.Dem, .Num, .rc .participialStage, .A, .N],
        [.N, .A, .rc .participialStage, .Num, .Dem]].map (·.map Slot.token) := by
  decide +kernel

-- (171), (175)
theorem unmarkedOrders_dem :
    unmarkedOrders [.rc .restrictive, .Dem] =
        [[.Dem, .rc .restrictive, .N], [.N, .rc .restrictive, .Dem]].map (·.map Slot.token) ∧
      unmarkedOrders [.Dem, .rc .nonRestrictive] =
        [[.rc .nonRestrictive, .Dem, .N], [.N, .Dem, .rc .nonRestrictive]].map
          (·.map Slot.token) := by
  decide +kernel

/-! ### The two Heads and the two derivations (§1.5) -/

/-- The size of a Head, a chunk of the nominal extended projection or a phrase around one. From
the smallest, a Head is the noun with its adjectives, the indefinite `dP` up to the cardinal
numeral, the full `DP`, or a DP inside a larger phrase, an adposition's or a possessor's. -/
inductive Size
  | NP | dP | DP | embedded
  deriving DecidableEq, Repr, Fintype

/-- Sizes are ordered by containment. -/
instance : LinearOrder Size := LinearOrder.lift' Size.ctorIdx (by decide)

/-- The external Head is the part of the nominal extended projection below the relative clause
(§1.4). It is a DP if it contains the demonstrative and the indefinite `dP` if it contains the
cardinal numeral. -/
def RCType.externalHead (t : RCType) : Size :=
  if .Dem ∈ hierarchy.take t.height then .DP
  else if .Num ∈ hierarchy.take t.height then .dP else .NP

/-- A type merged higher has a bigger external Head (Introduction, fn. 3). -/
theorem externalHead_mono : Monotone RCType.externalHead := by decide

/-- The two derivations, which differ in which Head is overt. -/
inductive Derivation
  /-- The internal Head raises to Spec,CP, is overt and deletes the external Head. -/
  | raising
  /-- The external Head is overt; the internal Head is deleted or replaced by a proform. -/
  | matching
  deriving DecidableEq, Repr

/-- The derivations a type admits. Maximalizing relatives, whose Head is interpreted inside the
clause, force raising (§2.1.1); kind-defining and non-restrictive relatives have only matching
(§2.1.1 fn. 12, §3.1.8). -/
def RCType.Admits (t : RCType) (d : Derivation) : Prop :=
  (t = .maximalizing → d = .raising) ∧ (t = .kindDefining ∨ t = .nonRestrictive → d = .matching)

instance (t : RCType) (d : Derivation) : Decidable (t.Admits d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Strategies for the internal Head (Chapter 4) -/

/-- The strategies realizing the internal Head. -/
inductive Strategy
  /-- A gap with an invariant relativizer, English *that*, Italian *che*. -/
  | invariantRelativizer
  /-- A relative pronoun or adjective, *who* and *which*, Italian *cui* and *il quale*. -/
  | relativePronoun
  /-- A resumptive pronoun or epithet. -/
  | resumptive
  /-- PRO, in participial relative clauses (§4.4). -/
  | pro
  /-- The internal Head pronounced as well as the external one (§4.5). -/
  | nonReduction
  deriving DecidableEq, Repr

/-- What the strategy leaves at the relativized position, in the substrate's inventory, where
PRO counts as a gap. -/
def Strategy.toNPRel : Strategy → NPRel
  | .invariantRelativizer | .pro => .gap
  | .relativePronoun => .relPronoun
  | .resumptive => .resumptive
  | .nonReduction => .nonReduction

/-! ### The relative clause -/

/-- A relative clause in the double-headed structure, with its type, its derivation, its
internal Head and the strategy realizing it, and the relativized position. -/
structure RC where
  type : RCType
  derivation : Derivation
  internalHead : Size
  strategy : Strategy
  position : Position
  deriving Repr

/-- The overt Head reconstructs into the clause when it is in a chain with the clause-internal
position, in raising (§1.5). -/
def RC.Reconstructs (r : RC) : Prop := r.derivation = .raising

instance (r : RC) : Decidable r.Reconstructs := inferInstanceAs (Decidable (_ = _))

/-- A relative clause is well formed when its type admits the derivation, a Head is deleted
only under identity with the other, the external Head in raising (§4.1) and the internal Head
under the gap strategy (§1.5), and a relative pronoun, a DP, realizes an internal Head at least
that big (§2.1.2). -/
structure RC.WellFormed (r : RC) : Prop where
  admits : r.type.Admits r.derivation
  deletion : r.Reconstructs ∨ r.strategy = .invariantRelativizer →
    r.internalHead = r.type.externalHead
  relativePronoun : r.strategy = .relativePronoun → .DP ≤ r.internalHead

theorem RC.wellFormed_iff (r : RC) : r.WellFormed ↔ r.type.Admits r.derivation ∧
    (r.Reconstructs ∨ r.strategy = .invariantRelativizer →
      r.internalHead = r.type.externalHead) ∧
    (r.strategy = .relativePronoun → .DP ≤ r.internalHead) :=
  ⟨fun ⟨a, d, p⟩ ↦ ⟨a, d, p⟩, fun ⟨a, d, p⟩ ↦ ⟨a, d, p⟩⟩

instance (r : RC) : Decidable r.WellFormed := decidable_of_iff _ r.wellFormed_iff.symm

variable {r : RC}

-- §4.2
theorem RC.wellFormed_iff_of_invariantRelativizer (hs : r.strategy = .invariantRelativizer) :
    r.WellFormed ↔ r.type.Admits r.derivation ∧ r.internalHead = r.type.externalHead := by
  simp [RC.wellFormed_iff, hs]

/-- A relative clause whose internal Head is bigger than its external one neither reconstructs nor
has a gap (§1.5, §2.1.2). -/
theorem RC.WellFormed.not_reconstructs_of_lt (h : r.WellFormed)
    (hlt : r.type.externalHead < r.internalHead) :
    ¬ r.Reconstructs ∧ r.strategy ≠ .invariantRelativizer :=
  not_or.1 (mt h.deletion hlt.ne')

/-- Below the demonstrative, a relative pronoun is bigger than the external Head, so the
relative clause does not reconstruct (§2.1.2.2 (43), §2.1.1 fn. 13). -/
theorem RC.WellFormed.not_reconstructs_of_relativePronoun (h : r.WellFormed)
    (hext : r.type.externalHead < .DP) (hs : r.strategy = .relativePronoun) :
    ¬ r.Reconstructs :=
  (h.not_reconstructs_of_lt (hext.trans_le (h.relativePronoun hs))).1

/-- Maximalizing relatives take no relative pronoun (§2.1.1 (8)), since they force raising, which
needs the internal Head to match the external `dP`. -/
theorem RC.WellFormed.strategy_ne_relativePronoun_of_maximalizing (h : r.WellFormed)
    (ht : r.type = .maximalizing) : r.strategy ≠ .relativePronoun := fun hs ↦
  h.not_reconstructs_of_relativePronoun (by rw [ht]; decide) hs (h.admits.1 ht)

/-! ### Worked examples -/

/-- *The book that John read*, by matching. -/
def englishThatObject : RC := ⟨.restrictive, .matching, .dP, .invariantRelativizer, .directObject⟩

/-- *The champagne that they spilled*, on its amount reading, by raising. -/
def englishThatAmount : RC := ⟨.maximalizing, .raising, .dP, .invariantRelativizer, .directObject⟩

/-- *The man to whom I spoke*, whose internal Head, a DP inside a PP, is a relative pronoun. -/
def englishWhomOblique : RC :=
  ⟨.restrictive, .matching, .embedded, .relativePronoun, .oblique⟩

/-- Hebrew *she-* with a resumptive at the genitive, the internal Head a DP inside a DP. -/
def hebrewResumptiveGenitive : RC :=
  ⟨.restrictive, .matching, .embedded, .resumptive, .genitive⟩

theorem englishThat_attested :
    englishThatObject.WellFormed ∧ englishThatAmount.WellFormed ∧
      ¬ englishThatObject.Reconstructs ∧ englishThatAmount.Reconstructs ∧
      Strategy.invariantRelativizer.toNPRel ∈
        English.Relativization.relThat.realize .directObject := by
  decide

theorem englishWhomOblique_attested :
    englishWhomOblique.WellFormed ∧
      ¬ { englishWhomOblique with strategy := .invariantRelativizer }.WellFormed ∧
      englishWhomOblique.strategy.toNPRel ∈
        English.Relativization.relWhom.realize englishWhomOblique.position := by
  decide

theorem hebrewResumptiveGenitive_attested :
    hebrewResumptiveGenitive.WellFormed ∧
      hebrewResumptiveGenitive.strategy.toNPRel ∈
        Hebrew.relShe.realize hebrewResumptiveGenitive.position := by
  decide

end Cinque2020
