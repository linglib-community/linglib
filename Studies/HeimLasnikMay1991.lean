module

public import Linglib.Semantics.Plurality.Reciprocal
public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Data.Examples.HeimLasnikMay1991

/-!
# Heim, Lasnik and May (1991): Reciprocity and Plurality

Heim, Lasnik and May analyze reciprocals quantificationally: *each other* decomposes at LF into a
distributor, *each*, which moves to the antecedent NP, and a reciprocator, *e other*, each keeping
the semantics of its non-reciprocal use, so that "the men saw each other" is `[[the men]₁ each₂] saw
[e₂ other]₃` ((8), (20)). The pieces `other` (16), `reciprocator` (18), and `distributor` (19)/(28)
compose to `eachOtherLF`, which on a plural antecedent is Strong Reciprocity
(`eachOtherLF_iff_strongReciprocity`), is vacuously true on a singleton, where Strong Reciprocity
fails, and is contradictory over an asymmetric relation ((68)). The grain problem
of §3, that (43) is three-ways ambiguous under a single indexing, is resolved by the range and
distribution indices of plural NPs: the four construals of an embedded pronoun (49) yield the four
readings, with the *I* and *you* readings bound variables and the *we* readings coreference, which a
preposed adjunct (60) filters. The scope puzzle of §4 is the attachment site of *each* (67): narrow
scope forces coreference and broad scope a bound variable, because distributors need sum-denoting
hosts and do not iterate (72) and the trace of *each* must be bound (74).

## Implementation notes

Pluralities are `Finset`s of atoms and proper atomic parthood is membership, matching the
substrate's `Reciprocal`. The reciprocator has universal force, as the paper adopts while
considering groups of two, where universal and existential force coincide; the weaker
schemes for larger groups are those of Dalrymple and colleagues. The grain and scope solutions are
stated over the finite construal and attachment types, with readings and anaphora
types derived; the syntactic derivation of *each*-movement itself is not represented.

## TODO

* §4.2 long-distance reciprocals and the Specified Subject Condition effects of §4.3.

## References

* [heim-lasnik-may-1991]
* [higginbotham-1980]
* [higginbotham-1985]
* [dalrymple-et-al-1998]
-/

@[expose] public section

namespace HeimLasnikMay1991

open Reciprocal

variable {A : Type*}

/-! ### The compositional pieces (§2.2)

HLM's model is `⟨D, A, Π⟩`: a domain with mereological structure, atoms
`A`, and proper-part-of `Π`; `·Π` is the proper-*atomic*-part relation.
Pluralities are encoded here as `Finset A` (sums of atoms) with `·Π` as
membership, matching the `(R, X)` signature of
`Reciprocal`. -/

/-- *other* (16) is a 3-place relation: its referent `z` is an atomic part
    of the range `y` distinct from the contrast `x`. In reciprocals both
    implicit arguments are supplied by the derived antecedent phrase:
    the contrast is bound by *each*, the range is coreferential with the
    antecedent. -/
def other (contrast : A) (range : Finset A) (z : A) : Prop :=
  z ∈ range ∧ z ≠ contrast

/-- The reciprocator `[e other]` (18) has universal force, so `x` stands in `ζ` to every
    *other* atomic part of the range. The paper adopts universal force while considering
    groups of two, where universal and existential force coincide. -/
def reciprocator (range : Finset A) (ζ : A → A → Prop) (x : A) : Prop :=
  ∀ z, other x range z → ζ x z

/-- The distributor (19)/(28), *each* or the covert `D`, universally quantifies over the
    atomic parts of its host NP. It is Link's D operator (`Mereology.D`) on finite
    sets of atoms. -/
def distributor (np : Finset A) (φ : A → Prop) : Prop :=
  ∀ x ∈ np, φ x

/-- The LF of "np V each other" after *each*-movement (8)/(20):
    the distributor scopes over the reciprocated predicate, with the
    reciprocator's range and contrast both anaphoric to the derived
    antecedent. -/
def eachOtherLF (np : Finset A) (R : A → A → Prop) : Prop :=
  distributor np (reciprocator np R)

/-! ### The keystone (21) -/

theorem eachOtherLF_iff_strongReciprocity {np : Finset A} (hnp : 1 < np.card)
    (R : A → A → Prop) : eachOtherLF np R ↔ StrongReciprocity R np := by
  rw [strongReciprocity_iff, and_iff_right (Finset.one_lt_card_iff_nontrivial.1 hnp)]
  constructor
  · intro h x hx y hy hxy
    exact h x hx y ⟨hy, hxy.symm⟩
  · intro h x hx z hz
    exact h hx hz.1 hz.2.symm

theorem eachOtherLF_singleton (a : A) (R : A → A → Prop) :
    eachOtherLF {a} R := by
  intro x hx z hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [Finset.mem_singleton] at hx hz1
  exact absurd (hz1.trans hx.symm) hz2

-- (68), (69), (70), (71), (72)
theorem eachOtherLF_asymmetric_contradictory
    {np : Finset A} {R : A → A → Prop}
    (hasym : ∀ x y, R x y → ¬ R y x) (hcard : 2 ≤ np.card) :
    ¬ eachOtherLF np R := by
  intro h
  have hpos : 0 < np.card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  obtain ⟨y, hy, hyx⟩ := np.exists_mem_ne (by omega) x
  exact hasym x y (h x hx y ⟨hy, hyx⟩) (h y hy x ⟨hx, hyx.symm⟩)

/-! ### The grain problem (§3)

Plural NPs bear a *range* index and, optionally, a *distribution* index
((26)–(28)); in a reciprocal LF the reciprocator contributes a third
index. An embedded plural pronoun anaphoric to the antecedent therefore
has exactly four construals ((29)/(49)) — the theory is exactly as
fine-grained as the attested ambiguity of "John and Mary told each other
that they should leave". -/

/-- The four construals of an embedded plural pronoun in a reciprocal
    sentence ((49a–d)). -/
inductive PronounConstrual where
  /-- coindexed with the antecedent's referential *range* index -/
  | range
  /-- range-coindexed, with its own covert distributor `D` -/
  | rangeDistributed
  /-- bound by the *distribution* index contributed by *each* -/
  | distributor
  /-- bound by the *reciprocator*'s index -/
  | reciprocator
  deriving DecidableEq, Repr

/-- The readings of "John and Mary told each other that they should
    leave" ((43): *I* = "each told the other: I should leave", *you* =
    "…: you should leave", *we* together/separately). -/
inductive GrainReading where
  | I
  | you
  | weTogether
  | weSeparately
  deriving DecidableEq, Repr

/-- Each construal yields exactly one reading (49a–d). -/
def PronounConstrual.reading : PronounConstrual → GrainReading
  | .distributor      => .I
  | .reciprocator     => .you
  | .range            => .weTogether
  | .rangeDistributed => .weSeparately

/-- Bound-variable vs coreference anaphora — the *type* distinction the
    grain solution encodes structurally (§3.1, against
    [higginbotham-1985]'s linking alternative, where I/we would be one
    vague reading). -/
inductive AnaphoraType where
  | boundVariable
  | coreference
  deriving DecidableEq, Repr

/-- Construals bound by the quantificational *each*/*other* indices are
    singular bound variables; range-coindexed construals are coreference
    with the referential sum. Hence I/you = bound variable, we =
    coreference. -/
def PronounConstrual.anaphoraType : PronounConstrual → AnaphoraType
  | .distributor | .reciprocator  => .boundVariable
  | .range | .rangeDistributed    => .coreference

/-- A bound-variable construal ranges over atoms; a coreferential one
    denotes the antecedent's sum (§2.4). -/
def PronounConstrual.DenotesAtom (c : PronounConstrual) : Prop :=
  c.anaphoraType = .boundVariable

/-- The construal places the pronoun under a distributor of its own ((49d)). -/
def PronounConstrual.HostsDistributor : PronounConstrual → Prop
  | .rangeDistributed => True
  | _                 => False

/-- Preposed adjuncts block bound-variable anaphora, since a quantifier
    cannot bind into a preposed adjunct (61), so "After they had left the
    room, the candidates criticized each other" (60) keeps only the *we*
    construals, while the postposed (57) is fully ambiguous. -/
def PronounConstrual.AvailableInPreposedAdjunct (c : PronounConstrual) : Prop :=
  c.anaphoraType = .coreference

instance : DecidablePred PronounConstrual.DenotesAtom := fun c ↦
  inferInstanceAs (Decidable (c.anaphoraType = .boundVariable))

instance : DecidablePred PronounConstrual.HostsDistributor
  | .rangeDistributed => isTrue trivial
  | .range | .distributor | .reciprocator => isFalse id

instance : DecidablePred PronounConstrual.AvailableInPreposedAdjunct := fun c ↦
  inferInstanceAs (Decidable (c.anaphoraType = .coreference))

-- (60), (57)
theorem not_availableInPreposedAdjunct_iff (c : PronounConstrual) :
    ¬ c.AvailableInPreposedAdjunct ↔ c.reading = .I ∨ c.reading = .you := by
  cases c <;> decide

/-! ### The scope puzzle (§4)

"John and Mary think they like each other" (64) has a narrow reading
(they think: we like each other) and a broad one (each thinks: I like
the other). HLM resolve it as the attachment site of *each* ((67)):
to the embedded pronoun (narrow) or to the matrix subject (broad). The
correlation with anaphora type is *derived*: distributors need
sum-denoting hosts and cannot iterate, and the trace of *each* must be
bound by the index its host acquires (Principle A). -/

/-- Where *each* attaches at LF ((67a)/(67b)). -/
inductive EachAttachment where
  /-- `[they₁ each₂] like [e₂ other]` — narrow scope -/
  | embedded
  /-- `[[John and Mary]₁ each₂] think they₂ like [e₂ other]` — broad -/
  | matrix
  deriving DecidableEq, Repr

/-- Wellformedness of an attachment–construal pair, from two independent
    constraints: an *each* attached to the embedded pronoun needs a
    sum-denoting host that is not already distributed ((72): distributors
    do not iterate), and under matrix attachment the pronoun must carry
    the distribution index so that the trace of *each* is A-bound
    (Principle A, (74)). -/
def ScopeWellFormed : EachAttachment → PronounConstrual → Prop
  | .embedded, c => ¬ c.DenotesAtom ∧ ¬ c.HostsDistributor
  | .matrix, c => c = .distributor

-- (67a)
theorem narrow_forces_coreference (c : PronounConstrual)
    (h : ScopeWellFormed .embedded c) :
    c.anaphoraType = .coreference := by
  cases c <;> simp_all [ScopeWellFormed, PronounConstrual.DenotesAtom,
    PronounConstrual.anaphoraType]

-- (67b), §4.1
theorem broad_forces_bound_variable (c : PronounConstrual)
    (h : ScopeWellFormed .matrix c) :
    c.anaphoraType = .boundVariable := by
  cases c <;> simp_all [ScopeWellFormed, PronounConstrual.anaphoraType]

-- (67a)
theorem embedded_unique_construal (c : PronounConstrual) :
    ScopeWellFormed .embedded c ↔ c = .range := by
  cases c <;> simp [ScopeWellFormed, PronounConstrual.DenotesAtom,
    PronounConstrual.anaphoraType, PronounConstrual.HostsDistributor]

end HeimLasnikMay1991
