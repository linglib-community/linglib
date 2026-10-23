module

public import Linglib.Data.Examples.Embick2010
public import Linglib.Morphology.DistributedMorphology.Locality

/-!
# Embick (2010): Localism versus Globalism in Morphology and Phonology

This file formalizes [embick-2010]'s C₁-LIN theory of contextual allomorphy: a node conditions
the Vocabulary Insertion ([halle-marantz-1993]) of another only when the two are concatenated and
active in the same cycle of Spell-Out. The category-defining heads are cyclic. Merging one spells
out the cyclic domains in its complement, so a cyclic head and the noncyclic heads attached to it
are realized in the cycle of the next cyclic head, the Domain Corollary, while the complement of
an inner cyclic head is inactive when an outer one is spelled out, the Activity Corollary; nodes
with null exponents are pruned from the concatenation statements. The case studies follow. The
Latin perfect indicative takes its special agreement endings only where a null present tense is
pruned between Agr and Asp[perf], the overt tenses of the other perfects intervening (§3.1.1); a
theme vowel reads the conjugation class of the node it is concatenated with, the root's across a
null v and *-ess*'s otherwise (§3.1.2); root-attached n has root-determined allomorphs while the
gerund's n, an outer cyclic head, has none, and *-ity* and *-ation* are potentiated by the *-able*
and *-ize* they follow (§2.2–2.3, §3.3); the noncyclic past tense and plural see the root across
pruned categorizers (§2.3.3); and the Hindi agentive Voice ([kratzer-1996]) shows root-determined
allomorphy in the transitive but only its default in the indirect causative, where the root lies
two cycles down (§3.2.2).

## Implementation notes

* Cycles, coactivity, the root's domain and adjacency across pruned heads are the substrate's
  `ComplexHead` API; this file contributes the heads of the case studies, the rows, and the
  predictions checked over them. A row records a word's heads innermost first with their
  exponents, the head whose realization is at issue, its conditioner, the root or another head,
  and whether the book attests or excludes the conditioning.
* The examples are `Data.Examples.Embick2010`.

## References

* [embick-2010]
* [halle-marantz-1993]
* [kratzer-1996]
-/

@[expose] public section

namespace Embick2010

open DistributedMorphology Embick2010.Examples

/-- The heads of the case studies are the categorizers, active and passive Voice, the theme
position, and the inflectional heads. -/
inductive Head
  | n
  | v
  | a
  | voice
  | voicePassive
  | theme
  | aspect
  | tense
  | agr
  | number
  deriving DecidableEq, Repr

/-- A head occurrence with its exponent, empty when null. -/
structure Morpheme where
  head : Head
  exponent : String
  deriving DecidableEq, Repr

/-- The category-defining heads are the cyclic heads (§2.3.1). -/
def cyclic (m : Morpheme) : Prop := m.head = .n ∨ m.head = .v ∨ m.head = .a

/-- A null exponent, pruned from the concatenation statements, (53) of ch. 2. -/
def phonNull (m : Morpheme) : Prop := m.exponent = ""

instance : DecidablePred cyclic := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))
instance : DecidablePred phonNull := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-! ### The case studies -/

/-- Whether the book attests the conditioning or excludes it. -/
inductive Claim
  | attested
  | blocked
  deriving DecidableEq, Repr

/-- A conditioning relation records the word's heads, the head whose realization is at issue, its
conditioner, `none` for the root, and the book's verdict. -/
structure Row where
  spine : ComplexHead Root Morpheme
  target : Fin spine.heads.length
  conditioner : Option (Fin spine.heads.length)
  claim : Claim

/-- The heads as named in the rows. -/
def headTable : List (String × Head) :=
  [("n", .n), ("v", .v), ("a", .a), ("voice", .voice), ("voicePassive", .voicePassive),
    ("theme", .theme), ("aspect", .aspect), ("tense", .tense), ("agr", .agr), ("number", .number)]

/-- The verdicts as named in the rows. -/
def claimTable : List (String × Claim) := [("attested", .attested), ("blocked", .blocked)]

/-- The roots of the pool, indexed by first occurrence. -/
def rootNames : List String := (Examples.all.filterMap (·.feature? "root")).eraseDups

/-- The heads of a row innermost first, `hᵢ` with the exponent `hᵢexp`. -/
def heads (ex : Datum) : List Morpheme :=
  ["h1", "h2", "h3", "h4", "h5"].filterMap fun k ↦
    (ex.parse? k headTable).map fun h ↦ ⟨h, (ex.feature? (k ++ "exp")).getD ""⟩

/-- The row of an example, whose positions count from one, innermost first. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let root ← ex.feature? "root"
  let hs := heads ex
  let t ← ex.nat? "target"
  let claim ← ex.parse? "claim" claimTable
  let c ← ex.feature? "conditioner"
  if ht : t - 1 < hs.length then
    if c = "root" then
      pure ⟨⟨⟨rootNames.idxOf root⟩, hs⟩, ⟨t - 1, ht⟩, none, claim⟩
    else
      let j ← ex.nat? "conditioner"
      if hj : j - 1 < hs.length then
        pure ⟨⟨⟨rootNames.idxOf root⟩, hs⟩, ⟨t - 1, ht⟩, some ⟨j - 1, hj⟩, claim⟩
      else none
  else none

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by decide

/-- The conditioning relations of §2.2–2.3 and §3.1–3.3. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-! ### Predictions -/

theorem root_rows :
    ∀ r ∈ rows, r.conditioner = none →
      (r.spine.SeesRoot cyclic phonNull r.target ↔ r.claim = .attested) := by
  decide

theorem head_rows :
    ∀ r ∈ rows, ∀ j, r.conditioner = some j →
      (r.spine.Sees cyclic phonNull r.target j ↔ r.claim = .attested) := by
  decide

/-- The Latin perfects share one cycle. Agr is coactive with Asp[perf] throughout, and only the
overt tense of the non-indicative forms intervenes, so the effect is linear rather than cyclic
(§3.1.1). -/
theorem perfect_one_cycle :
    ∀ r ∈ rows, r.spine.root = ⟨rootNames.idxOf "AM"⟩ → ∀ j, r.conditioner = some j →
      r.spine.Coactive cyclic r.target j ∧
        (r.spine.Sees cyclic phonNull r.target j ↔
          ∀ k, j < k → k < r.target → phonNull r.spine.heads[k]) := by
  decide

end Embick2010
