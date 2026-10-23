module

public import Linglib.Morphology.DistributedMorphology.Locality
public import Linglib.Data.Examples.Marantz2013

/-!
# Marantz (2013): Locality Domains for Contextual Allomorphy Across the Interfaces

This file formalizes the locality claim of [marantz-2013]: contextual allosemy, the choice
of a polysemous root's meaning in context, is bounded exactly as contextual allomorphy is,
by the spell-out domain of the first category head and by adjacency at the interface,
phonological for allomorphy and semantic for allosemy. Past tense conditions the root of
*taught* across a null v but not the root of *quantized* across *-ize*; a second category
head closes the domain, as *-er*, *-ness*, and the verb made from the noun *house* show;
*global* fixes the reading *globalize* cannot revert. The heads of the examples with their
nullness at each interface (`Head`, `Morpheme`, `cyclic`, `phonNull`, `semNull`) and the
words with the head whose conditioning is at issue (`Row`, `rows`) give the results: attested
conditioning is visible at its interface and blocked conditioning is not
(`allomorphy_rows`, `allosemy_rows`), idioms live below Voice in a domain that neither
contains nor is contained in the root's (`idiom_rows`, `domains_cross_cut`), and a head
that conditions the root is the first category head or noncyclic with only null heads below
it (`strong_prediction`).

## Implementation notes

The words are the rows of `Data/Examples/Marantz2013`, the examples of (1) to (3) and (5) to
(7) and Table 6.1 of the chapter; the locality predicates are those of
`Morphology/DistributedMorphology/Locality`.

## References

* [marantz-2013]
-/

@[expose] public section

namespace Marantz2013

open DistributedMorphology

/-! ### Heads and interfaces -/

/-- The heads of the examples: the categorizers, Voice, and the noncyclic
tense, participle, and continuative heads. -/
inductive Head where
  | n | v | a | voice | tense | participle | continuative
  deriving DecidableEq, Repr

/-- Whether a head occurrence contributes at LF. -/
inductive Sem where
  | contentful | null
  deriving DecidableEq, Repr

/-- A head occurrence: its exponent, empty when phonologically null, and its
semantic contribution. -/
structure Morpheme where
  head : Head
  exponent : String
  sem : Sem
  deriving DecidableEq, Repr

/-- The category heads are the cyclic heads. -/
def cyclic (m : Morpheme) : Prop := m.head = .n ∨ m.head = .v ∨ m.head = .a

/-- Phonologically null: no overt exponent. -/
def phonNull (m : Morpheme) : Prop := m.exponent = ""

/-- Semantically null: contributes nothing at LF. -/
def semNull (m : Morpheme) : Prop := m.sem = .null

/-- Introduces the external argument. -/
def agentive (m : Morpheme) : Prop := m.head = .voice

instance : DecidablePred cyclic := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))
instance : DecidablePred phonNull := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred semNull := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred agentive := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-! ### The words -/

/-- The paper's claim about a head's conditioning of its root. -/
inductive Claim where
  | attested | blocked
  deriving DecidableEq, Repr, Fintype

/-- A word, the head whose conditioning of the root is at issue, and the
paper's claims about allomorphy, allosemy, and idiomatic meaning. -/
structure Row where
  form : String
  spine : ComplexHead Root Morpheme
  trigger : Fin spine.heads.length
  allomorphy : Option Claim
  allosemy : Option Claim
  idiom : Option Claim
  deriving Repr

/-- A head occurrence from the pool's labels; `v0` is a semantically null v. -/
def Morpheme.ofLabel (exp : String) : String → Option Morpheme
  | "n" => some ⟨.n, exp, .contentful⟩
  | "v" => some ⟨.v, exp, .contentful⟩
  | "v0" => some ⟨.v, exp, .null⟩
  | "a" => some ⟨.a, exp, .contentful⟩
  | "voice" => some ⟨.voice, exp, .contentful⟩
  | "T" => some ⟨.tense, exp, .contentful⟩
  | "ptcp" => some ⟨.participle, exp, .contentful⟩
  | "cont" => some ⟨.continuative, exp, .contentful⟩
  | _ => none

/-- The position of the trigger among the heads, innermost first. -/
def triggerOfLabel : String → Option ℕ
  | "1" => some 0
  | "2" => some 1
  | "3" => some 2
  | "4" => some 3
  | _ => none

def Claim.ofLabel : String → Option Claim
  | "attested" => some .attested
  | "blocked" => some .blocked
  | _ => none

/-- The roots of the pool, indexed by first occurrence. -/
def rootNames : List String := (Examples.all.filterMap (·.feature? "root")).eraseDups

def Row.ofDatum (ex : Datum) : Option Row := do
  let root ← ex.feature? "root"
  let heads := [("h1", "h1exp"), ("h2", "h2exp"), ("h3", "h3exp"), ("h4", "h4exp")].filterMap
    fun (k, e) ↦ (ex.feature? k).bind (Morpheme.ofLabel ((ex.feature? e).getD ""))
  let t ← (ex.feature? "trigger").bind triggerOfLabel
  if h : t < heads.length then
    pure ⟨ex.primaryText, ⟨⟨rootNames.idxOf root⟩, heads⟩, ⟨t, h⟩,
      (ex.feature? "allomorphy").bind Claim.ofLabel, (ex.feature? "allosemy").bind Claim.ofLabel,
      (ex.feature? "idiom").bind Claim.ofLabel⟩
  else none

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by decide

/-- The words of (1)–(3), (5)–(7), Table 6.1, and §6.2–6.3. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-! ### Predictions -/

/-- **Allomorphy** ((1)–(3), §6.2): the trigger conditions root allomorphy
iff it is local and every head between them is phonologically null. -/
theorem allomorphy_rows :
    ∀ r ∈ rows, ∀ c, r.allomorphy = some c →
      (r.spine.SeesRoot cyclic phonNull r.trigger ↔ c = .attested) := by
  decide

/-- **Allosemy** (§6.2–6.4): the trigger fixes a special root meaning iff it
is local and every head between them is semantically null — so an overt but
semantically null verbalizer lets a noncyclic participle or continuative reach
the root, and an overt adjectivizer blocks it. -/
theorem allosemy_rows :
    ∀ r ∈ rows, ∀ c, r.allosemy = some c →
      (r.spine.SeesRoot cyclic semNull r.trigger ↔ c = .attested) := by
  decide

/-- **Idiom** (§6.3): the idiomatic *nationalize* lies below any external
argument, though its v is not local to the root. -/
theorem idiom_rows :
    ∀ r ∈ rows, r.idiom = some .attested →
      r.spine.IdiomLocal agentive r.trigger ∧ ¬ r.spine.RootLocal cyclic r.trigger := by
  decide

theorem domains_cross_cut :
    (∃ r ∈ rows, r.spine.RootLocal cyclic r.trigger ∧ ¬ r.spine.IdiomLocal agentive r.trigger) ∧
      ∃ r ∈ rows, r.spine.IdiomLocal agentive r.trigger ∧ ¬ r.spine.RootLocal cyclic r.trigger := by
  decide

/-- **The strong prediction** (§6.5): whatever conditions the root across an
intervening head sees only null heads below it, and if it is itself a
category head it is the first. -/
theorem strong_prediction {s : ComplexHead Root Morpheme} {null : Morpheme → Prop}
    {i : Fin s.heads.length}
    (h : s.SeesRoot cyclic null i) :
    (∀ j < i, null s.heads[j]) ∧ (cyclic s.heads[i] → ∀ j < i, ¬ cyclic s.heads[j]) :=
  ⟨h.2, h.rootLocal.cyclic_first⟩

end Marantz2013
