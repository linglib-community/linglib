module

public import Linglib.Semantics.Mereology.Topology
public import Linglib.Semantics.Plurality.Groups
public import Linglib.Data.Examples.GrimmDocekal2021
public import Linglib.Data.Examples.Readers

/-!
# Grimm and Dočekal (2021): Counting Aggregates, Groups and Kinds

Grimm and Dočekal account for the Czech morphology that counts aggregates, groups, and kinds. The
suffix *-í* derives strongly non-countable nouns from countable roots, *listí* 'foliage' from *list*
'leaf', which take no plural, no cardinal, and no packaging (`derived_aggregates_noncountable`); the
group numeral *-ice* yields a countable group, *dvě trojice námořníků* 'two groups of three
sailors', whereas the aggregate numeral *-oje* and the taxonomic numeral *-ojí* yield phrases that
no outer cardinal or universal quantifier can take (`complex_numerals_uncounted`); *-oje* selects
nouns whose referents come in connected sets (`aggregate_numeral_selects`); and Czech nouns are
inflexible, with no grinding and a taxonomic plural confined to non-episodic contexts where the
taxonomic numeral is free (`taxonomic_plural_nonepisodic`). Section 5 extends Krifka's nominal
semantics with Landman's groups for *-ice* and with Grimm's mereotopology for *-í* and *-oje*: a
cluster is a sum of entities transitively connected through entities of their kind
(`Mereology.IsCluster`), a maximal cluster absorbs every cluster it overlaps, *-oje* counts the
maximal clusters below its argument, whose number is therefore determinate (`ojeSem_determinate`),
and *-ojí* counts subkinds and so fails on a kind-less argument (`oji_needs_subkinds`).

## Implementation notes

The connection relation is a parameter, the paper's proximate or external connectedness, which (63)
binds existentially; the cluster of (61) uses a finite set of members and its supremum. The group
numeral is stated over the library's `Plurality.GroupStructure`, whose `up` forms a group atom
from a sum of individuals, which is why a group can be counted again. The paper's Table 1, the
twenty-two nouns derived by *-í*, is lexical data for the Czech Fragment and is not retyped here.

## Errata

The entry for *-ice* (55a), `λnλPλx[↑x ∧ P(x)(n)]`, conjoins the group `↑x` with a formula, as do
(55c) and footnote 22 (ii). `iceSem` takes the reading the text describes, the groups formed from
sums of `n` members of `P`: `λnλPλx∃y[x = ↑y ∧ P(y)(n)]`.

## References

* [grimm-docekal-2021]
* [krifka-1995b]
* [landman-1989]
* [grimm-2012]
* [casati-varzi-1999]

## TODO

Table 1's derived aggregates belong in `Fragments/Slavic/Czech/`; Krifka's kind and object unit
operators of section 4 are not formalized.
-/

@[expose] public section

namespace GrimmDocekal2021

open Mereology

/-! ### The judged noun phrases, section 2 -/

/-- A noun falls into one of these classes, which numerals and operations select. -/
inductive Noun where
  | ordinary
  | animate
  /-- The noun is derived by *-í*. -/
  | derivedAggregate
  | pluraleTantum
  /-- The noun is countable, and its referents typically come in multiples, *klíče* 'keys'. -/
  | multiple
  | substance
  | abstract
  /-- The phrase refers uniquely, *noha tohoto stolu* 'this table's leg'. -/
  | unique
  | proper
  deriving DecidableEq, Repr

/-- A phrase carries one of these numerals, or none. -/
inductive Numeral where
  | none
  | simple
  /-- The group numeral is *-ice*. -/
  | group
  /-- The aggregate numerals are *-oje* and *-ery*. -/
  | aggregate
  /-- The taxonomic numerals are *-ojí* and *-ero*. -/
  | taxonomic
  deriving DecidableEq, Repr

/-- A judged phrase tests one of these operations. -/
inductive Operation where
  | none
  | pluralization
  | simpleCardinal
  /-- The vague quantifier is *mnohé* 'many'. -/
  | vagueQuantifier
  /-- The universal quantifier is *všechny* 'all'. -/
  | universal
  /-- A simple cardinal applies over a complex numeral. -/
  | outerCardinal
  | packaging
  | grinding
  /-- An aggregate is derived with *-í*. -/
  | derivation
  deriving DecidableEq, Repr

/-- A reading is judged in one of these contexts. -/
inductive Context where
  | episodic
  | generic
  /-- The context is a fast-food order, section 2.2.2. -/
  | portion
  deriving DecidableEq, Repr

/-- A row records a noun phrase and its judgment. -/
structure Row where
  noun : Noun
  numeral : Numeral
  operation : Operation
  context : Option Context
  taxonomic : Bool
  judgment : Judgment
  deriving DecidableEq, Repr

def Row.ofDatum (ex : Datum) : Option Row := do
  let noun ← ex.parse? "noun"
    [("ordinary", Noun.ordinary), ("animate", .animate), ("derivedAggregate", .derivedAggregate),
      ("pluraleTantum", .pluraleTantum), ("multiple", .multiple), ("substance", .substance),
      ("abstract", .abstract), ("unique", .unique), ("proper", .proper)]
  let numeral ← ex.parse? "numeral"
    [("none", Numeral.none), ("simple", .simple), ("group", .group), ("aggregate", .aggregate),
      ("taxonomic", .taxonomic)]
  let operation ← ex.parse? "operation"
    [("none", Operation.none), ("pluralization", .pluralization),
      ("simpleCardinal", .simpleCardinal), ("vagueQuantifier", .vagueQuantifier),
      ("universal", .universal), ("outerCardinal", .outerCardinal), ("packaging", .packaging),
      ("grinding", .grinding), ("derivation", .derivation)]
  pure ⟨noun, numeral, operation,
    ex.parse? "context"
      [("episodic", Context.episodic), ("generic", .generic), ("portion", .portion)],
    ex.feature? "reading" = some "taxonomic", ex.judgment⟩

/-- The rows are the judged phrases of sections 2, 4, and 5. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- Nouns derived by *-í* take neither plural, nor simple cardinal, nor a vague quantifier, nor a
packaging reading, (9) to (12). -/
theorem derived_aggregates_noncountable :
    ∀ r ∈ rows, r.noun = .derivedAggregate → r.numeral ≠ .aggregate →
      r.operation ≠ .none → r.judgment ≠ .acceptable := by
  decide

-- (13)
theorem derivation_restricted :
    ∀ r ∈ rows, r.operation = .derivation → r.judgment = .ungrammatical := by
  decide

-- (17), (18), (19)
theorem group_numeral_countable :
    (∃ r ∈ rows, r.numeral = .group ∧ r.operation = .outerCardinal ∧ r.judgment = .acceptable) ∧
      (∃ r ∈ rows, r.numeral = .group ∧ r.operation = .vagueQuantifier ∧
        r.judgment = .acceptable) ∧
      ∀ r ∈ rows, r.numeral = .group → r.operation = .universal → r.judgment ≠ .acceptable := by
  decide

/-- Aggregate and taxonomic numeral phrases take no outer cardinal and no universal quantifier,
(26), (27), (32), (33). -/
theorem complex_numerals_uncounted :
    ∀ r ∈ rows, (r.numeral = .aggregate ∨ r.numeral = .taxonomic) →
      (r.operation = .outerCardinal ∨ r.operation = .universal) → r.judgment ≠ .acceptable := by
  decide

/-- *-oje* takes derived aggregates, pluralia tantum and nouns of multiples ((20) to (24)) and
rejects ordinary countable nouns ((25), (68)). -/
theorem aggregate_numeral_selects :
    (∀ r ∈ rows, r.numeral = .aggregate → r.operation = .none →
      (r.noun = .derivedAggregate ∨ r.noun = .pluraleTantum ∨ r.noun = .multiple) →
        r.judgment = .acceptable) ∧
      ∀ r ∈ rows, r.numeral = .aggregate → r.noun = .ordinary → r.judgment ≠ .acceptable := by
  decide

/-- Grinding is rejected ((34), (35)), and the taxonomic reading of a plural or cardinal phrase
needs a non-episodic context ((36) to (40); section 2.3). -/
theorem taxonomic_plural_nonepisodic :
    (∀ r ∈ rows, r.operation = .grinding → r.judgment ≠ .acceptable) ∧
      (∀ r ∈ rows, r.taxonomic = true → r.numeral ≠ .taxonomic →
        (r.judgment = .acceptable ↔ r.context = some .generic)) ∧
      ∀ r ∈ rows, r.taxonomic = true → r.numeral = .taxonomic → r.judgment = .acceptable := by
  decide

-- (52)
theorem taxonomic_needs_kind :
    ∀ r ∈ rows, r.numeral = .taxonomic → (r.noun = .unique ∨ r.noun = .proper) →
      r.judgment ≠ .acceptable := by
  decide

/-! ### The three numerals, sections 4.2 and 5

The aggregate numeral counts clusters, section 5.2. Connection is reflexive and symmetric ((56),
(57)) and whatever is connected to a part is connected to the whole (58): the axioms of
`Mereology.IsConnection`, from which overlap entails connection ((59),
`Mereology.IsConnection.of_overlap`). A cluster ((60), (61)) is `Mereology.IsCluster`, the sum of
entities of a property any two of which are transitively connected through such entities. Inside a
connected component clusters are cumulative (`Mereology.cum_isClusterIn`), the cumulativity of *-í*
nouns, *listí* and *listí* making *listí*; a maximal cluster absorbs every cluster it overlaps (63),
so two maximal clusters do not overlap (`Mereology.disjointPred_isMaxCluster`), the paper's remark
after (63). -/

variable {α : Type*} [SemilatticeSup α] (C : α → α → Prop)

/-- The group numeral (55) forms a group atom from a sum of `n` members of `P`. -/
def iceSem (G : Plurality.GroupStructure α) (n : ℕ) (P : α → ℕ → Prop) (x : α) : Prop :=
  ∃ y ∈ G.sums, x = G.up y ∧ P y n

-- (17), (54)
theorem iceSem_atom {G : Plurality.GroupStructure α} {n : ℕ} {P : α → ℕ → Prop} {x : α}
    (h : iceSem G n P x) : Mereology.Atom x :=
  let ⟨_, hy, hx, _⟩ := h
  hx ▸ G.atom_up hy

/-- By (64), `n`-*oje* `P` holds of a `P`-entity `x` when the maximal `P`-clusters properly
below `x` number `n`. -/
def ojeSem (n : ℕ) (P : α → Prop) (x : α) : Prop :=
  P x ∧ ∃ Y : Finset α, (∀ z, (z < x ∧ IsMaxCluster C P z) ↔ z ∈ Y) ∧ Y.card = n

/-- The cardinality an aggregate numeral asserts is determinate, so no outer cardinal can re-specify
it ((27) and (26)). -/
theorem ojeSem_determinate {n m : ℕ} {P : α → Prop} {x : α} (hn : ojeSem C n P x)
    (hm : ojeSem C m P x) : n = m := by
  obtain ⟨-, Y, hY, rfl⟩ := hn
  obtain ⟨-, Y', hY', rfl⟩ := hm
  rw [Finset.ext fun z ↦ (hY z).symm.trans (hY' z)]

/-- By (50), over a subkind relation `T`, `n`-*ojí* `k` holds of a set of subkinds of `k`
numbering `n`. -/
def ojiSem {κ : Type*} (T : κ → κ → Prop) (n : ℕ) (k : κ) (X : Finset κ) : Prop :=
  (∀ z ∈ X, T z k) ∧ X.card = n

/-- A kind-less argument defeats the taxonomic numeral (52), since a proper name has no
subkinds. -/
theorem oji_needs_subkinds {κ : Type*} {T : κ → κ → Prop} {k : κ} (hk : ∀ z, ¬ T z k) {n : ℕ}
    (hn : n ≠ 0) : ¬ ∃ X : Finset κ, ojiSem T n k X := by
  rintro ⟨X, hX, hcard⟩
  rcases Finset.eq_empty_or_nonempty X with rfl | ⟨z, hz⟩
  · exact hn (hcard ▸ rfl)
  · exact hk z (hX z hz)

/-! ### Three leaves in a row

The leaves of *listí* need only be proximately connected, section 5.2.1. Three leaves lie in a
row, each near its neighbours: the outer two are not near each other, yet their sum is a cluster,
since they are transitively connected through the middle leaf, which (61) lets lie outside the
cluster. Without the middle leaf the outer two form no cluster. -/

section Leaves

/-- Leaf sums are the sets of three leaves in a row. -/
abbrev LeafSum := Finset (Fin 3)

/-- Two sums are near when they contain the same or neighbouring leaves. -/
def Near (s t : LeafSum) : Prop := ∃ i ∈ s, ∃ j ∈ t, (i : ℕ) ≤ j + 1 ∧ (j : ℕ) ≤ i + 1

instance : DecidableRel Near := fun s t ↦ by unfold Near; infer_instance

/-- A leaf sum is a single leaf when it has one member. -/
def Leaf (s : LeafSum) : Prop := s.card = 1

instance : DecidablePred Leaf := fun s ↦ by unfold Leaf; infer_instance

/-- The outer leaves are the leaves other than the middle one. -/
def OuterLeaf (s : LeafSum) : Prop := s = {0} ∨ s = {2}

instance : DecidablePred OuterLeaf := fun s ↦ by unfold OuterLeaf; infer_instance

/-- The outer leaves sum to a cluster of leaves, connected through the middle leaf. -/
example : IsCluster Near Leaf ({0, 2} : LeafSum) := by
  have h02 : (connectionGraph Near Leaf).Reachable {0} {2} :=
    (connectionGraph_reachable (b := {1}) (by decide) (by decide) (by decide)).trans
      (connectionGraph_reachable (by decide) (by decide) (by decide))
  refine isCluster_iff.2 ⟨{{0}, {2}}, by simp, by decide, fun z hz z' hz' ↦ ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases hz with rfl | rfl <;> rcases hz' with rfl | rfl
    exacts [.refl _, h02, h02.symm, .refl _]
  · simpa using isLUB_pair (a := ({0} : LeafSum)) (b := {2})

/-- Without the middle leaf, the outer leaves form no cluster. -/
example : ¬ IsCluster Near OuterLeaf ({0, 2} : LeafSum) := by
  rintro ⟨c, Z, -, hZ, hlub⟩
  have hR : ∀ a b : LeafSum, a ≠ b → ¬ (OuterLeaf a ∧ OuterLeaf b ∧ Near a b) := by decide
  have hub (u : LeafSum) (hu : ∀ z ∈ Z, z = u) : ({0, 2} : LeafSum) ≤ u :=
    hlub.2 fun z hz ↦ (hu z hz).le
  have h0 : ({0} : LeafSum) ∈ Z := by
    by_contra h
    exact absurd (hub {2} fun z hz ↦ (hZ z hz).1.resolve_left fun e ↦ h (e ▸ hz)) (by decide)
  have h2 : ({2} : LeafSum) ∈ Z := by
    by_contra h
    exact absurd (hub {0} fun z hz ↦ (hZ z hz).1.resolve_right fun e ↦ h (e ▸ hz)) (by decide)
  have hreach := SimpleGraph.ConnectedComponent.exact ((hZ _ h0).2.trans (hZ _ h2).2.symm)
  rcases (SimpleGraph.reachable_iff_reflTransGen _ _).1 hreach |>.cases_head with h | ⟨b, hb, -⟩
  · exact absurd h (by decide)
  · simp only [connectionGraph, SimpleGraph.fromRel_adj] at hb
    rcases hb.2 with h | h
    exacts [hR _ _ hb.1 h, hR _ _ (Ne.symm hb.1) h]

end Leaves

end GrimmDocekal2021
