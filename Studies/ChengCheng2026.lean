module

public import Linglib.Data.Examples.ChengCheng2026
public import Linglib.Morphology.DistributedMorphology.RootCategorization
public import Studies.Harley2017
public import Linglib.Data.Examples.Readers

/-!
# Cheng and Cheng (2026): Using light verbs as verbalizers

Cheng and Cheng analyze the Mandarin light verb *dǎ* 'hit' as a rootless exponent of the
verbalizer, a head below the causative *gěi* and Voice *bǎ*. In *dǎ*+R (*dǎ-sǎo* 'clean') a root
adjoins to the verbalizer; in *dǎ*+N (*dǎ diànhuà* 'make a phone call') the verbalizer takes a
noun phrase.

## Implementation notes

* A pattern lists its heads bottom-up, each with the `Harley2017.Projection`s it bears. The
  paper's causative v is Harley's lower Caus, which Harley takes to be productive; the paper's
  (28) calls it lexical.
* One linking hypothesis connects the tests to structure: a form separating *dǎ* from what
  follows it is acceptable iff the two do not share a complex head.
* `Combination.ShareHead` compares complex heads as trees, which suffices because the heads
  compared differ in shape.

## TODO

* §5.4 attributes the idiosyncrasy of *dǎ*+N to a First Phase defined by *dǎ*, but the noun's
  root is not local to *dǎ*. Whether it belongs to idioms below Voice (level zero of the agentive
  heads) or to the noun, which (68) bears on, needs sourced data on *diànhuà*.
* Whether *dǎ-yíng* (22) admits the potential infix, the mark of a resultative in footnote 20,
  needs a sourced judgment.
* The independence claims of §3 beyond `subsetPrinciple_v`, and the light verbs of §6.3.

## References

* [cheng-cheng-2026]
* [harley-2017]
* [sybesma-2021]
* [alexiadou-lohndal-2017]
* [bobaljik-harley-2017]
-/

@[expose] public section

namespace ChengCheng2026

open DistributedMorphology DistributedMorphology.RootCategorization
open Morphology
open Harley2017 (Projection)
open PhraseStructure

/-! ### Three heads -/

/-- The exponents of the heads in (30). -/
inductive Exponent where
  /-- The light verb *dǎ*. -/
  | da
  /-- The causative *gěi*. -/
  | gei
  /-- Voice *bǎ*. -/
  | ba
  deriving DecidableEq, Repr

/-- Exponent names as they appear in the data. -/
def exponentTable : List (String × Exponent) := [("dǎ", .da), ("gěi", .gei), ("bǎ", .ba)]

/-- The context-free items *dǎ* for v, *gěi* for the lower Caus and *bǎ* for Voice; the last two
follow [sybesma-2021]. -/
def vocabulary : RuleSet (VocabularyItem Projection Exponent) :=
  [{.v} ⟷ .da, {.caus₁} ⟷ .gei, {.voice} ⟷ .ba]

theorem subsetPrinciple_v (l r : List (Finset Projection)) :
    subsetPrinciple vocabulary ⟨{.v}, l, r⟩ = some .da := by
  rw [subsetPrinciple_eq_head?_applicable (by decide)]
  simp [RuleSet.applicable, vocabulary]

/-- The exponents of the heads of a pattern, from the highest down. -/
def topDown (bs : List (List Projection)) : List (Option Exponent) :=
  (bs.map fun b ↦ subsetPrinciple vocabulary (Neighborhood.ofBundle b.toFinset)).reverse

/-- The exponents a datum lists, in surface order. -/
def exponents (d : Datum) : List Exponent :=
  (d.features "exponent").filterMap (exponentTable.lookup ·)

theorem exponents_ex_30 :
    ∀ d ∈ [Examples.ex_30a, Examples.ex_30b], exponents d = [.ba, .gei, .da] := by
  decide +kernel

/-- A pattern of v, the lower Caus and Voice realizes the exponents of (30) iff it has a head for
each, Harley's Turkish pattern. -/
theorem topDown_eq_iff {bs : List (List Projection)}
    (hbs : bs.flatten = [.v, .caus₁, .voice]) {d : Datum}
    (hd : d ∈ [Examples.ex_30a, Examples.ex_30b]) :
    topDown bs = (exponents d).map some ↔ bs = Harley2017.turkish := by
  rw [exponents_ex_30 d hd]
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; decide⟩
  have hnil : subsetPrinciple vocabulary (Neighborhood.ofBundle ([] : List Projection).toFinset) =
      none := by decide
  obtain ⟨b₀, b₁, b₂, rfl, h₀, h₁, h₂⟩ : ∃ b₀ b₁ b₂, bs = [b₀, b₁, b₂] ∧
      subsetPrinciple vocabulary (Neighborhood.ofBundle b₀.toFinset) = some .da ∧
      subsetPrinciple vocabulary (Neighborhood.ofBundle b₁.toFinset) = some .gei ∧
      subsetPrinciple vocabulary (Neighborhood.ofBundle b₂.toFinset) = some .ba := by
    have h' := congrArg List.reverse h
    simp only [topDown, List.reverse_reverse, List.map_cons, List.map_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.map_eq_cons_iff,
      List.map_eq_nil_iff] at h'
    obtain ⟨b₀, _, rfl, h₀, b₁, _, rfl, h₁, b₂, _, rfl, h₂, rfl⟩ := h'
    exact ⟨b₀, b₁, b₂, rfl, h₀, h₁, h₂⟩
  rcases b₀ with _ | ⟨x₀, t₀⟩
  · exact absurd (hnil.symm.trans h₀) (by simp)
  rcases b₁ with _ | ⟨x₁, t₁⟩
  · exact absurd (hnil.symm.trans h₁) (by simp)
  rcases b₂ with _ | ⟨x₂, t₂⟩
  · exact absurd (hnil.symm.trans h₂) (by simp)
  have hlen := congrArg List.length hbs
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append,
    List.length_cons, List.length_nil] at hlen
  obtain rfl : t₀ = [] := List.length_eq_zero_iff.1 (by omega)
  obtain rfl : t₁ = [] := List.length_eq_zero_iff.1 (by omega)
  obtain rfl : t₂ = [] := List.length_eq_zero_iff.1 (by omega)
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
    List.nil_append, List.cons.injEq, and_true] at hbs
  obtain ⟨rfl, rfl, rfl⟩ := hbs
  rfl

/-! ### Separability -/

/-- The two kinds of combination with *dǎ*. -/
inductive Combination where
  /-- *dǎ*+R, as in *dǎ-sǎo* 'clean'. -/
  | root
  /-- *dǎ*+N, as in *dǎ diànhuà* 'make a phone call'. -/
  | noun
  deriving DecidableEq, Repr

/-- Combination names as they appear in the data. -/
def combinationTable : List (String × Combination) := [("R", .root), ("N", .noun)]

/-- The lexicon of the *dǎ*+R structure, with trivial words. -/
def lexicon : Lexicon Unit := { x := .v, root := (), head := (), arg := () }

/-- The *dǎ*+N structure (53): the verbalizer over an nP. -/
def nounTree : Tree Cat Unit :=
  .node (.head .v) [.terminal (.head .v) (),
    .node (.head .n) [complexHead { x := .n, root := (), head := (), arg := () }]]

namespace Combination

/-- The structure of a combination; for *dǎ*+R, the adjunction structure (50). -/
def tree : Combination → Tree Cat Unit
  | root => (Configuration.modifier lexicon).tree
  | noun => nounTree

/-- The position of *dǎ*. -/
def daPos : Combination → GornAddress
  | root => (Configuration.modifier lexicon).head
  | noun => ⟨[0]⟩

/-- The position of the root after *dǎ*. -/
def rootPos : Combination → GornAddress
  | root => (Configuration.modifier lexicon).root
  | noun => ⟨[1, 0, 0]⟩

/-- *dǎ* and the root after it lie in one complex head. -/
def ShareHead (c : Combination) : Prop := x0At c.tree c.daPos = x0At c.tree c.rootPos

instance (c : Combination) : Decidable c.ShareHead := inferInstanceAs (Decidable (_ = _))

end Combination

/-- Under either attachment, *dǎ* and the root lie in one complex head. -/
theorem x0At_tree_lexicon (a : Attachment) :
    x0At (a.configuration lexicon).tree (a.configuration lexicon).head =
      x0At (a.configuration lexicon).tree (a.configuration lexicon).root := by
  cases a <;> rfl

/-- The combination a datum tests, and whether its form separates *dǎ* from what follows it. -/
def test? (d : Datum) : Option (Combination × Bool) := do
  let c ← d.parse? "combination" combinationTable
  let s ← d.parse? "separated" [("yes", true), ("no", false)]
  pure (c, s)

theorem length_filterMap_test? : (Examples.all.filterMap test?).length = 12 := by decide +kernel

/-- A test form is acceptable iff it keeps *dǎ* with what follows it or the two lie in different
complex heads ((44), (46), (48), (49)). -/
theorem diagnostics_iff : ∀ d ∈ Examples.all, ∀ p ∈ test? d,
    d.judgment = .acceptable ↔ (p.2 = true → ¬ p.1.ShareHead) := by
  decide +kernel

/-! ### Locality of the root -/

/-- *dǎ* is local to the root after it iff the combination is *dǎ*+R. -/
theorem mayCondition'_rootPos_daPos_iff (c : Combination) :
    MayCondition' c.tree c.rootPos c.daPos ↔ c = .root := by
  cases c <;> decide

end ChengCheng2026
