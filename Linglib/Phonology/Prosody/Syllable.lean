module

public import Mathlib.Data.PNat.Defs
public import Linglib.Phonology.Prosody.Mora
public import Linglib.Core.Data.RoseTree.Basic

/-!
# Syllables

The syllable σ is the level above the mora in the prosodic hierarchy, a headed moraic constituent
(Hayes 1989; Hyman 1985). A non-moraic `onset` sits over a moraic spine whose head is the nucleus,
the sonority peak (Clements 1990). The nucleus mora is mandatory and initial, so a σ has at least
one mora, and `tail` carries any further nuclear morae (long vowels) and a moraic coda. Weight is
mora-based, so the moraic structure is the carrier; Selkirk's (1982) rival onset-rime theory is a
re-representation (`toOnsetRime`) that agrees with it on weight. The file also defines the
prosodic constituents, the prosodic tree, and the Layeredness relation by which each constituent
licenses its daughters.

## Main definitions

* `Syllable` — a headed moraic σ: `onset`, a nucleus `head` mora, and a `tail` of morae.
* `Syllable.morae` / `nucleusMora` / `nucleusSegments` / `weight` / `moraCount` /
  `pnatMoraCount`.
* `Syllable.IsHeavy` / `IsLight` — the weight inventory (sonority/SSP well-formedness is
  a syllabification follow-up).
* `Syllable.ofCV` / `ofVowel` / `ofLongVowel` / `mk'` — smart constructors (a non-empty
  nucleus is required; a long vowel is two morae on one melody).
* `Syllable.yield` / `toOnsetRime` — re-representations; `toOnsetRime_weight` is the
  weight-correspondence between the moraic and onset-rime theories.
* `Syllable.Weight` — `Nat` (the mora count), with `.light`/`.heavy`/`.superheavy`.
* `Level`, `Constituent.level` — the levels of the prosodic hierarchy, linearly ordered
  σ < f < ω < φ < ι, and the level of a node.
* `Constituent`, `Tree` — the prosodic constituents and the prosodic tree over them.
* `Constituent.Licenses` — Layeredness: a node dominates only its own level or below.

## References

* [hayes-1989]
* [hyman-1985]
* [clements-1990]
* [selkirk-1980]
* [selkirk-1982]
* [selkirk-1996]
* [nespor-vogel-1986]
* [mccarthy-prince-1993]
* [dolatian-2020]
* [ito-mester-2003]
-/

@[expose] public section

namespace Prosody

open Phonology (Segment)

/-! ### Syllables -/

/-- A syllable σ is a headed moraic constituent ([hayes-1989]) with a non-moraic `onset`, a
    nucleus `head` mora (the sonority peak; mandatory, so σ has at least one mora and the head is
    initial by construction), and a `tail` of further morae (long-vowel morae and a moraic
    coda). -/
structure Syllable where
  /-- The non-moraic onset melody. -/
  onset : List Segment
  /-- The nucleus mora — the sonority peak; mandatory, so σ has ≥ 1 mora. -/
  head  : Mora
  /-- The further morae are long-vowel morae and a moraic coda. -/
  tail  : List Mora
  deriving DecidableEq

namespace Syllable

/-- Syllable weight is just the mora count — there is no separate weight type.
    `.light` (1μ), `.heavy` (2μ), `.superheavy` (3μ) name the common values for
    readable weight profiles in metrical and accentual computations. -/
abbrev Weight := Nat

namespace Weight
abbrev light : Weight := 1
abbrev heavy : Weight := 2
abbrev superheavy : Weight := 3
end Weight

/-- The moraic spine, nucleus (peak) first. -/
def morae (σ : Syllable) : List Mora := σ.head :: σ.tail

/-- The nucleus — the head mora (the sonority peak). -/
abbrev nucleusMora (σ : Syllable) : Mora := σ.head

/-- The nucleus segment(s). -/
def nucleusSegments (σ : Syllable) : List Segment := σ.head.dominates

/-- The number of morae — the syllable's weight. -/
def moraCount (σ : Syllable) : Nat := σ.morae.length

/-- The syllable's weight (= its mora count). -/
abbrev weight (σ : Syllable) : Weight := σ.moraCount

/-- A syllable has at least its nucleus mora. -/
theorem moraCount_pos (σ : Syllable) : 0 < σ.moraCount := Nat.succ_pos _

/-- The mora count as a positive natural is the weight a `Tone.Registered` word reads. -/
def pnatMoraCount (σ : Syllable) : ℕ+ := ⟨σ.moraCount, σ.moraCount_pos⟩

/-- A syllable is heavy when it has at least two morae. -/
def IsHeavy (σ : Syllable) : Prop := Weight.heavy ≤ σ.weight
/-- A syllable is light when it has exactly one mora. -/
def IsLight (σ : Syllable) : Prop := σ.weight = Weight.light

instance (σ : Syllable) : Decidable σ.IsHeavy := by unfold IsHeavy; infer_instance
instance (σ : Syllable) : Decidable σ.IsLight := by unfold IsLight; infer_instance

/-- Build a syllable from an explicit nucleus mora (+ optional further/coda morae). -/
def mk' (onset : List Segment) (nucleus : Mora) (coda : List Mora := []) : Syllable :=
  ⟨onset, nucleus, coda⟩

/-- Build a syllable from an onset and a non-empty mora spine (nucleus = first mora). -/
def ofMorae (onset : List Segment) (ms : List Mora) (h : ms ≠ [] := by simp) : Syllable :=
  ⟨onset, ms.head h, ms.tail⟩

/-- Build a syllable from a segmental onset–nucleus–coda string. Each nucleus segment
    projects a mora (the first is the nucleus head). Under Weight by Position
    ([hayes-1989]) the first coda segment projects its own mora and any further coda
    segments ride it, so the syllable stays at most bimoraic; without it the coda rides
    the last nucleus mora. A non-empty nucleus is required. -/
def ofCV (onset nucleus coda : List Segment) (wbp : Bool := true)
    (hn : nucleus ≠ [] := by simp) : Syllable :=
  match nucleus, hn with
  | [], h => (h rfl).elim
  | n₀ :: ns, _ =>
    match wbp, coda with
    | true, c :: cs => ⟨onset, Mora.of n₀, ns.map Mora.of ++ [(Mora.of c).attach cs]⟩
    | _, _ =>
      match (ns.map Mora.of).reverse with
      | last :: rest => ⟨onset, Mora.of n₀, rest.reverse ++ [last.attach coda]⟩
      | []           => ⟨onset, (Mora.of n₀).attach coda, []⟩

/-- The open syllable of an onset and a short vowel has one mora. -/
def ofVowel (onset : List Segment) (v : Segment) : Syllable := ⟨onset, .of v, []⟩

/-- The open syllable of an onset and a long vowel has two morae dominating the same melody
([hayes-1989]). -/
def ofLongVowel (onset : List Segment) (v : Segment) : Syllable := ⟨onset, .of v, [.of v]⟩

@[simp] theorem moraCount_ofVowel (onset : List Segment) (v : Segment) :
    (ofVowel onset v).moraCount = 1 := rfl

@[simp] theorem moraCount_ofLongVowel (onset : List Segment) (v : Segment) :
    (ofLongVowel onset v).moraCount = 2 := rfl

/-- The segment string, or yield, of a syllable is its onset followed by the moraic melody. -/
def yield (σ : Syllable) : List Segment := σ.onset ++ σ.morae.flatMap (·.dominates)

end Syllable

/-! ### Onset-rime re-representation -/

/-- The onset-rime structure of [selkirk-1982] is a rival theory of σ structure, an onset over a
    rime, here a re-representation of the canonical moraic `Syllable`. -/
structure OnsetRime where
  /-- The non-moraic onset melody. -/
  onset : List Segment
  /-- The rime is the moraic spine. -/
  rime  : List Mora
  deriving DecidableEq

/-- Passing from σ to onset-rime structure, the rime is the moraic spine ([selkirk-1982]). -/
def Syllable.toOnsetRime (σ : Syllable) : OnsetRime := ⟨σ.onset, σ.morae⟩

/-- By **weight correspondence**, the onset-rime rime's mora count equals σ's weight, so the
    moraic and onset-rime theories agree on weight ([selkirk-1982]; [hayes-1989]). -/
theorem Syllable.toOnsetRime_weight (σ : Syllable) :
    σ.toOnsetRime.rime.length = σ.moraCount := rfl

/-! ### Yield -/

/-- A **yield** is the terminal σ-weight string of a prosodic structure, the unparsed input or
    the leaves of a prosodic `Tree`. Unlike the prosodic word ω (an `IsWord` tree), which is a
    headed constituent, a yield is just the weight profile, with no head and no constituency. -/
abbrev Yield := List Syllable.Weight

namespace Yield

/-- The weight profile of fully-moraified syllables — the σ → yield bridge. -/
def ofSyllables (σs : List Syllable) : Yield := σs.map Syllable.weight

/-- Total mora count (each weight *is* a mora count). -/
def moraCount (y : Yield) : Nat := y.sum

/-- The minimal-word size constraint of [mccarthy-prince-1993] asks for at least `minMorae`
    morae (default 2, the moraic-trochee minimum), the moraic size floor on a prosodic word.
    Whether an ω must structurally contain a foot is a separate, non-presupposed matter
    (footless languages have ω directly over σ, [dolatian-2020]). -/
abbrev satisfiesMinWord (y : Yield) (minMorae : Nat := 2) : Prop := minMorae ≤ y.moraCount

end Yield

/-! ### The prosodic-tree carrier

The recursive prosodic constituent ([ito-mester-2003]): the Core ordered rose tree
`RoseTree` labeled by prosodic-level `Constituent`s — the **violable OT candidate
carrier** for ω/φ/… structures, including the ill-formed ones (a footless ω, a stray under
φ) that `IsWord` rules out. Its OT constraints are
`OptimalityTheory.Constraint Tree` values, defined alongside `IsWord`. Homed here because
`Constituent.weight`/`.syl` need `Syllable.Weight`; it inherits `DecidableEq`/`map` from
`RoseTree`. -/

/-- The levels of the prosodic hierarchy ([selkirk-1980]; [nespor-vogel-1986]), linearly ordered
σ < f < ω < φ < ι. -/
inductive Level
  | syl | ft | om | ph | iota
  deriving DecidableEq, Repr

namespace Level

/-- The rank of a level, σ lowest. -/
def toNat : Level → ℕ
  | syl => 0 | ft => 1 | om => 2 | ph => 3 | iota => 4

theorem toNat_injective : Function.Injective toNat := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

instance : LinearOrder Level := LinearOrder.lift' toNat toNat_injective

end Level

/-- In a prosodic node the **level is the constructor**. A σ carries its mora `weight` and
    `isHead`, and every non-root level carries `isHead` (whether it heads its parent).
    Constructor defaults match the former smart constructors, so node literals are unchanged;
    illegal nodes (a weight on a foot, a head on the ι root) are unrepresentable. -/
inductive Constituent
  /-- A syllable of the given `weight`, optionally the head of its foot. -/
  | syl (weight : Syllable.Weight := 0) (isHead : Bool := false)
  /-- A foot, optionally the head foot of its word. -/
  | ft (isHead : Bool := false)
  /-- A prosodic word ω, optionally the head word of its phrase. -/
  | om (isHead : Bool := false)
  /-- A phonological phrase φ, optionally the head phrase of its
  intonational phrase. -/
  | ph (isHead : Bool := false)
  /-- An intonational phrase ι — the root of the utterance-level
  hierarchy, headless. -/
  | iota
  deriving DecidableEq, Repr

namespace Constituent

/-- Whether a node heads its parent (a σ heads its foot, a foot heads its word, an ω its phrase,
    a φ its intonational phrase); `false` for the ι root. -/
def isHead : Constituent → Bool
  | .syl _ h => h | .ft h => h | .om h => h | .ph h => h | .iota => false

/-- The mora weight of a σ node; `none` for non-σ nodes. -/
def weight? : Constituent → Option Syllable.Weight
  | .syl w _ => some w | _ => none

/-- The level of a node, the constructor without its weight and head mark. -/
def level : Constituent → Level
  | .syl .. => .syl | .ft _ => .ft | .om _ => .om | .ph _ => .ph | .iota => .iota

@[simp] theorem level_syl (w : Syllable.Weight) (h : Bool) : (syl w h).level = .syl := rfl
@[simp] theorem level_ft (h : Bool) : (ft h).level = .ft := rfl
@[simp] theorem level_om (h : Bool) : (om h).level = .om := rfl
@[simp] theorem level_ph (h : Bool) : (ph h).level = .ph := rfl
@[simp] theorem level_iota : iota.level = .iota := rfl

/-- Under **Layeredness** ([selkirk-1996]) a node dominates only nodes of its own level or below:
    σ is the terminal, a foot a non-empty string of σs (foot recursion, contested, is excluded
    with it), and ω, φ and ι dominate anything at or below their level. Recursion at ω, φ and ι
    and level skipping, a σ or a foot directly under a φ, are thereby admitted: Nonrecursivity
    and Exhaustivity are the violable constraints `noRec` and `parseInto`. `Licenses a ks` says
    that `a` may dominate daughters labelled `ks`. -/
def Licenses : Constituent → List Constituent → Prop
  | .syl .., ks => ks = []
  | .ft _, ks => ks ≠ [] ∧ ∀ k ∈ ks, k.level = .syl
  | a, ks => ∀ k ∈ ks, k.level ≤ a.level

instance : ∀ (a : Constituent) (ks : List Constituent), Decidable (Licenses a ks)
  | .syl .., ks => inferInstanceAs (Decidable (ks = []))
  | .ft _, ks => inferInstanceAs (Decidable (ks ≠ [] ∧ ∀ k ∈ ks, k.level = .syl))
  | .om _, ks => inferInstanceAs (Decidable (∀ k ∈ ks, k.level ≤ (Constituent.om _).level))
  | .ph _, ks => inferInstanceAs (Decidable (∀ k ∈ ks, k.level ≤ (Constituent.ph _).level))
  | .iota, ks => inferInstanceAs (Decidable (∀ k ∈ ks, k.level ≤ Constituent.iota.level))

end Constituent

/-- A prosodic tree is an ordered rose tree labelled by `Constituent`s. Ordered children give
    No-Tangling by construction. -/
abbrev Tree := RoseTree Constituent

/-- A σ-leaf is the metrical terminal, a syllable of weight `w` with head mark `h`. -/
abbrev Tree.σ (w : Syllable.Weight := 0) (h : Bool := false) : Tree := .node (.syl w h) []

/-- A foot node over `cs`, optionally the head foot of its word. -/
abbrev Tree.ft (h : Bool) (cs : List Tree) : Tree := .node (.ft h) cs

/-- A prosodic-word (ω) node over `cs`. -/
abbrev Tree.om (cs : List Tree) : Tree := .node .om cs

/-- A phonological-phrase (φ) node over `cs`. -/
abbrev Tree.ph (cs : List Tree) : Tree := .node .ph cs

/-- **Leaf/branch induction on a prosodic tree.** A σ-leaf is a base case; every other node — a
    foot, word, phrase, or degenerate/ill-formed node — is a branch, carrying the induction
    hypothesis over its children and the fact that it is *not* a σ-leaf. This is what lets proofs
    reduce the σ-leaf `if` the reader equations carry (via `ite_eq_left ⟨ha, rfl⟩` or
    `ite_eq_right hne`) instead of `split`ting it. -/
@[elab_as_elim]
theorem Tree.recLeafBranch {motive : Tree → Prop}
    (leaf : ∀ a, a.level = .syl → motive (.node a []))
    (branch : ∀ a cs, ¬(a.level = .syl ∧ cs = []) → (∀ c ∈ cs, motive c) → motive (.node a cs))
    (t : Tree) : motive t := by
  induction t using RoseTree.rec' with
  | node a cs ih =>
    by_cases h : a.level = .syl ∧ cs = []
    · obtain ⟨ha, rfl⟩ := h; exact leaf a ha
    · exact branch a cs h ih

end Prosody
