module

public import Linglib.Morphology.Exponence.Select
public import Linglib.Morphology.Paradigm.Linkage
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Prod.Lex.Basic

/-!
# The PFM1 paradigm function

This file defines the Paradigm Function Morphology engine of Stump's book in Bonami and Stump's
streamlined form, PFM1. A paradigm function applies basic stem choice to a cell `⟨L, σ⟩` and then
an ordered cascade of rule blocks. A rule applies at the cell when `L` is in its class and its
property set is contained in `σ`, and in each block the narrowest applicable rule wins, by
Pāṇinian narrowness. The Identity Function Default and the Function Composition Default are the
least narrow rules of their blocks, and their behaviour as defaults is derived from that.

## Main definitions

* `PFM.Action`, `PFM.Rule`, `PFM.Rule.narrowness`: rule payloads, the realization rule shared by
  rules of exponence, referral and basic stem choice, and its narrowness key.
* `PFM.Rule.elsewhere`, `PFM.identityDefault`: the least narrow rule with a given payload, and
  the Identity Function Default.
* `PFM.Block.eval`, `PFM.evalBlocks`, `PFM.paradigmFunction`: a block, the block cascade and the
  paradigm function evaluated at a cell.
* `PFM.functionCompositionDefault`, `PFM.Block.portmanteau`: portmanteau blocks, whose least
  narrow rule is the Function Composition Default.

## Main results

* `PFM.Rule.narrowness_le_iff`, `PFM.Rule.applySet_mono`: the two clauses of narrowness, and
  applicability-set inclusion between rules of one class.
* `PFM.selectMinimal_append_elsewhere`, `PFM.selectMinimal_isSome_of_identityDefault_mem`: a
  least narrow rule is selected only where no other rule applies, and a block with the IFD always
  selects.
* `PFM.Block.eval_of_referral`: a rule of referral re-consults its block at the retargeted cell.
* `PFM.Block.eval_portmanteau_of_applicable_eq_nil`,
  `PFM.Block.eval_portmanteau_of_applicable_ne_nil`: the Function Composition Default, and its
  override by a portmanteau rule.
* `Morphology.Linkage.realized_eq_paradigmFunction`: under the default rule of paradigm linkage,
  the realization of a content cell is the paradigm function.

## Implementation notes

Blocks are evaluated at the cell rather than at a ⟨stem, property set⟩ pair, so the lexeme a stem
is covertly indexed with persists through every block by construction. The chapter's values
`⟨R, σ⟩` carry the cell's own property set, so evaluation returns the form alone. Whole-word
syncretism, a clause of the paradigm function such as (5), is a property mapping of `Linkage`
rather than a rule of referral. Morphophonological metageneralizations, conditions on a stem's
phonological shape, and overabundance are outside the engine. Numbered examples refer to Bonami
and Stump's chapter.

## TODO

Stump's later rule conflation, which replaces a portmanteau block by a single rule combining two
rules, is not modeled.

## References

* [bonami-stump-2016]
* [kiparsky-1973]
* [spencer-2013]
* [stump-2001]
* [stump-2016]
* [stump-2020]
* [stump-2022]
-/

@[expose] public section

namespace Morphology.PFM

open Morphology Morphology.Exponence

variable {L Z P F : Type*}

/-- A rule of *exponence* carries a form operation, which may consult the cell (its lexeme, with
which a stem is covertly indexed, and, as [stump-2020] allows, its property set); a rule of
*referral* carries a retargeting of property sets, at which its block is re-consulted. -/
inductive Action (L Z P : Type*)
  | expo (f : L × P → Z → Z)
  | referral (retarget : P → P)

/-- The rule of exponence applying `f` at every cell. -/
def Action.const (f : Z → Z) : Action L Z P := .expo fun _ ↦ f

/-- A realization rule `n, X_C, τ → f(X)` of [bonami-stump-2016] has a lexeme class `C`, the
property set `τ` it realizes, and a payload: an `Action` for rules of exponence and referral, a
stem for rules of basic stem choice. -/
structure Rule (L P F : Type*) where
  /-- The lexeme class the rule applies in. -/
  klass : Finset L
  /-- The property set the rule realizes. -/
  props : P
  /-- The action or stem the rule supplies. -/
  payload : F

section Narrowness
variable [PartialOrder P]

/-- Narrowness as a key: `r` is at least as narrow as `s` when `r`'s class is properly smaller, or
the classes coincide and `r` realizes a superset of `s`'s properties. -/
def Rule.narrowness (r : Rule L P F) : Finset L ×ₗ Pᵒᵈ := toLex (r.klass, OrderDual.toDual r.props)

/-- Narrowness (15): a properly smaller class, or the same class and a larger property set. -/
theorem Rule.narrowness_le_iff {r s : Rule L P F} :
    r.narrowness ≤ s.narrowness ↔ r.klass ⊂ s.klass ∨ r.klass = s.klass ∧ s.props ≤ r.props :=
  Prod.Lex.toLex_le_toLex

instance : Exponence.Rule (Rule L P F) (L × P) F where
  exponent := Rule.payload
  Applies r c := c.1 ∈ r.klass ∧ r.props ≤ c.2

@[simp] theorem Rule.applies_iff {r : Rule L P F} {c : L × P} :
    Applies r c ↔ c.1 ∈ r.klass ∧ r.props ≤ c.2 :=
  Iff.rfl

/-- Between rules of one class, a narrower rule applies in fewer cells. Across classes a smaller
class outranks a larger one whatever the property sets, so narrowness is strictly finer than
applicability-set inclusion. -/
theorem Rule.applySet_mono {r s : Rule L P F} (hk : r.klass = s.klass)
    (h : r.narrowness ≤ s.narrowness) : applySet r ⊆ applySet s := by
  rcases Rule.narrowness_le_iff.1 h with hlt | ⟨_, hp⟩
  · exact absurd hk hlt.ne
  · exact fun c hc ↦ ⟨hk ▸ hc.1, hp.trans hc.2⟩

variable [Fintype L] [OrderBot P]

/-- The least narrow rule with payload `f`, `n, X_U, {} → f(X)`, applies in the class of all
lexemes and realizes the empty property set. -/
def Rule.elsewhere (f : F) : Rule L P F := ⟨Finset.univ, ⊥, f⟩

@[simp] theorem Rule.narrowness_elsewhere (f : F) :
    (Rule.elsewhere f : Rule L P F).narrowness = ⊤ :=
  rfl

theorem Rule.elsewhere_applies (f : F) (c : L × P) : Applies (Rule.elsewhere f : Rule L P F) c :=
  ⟨Finset.mem_univ _, bot_le⟩

/-- The *Identity Function Default* (16) leaves the stem unchanged. -/
def identityDefault : Rule L P (Action L Z P) := .elsewhere (.const id)

end Narrowness

/-! ### Blocks and the paradigm function -/

/-- A *rule block* is a list of rules of exponence and referral in paradigmatic opposition. -/
abbrev Block (L Z P : Type*) := RuleSet (Rule L P (Action L Z P))

/-- The rules of exponence of a block, among which its rules of referral re-select. -/
def Block.expoFragment (b : Block L Z P) : Block L Z P :=
  b.filter (·.payload matches .expo _)

theorem Block.exists_eq_expo_of_mem_expoFragment {b : Block L Z P} {r : Rule L P (Action L Z P)}
    (h : r ∈ b.expoFragment) : ∃ f, r.payload = .expo f := by
  obtain ⟨-, h⟩ := List.mem_filter.mp h
  cases hr : r.payload with
  | expo f => exact ⟨f, rfl⟩
  | referral g => simp [hr] at h

section Selection
variable [PartialOrder P] [DecidableEq L] [DecidableLE P] [DecidableLT P]

instance : DecidableRel (Applies : Rule L P F → L × P → Prop) :=
  fun r c ↦ inferInstanceAs (Decidable (c.1 ∈ r.klass ∧ r.props ≤ c.2))

instance : DecidableRel ((· < ·) : Finset L ×ₗ Pᵒᵈ → Finset L ×ₗ Pᵒᵈ → Prop) :=
  Prod.Lex.decidable _ _

/-- A least narrow rule appended to a rule set is selected only where none of its rules applies. -/
theorem selectMinimal_append_elsewhere [Fintype L] [OrderBot P] (v : RuleSet (Rule L P F))
    (f : F) (c : L × P) : (v ++ [Rule.elsewhere f]).selectMinimal Rule.narrowness c =
      (v.selectMinimal Rule.narrowness c).or (some (Rule.elsewhere f)) :=
  RuleSet.selectMinimal_append_singleton (Rule.elsewhere_applies f c) fun _ _ ↦ le_top

/-- A block containing the IFD always selects a rule, the totality of Nar (14). -/
theorem selectMinimal_isSome_of_identityDefault_mem [Fintype L] [OrderBot P]
    {v : RuleSet (Rule L P (Action L Z P))} (h : identityDefault ∈ v) (c : L × P) :
    (v.selectMinimal Rule.narrowness c).isSome :=
  RuleSet.selectMinimal_isSome_iff.mpr ⟨_, h, Rule.elsewhere_applies _ c⟩

/-- `b.eval c w` is Nar (14), `[n : ⟨w, σ⟩]`: the narrowest rule of `b` applicable at the cell `c`
acts on the form `w`. A rule of referral re-selects among the rules of exponence at the
retargeted cell, and `w` is unchanged where no rule applies. -/
def Block.eval (b : Block L Z P) (c : L × P) (w : Z) : Z :=
  match b.selectMinimal Rule.narrowness c with
  | some ⟨_, _, .expo f⟩ => f c w
  | some ⟨_, _, .referral g⟩ =>
    match b.expoFragment.selectMinimal Rule.narrowness (c.1, g c.2) with
    | some ⟨_, _, .expo f⟩ => f (c.1, g c.2) w
    | _ => w
  | none => w

theorem Block.eval_of_expo {b : Block L Z P} {c : L × P} {r : Rule L P (Action L Z P)}
    {f : L × P → Z → Z} (hr : b.selectMinimal Rule.narrowness c = some r)
    (hf : r.payload = .expo f) (w : Z) : b.eval c w = f c w := by
  obtain ⟨k, p, a⟩ := r
  obtain rfl : a = _ := hf
  simp [Block.eval, hr]

/-- A selected rule of referral evaluates its block's rules of exponence at the retargeted cell,
as in the Sanskrit vocative (17). -/
theorem Block.eval_of_referral {b : Block L Z P} {c : L × P} {r : Rule L P (Action L Z P)}
    {g : P → P} (hr : b.selectMinimal Rule.narrowness c = some r)
    (hg : r.payload = .referral g) (w : Z) : b.eval c w = b.expoFragment.eval (c.1, g c.2) w := by
  obtain ⟨k, p, a⟩ := r
  obtain rfl : a = _ := hg
  rcases hs : b.expoFragment.selectMinimal Rule.narrowness (c.1, g c.2) with - | s
  · simp [Block.eval, hr, hs]
  · obtain ⟨k', p', a'⟩ := s
    obtain ⟨f, rfl⟩ := Block.exists_eq_expo_of_mem_expoFragment (RuleSet.selectMinimal_mem hs)
    simp [Block.eval, hr, hs]

/-- `evalBlocks bs c w` threads the form `w` through the blocks `bs`, listed inner-first, at the
cell `c`. -/
def evalBlocks (bs : List (Block L Z P)) (c : L × P) (w : Z) : Z :=
  bs.foldl (fun w b ↦ b.eval c w) w

@[simp] theorem evalBlocks_nil (c : L × P) (w : Z) : evalBlocks [] c w = w :=
  rfl

@[simp] theorem evalBlocks_cons (b : Block L Z P) (bs : List (Block L Z P)) (c : L × P) (w : Z) :
    evalBlocks (b :: bs) c w = evalBlocks bs c (b.eval c w) :=
  rfl

/-- The *paradigm function* (13) applies basic stem choice and then the blocks `bs`, listed
inner-first, so that `paradigmFunction stem [i, ii, iii]` realizes `[iii : [ii : [i : Stem]]]`. -/
def paradigmFunction (stem : L × P → Z) (bs : List (Block L Z P)) (c : L × P) : Z :=
  evalBlocks bs c (stem c)

/-! ### Portmanteau blocks -/

section Portmanteau
variable [Fintype L] [OrderBot P] {bmn bm bn : Block L Z P} {c : L × P}

/-- The *Function Composition Default* (24) of a portmanteau block `[m, n]` is the least narrow
rule realizing `[m : [n : ⟨X, σ⟩]]`. -/
def functionCompositionDefault (bm bn : Block L Z P) : Rule L P (Action L Z P) :=
  .elsewhere (.expo fun c w ↦ bm.eval c (bn.eval c w))

/-- A *portmanteau block* `[m, n]` of [stump-2001] has rules `bmn` in paradigmatic opposition to
blocks `m` and `n` together, and the Function Composition Default. -/
def Block.portmanteau (bmn bm bn : Block L Z P) : Block L Z P :=
  bmn ++ [functionCompositionDefault bm bn]

/-- Where no portmanteau rule applies, block `[m, n]` is the composition of blocks `m` and `n`,
the Function Composition Default (24). -/
theorem Block.eval_portmanteau_of_applicable_eq_nil (h : bmn.applicable c = []) (w : Z) :
    (bmn.portmanteau bm bn).eval c w = bm.eval c (bn.eval c w) := by
  have hs : (bmn.portmanteau bm bn).selectMinimal Rule.narrowness c =
      some (functionCompositionDefault bm bn) := by
    rw [Block.portmanteau, functionCompositionDefault, selectMinimal_append_elsewhere,
      RuleSet.selectMinimal_eq_none_iff.mpr h, Option.none_or]
  exact Block.eval_of_expo hs rfl w

/-- Where a portmanteau rule of exponence applies, it overrides blocks `m` and `n`. -/
theorem Block.eval_portmanteau_of_applicable_ne_nil
    (hbmn : ∀ r ∈ bmn, ∃ f, r.payload = .expo f) (h : bmn.applicable c ≠ []) (w : Z) :
    (bmn.portmanteau bm bn).eval c w = bmn.eval c w := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp <|
    (RuleSet.selectMinimal_isSome_iff (key := Rule.narrowness)).mpr <|
    (List.exists_mem_of_ne_nil _ h).imp fun _ ↦ RuleSet.mem_applicable.mp
  obtain ⟨f, hf⟩ := hbmn r (RuleSet.selectMinimal_mem hr)
  have hs : (bmn.portmanteau bm bn).selectMinimal Rule.narrowness c = some r := by
    rw [Block.portmanteau, functionCompositionDefault, selectMinimal_append_elsewhere, hr,
      Option.some_or]
  rw [Block.eval_of_expo hr hf, Block.eval_of_expo hs hf]

end Portmanteau

/-- Under the default rule of paradigm linkage (27), with property-preserving property mapping,
form cells realized by the block cascade at their stem's L-index, and the convention (11) that a
basic stem's L-index is its lexeme, a content cell realizes as the paradigm function. -/
theorem _root_.Morphology.Linkage.realized_eq_paradigmFunction [DecidableEq Z]
    (ℓ : Linkage L Z P P) (lindex : Z → L) (stem : L × P → Z) (bs : List (Block L Z P))
    (h : ℓ.IsPropertyPreserving id) (hstem : ∀ l σ, ℓ.realize l σ = {stem (l, σ)})
    (hl : ∀ c, lindex (stem c) = c.1) (l : L) (σ : P) :
    ℓ.realized (fun z τ ↦ evalBlocks bs (lindex z, τ) z) l σ
      = {(paradigmFunction stem bs (l, σ), σ)} := by
  simp [Linkage.realized, h l σ, hstem, hl, paradigmFunction]

end Selection

end Morphology.PFM
