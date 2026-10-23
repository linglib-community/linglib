module

public import Linglib.Morphology.Exponence.Select
public import Linglib.Morphology.Paradigm.Linkage
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Prod.Lex.Basic

/-!
# The PFM1 paradigm function

This file defines the standard Paradigm Function Morphology engine, Bonami and Stump's
streamlined PFM1 after Stump's original engine. A paradigm function is a set of **realization
rules** organized into ordered **blocks**. A rule `⟨klass, props, payload⟩` applies to a cell
`⟨L, σ⟩` when the lexeme `L` belongs to `klass` and the property set `props` is contained in
`σ`, and among the applicable rules of a block the narrowest wins, by Kiparsky's Elsewhere
Condition (PFM's Pāṇinian Determinism). One payload-polymorphic carrier `Rule L P F` serves all
three rule types: rules of exponence and referral take `F := Action Z P`, rules of basic stem
choice take `F := Z`, and the same narrowness order arbitrates stem-choice conflicts.

Narrowness (`Rule`'s `≤`) has the two clauses of Stump's original engine: same class with a
larger property set, or a properly smaller class. It is intensional. For same-class rules it
collapses to applicability-set inclusion (`applySet_mono`), but across classes a smaller class
outranks a larger one whatever the property sets, so the order is strictly finer than the
extensional domain-subset order of `Exponence/Basic.lean`, which Stump's later books adopt; his
encyclopedia overview of PFM likewise glosses "narrowest" as the smaller domain of application.

The **Identity Function Default**, a rule in every block leaving the stem unchanged, is assumed
as a universal principle in PFM; here it is a definition (`identityDefault`) whose consequences
are theorems (it is `≤`-maximal, and a block containing it always selects). As in Bonami and
Stump's presentation, two implicative devices are kept distinct. A **rule of referral**
(`Action.referral`) models block-confined syncretism and competes inside its block; whole-word
syncretism lives a layer up, as a many-to-one property mapping in `Linkage.pm`
(`Linkage.realized_eq_of_corr_eq`), where Stump's overview relocates it, and
paradigm-function-level override clauses are not modeled. Overabundance (one cell, several
forms) is out of scope, since the realized paradigm is function-valued. Morphophonological
metageneralizations (the `-a`-loss and umlaut rules of the Icelandic fragment) are phonological
substance and live in `Phonology/`; here stem alternants like *köll* enter as data-level stem
values, not string operations.

Because payloads are functions, `Exponence.RuleSet.Coherent` and `Realizes` over `Action Z P` are
`funext` propositions rather than decidable checks; a study decides realized values, not
payload equality.

## Main definitions

* `Action`, `Rule`: the payload (exponence or referral) and the payload-polymorphic
  realization rule, with its `Exponence.Rule` and two-clause narrowness `Preorder` instances.
* `identityDefault`: the Identity Function Default.
* `evalBlock`, `paradigmFunction`: narrowest-rule block evaluation and the block cascade.
  Basic stem choice over rules of stem choice is `Exponence.RuleSet.realizeMinimalD`,
  narrowest-rule realization with a per-lexeme fallback.
* `evalPortmanteau`, `functionCompositionDefault`: portmanteau blocks, and the Function
  Composition Default as a derived `≤`-maximal rule.

## Main results

* `Rule.applies_iff`, `Rule.le_iff`, `Rule.applySet_mono`: applicability and narrowness.
* `le_identityDefault`, `selectMinimal_isSome_of_mem_identityDefault`: the IFD is `≤`-maximal,
  and a block containing it always selects.
* `evalPortmanteau_eq_comp_of_not_applies`: the Function Composition Default.
* `selectMinimal_append_maximal`: appending a maximal always-applicable rule is
  elsewhere-only, the mechanism behind `identityDefault` and the FCD.
* `evalPortmanteau_eq_functionCompositionDefault`: the stipulated portmanteau evaluation
  equals its appended-block form.
* `Linkage.realized_eq_paradigmFunction`, `Linkage.ofFun_realized_eq_paradigmFunction`,
  `Linkage.ofRules_realized_eq_paradigmFunction`: the PFM2 realization of a linkage's block
  cascade is this paradigm function, with the stem choice of rules of paradigm linkage as its
  basic stem choice.

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

/-- The payload of a realization rule is an action. A rule of **exponence**
carries a form operation `f : P → Z → Z` that may consult the realized property
set, and a rule of **referral** carries a property-set retargeting `P → P` whose
block is re-consulted at the retargeted cell. The property argument makes the form
operation σ-sensitive, as [stump-2020]'s rule format allows (his conditional
affixation operator for ambifixal classes consults σ), and lets the Function
Composition Default carry a rule whose action is "evaluate two blocks at the
current cell". -/
inductive Action (Z P : Type*)
  | expo (f : P → Z → Z)
  | referral (retarget : P → P)

/-- `Action.const f` is the property-insensitive rule of exponence that applies
the form operation `f : Z → Z` regardless of the property set. It is the special
case of `Action.expo` before [stump-2020]'s σ-sensitive rule format, and the
shape of every exponent in [bonami-stump-2016]'s worked fragments. -/
def Action.const (f : Z → Z) : Action Z P := .expo (fun _ => f)

/-- A realization rule has [bonami-stump-2016]'s format `⟨klass, props, payload⟩`
(the chapter's `n, X_C, τ → f(X)`) and is payload-polymorphic à la
`Containment.SpanRule`, so rules of exponence and referral instantiate
`F := Action Z P` and rules of basic stem choice `F := Z`. `klass` is the lexeme
class `C`, and `props` is the realized property set `τ`. -/
structure Rule (L P F : Type*) where
  /-- `klass` is the lexeme class the rule applies in. -/
  klass : Finset L
  /-- `props` is the property set the rule realizes. -/
  props : P
  /-- `payload` is the form operation (exponence or referral) or the stem the rule
  supplies. -/
  payload : F

section Narrowness
variable [PartialOrder P]

/-- Two-clause Pāṇinian narrowness ([stump-2001]) as a key: `r` is at least as narrow as `s` when
`r`'s class is properly smaller, or they share a class and `s` realizes a subset of `r`'s
properties. Narrowness is intensional, strictly finer than applicability-set inclusion (see
`Rule.applySet_mono`; the converse fails). -/
def Rule.narrowness (r : Rule L P F) : Finset L ×ₗ Pᵒᵈ := toLex (r.klass, OrderDual.toDual r.props)

theorem Rule.narrowness_le_iff {r s : Rule L P F} :
    r.narrowness ≤ s.narrowness ↔ r.klass ⊂ s.klass ∨ r.klass = s.klass ∧ s.props ≤ r.props :=
  Prod.Lex.toLex_le_toLex

/-- Under [bonami-stump-2016]'s rule format, a rule applies to a cell `⟨L, σ⟩`
when `L` is in its class and its property set is contained in `σ`. -/
instance : Exponence.Rule (Rule L P F) (L × P) F where
  exponent := Rule.payload
  Applies r c := c.1 ∈ r.klass ∧ r.props ≤ c.2

@[simp] theorem Rule.applies_iff {r : Rule L P F} {c : L × P} :
    Exponence.Applies r c ↔ c.1 ∈ r.klass ∧ r.props ≤ c.2 :=
  Iff.rfl

theorem Rule.applySet_mono {r s : Rule L P F} (hk : r.klass = s.klass)
    (h : r.narrowness ≤ s.narrowness) : Exponence.applySet r ⊆ Exponence.applySet s := by
  rcases Rule.narrowness_le_iff.1 h with hlt | ⟨_, hp⟩
  · exact absurd hk hlt.ne
  · intro c hc
    rw [Exponence.mem_applySet] at hc ⊢
    exact ⟨hk ▸ hc.1, hp.trans hc.2⟩

end Narrowness

/-! ### Selection over the narrowness order -/

section Selection
variable [PartialOrder P] [DecidableEq L] [DecidableLE P] [DecidableLT P]

instance : DecidableRel (Exponence.Applies : Rule L P F → L × P → Prop) :=
  fun r c => inferInstanceAs (Decidable (c.1 ∈ r.klass ∧ r.props ≤ c.2))

instance : DecidableRel ((· < ·) : Finset L ×ₗ Pᵒᵈ → Finset L ×ₗ Pᵒᵈ → Prop) :=
  Prod.Lex.decidable _ _

/-! ### The Identity Function Default -/

section IdentityDefault
variable [Fintype L] [OrderBot P]

/-- The **Identity Function Default** ([bonami-stump-2016]) is the rule that
applies to every lexeme and every property set and changes nothing. PFM assumes
a rule of this form in every block as a universal principle; here it is a
definition whose consequences are theorems. -/
def identityDefault : Rule L P (Action Z P) where
  klass := Finset.univ
  props := ⊥
  payload := .const id

omit [DecidableEq L] [DecidableLE P] [DecidableLT P] in
theorem identityDefault_applies (c : L × P) :
    Exponence.Applies (identityDefault (L := L) (Z := Z) (P := P)) c :=
  ⟨Finset.mem_univ _, bot_le⟩

omit [DecidableLE P] [DecidableLT P] in
theorem le_identityDefault (r : Rule L P (Action Z P)) :
    r.narrowness ≤ (identityDefault (Z := Z) (P := P)).narrowness := by
  by_cases h : r.klass = Finset.univ
  · exact Rule.narrowness_le_iff.2 (.inr ⟨h, bot_le⟩)
  · exact Rule.narrowness_le_iff.2 (.inl (Finset.ssubset_univ_iff.mpr h))

/-- A block containing the IFD always selects a rule — the totality of Nar
([bonami-stump-2016]'s (14)) that [stump-2001] secures by stipulating the IFD. -/
theorem selectMinimal_isSome_of_mem_identityDefault
    {v : RuleSet (Rule L P (Action Z P))} {c : L × P}
    (h : identityDefault (Z := Z) (P := P) ∈ v) : (v.selectMinimal Rule.narrowness c).isSome :=
  RuleSet.selectMinimal_isSome_iff.mpr
    ⟨identityDefault (P := P), h, identityDefault_applies c⟩

end IdentityDefault

/-! ### Blocks and the paradigm function -/

/-- A **rule block** ([bonami-stump-2016]) is a list of rules of exponence and
referral in paradigmatic opposition, of which only the narrowest applies. -/
abbrev Block (L Z P : Type*) := RuleSet (Rule L P (Action Z P))

/-- `expoFragment b` keeps the rules of exponence in the block `b` and drops its
referral rules; it is the target of a referral's re-selection. -/
def expoFragment (b : Block L Z P) : Block L Z P :=
  b.filter (fun r => r.payload matches .expo _)

omit [PartialOrder P] [DecidableEq L] [DecidableLE P] [DecidableLT P] in
theorem mem_expoFragment_expo {b : Block L Z P} {r : Rule L P (Action Z P)}
    (h : r ∈ expoFragment b) : ∃ f, r.payload = Action.expo f := by
  simp only [expoFragment, List.mem_filter] at h
  obtain ⟨-, h2⟩ := h
  cases hp : r.payload with
  | expo f => exact ⟨f, rfl⟩
  | referral g => rw [hp] at h2; simp at h2

/-- Evaluating a block at a cell selects the narrowest applicable rule to produce
a form. An exponence rule applies its form operation, and a referral rule
re-selects among the block's exponence rules at the retargeted property set (one
hop). The stem is left unchanged when nothing applies. -/
def evalBlockForm (Lindex : Z → L) (b : Block L Z P) (wσ : Z × P) : Z :=
  match b.selectMinimal Rule.narrowness (Lindex wσ.1, wσ.2) with
  | some r =>
    match r.payload with
    | .expo f => f wσ.2 wσ.1
    | .referral retarget =>
      match RuleSet.selectMinimal (expoFragment b) Rule.narrowness
          (Lindex wσ.1, retarget wσ.2) with
      | some s =>
        match s.payload with
        | .expo g => g (retarget wσ.2) wσ.1
        | .referral _ => wσ.1
      | none => wσ.1
  | none => wσ.1

theorem evalBlockForm_referral {Lindex : Z → L} {b : Block L Z P} {w : Z} {σ : P}
    {r : Rule L P (Action Z P)} {retarget : P → P}
    (hr : b.selectMinimal Rule.narrowness (Lindex w, σ) = some r)
    (hpay : r.payload = Action.referral retarget) :
    evalBlockForm Lindex b (w, σ)
      = evalBlockForm Lindex (expoFragment b) (w, retarget σ) := by
  cases hs : RuleSet.selectMinimal (expoFragment b) Rule.narrowness (Lindex w, retarget σ) with
  | none => simp only [evalBlockForm, hr, hpay, hs]
  | some s =>
    obtain ⟨g, hg⟩ := mem_expoFragment_expo (RuleSet.selectMinimal_mem hs)
    simp only [evalBlockForm, hr, hpay, hs, hg]

/-- `evalBlock` evaluates a block at a form-state and keeps the property set, as
[bonami-stump-2016]'s rule format outputs `⟨f(W), σ⟩`. -/
def evalBlock (Lindex : Z → L) (b : Block L Z P) (wσ : Z × P) : Z × P :=
  (evalBlockForm Lindex b wσ, wσ.2)

@[simp] theorem evalBlock_snd (Lindex : Z → L) (b : Block L Z P) (wσ : Z × P) :
    (evalBlock Lindex b wσ).2 = wσ.2 :=
  rfl

/-- `blocksEval` threads a form-state through a block cascade, with the blocks
listed inner-first. -/
def blocksEval (Lindex : Z → L) (blocks : List (Block L Z P)) (wσ : Z × P) : Z × P :=
  blocks.foldl (fun w b => evalBlock Lindex b w) wσ

@[simp] theorem blocksEval_snd (Lindex : Z → L) (blocks : List (Block L Z P))
    (wσ : Z × P) : (blocksEval Lindex blocks wσ).2 = wσ.2 := by
  induction blocks generalizing wσ with
  | nil => rfl
  | cons b bs ih => exact (ih (evalBlock Lindex b wσ)).trans (evalBlock_snd Lindex b wσ)

/-- The **paradigm function** ([bonami-stump-2016]'s (13)) applies basic stem
choice and then the stipulated block cascade. The `blocks` are listed inner-first, so
`[I, II, III]` realizes `[iii : [ii : [i : Stem]]]`. `Lindex : Z → L` recovers a
stem's covert lexemic index (fn. 7); L-index persistence holds by construction,
since selection threads a fixed lexeme through `L × P`. -/
def paradigmFunction (Lindex : Z → L) (stemChoice : L × P → Z)
    (blocks : List (Block L Z P)) (c : L × P) : Z × P :=
  blocksEval Lindex blocks (stemChoice c, c.2)

/-- The rules of a **portmanteau block** `[m, n]` ([bonami-stump-2016]) compete
with the composition of blocks `m` and `n`, and when none applies the **Function
Composition Default** falls back to that composition. This is the handbook's
block-straddling device; [stump-2020] supersedes it with **rule conflation** (a
portmanteau rule as the conflation of two rules, sitting in a single block and
winning by ordinary narrowness), the route [stump-2022] develops. It is kept here
as the faithfully pre-conflation account. -/
def evalPortmanteau (Lindex : Z → L) (bmn bm bn : Block L Z P) (wσ : Z × P) : Z × P :=
  if (bmn.applicable (Lindex wσ.1, wσ.2)).isEmpty
  then evalBlock Lindex bm (evalBlock Lindex bn wσ)
  else evalBlock Lindex bmn wσ

theorem evalPortmanteau_eq_comp_of_not_applies (Lindex : Z → L) (bmn bm bn : Block L Z P)
    (wσ : Z × P) (h : bmn.applicable (Lindex wσ.1, wσ.2) = []) :
    evalPortmanteau Lindex bmn bm bn wσ = evalBlock Lindex bm (evalBlock Lindex bn wσ) := by
  simp [evalPortmanteau, h]

theorem selectMinimal_append_maximal {v : RuleSet (Rule L P F)} {c : L × P}
    {top : Rule L P F} (hmax : ∀ r : Rule L P F, r.narrowness ≤ top.narrowness)
    (htop : Exponence.Applies top c) :
    RuleSet.selectMinimal (v ++ [top]) Rule.narrowness c =
      (v.selectMinimal Rule.narrowness c).or (some top) := by
  have htop' : c.1 ∈ top.klass ∧ top.props ≤ c.2 := htop
  have happl : RuleSet.applicable (v ++ [top]) c = v.applicable c ++ [top] := by
    simp [RuleSet.applicable, List.filter_append, htop']
  have hpred : (fun r : Rule L P F =>
        (RuleSet.applicable (v ++ [top]) c).all
          (fun s => decide (¬ s.narrowness < r.narrowness)))
      = (fun r : Rule L P F =>
          (v.applicable c).all (fun s => decide (¬ s.narrowness < r.narrowness))) := by
    funext r
    have : ¬ top.narrowness < r.narrowness := fun hlt => absurd (hmax r) (not_le_of_gt hlt)
    rw [happl]; simp [List.all_append, this]
  have hfold : List.find?
      (fun r => (v.applicable c).all (fun s => decide (¬ s.narrowness < r.narrowness)))
      (v.applicable c) = v.selectMinimal Rule.narrowness c := rfl
  rw [RuleSet.selectMinimal, hpred, happl, List.find?_append, hfold]
  rcases hs : v.selectMinimal Rule.narrowness c with _ | r
  · have hnil : v.applicable c = [] := RuleSet.selectMinimal_eq_none_iff.mp hs
    rw [Option.none_or, hnil]
    simp
  · rfl

/-! ### The Function Composition Default as a derived rule -/

section FunctionCompositionDefault
variable [Fintype L] [OrderBot P]

/-- The **Function Composition Default** as a derived rule ([spencer-2013]) is the
rule of a portmanteau block `[m, n]` whose σ-sensitive action evaluates block `n`
and then block `m` at the current cell. Like `identityDefault` it applies
everywhere (`klass = univ`, `props = ⊥`) and is `≤`-maximal, so any explicit
portmanteau rule, being narrower, preempts it by ordinary Pāṇinian narrowness. [spencer-2013]
observes that an explicit portmanteau rule is by definition more specific than
the FCD, so ordinary narrowness suffices to order them; this derives what
`evalPortmanteau` stipulates, the same stipulate-to-derive upgrade
`identityDefault` gives the Identity Function Default. -/
def functionCompositionDefault (Lindex : Z → L) (bm bn : Block L Z P) :
    Rule L P (Action Z P) where
  klass := Finset.univ
  props := ⊥
  payload := .expo (fun σ z => (evalBlock Lindex bm (evalBlock Lindex bn (z, σ))).1)

theorem functionCompositionDefault_applies (Lindex : Z → L) (bm bn : Block L Z P)
    (c : L × P) : Exponence.Applies
      (functionCompositionDefault Lindex bm bn) c :=
  ⟨Finset.mem_univ _, bot_le⟩

theorem le_functionCompositionDefault (Lindex : Z → L) (bm bn : Block L Z P)
    (r : Rule L P (Action Z P)) :
    r.narrowness ≤ (functionCompositionDefault Lindex bm bn).narrowness := by
  by_cases h : r.klass = Finset.univ
  · exact Rule.narrowness_le_iff.2 (.inr ⟨h, bot_le⟩)
  · exact Rule.narrowness_le_iff.2 (.inl (Finset.ssubset_univ_iff.mpr h))

theorem evalPortmanteau_eq_functionCompositionDefault (Lindex : Z → L)
    (bmn bm bn : Block L Z P) (wσ : Z × P)
    (hbmn : ∀ r ∈ bmn, ∃ f, r.payload = Action.expo f) :
    evalPortmanteau Lindex bmn bm bn wσ
      = evalBlock Lindex (bmn ++ [functionCompositionDefault Lindex bm bn]) wσ := by
  have hsel := selectMinimal_append_maximal (v := bmn)
    (c := (Lindex wσ.1, wσ.2)) (le_functionCompositionDefault Lindex bm bn)
    (functionCompositionDefault_applies Lindex bm bn (Lindex wσ.1, wσ.2))
  unfold evalPortmanteau
  by_cases h : (bmn.applicable (Lindex wσ.1, wσ.2)).isEmpty = true
  · rw [ite_eq_left h]
    rw [List.isEmpty_iff] at h
    rw [RuleSet.selectMinimal_eq_none_iff.mpr h, Option.none_or] at hsel
    conv_rhs => rw [evalBlock, evalBlockForm, hsel]
    simp only [functionCompositionDefault, Prod.mk.eta]
    refine Prod.ext rfl ?_
    simp only [evalBlock_snd]
  · rw [ite_eq_right h]
    rw [List.isEmpty_iff] at h
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp
      (RuleSet.selectMinimal_isSome_iff (key := Rule.narrowness).mpr
        ⟨r, (RuleSet.mem_applicable.mp hr).1, (RuleSet.mem_applicable.mp hr).2⟩)
    obtain ⟨f, hf⟩ := hbmn r' (RuleSet.selectMinimal_mem hr')
    rw [hr', Option.some_or] at hsel
    simp only [evalBlock, evalBlockForm, hsel, hr', hf]

end FunctionCompositionDefault

theorem _root_.Morphology.Linkage.realized_eq_paradigmFunction [DecidableEq Z]
    (ℓ : Linkage L Z P P) (Lindex : Z → L) (stemChoice : L × P → Z)
    (blocks : List (Block L Z P)) (l : L) (σ : P) (h : ℓ.IsPropertyPreserving id)
    (hstem : ∀ l σ, ℓ.realize l σ = {stemChoice (l, σ)}) :
    ℓ.realized (fun z τ ↦ (blocksEval Lindex blocks (z, τ)).1) l σ
      = {paradigmFunction Lindex stemChoice blocks (l, σ)} := by
  simp [Linkage.realized, h l σ, hstem, paradigmFunction, Prod.ext_iff]

theorem _root_.Morphology.Linkage.ofFun_realized_eq_paradigmFunction [DecidableEq Z]
    (Lindex : Z → L) (stemChoice : L × P → Z) (blocks : List (Block L Z P)) (l : L) (σ : P) :
    (Linkage.ofFun id (Function.curry stemChoice)).realized
        (fun z τ ↦ (blocksEval Lindex blocks (z, τ)).1) l σ
      = {paradigmFunction Lindex stemChoice blocks (l, σ)} :=
  Linkage.realized_eq_paradigmFunction _ Lindex stemChoice blocks l σ (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl

theorem _root_.Morphology.Linkage.ofRules_realized_eq_paradigmFunction [DecidableEq Z]
    {R : Type*} [Exponence.Rule R P Z] {κ : Type*} [Preorder κ] (key : R → κ)
    [DecidableRel (· < · : κ → κ → Prop)]
    [DecidableRel (Exponence.Applies : R → P → Prop)] (rules : L → List R) (root : L → Z)
    (Lindex : Z → L) (blocks : List (Block L Z P)) (l : L) (σ : P) :
    (Linkage.ofRules id key rules root).realized (fun z τ ↦ (blocksEval Lindex blocks (z, τ)).1) l σ
      = {paradigmFunction Lindex
          (fun c ↦ RuleSet.realizeMinimalD (rules c.1) key (fun _ ↦ root c.1) c.2) blocks (l, σ)} :=
  Linkage.realized_eq_paradigmFunction _ Lindex _ blocks l σ (fun _ _ ↦ rfl) fun _ _ ↦ rfl

/-- `paradigmRealization` presents the paradigm function as a realization whose
opaque indices are lexemes, realized at every cell, total and univalent, PFM's
stratum. `Lindex` is the seed of the lexeme-to-√ coarsening arrow between
individuation grains. -/
def paradigmRealization (Lindex : Z → L) (stemChoice : L × P → Z)
    (blocks : List (Block L Z P)) : Realization L P (Z × P) :=
  ⟨fun l σ => {paradigmFunction Lindex stemChoice blocks (l, σ)}⟩

theorem paradigmRealization_isTotal (Lindex : Z → L) (stemChoice : L × P → Z)
    (blocks : List (Block L Z P)) :
    (paradigmRealization Lindex stemChoice blocks).IsTotal :=
  fun _ _ => Finset.singleton_nonempty _

theorem paradigmRealization_isUnivalent (Lindex : Z → L) (stemChoice : L × P → Z)
    (blocks : List (Block L Z P)) :
    (paradigmRealization Lindex stemChoice blocks).IsUnivalent :=
  fun _ _ => (Finset.card_singleton _).le

end Selection

/-! ### Payload functoriality -/

section MapPayload
variable {F' : Type*}

/-- `r.mapPayload g` relabels the payload of `r` by `g`, keeping its class and
property set. -/
def Rule.mapPayload (g : F → F') (r : Rule L P F) : Rule L P F' where
  klass := r.klass
  props := r.props
  payload := g r.payload

@[simp] theorem Rule.mapPayload_klass (g : F → F') (r : Rule L P F) :
    (r.mapPayload g).klass = r.klass := rfl

@[simp] theorem Rule.mapPayload_props (g : F → F') (r : Rule L P F) :
    (r.mapPayload g).props = r.props := rfl

@[simp] theorem Rule.narrowness_mapPayload {g : F → F'} {r : Rule L P F} :
    (r.mapPayload g).narrowness = r.narrowness := rfl

section
variable [PartialOrder P] [DecidableEq L] [DecidableLE P] [DecidableLT P]

theorem selectMinimal_map_payload (g : F → F') (v : RuleSet (Rule L P F)) (c : L × P) :
    RuleSet.selectMinimal (v.map (Rule.mapPayload g)) Rule.narrowness c
      = (v.selectMinimal Rule.narrowness c).map (Rule.mapPayload g) := by
  have hA : RuleSet.applicable (v.map (Rule.mapPayload g)) c
      = (v.applicable c).map (Rule.mapPayload g) := by
    simp only [RuleSet.applicable, List.filter_map, Function.comp_def, Rule.applies_iff,
      Rule.mapPayload_klass, Rule.mapPayload_props]
  rw [RuleSet.selectMinimal, RuleSet.selectMinimal, hA, List.find?_map]
  simp only [Function.comp_def, List.all_map, Rule.narrowness_mapPayload]

end

end MapPayload

end Morphology.PFM
