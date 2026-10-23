module

public import Linglib.Semantics.Plurality.Number
public import Linglib.Semantics.Aspect.Telicity
public import Linglib.Semantics.Mereology.Topology
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Moon (2026): countability and measured parts in mixed drink nouns

Mixed drink nouns (*martini*, *cappuccino*) are count nouns that denote liquids. Moon derives their
countability from their part structure: a mixed drink is a mereological sum of ingredient parts
standing in a fixed ratio of measures (`Recipe`, `RatioHolds`), one of which — the shot of liquor or
espresso, the MEASURED PART — supplies the unit of individuation, and the whole is a connected
liquid, self-connected in the mereotopological sense of Casati and Varzi and of Grimm under a
connection relation `C` (`ConnectedLiquid`, `Mereology.SelfConnected`). The denotation
`mixedDrinkDen` packages Moon's final formula as the existence of a `MixedDrinkWitness`.

Two consequences carry the countability argument. The sum of two spatially separate drinks is not a
connected liquid, so the denotation is not cumulative (`not_mixedDrinkDen_of_not_selfConnected`), a
mereotopological route to non-cumulativity that a bare semilattice lacks, where it comes only from
quantization (`connectivity_breaks_cum`). And a mixed drink has proper parts, so it is not a
mereological atom (`mixedDrink_not_atom`), and the atomicity on which count theories found
countability excludes it (`atomsOf_excludes_mixed_drinks`), while half a drink with its ratios
preserved is still a drink, so the denotation is not quantized either (`mixedDrink_not_qua`). Mixed
drinks thus occupy Filip's ¬CUM ∧ ¬QUA middle ground (`mixedDrink_middle_ground`), and the gap
propagates to drinking VPs through `middle_ground_stable` (`mixedDrink_VP_propagation_gap`).
Multipliers such as *double* rescale the measured part's ratio constant rather than the whole
(`doubleRecipe`, Wągiel's subatomic quantification), and *dry* rescales another ingredient's
(`modifyRatio`).

Moon's corpus and judgment data stay in prose: in her COCA counts (Appendix A) cocktail
nouns pattern with count nouns on bare plurals and numerals while non-count drink nouns
take bare singulars and containers; countability survives coercion contexts such as
*pitcher of martinis*; and *who drank more americanos?* is ambiguous between volume,
portions, and measured parts.

## Implementation notes

Self-connection is Moon's (20b), stated with the library's overlap, which unlike (20a) relates
non-null parts only; connected liquid (23) is read with this notion rather than the touch-based
self-connection of (22), and without its temporal parameter.

## References

* [moon-2026]
* [casati-varzi-1999], [filip-2012], [grimm-2012], [krifka-2021], [wagiel-2021]
-/

@[expose] public section

namespace Moon2026

open Mereology
open Aspect (SINC VP)

/-! ### Mereotopology -/

section Mereotopology

variable {α : Type*}

/-- The phases of matter ([krifka-2021]) are solids, which retain shape, granulars, which are
aggregates of discrete pieces, and liquids, whose parts are in constant internal motion. -/
inductive Phase where
  | solid
  | granular
  | liquid
  deriving DecidableEq, Repr

/-- A connected liquid (Moon's definition (23), without its temporal parameter) is
self-connected with every part liquid. -/
def ConnectedLiquid [PartialOrder α] (C : α → α → Prop) (phase : α → Phase) (x : α) : Prop :=
  SelfConnected C x ∧ ∀ y ≤ x, phase y = .liquid

theorem ConnectedLiquid.selfConnected [PartialOrder α] {C : α → α → Prop} {phase : α → Phase}
    {x : α} (h : ConnectedLiquid C phase x) : SelfConnected C x :=
  h.1

variable [SemilatticeSup α] {C : α → α → Prop} {P : α → Prop}

theorem connectivity_breaks_cum (hConn : ∀ x, P x → SelfConnected C x) {x y : α} (hx : P x)
    (hy : P y) (hDisc : ¬ SelfConnected C (x ⊔ y)) : ¬ CUM P :=
  fun hCum ↦ hDisc (hConn _ (hCum hx hy))

theorem connectivity_middle_ground (hConn : ∀ x, P x → SelfConnected C x) {a b : α}
    (ha : P a) (hb : P b) (hDisc : ¬ SelfConnected C (a ⊔ b)) {x y : α} (hx : P x) (hy : P y)
    (hlt : y < x) : ¬ CUM P ∧ ¬ QUA P :=
  ⟨connectivity_breaks_cum hConn ha hb hDisc, fun hQ ↦ hQ hy hx hlt.ne hlt.le⟩

end Mereotopology

/-! ### Recipes and the mixed-drink denotation -/

/-- A mixed drink recipe lists ingredient predicates, positive ratio constants, and the index of
the measured part. -/
structure Recipe (α K : Type*) [Zero K] [LT K] (n : ℕ) where
  /-- Each slot has an ingredient predicate. -/
  ingredients : Fin n → α → Prop
  /-- Each slot has a ratio constant. -/
  ratios : Fin n → K
  ratios_pos : ∀ i, 0 < ratios i
  /-- The measured part is the ingredient that supplies the unit. -/
  measuredPart : Fin n

variable {α K : Type*} [SemilatticeSup α] [Field K] [LinearOrder K] {n : ℕ}

/-- Moon's ratio constraint requires `μ yᵢ / rᵢ = μ yⱼ / rⱼ` for all ingredient parts, here in
cross-multiplied form. -/
def RatioHolds (μ : α → K) (recipe : Recipe α K n) (parts : Fin n → α) : Prop :=
  ∀ i j, μ (parts i) * recipe.ratios j = μ (parts j) * recipe.ratios i

/-- A witness that `x` is a mixed drink under `recipe` gives non-null, pairwise non-overlapping
ingredient parts of `x` that exhaust it and satisfy their ingredient predicates and the ratio
constraint, with `x` a connected liquid. -/
structure MixedDrinkWitness (C : α → α → Prop) (recipe : Recipe α K n) (μ : α → K)
    (phase : α → Phase) (x : α) where
  /-- Each ingredient slot is filled by an entity. -/
  assign : Fin n → α
  part_le : ∀ i, assign i ≤ x
  present : ∀ i, ¬ IsBot (assign i)
  satisfies : ∀ i, recipe.ingredients i (assign i)
  ratio : RatioHolds μ recipe assign
  disjoint : ∀ i j, i ≠ j → ¬ Overlap (assign i) (assign j)
  covers : ∀ z, z ≤ x → ∃ i, Overlap z (assign i)
  connected : ConnectedLiquid C phase x

/-- The denotation of a mixed drink noun, Moon's final formula, holds of ratio-related
ingredient parts forming a connected liquid. The MEASURED PART conjunct, which Moon leaves informal,
is recorded only as the recipe's `measuredPart` index and not imposed as a truth
condition, so this is her ratio formula (19) plus CONNECTED LIQUID; she notes that (19)
alone also covers ratio-structured non-count drinks such as *lemonade*. -/
def mixedDrinkDen (C : α → α → Prop) (recipe : Recipe α K n) (μ : α → K) (phase : α → Phase)
    (x : α) : Prop :=
  Nonempty (MixedDrinkWitness C recipe μ phase x)

variable {C : α → α → Prop} {recipe : Recipe α K n} {μ : α → K} {phase : α → Phase}

theorem selfConnected_of_mixedDrinkDen {x : α} (hx : mixedDrinkDen C recipe μ phase x) :
    SelfConnected C x :=
  hx.some.connected.selfConnected

theorem not_mixedDrinkDen_of_not_selfConnected {x : α} (hDisc : ¬ SelfConnected C x) :
    ¬ mixedDrinkDen C recipe μ phase x :=
  fun hx ↦ hDisc (selfConnected_of_mixedDrinkDen hx)

theorem not_mixedDrinkDen_of_exclusive {recipe : Recipe α K (n + 2)} {y : α} (i : Fin (n + 2))
    (hExcl : ∀ j ≠ i, ∀ z ≤ y, ¬ recipe.ingredients j z) :
    ¬ mixedDrinkDen C recipe μ phase y :=
  fun ⟨w⟩ ↦ let ⟨j, hj⟩ := exists_ne i; hExcl j hj _ (w.part_le j) (w.satisfies j)

theorem mixedDrink_not_atom {recipe : Recipe α K (n + 2)} {x : α}
    (hx : mixedDrinkDen C recipe μ phase x) : ¬ Atom x := by
  intro hAtom
  obtain ⟨w⟩ := hx
  have h0 : w.assign 0 = x := Atom.eq hAtom (w.part_le 0) (w.present 0)
  have h1 : w.assign 1 = x := Atom.eq hAtom (w.part_le 1) (w.present 1)
  have hDisj := w.disjoint 0 1 Fin.zero_ne_one
  rw [h0, h1] at hDisj
  exact hDisj (Overlap.refl hAtom.not_isBot)

theorem atomsOf_excludes_mixed_drinks {recipe : Recipe α K (n + 2)} (DRINK : α → Prop) {x : α}
    (hx : mixedDrinkDen C recipe μ phase x) : ¬ Number.atomsOf DRINK x :=
  fun ⟨_, hAtom⟩ ↦ mixedDrink_not_atom hx hAtom

theorem mixedDrink_not_qua {x y : α} (hx : mixedDrinkDen C recipe μ phase x)
    (hy : mixedDrinkDen C recipe μ phase y) (hlt : y < x) :
    ¬ QUA (mixedDrinkDen C recipe μ phase) :=
  fun hQ ↦ hQ hy hx hlt.ne hlt.le

theorem mixedDrink_middle_ground {a b : α} (ha : mixedDrinkDen C recipe μ phase a)
    (hb : mixedDrinkDen C recipe μ phase b) (hDisc : ¬ SelfConnected C (a ⊔ b)) {x y : α}
    (hx : mixedDrinkDen C recipe μ phase x) (hy : mixedDrinkDen C recipe μ phase y) (hlt : y < x) :
    ¬ CUM (mixedDrinkDen C recipe μ phase) ∧ ¬ QUA (mixedDrinkDen C recipe μ phase) :=
  connectivity_middle_ground (fun _ ↦ selfConnected_of_mixedDrinkDen) ha hb hDisc hx hy hlt

private theorem not_cum_vp {β : Type*} [SemilatticeSup β] {θ : α → β → Prop} {OBJ : α → Prop}
    (hs : SUM θ) (hU : UP θ) {x y : α}
    {e₁ e₂ : β} (hx : OBJ x) (hy : OBJ y) (hθ₁ : θ x e₁) (hθ₂ : θ y e₂) (hSum : ¬ OBJ (x ⊔ y)) :
    ¬ CUM (VP θ OBJ) := by
  intro hCum
  obtain ⟨z, hz_obj, hz_θ⟩ := hCum ⟨x, hx, hθ₁⟩ ⟨y, hy, hθ₂⟩
  exact hSum (hU hz_θ (hs hθ₁ hθ₂) ▸ hz_obj)

theorem middle_ground_stable {β : Type*} [SemilatticeSup β] {θ : α → β → Prop} (h : SINC θ)
    (hU : UP θ) (hs : SUM θ) {OBJ : α → Prop} {a b : α} {e_a e_b : β} (ha : OBJ a) (hb : OBJ b)
    (hθ_a : θ a e_a) (hθ_b : θ b e_b) (hSum : ¬ OBJ (a ⊔ b)) {x y : α} {e_x : β} (hx : OBJ x)
    (hy : OBJ y) (hlt : y < x) (hθ_x : θ x e_x) : ¬ CUM (VP θ OBJ) ∧ ¬ QUA (VP θ OBJ) := by
  refine ⟨not_cum_vp hs hU ha hb hθ_a hθ_b hSum, fun hQua ↦ ?_⟩
  obtain ⟨e_y, he_y_lt, hθ_y⟩ := h.mse hθ_x hlt
  exact hQua ⟨y, hy, hθ_y⟩ ⟨x, hx, hθ_x⟩ he_y_lt.ne he_y_lt.le

theorem mixedDrink_VP_propagation_gap {β : Type*} [SemilatticeSup β] {drinkTheme : α → β → Prop}
    (h : SINC drinkTheme) (hU : UP drinkTheme) (hs : SUM drinkTheme) {a b : α} {e_a e_b : β}
    (ha : mixedDrinkDen C recipe μ phase a) (hb : mixedDrinkDen C recipe μ phase b)
    (hθ_a : drinkTheme a e_a) (hθ_b : drinkTheme b e_b)
    (hSum : ¬ mixedDrinkDen C recipe μ phase (a ⊔ b)) {x y : α} {e_x : β}
    (hx : mixedDrinkDen C recipe μ phase x) (hy : mixedDrinkDen C recipe μ phase y) (hlt : y < x)
    (hθ_x : drinkTheme x e_x) :
    ¬ CUM (VP drinkTheme (mixedDrinkDen C recipe μ phase)) ∧
      ¬ QUA (VP drinkTheme (mixedDrinkDen C recipe μ phase)) :=
  middle_ground_stable h hU hs ha hb hθ_a hθ_b hSum hx hy hlt hθ_x

/-! ### Modifying the ratios -/

variable [IsStrictOrderedRing K]

/-- Rescaling one ingredient's ratio constant gives *dry martini* (Moon's (27b)), which lowers
the vermouth relative to the gin. -/
def modifyRatio (recipe : Recipe α K n) (target : Fin n) (factor : K) (hPos : 0 < factor) :
    Recipe α K n where
  ingredients := recipe.ingredients
  ratios i := if i = target then factor * recipe.ratios i else recipe.ratios i
  ratios_pos i := by
    split_ifs
    exacts [mul_pos hPos (recipe.ratios_pos i), recipe.ratios_pos i]
  measuredPart := recipe.measuredPart

/-- The multiplier *double* targets the measured part ([wagiel-2021]), so a double americano
has twice the espresso, not twice the volume. -/
def doubleRecipe (recipe : Recipe α K n) : Recipe α K n :=
  modifyRatio recipe recipe.measuredPart 2 two_pos

/-- A margarita mixes tequila, triple sec and lime juice in ratio `5 : 2 : 3/2`, with the
tequila as measured part. -/
def margaritaRecipe (α K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (tequila tripleSec limeJuice : α → Prop) : Recipe α K 3 where
  ingredients := ![tequila, tripleSec, limeJuice]
  ratios := ![5, 2, 3 / 2]
  ratios_pos i := by fin_cases i <;> norm_num
  measuredPart := 0

end Moon2026
