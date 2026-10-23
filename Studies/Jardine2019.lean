/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Computability.Language
public import Linglib.Phonology.Autosegmental.MergeAR
public import Linglib.Phonology.Subregular.AutosegmentalStrictlyLocal
public import Linglib.Phonology.Subregular.TierStrictlyLocal
public import Linglib.Phonology.Tone.Basic
public import Linglib.Data.Examples.Jardine2019

/-!
# Jardine (2019): The expressivity of autosegmental grammars

The map `gT` sends each tone symbol to a primitive autosegmental graph, `H` and `L` a tone over
a mora and `F` the falling contour `H L` over one, and extends to strings by merging
concatenation, which fuses a run of `H`s into one `H` over its morae. A banned-subgraph grammar
over this realization describes the strings whose graph avoids it, an instance of the
autosegmental strictly local class (`Language.bannedSubgraph`). Every graph in `gT(Σ*)` obeys
the OCP and the No-Crossing Constraint. Membership decides on strings: the spreading grammar
admits exactly its example strings, and the grammar of unbounded tonal plateauing admits
`L_UTP` and excludes the plateau `HHLLHH` at any width, which the unmerged realization leaves
free.

Theorem 3 compares the class with the string classes. `gT(HL)` is a subgraph of `gT(HF)`, so no
grammar excludes `HL` without excluding `HF`. And `L_UTP` is neither strictly local nor
tier-based strictly local at any width: with `x = L^(k-1)`, `H L x` and `x H` are in it and
`H L x H` is not, and every symbol is visible, so a tier-based grammar would be strictly local.

## Main results

* `toAR_realize`: the realization of a string is the presentation `merged` of its words.
* `isCleanAt_and_noCrossing_realize`: graphs in `gT(Σ*)` obey the OCP and the NCC.
* `rows_agree`: the grammars decide the paper's example strings.
* `not_mem_ASL_HF_of_not_mem_ASL_HL`: a grammar excluding `HL` excludes `HF`.
* `not_isStrictlyLocal_ASL_utp`, `not_isTierStrictlyLocal_ASL_utp`: `L_UTP` is neither strictly
  local nor tier-based strictly local.

## Implementation notes

* The paper evaluates a grammar on `g(⋊w⋉)`, with border primitives for `⋊` and `⋉`, which this
  file omits. The grammars here mention no border.
* Banned subgraphs need not be connected (`Autosegmental/Factors.lean`), so the class here
  contains the paper's.
* `gT` extends to strings by Definition 2, the product of primitives under merging
  concatenation (`MergeAR`). Its primitives are OCP-clean, so it agrees with collapsing the
  bridged concatenation (`MergeAR.prod_map_ofAR`), whose presentation `merged` the proofs
  compute with.
* The unmerged realization `(w.map gT).prod` is kept for the contrast merging makes.

## TODO

Add the border primitives, and with them Theorem 3's other half, that the strictly 2-local
`HL`-free language is not in the class. Theorem 2, that the class is properly contained in the
star-free languages, is formalized only for the link-free unmerged fragment
(`isStarFree_free_prod_map_hlh`); Theorem 4, incomparability with the strictly piecewise
languages, needs connected factors.

## References

* [jardine-2019]
-/

@[expose] public section

namespace Jardine2019

open Autosegmental Tone Tone.TRN

/-- A symbol of the string alphabet `Σ_T` (§5.2.2) is a high, low or falling-toned mora. -/
inductive Sym | H | L | F
  deriving DecidableEq, Repr

/-- A symbol's primitive carries its melody, `F` the falling contour `H L`. -/
def Sym.melody : Sym → List TRN
  | .H => [TRN.H]
  | .L => [TRN.L]
  | .F => [TRN.H, TRN.L]

/-- The mora, the paper's tone-bearing unit. -/
abbrev μ : TBUKind := .mora

/-- `gT` (23) maps a symbol to the primitive (Definition 1) of its melody over one mora. -/
def gT (s : Sym) : AR (TwoTier TRN TBUKind) := AR.primitive s.melody μ

/-- `gT(w)` (Definition 2): the product of the primitives under merging concatenation. -/
def realize (w : List Sym) : MergeAR true (TwoTier TRN TBUKind) :=
  (w.map fun s ↦ MergeAR.ofAR (gT s)).prod

/-- The merged realization of a string, read as a representation of words. -/
abbrev merged (w : List Sym) :=
  AR.ofWords (OCP.collapse (w.map Sym.melody).flatten) (w.map fun _ => [μ]).flatten
    (MergedLinks (w.map Sym.melody).flatten
      (BlockLinks Sym.melody (fun _ => [μ]) (fun _ _ _ => True) w))

/-- The unmerged realization of a string, read as a representation of words. -/
abbrev unmerged (w : List Sym) :=
  AR.ofWords (w.map Sym.melody).flatten (w.map fun _ => [μ]).flatten
    (BlockLinks Sym.melody (fun _ => [μ]) (fun _ _ _ => True) w)

theorem isCleanAt_gT (s : Sym) : (gT s).IsCleanAt true := by
  cases s <;> simp [AR.IsCleanAt, gT, Sym.melody, show H ≠ L by decide]

theorem prod_map_gT (w : List Sym) : (w.map gT).prod = unmerged w :=
  AR.prod_ofWords Sym.melody (fun _ ↦ [μ]) (fun _ _ _ ↦ True) w

theorem toAR_realize (w : List Sym) : MergeAR.toAR (realize w) = merged w := by
  rw [realize, MergeAR.prod_map_ofAR isCleanAt_gT, MergeAR.toAR_ofAR]
  exact AR.prod_ofWords_collapse Sym.melody (fun _ ↦ [μ]) (fun _ _ _ ↦ True) w

/-- `L(B^{gT})` (§5.3) is the set of strings whose realization avoids the grammar. -/
def ASL (B : List (AR (TwoTier TRN TBUKind))) : Language Sym :=
  Language.bannedSubgraph (fun w ↦ MergeAR.toAR (realize w)) B

theorem mem_ASL_iff {B : List (AR (TwoTier TRN TBUKind))} {w : List Sym} :
    w ∈ ASL B ↔ (merged w).Free B := by
  rw [ASL, Language.mem_bannedSubgraph, toAR_realize]

/-- Every graph in `gT(Σ*)` obeys the OCP and the NCC, as they are preserved from the
primitives (§5.2.2). -/
theorem isCleanAt_and_noCrossing_realize (w : List Sym) :
    (MergeAR.toAR (realize w)).IsCleanAt true ∧ (MergeAR.toAR (realize w)).NoCrossing :=
  ⟨MergeAR.isCleanAt_toAR_prod fun _ hX ↦ by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hX
      exact isCleanAt_gT s,
    MergeAR.noCrossing_toAR_prod fun _ hX ↦ by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hX
      exact AR.noCrossing_primitive (as := Sym.melody s) μ⟩

/-! ### The grammars of (26) and (33) -/

/-- The factor of (26) is a tone over two morae. -/
abbrev spread := AR.ofWords [H] [μ, μ] fun _ _ => True

/-- (3), the melody `H L H`. -/
abbrev hlh := AR.ofWords [H, L, H] ([] : List TBUKind) fun _ _ => False

/-- The falling contour is `H L` over one mora. -/
abbrev fall := AR.primitive [H, L] μ

/-- The grammar of (26) bans a tone over two morae. -/
def spreadGrammar : List (AR (TwoTier TRN TBUKind)) := [spread]

/-- The grammar `B_UTP` (33) bans the melody `H L H` and the contour. -/
def utpGrammar : List (AR (TwoTier TRN TBUKind)) := [hlh, fall]

theorem mem_ASL_spreadGrammar_iff (w : List Sym) :
    w ∈ ASL spreadGrammar ↔ ¬ spread.FactorEmbeds (merged w) := by
  simp only [mem_ASL_iff, spreadGrammar, AR.free_cons, AR.free_nil, and_true]

theorem mem_ASL_utpGrammar_iff (w : List Sym) :
    w ∈ ASL utpGrammar ↔ ¬ hlh.FactorEmbeds (merged w) ∧ ¬ fall.FactorEmbeds (merged w) := by
  simp only [mem_ASL_iff, utpGrammar, AR.free_cons, AR.free_nil, and_true]

instance (w : List Sym) : Decidable (w ∈ ASL spreadGrammar) :=
  decidable_of_iff _ (mem_ASL_spreadGrammar_iff w).symm

instance (w : List Sym) : Decidable (w ∈ ASL utpGrammar) :=
  decidable_of_iff _ (mem_ASL_utpGrammar_iff w).symm

/-! ### The data of (27) and (32) -/

/-- The two grammars of the paper's examples. -/
inductive Grammar
  | spread
  | utp
  deriving DecidableEq

/-- A row records a string, the grammar it is tested against, and whether it is in the set. -/
structure Row where
  string : List Sym
  grammar : Grammar
  member : Bool
  deriving DecidableEq

/-- A symbol from its spelling. -/
def Sym.ofChar : Char → Sym
  | 'H' => .H
  | 'F' => .F
  | _ => .L

/-- A row from the paper's features. -/
def Row.ofDatum (e : Datum) : Option Row := do
  let w ← e.feature? "string"
  let g ← match e.feature? "grammar" with
    | some "26" => some Grammar.spread
    | some "33" => some Grammar.utp
    | _ => none
  let m ← e.feature? "member"
  some ⟨w.toList.map Sym.ofChar, g, m = "yes"⟩

/-- The strings of (27) with the `HH` and `HF` the grammar (26) excludes, and those of (32). -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- The set a row's grammar describes. -/
def Grammar.set : Grammar → Language Sym
  | .spread => ASL spreadGrammar
  | .utp => ASL utpGrammar

instance (g : Grammar) (w : List Sym) : Decidable (w ∈ g.set) := by
  cases g <;> simp only [Grammar.set] <;> infer_instance

/-- The grammar (26) admits the strings of (27) and excludes `HH` and `HF`, whose fused `H`
spans two morae, and `B_UTP` admits the strings of `L_UTP`, (32). -/
theorem rows_agree : ∀ r ∈ rows, r.string ∈ r.grammar.set ↔ r.member = true := by decide +kernel

theorem HLH_not_mem_ASL_utp : [.H, .L, .H] ∉ ASL utpGrammar := by decide

theorem LHHLH_not_mem_ASL_utp : [.L, .H, .H, .L, .H] ∉ ASL utpGrammar := by decide

theorem HHLLHH_not_mem_ASL_utp : [.H, .H, .L, .L, .H, .H] ∉ ASL utpGrammar := by decide

theorem HHLLHH_free_prod_map_gT :
    (([.H, .H, .L, .L, .H, .H] : List Sym).map gT).prod.Free utpGrammar := by
  rw [prod_map_gT]
  simp only [utpGrammar, AR.free_cons, AR.free_nil, and_true]
  decide

/-! ### Theorem 3: contours contain their pure counterparts -/

theorem realize_HL_embeds_HF :
    (MergeAR.toAR (realize [.H, .L])).FactorEmbeds (MergeAR.toAR (realize [.H, .F])) := by
  rw [toAR_realize, toAR_realize]
  decide

/-- No forbidden-subgraph grammar excludes `HL` without excluding `HF` (Theorem 3), since a
subgraph of `gT(HL)` is a subgraph of `gT(HF)`. -/
theorem not_mem_ASL_HF_of_not_mem_ASL_HL (B : List (AR (TwoTier TRN TBUKind)))
    (h : [.H, .L] ∉ ASL B) : [.H, .F] ∉ ASL B :=
  fun hHF => h (Language.mem_bannedSubgraph_of_factorEmbeds realize_HL_embeds_HF hHF)

/-! ### The link-free fragment of the unmerged class is star-free -/

theorem isStarFree_free_prod_map_hlh :
    (Language.bannedSubgraph (fun w ↦ (w.map gT).prod) [hlh]).IsStarFree :=
  Language.isStarFree_bannedSubgraph_prod_map gT _ fun F hF => by
    rw [List.mem_singleton] at hF
    subst hF
    exact AR.not_link_ofWords_false

/-! ### Theorem 3: `L_UTP` is neither strictly local nor tier-based strictly local

In a string without `F` every mora carries its own symbol's single tone, so no contour occurs
and membership in `L_UTP` depends only on the merged melody. With `x = L^{k−1}`, `H L·x` and
`x·H` are in `L_UTP` and `H L·x·H` is not, which breaks suffix substitution at every width; and
every symbol is visible, so a tier-based grammar would have to be strictly local. -/

private theorem eq_of_blockLinks {w : List Sym} (hw : ∀ s ∈ w, s ≠ .F) {p q : ℕ}
    (h : BlockLinks Sym.melody (fun _ => [μ]) (fun _ _ _ => True) w p q) : p = q := by
  induction w generalizing p q with
  | nil => exact h.elim
  | cons s w ih =>
    have hs : (Sym.melody s).length = 1 := by
      cases s <;> simp_all [Sym.melody]
    rcases h with ⟨hp, hq, -⟩ | ⟨hp, hq, h⟩
    · simp only [hs, List.length_singleton] at hp hq; omega
    · have := ih (fun t ht => hw t (List.mem_cons_of_mem _ ht)) h
      simp only [hs, List.length_singleton] at hp hq this; omega

theorem not_fall_factorEmbeds_merged {w : List Sym} (hw : ∀ s ∈ w, s ≠ .F) :
    ¬ fall.FactorEmbeds (merged w) := by
  rw [AR.factorEmbeds_ofWords_iff]
  rintro ⟨ot, -, of, -, -, -, hl⟩
  obtain ⟨p₁, -, hb₁, hr₁⟩ := hl 0 (by simp) 0 (by simp) trivial
  obtain ⟨p₂, -, hb₂, hr₂⟩ := hl 1 (by simp) 0 (by simp) trivial
  have e₁ := eq_of_blockLinks hw hb₁
  have e₂ := eq_of_blockLinks hw hb₂
  subst e₁; subst e₂
  omega

theorem hlh_factorEmbeds_merged_iff (w : List Sym) :
    hlh.FactorEmbeds (merged w) ↔ [H, L, H] <:+: OCP.collapse (w.map Sym.melody).flatten := by
  rw [AR.factorEmbeds_iff_infix_of_link_free AR.not_link_ofWords_false]
  refine ⟨fun h => by simpa using h true, fun h i => ?_⟩
  cases i
  · simp
  · simpa using h

private theorem melody_replicate_L (m : ℕ) :
    ((List.replicate m Sym.L).map Sym.melody).flatten = List.replicate m L := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, Sym.melody]

private theorem collapse_HL_replicate (m : ℕ) :
    OCP.collapse ([H, L] ++ List.replicate m L) = [H, L] := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [List.replicate_succ', ← List.append_assoc, OCP.collapse_append, ih]
    decide

private theorem not_infix_HLH_of_length {xs : List TRN} (h : xs.length ≤ 2) :
    ¬ [H, L, H] <:+: xs :=
  fun hi => absurd (hi.length_le.trans h) (by decide)

theorem mem_ASL_utp_HL_replicate (m : ℕ) :
    [Sym.H, Sym.L] ++ List.replicate m Sym.L ∈ ASL utpGrammar := by
  rw [mem_ASL_utpGrammar_iff, hlh_factorEmbeds_merged_iff]
  refine ⟨?_, not_fall_factorEmbeds_merged ?_⟩
  · have hHL : ([Sym.H, Sym.L].map Sym.melody).flatten = [H, L] := rfl
    simp only [List.map_append, List.flatten_append, melody_replicate_L, hHL,
      collapse_HL_replicate]
    exact not_infix_HLH_of_length (by simp)
  · grind

theorem mem_ASL_utp_replicate_H (m : ℕ) :
    List.replicate m Sym.L ++ [Sym.H] ∈ ASL utpGrammar := by
  rw [mem_ASL_utpGrammar_iff, hlh_factorEmbeds_merged_iff]
  refine ⟨?_, not_fall_factorEmbeds_merged ?_⟩
  · have hH : ([Sym.H].map Sym.melody).flatten = [H] := rfl
    simp only [List.map_append, List.flatten_append, melody_replicate_L, hH]
    rcases m with _ | m
    · decide
    · rw [OCP.collapse_append, OCP.collapse_replicate]
      exact not_infix_HLH_of_length (by decide)
  · grind

theorem not_mem_ASL_utp_HL_replicate_H (m : ℕ) :
    [Sym.H, Sym.L] ++ List.replicate m Sym.L ++ [Sym.H] ∉ ASL utpGrammar := by
  rw [mem_ASL_utpGrammar_iff, hlh_factorEmbeds_merged_iff, not_and_or, not_not]
  left
  have hHL : ([Sym.H, Sym.L].map Sym.melody).flatten = [H, L] := rfl
  have hH : ([Sym.H].map Sym.melody).flatten = [H] := rfl
  simp only [List.map_append, List.flatten_append, melody_replicate_L, hHL, hH]
  rw [OCP.collapse_append, collapse_HL_replicate]
  decide

/-- `L_UTP` is not strictly local at any width (Theorem 3). -/
theorem not_isStrictlyLocal_ASL_utp (k : ℕ) : ¬ (ASL utpGrammar).IsStrictlyLocal k := fun h =>
  not_mem_ASL_utp_HL_replicate_H (k - 1) (h.suffixSubstitutionClosed [.H, .L] [] [] [.H]
    (List.replicate (k - 1) .L) (by simp) (by simpa using mem_ASL_utp_HL_replicate (k - 1))
    (by simpa using mem_ASL_utp_replicate_H (k - 1)))

theorem ASL_utp_visible :
    ∀ a : Sym, ∃ u v, ¬ (u ++ a :: v ∈ ASL utpGrammar ↔ u ++ v ∈ ASL utpGrammar)
  | .H => ⟨[.H, .L], [], by decide⟩
  | .L => ⟨[.H], [.H], by decide⟩
  | .F => ⟨[], [], by decide⟩

/-- `L_UTP` is not tier-based strictly local at any width (Theorem 3). -/
theorem not_isTierStrictlyLocal_ASL_utp (k : ℕ) : ¬ (ASL utpGrammar).IsTierStrictlyLocal k :=
  fun h => not_isStrictlyLocal_ASL_utp k (h.isStrictlyLocal ASL_utp_visible)

end Jardine2019
