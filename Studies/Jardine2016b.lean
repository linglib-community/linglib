/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Correspondence
public import Linglib.Data.Examples.Jardine2016b
public import Linglib.Data.Examples.Readers

/-!
# Jardine (2016): intervocalic voicing as a local string relation

This file formalizes chapter 7 of Jardine's dissertation, which presents a phonological process as a
relation between input and output strings: a set of correspondence graphs, carved out of GEN by
banned-subgraph constraints. Section 7.2 runs the idea on intervocalic voicing, (7.1), whose
relation over `a`, `b` and `p` is `Rvoice`, (7.5). The primitives Γ of (7.14), an input symbol
over its output, generate GEN by concatenation, (7.15) (`g`), and five banned subgraphs cut the
voicing relation out of it: φ_apa, (7.19), forbids a surface `apa`, and the four of (7.21) forbid
a `p` surfacing as `b` word-initially, word-finally, after a `p` and before a `p`. The grammar is
φ_apba, (7.22), and the relation it presents is `R(CG(φ_apba))`, Definition 25 (`voicing`): a
pair is in it iff the Γ-string spelling it, which is unique, is free of the grammar
(`voicing_iff_spell`), so membership decides, and on the pairs of (7.5) and (7.17) the relation
agrees with `Rvoice` (`rows_agree`).

## Implementation notes

* Correspondence graphs are `Autosegmental.Correspondence.Rep`; the word boundaries ⋊ and ⋉
  that (7.21) reads are symbols of the alphabet, and a Γ-string's graph is wrapped in them.
* `Rvoice` is written as the rule (7.1) applied pointwise, `voiceRule`, a `p` between two `a`s
  surfacing as `b`.

## Errata

* The text leaves to the reader that `R(CG(φ_apba)) = Rvoice`. The identity fails: no subgraph of
  (7.22) mentions a `b` beside the target, so the grammar [admits](##voicing_bpa_bba)
  `bpa ↦ bba`, which the rule (7.1) does not, and the two relations
  [differ](##voicing_ne_voiceRule).

## References

* [jardine-2016b]
-/

@[expose] public section

namespace Jardine2016b

open Autosegmental Correspondence

/-- Σ = ∆ = {a, b, p} of (7.1), with the word boundaries ⋊ (`lb`) and ⋉ (`rb`) that the
subgraphs of (7.21) read. -/
inductive Seg | a | b | p | lb | rb
  deriving DecidableEq, Repr

/-- The correspondence primitives Γ = {aa, pb, pp, bb} of (7.14) — an input symbol over its
output — with the boundary primitives ⋊ over ⋊ and ⋉ over ⋉. -/
inductive Pair | aa | pb | pp | bb | lb | rb
  deriving DecidableEq, Repr

namespace Pair

/-- The input symbol of a primitive. -/
def input : Pair → Seg
  | aa => .a | pb => .p | pp => .p | bb => .b | lb => .lb | rb => .rb

/-- The output symbol of a primitive. -/
def output : Pair → Seg
  | aa => .a | pb => .b | pp => .p | bb => .b | lb => .lb | rb => .rb

theorem ext {x y : Pair} (hi : x.input = y.input) (ho : x.output = y.output) : x = y := by
  cases x <;> cases y <;> simp_all [input, output]

theorem map_injective {γs γs' : List Pair} (hi : γs.map input = γs'.map input)
    (ho : γs.map output = γs'.map output) : γs = γs' := by
  induction γs generalizing γs' with
  | nil => exact (List.map_eq_nil_iff.mp hi.symm).symm
  | cons x xs ih =>
    cases γs' with
    | nil => simp at hi
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at hi ho
      rw [ext hi.1 ho.1, ih hi.2 ho.2]

/-- The primitive spelling an input symbol over an output symbol, if any. -/
def ofSegs : Seg → Seg → Option Pair
  | .a, .a => some aa
  | .p, .b => some pb
  | .p, .p => some pp
  | .b, .b => some bb
  | .lb, .lb => some lb
  | .rb, .rb => some rb
  | _, _ => none

theorem ofSegs_eq_some_iff {i o : Seg} {γ : Pair} :
    ofSegs i o = some γ ↔ γ.input = i ∧ γ.output = o := by
  cases i <;> cases o <;> cases γ <;> simp [ofSegs, input, output]

theorem ofSegs_input_output (γ : Pair) : ofSegs γ.input γ.output = some γ := by
  cases γ <;> rfl

end Pair

/-- The Γ-string spelling an input and an output string, if any. -/
def spell : List Seg → List Seg → Option (List Pair)
  | [], [] => some []
  | i :: w, o :: v =>
    match Pair.ofSegs i o, spell w v with
    | some γ, some γs => some (γ :: γs)
    | _, _ => none
  | _, _ => none

theorem spell_map (γs : List Pair) : spell (γs.map Pair.input) (γs.map Pair.output) = some γs := by
  induction γs with
  | nil => rfl
  | cons γ γs ih => simp [spell, ih, Pair.ofSegs_input_output]

theorem spell_eq_some {w v : List Seg} {γs : List Pair} (h : spell w v = some γs) :
    γs.map Pair.input = w ∧ γs.map Pair.output = v := by
  induction w generalizing v γs with
  | nil => cases v <;> cases γs <;> simp_all [spell]
  | cons i w ih =>
    cases v with
    | nil => simp [spell] at h
    | cons o v =>
      rw [spell] at h
      split at h
      · next γ γs' hγ hγs =>
        obtain rfl := Option.some.inj h
        obtain ⟨rfl, rfl⟩ := Pair.ofSegs_eq_some_iff.1 hγ
        simp [ih hγs]
      · exact absurd h (by simp)

theorem spell_eq_some_iff {w v : List Seg} {γs : List Pair} :
    spell w v = some γs ↔ γs.map Pair.input = w ∧ γs.map Pair.output = v :=
  ⟨spell_eq_some, fun ⟨hw, hv⟩ ↦ hw ▸ hv ▸ spell_map γs⟩

/-- Jardine's `g` on Γ-strings ((7.15)): the correspondence graph spelling the input and
output symbols position by position. -/
abbrev g (γs : List Pair) : Rep Seg Seg :=
  AR.ofWords (γs.map Pair.input) (γs.map Pair.output) (· = ·)

/-- A Γ-string's graph between the boundaries ⋊ and ⋉. -/
abbrev gen (γs : List Pair) : Rep Seg Seg := g (.lb :: γs ++ [.rb])

/-! ### The grammar φ_apba -/

/-- φ_apa (7.19): a surface `apa` — output-only, the markedness constraint *VTV. -/
abbrev banApa : Rep Seg Seg := AR.ofWords [] [.a, .p, .a] fun _ _ ↦ False

/-- φ_⋊pb (7.21): a `p` surfacing as `b` word-initially. -/
abbrev banInitialPb : Rep Seg Seg := AR.ofWords [.p] [.lb, .b] fun i o ↦ i = 0 ∧ o = 1

/-- φ_pb⋉ (7.21): a `p` surfacing as `b` word-finally. -/
abbrev banFinalPb : Rep Seg Seg := AR.ofWords [.p] [.b, .rb] fun i o ↦ i = 0 ∧ o = 0

/-- φ_ppb (7.21): a `p` surfacing as `b` after a surface `p`. -/
abbrev banPbAfterP : Rep Seg Seg := AR.ofWords [.p] [.p, .b] fun i o ↦ i = 0 ∧ o = 1

/-- φ_pbp (7.21): a `p` surfacing as `b` before a surface `p`. -/
abbrev banPbBeforeP : Rep Seg Seg := AR.ofWords [.p] [.b, .p] fun i o ↦ i = 0 ∧ o = 0

/-- φ_apba (7.22). -/
def voicingGrammar : List (Rep Seg Seg) :=
  [banApa, banInitialPb, banFinalPb, banPbAfterP, banPbBeforeP]

theorem free_voicingGrammar_iff (G : Rep Seg Seg) :
    G.Free voicingGrammar ↔
      ¬ banApa.FactorEmbeds G ∧ ¬ banInitialPb.FactorEmbeds G ∧ ¬ banFinalPb.FactorEmbeds G ∧
        ¬ banPbAfterP.FactorEmbeds G ∧ ¬ banPbBeforeP.FactorEmbeds G := by
  simp only [voicingGrammar, AR.free_cons, AR.free_nil, and_true]

/-- On GEN the grammar decides. -/
instance (γs : List Pair) : Decidable ((gen γs).Free voicingGrammar) :=
  decidable_of_iff _ (free_voicingGrammar_iff (gen γs)).symm

/-! ### The relation R(CG(φ_apba)) -/

/-- CG(φ_apba): the graphs of GEN = CG(Γ) free of the grammar. -/
def CG (G : Rep Seg Seg) : Prop := (∃ γs, G = gen γs) ∧ G.Free voicingGrammar

/-- R(CG(φ_apba)) (Def. 25), on boundary-augmented strings. -/
def voicing (w v : List Seg) : Prop := relRep CG (.lb :: w ++ [.rb]) (.lb :: v ++ [.rb])

-- Def. 25
theorem voicing_iff {w v : List Seg} :
    voicing w v ↔ ∃ γs, γs.map Pair.input = w ∧ γs.map Pair.output = v ∧
      (gen γs).Free voicingGrammar := by
  constructor
  · rintro ⟨G, ⟨⟨γs, rfl⟩, hφ⟩, hi, ho⟩
    refine ⟨γs, ?_, ?_, hφ⟩
    · simpa [Pair.input] using hi
    · simpa [Pair.output] using ho
  · rintro ⟨γs, rfl, rfl, hφ⟩
    exact ⟨gen γs, ⟨⟨γs, rfl⟩, hφ⟩, by simp [Pair.input], by simp [Pair.output]⟩

/-- Definition 25 holds of `(w, v)` iff its Γ-string spelling exists and its graph is free of the
grammar. -/
theorem voicing_iff_spell {w v : List Seg} :
    voicing w v ↔ ∃ γs, spell w v = some γs ∧ (gen γs).Free voicingGrammar := by
  simp only [voicing_iff, spell_eq_some_iff, and_assoc]

instance (w v : List Seg) : Decidable (voicing w v) :=
  decidable_of_iff _ voicing_iff_spell.symm

/-! ### The data of (7.5) and (7.17) -/

/-- A segment from its spelling. -/
def segOf : Char → Seg
  | 'a' => .a
  | 'b' => .b
  | _ => .p

/-- A row: an input and an output string, and whether the pair is in `Rvoice`. -/
structure Row where
  input : List Seg
  output : List Seg
  inRvoice : Bool
  deriving DecidableEq

/-- A row from the paper's features. -/
def Row.ofDatum (e : Datum) : Option Row := do
  let i ← e.feature? "input"
  let o ← e.feature? "output"
  let m ← e.feature? "in_rvoice"
  some ⟨i.toList.map segOf, o.toList.map segOf, m = "yes"⟩

/-- The pairs of `Rvoice`, (7.5), and the pairs of GEN outside it, (7.17). -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- The grammar's relation agrees with `Rvoice` on the paper's pairs ((7.5), (7.17), (7.18b),
(7.20)). -/
theorem rows_agree : ∀ r ∈ rows, voicing r.input r.output ↔ r.inRvoice = true := by decide

/-- The rule (7.1) pointwise: a `p` between two `a`s surfaces as `b`. -/
def voiceRule (w : List Seg) : List Seg :=
  w.mapIdx fun i x ↦
    if x = .p ∧ w[i - 1]? = some .a ∧ i ≠ 0 ∧ w[i + 1]? = some .a then .b else x

theorem voiceRule_rows : ∀ r ∈ rows, voiceRule r.input = r.output ↔ r.inRvoice = true := by
  decide

-- (7.22)
theorem voicing_bpa_bba : voicing [.b, .p, .a] [.b, .b, .a] := by decide

/-- The grammar's relation is not `Rvoice`, against the identity the text leaves to the reader:
the rule (7.1) leaves `bpa` unchanged. -/
theorem voicing_ne_voiceRule : ¬ ∀ w v, voicing w v ↔ voiceRule w = v :=
  fun h ↦ absurd ((h _ _).1 voicing_bpa_bba) (by decide)

end Jardine2016b
