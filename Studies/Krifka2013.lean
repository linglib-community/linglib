module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Krifka (2013): Definitional Generics

This file formalizes [krifka-2013]'s distinction between descriptive and definitional generic
sentences. *Madrigals are popular* generalizes about the world; *A madrigal is polyphonic* says
how the word *madrigal* is to be interpreted, which is why an accidental property makes an
indefinite-singular generic odd (*#A madrigal is popular*). Meaning depends on two indices, an
interpretation and a world, and a common ground pairs a set of admissible interpretations with
a set of worlds (`CommonGround`). A descriptive update keeps the interpretations and discards
worlds (`descUpdate`); a definitional update keeps the worlds and discards interpretations
(`defUpdate`), and with a topic-comment structure it restricts only the interpretation of the
definiendum (`defUpdateTopic`). Two further claims are theorems: admissible interpretations
stay convex under a definitional update whose proposition is convex in the interpretation
(`ordConnected_defUpdate`), and a definitional generic can rest on an empirical finding: once
a species rule ties the chromosome number to being a donkey, the descriptive update with
Chiquita's count leaves the definitional update with *A donkey has 62 chromosomes* nothing to
do (`defUpdateTopic_descUpdate`).

## Implementation notes

* Common grounds carry finite sets so that the paper's models are decided, and the updates
  take decidable propositions.
* The species rule is stated per interpretation; the chromosome count is a measure and so the
  same under every interpretation; and Chiquita, a specimen, is a donkey under every admissible
  interpretation.
* The paper's data are in `Data/Examples/Krifka2013.json`. The correlation of subject form
  with reading, which the paper leaves as a tendency, is not formalized.

## TODO

* The paper's definitional update with *Feynman is tall* and *Teller is not tall* is meant to
  leave the middle standard, but with the heights it lists Teller is tall under that standard in
  the first world, so the update as printed leaves no standard; the descriptive update with
  *Feynman is tall* is computed instead.

## References

* [krifka-2013]
* [barker-2002-vagueness] — the descriptive and metalinguistic uses of *tall*
* [cohen-2001] — the rule types of indefinite-singular generics
* [greenberg-2007], [kripke-1980] — in-virtue-of generics; necessity a posteriori
-/

@[expose] public section

namespace Krifka2013

variable {I W X : Type*}

/-- A common ground (§3.1): the admissible interpretations and the possible worlds. -/
@[ext]
structure CommonGround (I W : Type*) where
  interps : Finset I
  worlds : Finset W
  deriving DecidableEq

namespace CommonGround

variable (cg : CommonGround I W) (φ : I → W → Prop) [∀ i w, Decidable (φ i w)]

/-- A descriptive update (14): keep the worlds in which the proposition holds under some
admissible interpretation. -/
def descUpdate : CommonGround I W :=
  ⟨cg.interps, cg.worlds.filter λ w => ∃ i ∈ cg.interps, φ i w⟩

/-- A definitional update (15): keep the interpretations under which the proposition holds in
every world. -/
def defUpdate : CommonGround I W :=
  ⟨cg.interps.filter λ i => ∀ w ∈ cg.worlds, φ i w, cg.worlds⟩

/-- A definitional update with a predicative topic (25): keep the interpretations of the
definiendum `α` under which whatever falls under it satisfies the definiens `β` under every
admissible interpretation. -/
def defUpdateTopic [Fintype X] (α β : I → W → X → Prop) [∀ i w x, Decidable (α i w x)]
    [∀ i w x, Decidable (β i w x)] : CommonGround I W :=
  ⟨cg.interps.filter λ i => ∀ w ∈ cg.worlds, ∀ x, α i w x → ∀ i' ∈ cg.interps, β i' w x,
    cg.worlds⟩

@[simp] theorem interps_descUpdate : (cg.descUpdate φ).interps = cg.interps := rfl

@[simp] theorem worlds_defUpdate : (cg.defUpdate φ).worlds = cg.worlds := rfl

theorem worlds_descUpdate_subset : (cg.descUpdate φ).worlds ⊆ cg.worlds :=
  Finset.filter_subset _ _

theorem interps_defUpdate_subset : (cg.defUpdate φ).interps ⊆ cg.interps :=
  Finset.filter_subset _ _

/-- A convex definitional update keeps a convex set of admissible interpretations convex (§3.1). -/
theorem ordConnected_defUpdate [Preorder I] (hI : (↑cg.interps : Set I).OrdConnected)
    (hφ : ∀ w ∈ cg.worlds, {i | φ i w}.OrdConnected) :
    (↑(cg.defUpdate φ).interps : Set I).OrdConnected := by
  refine ⟨λ x hx y hy z hz => ?_⟩
  simp only [defUpdate, Finset.coe_filter] at hx hy ⊢
  exact ⟨hI.out hx.1 hy.1 hz, λ w hw => (hφ w hw).out (hx.2 w hw) (hy.2 w hw) hz⟩

/-- With the species rule (33) in the common ground, the descriptive update with Chiquita's
chromosome count settles the definitional update ((31)–(36)). -/
theorem defUpdateTopic_descUpdate [Fintype X] (donkey : I → W → X → Prop)
    [∀ i w x, Decidable (donkey i w x)] (chrom : I → W → X → ℕ) (ch : X) (n : ℕ)
    (hrule : ∀ i ∈ cg.interps, ∀ w ∈ cg.worlds, ∀ x y, donkey i w x → donkey i w y →
      chrom i w x = chrom i w y)
    (hchrom : ∀ i i' w x, chrom i w x = chrom i' w x)
    (hch : ∀ i ∈ cg.interps, ∀ w ∈ cg.worlds, donkey i w ch) :
    (cg.descUpdate λ i w => chrom i w ch = n ∧ donkey i w ch).defUpdateTopic donkey
        (λ i w x => chrom i w x = n) =
      cg.descUpdate λ i w => chrom i w ch = n ∧ donkey i w ch := by
  refine CommonGround.ext (Finset.filter_true_of_mem λ i hi w hw x hx i' _ => ?_) rfl
  obtain ⟨hwW, i₀, _, hn, _⟩ := Finset.mem_filter.1 hw
  rw [hchrom i' i, hrule i hi w hwW x ch hx (hch i hi w hwW), hchrom i i₀, hn]

end CommonGround

/-! ### Tall, popular, polyphonic -/

/-- Three interpretations, or three worlds. -/
abbrev Idx := Fin 3

/-- The standards of tallness of (16), in centimetres. -/
def standard : Idx → ℕ
  | 0 => 190
  | 1 => 180
  | 2 => 170

/-- Feynman's height in each world of (16). -/
def feynman : Idx → ℕ
  | 0 => 195
  | 1 => 185
  | 2 => 175

/-- *Feynman is tall* under a standard, in a world. -/
abbrev feynmanTall (i w : Idx) : Prop := standard i ≤ feynman w

-- (17)
theorem descUpdate_feynmanTall :
    (CommonGround.mk {0, 1} Finset.univ).descUpdate feynmanTall = ⟨{0, 1}, {0, 1}⟩ := by
  decide

/-- The initial common ground of (20) and (21). -/
def cg₀ : CommonGround Idx Idx := ⟨Finset.univ, Finset.univ⟩

/-- *Madrigals are popular* holds in the first two worlds under every interpretation. -/
abbrev popular (_ w : Idx) : Prop := w ≠ 2

/-- *Madrigals are polyphonic* holds under the first two interpretations in every world. -/
abbrev polyphonic (i _ : Idx) : Prop := i ≠ 2

-- (20)
theorem descUpdate_popular : cg₀.descUpdate popular = ⟨Finset.univ, {0, 1}⟩ := by decide

-- (21)
theorem defUpdate_polyphonic : cg₀.defUpdate polyphonic = ⟨{0, 1}, Finset.univ⟩ := by decide

end Krifka2013
