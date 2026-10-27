module

public import Mathlib.Data.Fintype.Prod
public import Linglib.Semantics.Degree.Antonymy
public import Linglib.Pragmatics.Bidirectional

/-!
# Krifka (2007): Negated Antonyms: Creating and Filling the Gap

Krifka accounts for antonym quadruplets such as *happy*, *not happy*, *unhappy*, *not unhappy*,
and in particular for the double negative, which reports a mild state of happiness rather than
the middle ground that Horn's contrary analysis of antonyms predicts. The border between an
antonym pair is sharp but its location is not fixed, as on Williamson's epistemic view of
vagueness; the pair exhausts its scale, so *happy* and *unhappy* are literally contradictories;
and the M principle reserves the more complex of two equivalent expressions for the
non-stereotypical cases. Speakers use the simple forms only where every admissible border agrees,
which opens the gap, and the complex forms where the simple form is true at the speaker's border
but not safely usable, which fills it. The M principle is derived within Blutner's bidirectional
optimality theory on McCawley's *kill* example, and the same evaluation over the quadruplet
yields Krifka's assignment.

## Implementation notes

* Literal meanings are the substrate's single-threshold `AntonymForm.contradictoryDenotation`;
  the admissible borders form a set of thresholds on a linear order, and the diagrams are read
  relative to a speaker's border within that set.
* Bidirectional evaluation is the substrate's weak optimality, (14), which compares two pairs
  only when they share a form or an interpretation, by the preference ordering on the other: the
  product of the two orderings, with no ranking between them. The quadruplet game is built from
  the literal semantics (a form and a region on the same side of the border), form complexity
  (`AntonymForm.complexity`) and the markedness of the border regions.
* The other uses of double negatives the paper sets aside (denial, irony, amplification) and
  the local strengthening of *neither happy nor unhappy* are not formalized.

## References

* [krifka-2007b]
* [horn-1989]
* [horn-1984]
* [williamson-1994]
* [levinson-2000]
* [blutner-2000]
* [mccawley-1978]
-/

@[expose] public section

namespace Krifka2007b

open Degree BidirectionalOT

variable {D : Type*} [LinearOrder D]

/-! ### Safe and marked uses -/

/-- The simpler form with the same literal meaning is *happy* for *not unhappy* and *unhappy*
for *not happy*. -/
def simple : AntonymForm → AntonymForm
  | .notNegative => .positive
  | .notPositive => .negative
  | f => f

/-- At a border `θ` antonyms literally denote contradictories (16). -/
abbrev literal (θ : D) (f : AntonymForm) : Set D := AntonymForm.contradictoryDenotation θ f

/-- A use is safe (18) when it is true under every admissible border, so that speaker and
addressee agree on it whichever border they set. -/
def Safe (Θ : Set D) (f : AntonymForm) (d : D) : Prop := ∀ θ ∈ Θ, d ∈ literal θ f

/-- A use of a complex form is marked ((19), (20)) when it is literally true at the speaker's
border, where the simpler form with the same literal meaning is not safe. -/
def Marked (Θ : Set D) (θ : D) (f : AntonymForm) (d : D) : Prop :=
  d ∈ literal θ f ∧ ¬ Safe Θ (simple f) d

variable {Θ : Set D} {θ θ₁ θ₂ d d₁ d₂ : D}

-- (21), (22)
theorem literal_positive_or_negative (θ d : D) :
    d ∈ literal θ .positive ∨ d ∈ literal θ .negative :=
  lt_or_ge θ d

theorem not_safe_of_between (h₂ : θ₂ ∈ Θ) (h₁ : θ₁ ∈ Θ) (hd : θ₁ < d) (hd' : d ≤ θ₂) :
    ¬ Safe Θ .positive d ∧ ¬ Safe Θ .negative d :=
  ⟨fun h ↦ absurd (h θ₂ h₂) (not_lt.2 hd'), fun h ↦ absurd (h θ₁ h₁) (not_le.2 hd)⟩

-- (3), (19)
theorem marked_notNegative_iff : Marked Θ θ .notNegative d ↔ θ < d ∧ ∃ θ' ∈ Θ, d ≤ θ' := by
  refine and_congr Iff.rfl ⟨fun h ↦ ?_, fun ⟨θ', hθ', hle⟩ h ↦ absurd (h θ' hθ') (not_lt.2 hle)⟩
  by_contra hn
  exact h fun θ' hθ' ↦ lt_of_not_ge fun hle ↦ hn ⟨θ', hθ', hle⟩

-- (9), (20)
theorem marked_notPositive_iff : Marked Θ θ .notPositive d ↔ d ≤ θ ∧ ∃ θ' ∈ Θ, θ' < d := by
  refine and_congr Iff.rfl ⟨fun h ↦ ?_, fun ⟨θ', hθ', hlt⟩ h ↦ absurd (h θ' hθ') (not_le.2 hlt)⟩
  by_contra hn
  exact h fun θ' hθ' ↦ le_of_not_gt fun hlt ↦ hn ⟨θ', hθ', hlt⟩

-- (20)
theorem lt_of_marked (h₁ : Marked Θ θ .notPositive d₁) (h₂ : Marked Θ θ .notNegative d₂) :
    d₁ < d₂ :=
  lt_of_le_of_lt h₁.1 h₂.1

/-- Between two admissible borders a degree is *not unhappy* by the lower border and *not happy* by
the higher, so the two lack a fixed border (20). -/
theorem marked_both (h₁ : θ₁ ∈ Θ) (h₂ : θ₂ ∈ Θ) (hlt : θ₁ < θ₂) :
    Marked Θ θ₁ .notNegative θ₂ ∧ Marked Θ θ₂ .notPositive θ₂ :=
  ⟨marked_notNegative_iff.2 ⟨hlt, θ₂, h₂, le_rfl⟩, marked_notPositive_iff.2 ⟨le_rfl, θ₁, h₁, hlt⟩⟩

/-! ### The M principle in bidirectional optimality theory -/

/-- The two forms of (13), *Black Bart killed the sheriff* and *Black Bart caused the sheriff
to die*. -/
inductive Form
  | killed
  | causedToDie
  deriving DecidableEq, Fintype, Repr

/-- The two interpretations of (13), direct and indirect killing. -/
inductive Interp
  | direct
  | indirect
  deriving DecidableEq, Fintype, Repr

/-- The preference for the shorter form, F1 over F2. -/
def Form.complexity : Form → ℕ
  | .killed => 0
  | .causedToDie => 1

/-- The preference for the stereotypical interpretation, I1 over I2. -/
def Interp.markedness : Interp → ℕ
  | .direct => 0
  | .indirect => 1

instance : LinearOrder Form := LinearOrder.lift' Form.complexity (by decide)

instance : LinearOrder Interp := LinearOrder.lift' Interp.markedness (by decide)

/-- The M principle pairs the shorter form with the stereotypical interpretation and the longer
form with the other. -/
def mPairing : Form ≃o Interp where
  toFun | .killed => .direct | .causedToDie => .indirect
  invFun | .direct => .killed | .indirect => .causedToDie
  left_inv a := by cases a <;> rfl
  right_inv b := by cases b <;> rfl
  map_rel_iff' {a b} := by cases a <;> cases b <;> decide

/-- Under weak optimality ((14), (15)), *kill* pairs with direct and *cause to die* with indirect
killing. -/
theorem superoptimal_mccawley :
    superoptimalSet Set.univ (Prod.map Form.complexity Interp.markedness) =
      {(.killed, .direct), (.causedToDie, .indirect)} := by
  have hF : StrictMono Form.complexity := fun _ _ h ↦ h
  have hI : StrictMono Interp.markedness := fun _ _ h ↦ h
  rw [superoptimalSet_eq_graphOn _ mPairing (hF.prodMap hI) Set.finite_univ.isWF
    (Set.subset_univ _)]
  ext ⟨a, b⟩
  simp only [Set.mem_graphOn, Set.mem_univ, true_and, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
  revert a b
  decide

/-- After strengthening ((18)–(20)) the scale divides into the regions safely happy, mildly
happy, mildly unhappy and safely unhappy. -/
inductive Region
  | positive
  | plateauHigh
  | plateauLow
  | negative
  deriving DecidableEq, Repr

/-- Mirror image of a region under the polarity flip. -/
def Region.flip : Region → Region
  | .positive => .negative
  | .negative => .positive
  | .plateauHigh => .plateauLow
  | .plateauLow => .plateauHigh

@[simp] theorem Region.flip_flip (r : Region) : r.flip.flip = r := by cases r <;> rfl

/-- The regions above the border. -/
def Region.above : Region → Bool
  | .positive | .plateauHigh => true
  | .plateauLow | .negative => false

/-- The border regions are the non-stereotypical interpretations. -/
def Region.markedness : Region → ℕ
  | .plateauHigh | .plateauLow => 1
  | .positive | .negative => 0

/-- The forms literally true above the border (16). -/
def formAbove : AntonymForm → Bool
  | .positive | .notNegative => true
  | .notPositive | .negative => false

/-- The literal semantics admits the pairs of a form and a region on the same side of the
border. -/
def quadrupletPairs : Finset (AntonymForm × Region) :=
  ([.positive, .notPositive, .negative, .notNegative].toFinset ×ˢ
      [.positive, .plateauHigh, .plateauLow, .negative].toFinset).filter
    fun p ↦ formAbove p.1 = p.2.above

/-- Krifka's assignment gives the simple forms the safe regions and the complex forms the border
regions on their side. -/
def krifkaQuadruplet : Finset (AntonymForm × Region) :=
  {(.positive, .positive), (.notNegative, .plateauHigh),
    (.negative, .negative), (.notPositive, .plateauLow)}

local instance : DecidableLT (ℕ × ℕ) := fun _ _ ↦ decidable_of_iff _ Prod.lt_iff.symm

/-- Weak optimality over the quadruplet, as in (14), gives each half's simpler form the safe region
and the more complex form the border region ((18)–(20)). -/
theorem superoptimal_quadruplet :
    superoptimal quadrupletPairs (Prod.map AntonymForm.complexity Region.markedness) =
      krifkaQuadruplet := by
  decide

end Krifka2007b
