module

public import Studies.Blutner2000
public import Linglib.Semantics.Degree.Antonymy

/-!
# Krifka (2007): Negated Antonyms: Creating and Filling the Gap

Krifka accounts for antonym quadruplets such as *happy*, *not happy*, *unhappy*, *not unhappy*,
and in particular for the double negative, which reports a mild state of happiness rather than
the whole middle ground that Horn's contrary analysis leaves it. The border between *happy* and
*unhappy* is sharp but not agreed on, as on Williamson's epistemic view of vagueness, and the pair
is literally contradictory. Speakers use a simple form only where every admissible border makes it
true, so the pair [is used as contraries exactly when the border is open](##isContrary_safe_iff).
The gap this creates [divides at the speaker's border](##compl_safe_union) into a lower and an
upper region, [ordered along the scale](##Region.lt_of_mem_degrees) between the two safe ones, and
bidirectional optimality theory, read on [the literal meanings of the four
regions](##mem_quadrupletPairs_iff), gives the lower one to *not happy* and the upper one to
*not unhappy* [exactly when *not* costs more than *un-*](##superoptimal_quadruplet_iff).

## Implementation notes

* Literal meanings are the substrate's single-threshold `AntonymForm.contradictoryDenotation`. The
  admissible borders are a set `Θ` of thresholds on a linear order, and the two middle regions
  are read relative to the speaker's own border `θ`, as the alternative bracketings of the paper's
  diagrams are.
* The paper states weak optimality as the fixed-point condition
  `BidirectionalOT.mem_superoptimalSet` and works it on McCawley's *kill* and *cause to die*,
  which is Blutner's schematic tableau.
  For the quadruplet it says only that each half is the configuration that triggers the M
  implicature; the game here is that evaluation on the four forms and four regions, two copies of
  the tableau that share no form and no region, with the product of form cost and region
  markedness as harmony, no ranking between the two.
* The other uses of double negatives the paper sets aside (denial, irony, amplification) and
  the local strengthening of *neither happy nor unhappy* are not formalized.

## References

* [krifka-2007b]
* [horn-1989]
* [williamson-1994]
* [levinson-2000]
* [mccawley-1978]
* [blutner-2000]
* [blutner-2004]
* [jaeger-2002]
-/

@[expose] public section

namespace Krifka2007b

open BidirectionalOT Aristotelian

variable {D : Type*} [LinearOrder D] {Θ : Set D} {θ θ₁ θ₂ d d₁ d₂ : D} {f : AntonymForm}

/-! ### Safe use -/

/-- At a border `θ` antonyms literally denote contradictories (16). -/
abbrev literal (θ : D) (f : AntonymForm) : Set D := AntonymForm.contradictoryDenotation θ f

/-- The safe uses of a form (18) are the degrees at which it is true under every admissible border,
so that speaker and addressee agree on it whichever border each sets. -/
def safe (Θ : Set D) (f : AntonymForm) : Set D := ⋂ θ ∈ Θ, literal θ f

theorem mem_safe : d ∈ safe Θ f ↔ ∀ θ ∈ Θ, d ∈ literal θ f := Set.mem_iInter₂

theorem safe_subset_literal (hθ : θ ∈ Θ) : safe Θ f ⊆ literal θ f := Set.biInter_subset_of_mem hθ

/-- The safe uses of *happy* and *unhappy* are contraries exactly when two borders are admissible:
an agreed border leaves the pair contradictory, as in the unconditional (22), and an open one
makes *neither happy nor unhappy* (21) consistent. -/
theorem isContrary_safe_iff : IsContrary (safe Θ .positive) (safe Θ .negative) ↔ Θ.Nontrivial := by
  rw [Set.nontrivial_iff_exists_lt]
  refine ⟨fun h ↦ ?_, fun ⟨θ₁, h₁, θ₂, h₂, hlt⟩ ↦ ⟨Set.disjoint_left.2 fun d hp hn ↦
    (mem_safe.1 hn θ₁ h₁).not_gt (mem_safe.1 hp θ₁ h₁), fun h ↦ ?_⟩⟩
  · obtain ⟨d, hd⟩ := (Set.ne_univ_iff_exists_notMem _).1 (mt codisjoint_iff.2 h.2)
    simp only [Set.sup_eq_union, Set.mem_union, mem_safe, not_or, not_forall] at hd
    obtain ⟨⟨θ₂, h₂, hd₂⟩, θ₁, h₁, hd₁⟩ := hd
    exact ⟨θ₁, h₁, θ₂, h₂, (not_le.1 hd₁).trans_le (not_lt.1 hd₂)⟩
  · exact (h.eq_top.ge (Set.mem_univ θ₂)).elim (fun hp ↦ lt_irrefl _ (mem_safe.1 hp θ₂ h₂))
      fun hn ↦ hlt.not_ge (mem_safe.1 hn θ₁ h₁)

/-! ### The four regions -/

/-- After strengthening ((18)–(20)) the scale divides into the regions safely happy, mildly
happy, mildly unhappy and safely unhappy. -/
inductive Region
  | positive
  | plateauHigh
  | plateauLow
  | negative
  deriving DecidableEq, Repr, Fintype

namespace Region

/-- The position of a region on the scale, from safely unhappy up to safely happy. -/
def rank : Region → ℕ
  | .negative => 0
  | .plateauLow => 1
  | .plateauHigh => 2
  | .positive => 3

instance : LinearOrder Region := LinearOrder.lift' rank (by decide)

/-- Mirror image of a region under the polarity flip. -/
def flip : Region → Region
  | .positive => .negative
  | .negative => .positive
  | .plateauHigh => .plateauLow
  | .plateauLow => .plateauHigh

@[simp] theorem flip_flip (r : Region) : r.flip.flip = r := by cases r <;> rfl

/-- The border regions are the non-stereotypical interpretations, those on which the simple form
is true but not safe. -/
def markedness : Region → ℕ
  | .plateauHigh | .plateauLow => 1
  | .positive | .negative => 0

/-- The degrees of a region, given the admissible borders `Θ` and the speaker's border `θ`: the
safe uses of the two simple forms, and between them what is left of their literal meanings at
`θ`. -/
def degrees (Θ : Set D) (θ : D) : Region → Set D
  | .positive => safe Θ .positive
  | .plateauHigh => literal θ .positive \ safe Θ .positive
  | .plateauLow => literal θ .negative \ safe Θ .negative
  | .negative => safe Θ .negative

-- (19)
theorem mem_degrees_plateauHigh : d ∈ plateauHigh.degrees Θ θ ↔ θ < d ∧ ∃ θ' ∈ Θ, d ≤ θ' := by
  simp [degrees, mem_safe, AntonymForm.contradictoryDenotation]

-- (20)
theorem mem_degrees_plateauLow : d ∈ plateauLow.degrees Θ θ ↔ d ≤ θ ∧ ∃ θ' ∈ Θ, θ' < d := by
  simp [degrees, mem_safe, AntonymForm.contradictoryDenotation]

theorem lt_iff_of_mem_degrees {r : Region} (hθ : θ ∈ Θ) (hd : d ∈ r.degrees Θ θ) :
    θ < d ↔ plateauLow < r := by
  cases r
  · exact iff_of_true (mem_safe.1 hd θ hθ) (by decide)
  · exact iff_of_true hd.1 (by decide)
  · exact iff_of_false (not_lt.2 hd.1) (by decide)
  · exact iff_of_false (not_lt.2 (mem_safe.1 hd θ hθ)) (by decide)

/-- The regions lie along the scale in their order, so *unhappy* reports a more severe state than
*not happy* (9) and *not unhappy* a higher level of happiness than *not happy* (20). -/
theorem lt_of_mem_degrees {r₁ r₂ : Region} (hθ : θ ∈ Θ) (h : r₁ < r₂)
    (h₁ : d₁ ∈ r₁.degrees Θ θ) (h₂ : d₂ ∈ r₂.degrees Θ θ) : d₁ < d₂ := by
  by_cases hr₁ : plateauLow < r₁ <;> by_cases hr₂ : plateauLow < r₂
  · obtain ⟨rfl, rfl⟩ : r₁ = plateauHigh ∧ r₂ = positive := by
      clear h₁ h₂; revert r₁ r₂; decide
    obtain ⟨θ', hθ', hle⟩ := (mem_degrees_plateauHigh.1 h₁).2
    exact hle.trans_lt (mem_safe.1 h₂ θ' hθ')
  · exact absurd (hr₁.trans h) hr₂
  · exact (not_lt.1 (mt (lt_iff_of_mem_degrees hθ h₁).1 hr₁)).trans_lt
      ((lt_iff_of_mem_degrees hθ h₂).2 hr₂)
  · obtain ⟨rfl, rfl⟩ : r₁ = negative ∧ r₂ = plateauLow := by
      clear h₁ h₂; revert r₁ r₂; decide
    obtain ⟨θ', hθ', hlt⟩ := (mem_degrees_plateauLow.1 h₂).2
    exact (mem_safe.1 h₁ θ' hθ').trans_lt hlt

end Region

/-- The gap that safe use leaves between *happy* and *unhappy* consists of the two border regions,
so no part of it is left to a form meaning neither. -/
theorem compl_safe_union (hθ : θ ∈ Θ) :
    (safe Θ .positive ∪ safe Θ .negative)ᶜ =
      Region.plateauLow.degrees Θ θ ∪ Region.plateauHigh.degrees Θ θ := by
  ext d
  simp only [Set.mem_compl_iff, Set.mem_union, not_or, Region.degrees, Set.mem_sdiff]
  refine ⟨fun ⟨hp, hn⟩ ↦ (lt_or_ge θ d).elim (fun h ↦ .inr ⟨h, hp⟩) fun h ↦ .inl ⟨h, hn⟩, ?_⟩
  rintro (⟨h, hn⟩ | ⟨h, hp⟩)
  · exact ⟨fun hp ↦ (safe_subset_literal hθ hp).not_ge h, hn⟩
  · exact ⟨hp, fun hn ↦ (safe_subset_literal hθ hn).not_gt h⟩

-- (20)
theorem mem_degrees_plateau_of_lt (h₁ : θ₁ ∈ Θ) (h₂ : θ₂ ∈ Θ) (hlt : θ₁ < θ₂) :
    θ₂ ∈ Region.plateauHigh.degrees Θ θ₁ ∩ Region.plateauLow.degrees Θ θ₂ :=
  ⟨Region.mem_degrees_plateauHigh.2 ⟨hlt, θ₂, h₂, le_rfl⟩,
    Region.mem_degrees_plateauLow.2 ⟨le_rfl, θ₁, h₁, hlt⟩⟩

/-! ### The M principle in bidirectional optimality theory -/

-- (13)–(15)
theorem superoptimal_mccawley :
    superoptimalSet Set.univ
        (Prod.map Blutner2000.Form.markedness Blutner2000.Situation.markedness) =
      {(.unmarked, .stereotypical), (.marked, .marked)} :=
  Blutner2000.superoptimalSet_eq_iconic <|
    StrictMono.prodMap (fun _ _ h ↦ h) fun _ _ h ↦ h

/-- The generator of the quadruplet pairs a form with the regions where it is literally true (16),
the border lying between the mildly unhappy and the mildly happy region. -/
def quadrupletPairs : Finset (AntonymForm × Region) :=
  Finset.univ.filter fun p ↦ p.2 ∈ literal Region.plateauLow p.1

/-- The generator is the literal semantics of the scale: it pairs a form with a region iff the form
is true, at the speaker's border, of the region's degrees. -/
theorem mem_quadrupletPairs_iff {r : Region} (hθ : θ ∈ Θ) (hd : d ∈ r.degrees Θ θ) :
    (f, r) ∈ quadrupletPairs ↔ d ∈ literal θ f := by
  have h := Region.lt_iff_of_mem_degrees hθ hd
  have h' : d ≤ θ ↔ r ≤ Region.plateauLow := by rw [← not_lt, ← not_lt, h]
  cases f <;> simp [quadrupletPairs, AntonymForm.contradictoryDenotation, h, h']

/-- Krifka's assignment gives the simple forms the safe regions and the complex forms the border
regions on their side. -/
def krifkaQuadruplet : Finset (AntonymForm × Region) :=
  {(.positive, .positive), (.notNegative, .plateauHigh),
    (.negative, .negative), (.notPositive, .plateauLow)}

/-- The two forms with a pole's literal meaning, its simple form and the negated form of the other
pole. -/
def form : Polarity → Blutner2000.Form → AntonymForm
  | .positive, .unmarked => .positive
  | .positive, .marked => .notNegative
  | .negative, .unmarked => .negative
  | .negative, .marked => .notPositive

/-- The two regions of a pole's literal meaning, the safe one and the border one. -/
def region : Polarity → Blutner2000.Situation → Region
  | .positive, .stereotypical => .positive
  | .positive, .marked => .plateauHigh
  | .negative, .stereotypical => .negative
  | .negative, .marked => .plateauLow

theorem form_injective (e : Polarity) : Function.Injective (form e) := by
  cases e <;> decide

theorem region_injective (e : Polarity) : Function.Injective (region e) := by
  cases e <;> decide

theorem coe_quadrupletPairs :
    (↑quadrupletPairs : Set (AntonymForm × Region)) =
      Prod.map (form .positive) (region .positive) '' Set.univ ∪
        Prod.map (form .negative) (region .negative) '' Set.univ := by
  ext ⟨a, r⟩
  simp only [quadrupletPairs, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
    Set.image_univ, Set.mem_union, Set.mem_range, Prod.exists, Prod.map_apply, Prod.mk.injEq]
  revert a r
  decide

private theorem strictMono_form {α : Type*} [Preorder α] {g : Blutner2000.Form → α}
    (h : g .unmarked < g .marked) : StrictMono g := fun a b hab ↦ by
  cases a <;> cases b <;> first | exact h | exact absurd hab (by decide)

private theorem strictMono_situation {α : Type*} [Preorder α] {g : Blutner2000.Situation → α}
    (h : g .stereotypical < g .marked) : StrictMono g := fun a b hab ↦ by
  cases a <;> cases b <;> first | exact h | exact absurd hab (by decide)

local instance : DecidableLT (ℕ × ℕ) := fun _ _ ↦ decidable_of_iff _ Prod.lt_iff.symm

/-- With sentential negation costing `n` and the negative prefix `k`, weak optimality gives each
simple form the safe region and each negated form the border region ((19), (20)) exactly when the
prefix is the cheaper, the assumption the paper makes for *unhappy* and *not happy*. -/
theorem superoptimal_quadruplet_iff (n k : ℕ) :
    superoptimal quadrupletPairs (Prod.map (AntonymForm.cost n k) Region.markedness) =
      krifkaQuadruplet ↔ k < n := by
  refine ⟨fun h ↦ not_le.1 fun hnk ↦ ?_, fun hk ↦ ?_⟩
  · have hmem : (AntonymForm.notPositive, Region.negative) ∈ krifkaQuadruplet :=
      h ▸ strongOptimal_subset_superoptimal _ _ (mem_strongOptimal.2 ⟨by decide, ?_⟩)
    · exact absurd hmem (by decide)
    · rintro ⟨⟨a, r⟩, hq, hc, hlt⟩
      cases a <;> cases r <;> first
        | exact absurd (Finset.mem_coe.1 hq) (by decide)
        | (simp_all [AntonymForm.cost, Region.markedness, Competes, Prod.lt_iff]; try omega)
  · have hsep : ∀ p ∈ Prod.map (form .positive) (region .positive) '' Set.univ,
        ∀ q ∈ Prod.map (form .negative) (region .negative) '' Set.univ, ¬ Competes p q := by
      rintro _ ⟨⟨a, b⟩, -, rfl⟩ _ ⟨⟨c, d⟩, -, rfl⟩
      revert a b c d
      decide
    have hpos : StrictMono (Prod.map (AntonymForm.cost n k) Region.markedness ∘
        Prod.map (form .positive) (region .positive)) :=
      (strictMono_form (g := AntonymForm.cost n k ∘ form .positive)
        (show 0 < n + k by omega)).prodMap
          (strictMono_situation (g := Region.markedness ∘ region .positive) (by decide))
    have hneg : StrictMono (Prod.map (AntonymForm.cost n k) Region.markedness ∘
        Prod.map (form .negative) (region .negative)) :=
      (strictMono_form (g := AntonymForm.cost n k ∘ form .negative) hk).prodMap
        (strictMono_situation (g := Region.markedness ∘ region .negative) (by decide))
    rw [← Finset.coe_inj, coe_superoptimal, coe_quadrupletPairs,
      superoptimalSet_union (Set.toFinite _).isWF hsep,
      superoptimalSet_image (form_injective _) (region_injective _) _ (Set.toFinite _).isWF,
      superoptimalSet_image (form_injective _) (region_injective _) _ (Set.toFinite _).isWF,
      Blutner2000.superoptimalSet_eq_iconic hpos, Blutner2000.superoptimalSet_eq_iconic hneg]
    ext ⟨a, r⟩
    simp only [Set.image_pair, Prod.map_apply, form, region, krifkaQuadruplet, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

end Krifka2007b
