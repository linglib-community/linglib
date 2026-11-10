module

public import Studies.Blutner2000
public import Linglib.Pragmatics.NeoGricean.DivisionOfLabour

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
*not unhappy* [exactly when each negated form is the more complex of its
pair](##superoptimal_quadruplet_iff).

## Implementation notes

* A border is the set of degrees above it, the extension of *happy*, and literal meanings are the
  substrate's `AntonymForm.denotation` on it and its complement. The admissible borders are a
  family `Θ` of such sets. Only the ordering of the regions uses the paper's linear scale, on which the
  borders are upper sets.
* Safe use is a restriction on use, not a truth value: at the speaker's own border `U` every
  form stays true or false of every degree, which is where the account parts from
  supervaluation. The family `Θ` is fixed, although the paper lets the limits of safe use be
  vague and negotiated in turn.
* The paper first derives the M principle by avoidance of synonymy, the complex form taking what
  the safe use of the simple one leaves of their shared literal meaning, the substrate's
  `AntonymForm.dividedUse`. The two border regions are defined that way, and [the two derivations
  agree](##degrees_eq_dividedUse). It then derives the principle in bidirectional optimality
  theory, stated as the fixed-point condition `BidirectionalOT.mem_superoptimalSet` and worked on McCawley's
  *kill* and *cause to die*, which is Blutner's schematic tableau. For the quadruplet it says only
  that each half is the configuration that triggers the M implicature; the game here is that
  evaluation on the four forms and four regions, two copies of the tableau that share no form and
  no region, with the product of form cost and region markedness as harmony.
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
* [fine-1975]
-/

@[expose] public section

namespace Krifka2007b

open BidirectionalOT Aristotelian

variable {D : Type*} {Θ : Set (Set D)} {U U₁ U₂ : Set D} {d d₁ d₂ : D} {f : AntonymForm}

/-! ### Safe use -/

/-- The safe uses of a pole (18) are the degrees in its extension under every admissible border,
so that speaker and addressee agree on them whichever border each sets. -/
def safe (Θ : Set (Set D)) (p : Polarity) : Set D := ⋂ U ∈ Θ, p • U

theorem mem_safe_positive : d ∈ safe Θ .positive ↔ ∀ U ∈ Θ, d ∈ U := Set.mem_iInter₂

theorem mem_safe_negative : d ∈ safe Θ .negative ↔ ∀ U ∈ Θ, d ∉ U := Set.mem_iInter₂

/-- The safe uses of *happy* and *unhappy* are contraries exactly when two borders are admissible,
which is what makes *neither happy nor unhappy* (21) consistent although the literal pair is
exhaustive, as the unconditional (22) shows. -/
theorem isContrary_safe_iff : IsContrary (safe Θ .positive) (safe Θ .negative) ↔ Θ.Nontrivial := by
  refine ⟨fun h ↦ ?_, fun ⟨U₁, h₁, U₂, h₂, hne⟩ ↦ ⟨Set.disjoint_left.2 fun d hp hn ↦
    mem_safe_negative.1 hn U₁ h₁ (mem_safe_positive.1 hp U₁ h₁),
      fun h ↦ hne (Set.ext fun d ↦ ?_)⟩⟩
  · obtain ⟨d, hd⟩ := (Set.ne_univ_iff_exists_notMem _).1 (mt codisjoint_iff.2 h.2)
    simp only [Set.sup_eq_union, Set.mem_union, mem_safe_positive, mem_safe_negative, not_or] at hd
    push Not at hd
    obtain ⟨⟨U₂, h₂, hd₂⟩, U₁, h₁, hd₁⟩ := hd
    exact ⟨U₁, h₁, U₂, h₂, fun heq ↦ hd₂ (heq ▸ hd₁)⟩
  · rcases h.eq_top.ge (Set.mem_univ d) with hp | hn
    · exact iff_of_true (mem_safe_positive.1 hp U₁ h₁) (mem_safe_positive.1 hp U₂ h₂)
    · exact iff_of_false (mem_safe_negative.1 hn U₁ h₁) (mem_safe_negative.1 hn U₂ h₂)

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

/-- The degrees of a region, given the admissible borders `Θ` and the speaker's border `U`: the
safe uses of the two simple forms, and between them what safe use leaves of their literal
meanings at `U`, which avoidance of synonymy gives to the negated forms (12). -/
def degrees (Θ : Set (Set D)) (U : Set D) : Region → Set D
  | .positive => safe Θ .positive
  | .plateauHigh => U \ safe Θ .positive
  | .plateauLow => Uᶜ \ safe Θ .negative
  | .negative => safe Θ .negative

-- (19)
theorem mem_degrees_plateauHigh : d ∈ plateauHigh.degrees Θ U ↔ d ∈ U ∧ ∃ V ∈ Θ, d ∉ V := by
  simp [degrees, mem_safe_positive]

-- (20)
theorem mem_degrees_plateauLow : d ∈ plateauLow.degrees Θ U ↔ d ∉ U ∧ ∃ V ∈ Θ, d ∈ V := by
  simp [degrees, mem_safe_negative]

theorem mem_iff_of_mem_degrees {r : Region} (hU : U ∈ Θ) (hd : d ∈ r.degrees Θ U) :
    d ∈ U ↔ plateauLow < r := by
  cases r
  · exact iff_of_true (mem_safe_positive.1 hd U hU) (by decide)
  · exact iff_of_true hd.1 (by decide)
  · exact iff_of_false hd.1 (by decide)
  · exact iff_of_false (mem_safe_negative.1 hd U hU) (by decide)

/-- On a linear scale whose borders are upper sets the regions lie in their order, so *unhappy*
reports a more severe state than *not happy* (9) and *not unhappy* a higher level of happiness
than *not happy* (20). -/
theorem lt_of_mem_degrees [LinearOrder D] {r₁ r₂ : Region} (hΘ : ∀ V ∈ Θ, IsUpperSet V)
    (hU : U ∈ Θ) (h : r₁ < r₂) (h₁ : d₁ ∈ r₁.degrees Θ U) (h₂ : d₂ ∈ r₂.degrees Θ U) :
    d₁ < d₂ := by
  have key : ∀ V ∈ Θ, d₁ ∉ V → d₂ ∈ V → d₁ < d₂ := fun V hV hn hm ↦
    lt_of_not_ge fun hle ↦ hn (hΘ V hV hle hm)
  by_cases hr₁ : plateauLow < r₁ <;> by_cases hr₂ : plateauLow < r₂
  · obtain ⟨rfl, rfl⟩ : r₁ = plateauHigh ∧ r₂ = positive := by
      clear h₁ h₂; revert r₁ r₂; decide
    obtain ⟨V, hV, hn⟩ := (mem_degrees_plateauHigh.1 h₁).2
    exact key V hV hn (mem_safe_positive.1 h₂ V hV)
  · exact absurd (hr₁.trans h) hr₂
  · exact key U hU (mt (mem_iff_of_mem_degrees hU h₁).1 hr₁) ((mem_iff_of_mem_degrees hU h₂).2 hr₂)
  · obtain ⟨rfl, rfl⟩ : r₁ = negative ∧ r₂ = plateauLow := by
      clear h₁ h₂; revert r₁ r₂; decide
    obtain ⟨V, hV, hm⟩ := (mem_degrees_plateauLow.1 h₂).2
    exact key V hV (mem_safe_negative.1 h₁ V hV) hm

end Region

/-- The gap that safe use leaves between *happy* and *unhappy* consists of the two border regions,
so no part of it is left to a form meaning neither. -/
theorem compl_safe_union (hU : U ∈ Θ) :
    (safe Θ .positive ∪ safe Θ .negative)ᶜ =
      Region.plateauLow.degrees Θ U ∪ Region.plateauHigh.degrees Θ U := by
  ext d
  simp only [Set.mem_compl_iff, Set.mem_union, not_or, Region.degrees, Set.mem_sdiff]
  refine ⟨fun ⟨hp, hn⟩ ↦ (em (d ∈ U)).elim (fun h ↦ .inr ⟨h, hp⟩) fun h ↦ .inl ⟨h, hn⟩, ?_⟩
  rintro (⟨h, hn⟩ | ⟨h, hp⟩)
  · exact ⟨fun hp ↦ h (mem_safe_positive.1 hp U hU), hn⟩
  · exact ⟨hp, fun hn ↦ mem_safe_negative.1 hn U hU h⟩

-- (20)
theorem mem_degrees_plateau_of_mem_of_notMem (h₁ : U₁ ∈ Θ) (h₂ : U₂ ∈ Θ) (hd₁ : d ∈ U₁)
    (hd₂ : d ∉ U₂) : d ∈ Region.plateauHigh.degrees Θ U₁ ∩ Region.plateauLow.degrees Θ U₂ :=
  ⟨Region.mem_degrees_plateauHigh.2 ⟨hd₁, U₂, h₂, hd₂⟩,
    Region.mem_degrees_plateauLow.2 ⟨hd₂, U₁, h₁, hd₁⟩⟩

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
  Finset.univ.filter fun p ↦ p.2 ∈ p.1.denotation (· • Set.Ioi Region.plateauLow)

theorem mem_quadrupletPairs_iff {r : Region} (hU : U ∈ Θ) (hd : d ∈ r.degrees Θ U) :
    (f, r) ∈ quadrupletPairs ↔ d ∈ f.denotation (· • U) := by
  have h := Region.mem_iff_of_mem_degrees hU hd
  cases f <;> simp [quadrupletPairs, AntonymForm.denotation, h]

/-- Krifka's assignment gives the simple forms the safe regions and the complex forms the border
regions on their side. -/
def krifkaQuadruplet : Finset (AntonymForm × Region) :=
  {(.positive, .positive), (.notNegative, .plateauHigh),
    (.negative, .negative), (.notPositive, .plateauLow)}

/-- Avoidance of synonymy and weak optimality agree: the region the assignment gives a form holds
the degrees the division of labour leaves it, with safe use as the stereotype (12). -/
theorem degrees_eq_dividedUse {r : Region} (h : (f, r) ∈ krifkaQuadruplet) :
    r.degrees Θ U = AntonymForm.dividedUse (· • U) (safe Θ) f := by
  simp only [krifkaQuadruplet, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [Region.degrees, AntonymForm.dividedUse, AntonymForm.denotation]

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

/-- Weak optimality gives each simple form the safe region and each negated form the border
region ((19), (20)) exactly when each negated form costs more than the simple form of the other
pole: *not unhappy* than *happy*, which the paper takes to be clear, and *not happy* than
*unhappy*, for which it argues that syntactic complexity outweighs morphological. -/
theorem superoptimal_quadruplet_iff (c : AntonymForm → ℕ) :
    superoptimal quadrupletPairs (Prod.map c Region.markedness) = krifkaQuadruplet ↔
      c .positive < c .notNegative ∧ c .negative < c .notPositive := by
  refine ⟨fun h ↦ ?_, fun ⟨hp, hn⟩ ↦ ?_⟩
  · have key : ∀ p ∈ quadrupletPairs, p ∉ krifkaQuadruplet →
        Blocks Competes (Prod.map c Region.markedness) ↑quadrupletPairs p := fun p hp hk ↦
      not_not.1 fun hb ↦
        hk (h ▸ strongOptimal_subset_superoptimal _ _ (mem_strongOptimal.2 ⟨hp, hb⟩))
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨a, r⟩, hq, hc, hlt⟩ := key (.notNegative, .positive) (by decide) (by decide)
      cases a <;> cases r <;> first
        | exact absurd (Finset.mem_coe.1 hq) (by decide)
        | (simp_all [Region.markedness, Competes, Prod.lt_iff])
    · obtain ⟨⟨a, r⟩, hq, hc, hlt⟩ := key (.notPositive, .negative) (by decide) (by decide)
      cases a <;> cases r <;> first
        | exact absurd (Finset.mem_coe.1 hq) (by decide)
        | (simp_all [Region.markedness, Competes, Prod.lt_iff])
  · have hsep : ∀ p ∈ Prod.map (form .positive) (region .positive) '' Set.univ,
        ∀ q ∈ Prod.map (form .negative) (region .negative) '' Set.univ, ¬ Competes p q := by
      rintro _ ⟨⟨a, b⟩, -, rfl⟩ _ ⟨⟨c, d⟩, -, rfl⟩
      revert a b c d
      decide
    have hpos : StrictMono (Prod.map c Region.markedness ∘
        Prod.map (form .positive) (region .positive)) :=
      (strictMono_form (g := c ∘ form .positive) hp).prodMap
        (strictMono_situation (g := Region.markedness ∘ region .positive) (by decide))
    have hneg : StrictMono (Prod.map c Region.markedness ∘
        Prod.map (form .negative) (region .negative)) :=
      (strictMono_form (g := c ∘ form .negative) hn).prodMap
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
