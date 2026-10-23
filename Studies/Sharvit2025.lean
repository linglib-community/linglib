module

public import Linglib.Semantics.ConventionalImplicature
public import Linglib.Core.Order.Minimals
public import Linglib.Data.Examples.Sharvit2025

/-!
# Sharvit (2025): Rooth-Partee Conditionals and the Symmetry of Disjunction

This file formalizes the paper's case that *or* is inherently symmetric and its closest-worlds
theory of the connectives. A Rooth-Partee conditional, *If Mia is penniless or proud of her
money, then Sue is*, has an if-over-∃ reading, one conditional with a disjunctive antecedent,
and a ∀-over-if reading, one conditional per disjunct with the ellipsis matched to it; the second
reading presupposes that Sue has money if Mia does, and both readings survive swapping the
disjuncts. A disjunction that projects its left disjunct's presupposition, the K+ connective
under CON-asymmetry (16)–(17), cannot deliver this: swapping the disjuncts changes what the
antecedent presupposes (`orAsym_notAtIssue_ne`), and the paper argues that accommodation does
not repair it. Karttunen and Peters's symmetric disjunction (102) does
(`TwoDim.orKPSymmetric_comm`), but its Karttunen conditional presupposition, the consequent's
presupposition at the evaluation world if the antecedent is true there (100), is too weak for the
∀-over-if presupposition (`ifKP_notAtIssue_of_not_atIssue`), the Proviso Problem.

The proposal replaces the local presupposition by a closest-worlds one after Heim: a conditional
presupposes its consequent's presupposition at the closest antecedent-worlds of the epistemic
state (119), and conjunction and disjunction inherit the condition (127)–(128) (`clos`,
`ifKPstar`, `andKPstar`, `orKPstar`, symmetric by construction, `orKPstar_comm`). A
closest-worlds presupposition strengthens to an unconditional one wherever the laws in force
allow the antecedent without it (`presup_strengthens`, the reasoning of (122)). For the
∀-over-if reading the conditional must quantify over the properties the antecedent disjoins
(142), since a conditional over the disjunction itself checks only the closest
disjunction-worlds and can miss a disjunct altogether
(`kpstarForallOverIf_notAtIssue_of_closest`, the paper's Scenario I). The K/P** readings (143)
come out as the paper states them (`ifOverExists_atIssue`, `forallOverIf_notAtIssue`,
`forallOverIf_atIssue`), are invariant under swapping the disjuncts (`forallOverIf_comm`), and
for Mia and Sue the ∀-over-if reading presupposes that Sue has money at the closest worlds where
Mia is proud of hers (`roothPartee_notAtIssue`), which strengthens to *if Mia has money, Sue has
money* (`roothPartee_notAtIssue_strengthens`). Under a strict conditional the ∀-over-if reading
entails the if-over-∃ reading, the asymmetry of the responses (33)
(`forallOverIf_imp_ifOverExists`).

## Implementation notes

* Meanings are two-dimensional in Karttunen and Peters's way, an at-issue proposition paired
  with a presupposition (`ConventionalImplicature.TwoDim`), since the K/P connectives read a
  constituent's at-issue content where its presupposition fails; a property gives such a meaning
  for each individual (`Property`).
* The defined negation of a disjunct in (128) is read as presupposition-free (`definedFalse`);
  read as domain-restricted, the disjunction would presuppose both disjuncts' presuppositions at
  the evaluation world, against (134)–(135).
* The epistemic state `EP` and the similarity ordering the context supplies are parameters; the
  Limit Assumption built into CLOS (120) is not needed for the theorems stated.
* The type-flexible connectives are given at the two types the paper uses. The
  structured-proposition extension (153)–(157), the Cooperative Principle (123)–(124), and
  accommodation as conjunction are not formalized.

## References

* [sharvit-2025]
* [rooth-partee-1982]
* [karttunen-peters-1979]
* [heim-1992]
-/

@[expose] public section

namespace Sharvit2025

open ConventionalImplicature

variable {W E : Type*}

/-! ### CON-asymmetry and the symmetry of *or* -/

/-- The K+ disjunction under CON-asymmetry (16c), (17), which presupposes exactly what its left
disjunct presupposes. -/
def orAsym (p q : TwoDim W (W → Prop)) : TwoDim W (W → Prop) where
  atIssue := p.atIssue ⊔ q.atIssue
  notAtIssue := p.notAtIssue

/-- Swapping the disjuncts of an asymmetric disjunction changes its presupposition wherever the
disjuncts differ in it, so the LFs (62) and (64) are not equivalent. -/
theorem orAsym_notAtIssue_ne {p q : TwoDim W (W → Prop)} {w : W} (hp : p.notAtIssue w)
    (hq : ¬ q.notAtIssue w) : (orAsym p q).notAtIssue w ∧ ¬ (orAsym q p).notAtIssue w :=
  ⟨hp, hq⟩

/-! ### Karttunen's conditional presupposition and the closest-worlds one -/

variable (EP : Set W) (sim : W → Preorder W)

/-- The K/P conditional (100) presupposes the antecedent's presupposition, and the consequent's
at the evaluation world if the antecedent is true there, and asserts that every antecedent-world
of the epistemic state is a consequent-world. -/
def ifKP (p q : TwoDim W (W → Prop)) : TwoDim W (W → Prop) where
  atIssue _ := ∀ w' ∈ EP, p.atIssue w' → q.atIssue w'
  notAtIssue w := p.notAtIssue w ∧ (p.atIssue w → q.notAtIssue w)

theorem ifKP_notAtIssue_of_not_atIssue {p : TwoDim W (W → Prop)} (q : TwoDim W (W → Prop))
    {w : W} (hp : p.notAtIssue w) (h : ¬ p.atIssue w) : (ifKP EP p q).notAtIssue w :=
  ⟨hp, fun ha ↦ absurd ha h⟩

/-- The closest worlds to `w` among the `Y`-worlds of the epistemic state, under the similarity
ordering the context supplies (CLOS, (120)). -/
def clos (w : W) (Y : Set W) : Set W := (sim w).minimals (Y ∩ EP)

theorem clos_subset (w : W) (Y : Set W) : clos EP sim w Y ⊆ Y :=
  (Preorder.minimals_subset _ _).trans Set.inter_subset_left

/-- The K/P* conditional (119) presupposes the antecedent's presupposition and the consequent's
at the closest antecedent-worlds, and asserts that those are consequent-worlds. -/
def ifKPstar (p q : TwoDim W (W → Prop)) : TwoDim W (W → Prop) where
  atIssue w := clos EP sim w {w' | p.atIssue w'} ⊆ {w' | q.atIssue w'}
  notAtIssue w := p.notAtIssue w ∧ clos EP sim w {w' | p.atIssue w'} ⊆ {w' | q.notAtIssue w'}

/-- The K/P* conjunction (127) presupposes the first conjunct's presupposition, and the second's
at the evaluation world or at the closest worlds where the first is true. -/
def andKPstar (p q : TwoDim W (W → Prop)) : TwoDim W (W → Prop) where
  atIssue := p.atIssue ⊓ q.atIssue
  notAtIssue w :=
    p.notAtIssue w ∧ (q.notAtIssue w ∨ clos EP sim w {w' | p.atIssue w'} ⊆ {w' | q.notAtIssue w'})

/-- The presupposition-free proposition that `p`'s presupposition holds and its at-issue content
is false. -/
def definedFalse (p : TwoDim W (W → Prop)) : TwoDim W (W → Prop) :=
  pure fun w ↦ p.notAtIssue w ∧ ¬ p.atIssue w

/-- The K/P* disjunction (128) presupposes that one disjunct's presupposition holds and that each
disjunct's defined negation conjoins with the other. -/
def orKPstar (p q : TwoDim W (W → Prop)) : TwoDim W (W → Prop) where
  atIssue := p.atIssue ⊔ q.atIssue
  notAtIssue w :=
    (p.notAtIssue w ∨ q.notAtIssue w) ∧ (andKPstar EP sim (definedFalse p) q).notAtIssue w ∧
      (andKPstar EP sim (definedFalse q) p).notAtIssue w

theorem orKPstar_notAtIssue (p q : TwoDim W (W → Prop)) (w : W) :
    (orKPstar EP sim p q).notAtIssue w ↔
      (p.notAtIssue w ∨ q.notAtIssue w) ∧
        (q.notAtIssue w ∨
          clos EP sim w {w' | p.notAtIssue w' ∧ ¬ p.atIssue w'} ⊆ {w' | q.notAtIssue w'}) ∧
        (p.notAtIssue w ∨
          clos EP sim w {w' | q.notAtIssue w' ∧ ¬ q.atIssue w'} ⊆ {w' | p.notAtIssue w'}) := by
  simp [orKPstar, andKPstar, definedFalse]

theorem orKPstar_comm (p q : TwoDim W (W → Prop)) : orKPstar EP sim p q = orKPstar EP sim q p :=
  TwoDim.ext (sup_comm ..) (funext fun _ ↦ propext (and_congr or_comm and_comm))

/-- A closest-worlds presupposition holding throughout `M` strengthens to `Q` throughout `M` when
the laws allow `P` without `Q` (122). -/
theorem presup_strengthens {M P Q : Set W}
    (hlaw : ∀ w ∈ M, w ∉ Q → ¬ clos EP sim w P ⊆ Q) (h : ∀ w ∈ M, clos EP sim w P ⊆ Q) :
    ∀ w ∈ M, w ∈ Q := by
  intro w hw
  by_contra hq
  exact hlaw w hw hq (h w hw)

/-! ### K/P**: the conditional quantifies over the disjoined properties -/

/-- A property of individuals, a two-dimensional proposition for each individual. -/
abbrev Property (W E : Type*) := E → TwoDim W (W → Prop)

/-- The type-flexible disjunction of two properties applied to `x` (142a), a partial function of
properties `Z` defined for the two disjuncts where the propositional disjunction of the two
applied to `x` is defined, and true of `Z` when `x` has `Z`. -/
def orProps (α β : Property W E) (x : E) (Z : Property W E) : TwoDim W (W → Prop) where
  atIssue w := (Z = α ∨ Z = β) ∧ (Z x).atIssue w
  notAtIssue w := (orKPstar EP sim (α x) (β x)).notAtIssue w ∧ (Z = α ∨ Z = β)

/-- The type-flexible conditional over property-valued arguments (142b) requires, for every
property the antecedent is defined for, that the consequent be defined at the closest
antecedent-worlds and hold there. -/
def ifProps (O₁ O₂ : Property W E → TwoDim W (W → Prop)) : TwoDim W (W → Prop) where
  atIssue w :=
    ∀ Z, (O₁ Z).notAtIssue w →
      clos EP sim w {w' | (O₁ Z).atIssue w'} ⊆ {w' | (O₂ Z).atIssue w'}
  notAtIssue w := (∃ Z, (O₁ Z).notAtIssue w) ∧
    ∀ Z, (O₁ Z).notAtIssue w →
      clos EP sim w {w' | (O₁ Z).atIssue w'} ⊆ {w' | (O₂ Z).notAtIssue w'}

/-- The existential closure of (144a). -/
def exists' (O : Property W E → TwoDim W (W → Prop)) : TwoDim W (W → Prop) where
  atIssue w := ∃ Z, (O Z).atIssue w
  notAtIssue w := ∃ Z, (O Z).notAtIssue w

/-- The if-over-∃ LF (143a), in which the conditional takes the existential closures of the
disjoined properties applied to `x` and to `y`, the ellipsis resolved to the disjunction. -/
def ifOverExists (α β : Property W E) (x y : E) : TwoDim W (W → Prop) :=
  ifKPstar EP sim (exists' (orProps EP sim α β x)) (exists' (orProps EP sim α β y))

/-- The ∀-over-if LF (143b), in which the conditional quantifies over the disjoined properties,
the ellipsis bound to each in turn. -/
def forallOverIf (α β : Property W E) (x y : E) : TwoDim W (W → Prop) :=
  ifProps EP sim (orProps EP sim α β x) fun Z ↦ Z y

theorem exists'_orProps_atIssue (α β : Property W E) (x : E) (w : W) :
    (exists' (orProps EP sim α β x)).atIssue w ↔ (α x).atIssue w ∨ (β x).atIssue w := by
  simp [exists', orProps]

/-- The if-over-∃ reading asserts that the closest worlds where `x` has one of the properties are
worlds where `y` has one of them (145b). -/
theorem ifOverExists_atIssue (α β : Property W E) (x y : E) (w : W) :
    (ifOverExists EP sim α β x y).atIssue w ↔
      clos EP sim w {w' | (α x).atIssue w' ∨ (β x).atIssue w'} ⊆
        {w' | (α y).atIssue w' ∨ (β y).atIssue w'} := by
  simp only [ifOverExists, ifKPstar, exists'_orProps_atIssue]

/-- The ∀-over-if reading presupposes the disjunction of the antecedent and that `y`'s property is
defined at the closest worlds where `x` has it (146a). -/
theorem forallOverIf_notAtIssue (α β : Property W E) (x y : E) (w : W) :
    (forallOverIf EP sim α β x y).notAtIssue w ↔
      (orKPstar EP sim (α x) (β x)).notAtIssue w ∧
        clos EP sim w {w' | (α x).atIssue w'} ⊆ {w' | (α y).notAtIssue w'} ∧
        clos EP sim w {w' | (β x).atIssue w'} ⊆ {w' | (β y).notAtIssue w'} := by
  constructor
  · rintro ⟨⟨Z, hP, -⟩, h⟩
    refine ⟨hP, ?_, ?_⟩
    · simpa [orProps] using h α ⟨hP, Or.inl rfl⟩
    · simpa [orProps] using h β ⟨hP, Or.inr rfl⟩
  · rintro ⟨hP, hα, hβ⟩
    refine ⟨⟨α, hP, Or.inl rfl⟩, ?_⟩
    rintro Z ⟨-, rfl | rfl⟩
    · simpa [orProps] using hα
    · simpa [orProps] using hβ

/-- Where defined, the ∀-over-if reading asserts that, for each disjoined property, the closest
worlds where `x` has it are worlds where `y` has it (146b). -/
theorem forallOverIf_atIssue (α β : Property W E) (x y : E) (w : W)
    (h : (orKPstar EP sim (α x) (β x)).notAtIssue w) :
    (forallOverIf EP sim α β x y).atIssue w ↔
      clos EP sim w {w' | (α x).atIssue w'} ⊆ {w' | (α y).atIssue w'} ∧
        clos EP sim w {w' | (β x).atIssue w'} ⊆ {w' | (β y).atIssue w'} := by
  constructor
  · intro hall
    exact ⟨by simpa [orProps] using hall α ⟨h, Or.inl rfl⟩,
      by simpa [orProps] using hall β ⟨h, Or.inr rfl⟩⟩
  · rintro ⟨hα, hβ⟩ Z ⟨-, rfl | rfl⟩
    · simpa [orProps] using hα
    · simpa [orProps] using hβ

theorem orProps_comm (α β : Property W E) (x : E) :
    orProps EP sim α β x = orProps EP sim β α x := by
  funext Z
  simp only [orProps, orKPstar_comm EP sim (α x), or_comm (a := Z = α)]

theorem forallOverIf_comm (α β : Property W E) (x y : E) :
    forallOverIf EP sim α β x y = forallOverIf EP sim β α x y := by
  rw [forallOverIf, orProps_comm, forallOverIf]

/-- Under a strict conditional the ∀-over-if reading entails the if-over-∃ reading, though not
conversely by the responses (33), (33b). -/
theorem forallOverIf_imp_ifOverExists (hstrict : ∀ w Y, clos EP sim w Y = Y ∩ EP)
    (α β : Property W E) (x y : E) (w : W) (h : (orKPstar EP sim (α x) (β x)).notAtIssue w) :
    (forallOverIf EP sim α β x y).atIssue w → (ifOverExists EP sim α β x y).atIssue w := by
  rw [forallOverIf_atIssue EP sim α β x y w h, ifOverExists_atIssue, hstrict, hstrict,
    hstrict]
  rintro ⟨hα, hβ⟩ w' ⟨hor, hw'⟩
  rcases hor with hx | hx
  · exact Or.inl (hα ⟨hx, hw'⟩)
  · exact Or.inr (hβ ⟨hx, hw'⟩)

/-! ### Why the conditional must quantify over the disjuncts -/

/-- The consequent of (136) with the ellipsis resolved by the world-dependent property of
(137b), saying that `y` has whichever disjoined property `x` has. -/
def matched (α β : Property W E) (x y : E) : TwoDim W (W → Prop) where
  atIssue w :=
    ((α x).atIssue w → (α y).atIssue w) ∧ ((β x).atIssue w → (β y).atIssue w)
  notAtIssue w :=
    ((α x).atIssue w → (α y).notAtIssue w) ∧ ((β x).atIssue w → (β y).notAtIssue w)

/-- The K/P* attempt at the ∀-over-if reading, (136) with (137b), a conditional over the
disjunction itself. -/
def kpstarForallOverIf (α β : Property W E) (x y : E) : TwoDim W (W → Prop) :=
  ifKPstar EP sim (orKPstar EP sim (α x) (β x)) (matched α β x y)

/-- In Scenario I (141), the conditional over the disjunction lacks the presupposition about `y` and
the second property that the ∀-over-if reading carries (146). -/
theorem kpstarForallOverIf_notAtIssue_of_closest (α β : Property W E) (x y : E) (w : W)
    (hc : clos EP sim w {w' | (α x).atIssue w' ∨ (β x).atIssue w'} ⊆
      {w' | (α x).atIssue w' ∧ ¬ (β x).atIssue w'}) :
    (kpstarForallOverIf EP sim α β x y).notAtIssue w ↔
      (orKPstar EP sim (α x) (β x)).notAtIssue w ∧
        clos EP sim w {w' | (α x).atIssue w' ∨ (β x).atIssue w'} ⊆
          {w' | (α y).notAtIssue w'} := by
  constructor
  · rintro ⟨hP, h⟩
    exact ⟨hP, fun w' hw' ↦ (h hw').1 (hc hw').1⟩
  · rintro ⟨hP, h⟩
    exact ⟨hP, fun w' hw' ↦ ⟨fun _ ↦ h hw', fun hβ ↦ absurd hβ (hc hw').2⟩⟩

/-! ### Mia and Sue (138) -/

variable (hasMoney proudOf : W → E → Prop)

/-- *Penniless* (138a), true of `x` when `x` has no money. -/
def penniless (x : E) : TwoDim W (W → Prop) := pure fun w ↦ ¬ hasMoney w x

/-- *Proud of her money* (138b), which presupposes that `x` has money. -/
def proudOfMoney (x : E) : TwoDim W (W → Prop) where
  atIssue w := proudOf w x
  notAtIssue w := hasMoney w x

/-- The disjunction *penniless or proud of her money* is presupposition-free, (134a) and
(135a). -/
theorem orKPstar_penniless_proud (x : E) (w : W) :
    (orKPstar EP sim (penniless hasMoney x) (proudOfMoney hasMoney proudOf x)).notAtIssue w := by
  simp [orKPstar_notAtIssue, penniless, proudOfMoney, clos_subset]

/-- The ∀-over-if reading of *If Mia is penniless or proud of her money, then Sue is* presupposes
that Sue has money where Mia is proud of hers ((146a); (135a-iii) before strengthening). -/
theorem roothPartee_notAtIssue (mia sue : E) (w : W) :
    (forallOverIf EP sim (penniless hasMoney) (proudOfMoney hasMoney proudOf) mia sue).notAtIssue
      w ↔ clos EP sim w {w' | proudOf w' mia} ⊆ {w' | hasMoney w' sue} := by
  rw [forallOverIf_notAtIssue]
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · exact fun h ↦ ⟨orKPstar_penniless_proud EP sim hasMoney proudOf mia w, fun _ _ ↦ trivial, h⟩

theorem roothPartee_notAtIssue_strengthens (mia sue : E)
    (hlaw : ∀ w ∈ EP ∩ {w | hasMoney w mia}, ¬ hasMoney w sue →
      ¬ clos EP sim w {w' | proudOf w' mia} ⊆ {w' | hasMoney w' sue})
    (h : ∀ w ∈ EP,
      (forallOverIf EP sim (penniless hasMoney) (proudOfMoney hasMoney proudOf) mia
        sue).notAtIssue w) :
    ∀ w ∈ EP ∩ {w | hasMoney w mia}, hasMoney w sue :=
  presup_strengthens EP sim hlaw fun w hw ↦
    (roothPartee_notAtIssue EP sim hasMoney proudOf mia sue w).mp (h w hw.1)

end Sharvit2025
