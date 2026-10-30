module

public import Linglib.Semantics.Possession.Quantifier
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Data.Examples.Barker1995
public import Mathlib.Data.Fintype.Prod

/-!
# Barker (1995): Possessive Descriptions

Possessives are descriptions: a possessor, a possession relation — the noun's
own relation for a relational noun (*John's child*), a contextually resolved
one otherwise (*John's stick*) — and a sortal restrictor. Like definites they
presuppose a unique maximal possessee per possessor; like indefinites they can
introduce novel referents. In a quantificational possessive (*most planets'
rings*) the quantifier binds the possessor and possessee variables together.
Two consequences follow: quantification *narrows* to possessors that have a
possessee, and the possessor-dominant and symmetric construals cannot be told
apart truth-conditionally — uniqueness leaves one instance per case, which is
the book's resolution of the perspective paradox.

## References

* [barker-1995]: Possessive Descriptions. CSLI Publications.
-/

@[expose] public section

namespace Barker1995

open Quantifier Quantifier.Det Possession

/-! ### The perspective paradox resolved (Ch. 4)

With a unique possessee per possessor there is one instance per case, whether
or not the possessee variable helps distinguish cases: counting
possessor–possessee pairs agrees with counting possessors. -/

variable {α : Type*}

private theorem ncard_pair_eq (C A : Set α) (R : α → α → Prop)
    (huniq : ∀ x y y', y ∈ A → R x y → y' ∈ A → R x y' → y = y') (P : α → α → Prop) :
    {p : α × α | (p.1 ∈ C ∧ p.2 ∈ A ∧ R p.1 p.2) ∧ P p.1 p.2}.ncard =
      {x | (x ∈ C ∧ dom A R x) ∧ ∃ y ∈ A, R x y ∧ P x y}.ncard :=
  Set.ncard_congr (fun p _ ↦ p.1)
    (fun ⟨_, y⟩ ⟨⟨hC, hA, hR⟩, hP⟩ ↦ ⟨⟨hC, y, hA, hR⟩, y, hA, hR, hP⟩)
    (by
      rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨⟨-, hA, hR⟩, -⟩ ⟨⟨-, hA', hR'⟩, -⟩ (rfl : x = x')
      exact congrArg (Prod.mk x) (huniq x y y' hA hR hA' hR'))
    fun x ⟨⟨hC, _⟩, y, hA, hR, hP⟩ ↦ ⟨(x, y), ⟨⟨hC, hA, hR⟩, hP⟩, rfl⟩

/-- When each possessor has at most one possessee, the symmetric and possessor-dominant construals
of *most* agree (Ch. 4). -/
theorem symmetric_iff_possessor_dominant (C A B : Set α) (R : α → α → Prop)
    (huniq : ∀ x y y', y ∈ A → R x y → y' ∈ A → R x y' → y = y') :
    most {p : α × α | p.1 ∈ C ∧ p.2 ∈ A ∧ R p.1 p.2} {p | p.2 ∈ B} ↔
      Poss most C Det.some R A B := by
  have h₁ : ({p : α × α | p.1 ∈ C ∧ p.2 ∈ A ∧ R p.1 p.2} ∩ {p | p.2 ∈ B}).ncard =
      (C ∩ {x | dom A R x} ∩ {x | Det.some (π A R x) B}).ncard :=
    (ncard_pair_eq C A R huniq fun _ y ↦ y ∈ B).trans <| congrArg _ <| Set.ext fun _ ↦
      and_congr_right' <| exists_congr fun _ ↦ and_assoc.symm
  have h₂ : ({p : α × α | p.1 ∈ C ∧ p.2 ∈ A ∧ R p.1 p.2} \ {p | p.2 ∈ B}).ncard =
      ((C ∩ {x | dom A R x}) \ {x | Det.some (π A R x) B}).ncard :=
    (ncard_pair_eq C A R huniq fun _ y ↦ y ∉ B).trans <| congrArg _ <| Set.ext fun x ↦ by
      constructor
      · rintro ⟨⟨hC, hdom⟩, y, hA, hR, hnB⟩
        exact ⟨⟨hC, hdom⟩, fun ⟨y', ⟨hA', hR'⟩, hB'⟩ ↦
          hnB (huniq x y' y hA' hR' hA hR ▸ hB')⟩
      · rintro ⟨⟨hC, y, hA, hR⟩, hn⟩
        exact ⟨⟨hC, ⟨y, hA, hR⟩⟩, y, hA, hR, fun hB ↦ hn ⟨y, ⟨hA, hR⟩, hB⟩⟩
  rw [Poss, most_apply, most_apply, h₁, h₂]

/-! ### Narrowing: the planets and their rings (Ch. 4)

Nine planets, of which only Saturn, Neptune and Uranus have rings; Saturn's
and Neptune's rings are icy, Uranus's are not. *Most planets' rings are made
of ice* is judged true — the quantification ranges only over the three ringed
planets. Entities `0`–`8` are the planets, `9`–`11` their rings. -/

abbrev isPlanet : Set (Fin 12) := {x | x.val < 9}

abbrev isRing : Set (Fin 12) := {x | 9 ≤ x.val}

abbrev hasRing : Fin 12 → Fin 12 → Prop := fun x y ↦
  (x = 0 ∧ y = 9) ∨ (x = 1 ∧ y = 10) ∨ (x = 2 ∧ y = 11)

abbrev isIcy : Set (Fin 12) := {9, 10}

/-- *Most planets' rings are made of ice* is true: `Poss` narrows the domain
to the three ringed planets, two of which have icy rings. -/
theorem most_planets_rings_icy :
    Poss most isPlanet Det.some hasRing isRing isIcy := by
  unfold Poss; decide

/-- Without narrowing, the quantification is false: only two of the nine
planets have an icy ring. -/
theorem not_unnarrowed :
    ¬ most isPlanet {x | Det.some (isRing ∩ {y | hasRing x y}) isIcy} := by
  decide

/-! ### No possessee-dominant reading (Ch. 4)

Five people and three colors: one favors red, one yellow, three blue. *Most
people's favorite color is blue* is true counting people (3 of 5) and would
be false counting colors (1 of 3); the color-counting reading does not exist.
Entities `0`–`4` are the people; `5`, `6`, `7` are red, yellow, blue. -/

abbrev isPerson : Set (Fin 8) := {x | x.val < 5}

abbrev isColor : Set (Fin 8) := {x | 5 ≤ x.val}

abbrev favors : Fin 8 → Fin 8 → Prop := fun x y ↦
  (x = 0 ∧ y = 5) ∨ (x = 1 ∧ y = 6) ∨ ((x = 2 ∨ x = 3 ∨ x = 4) ∧ y = 7)

abbrev isBlue : Set (Fin 8) := {7}

/-- *Most people's favorite color is blue*, counting people, is true, with 3 of 5. -/
theorem favorite_color_possessor_dominant :
    Poss most isPerson Det.some favors isColor isBlue := by
  unfold Poss; decide

/-- Counting favored colors instead of people would make the sentence false —
the reading English does not have. -/
theorem not_favorite_color_possessee_dominant :
    ¬ most (isColor ∩ {c | ∃ p ∈ isPerson, favors p c}) isBlue := by
  decide

theorem favors_unique :
    ∀ x y y' : Fin 8, y ∈ isColor → favors x y → y' ∈ isColor → favors x y' →
      y = y' := by decide

theorem favorite_color_symmetric :
    most {p : Fin 8 × Fin 8 | p.1 ∈ isPerson ∧ p.2 ∈ isColor ∧ favors p.1 p.2}
      {p | p.2 ∈ isBlue} :=
  (symmetric_iff_possessor_dominant isPerson isColor isBlue favors
    favors_unique).mpr favorite_color_possessor_dominant

/-! ### Definiteness (Ch. 2)

A definite possessive presupposes a unique possessee: in a model where the boy `0` owns exactly
the cat `1`, the possessee predicate of *the boy's cat* has one satisfier. -/

theorem theBoysCat_unique :
    ∃! y : Fin 3, π (· = 1) (fun x y : Fin 3 ↦ x = 0 ∧ y = 1) 0 y :=
  ⟨1, ⟨rfl, rfl, rfl⟩, fun _ h ↦ h.1⟩

/-! ### Narrowing with a single possessor

For a single possessor, narrowing surfaces as existential import: *Mercury's rings are icy* fails
because Mercury (planet `3`) has no ring. -/

theorem mercurysRings_not_icy : ¬ PossNP (individual 3) Det.some hasRing isRing isIcy := by
  intro h
  obtain ⟨b, -, ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨h3, -⟩⟩ := possNP_individual_existential_import h <;>
    exact absurd h3 (by decide)

end Barker1995
