module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Just2024
public import Studies.Haspelmath2021
public import Linglib.Syntax.Clause.ArgumentRole
public import Linglib.Syntax.Clause.Scenario
public import Linglib.Syntax.Person.Basic

/-!
# Just (2024): A structural and functional comparison of differential A and P indexing

This file formalizes Just's claim that differential A indexing and differential P indexing,
the variable occurrence of a verbal index for reasons other than the referent's argument role,
are one phenomenon: a referent is indexed when it reaches a language-specific level of
referential prominence in Haspelmath's sense, whatever its role. The two look like mirror
images because the roles differ in default prominence: A referents are typically prominent, so
a non-prominent or focused A loses an otherwise present index, while P referents typically are
not, so a topical, definite, or animate P gains one. The principle is `Indexed`, prominence at
or above the threshold, whose coding length is the cutoff split `Haspelmath2021.atLeast`, and
`deviation_coding` derives the mirror image and its consequence for coding asymmetries: a
referent that deviates from its role's default receives longer coding exactly when the default
is unindexed, so Haspelmath's generalization that deviations from role-reference associations
are coded by longer forms holds of differential P indexing and fails of differential A
indexing, where the deviating configuration loses the index. The examples of the paper's
survey are rows, and `indexed_iff_prominent` reads each as the paper does, the index present
exactly where the referent has the prominence the language demands, for A and P alike.

Co-argument sensitivity is the paper's other case: in Reyesano which of A and P is indexed
depends on the persons of both, its table being rows of `Clause.Scenario Person`, and
`no_ranking_fits` shows that no ranking of the persons predicts the table by indexing the
argument the scenario's kind under that ranking favours, as the paper argues after
Witzlack-Makarevich and colleagues that hierarchies are not needed to describe such systems.

## Implementation notes

* Prominence is a linear order with a threshold; the paper's factors, identifiability,
  animacy, topicality, and person, are language-specific and enter the rows as the condition
  the paper names for each example.
* Coding length counts the index only, which is what the paper's argument about coding
  asymmetries concerns.

## References

* [just-2024]
* [haspelmath-2021]
* [witzlack-makarevich-etal-2016]
-/

@[expose] public section

namespace Just2024

open Clause (Scenario)
open Haspelmath2021 (atLeast)

/-! ### Indexing and referential prominence -/

section Principle

variable {Prominence : Type*} [LinearOrder Prominence] (θ : Prominence)

/-- By the principle, a referent is indexed when its prominence reaches the language's
threshold. -/
def Indexed (p : Prominence) : Prop := θ ≤ p

instance (p : Prominence) : Decidable (Indexed θ p) := inferInstanceAs (Decidable (θ ≤ p))

variable {ρ : Type*} (dflt : ρ → Prominence)

/-- A referent deviates from its role when it lies on the other side of the threshold from
the role's default prominence. -/
def Deviates (r : ρ) (p : Prominence) : Prop := Indexed θ p ↔ ¬ Indexed θ (dflt r)

instance (r : ρ) (p : Prominence) : Decidable (Deviates θ dflt r p) :=
  inferInstanceAs (Decidable (_ ↔ _))

/-- The mirror image yields the coding asymmetry, a deviating referent being coded longer than
its role's default exactly when the default is unindexed. Differential P indexing, with a
default below the threshold, codes the deviation by adding an index; differential A
indexing, with a default above it, codes the deviation by dropping one. -/
theorem deviation_coding {r : ρ} {p : Prominence} (h : Deviates θ dflt r p) :
    atLeast θ (dflt r) < atLeast θ p ↔ ¬ Indexed θ (dflt r) := by
  by_cases hd : θ ≤ dflt r
  · have hp : ¬ θ ≤ p := fun hp ↦ h.1 hp hd
    simp only [atLeast, ite_eq_left hd, ite_eq_right hp]
    exact ⟨fun h ↦ absurd h (by omega), fun h ↦ absurd hd h⟩
  · have hp : θ ≤ p := h.2 hd
    simp only [atLeast, ite_eq_right hd, ite_eq_left hp]
    exact ⟨fun _ ↦ hd, fun _ ↦ Nat.zero_lt_one⟩

/-- The deviating referent of a role indexed by default is coded shorter. -/
theorem deviation_shorter {r : ρ} {p : Prominence} (h : Deviates θ dflt r p)
    (hr : Indexed θ (dflt r)) : atLeast θ p < atLeast θ (dflt r) := by
  have hp : ¬ θ ≤ p := fun hp ↦ h.1 hp hr
  have hr' : θ ≤ dflt r := hr
  simp only [atLeast, ite_eq_right hp, ite_eq_left hr']
  exact Nat.zero_lt_one

end Principle

/-- A transitive role's default prominence follows its rank, prominent for the higher-ranked A
and not for the lower-ranked P, the role-reference associations of [haspelmath-2021]. -/
def transitiveDefault (r : ArgumentRole) : Bool := decide r.IsHigherRanked

/-- A non-prominent A and a prominent P both deviate from their defaults; the A is coded
shorter than a default A and the P longer than a default P. -/
theorem transitive_mirror :
    atLeast true false < atLeast true (transitiveDefault .A) ∧
      atLeast true (transitiveDefault .P) < atLeast true true :=
  ⟨deviation_shorter true transitiveDefault (r := .A) (p := false) (by decide) (by decide),
    (deviation_coding true transitiveDefault (r := .P) (p := true) (by decide)).2 (by decide)⟩

/-! ### The survey -/

/-- The condition under which the paper reports a referent indexed or not, the factor named
for the example. `focus` is focus on the referent, `otherFocus` focus on another constituent
of a language whose index requires predicate focus. -/
inductive Condition where
  | topical
  | focus
  | otherFocus
  | animate
  | inanimate
  | definite
  | indefinite
  | pronominal
  | lexical
  | predicateFocus
  deriving DecidableEq, Repr

/-- Whether a condition puts the referent at the prominence the language demands. Topical,
animate, definite, and pronominal referents do, and so does predicate focus, which leaves the
arguments unfocused; a focused, inanimate, indefinite, or lexical referent falls short, as does
an argument in a clause whose focus lies elsewhere than the predicate. -/
def Condition.Prominent : Condition → Prop
  | .topical | .animate | .definite | .pronominal | .predicateFocus => True
  | .focus | .otherFocus | .inanimate | .indefinite | .lexical => False

instance : DecidablePred Condition.Prominent
  | .topical | .animate | .definite | .pronominal | .predicateFocus => isTrue trivial
  | .focus | .otherFocus | .inanimate | .indefinite | .lexical => isFalse id

/-- A grammatical row of the survey gives the role, whether it is indexed, and the paper's
condition. -/
def datum (r : Datum) : Option (ArgumentRole × Bool × Condition) := do
  if r.judgment ≠ .acceptable then none
  let role ← r.parse? "role" [("A", ArgumentRole.A), ("P", .P)]
  let ix ← r.parse? "indexed" [("true", true), ("false", false)]
  let c ← r.parse? "condition" [("topical", Condition.topical), ("focus", .focus),
    ("otherFocus", .otherFocus), ("animate", .animate), ("inanimate", .inanimate),
    ("definite", .definite), ("indefinite", .indefinite), ("pronominal", .pronominal),
    ("lexical", .lexical), ("predicateFocus", .predicateFocus)]
  pure (role, ix, c)

/-- The examples of the survey for which the paper names the conditioning factor. -/
def data : List (ArgumentRole × Bool × Condition) := Examples.all.filterMap datum

/-- Across the survey the index is present exactly where the referent is prominent under the
named condition, for A and for P. -/
theorem indexed_iff_prominent : ∀ d ∈ data, d.2.1 = true ↔ d.2.2.Prominent := by
  decide +kernel

/-- Both roles are attested in both directions, with an indexed and an unindexed A and an
indexed and an unindexed P. -/
theorem both_roles_both_ways :
    ∀ role ∈ [ArgumentRole.A, .P], ∀ b ∈ [true, false],
      ∃ d ∈ data, d.1 = role ∧ d.2.1 = b := by
  decide +kernel

/-! ### Co-argument sensitivity: Reyesano -/

/-- The arguments indexed in a scenario. -/
inductive IndexedArgs where
  | a
  | p
  | both
  deriving DecidableEq, Repr

/-- A scenario of the paper's table, the persons of A and P, with the arguments indexed. -/
def scenario (r : Datum) : Option (Scenario Person × IndexedArgs) := do
  let persons := [("1", Person.first), ("2", .second), ("3", .third)]
  let a ← r.parse? "aPerson" persons
  let p ← r.parse? "pPerson" persons
  let ix ← r.parse? "indexed" [("A", IndexedArgs.a), ("P", .p), ("AP", .both)]
  pure (⟨a, p⟩, ix)

/-- The Reyesano table. -/
def reyesano : List (Scenario Person × IndexedArgs) := Examples.all.filterMap scenario

/-- Indexing by a ranking of persons indexes the higher-ranked argument, the A in a downstream
scenario and the P in an upstream one, and both when balanced. -/
def byRanking (rank : Person → Fin 3) (s : Scenario Person) : IndexedArgs :=
  match (s.map rank).kind with
  | .downstream => .a
  | .upstream => .p
  | .balanced => .both

/-- Whether an A of a given person is indexed depends on the person of its co-argument. -/
theorem coargument_sensitive :
    ∃ s ∈ reyesano, ∃ s' ∈ reyesano, s.1.high = s'.1.high ∧ s.2 ≠ s'.2 := by
  decide +kernel

/-- No ranking of the tripartition predicts the table by indexing the higher-ranked
argument, since a first-person A outranks a third-person P but a third-person A ties with a
first-person P. -/
theorem no_ranking_fits :
    ¬ ∃ rank : Person → Fin 3, ∀ s ∈ reyesano, s.2 = byRanking rank s.1 := by
  decide +kernel

end Just2024
