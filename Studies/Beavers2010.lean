module

public import Linglib.Semantics.ArgumentStructure.Affectedness
public import Linglib.Semantics.ArgumentStructure.LevinClass.Alternation
public import Linglib.Data.Examples.Levin1993
public import Linglib.Data.Examples.Beavers2010
public import Mathlib.Order.Cover
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.WithTopBot
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Beavers (2010): The Structure of Lexical Meaning

This file formalizes Beavers's account of object/oblique alternations. The direct realization of an
alternating argument carries monotonically stronger lexical entailments than its oblique
realization, rather than a different event structure. In the conative and locative alternations
the entailments are the degrees of affectedness, each an existential weakening of the next, so that
of the eight sets of the three affectedness entailments only four are contentful, and they form a
chain. The Morphosyntactic Alignment Principle requires the oblique to bear the minimally weaker
role, which on the chain is weak covering. Every attested contrast satisfies it, the three
conatives together realize each covering pair, and reversed and level-skipping alternations violate
it. Total traversal of a path is the same entailment as quantized change, read of the scale rather
than the theme, and adding it to the entailments of patienthood gives five contentful roles, among
which *climb the stairs* and *climb up the stairs* are a minimal contrast. The same principle runs
on the chain of arrival and possession behind the dative alternation.

## Implementation notes

* A role is a set of entailments. The contentful sets of affectedness entailments are the lower
  sets, which correspond to the degrees by Birkhoff's representation, so a contrast records the
  degrees of the alternating participant in its two realizations.
* The entailments are stated over a result relation relative to a world. Potential for change is
  modal ((38)), and it is an existential generalization of nonquantized change only when the actual
  world is among the worlds the modality ranges over, which the paper assumes and the file takes as
  a hypothesis. Beavers leaves the modal base open.
* The paper defines the degrees of traversal (85) by the formulas of the degrees of affectedness,
  abstracting over the scale instead of the theme, so the file states each formula once. Only total
  traversal enters the roles of (86), and naming a role of (87) by its strongest entailment rules
  out affected paths, as the paper assumes.
* The paper states its conditions of a sentence with the theme, scale and event given; the file
  states them of a relation, over all themes, scales and events. A predicate-supplied goal is fixed
  across the predicate's events, so the end of the path in (84a) is read as the endpoint of the
  goal type.
* Beavers's rough correspondence between Dowty's proto-patient entailments and his own (Table 5)
  is not formalized, since it marks two of its cells as uncertain.

## TODO

* Derive the contrasts from the example rows of `Data.Examples.Beavers2010` rather than typing the
  verbs and degrees in.

## References

* [J. Beavers, *The structure of lexical meaning: Why semantics really matters*
  (2010)][beavers-2010]
* [J. Beavers, *On Affectedness* (2011)][beavers-2011]
* [B. Levin, *English Verb Classes and Alternations: A Preliminary Investigation*
  (1993)][levin-1993]
-/

@[expose] public section

namespace Beavers2010

open ArgumentStructure
open ArgumentStructure (AffectednessDegree)
open ArgumentStructure (DiathesisAlternation)

/-! ### L-thematic roles as sets of entailments ((65)–(67))

An L-thematic role is a set of lexical entailments. The three affectedness entailments of (65)
entail one another, so a set of them is contentful exactly when it is closed under entailment, and
the contentful sets are the degrees of affectedness (`AffectednessDegree.entailments`). -/

example : Fintype.card AffectednessEntailment = 3 := by decide

example : Fintype.card (Set AffectednessEntailment) = 8 := by rw [Fintype.card_set]; rfl

example : Nat.card (LowerSet AffectednessEntailment) = 4 := by
  rw [← Nat.card_congr AffectednessDegree.entailments.toEquiv, Nat.card_eq_fintype_card]; rfl

/-! ### The entailments ((31), (38))

The result relation `R w x s g e` says that in the world `w` the theme `x` ends the event `e` at
the goal `g` on the scale `s`, and `w₀` is the actual world. -/

section Entailments

variable {W α S G β : Type*} (acc : W → W → Prop) (w₀ : W) (R : W → α → S → G → β → Prop)
  (φ : α → S → β → Prop)

/-- A predicate entails a **quantized change** to the goal `g` when its theme ends every event of
it at `g` on its scale ((31a)). Of the scale, the same condition says it is **totally traversed**
((85a)). -/
def Quantized (g : G) : Prop := ∀ x s e, φ x s e → R w₀ x s g e

/-- A predicate entails a **nonquantized change** when its theme ends every event of it at some
goal on its scale ((31b)). Of the scale, the same condition says it is **traversed** ((85b)). -/
def Nonquantized : Prop := ∀ x s e, φ x s e → ∃ g, R w₀ x s g e

/-- A predicate gives its theme **potential for change** when in every event of it the theme ends
at some goal on its scale in some world accessible from the actual one ((38a)). Of the scale, the
same condition says it is **potentially traversed** ((85c)). -/
def Potential : Prop := ∀ x s e, φ x s e → ∃ w, acc w₀ w ∧ ∃ g, R w x s g e

variable {acc w₀ R φ}

theorem Quantized.nonquantized {g : G} (h : Quantized w₀ R φ g) : Nonquantized w₀ R φ :=
  fun x s e hx ↦ ⟨g, h x s e hx⟩

/-- A nonquantized change entails potential for change when the actual world is accessible ((38a),
(31b)). -/
theorem Nonquantized.potential (hacc : acc w₀ w₀) (h : Nonquantized w₀ R φ) :
    Potential acc w₀ R φ :=
  fun x s e hx ↦ ⟨w₀, hacc, h x s e hx⟩

variable (acc w₀ R φ) in
/-- The condition each degree of affectedness names for a predicate ((31), (38)). -/
def Holds : AffectednessDegree → Prop
  | .unspecified => True
  | .potential => Potential acc w₀ R φ
  | .nonquantized => Nonquantized w₀ R φ
  | .quantized => ∃ g, Quantized w₀ R φ g

/-- Each degree entails every weaker one, given that the actual world is among the worlds the
modality ranges over. -/
theorem holds_antitone (hacc : acc w₀ w₀) : Antitone (Holds acc w₀ R φ) := by
  intro d d' h
  cases d <;> cases d' <;> first
    | exact absurd h (by decide)
    | exact fun _ ↦ trivial
    | exact id
    | exact fun ⟨_, hq⟩ ↦ hq.nonquantized
    | exact Nonquantized.potential hacc
    | exact fun ⟨_, hq⟩ ↦ hq.nonquantized.potential hacc

variable (acc w₀ R φ) in
/-- The role a predicate assigns its theme is the set of affectedness entailments it has ((65)). -/
def role : Set AffectednessEntailment := {e | Holds acc w₀ R φ e.1}

/-- Every predicate's role is contentful, closed under entailment ((67)), given that the actual
world is among the worlds the modality ranges over. -/
theorem isLowerSet_role (hacc : acc w₀ w₀) : IsLowerSet (role acc w₀ R φ) :=
  fun _ _ h ↦ holds_antitone hacc h

end Entailments

/-! ### The MAP ((68)–(69)) as weak covering -/

instance : DecidableRel (· ⩿ · : AffectednessDegree → AffectednessDegree → Prop) :=
  fun a b ↦ decidable_of_iff (a ≤ b ∧ ∀ c, a < c → ¬c < b) Iff.rfl

instance : DecidableRel (· ⋖ · : AffectednessDegree → AffectednessDegree → Prop) :=
  fun a b ↦ decidable_of_iff (a < b ∧ ∀ c, a < c → ¬c < b) Iff.rfl

/-- The Morphosyntactic Alignment Principle (69) holds of the roles of an alternating participant's
direct and oblique realizations on a hierarchy of roles when the oblique role is minimally weaker,
weakly covered by the direct one ((68)). -/
def MAP {ρ : Type*} [Preorder ρ] (direct oblique : ρ) : Prop :=
  oblique ⩿ direct

instance {ρ : Type*} [Preorder ρ] [DecidableRel (· ⩿ · : ρ → ρ → Prop)] (d o : ρ) :
    Decidable (MAP d o) := by
  unfold MAP; infer_instance

/-- Minimal contrast of the roles of (66) is weak covering of their degrees. -/
theorem entailments_wcovBy_entailments_iff (d d' : AffectednessDegree) :
    d.entailments ⩿ d'.entailments ↔ d ⩿ d' :=
  apply_wcovBy_apply_iff AffectednessDegree.entailments

/-- Under the MAP the oblique degree is at most the direct one, so the oblique's entailments are
among the direct realization's (27). -/
theorem MAP.oblique_le {ρ : Type*} [Preorder ρ] {d o : ρ} (h : MAP d o) : o ≤ d :=
  h.le

/-! ### The attested contrasts (Tables 3–4, (75)) -/

/-- An alternation contrast records a verb and the affectedness degrees of its alternating
participant as direct object and as oblique. -/
structure AlternationContrast where
  /-- The verb. -/
  verb : String
  /-- The alternation it instantiates. -/
  alternationType : DiathesisAlternation
  /-- Degree in direct realization. -/
  directDegree : AffectednessDegree
  /-- Degree in oblique realization. -/
  obliqueDegree : AffectednessDegree
  deriving Repr, DecidableEq

/-- *Ate her cake* against *ate at her cake* (21) contrasts quantized with non-quantized change. -/
def eatConative : AlternationContrast :=
  ⟨"eat", .conative, .quantized, .nonquantized⟩

/-- *Cut the rope* against *cut at the rope* (20) contrasts non-quantized change with potential for
change. -/
def cutConative : AlternationContrast :=
  ⟨"cut", .conative, .nonquantized, .potential⟩

/-- *Hit Defarge* against *hit at Defarge* (22) contrasts potential for change with no entailment
about change. -/
def hitConative : AlternationContrast :=
  ⟨"hit", .conative, .potential, .unspecified⟩

/-- In *loaded the wagon (with hay)* (49) the location is completely filled as object and partly as
oblique. -/
def loadLocation : AlternationContrast :=
  ⟨"load", .locative, .quantized, .nonquantized⟩

/-- In *loaded the hay (onto the wagon)* (49) the theme is all moved as object and partly as
oblique. -/
def loadTheme : AlternationContrast :=
  ⟨"load", .locative, .quantized, .nonquantized⟩

/-- In *cut the window (with the diamond)* (54) the location is damaged as object and potentially
damaged as oblique. -/
def cutLocation : AlternationContrast :=
  ⟨"cut", .locative, .nonquantized, .potential⟩

/-- *Cut the diamond (on the window)* (54) shows the same contrast for the theme. -/
def cutTheme : AlternationContrast :=
  ⟨"cut", .locative, .nonquantized, .potential⟩

/-- In *hit the fence with the stick* against *hit the stick against the fence* ((24), (75)) both
realizations have potential for change, the equal-role alternation the MAP permits with no
truth-conditional contrast. -/
def hitLocative : AlternationContrast :=
  ⟨"hit", .locative, .potential, .potential⟩

/-- The attested contrasts. -/
def allContrasts : List AlternationContrast :=
  [eatConative, cutConative, hitConative,
   loadLocation, loadTheme, cutLocation, cutTheme, hitLocative]

/-- The MAP holds of a contrast. -/
def MapHolds (c : AlternationContrast) : Prop :=
  MAP c.directDegree c.obliqueDegree

instance (c : AlternationContrast) : Decidable (MapHolds c) := by
  unfold MapHolds; infer_instance

/-- The MAP holds of every attested contrast, each oblique realization being a minimal weakening
of its direct counterpart or, as in (75), the same role. -/
theorem MAP_holds_all_alternations : ∀ c ∈ allContrasts, MapHolds c := by decide

theorem MapHolds.oblique_le {c : AlternationContrast} (h : MapHolds c) :
    c.obliqueDegree ≤ c.directDegree :=
  MAP.oblique_le h

/-- The three conatives realize exactly the covering pairs of the affectedness hierarchy,
together tiling the chain (Table 3). -/
theorem conatives_witness_all_covers :
    ∀ q r : AffectednessDegree, q ⋖ r ↔
      ∃ c ∈ [eatConative, cutConative, hitConative],
        c.directDegree = r ∧ c.obliqueDegree = q := by decide

/-! ### Impossible alternations ((76)–(77)) -/

/-- In a reversed contrast (76) the oblique strictly outranks the direct realization. -/
def reversedConative : AlternationContrast :=
  ⟨"reversed", .conative, .potential, .quantized⟩

/-- A level-skipping contrast (77) has a quantized direct and a potential oblique realization. -/
def skippingLocative : AlternationContrast :=
  ⟨"skipping", .locative, .quantized, .potential⟩

theorem reversed_violates_MAP : ¬ MapHolds reversedConative := by decide

/-- Skipping a level violates the MAP even though the degree order is respected, since `⊆_M`
demands the next-weakest role, not any weaker one. -/
theorem skipping_violates_MAP :
    ¬ MapHolds skippingLocative ∧
      skippingLocative.obliqueDegree ≤ skippingLocative.directDegree :=
  ⟨by decide, by decide⟩


/-! ### Total traversal ((84)–(87)) -/

/-- A role of (87) is named by its strongest entailment ((66)), an affectedness entailment or total
traversal of a path ((86d)), which is incomparable with the affectedness entailments, and `⊥` is
the empty role. A role with both kinds would be an affected path, which (87) rules out. -/
abbrev Role := WithBot (AffectednessEntailment ⊕ Unit)

/-- `{totally traversed}`. -/
def Role.totallyTraversed : Role := ↑(Sum.inr () : AffectednessEntailment ⊕ Unit)

example : Fintype.card Role = 5 := by decide

/-- *Climbed the stairs* and *climbed up the stairs* ((81)–(84)) form a minimal contrast as the MAP
(69) requires ((86), (87)). -/
theorem climb_map : MAP Role.totallyTraversed ⊥ := by
  refine CovBy.wcovBy ?_
  rw [Role.totallyTraversed, WithBot.bot_covBy_coe]
  rintro (e | u) h
  · exact absurd h Sum.not_inl_le_inr
  · exact le_rfl

/-! ### The dative chain (90) -/

/-- The roles of the dative chain (90) are being arrived at and being arrived into the possession
of. -/
inductive DativeRole where
  /-- A goal is arrived at. -/
  | goal
  /-- A recipient-goal is arrived into the possession of. -/
  | recipientGoal
  deriving DecidableEq, Fintype, Repr

/-- Strength on the dative chain. -/
def DativeRole.strength : DativeRole → Nat
  | .goal => 0
  | .recipientGoal => 1

instance : LinearOrder DativeRole :=
  .lift' DativeRole.strength fun a b ↦ by
    cases a <;> cases b <;> simp [DativeRole.strength]

instance : DecidableRel (· ⩿ · : DativeRole → DativeRole → Prop) :=
  fun a b ↦ decidable_of_iff (a ≤ b ∧ ∀ c, a < c → ¬c < b) Iff.rfl

/-- In *mailed Mary the letter* against *mailed the letter to Mary* ((88)–(89)), the indirect object
adds prospective possession to arrival. -/
theorem dative_map : MAP DativeRole.recipientGoal .goal := by decide

/-! ### Bridge to [levin-1993]'s judgment rows -/

/-- The conative alternation is attested for *cut* and *hit* (Table 3). -/
theorem conative_data_attested :
    Levin1993.Examples.con_cut.judgment = .acceptable ∧
    Levin1993.Examples.con_hit.judgment = .acceptable := ⟨rfl, rfl⟩

theorem break_no_conative :
    Levin1993.Examples.con_break.judgment = .ungrammatical := rfl

/-- The locative alternation is attested for spray/load verbs (Table 4). -/
theorem locative_data_attested :
    Levin1993.Examples.loc_spray.judgment = .acceptable ∧
    Levin1993.Examples.loc_load.judgment = .acceptable := ⟨rfl, rfl⟩

end Beavers2010
