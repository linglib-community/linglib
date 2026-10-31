module

public import Linglib.Data.Examples.RomeroHan2004
public import Linglib.Discourse.CommonGround
public import Linglib.Fragments.English.PolarityItems
public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Questions.Polar
public import Linglib.Semantics.Questions.Bias
public import Linglib.Syntax.Negation
public import Mathlib.Order.Interval.Set.Defs
public import Linglib.Data.Examples.Readers

/-!
# Romero and Han (2004): On negative yes/no questions

This file formalizes the paper's derivation of the epistemic bias of yes/no questions with preposed
negation from one assumption: preposing negation contributes the conversational epistemic operator
VERUM, FOR-SURE-CG (43), true at a world when the proposition is in the common ground at every world
satisfying the conversational goals of an individual `x` at every world conforming to the knowledge
of `x`, `x` being the addressee, or the addressee and the speaker together. With `epi` and `conv`
the accessibility relations of `x`, it is the necessity `□[epi ○ conv] (p ∈ cg ·)`,
which `ModalLogic.box_comp` unfolds into the paper's two quantifiers. A question over VERUM
partitions on certainty about adding the proposition to the common ground rather than on the
proposition, `denotation_eq`, a meta-conversational move licit only under a prior bias; the paper's
positive and negative readings are the two scopes of negation relative to VERUM, distinguished by
which polarity items they license, `Licensed`. The polarity of the implicature is fixed not by the
partition, which the positive reading shares with a *really*-question, but by the pronounced cell:
pronouncing certainty asks for conclusive evidence, so the speaker believes the negation, and
pronouncing uncertainty asks for doubts, so the speaker believes the proposition,
`speakerBelief_eq`. The paper's examples are rows: the polarity-item judgments follow licensing, and
the bias of every question with preposed negation and of every VERUM form is the one the model
implicates, `bias_of_form`.

## Implementation notes

The common ground at a world is a filter of propositions, so acceptance is closed under entailment
and conjunction where the paper speaks of a set of propositions. VERUM is not a named operator of
its own: other analyses built on it, Repp's FALSUM among them, are necessities along the same
relation of the common ground's acceptance of a proposition or its failure to. Speaker belief is the
epistemic proposition of the states settling a proposition, `Set.Iic`. A question's form is the
position of its negation, `Option Negation.Position`, what matters being its position relative to
the rest of the clause, preposed or not; a bias is the sign of the proposition the speaker's belief
supports. The Principle of Economy that makes VERUM questions biased is stated in the paper in prose
and is not formalized.

## References

* [M. Romero, C.-H. Han, *On negative yes/no questions* (2004)][romero-han-2004]
* [D. R. Ladd, *A first look at the semantics and pragmatics of negative questions and tag
  questions* (1981)][ladd-1981]
* [T. N. Höhle, *Über Verum-Fokus im Deutschen* (1992)][hohle-1992]
* [S. Repp, *Common ground management: Modal particles, illocutionary negation and VERUM*
  (2013)][repp-2013]
-/

@[expose] public section

namespace RomeroHan2004

open scoped ModalLogic
open Question (polar polar_compl)
open Set (Iic)

open scoped SetRel

variable {W : Type*} (epi conv : SetRel W W) (cg : W → Filter W) (p : Set W)

/-! ### The four VERUM questions -/

/-- The yes/no questions containing VERUM, namely the positive reading of preposed negation, with
negation over VERUM (73), the negative reading, with VERUM over negation (68), the
*really*-question (111), and focused *NOT* (118). -/
inductive Form
  | pi
  | ni
  | really
  | notFocus
  deriving DecidableEq, Fintype

/-- The proposition under VERUM is the proposition for the positive reading and *really*, and its
negation for the negative reading and focused *NOT*. -/
def prejacent : Form → Set W
  | .pi | .really => p
  | .ni | .notFocus => pᶜ

/-- Whether the form pronounces the doubt cell, the complement of VERUM, as only the positive
reading, where negation scopes over VERUM, does. -/
def Form.Doubt : Form → Prop
  | .pi => True
  | .ni | .really | .notFocus => False

instance : DecidablePred Form.Doubt := λ f => by cases f <;> unfold Form.Doubt <;> infer_instance

/-- The cell a form pronounces, VERUM of the prejacent or its complement. -/
def pronounced (f : Form) : Set W :=
  if f.Doubt then {w | □[epi ○ conv] (prejacent p f ∈ cg ·) w}ᶜ
  else {w | □[epi ○ conv] (prejacent p f ∈ cg ·) w}

/-- The question a form denotes is the polar question over the pronounced cell. -/
def denotation (f : Form) : Question W := polar (pronounced epi conv cg p f)

/-- Every VERUM question denotes the partition on certainty about its prejacent (48), (69),
(74), whichever cell it pronounces. -/
theorem denotation_eq (f : Form) :
    denotation epi conv cg p f =
      polar {w | □[epi ○ conv] (prejacent p f ∈ cg ·) w} := by
  unfold denotation pronounced
  split_ifs <;> simp

-- (84), (85)
theorem denotation_pi_eq_really :
    denotation epi conv cg p .pi = denotation epi conv cg p .really := by
  simp [denotation_eq, prejacent]

/-! ### The epistemic implicature

A question pronouncing certainty about its prejacent asks for conclusive evidence for it,
which the addressee can only supply if the prejacent is the addressee's proposition and its
negation the speaker's belief; a question pronouncing uncertainty asks for doubts, so the
prejacent is the speaker's belief. -/

/-- The speaker's original belief implicated by a form is the epistemic proposition of the
states settling the prejacent's negation, or the prejacent itself for the doubt cell. -/
def speakerBelief (f : Form) : Set (Set W) :=
  if f.Doubt then Iic (prejacent p f) else Iic (prejacent p f)ᶜ

/-- The bias each form implicates is belief in the proposition for the preposed-negation
readings (81), (82) and focused *NOT* (117), and belief in its negation for *really* (110). -/
def Form.implicature : Form → Polarity
  | .pi | .ni | .notFocus => .positive
  | .really => .negative

theorem speakerBelief_eq (f : Form) : speakerBelief p f = Iic (f.implicature • p) := by
  cases f <;> simp [speakerBelief, Form.Doubt, Form.implicature, prejacent]

/-! ### Polarity items

Positive polarity items are licensed under VERUM in a positive clause and negative ones in
a negative clause (70), (71), (75), (76); VERUM intervenes between negation and the clause
in the positive reading, so the clause is negated only in the negative reading and under
focused *NOT*. -/

/-- Whether the clause under VERUM is negated. -/
def Form.Negated : Form → Prop
  | .ni | .notFocus => True
  | .pi | .really => False

instance : DecidablePred Form.Negated := λ f => by
  cases f <;> unfold Form.Negated <;> infer_instance

/-- A polarity item is licensed in a form iff a positive item finds the clause unnegated and
a negative one finds it negated. -/
def Licensed (e : PolarityItem) (f : Form) : Prop :=
  (e.IsPPI → ¬ f.Negated) ∧ (e.IsNPI → f.Negated)

instance (e : PolarityItem) (f : Form) : Decidable (Licensed e f) := by
  unfold Licensed; infer_instance

/-! ### The paper's examples -/

/-- An example, with the position of its negation, if any, its reported bias, its VERUM
form and its polarity item, each when the paper gives one, and its judgment. -/
structure Row where
  negation : Option (Option Negation.Position)
  bias : Option SignType
  form : Option Form
  item : Option PolarityItem
  judgment : Judgment

/-- A datum read into its row. -/
def Row.ofDatum (e : Datum) : Row where
  negation := e.parse? "negation"
    [("preposed", some Negation.Position.preposed), ("nonPreposed", some .nonPreposed),
      ("none", none)]
  bias := e.parse? "bias" [("positive", (1 : SignType)), ("negative", -1), ("none", 0)]
  form := e.parse? "form" [("pi", Form.pi), ("ni", .ni), ("really", .really),
    ("notFocus", .notFocus)]
  item := e.parse? "item"
    [("too", English.PolarityItems.too), ("either", English.PolarityItems.either)]
  judgment := e.judgment

/-- The paper's examples. -/
def data : List Row := Examples.all.map Row.ofDatum

-- (6), (7), (77), (80)
theorem licensed_iff_acceptable :
    ∀ d ∈ data, ∀ e ∈ d.item.toList, ∀ f ∈ d.form.toList,
      (Licensed e f ↔ d.judgment = .acceptable) := by
  decide

-- (1), (5), (14), (18)
theorem bias_of_negation :
    ∀ d ∈ data, ∀ n ∈ d.negation.toList, ∀ b ∈ d.bias.toList,
      (n = some .preposed → b = 1) ∧ (n = some .nonPreposed → b = 0) := by
  decide

theorem bias_of_form :
    ∀ d ∈ data, ∀ f ∈ d.form.toList, ∀ b ∈ d.bias.toList, b = f.implicature := by
  decide

end RomeroHan2004
