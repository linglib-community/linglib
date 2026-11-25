module

public import Linglib.Syntax.Mereological.Spine
public import Linglib.Data.Examples.WangSun2026
public import Linglib.Syntax.Spine.Hosting

/-!
# Wang and Sun (2026): Detaching Mandarin Classifiers from Nouns

This file formalizes [wang-sun-2026]'s account of three restrictions on Mandarin classifier
phrases in [adger-2025]'s mereological syntax. A classifier is not a projection of the noun but
an object of its own, (7a): it subjoins to Q as Q's 1-part, the numeral is Q's 2-part, and the
noun, if present, is the classifier's 1-part, (7b), (26). Dimensionality then leaves no room at
Q, so a degree-modified adjective cannot sit between the numeral and the classifier, (29a)
(`subjoin_modifier_q`), although it subjoins to the classifier as its 2-part, (28a)
(`subjoin_modifier_cl`), or to D, (28b) (`subjoin_modifier_d`). The classifier is on Q's
complementation line, (26b) (`spine_q`), and spells out together with Q, at Q (`words`), so
every object in which the classifier is pronounced has the numeral and the noun pronounced in it
too (`pronouncedIn_of_cl`). The particle *de* realises Mod, (7c): with *de* after the classifier
the quantity phrase is the 1-part of a Mod that is D's 2-part, and the classifier is reached
from D only across dimensions, (34)–(35) (`not_clVisible_numClDeN`). Visibility from D
is the paper's structural correlate of the sortal reading, glasses as entities, against the
mensural reading, glassfuls, (33) (`reading`). Nothing more, such as a second *de*-modifier, can
subjoin to the filled D, (37a) (`subjoin_numClDeN`). In the measure use the classifier has no
noun and Q is the 2-part of Deg, off the complementation line of the predicate, (45)
(`spine_pred`).

Extraction runs by Angular Locality, (40), on the clausal structure of (41): the object D is
the 2-part of O, and O, v and Asp are the 1-part chain of C. A wh-numeral first subjoins to D
and from there to C, (41) (`wh_numeral`); with a *de*-modifier in D's 2-part the numeral can
neither subjoin to D nor, in any derivation, reach C, (39b), (42) (`wh_numeral_modifier`).
Topicalisation of the whole D reaches C at once, (43c) (`topic_d`); the noun must subjoin to D
first, stranding the numeral and classifier, (43d) (`topic_n`), which a modifier as the
classifier's 2-part permits, (44a) (`topic_n_modifier_cl`), and a modifier as D's 2-part blocks
for good, (44b) (`topic_n_modifier_d`).

These predictions match the judgments of the paper's rows. A modifier subjoins exactly where
the row is acceptable. A string of the nominal is fronted alone exactly when some object in which
just that string is pronounced becomes a part of C: the noun and the whole nominal front, and
neither the classifier with the noun nor the numeral with the classifier does, there being no
such object. The wh-numeral becomes a part of C exactly in the acceptable rows.

## Implementation notes

* The nominal structures and the clause of (41) are `Parthood` values on one type of objects, so
  visibility from D, Dimensionality at Q and D, and extraction are read off the same parthood
  relations, and each claim is checked by `decide`. In the clause, Mod stands for the whole
  modifier, whose internal structure, (27), is given only in the nominal structures.
* The collective spell-out of Q with Cl is a division of D's spine into words, each with the
  object at which it is pronounced, as `Spine.hosting` takes them. An object is pronounced in
  `X` when its site is `X` or inside `X`, and fronting moves an object with everything
  pronounced in it. The order of the words, (7e), is not represented; the adjacency of the
  numeral and the classifier is stated as Dimensionality at Q, which is what the paper derives
  it from.
* The topicalisation of the whole D in (43c) is proved for the structure without a modifier.

## TODO

* A bare adjective before the classifier, (29b), is in the paper part of what is pronounced at Q
  and not an object, so the row has no structure of its own here.
* The rows on a modifier between the demonstrative and the numeral, (31), and on a modifier
  nested inside the modifier of D, (37b), are not derived.
* The readings of (33) are paired with `reading` by name only; the rows carry them as untyped
  features.

## References

* [wang-sun-2026]
* [adger-2025]
-/

@[expose] public section

namespace WangSun2026

open MereologicalSyntax MereologicalSyntax.Parthood

/-- The objects of the nominal structures and of the clausal structure (41). -/
inductive Node
  | C | Asp | v | O | V | Agent | D | Q | Cl | N | Num | Mod | Deg | A | Adv | Pred
  deriving DecidableEq, Fintype, Repr

/-! ### Structures, (26)–(28), (34), (45) -/

/-- In *yī zhāng zhuōzi* 'a table', (26), beside the modifier *hěn dà de* 'very big', (27), N is
the 1-part of Cl, Cl the 1-part and the numeral the 2-part of Q, and Q the 1-part of D; Mod, the
spell-out of *de*, has the degree object Deg as its 1-part, whose 1-part is A and 2-part Adv. -/
def numClN : Parthood Node where
  part
    | .one => fun
      | .D => some .Q | .Q => some .Cl | .Cl => some .N | .Mod => some .Deg | .Deg => some .A
      | _ => none
    | .two => fun | .Q => some .Num | .Deg => some .Adv | _ => none

/-- In *yī zhāng hěn dà de zhuōzi*, (28a), the modifier is the classifier's 2-part. -/
def numClModN : Parthood Node := numClN.addPart .two .Mod .Cl

/-- In *hěn dà de yī zhāng zhuōzi*, (28b), the modifier is D's 2-part. -/
def modNumClN : Parthood Node := numClN.addPart .two .Mod .D

/-- In *sān bēi de jiǔ* 'three glassfuls of liquor', (34b), the noun is D's 1-part, and the quantity
phrase, with a bare classifier, is the 1-part of Mod, D's 2-part. -/
def numClDeN : Parthood Node where
  part
    | .one => fun | .D => some .N | .Mod => some .Q | .Q => some .Cl | _ => none
    | .two => fun | .D => some .Mod | .Q => some .Num | _ => none

/-- In *duō sān kē* 'three (units) more', (45b), the quantity phrase, with a bare classifier, is the
2-part of Deg, whose 1-part is the adjective, under the predicate object. -/
def numClPred : Parthood Node where
  part
    | .one => fun | .Pred => some .Deg | .Deg => some .A | .Q => some .Cl | _ => none
    | .two => fun | .Deg => some .Q | .Q => some .Num | _ => none

/-! ### Modification, (28)–(29), (37) -/

/-- Q has both parts, so the modifier cannot subjoin between the numeral and the classifier,
(29a). -/
theorem subjoin_modifier_q : numClN.subjoin .Mod .Q = none := subjoin_eq_none_iff.2 ⟨rfl, rfl⟩

/-- The classifier has room for the modifier as its 2-part, (28a). -/
theorem subjoin_modifier_cl : numClN.subjoin .Mod .Cl = some numClModN := by decide +kernel

/-- So does D, (28b). -/
theorem subjoin_modifier_d : numClN.subjoin .Mod .D = some modNumClN := by decide +kernel

/-- With *de* after the classifier D is full, so nothing more subjoins to it, (37a). -/
theorem subjoin_numClDeN (x : Node) : numClDeN.subjoin x .D = none :=
  subjoin_eq_none_iff.2 ⟨rfl, rfl⟩

/-! ### Spell-out lines, (26b), (45b) -/

/-- The spine of Q is the noun, the classifier and Q, so the classifier spells out with Q (26b). -/
theorem spine_q : numClN.spine .Q = ⟨[.N, .Cl, .Q]⟩ := by decide +kernel

/-- Pred, Deg and A spell out together, (45b); the quantity phrase, Deg's 2-part, is off the
line. -/
theorem spine_pred : numClPred.spine .Pred = ⟨[.A, .Deg, .Pred]⟩ := by decide +kernel

/-! ### Visibility and the reading of a classifier, (33)–(36) -/

/-- The classifier is visible from D when it is one of D's 1-parts. -/
abbrev ClVisible (P : Parthood Node) : Prop := P.NPart .one .Cl .D

theorem clVisible_numClN : ClVisible numClN := by decide +kernel

theorem clVisible_numClModN : ClVisible numClModN := by decide +kernel

theorem clVisible_modNumClN : ClVisible modNumClN := by decide +kernel

/-- With *de* the classifier is reached from D only across dimensions, (34b), so it is
invisible. -/
theorem not_clVisible_numClDeN : ¬ ClVisible numClDeN := by decide +kernel

theorem nVisible : numClN.NPart .one .N .D ∧ numClDeN.NPart .one .N .D := by decide +kernel

/-- A classifier denotes a concrete object or an abstract unit. -/
inductive Reading
  | sortal
  | mensural
  deriving DecidableEq

/-- The reading of the classifier at a nominal is sortal when the classifier is visible from D,
and mensural otherwise. -/
def reading (P : Parthood Node) : Reading := if ClVisible P then .sortal else .mensural

theorem reading_numClN : reading numClN = .sortal := by decide +kernel

theorem reading_numClDeN : reading numClDeN = .mensural := by decide +kernel

theorem reading_numClModN : reading numClModN = .sortal := by decide +kernel

theorem reading_modNumClN : reading modNumClN = .sortal := by decide +kernel

/-! ### Extraction by Angular Locality, (39)–(44) -/

/-- In *Sān gè píngguǒ, Zhāngsān chī-le* before topicalisation, (41), (43), D is the 2-part of O, O
the 1-part of v, v of Asp, Asp of C, and the agent, the 2-part of v, has subjoined to Asp. -/
def clause : Parthood Node where
  part
    | .one => fun
      | .C => some .Asp | .Asp => some .v | .v => some .O | .O => some .V
      | .D => some .Q | .Q => some .Cl | .Cl => some .N | _ => none
    | .two => fun
      | .Asp => some .Agent | .v => some .Agent | .O => some .D | .Q => some .Num | _ => none

/-- `clause` with a modifier as the classifier's 2-part, (39a), (44a). -/
def clauseModCl : Parthood Node := clause.addPart .two .Mod .Cl

/-- `clause` with a modifier as D's 2-part, (39b), (44b). -/
def clauseModD : Parthood Node := clause.addPart .two .Mod .D

/-- `clauseModCl` after the wh-numeral subjoins to D, (41). -/
def clauseModClNum : Parthood Node := clauseModCl.addPart .two .Num .D

/-- `clause` after the noun subjoins to D, (43d). -/
def clauseN : Parthood Node := clause.addPart .two .N .D

/-- `clauseModCl` after the noun subjoins to D, (44a). -/
def clauseModClN : Parthood Node := clauseModCl.addPart .two .N .D

/-- The objects inside D in the clause of (41), other than a modifier in D's 2-part. -/
abbrev inD : Set Node := {.D, .Q, .Cl, .N, .Num}

/-- A wh-numeral subjoins to D and then to C, but not directly to C (41). -/
theorem wh_numeral :
    ¬ clauseModCl.CanSubjoin .Num .C ∧ clauseModCl.Subjoins .Num .D clauseModClNum ∧
      clauseModClNum.Subjoins .Num .C (clauseModClNum.addPart .two .Num .C) := by
  decide +kernel

/-- With a modifier as D's 2-part, Dimensionality blocks the wh-numeral at D, and it never becomes a
part of C (42). -/
theorem wh_numeral_modifier :
    clauseModD.CanSubjoin .Num .D ∧ clauseModD.subjoin .Num .D = none ∧
      ¬ clauseModD.Reaches .Num .C :=
  ⟨by decide +kernel, subjoin_eq_none_iff.2 ⟨rfl, rfl⟩,
    IsDomain.not_reaches (S := inD) (b := .D) (c := .Mod) (by decide +kernel) rfl (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide)⟩

/-- The whole D, the 2-part of O, subjoins to C, (43c). -/
theorem topic_d : clause.CanSubjoin .D .C := by decide +kernel

/-- The noun cannot subjoin directly to C but reaches C through D, stranding the numeral and
classifier (43d). -/
theorem topic_n :
    ¬ clause.CanSubjoin .N .C ∧ clause.Subjoins .N .D clauseN ∧
      clauseN.Subjoins .N .C (clauseN.addPart .two .N .C) := by
  decide +kernel

/-- A modifier as the classifier's 2-part leaves D's 2-part free, and the noun topicalises,
(44a). -/
theorem topic_n_modifier_cl :
    clauseModCl.Subjoins .N .D clauseModClN ∧
      clauseModClN.Subjoins .N .C (clauseModClN.addPart .two .N .C) := by
  decide +kernel

/-- A modifier as D's 2-part fills D: the noun cannot subjoin to it, and no derivation makes the
noun a part of C, (44b). -/
theorem topic_n_modifier_d :
    clauseModD.subjoin .N .D = none ∧ ¬ clauseModD.Reaches .N .C :=
  ⟨subjoin_eq_none_iff.2 ⟨rfl, rfl⟩,
    IsDomain.not_reaches (S := inD) (b := .D) (c := .Mod) (by decide +kernel) rfl (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide)⟩

/-! ### Spell-out at Q, (26b) -/

/-- The words of D's spine, each with the object at which it is pronounced, (26b): the classifier
and Q spell out together at Q. -/
def words : List (List Node × Node) := [([.N], .N), ([.Cl, .Q], .Q), ([.D], .D)]

-- the words divide D's spine, and the classifier is hosted at Q
theorem hosting_words :
    words.flatMap Prod.fst = (numClN.spine .D).heads ∧
      Spine.hosting words = [.N, .Q, .Q, .D] := by
  decide +kernel

-- a stretch of the spine spells out at one of its own objects
theorem isContiguous_hosting_words : IsContiguous (Spine.hosting words).get :=
  Spine.isContiguous_hosting (by decide) (by decide)

/-- The object at which `x` is pronounced: the site of its word on D's spine, and `x` itself off
the spine. -/
def site (x : Node) : Node := (words.find? fun w ↦ decide (x ∈ w.1)).elim x (·.2)

/-- `x` is pronounced in `X`: the site of `x` is `X` or inside it. -/
def PronouncedIn (P : Parthood Node) (x X : Node) : Prop := site x = X ∨ P.Descendant (site x) X

instance (P : Parthood Node) (x X : Node) : Decidable (PronouncedIn P x X) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The string `W` of the nominal is fronted alone: some object in which exactly the objects of
`W`, among the numeral, the classifier, the noun and the modifier, are pronounced becomes a part
of C. -/
def Fronts (P : Parthood Node) (W : List Node) : Prop :=
  ∃ X, (∀ w ∈ [Node.Num, .Cl, .N, .Mod], PronouncedIn P w X ↔ w ∈ W) ∧ P.Reaches X .C

/-- Every object in which the classifier is pronounced has the numeral and the noun pronounced in
it too, so fronting the classifier strands neither, (5c), (14). -/
theorem pronouncedIn_of_cl :
    ∀ X, PronouncedIn clause .Cl X → PronouncedIn clause .Num X ∧ PronouncedIn clause .N X := by
  decide +kernel

-- as an object the classifier subjoins to D and from there to C, as the noun does
theorem cl_reaches : clause.Reaches .Cl .C :=
  have h : clause.Subjoins .Cl .D (clause.addPart .two .Cl .D) ∧
      (clause.addPart .two .Cl .D).Subjoins .Cl .C
        ((clause.addPart .two .Cl .D).addPart .two .Cl .C) := by decide +kernel
  Reaches.of_derives h.1.derives h.2.reaches

/-! ### The data -/

/-- A modifier subjoins to the classifier and not to Q, and nothing more subjoins to a filled D:
the rows on the position of a modifier, (4c), (8a), (28a), (29a), and on a second *de*-modifier,
(37a). -/
theorem modification_rows :
    ((numClN.subjoin .Mod .Q).isSome ↔ Examples.ex_1.judgment = .acceptable) ∧
      ((numClN.subjoin .Mod .Q).isSome ↔ Examples.ex_3.judgment = .acceptable) ∧
      ((numClN.subjoin .Mod .Cl).isSome ↔ Examples.ex_2.judgment = .acceptable) ∧
      ((numClN.subjoin .Mod .Cl).isSome ↔ Examples.ex_5.judgment = .acceptable) ∧
      ((∃ x, (numClDeN.subjoin x .D).isSome) ↔ Examples.ex_14.judgment = .acceptable) := by
  decide +kernel

/-- A string of the nominal is fronted alone exactly in the acceptable rows on topicalisation:
the classifier with the noun, (5c), the noun, (13b), the numeral with the classifier, (14a), the
whole nominal, (43a), and the noun past a modifier, (44). -/
theorem fronting_rows :
    (Fronts clause [.Cl, .N] ↔ Examples.ex_6.judgment = .acceptable) ∧
      (Fronts clause [.N] ↔ Examples.ex_7.judgment = .acceptable) ∧
      (Fronts clause [.Num, .Cl] ↔ Examples.ex_8.judgment = .acceptable) ∧
      (Fronts clause [.Num, .Cl, .N] ↔ Examples.ex_16.judgment = .acceptable) ∧
      (Fronts clauseModCl [.N] ↔ Examples.ex_17.judgment = .acceptable) ∧
      (Fronts clauseModD [.N] ↔ Examples.ex_18.judgment = .acceptable) := by
  have h₆ : ∀ X, ¬ ∀ w ∈ [Node.Num, .Cl, .N, .Mod],
      PronouncedIn clause w X ↔ w ∈ [Node.Cl, .N] := by decide +kernel
  have h₈ : ∀ X, ¬ ∀ w ∈ [Node.Num, .Cl, .N, .Mod],
      PronouncedIn clause w X ↔ w ∈ [Node.Num, .Cl] := by decide +kernel
  have h₁₈ : ∀ X, (∀ w ∈ [Node.Num, .Cl, .N, .Mod],
      PronouncedIn clauseModD w X ↔ w ∈ [Node.N]) → X = .N ∨ X = .Cl := by decide +kernel
  refine ⟨iff_of_false (fun ⟨X, hX, _⟩ ↦ h₆ X hX) (by decide),
    iff_of_true ⟨.N, by decide +kernel,
      Reaches.of_derives topic_n.2.1.derives topic_n.2.2.reaches⟩ rfl,
    iff_of_false (fun ⟨X, hX, _⟩ ↦ h₈ X hX) (by decide),
    iff_of_true ⟨.D, by decide +kernel,
      Subjoins.reaches (Q := clause.addPart .two .D .C) (by decide +kernel)⟩ rfl,
    iff_of_true ⟨.N, by decide +kernel,
      Reaches.of_derives topic_n_modifier_cl.1.derives topic_n_modifier_cl.2.reaches⟩ rfl,
    iff_of_false ?_ (by decide)⟩
  rintro ⟨X, hX, hC⟩
  rcases h₁₈ X hX with rfl | rfl
  · exact topic_n_modifier_d.2 hC
  · exact IsDomain.not_reaches (P := clauseModD) (S := inD) (b := .D) (c := .Mod)
      (by decide +kernel) rfl (by decide) (by decide) (by decide) (by decide +kernel) (by decide) hC

/-- The wh-numeral becomes a part of C exactly in the acceptable rows, (39). -/
theorem wh_rows :
    (clauseModCl.Reaches .Num .C ↔ Examples.ex_9.judgment = .acceptable) ∧
      (clauseModD.Reaches .Num .C ↔ Examples.ex_10.judgment = .acceptable) :=
  ⟨iff_of_true (Reaches.of_derives wh_numeral.2.1.derives wh_numeral.2.2.reaches) rfl,
    iff_of_false wh_numeral_modifier.2.2 (by decide)⟩

end WangSun2026
