module

public import Linglib.Semantics.ArgumentStructure.Affectedness
public import Linglib.Semantics.ArgumentStructure.LevinClass.Properties
public import Linglib.Logic.Modal.Defs
public import Linglib.Core.Order.UpperLower.Cover
public import Linglib.Data.Examples.Beavers2010
public import Linglib.Data.Examples.Readers
public import Studies.Dowty1991
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.WithTopBot
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Beavers (2010): The Structure of Lexical Meaning

This file formalizes Beavers's account of object/oblique alternations. A role is a set of lexical
entailments closed under entailment, and an alternating participant's role as oblique is minimally
weaker than its role as direct argument. The affectedness entailments are the conditions of the
Affectedness Hierarchy, with the scalar relation read, as the paper reads it, as possibly ending at
some goal. A variant's logical form says where the participant ends up, at the goal the predicate
supplies, at some goal, or possibly so, and [the role it lexically assigns is the degree that
result names](##mem_lexicalRole). [Every attested alternation is then a minimal
contrast](##lexicalRole_wcovBy_of_mem_attested), as is [a conative that embeds the object's result
under a modality, unless that result is the predicate's goal](##degree_possibly_wcovBy_iff), and
[the judgments of the conatives and of the *load* locative under diagnostics of change
follow](##diagnosed_rows). The double modality of *hit at* leaves it unspecified for change [only
along a modal base that is not transitive](##holds_potential_possibly_of_isTrans). Total traversal
of a path is quantized change read of the scale, and the dative alternation runs on a chain of
arrival and possession.

## Implementation notes

* The contentful sets of affectedness entailments are the lower sets, which correspond to the
  degrees by Birkhoff's representation.
* Potential for change is modal, and it generalizes nonquantized change only when the actual world
  is among the worlds its modal base admits, which the paper assumes and every model satisfies;
  quantized and nonquantized change then need no scalar relation beyond the result. Beavers leaves
  the modal base open.
* A lexical entailment of a logical form is one it has in every model, whatever the verb's own
  relation, which can only restrict the events. In a locative variant each participant's role is
  read off its own conjunct, the other participant's conjunct counting as part of the verb's
  relation.
* The paper gives no logical forms for the *clear* and *hit* locatives, only roles: quantized change
  for both participants of *clear*, potential for change for both of *hit*. Their results are the
  ones that name these roles.
* Each alternation is typed by the section of Levin's catalogue it falls under. Levin's *cut* class
  lists no locative alternation, so the *cut* locative, which Beavers takes from Fillmore, has none.
* The degrees of traversal are the formulas of the degrees of affectedness abstracted over the
  scale instead of the theme, so the file states each formula once. Only total traversal enters the
  extended hierarchy of roles, and naming a role by its strongest entailment rules out affected
  paths, as the paper assumes.
* The paper states its conditions of a sentence with the theme and event given; the file states
  them of a relation, over all themes and events. A goal the predicate supplies is fixed across its
  events and read by the result relation relative to the theme and scale, as the size of the pizza
  or the end of the stairs.
* Beavers's rough correspondence with Dowty's proto-patient entailments is not formalized, since
  it marks two of its cells as uncertain.

## Errata

* Two cross-references in the discussion of *climb* are off by four: the scalar analysis "as in
  88" is (84), and the degrees of traversal "as in 89" are (85).
* (38a) writes result′(x, g, s, e), swapping the scale and goal arguments of (31) and (38b).

## TODO

* The telicity diagnostic (32), *What happened to x* for the *load* locative (53), and the
  diagnostics of the *cut* locative (55)–(56).
* Beavers's resolution of Dowty's *hit the fence with the stick* problem, which needs Dowty's own
  discussion checked against the profiles of `Dowty1991`: Beavers counts the stick's dependent
  motion as a Proto-Patient entailment, where those profiles give it movement, a Proto-Agent one.
* Fragment entries for *clear* and *climb*, so that every alternation names its verb.

## References

* [J. Beavers, *The structure of lexical meaning: Why semantics really matters*
  (2010)][beavers-2010]
* [J. Beavers, *On Affectedness* (2011)][beavers-2011]
* [D. Dowty, *Thematic proto-roles and argument selection* (1991)][dowty-1991]
* [B. Levin, *English Verb Classes and Alternations: A Preliminary Investigation*
  (1993)][levin-1993]
-/

@[expose] public section

namespace Beavers2010

open ArgumentStructure ModalLogic
open scoped SetRel

/-! ### L-thematic roles as sets of entailments ((65)–(67))

An L-thematic role is a set of lexical entailments. The three affectedness entailments of (65)
entail one another, so a set of them is contentful exactly when it is closed under entailment, and
the contentful sets are the degrees of affectedness (`AffectednessDegree.entailments`). -/

example : Fintype.card AffectednessEntailment = 3 := by decide

example : Fintype.card (Set AffectednessEntailment) = 8 := by rw [Fintype.card_set]; rfl

example : Nat.card (LowerSet AffectednessEntailment) = 4 := by
  rw [← Nat.card_congr AffectednessDegree.entailments.toEquiv, Nat.card_eq_fintype_card]; rfl

/-! ### Models of the logical forms ((31), (38), (40)) -/

/-- A model of the logical forms: worlds with a modal base under which the actual world is
accessible from itself, participants, scales, goals with the goal the predicate supplies, events,
the verb's own relation and the result relation. -/
structure Model where
  /-- The worlds. -/
  W : Type
  /-- The participants. -/
  α : Type
  /-- The scales. -/
  S : Type
  /-- The goals. -/
  G : Type
  /-- The events. -/
  β : Type
  /-- The modal base, relating a world to the worlds it admits. -/
  acc : SetRel W W
  /-- The actual world. -/
  w₀ : W
  /-- The actual world is among the worlds its modal base admits. -/
  refl : w₀ ~[acc] w₀
  /-- The goal the predicate supplies. -/
  goal : G
  /-- The verb's own relation between the participant and the event. -/
  V : α → β → Prop
  /-- The result relation: at `w`, the participant `x` ends `e` at `g` on `s`. -/
  R : W → α → S → G → β → Prop

namespace Model

variable (M : Model)

/-- The scalar relation of the unspecified degree (40a) read as the paper reads it, possibly ending
at some goal on the scale in a world the modal base admits, which makes potential for change
(38a). -/
def possibleResult : M.α → M.S → M.β → Prop :=
  fun x s e ↦ ◇[M.acc] (fun w ↦ ∃ g, M.R w x s g e) M.w₀

variable {M} {φ : M.α → M.β → Prop}

-- (31a)
theorem holds_quantized_iff :
    AffectednessDegree.Holds M.possibleResult (M.R M.w₀) φ .quantized ↔
      ∃ g, ∀ x e, φ x e → ∃ s, M.R M.w₀ x s g e :=
  exists_congr fun _ ↦ forall₂_congr fun _ _ ↦ imp_congr_right fun _ ↦
    ⟨fun ⟨s, _, h⟩ ↦ ⟨s, h⟩, fun ⟨s, h⟩ ↦ ⟨s, ⟨M.w₀, M.refl, _, h⟩, h⟩⟩

-- (31b)
theorem holds_nonquantized_iff :
    AffectednessDegree.Holds M.possibleResult (M.R M.w₀) φ .nonquantized ↔
      ∀ x e, φ x e → ∃ s g, M.R M.w₀ x s g e :=
  forall₂_congr fun _ _ ↦ imp_congr_right fun _ ↦
    ⟨fun ⟨s, _, g, h⟩ ↦ ⟨s, g, h⟩, fun ⟨s, g, h⟩ ↦ ⟨s, ⟨M.w₀, M.refl, g, h⟩, g, h⟩⟩

end Model

/-! ### The logical forms of the variants (§3.2)

A variant's logical form conjoins the verb's own relation with what it says about where the
participant ends up, and its lexical entailments are those it has in every model. -/

/-- What a logical form says about where a participant ends up. -/
inductive Result where
  /-- At the goal the predicate supplies, as *ate the pizza* says of the pizza ((42a)). -/
  | goal
  /-- At some goal, as *ate at the pizza* and *cut the rope* say ((42b), (44a)). -/
  | someGoal
  /-- Possibly as `r` says, embedding `r` under a modality, as *cut at the rope* and *hit the rope*
  do with some goal and *hit at the rope* with possibly some goal ((44b), (46)). -/
  | possibly (r : Result)
  deriving DecidableEq, Repr

namespace Result

/-- What a result says of a participant, a scale and an event at a world. -/
def HoldsAt (M : Model) : Result → M.W → M.α → M.S → M.β → Prop
  | .goal, w, x, s, e => M.R w x s M.goal e
  | .someGoal, w, x, s, e => ∃ g, M.R w x s g e
  | .possibly r, w, x, s, e => ◇[M.acc] (fun v ↦ r.HoldsAt M v x s e) w

/-- The logical form of a variant with the result `r`: the verb's relation holds and `r` holds at
the actual world on some scale. -/
def form (r : Result) (M : Model) : M.α → M.β → Prop :=
  fun x e ↦ M.V x e ∧ ∃ s, r.HoldsAt M M.w₀ x s e

/-- The role a result lexically assigns: the affectedness entailments its logical form has in every
model. -/
def lexicalRole (r : Result) : LowerSet AffectednessEntailment :=
  ⟨⋂ M : Model, affectednessRole M.possibleResult (M.R M.w₀) (r.form M),
    isLowerSet_iInter fun _ ↦ LowerSet.lower _⟩

/-- The degree of affectedness a result names. -/
def degree : Result → AffectednessDegree
  | .goal => .quantized
  | .someGoal => .nonquantized
  | .possibly .goal | .possibly .someGoal => .potential
  | .possibly (.possibly _) => .unspecified

theorem holds_degree (M : Model) :
    ∀ r : Result, AffectednessDegree.Holds M.possibleResult (M.R M.w₀) (r.form M) r.degree
  | .goal => ⟨M.goal, fun _ _ ⟨_, s, h⟩ ↦ ⟨s, ⟨M.w₀, M.refl, _, h⟩, h⟩⟩
  | .someGoal => fun _ _ ⟨_, s, g, h⟩ ↦ ⟨s, ⟨M.w₀, M.refl, g, h⟩, g, h⟩
  | .possibly .goal => fun _ _ ⟨_, s, v, hv, h⟩ ↦ ⟨s, v, hv, _, h⟩
  | .possibly .someGoal => fun _ _ ⟨_, s, h⟩ ↦ ⟨s, h⟩
  | .possibly (.possibly _) => trivial

private theorem holdsAt_of_forall {M : Model} {w : M.W} (hw : w ~[M.acc] w)
    (hR : ∀ x s g e, M.R w x s g e) : ∀ (r : Result) x s e, r.HoldsAt M w x s e
  | .goal, x, s, e => hR x s _ e
  | .someGoal, x, s, e => ⟨M.goal, hR x s _ e⟩
  | .possibly r, x, s, e => ⟨w, hw, holdsAt_of_forall hw hR r x s e⟩

/-- Two events of the predicate end at different goals. -/
private def twoGoals : Model :=
  ⟨Unit, Unit, Unit, Bool, Bool, .univ, (), Set.mem_univ _, true, fun _ _ ↦ True,
    fun _ _ _ g e ↦ g = e⟩

/-- The result holds at a world the actual world accesses, but not at the actual world. -/
private def elsewhere : Model :=
  ⟨Bool, Unit, Unit, Unit, Unit, .univ, false, Set.mem_univ _, (), fun _ _ ↦ True,
    fun w _ _ _ _ ↦ w = true⟩

/-- The actual world reaches in two steps a world it does not access. -/
private def twoSteps : Model :=
  ⟨ℕ, Unit, Unit, Unit, Unit, {p | p.2 = p.1 ∨ p.2 = p.1 + 1}, 0, Or.inl rfl, (), fun _ _ ↦ True,
    fun w _ _ _ _ ↦ w = 2⟩

private theorem not_quantized_twoGoals : ¬ AffectednessDegree.Holds twoGoals.possibleResult
    (twoGoals.R twoGoals.w₀) (someGoal.form twoGoals) .quantized := by
  rintro ⟨g, h⟩
  obtain ⟨_, _, h⟩ := h () (!g) ⟨trivial, (), _, rfl⟩
  revert h; cases g <;> nofun

private theorem not_nonquantized_elsewhere (r : Result) : ¬ AffectednessDegree.Holds
    elsewhere.possibleResult (elsewhere.R elsewhere.w₀) ((possibly r).form elsewhere)
    .nonquantized := fun h ↦
  let ⟨_, _, _, h⟩ := h () () ⟨trivial, (), true, Set.mem_univ _,
    holdsAt_of_forall (M := elsewhere) (w := true) (Set.mem_univ _) (fun _ _ _ _ ↦ rfl) r () () ()⟩
  Bool.false_ne_true h

private theorem not_potential_twoSteps (r : Result) : ¬ AffectednessDegree.Holds
    twoSteps.possibleResult (twoSteps.R twoSteps.w₀) ((possibly (possibly r)).form twoSteps)
    .potential := fun h ↦ by
  obtain ⟨_, v, hv, _, rfl⟩ := h () () ⟨trivial, (), (1 : ℕ), Or.inr rfl, (2 : ℕ), Or.inr rfl,
    holdsAt_of_forall (M := twoSteps) (w := (2 : ℕ)) (Or.inl rfl) (fun _ _ _ _ ↦ rfl) r () () ()⟩
  exact absurd (show (2 : ℕ) = 0 ∨ (2 : ℕ) = 0 + 1 from hv) (by decide)

private theorem exists_not_holds : ∀ {r : Result} {d : AffectednessDegree}, r.degree < d →
    ∃ M : Model, ¬ AffectednessDegree.Holds M.possibleResult (M.R M.w₀) (r.form M) d
  | .goal, d, h => absurd h (by cases d <;> decide)
  | .someGoal, d, h => ⟨twoGoals, fun hd ↦ not_quantized_twoGoals <| by
      cases d <;> first | exact hd | exact absurd h (by decide)⟩
  | .possibly .goal, d, h | .possibly .someGoal, d, h =>
      ⟨elsewhere, fun hd ↦ not_nonquantized_elsewhere _ <| AffectednessDegree.holds_antitone _ _ _
        (show .nonquantized ≤ d by revert h; cases d <;> decide) hd⟩
  | .possibly (.possibly _), d, h =>
      ⟨twoSteps, fun hd ↦ not_potential_twoSteps _ <| AffectednessDegree.holds_antitone _ _ _
        (show .potential ≤ d by change .unspecified < d at h; revert h; cases d <;> decide) hd⟩

/-- A logical form lexically entails exactly the affectedness entailments at most as strong as the
degree its result names, so the roles of the variants are those Tables 3 and 4 give. -/
theorem mem_lexicalRole {r : Result} {e : AffectednessEntailment} :
    e ∈ r.lexicalRole ↔ e.1 ≤ r.degree := by
  rw [lexicalRole, LowerSet.mem_mk, Set.mem_iInter]
  exact ⟨fun h ↦ le_of_not_gt fun hlt ↦ let ⟨M, hM⟩ := exists_not_holds hlt; hM (h M),
    fun h M ↦ AffectednessDegree.holds_antitone _ _ _ h (holds_degree M r)⟩

theorem lexicalRole_eq (r : Result) : r.lexicalRole = r.degree.entailments :=
  SetLike.ext fun _ ↦ mem_lexicalRole

/-- Embedding the object variant's result under a modality, as the *cut* and *hit* conatives do,
gives an oblique minimally weaker than the object unless the object's result is the predicate's
goal: an *eat at* that said only that the pizza was possibly eaten up would skip nonquantized
change, so the unified modal analysis of the conative floated on p. 838 must keep the change of
(42b). -/
theorem degree_possibly_wcovBy_iff {r : Result} : (possibly r).degree ⩿ r.degree ↔ r ≠ goal := by
  rcases r with _ | _ | (_ | _ | r)
  iterate 4 decide
  exact iff_of_true WCovBy.rfl (by simp)

-- p. 831: a variant entails the variant that embeds its result under a modality
theorem form_le_form_possibly (M : Model) (r : Result) : r.form M ≤ (possibly r).form M :=
  fun _ _ ⟨hV, s, h⟩ ↦ ⟨hV, s, M.w₀, M.refl, h⟩

theorem form_goal_le_form_someGoal (M : Model) : goal.form M ≤ someGoal.form M :=
  fun _ _ ⟨hV, s, h⟩ ↦ ⟨hV, s, _, h⟩

/-- Along a transitive modal base a result under a modality has potential for change however deeply
it is embedded, so *hit at* would pass *What happened to x* (39), against (48b): the double modality
of (46b) is weaker than potential for change only along a modal base that is not transitive. -/
theorem holds_potential_possibly_of_isTrans (M : Model) [M.acc.IsTrans] (r : Result) :
    AffectednessDegree.Holds M.possibleResult (M.R M.w₀) ((possibly r).form M) .potential :=
  fun x e ⟨_, s, h⟩ ↦ ⟨s, go r M.w₀ x s e h⟩
where
  go : ∀ (r : Result) (w : M.W) (x : M.α) (s : M.S) (e : M.β), (possibly r).HoldsAt M w x s e →
      ◇[M.acc] (fun v ↦ ∃ g, M.R v x s g e) w
    | .goal, _, _, _, _, ⟨v, hv, h⟩ => ⟨v, hv, _, h⟩
    | .someGoal, _, _, _, _, h => h
    | .possibly r, _, x, s, e, ⟨v, hv, h⟩ =>
      let ⟨u, hu, hg⟩ := go r v x s e h; ⟨u, M.acc.trans hv hu, hg⟩

end Result

open Result

/-! ### The MAP ((68)–(69))

Of two roles on a hierarchy, `Q ⩿ R` says that `Q` is minimally weaker than `R` ((68)). The
Morphosyntactic Alignment Principle requires an alternating participant's role as oblique to be
minimally weaker than its role as direct argument ((69)). -/

-- (66)
theorem entailments_wcovBy_entailments_iff (d d' : AffectednessDegree) :
    d.entailments ⩿ d'.entailments ↔ d ⩿ d' :=
  apply_wcovBy_apply_iff AffectednessDegree.entailments

-- p. 849: a minimal contrast drops one entailment of the direct role, its strongest
theorem exists_eq_insert_of_covBy {o d : AffectednessDegree} (h : o ⋖ d) :
    ∃ e ∉ o.entailments, e.1 = d ∧
      (d.entailments : Set AffectednessEntailment) = insert e (o.entailments : Set _) := by
  obtain ⟨e, he, hd⟩ :=
    LowerSet.covBy_iff_exists_insert.1 ((apply_covBy_apply_iff AffectednessDegree.entailments).2 h)
  have hmax := LowerSet.maximal_of_coe_eq_insert he hd
  have he₁ : e.1 ≤ d := hmax.1
  exact ⟨e, he, le_antisymm he₁ (hmax.2 (y := ⟨d, AffectednessDegree.supIrred_iff_ne_bot.2
    (ne_bot_of_gt h.lt)⟩) (show d ≤ d from le_rfl) he₁), hd⟩

theorem card_entailments (d : AffectednessDegree) : Nat.card d.entailments = d.strength := by
  rw [show Nat.card d.entailments = Nat.card {e : AffectednessEntailment // e.1 ≤ d} from rfl,
    Nat.card_eq_fintype_card]
  cases d <;> decide

-- (61), (63): counted, as Dowty's Corollary 2 counts them, Beavers's entailments order roles as
-- inclusion does
theorem card_entailments_lt_card_iff {o d : AffectednessDegree} :
    Nat.card o.entailments < Nat.card d.entailments ↔ o < d := by
  rw [card_entailments, card_entailments]
  cases o <;> cases d <;> decide

-- p. 846: Dowty's Corollary 2 can prefer as object a role that lacks an entailment of the oblique
example : ∃ p q : EntailmentProfile, Dowty1991.DirectObjectOver p q ∧ ¬ q ⊆ p :=
  ⟨{.changeOfState, .incrementalTheme}, {.stationary}, by decide, by decide⟩

/-! ### The attested alternations (Tables 3–4, (75)) -/

/-- An alternation: examples of a participant as direct argument and as oblique, the verb's class
and the section of Levin's catalogue the alternation falls under, if any, with what each variant's
logical form says about the result of the participant or, for a path, of the theme that traverses
it. -/
structure Alternation where
  /-- The example with the participant as direct argument. -/
  directEx : Datum
  /-- The example with the participant as oblique. -/
  obliqueEx : Datum
  /-- The verb's class. -/
  verbClass : LevinClass
  /-- The section of Levin's catalogue the alternation falls under. -/
  levinSection : Option DiathesisAlternation
  /-- The participant's result as direct argument. -/
  direct : Result
  /-- The participant's result as oblique. -/
  oblique : Result

open Examples

/-- *Ate her cake* against *ate at her cake* ((21), (42)). -/
def eat : Alternation := ⟨ex_21a, ex_21b, .eat, some .conative, .goal, .someGoal⟩

/-- *Cut the rope* against *cut at the rope* ((20), (44)). -/
def cut : Alternation := ⟨ex_20a, ex_20b, .cut, some .conative, .someGoal, .possibly .someGoal⟩

/-- *Hit Defarge* against *hit at Defarge* ((22), (46)). -/
def hit : Alternation :=
  ⟨ex_22a, ex_22b, .hit, some .conative, .possibly .someGoal, .possibly (.possibly .someGoal)⟩

/-- The wagon in *loaded the wagon with the hay* against *loaded the hay onto the wagon*, filled
as object and partly filled as oblique ((9), (49)). -/
def loadLocation : Alternation := ⟨ex_9b, ex_9a, .sprayLoad, some .sprayLoad, .goal, .someGoal⟩

/-- The hay in the same pair, all moved as object and partly moved as oblique ((9), (49)). -/
def loadTheme : Alternation := ⟨ex_9a, ex_9b, .sprayLoad, some .sprayLoad, .goal, .someGoal⟩

/-- The glass in *cut the glass with the diamond* against *cut the diamond on the glass*, damaged
as object and possibly damaged as oblique ((18), (54)). -/
def cutLocation : Alternation := ⟨ex_18b, ex_18a, .cut, none, .someGoal, .possibly .someGoal⟩

/-- The diamond in the same pair ((18), (54)). -/
def cutTheme : Alternation := ⟨ex_18a, ex_18b, .cut, none, .someGoal, .possibly .someGoal⟩

/-- The table in *cleared the table of the dishes* against *cleared the dishes off the table*,
cleared under both ((25), (75)). -/
def clearLocation : Alternation := ⟨ex_25a, ex_25b, .clear, some .clearTransitive, .goal, .goal⟩

/-- The dishes in the same pair ((25), (75)). -/
def clearTheme : Alternation := ⟨ex_25b, ex_25a, .clear, some .clearTransitive, .goal, .goal⟩

/-- The fence in *hit the fence with the stick* against *hit the stick against the fence*, impacted
and so with potential for change under both ((24), p. 851). -/
def hitLocation : Alternation :=
  ⟨ex_24a, ex_24b, .hit, some .withAgainst, .possibly .someGoal, .possibly .someGoal⟩

/-- The stick in the same pair, impacted and moved under both ((24), p. 851). -/
def hitTheme : Alternation :=
  ⟨ex_24b, ex_24a, .hit, some .withAgainst, .possibly .someGoal, .possibly .someGoal⟩

/-- The attested alternations of affectedness. -/
def attested : List Alternation :=
  [eat, cut, hit, loadLocation, loadTheme, cutLocation, cutTheme, clearLocation, clearTheme,
    hitLocation, hitTheme]

/-- Every attested alternation satisfies the MAP: the participant's lexical role as oblique is
minimally weaker than its lexical role as direct argument. -/
theorem lexicalRole_wcovBy_of_mem_attested :
    ∀ a ∈ attested, a.oblique.lexicalRole ⩿ a.direct.lexicalRole := by
  simp only [lexicalRole_eq, entailments_wcovBy_entailments_iff]
  decide

-- (69): the participant is realized both ways
theorem acceptable_of_mem_attested :
    ∀ a ∈ attested, a.directEx.judgment = .acceptable ∧ a.obliqueEx.judgment = .acceptable := by
  decide

-- (18): Levin's *cut* class neither attests nor stars a locative alternation
example : ¬ LevinClass.cut.Tests .locative ∧ ¬ LevinClass.cut.Tests .sprayLoad ∧
    ¬ LevinClass.cut.Tests .withAgainst := by
  decide

-- p. 831, (27): each conative's object variant entails its oblique variant
theorem affectednessRole_oblique_le_direct (M : Model) :
    ∀ a ∈ [eat, cut, hit], affectednessRole M.possibleResult (M.R M.w₀) (a.oblique.form M) ≤
      affectednessRole M.possibleResult (M.R M.w₀) (a.direct.form M) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨affectednessRole_antitone _ _ (form_goal_le_form_someGoal M),
    affectednessRole_antitone _ _ (form_le_form_possibly M _),
    affectednessRole_antitone _ _ (form_le_form_possibly M _)⟩

-- Table 3
theorem covBy_iff_exists_conative (q r : AffectednessDegree) :
    q ⋖ r ↔ ∃ a ∈ [eat, cut, hit], a.direct.degree = r ∧ a.oblique.degree = q := by
  revert q r; decide

-- (76): the oblique has more entailments than the object
example : ¬ AffectednessDegree.nonquantized ⩿ .potential := by decide

-- (77): the contrast skips nonquantized change
example : ¬ AffectednessDegree.potential ⩿ .quantized := by decide

/-! ### The diagnostics ((10), (34), (39)) -/

/-- Three diagnostics of affectedness. -/
inductive Diagnostic where
  /-- A continuation denying that `x` changed, *but nothing is different about x* or *but none of
  the hay moved*, infelicitous when the predicate entails that `x` changes ((10d), (34)). -/
  | noChange
  /-- A continuation denying that `x` changed completely, *but still needed a truck for the rest*,
  infelicitous when the predicate entails a quantized change of `x` ((10a), (11a)). -/
  | notAll
  /-- *What happened to x is …*, felicitous when the predicate entails potential for change of `x`
  ((39)). -/
  | whatHappened
  deriving DecidableEq, Repr

/-- A diagnostic accepts a predicate that gives the participant tested the degree `d`. -/
def Diagnostic.Accepts : Diagnostic → AffectednessDegree → Prop
  | .noChange, d => d < .nonquantized
  | .notAll, d => d < .quantized
  | .whatHappened, d => .potential ≤ d

instance : ∀ t d, Decidable (Diagnostic.Accepts t d)
  | .noChange, d => inferInstanceAs (Decidable (d < _))
  | .notAll, d => inferInstanceAs (Decidable (d < _))
  | .whatHappened, d => inferInstanceAs (Decidable (_ ≤ d))

/-- The diagnostic rows, each with the result its variant gives the participant tested and the
diagnostic it applies. -/
def diagnosed : List (Datum × Result × Diagnostic) :=
  [(ex_10a, loadTheme.direct, .notAll), (ex_10b, loadTheme.oblique, .notAll),
    (ex_10d, loadTheme.oblique, .noChange), (ex_11a, loadLocation.direct, .notAll),
    (ex_11b, loadLocation.oblique, .notAll), (ex_11d, loadLocation.oblique, .noChange),
    (ex_43a, eat.direct, .noChange), (ex_43b, eat.oblique, .noChange),
    (ex_43c, eat.direct, .whatHappened), (ex_43d, eat.oblique, .whatHappened),
    (ex_45a, cut.direct, .noChange), (ex_45b, cut.oblique, .noChange),
    (ex_45c, cut.direct, .whatHappened), (ex_45d, cut.oblique, .whatHappened),
    (ex_47a_hit, hit.direct, .noChange), (ex_47a_hitat, hit.oblique, .noChange),
    (ex_48a, hit.direct, .whatHappened), (ex_48b, hit.oblique, .whatHappened)]

/-- The paper's judgments of the conative and *load* variants under the diagnostics follow from the
degrees their results name, *hit at* failing *What happened to x* for its double modality. -/
theorem diagnosed_rows :
    ∀ p ∈ diagnosed, p.1.judgment.band = .ofProp (p.2.2.Accepts p.2.1.degree) := by
  decide

/-! ### Total traversal ((84)–(87)) -/

/-- A role of (87) is named by its strongest entailment ((66)), an affectedness entailment or total
traversal of a path ((86d)), which is incomparable with the affectedness entailments, and `⊥` is
the empty role. A role with both kinds would be an affected path, which (87) rules out. -/
abbrev Role := WithBot (AffectednessEntailment ⊕ Unit)

/-- `{totally traversed}`. -/
def Role.totallyTraversed : Role := ↑(Sum.inr () : AffectednessEntailment ⊕ Unit)

example : Fintype.card Role = 5 := by decide

/-- The role of (87) a result gives the scale it is stated on: totally traversed when the result is
the predicate's goal, which read of the scale is (85a), and otherwise empty, since traversal and
potential traversal are not among the entailments of (86). -/
def Result.traversal (r : Result) : Role :=
  if r.degree = .quantized then Role.totallyTraversed else ⊥

/-- *John climbed the stairs* against *John climbed up the stairs*: John ends at the end of the
stairs, or somewhere on them ((81), (84)). -/
def climb : Alternation :=
  ⟨ex_81a, ex_81b, .inherentlyDirectedMotion, some .locativePrepositionDrop, .goal, .someGoal⟩

-- Levin's class pages list every alternation that falls under one of her sections
theorem participates_of_mem_attested :
    ∀ a ∈ climb :: attested, ∀ x ∈ a.levinSection, a.verbClass.Participates x := by
  decide

-- (81), (84), (69), (87)
theorem climb_traversal_wcovBy : climb.oblique.traversal ⩿ climb.direct.traversal := by
  refine CovBy.wcovBy (?_ : ⊥ ⋖ Role.totallyTraversed)
  rw [Role.totallyTraversed, WithBot.bot_covBy_coe]
  rintro (e | u) h
  · exact absurd h Sum.not_inl_le_inr
  · exact le_rfl

/-! ### The dative chain (90) -/

/-- The roles of the dative chain (90), each named by its strongest entailment. -/
inductive DativeRole where
  /-- `{goal}`: being arrived at. -/
  | goal
  /-- `{recipient-goal, goal}`: being arrived into the possession of. -/
  | recipient
  deriving DecidableEq, Fintype, Repr

/-- Strength on the dative chain. -/
def DativeRole.strength : DativeRole → ℕ
  | .goal => 0
  | .recipient => 1

instance : LinearOrder DativeRole :=
  .lift' DativeRole.strength fun a b ↦ by cases a <;> cases b <;> simp [DativeRole.strength]

-- (88), (89), (90)
theorem goal_wcovBy_recipient : DativeRole.goal ⩿ .recipient := by decide

end Beavers2010
