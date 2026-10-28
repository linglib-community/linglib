module

public import Mathlib.Data.Fintype.Powerset
public import Linglib.Semantics.Exhaustification.DomainAlternatives
public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Modality.EventRelativity
public import Linglib.Discourse.SpeechAct
public import Linglib.Logic.Trivalent.Basic
public import Linglib.Data.Examples.AlonsoOvalleRoyer2024

/-!
# Alonso-Ovalle & Royer (2024): modal indefinites and semantic variation in Chuj

A Chuj *yalnhej* DP is an existential quantifier with an at-issue free choice component (59):
some member of the noun's extension satisfies the scope, and every member satisfies it in some
world projected from the DP's anchor, an event variable. Bound to the VP event, the anchor
projects the worlds where the decision behind the event is fulfilled, which gives
[random choice](##randomChoice); left free, it is the assertion, which projects the speaker's
doxastic alternatives and gives an [epistemic component compatible with any degree of
ignorance](##epistemic). Modal indefinites vary in the anchors they admit: *uno cualquiera* admits
only those with normative conditions, [decisions and orders](##cualquiera_selective). Since the
extension of a number-neutral noun is closed under sums, the component says that [the whole
domain might satisfy the scope](##freeChoice_sums_iff), which [mispredicts two of the paper's
judgments](##sums_mispredict).

## Implementation notes

* An individual is a nonempty set of items, an item or a sum of items, and a world records the
  items the agent took; a sum was taken when each of its members was. A singular noun denotes
  the `atoms`, a number-neutral one the `sums`, Link's closure of the atoms (`mem_sums_iff`).
* The anchors are `Modality.EventBinder`'s. The speech event is the assertion of a declarative
  and the order of an imperative; an order projects the worlds where the decision leading to it
  is fulfilled.
* (59)'s condition that the possible event be similar to the actual one (fn. 14) is left out,
  and the restrictor does not vary with the world.
* A row's reading names its anchor, the VP event for random choice and the speech event for an
  epistemic reading. The position rows are checked with the component restricted to atoms,
  which predicts all of them (`position_rows`).
* The bounds of *algún* and *uno cualquiera*, the first a quantity implicature, are part of the
  assertion here.
* The study models the at-issue status of the component under negation
  (`negation_targets_component`), but not in conditional antecedents; the unremarkable readings
  and the predicative uses (§5) are row data.

## Errata

* With the noun's extension closed under sums (fn. 14), the modal component of (59) holds only if
  the anchor projects a world where the whole domain satisfies the scope, as the gloss "maybe all
  did" of (22) has it. It then predicts (22) false in (23a), where the speaker knows that not
  everyone danced, and (37) false in (38a), where the jury decides to choose one participant; the
  paper judges both acceptable. Restricted to atoms, the component predicts both.
* (75) and (92) write `agent(y)(e)`, the actual event, for `agent(y)(e′)`.
* The discussion of (39) cites (40c) for the scenario in which it rained everywhere, which is
  (40b).

## TODO

* Under an overt possibility modal *un N qualsiasi* has an epistemic reading (Chierchia's
  (31a)), which *uno cualquiera*'s anchors exclude ((93)); the scenario has no overt epistemic
  modal to state the contrast.
* No source gives *n'importe quel* an upper bound or denies it one.
* Fn. 18 ties the missing upper bound to *yalnhej*'s number neutrality.

## References

* [alonso-ovalle-royer-2024]
* [alonso-ovalle-royer-2022]
* [alonso-ovalle-royer-2021]
* [alonso-ovalle-menendez-benito-2018]
* [alonso-ovalle-menendez-benito-2010]
* [hacquard-2006]
* [kratzer-shimoyama-2002]
* [link-1983]
* [von-fintel-2000-whatever]
* [chierchia-2013]
-/

@[expose] public section

namespace AlonsoOvalleRoyer2024

open Finset ModalLogic Exhaustification Discourse.SpeechAct
open Modality (EventBinder)

/-! ### The schema (59) -/

section Schema

variable {E W X : Type*} (R : SetRel E W) (D : Finset X) (Q : W → X → Prop)

/-- The truth condition (59) holds when some member of `D` satisfies the scope at `w` and every
member satisfies it in some world the anchor `e` projects along `R`. -/
def ModalExists (e : E) (w : W) : Prop := claim Q D w ∧ FreeChoice R e D Q

/-- A unique member of `D` satisfies the scope, the bound of *uno cualquiera* (p. 31). -/
def UniqueWitness (w : W) : Prop := ∃ x ∈ D, Q w x ∧ ∀ y ∈ D, Q w y → y = x

/-- Not every member of `D` satisfies the scope, the weaker bound of *algún* (p. 31). -/
def NotAll (w : W) : Prop := ¬ ∀ x ∈ D, Q w x

variable (w : W) [DecidablePred (Q w)]

instance [DecidableEq X] : Decidable (UniqueWitness D Q w) := by
  unfold UniqueWitness; infer_instance

instance : Decidable (NotAll D Q w) := by unfold NotAll; infer_instance

end Schema

/-! ### Individuals, worlds and anchors -/

/-- There are two items. -/
abbrev Item := Fin 2

/-- A world records which items the agent took (bought, liked, grabbed). -/
abbrev World := Finset Item

/-- An individual, a nonempty set of items, was taken in a world when each of its members was. -/
def Took (w : World) (y : Finset Item) : Prop := y ⊆ w

instance (w : World) : DecidablePred (Took w) := fun y ↦ inferInstanceAs (Decidable (y ⊆ w))

/-- The atoms, the extension of a singular noun. -/
abbrev atoms : Finset (Finset Item) := univ.map ⟨({·}), singleton_injective⟩

/-- The sums, the extension of a number-neutral noun. -/
abbrev sums : Finset (Finset Item) := univ.filter Finset.Nonempty

-- fn. 14
theorem mem_sums_iff {y : Finset Item} : y ∈ sums ↔ Mereology.AlgClosure (· ∈ atoms) y := by
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · refine Nonempty.cons_induction (fun a ↦ .base (by simp)) fun a s h _ ih ↦ ?_
    rw [cons_eq_insert, insert_eq, ← sup_eq_union]
    exact .sum (.base (by simp)) ih
  · intro hy
    induction hy with
    | base h => obtain ⟨a, -, rfl⟩ := mem_map.1 h; exact singleton_nonempty a
    | sum _ _ ih _ => exact ih.mono le_sup_left

/-- `nonempty` is the set of worlds in which something was taken. -/
abbrev nonempty : Finset World := univ.filter Finset.Nonempty

/-- A scenario fixes the worlds each anchor projects: the worlds where the decision behind the VP
event is fulfilled, if the verb is volitional; the content of the speech event, the speaker's
doxastic alternatives for an assertion and the worlds where the decision leading to an order is
fulfilled for an order; and the belief state of an attitude embedding the DP, if any. -/
structure Scenario where
  decision : Option (Finset World)
  speech : Finset World
  force : Force
  attitude : Option (Finset World)

/-- `scenario` builds a scenario from the decision and the content of the speech event, an
assertion unless stated otherwise, with no attitude unless one is given. -/
def scenario (decision : Option (Finset World)) (speech : Finset World := ∅)
    (force : Force := .assertion) (attitude : Option (Finset World) := none) : Scenario :=
  ⟨decision, speech, force, attitude⟩

/-- `s.worlds e` is the set of worlds the anchor `e` projects in `s`, empty where it projects none:
the VP event of a non-volitional verb contains no decision (Fig. 2). -/
def Scenario.worlds (s : Scenario) : EventBinder → Finset World
  | .vpEvent => s.decision.getD ∅
  | .speechAct => s.speech
  | .attitude => s.attitude.getD ∅

/-- The domain-fixing function `f` of (59), as the relation from each anchor to the worlds it
projects. -/
def Scenario.projection (s : Scenario) : SetRel EventBinder World :=
  .ofSuccessors fun e ↦ ↑(s.worlds e)

/-- `Claim D s e w` is the claim of a *yalnhej* DP whose noun has extension `D`, anchored to
`e`. -/
def Claim (D : Finset (Finset Item)) (s : Scenario) (e : EventBinder) (w : World) : Prop :=
  ModalExists s.projection D Took e w

section Claim

variable {D : Finset (Finset Item)} {s : Scenario} {e : EventBinder} {w : World}

theorem claim_iff : Claim D s e w ↔ (∃ y ∈ D, y ⊆ w) ∧ ∀ y ∈ D, ∃ v ∈ s.worlds e, y ⊆ v := by
  simp [Claim, ModalExists, claim, FreeChoice, Diamond, Scenario.projection, Took]

instance : Decidable (Claim D s e w) := decidable_of_iff _ claim_iff.symm

/-- Over the sums, the free choice component holds exactly when the anchor projects the world in
which everything was taken. -/
theorem freeChoice_sums_iff : FreeChoice s.projection e sums Took ↔ univ ∈ s.worlds e := by
  rw [freeChoice_iff_of_isGreatest s.projection e sums Took ⟨by simp, fun y _ ↦ subset_univ y⟩
    fun _ _ _ hba ha ↦ Subset.trans hba ha]
  simp [Diamond, Scenario.projection, Took]

/-- The decisions *buy a book* and *buy all books* satisfy the modal component and *buy b₁* does
not (Fig. 1, (32)–(33)). -/
theorem randomChoice :
    Claim sums (scenario (some nonempty)) .vpEvent {0} ∧
      Claim sums (scenario (some {univ})) .vpEvent univ ∧
      ¬ Claim sums (scenario (some {{0}})) .vpEvent {0} := by
  decide

/-- Anchored to the assertion, the component holds under total or partial ignorance and when the
whole domain qualifies, but not when the speaker knows which part does (Figs. 2–3, (29)). -/
theorem epistemic :
    Claim sums (scenario none nonempty) .speechAct {0} ∧
      Claim sums (scenario none {{0}, univ}) .speechAct {0} ∧
      Claim sums (scenario none {univ}) .speechAct univ ∧
      ¬ Claim sums (scenario none {{0}}) .speechAct {0} := by
  decide

-- (34), Fig. 2
theorem nonvolitional (speech : Finset World) (force : Force) (att : Option (Finset World)) :
    ¬ Claim D (scenario none speech force att) .vpEvent w := by
  rintro ⟨⟨y, hy, -⟩, h⟩
  simpa [Diamond, Scenario.projection, Scenario.worlds, scenario] using h y hy

-- (82)–(85)
theorem harmonic :
    ¬ Claim sums (scenario (some {{0}}) nonempty .directive) .vpEvent {0} ∧
      Claim sums (scenario (some {{0}}) nonempty .directive) .speechAct {0} := by
  decide

end Claim

/-! ### Position and anchors (§3.4) -/

/-- A site is the base position of the DP relative to the abstraction over the VP event. An
external argument merges above it (74), internal arguments and adjuncts below (62). -/
inductive Site | external | internal | adjunct
  deriving DecidableEq

/-- At a site, the DP's anchor can be bound to the VP event where the abstraction over it
c-commands the DP, to the anchor of an attitude embedding the DP (91), and to the speech event:
the assertion when left free (71), fn. 17, and the order when coindexed with the imperative's
anchor (87). -/
def binders (site : Site) (s : Scenario) : List EventBinder :=
  (if site = .external then [] else [.vpEvent]) ++
    (s.attitude.map fun _ ↦ EventBinder.attitude).toList ++ [.speechAct]

/-! ### Items (§§4, 6.2) -/

/-- A modal indefinite of the schema (59) varies, as §6.2 describes, in the anchors it admits,
a definedness condition, and in the bound on its witnesses; its noun's extension is the atoms or
their sums. -/
structure ModalIndefinite where
  /-- The extension of the item's noun. -/
  domain : Finset (Finset Item)
  /-- `Admits s e` holds when the item admits the anchor `e` in `s`. -/
  Admits : Scenario → EventBinder → Prop
  [decAdmits : ∀ s e, Decidable (Admits s e)]
  /-- `Bound w` bounds the witnesses in `w`. -/
  Bound : World → Prop
  [decBound : DecidablePred Bound]

attribute [instance] ModalIndefinite.decAdmits ModalIndefinite.decBound

/-- The item's denotation anchored to `e` is defined when the item admits the anchor and true
when the claim holds within the bound. -/
def ModalIndefinite.denotation (i : ModalIndefinite) (s : Scenario) (e : EventBinder) :
    World → SignType :=
  fun w ↦ if i.Admits s e then SignType.ofProp (Claim i.domain s e w ∧ i.Bound w) else 0

/-- The decision behind a volitional event and an order have normative conditions; an assertion
and a belief state do not, having informational content (p. 35, after
[alonso-ovalle-menendez-benito-2018] pp. 29, 31). -/
def Scenario.Normative (s : Scenario) : EventBinder → Prop
  | .vpEvent => s.decision.isSome
  | .speechAct => s.force = .directive
  | .attitude => False

instance (s : Scenario) : DecidablePred s.Normative
  | .vpEvent => inferInstanceAs (Decidable (s.decision.isSome = true))
  | .speechAct => inferInstanceAs (Decidable (s.force = .directive))
  | .attitude => instDecidableFalse

/-- *Yalnhej* is number neutral, admits any anchor and has no bound (§4.2). -/
def yalnhej : ModalIndefinite := ⟨sums, fun _ _ ↦ True, fun _ ↦ True⟩

/-- *Uno cualquiera* is singular, admits normative anchors and requires a unique witness
(p. 31). -/
def cualquiera : ModalIndefinite := ⟨atoms, Scenario.Normative, UniqueWitness atoms Took⟩

/-- *N'importe quel* is singular and admits normative anchors (120). -/
def nimporteQuel : ModalIndefinite := ⟨atoms, Scenario.Normative, fun _ ↦ True⟩

-- (49)–(50): the negated claim is true where its existential component holds
theorem negation_targets_component :
    -yalnhej.denotation (scenario (some {{0}})) .vpEvent {0} = 1 ∧ claim Took sums {0} := by
  decide

/-- *Uno cualquiera* has no epistemic reading, being undefined anchored to an assertion or a
belief state, but is defined anchored to the order of (86) ((67)–(68), (93)). -/
theorem cualquiera_selective (decision : Option (Finset World)) (speech : Finset World)
    (att : Option (Finset World)) (s : Scenario) (w : World) :
    cualquiera.denotation (scenario decision speech .assertion att) .speechAct w = 0 ∧
      cualquiera.denotation s .attitude w = 0 ∧
      cualquiera.denotation (scenario (some {{0}}) nonempty .directive) .speechAct {0} = 1 := by
  refine ⟨?_, ?_, by decide⟩ <;>
    simp [ModalIndefinite.denotation, cualquiera, Scenario.Normative, scenario]

-- (120)
theorem nimporteQuel_selective (decision : Option (Finset World)) (speech : Finset World)
    (att : Option (Finset World)) (w : World) :
    nimporteQuel.denotation (scenario (some nonempty)) .vpEvent {0} = 1 ∧
      nimporteQuel.denotation (scenario decision speech .assertion att) .speechAct w = 0 :=
  ⟨by decide, by simp [ModalIndefinite.denotation, nimporteQuel, Scenario.Normative, scenario]⟩

-- (122)–(127)
theorem upperBound_universal :
    yalnhej.denotation (scenario none {univ}) .speechAct univ = 1 ∧
      yalnhej.denotation (scenario (some {univ})) .vpEvent univ = 1 ∧
      ¬ NotAll atoms Took univ ∧
      cualquiera.denotation (scenario (some {univ})) .vpEvent univ = -1 := by
  decide

/-! ### The paper's judgments -/

/-- `readingAnchor` gives the anchor of the reading a row names, the VP event for random choice
(§4.1) and the speech event for an epistemic reading (§4.2). -/
def readingAnchor : String → Option EventBinder
  | "random choice" => some .vpEvent
  | "epistemic" => some .speechAct
  | _ => none

/-- `doxOf` gives the doxastic alternatives a row's `epistemicState` names, with `{0}` the
actual world unless everything was taken. -/
def doxOf : String → Option (Finset World)
  | "ignorant" => some nonempty
  | "ignorant, not all" => some {{0}, {1}}
  | "knows which, not all" => some {{0}}
  | "knows all" => some {univ}
  | _ => none

/-- `decisionOf` gives the decision a row's `decision` feature names. -/
def decisionOf : String → Option (Finset World)
  | "indiscriminate" => some nonempty
  | "one, any" => some {{0}, {1}}
  | "specific" => some {{0}}
  | "all" => some {univ}
  | _ => none

/-- A position row is predicted acceptable iff the anchor of its reading is available at its
site and the claim anchored there holds in the row's scenario, the noun denoting `D`. -/
def positionPredicted (D : Finset (Finset Item)) (row : Datum) : Option Bool := do
  let site ← match row.feature? "position" with
    | some "external" => some Site.external
    | some "internal" => some .internal
    | some "adjunct" => some .adjunct
    | _ => none
  let e ← row.feature? "reading" >>= readingAnchor
  let decision := if row.feature? "volitional" == some "yes" then
    some ((row.feature? "decision" >>= decisionOf).getD nonempty) else none
  let s := scenario decision ((row.feature? "epistemicState" >>= doxOf).getD nonempty)
  let w : World := if row.feature? "epistemicState" == some "knows all" ||
    row.feature? "decision" == some "all" then univ else {0}
  return decide (e ∈ binders site s ∧ Claim D s e w)

-- §3.2
theorem position_rows :
    ∀ row ∈ Examples.all, ∀ b ∈ positionPredicted atoms row,
      (row.judgment == .acceptable) = b := by
  decide +kernel

/-- Over the sums, the claim mispredicts exactly two position rows: (22) in (23a), where the
speaker knows that not everyone danced, and (37) in (38a), where the jury decides to choose one
participant. -/
theorem sums_mispredict :
    Examples.all.filter (fun row ↦ (positionPredicted sums row).any
      (· != (row.judgment == .acceptable))) = [Examples.ex_22_23a, Examples.ex_37_38a] := by
  decide +kernel

/-- `itemOf` gives the item a row's `item` feature names, among those the study gives a
denotation. *Un N qualsiasi* is *uno cualquiera*'s Italian counterpart (p. 32); *algún* and
*irgendein*, whose modal components are implicatures (§6.1), and the modifier *komon* have
none here. -/
def itemOf : String → Option ModalIndefinite
  | "yalnhej" => some yalnhej
  | "uno cualquiera" | "un qualsiasi" => some cualquiera
  | "n'importe quel" => some nimporteQuel
  | _ => none

/-- A reading anchored to `e` is available unembedded when it makes the item defined and true
on an object (62), (71), given an indiscriminate decision and an ignorant speaker. -/
def ModalIndefinite.Available (i : ModalIndefinite) (e : EventBinder) : Prop :=
  i.denotation (scenario (some nonempty) nonempty) e {0} = 1

instance (i : ModalIndefinite) (e : EventBinder) : Decidable (i.Available e) := by
  unfold ModalIndefinite.Available; infer_instance

/-- A row is bare when it embeds the item nowhere and fixes no position, anchor, scenario or
continuation. -/
def IsBare (row : Datum) : Prop :=
  ∀ f ∈ ["position", "survives", "embedded", "anchor", "scenario", "continuation",
    "construction", "property"], row.feature? f = none

instance (row : Datum) : Decidable (IsBare row) := by unfold IsBare; infer_instance

-- (54), (93), (119)–(121), fn. 20 (i)
theorem reading_rows :
    ∀ row ∈ Examples.all, IsBare row → ∀ i ∈ (row.feature? "item").bind itemOf,
      (∀ e ∈ (row.feature? "reading").bind readingAnchor,
        (row.judgment == .acceptable) = decide (i.Available e)) ∧
      ∀ r ∈ row.readings, ∀ e ∈ readingAnchor r.1,
        (r.2 == .acceptable) = decide (i.Available e) := by
  decide +kernel

example : (∃ row ∈ Examples.all, (positionPredicted atoms row).isSome) ∧
    ∃ row ∈ Examples.all, IsBare row ∧ ((row.feature? "item").bind itemOf).isSome := by
  decide +kernel

end AlonsoOvalleRoyer2024
