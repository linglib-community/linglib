module

public import Mathlib.Data.Fintype.Powerset
public import Linglib.Semantics.Modality.EventRelativity
public import Linglib.Semantics.Mood.SpeechEvent
public import Linglib.Logic.Trivalent.Basic
public import Linglib.Data.Examples.AlonsoOvalleRoyer2024

/-!
# Alonso-Ovalle & Royer (2024): modal indefinites and semantic variation in Chuj

Chuj *yalnhej* DPs are existential quantifiers with an at-issue modal component (59): some
member of the domain satisfies restrictor and scope, and every member does so in some world of
the content of the DP's event anchor (`ModalExists`, on `Modality.contentPossibility`). The DP's
event variable is bound by the abstraction over the VP event (62), left free and read as the
assertion (69)/(71), or bound by an external modal's anchor (87)/(91). A VP event projects the
worlds where the decision that caused it is fulfilled, which gives random choice: an
indiscriminate decision, or one to take everything, satisfies the component and a decision for
one item does not (`randomChoice`, Fig. 1, (32)–(33)). The assertion projects the speaker's
doxastic alternatives, which gives an epistemic component compatible with any degree of
ignorance and with knowing that the whole domain qualifies, but not with knowing which proper
part does (`epistemic`, Figs. 2–3, (29)). A non-volitional verb's event has no decision
(`nonvolitional`, (34)), and an external argument merges above the VP abstraction, so the
flavors available at a site follow from the binders that reach it (`flavors_pattern`, §3.4,
fn. 17). Under an imperative the anchor can be the order's (`harmonic`, (82)–(85)).

Modal indefinites vary in the anchors they admit and in the bound on their witnesses (§6.2).
*Uno cualquiera* admits only anchors with normative conditions, decisions and orders, as
Alonso-Ovalle and Menéndez-Benito argue, so it has no epistemic reading but has the harmonic one
under an imperative (`cualquiera_selective`, (67)–(68), (86), (93)); *n'importe quel* (120) and
Italian *un N qualsiasi* (121) are as selective. *Yalnhej*'s claim has no upper bound, where
*algún*'s excludes the whole domain and *uno cualquiera*'s requires a unique witness
(`upperBound_universal`, (122)–(127)). The readings the rows list follow from the denotations
(`reading_rows`).

## Implementation notes

* A world records which of two items the agent took, and a scenario fixes the worlds each event
  projects. (59)'s condition that the possible event be similar to the actual one (fn. 14) is
  left out: a possible world in the content of the anchor verifies the scope of a member.
* A component has its anchor's flavor. A decision gives random choice, a circumstantial
  flavor; the assertion and the order give the primary flavors Hacquard assigns the
  declarative and imperative speech acts; a belief state gives an epistemic flavor.
* The bounds of *algún* and *uno cualquiera* (p. 31), the first a quantity implicature (p. 32),
  are part of the assertion here.
* The paper reports only unembedded readings of *n'importe quel* and *un N qualsiasi*, and
  §6.2 ascribes such selectivity to the anchors an item admits. The study gives both
  *uno cualquiera*'s anchors; *un N qualsiasi*, the "potential Italian counterpart of uno
  cualquiera" (p. 32), also its unique witness, which Chierchia derives by scalar competition
  with the numeral.
* The at-issue status of the components (`survives` rows, §§3.3, 6.1), the unremarkable
  readings and the predicative uses (§5) are row data: the study models neither embedding
  under negation nor predication.

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
* [von-fintel-2000-whatever]
* [chierchia-2013]
-/

@[expose] public section

namespace AlonsoOvalleRoyer2024

open Modality Finset Discourse.SpeechAct

/-! ### The schema (59) -/

section Schema

variable {E W X : Type*} (con : E → Option (Set W)) (D : Finset X) (P Q : X → W → Prop)

/-- The truth condition (59) holds when some member of `D` satisfies restrictor and scope and
every restrictor member satisfies the scope in some world of the content of the anchoring
event `e`. -/
def ModalExists (e : E) (w : W) : Prop :=
  (∃ x ∈ D, P x w ∧ Q x w) ∧ ∀ y ∈ D, P y w → contentPossibility con (Q y) e

/-- A unique member of `D` satisfies restrictor and scope, the bound of *uno cualquiera*
(p. 31). -/
def UniqueWitness (w : W) : Prop :=
  ∃ x ∈ D, P x w ∧ Q x w ∧ ∀ y ∈ D, P y w → Q y w → y = x

/-- Not every restrictor member satisfies the scope, the weaker bound of *algún* (p. 31). -/
def NotAll (w : W) : Prop := ¬ ∀ x ∈ D, P x w → Q x w

variable (w : W) [∀ x, Decidable (P x w)] [∀ x, Decidable (Q x w)]

instance [DecidableEq X] : Decidable (UniqueWitness D P Q w) := by
  unfold UniqueWitness; infer_instance

instance : Decidable (NotAll D P Q w) := by unfold NotAll; infer_instance

end Schema

/-! ### Events and what they project -/

/-- There are two items, and a world records which of them the agent took (bought, liked,
grabbed). -/
abbrev Item := Fin 2

abbrev World := Finset Item

/-- Item `y` is among what was taken. -/
def Taken (y : Item) (w : World) : Prop := y ∈ w

instance (y : Item) : DecidablePred (Taken y) := fun w ↦ inferInstanceAs (Decidable (y ∈ w))

/-- A scenario has four events, the VP event, the assertion, an order and a belief. -/
inductive Ev | vp | assertion | order | belief
  deriving DecidableEq

/-- A scenario fixes the worlds each event projects, namely those where the decision that
caused the VP event is fulfilled, if the verb is volitional, the speaker's doxastic
alternatives, the addressee's to-do list and the attitude holder's belief state. -/
structure Scenario where
  decision : Option (Finset World)
  dox : Finset World := ∅
  todo : Finset World := ∅
  belief : Finset World := ∅

/-- `scenario` builds a scenario from the decision and the doxastic alternatives, with an
optional order and belief state. -/
def scenario (decision : Option (Finset World)) (dox : Finset World := ∅)
    (todo : Finset World := ∅) (belief : Finset World := ∅) : Scenario :=
  ⟨decision, dox, todo, belief⟩

/-- `s.worlds e` is the set of worlds the event `e` projects in `s`, if any. -/
def Scenario.worlds (s : Scenario) : Ev → Option (Finset World)
  | .vp => s.decision
  | .assertion => some s.dox
  | .order => some s.todo
  | .belief => some s.belief

/-- The content of an event is (59)'s domain-fixing function. -/
def Scenario.content (s : Scenario) (e : Ev) : Option (Set World) := (s.worlds e).map (↑)

theorem contentPossibility_content (s : Scenario) (q : World → Prop) (e : Ev) :
    contentPossibility s.content q e ↔ ∃ d ∈ s.worlds e, ∃ w ∈ d, q w := by
  simp [contentPossibility, Scenario.content]

instance (s : Scenario) (q : World → Prop) [DecidablePred q] (e : Ev) :
    Decidable (contentPossibility s.content q e) :=
  decidable_of_iff _ (contentPossibility_content s q e).symm

/-- An event projects a component of its own flavor. The decision behind a VP event gives
random choice, a circumstantial flavor, the assertion and the order the primary flavors of the
declarative and imperative speech acts, and a belief state an epistemic flavor. -/
def Ev.flavor : Ev → ModalFlavor
  | .vp => .circumstantial
  | .assertion => Force.assertion.primaryFlavor.get rfl
  | .order => Force.directive.primaryFlavor.get rfl
  | .belief => .epistemic

/-- `Claim s e` is the claim of a *yalnhej* DP over the whole domain, anchored to `e`. -/
def Claim (s : Scenario) (e : Ev) (w : World) : Prop :=
  ModalExists s.content univ (fun _ _ ↦ True) Taken e w

instance (s : Scenario) (e : Ev) (w : World) : Decidable (Claim s e w) := by
  unfold Claim ModalExists; infer_instance

/-- `nonempty` is the set of worlds in which something was taken. -/
abbrev nonempty : Finset World := univ.filter Finset.Nonempty

/-- The decisions *buy a book* and *buy all books* satisfy the modal component and *buy b₁* does not
(Fig. 1, (32)–(33)). -/
theorem randomChoice :
    Claim (scenario (some nonempty)) .vp {0} ∧ Claim (scenario (some {{0, 1}})) .vp {0, 1} ∧
      ¬ Claim (scenario (some {{0}})) .vp {0} := by
  decide

/-- The assertion-anchored component holds under total or partial ignorance and when the whole
domain qualifies, but not when the speaker knows which part does (Figs. 2–3, (29)). -/
theorem epistemic :
    Claim (scenario none nonempty) .assertion {0} ∧
      Claim (scenario none {{0}, {0, 1}}) .assertion {0} ∧
      Claim (scenario none {{0, 1}}) .assertion {0, 1} ∧
      ¬ Claim (scenario none {{0}}) .assertion {0} := by
  decide

/-- A non-volitional VP event contains no decision, so nothing projects from it and the random
choice reading of (34) is unavailable whatever the world. -/
theorem nonvolitional (dox todo belief : Finset World) (w : World) :
    ¬ Claim (scenario none dox todo belief) .vp w := by
  simp [Claim, ModalExists, contentPossibility, Scenario.content, Scenario.worlds, scenario]

/-- Under the imperative of (82)–(85), projection from the addressee's deliberate decision
fails, while projection from the order, which permits any card, succeeds. -/
theorem harmonic :
    ¬ Claim (scenario (some {{0}}) ∅ {{0}, {1}}) .vp {0} ∧
      Claim (scenario (some {{0}}) ∅ {{0}, {1}}) .order {0} := by
  decide

/-! ### Position and flavor (§3.4) -/

/-- A site is the base position of the DP relative to the abstraction over the VP event. An
external argument merges above it (74), internal arguments and adjuncts below (62). -/
inductive Site | external | internal | adjunct
  deriving DecidableEq

def Site.belowVPAbstraction : Site → Bool
  | .external => false
  | .internal | .adjunct => true

/-- At a site, the DP's event variable can be bound to the VP event where its abstraction
c-commands the DP, to an external modal's anchor when embedded under one, and to the assertion
when left free (fn. 17). -/
def binders (site : Site) (embedded : Option Ev) : List Ev :=
  (if site.belowVPAbstraction then [.vp] else []) ++ embedded.toList ++ [.assertion]

/-- A DP at a site can express the flavors of those of its binders that project worlds in the
scenario. -/
def flavors (s : Scenario) (site : Site) (embedded : Option Ev) : List ModalFlavor :=
  (binders site embedded).filterMap fun e ↦ (s.worlds e).map fun _ ↦ e.flavor

/-- An external argument has only the epistemic reading, and an internal argument or adjunct also
random choice with a volitional verb (§3.4). -/
theorem flavors_pattern (d dox : Finset World) :
    flavors (scenario (some d) dox) .external none = [.epistemic] ∧
      flavors (scenario none dox) .external none = [.epistemic] ∧
      flavors (scenario (some d) dox) .internal none = [.circumstantial, .epistemic] ∧
      flavors (scenario none dox) .internal none = [.epistemic] ∧
      flavors (scenario (some d) dox) .adjunct none = [.circumstantial, .epistemic] ∧
      flavors (scenario none dox) .adjunct none = [.epistemic] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Items (§§4, 6.2) -/

/-- A modal indefinite of the schema (59) varies, as §6.2 describes, in the anchors it admits,
a definedness condition, and in the bound on its witnesses. -/
structure ModalIndefinite where
  /-- `Admits s e` holds when the item admits the anchor `e` in `s`. -/
  Admits : Scenario → Ev → Prop
  [decAdmits : ∀ s e, Decidable (Admits s e)]
  /-- `Bound w` bounds the witnesses in `w`. -/
  Bound : World → Prop
  [decBound : DecidablePred Bound]

attribute [instance] ModalIndefinite.decAdmits ModalIndefinite.decBound

/-- The item's denotation anchored to `e` is defined when the item admits the anchor and true
when the claim holds within the bound. -/
def ModalIndefinite.denotation (i : ModalIndefinite) (s : Scenario) (e : Ev) :
    World → SignType :=
  fun w ↦ if i.Admits s e then SignType.ofProp (Claim s e w ∧ i.Bound w) else 0

/-- The decision behind a volitional event and an order have normative conditions; a speech
event and a belief state do not, having informational content (p. 35, after
[alonso-ovalle-menendez-benito-2018] pp. 29, 31). -/
def Scenario.Normative (s : Scenario) : Ev → Prop
  | .vp => s.decision.isSome
  | .order => True
  | .assertion | .belief => False

instance (s : Scenario) : DecidablePred s.Normative
  | .vp => inferInstanceAs (Decidable (s.decision.isSome = true))
  | .order => instDecidableTrue
  | .assertion | .belief => instDecidableFalse

/-- *Yalnhej* admits any anchor and has no bound (§4.2). -/
def yalnhej : ModalIndefinite := ⟨fun _ _ ↦ True, fun _ ↦ True⟩

/-- *Uno cualquiera* admits normative anchors and requires a unique witness (p. 31). -/
def cualquiera : ModalIndefinite :=
  ⟨Scenario.Normative, UniqueWitness univ (fun _ _ ↦ True) Taken⟩

/-- *N'importe quel* admits normative anchors (120). -/
def nimporteQuel : ModalIndefinite := ⟨Scenario.Normative, fun _ ↦ True⟩

/-- *Uno cualquiera* has no epistemic reading, being undefined anchored to the assertion or a
belief, but is defined anchored to the order of (86) ((67)–(68), (93)). -/
theorem cualquiera_selective (s : Scenario) (w : World) :
    cualquiera.denotation s .assertion w = 0 ∧ cualquiera.denotation s .belief w = 0 ∧
      cualquiera.denotation (scenario (some {{0}}) ∅ {{0}, {1}}) .order {0} = 1 := by
  refine ⟨?_, ?_, by decide⟩ <;>
    simp [ModalIndefinite.denotation, cualquiera, Scenario.Normative]

-- (120)
theorem nimporteQuel_selective (s : Scenario) (w : World) :
    nimporteQuel.denotation (scenario (some nonempty)) .vp {0} = 1 ∧
      nimporteQuel.denotation s .assertion w = 0 :=
  ⟨by decide, by simp [ModalIndefinite.denotation, nimporteQuel, Scenario.Normative]⟩

/-- Where everything was taken ((124)–(125), (126)–(127)), *yalnhej*'s claim holds while *algún*'s
bound (122) and *uno cualquiera*'s unique witness (123) fail. -/
theorem upperBound_universal :
    yalnhej.denotation (scenario none {{0, 1}}) .assertion {0, 1} = 1 ∧
      yalnhej.denotation (scenario (some {{0, 1}})) .vp {0, 1} = 1 ∧
      ¬ NotAll univ (fun _ _ ↦ True) Taken {0, 1} ∧
      cualquiera.denotation (scenario (some {{0, 1}})) .vp {0, 1} = -1 := by
  decide

/-! ### The paper's judgments -/

/-- `readingFlavor` gives the flavor of the reading a row names. -/
def readingFlavor : String → Option ModalFlavor
  | "epistemic" => some .epistemic
  | "random choice" => some .circumstantial
  | _ => none

/-- `doxOf` gives the doxastic alternatives a row's `epistemicState` names, with `{0}` the
actual world. -/
def doxOf : String → Option (Finset World)
  | "ignorant" => some nonempty
  | "knows which, not all" => some {{0}}
  | "knows all" => some {{0, 1}}
  | _ => none

/-- `decisionOf` gives the decision a row's `decision` feature names. -/
def decisionOf : String → Option (Finset World)
  | "indiscriminate" => some nonempty
  | "specific" => some {{0}}
  | "all" => some {{0, 1}}
  | _ => none

/-- A position row is predicted acceptable iff some binder available at its site projects
the reading's flavor and, when the row gives a scenario, the claim anchored there holds. -/
def positionPredicted (row : Datum) : Option Bool := do
  let site ← match row.feature? "position" with
    | some "external" => some Site.external
    | some "internal" => some .internal
    | some "adjunct" => some .adjunct
    | _ => none
  let fl ← row.feature? "reading" >>= readingFlavor
  let decision := if row.feature? "volitional" == some "yes" then
    some ((row.feature? "decision" >>= decisionOf).getD nonempty) else none
  let dox := (row.feature? "epistemicState" >>= doxOf).getD nonempty
  let s : Scenario := scenario decision dox
  let w : World := if row.feature? "epistemicState" == some "knows all" ||
    row.feature? "decision" == some "all" then {0, 1} else {0}
  return (binders site none).any fun e ↦ e.flavor == fl && decide (Claim s e w)

theorem position_rows :
    ∀ row ∈ Examples.all, ∀ b ∈ positionPredicted row,
      (row.judgment == .acceptable) = b := by decide +kernel

/-- `itemOf` gives the item a row's `item` feature names, among those the study gives a
denotation. *Un N qualsiasi* is *uno cualquiera*'s Italian counterpart (p. 32); *algún* and
*irgendein*, whose modal components are implicatures (§6.1), and the modifier *komon* have
none here. -/
def itemOf : String → Option ModalIndefinite
  | "yalnhej" => some yalnhej
  | "uno cualquiera" | "un qualsiasi" => some cualquiera
  | "n'importe quel" => some nimporteQuel
  | _ => none

/-- A reading of flavor `fl` is available unembedded when a binder of an object (62), (69) of
that flavor makes the item defined and true given an indiscriminate decision and an ignorant
speaker. -/
def ModalIndefinite.Available (i : ModalIndefinite) (fl : ModalFlavor) : Prop :=
  ∃ e ∈ binders .internal none, e.flavor = fl ∧
    i.denotation (scenario (some nonempty) nonempty) e {0} = 1

instance (i : ModalIndefinite) (fl : ModalFlavor) : Decidable (i.Available fl) := by
  unfold ModalIndefinite.Available; infer_instance

/-- A row is bare when it embeds the item nowhere and fixes no position, anchor, scenario or
continuation. -/
def IsBare (row : Datum) : Prop :=
  ∀ f ∈ ["position", "survives", "embedded", "anchor", "scenario", "continuation",
    "construction", "property"], row.feature? f = none

instance (row : Datum) : Decidable (IsBare row) := by unfold IsBare; infer_instance

/-- In every bare row of an analysed item, each named or listed reading is acceptable iff the item
makes it available ((54), (93), (119)–(121), fn. 20 (i)). -/
theorem reading_rows :
    ∀ row ∈ Examples.all, IsBare row → ∀ i ∈ (row.feature? "item").bind itemOf,
      (∀ fl ∈ (row.feature? "reading").bind readingFlavor,
        (row.judgment == .acceptable) = decide (i.Available fl)) ∧
      ∀ r ∈ row.readings, ∀ fl ∈ readingFlavor r.1,
        (r.2 == .acceptable) = decide (i.Available fl) := by
  decide +kernel

example : (∃ row ∈ Examples.all, (positionPredicted row).isSome) ∧
    ∃ row ∈ Examples.all, IsBare row ∧ ((row.feature? "item").bind itemOf).isSome := by
  decide +kernel

end AlonsoOvalleRoyer2024
