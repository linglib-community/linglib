module

public import Mathlib.Data.Fintype.Powerset
public import Linglib.Semantics.Exhaustification.DomainAlternatives
public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Modality.EventRelativity
public import Linglib.Discourse.SpeechAct
public import Linglib.Logic.Trivalent.Basic
public import Linglib.Fragments.Mayan.Chuj.Verbs
public import Linglib.Fragments.Mayan.Chuj.Voice
public import Linglib.Fragments.Mayan.Chuj.Extraction
public import Linglib.Semantics.ArgumentStructure.Unaccusativity
public import Linglib.Data.Examples.Gloss
public import Linglib.Data.Examples.AlonsoOvalleRoyer2024
public import Linglib.Morphology.Word.Leipzig

/-!
# Alonso-Ovalle & Royer (2024): modal indefinites and semantic variation in Chuj

A Chuj *yalnhej* DP is an existential quantifier with an at-issue free choice component (59):
some member of the noun's extension satisfies the scope, and every member satisfies it in some
world projected from the DP's anchor, an event variable. Bound to the VP event, the anchor
projects the worlds where the decision behind the event is fulfilled, which gives random choice;
left free, it is the assertion, which projects the speaker's doxastic alternatives and gives an
epistemic component. Either way, an anchor whose worlds all lack some item [rules the component
out](##not_claim_of_forall_not_mem). Modal indefinites vary in the anchors they admit: *uno
cualquiera* admits only those with normative conditions, [decisions and
orders](##cualquiera_selective). Since the extension of a number-neutral noun is closed under
sums, the component says that [the whole domain might satisfy the scope](##claim_sums_iff); with
the noun restricted to atoms the model [predicts every judgment in the contexts it
models](##context_rows), and with the sums it [mispredicts four](##sums_mispredict).

## Implementation notes

* An individual is a nonempty set of items, an item or a sum of items, and a world records the
  items the agent took; a sum was taken when each of its members was. A singular noun denotes
  the `atoms`, a number-neutral one the `sums`, Link's closure of the atoms (`mem_sums_iff`).
* The anchors are `Modality.EventBinder`'s. The speech event is the assertion of a declarative
  and the order of an imperative; an order projects the worlds where the decision leading to it
  is fulfilled. Under an imperative the claim is evaluated at one permitted world.
* (59)'s condition that the possible event be similar to the actual one (fn. 14) is left out,
  and the restrictor does not vary with the world.
* A row's judgments are of the readings it names. Its item, its negation, the site of its DP and
  whether its verb is volitional are read off its glossed words: the site from the Agent Focus
  marking of `Chuj.Extraction.realize`, the passive of `Chuj.passive` and the verbs of
  `Fragments/Mayan/Chuj/Verbs.lean`, whose subjects' entailments also give volitionality. Each
  context the study models is a typed definition quoting the paper.
* The bounds of *algún* and *uno cualquiera*, the first a quantity implicature, are part of the
  assertion here.
* The study models the at-issue status of the component under negation, but not in conditional
  antecedents or under pretended ignorance; the unremarkable readings and the predicative uses
  (§5) are row data.

## Errata

* With the noun's extension closed under sums (fn. 14), the modal component of (59) holds only if
  the anchor projects a world where the whole domain satisfies the scope, as the gloss "maybe all
  did" of (22) has it. It then predicts (22) false in (23a), where the speaker knows that not
  everyone danced, and (37), (41) and (82) false in (38a), (42a) and (49), where the agent is to
  choose one at random; the paper judges all four acceptable. Restricted to atoms, the component
  predicts them.
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
* [dowty-1991]
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

section Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An individual, a nonempty set of items, was taken in a world, the set of items the agent took
(bought, liked, grabbed), when each of its members was. -/
def Took (w y : Finset ι) : Prop := y ⊆ w

instance (w : Finset ι) : DecidablePred (Took w) := fun y ↦ inferInstanceAs (Decidable (y ⊆ w))

/-- The atoms, the extension of a singular noun. -/
abbrev atoms : Finset (Finset ι) := univ.map ⟨({·}), singleton_injective⟩

/-- The sums, the extension of a number-neutral noun. -/
abbrev sums : Finset (Finset ι) := univ.filter Finset.Nonempty

-- fn. 14
theorem mem_sums_iff {y : Finset ι} : y ∈ sums ↔ Mereology.AlgClosure (· ∈ atoms) y := by
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · refine Nonempty.cons_induction (fun a ↦ .base (by simp)) fun a s h _ ih ↦ ?_
    rw [cons_eq_insert, insert_eq, ← sup_eq_union]
    exact .sum (.base (by simp)) ih
  · intro hy
    induction hy with
    | base h => obtain ⟨a, -, rfl⟩ := mem_map.1 h; exact singleton_nonempty a
    | sum _ _ ih _ => exact ih.mono le_sup_left

variable (ι) in
/-- A scenario fixes the worlds each anchor projects: the worlds where the decision behind the VP
event is fulfilled, if the event has one; the content of the speech event, the speaker's doxastic
alternatives for an assertion and the worlds where the decision leading to an order is fulfilled
for an order; and the belief state of an attitude embedding the DP, if any. -/
structure Scenario where
  decision : Option (Finset (Finset ι))
  speech : Finset (Finset ι)
  force : Force
  attitude : Option (Finset (Finset ι))

/-- `scenario` builds a scenario from the decision and the content of the speech event, an
assertion unless stated otherwise, with no attitude unless one is given. -/
def scenario (decision : Option (Finset (Finset ι))) (speech : Finset (Finset ι) := ∅)
    (force : Force := .assertion) (attitude : Option (Finset (Finset ι)) := none) : Scenario ι :=
  ⟨decision, speech, force, attitude⟩

/-- `s.worlds e` is the set of worlds the anchor `e` projects in `s`, empty where it projects
none. -/
def Scenario.worlds (s : Scenario ι) : EventBinder → Finset (Finset ι)
  | .vpEvent => s.decision.getD ∅
  | .speechAct => s.speech
  | .attitude => s.attitude.getD ∅

/-- The domain-fixing function `f` of (59), as the relation from each anchor to the worlds it
projects. -/
def Scenario.projection (s : Scenario ι) : SetRel EventBinder (Finset ι) :=
  .ofSuccessors fun e ↦ ↑(s.worlds e)

/-- `Claim D s e w` is the claim of a *yalnhej* DP whose noun has extension `D`, anchored to
`e`. -/
def Claim (D : Finset (Finset ι)) (s : Scenario ι) (e : EventBinder) (w : Finset ι) : Prop :=
  ModalExists s.projection D Took e w

variable {D : Finset (Finset ι)} {s : Scenario ι} {e : EventBinder} {w : Finset ι}

omit [Fintype ι] [DecidableEq ι] in
theorem claim_iff : Claim D s e w ↔ (∃ y ∈ D, y ⊆ w) ∧ ∀ y ∈ D, ∃ v ∈ s.worlds e, y ⊆ v := by
  simp [Claim, ModalExists, claim, FreeChoice, Diamond, Scenario.projection, Took]

instance : Decidable (Claim D s e w) := decidable_of_iff _ claim_iff.symm

omit [DecidableEq ι] in
theorem claim_atoms_iff : Claim atoms s e w ↔ w.Nonempty ∧ ∀ x, ∃ v ∈ s.worlds e, x ∈ v := by
  simp [claim_iff, Finset.Nonempty]

omit [DecidableEq ι] in
theorem freeChoice_sums_iff [Nonempty ι] :
    FreeChoice s.projection e sums Took ↔ univ ∈ s.worlds e := by
  rw [freeChoice_iff_of_isGreatest s.projection e sums Took ⟨by simp, fun y _ ↦ subset_univ y⟩
    fun _ _ _ hba ha ↦ Subset.trans hba ha]
  simp [Diamond, Scenario.projection, Took]

omit [DecidableEq ι] in
/-- Over the sums, the claim says that something was taken and that the anchor projects the world
in which everything was: *maybe all did*. -/
theorem claim_sums_iff [Nonempty ι] : Claim sums s e w ↔ w.Nonempty ∧ univ ∈ s.worlds e := by
  rw [Claim, ModalExists, freeChoice_sums_iff]
  simp only [claim, mem_filter, mem_univ, true_and, Took]
  exact and_congr_left' ⟨fun ⟨y, hy, hyw⟩ ↦ hy.mono hyw, fun h ↦ ⟨w, h, subset_rfl⟩⟩

omit [Fintype ι] [DecidableEq ι] in
/-- An anchor all of whose worlds lack some item rules the component out, over the atoms or the
sums: a decision to buy one particular book, or a belief state in which one particular dish was
liked (Figs. 1–2 (b)). -/
theorem not_claim_of_forall_not_mem {x : ι} (hD : ∃ y ∈ D, x ∈ y)
    (hx : ∀ v ∈ s.worlds e, x ∉ v) : ¬ Claim D s e w := by
  rw [claim_iff]
  rintro ⟨-, h⟩
  obtain ⟨y, hy, hxy⟩ := hD
  obtain ⟨v, hv, hyv⟩ := h y hy
  exact hx v hv (hyv hxy)

-- (34), Fig. 2
omit [Fintype ι] [DecidableEq ι] in
theorem nonvolitional (speech : Finset (Finset ι)) (force : Force)
    (att : Option (Finset (Finset ι))) : ¬ Claim D (scenario none speech force att) .vpEvent w := by
  rintro ⟨⟨y, hy, -⟩, h⟩
  simpa [Diamond, Scenario.projection, Scenario.worlds, scenario] using h y hy

/-! ### Position and anchors (§3.4) -/

/-- A site is the base position of the DP relative to the abstraction over the VP event. An
external argument merges above it (74), internal arguments and adjuncts below (62). -/
inductive Site | external | internal | adjunct
  deriving DecidableEq

/-- At a site, the DP's anchor can be bound to the VP event where the abstraction over it
c-commands the DP, to the anchor of an attitude embedding the DP (91), and to the speech event:
the assertion when left free (71), fn. 17, and the order when coindexed with the imperative's
anchor (87). -/
def binders (site : Site) (s : Scenario ι) : List EventBinder :=
  (if site = .external then [] else [.vpEvent]) ++
    (s.attitude.map fun _ ↦ EventBinder.attitude).toList ++ [.speechAct]

/-! ### Items (§§4, 6.2) -/

variable (ι) in
/-- A modal indefinite of the schema (59) varies, as §6.2 describes, in the anchors it admits,
a definedness condition, and in the bound on its witnesses; its noun's extension is the atoms or
their sums. -/
structure ModalIndefinite where
  /-- The extension of the item's noun. -/
  domain : Finset (Finset ι)
  /-- `Admits s e` holds when the item admits the anchor `e` in `s`. -/
  Admits : Scenario ι → EventBinder → Prop
  [decAdmits : ∀ s e, Decidable (Admits s e)]
  /-- `Bound w` bounds the witnesses in `w`. -/
  Bound : Finset ι → Prop
  [decBound : DecidablePred Bound]

attribute [instance] ModalIndefinite.decAdmits ModalIndefinite.decBound

/-- The item's denotation anchored to `e` is defined when the item admits the anchor and true
when the claim holds within the bound. -/
def ModalIndefinite.denotation (i : ModalIndefinite ι) (s : Scenario ι) (e : EventBinder) :
    Finset ι → SignType :=
  fun w ↦ if i.Admits s e then SignType.ofProp (Claim i.domain s e w ∧ i.Bound w) else 0

/-- The item with its noun restricted to the atoms. -/
def ModalIndefinite.atomic (i : ModalIndefinite ι) : ModalIndefinite ι := { i with domain := atoms }

/-- The decision behind a volitional event and an order have normative conditions; an assertion
and a belief state do not, having informational content (p. 35, after
[alonso-ovalle-menendez-benito-2018] pp. 29, 31). -/
def Scenario.Normative (s : Scenario ι) : EventBinder → Prop
  | .vpEvent => s.decision.isSome
  | .speechAct => s.force = .directive
  | .attitude => False

instance (s : Scenario ι) : DecidablePred s.Normative
  | .vpEvent => inferInstanceAs (Decidable (s.decision.isSome = true))
  | .speechAct => inferInstanceAs (Decidable (s.force = .directive))
  | .attitude => instDecidableFalse

/-- *Yalnhej* is number neutral, admits any anchor and has no bound (§4.2). -/
def yalnhej : ModalIndefinite ι := ⟨sums, fun _ _ ↦ True, fun _ ↦ True⟩

/-- *Uno cualquiera* is singular, admits normative anchors and requires a unique witness
(p. 31). -/
def cualquiera : ModalIndefinite ι := ⟨atoms, Scenario.Normative, UniqueWitness atoms Took⟩

/-- *N'importe quel* is singular and admits normative anchors (120). -/
def nimporteQuel : ModalIndefinite ι := ⟨atoms, Scenario.Normative, fun _ ↦ True⟩

-- (49)–(50): negation targets the modal component with the existential
theorem neg_yalnhej_denotation : -yalnhej.denotation s e w = 1 ↔ ¬ Claim sums s e w := by
  rw [neg_eq_iff_eq_neg]
  simp [ModalIndefinite.denotation, yalnhej]

/-- *Uno cualquiera* is defined anchored to the speech event exactly when it is an order, and
never anchored to a belief state: it has no epistemic reading, but a harmonic one under an
imperative ((67)–(68), (86), (93)). -/
theorem cualquiera_selective :
    (cualquiera.denotation s .speechAct w ≠ 0 ↔ s.force = .directive) ∧
      cualquiera.denotation s .attitude w = 0 := by
  constructor
  · by_cases h : s.force = .directive <;>
      simp [ModalIndefinite.denotation, cualquiera, Scenario.Normative, h]
  · simp [ModalIndefinite.denotation, cualquiera, Scenario.Normative]

-- (120)
theorem nimporteQuel_selective :
    (nimporteQuel.denotation s .speechAct w ≠ 0 ↔ s.force = .directive) ∧
      nimporteQuel.denotation s .attitude w = 0 := by
  constructor
  · by_cases h : s.force = .directive <;>
      simp [ModalIndefinite.denotation, nimporteQuel, Scenario.Normative, h]
  · simp [ModalIndefinite.denotation, nimporteQuel, Scenario.Normative]

-- (124)–(127): where everything was taken
theorem yalnhej_denotation_univ [Nonempty ι] :
    yalnhej.denotation s e univ = 1 ↔ univ ∈ s.worlds e := by
  simp [ModalIndefinite.denotation, yalnhej, claim_sums_iff, univ_nonempty]

-- (122)–(123): *algún*'s bound and *uno cualquiera*'s unique witness fail where everything was
omit [DecidableEq ι] in
theorem not_notAll_univ : ¬ NotAll atoms Took (univ : Finset ι) := by
  simp [NotAll, Took]

theorem cualquiera_denotation_univ [Nontrivial ι] (h : s.Normative e) :
    cualquiera.denotation s e univ = -1 := by
  have : ¬ UniqueWitness atoms Took (univ : Finset ι) := by
    rintro ⟨x, -, -, hx⟩
    obtain ⟨a, b, hab⟩ := exists_pair_ne ι
    exact hab (singleton_injective ((hx {a} (by simp) (subset_univ _)).trans
      (hx {b} (by simp) (subset_univ _)).symm))
  simp [ModalIndefinite.denotation, cualquiera, h, this]

end Model

/-! ### The paper's judgments -/

/-- There are two items; `0` is the one taken in the actual world unless both were. -/
abbrev Item := Fin 2

/-- `nonempty` is the set of worlds in which something was taken. -/
abbrev nonempty : Finset (Finset Item) := univ.filter Finset.Nonempty

example : Claim sums (scenario (some nonempty)) .vpEvent ({0} : Finset Item) ∧
    ¬ Claim sums (scenario (some {{0}})) .vpEvent ({0} : Finset Item) := by
  decide

example : Claim sums (scenario none {{0}, univ}) .speechAct ({0} : Finset Item) ∧
    ¬ Claim sums (scenario none {{0}}) .speechAct ({0} : Finset Item) := by
  decide

/-- A model of a row's context: the worlds its anchors project and the actual world. -/
abbrev Context := Scenario Item × Finset Item

/-- The speaker cannot tell which items were taken, nor whether all were: (27a) "you couldn't
tell who", (29a), (36a), (40a), (47). -/
def ignorant : Context := (scenario none nonempty, {0})

/-- The speaker knows that not everything was taken but not which part was: (23a) "you know for a
fact that not everyone danced, but ... you don't know who exactly danced". -/
def notAllUnknownWhich : Context := (scenario none {{0}, {1}}, {0})

/-- The speaker knows which part was taken and that it is not everything: (23b), (27c), (29b),
(36c), (40c), and (52b) "the dish that everybody didn't like, that's the one he ate". -/
def knowsWhich : Context := (scenario none {{0}}, {0})

/-- The speaker knows that everything was taken: (24), (27b), (29c), (36b), (40b). -/
def knowsAll : Context := (scenario none {univ}, univ)

/-- The agent decided to take something, whatever it was: (32a) "didn't have any specific book in
mind", (44) "doesn't need one in particular", where three of ten tools are taken. -/
def indiscriminate : Context := (scenario (some nonempty), {0})

/-- The agent decided to take everything, indiscriminately: (33) "buying books indiscriminately,
to the point where he ends up buying all books", and (123), where the decision does not
matter. -/
def allTaken : Context := (scenario (some nonempty), univ)

/-- The agent decided to take one item, any one: (38a) "they decide to choose one at random",
(42a) "she chose a place to eat at random". -/
def oneAtRandom : Context := (scenario (some {{0}, {1}}), {0})

/-- The agent decided on a specific item: (32b), (38b), (42b), and (50a), where Xun "selected a
specific card". -/
def specific : Context := (scenario (some {{0}}), {0})

/-- The rules order the addressee to pick one card at random, and the addressee does: (49), for
(82). -/
def pickOneAtRandom : Context := (scenario (some {{0}, {1}}) ∅ .directive, {0})

/-- The order permits any card, and the addressee decides on one: (85) "players must select any
card they want", and (86). -/
def anyPermitted : Context := (scenario (some {{0}}) nonempty .directive, {0})

/-- Xun thinks that some people danced and that it could be anyone; the speaker knows who danced,
not everyone: (89)–(90). -/
def xunThinksAnyone : Context := (scenario none {{0}} .assertion (some nonempty), {0})

/-- The rows whose contexts the study models, with their models. (34) gives no context, so it has
the one most favourable to random choice. -/
def contexts : List (Datum × Context) :=
  [(Examples.ex_22_23a, notAllUnknownWhich), (Examples.ex_22_23b, knowsWhich),
   (Examples.ex_22_24, knowsAll), (Examples.ex_26_27a, ignorant), (Examples.ex_26_27b, knowsAll),
   (Examples.ex_26_27c, knowsWhich), (Examples.ex_28_29a, ignorant),
   (Examples.ex_28_29b, knowsWhich), (Examples.ex_28_29c, knowsAll),
   (Examples.ex_34, indiscriminate), (Examples.ex_31_32a, indiscriminate),
   (Examples.ex_31_32b, specific), (Examples.ex_31_33, allTaken),
   (Examples.ex_35_36a, ignorant), (Examples.ex_35_36b, knowsAll),
   (Examples.ex_35_36c, knowsWhich), (Examples.ex_37_38a, oneAtRandom),
   (Examples.ex_37_38b, specific), (Examples.ex_39_40a, ignorant),
   (Examples.ex_39_40b, knowsAll), (Examples.ex_39_40c, knowsWhich),
   (Examples.ex_41_42a, oneAtRandom), (Examples.ex_41_42b, specific),
   (Examples.ex_43_44, indiscriminate), (Examples.ex_46_47, ignorant),
   (Examples.ex_50b, specific), (Examples.ex_52a, knowsWhich),
   (Examples.ex_82_49, pickOneAtRandom), (Examples.ex_82_85, anyPermitted),
   (Examples.ex_86, anyPermitted), (Examples.ex_90_89, xunThinksAnyone),
   (Examples.ex_123, allTaken)]

/-! #### What a row shows -/

/-- The analysed items by their words. *Un N qualsiasi* is *uno cualquiera*'s Italian counterpart
(p. 32); *algún* and *irgendein*, whose modal components are implicatures (§6.1), and the
modifier *komon* have no denotation here. -/
def items : List (String × ModalIndefinite Item) :=
  [("yalnhej", yalnhej), ("cualquiera", cualquiera), ("qualsiasi", cualquiera),
   ("n'importe", nimporteQuel)]

/-- The analysed item of a row, the first among its words. -/
def itemIn (row : Datum) : Option (ModalIndefinite Item) := Gloss.lookup? items row.glossStream

/-- The glossed words of a row from its item on: the clause of the item's DP, which is
fronted. -/
def clauseOf (row : Datum) : List GlossedWord :=
  row.glossedWords.dropWhile fun w ↦ (Gloss.lookup? items [w.wordform]).isNone

/-- A word bears a reflex on the verb when its morphs include the reflex's marker. -/
def Bears (w : GlossedWord) : Reflex Mayan.Host → Prop
  | .morpheme .verb ms => ∀ m ∈ ms, m.form.toList ∈ w.morphs.map (·.1)
  | _ => False

instance (w : GlossedWord) : DecidablePred (Bears w) := fun x ↦ by
  unfold Bears; split <;> infer_instance

/-- The verb of the item's clause, the first word whose lexical morph is the root of a verb of
`Chuj.Verbs.all`, with the word. -/
def verbOf (row : Datum) : Option (Verb × GlossedWord) :=
  (clauseOf row).findSome? fun w ↦ w.lexicalMorph?.bind fun r ↦
    (Chuj.Verbs.all.find? (·.form.toList = r)).map (·, w)

/-- The argument a transitive verb has extracted, the first of its subject and its object whose
extraction reflexes, by `Chuj.Extraction.realize`, the verb bears: a verb in Agent Focus has its
subject extracted, a verb without it its object. -/
def extractedFrom (w : GlossedWord) : Option ArgumentRole :=
  [ArgumentRole.A, .P].find? fun r ↦
    (Chuj.Extraction.realize (.argument r)).any fun m ↦ decide (∀ x ∈ m, Bears w x)

/-- The site of the item's DP: an adjunct when its *wh*-word means 'where'; otherwise an argument
of the clause's verb, internal as the subject of a passive (`Chuj.passive`), external or internal
as `extractedFrom` finds the subject or the object of a transitive verb, and as the subject of an
intransitive verb internal if the verb is unaccusative and external if it is unergative. The site
of a DP whose clause has no verb of `Chuj.Verbs.all`, or whose intransitive verb is classified as
neither, is not read off. -/
def siteOf (row : Datum) : Option Site :=
  if ((clauseOf row).drop 1).head?.any (·.lexicalGloss? = some "where".toList) then some .adjunct
  else (verbOf row).bind fun (v, w) ↦
    if Bears w (.morpheme .verb Chuj.passive.marker) then some .internal
    else if ArgumentFrame.np ∈ v.valency.frames then
      (extractedFrom w).map fun r ↦ if r = .A then .external else .internal
    else if v.IsUnaccusative then some .internal
    else if v.IsUnergative then some .external
    else none

/-- The sites a row leaves open: the one read off, or any. -/
def sitesOf (row : Datum) : List Site := (siteOf row).elim [.external, .internal, .adjunct] ([·])

/-- A verb is volitional when it entails that its subject acts volitionally. -/
def Volitional (v : Verb) : Prop :=
  ∃ p ∈ v.slotProfile? .external, ArgumentStructure.ProtoRoleFeature.volition ∈ p

instance (v : Verb) : Decidable (Volitional v) := by unfold Volitional; infer_instance

/-- A row's sentence is negated when one of its words is glossed as negation. -/
def Negated (row : Datum) : Prop :=
  ∃ w ∈ row.glossedWords,
    Morphology.Features.ofLabels w.labels .polarity = (UD.Polarity.Neg : Flat _)

instance (row : Datum) : Decidable (Negated row) := by unfold Negated; infer_instance

/-- The VP event of a verb that does not entail its subject's volition contains no decision
(Fig. 2). -/
def Context.gate (row : Datum) (c : Context) : Context :=
  if (verbOf row).any fun v ↦ !decide (Volitional v.1) then ({ c.1 with decision := none }, c.2)
  else c

/-- `ReadsFrom s e r` holds when the reading `r` the paper names projects from the anchor `e`:
random choice from the VP event (§4.1), an epistemic reading from an assertion (§4.2), and a
harmonic one from the anchor of an external modal, an order or an attitude (§4.3). -/
def ReadsFrom (s : Scenario Item) (e : EventBinder) (r : String) : Prop :=
  if r = "random choice" then e = .vpEvent
  else if r = "epistemic" then e = .speechAct ∧ s.force = .assertion
  else if r = "harmonic" then e = .attitude ∨ e = .speechAct ∧ s.force = .directive
  else False

instance (s : Scenario Item) (e : EventBinder) (r : String) : Decidable (ReadsFrom s e r) := by
  unfold ReadsFrom; infer_instance

/-- In the context `c`, the item `i` gives the reading `r` at `site` when an anchor the reading
projects from binds the DP there and the sentence, negated if `neg`, is true. -/
def Gives (i : ModalIndefinite Item) (neg : Prop) [Decidable neg] (c : Context) (site : Site)
    (r : String) : Prop :=
  ∃ e ∈ binders site c.1, ReadsFrom c.1 e r ∧
    (if neg then -i.denotation c.1 e c.2 else i.denotation c.1 e c.2) = 1

instance (i : ModalIndefinite Item) (neg : Prop) [Decidable neg] (c : Context) (site : Site)
    (r : String) : Decidable (Gives i neg c site r) := by
  unfold Gives; infer_instance

/-- The study's judgment of a row's reading in a modelled context, at every site the row leaves
open. -/
def Agrees (i : ModalIndefinite Item) (row : Datum) (c : Context) : Prop :=
  ∀ site ∈ sitesOf row, ∀ r ∈ row.readings,
    (r.2 == .acceptable) = decide (Gives i (Negated row) (c.gate row) site r.1)

instance (i : ModalIndefinite Item) (row : Datum) (c : Context) : Decidable (Agrees i row c) := by
  unfold Agrees; infer_instance

/-- With the noun restricted to atoms, the model predicts the judgment of every reading in every
row whose context it models. -/
theorem context_rows : ∀ p ∈ contexts, ∀ i ∈ itemIn p.1, Agrees i.atomic p.1 p.2 := by
  decide +kernel

/-- With the noun of *yalnhej* closed under sums, as (59) has it, the model's judgments differ
from the paper's in exactly four rows: (22) in (23a), where the speaker knows that not everyone
danced, and (37), (41) and (82) in (38a), (42a) and (49), where the agent is to choose one at
random. -/
theorem sums_mispredict :
    (contexts.filter fun p ↦ (itemIn p.1).any fun i ↦ !decide (Agrees i p.1 p.2)).map Prod.fst =
      [Examples.ex_22_23a, Examples.ex_37_38a, Examples.ex_41_42a, Examples.ex_82_49] := by
  decide +kernel

/-- A reading is available unembedded when the item gives it on an object, given an
indiscriminate decision and an ignorant speaker. -/
def ModalIndefinite.Available (i : ModalIndefinite Item) (r : String) : Prop :=
  Gives i False (scenario (some nonempty) nonempty, {0}) .internal r

instance (i : ModalIndefinite Item) (r : String) : Decidable (i.Available r) := by
  unfold ModalIndefinite.Available; infer_instance

/-- The readings the study analyses. -/
def analysed : List String := ["random choice", "epistemic", "harmonic"]

-- (54), (57)–(58), (93), (111)–(112), (119)–(121), fn. 20 (i)
theorem reading_rows : ∀ row ∈ Examples.all, row ∉ contexts.map Prod.fst →
    ∀ i ∈ itemIn row, ∀ r ∈ row.readings, r.1 ∈ analysed →
      (r.2 == .acceptable) = decide (i.atomic.Available r.1) := by
  decide +kernel

-- (67)–(68): a question asking which witness is felicitous only where none is unknown
theorem which_rows : ∀ row ∈ Examples.all,
    (∃ w ∈ row.glossedWords, w.lexicalGloss? = some "which".toList) →
    ∀ i ∈ itemIn row, (row.judgment == .acceptable) = !decide (i.atomic.Available "epistemic") := by
  decide +kernel

-- every row with a context, an analysed item and an analysed reading is checked
theorem contexts_complete : ∀ row ∈ Examples.all, row.context ≠ "" → (itemIn row).isSome →
    (row.readings.any fun r ↦ r.1 ∈ analysed) →
      row ∈ contexts.map Prod.fst ∨ row ∈ [Examples.ex_30b, Examples.ex_51b, Examples.ex_53b] := by
  decide +kernel

-- the passive (37), the locative (41), Agent Focus (26), a transitive's object (31), an
-- unergative's subject (22), and a verb `Chuj.Verbs.all` lacks (35)
example : [siteOf Examples.ex_37_38a, siteOf Examples.ex_41_42a, siteOf Examples.ex_26_27a,
    siteOf Examples.ex_31_32a, siteOf Examples.ex_22_23a, siteOf Examples.ex_35_36a] =
      [some .internal, some .adjunct, some .external, some .internal, some .external, none] := by
  decide +kernel

end AlonsoOvalleRoyer2024
