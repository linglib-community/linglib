module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Exhaustification.DomainAlternatives
public import Linglib.Data.Examples.AlonsoOvalleMenendezBenito2010

/-!
# Alonso-Ovalle & Menéndez-Benito (2010): modal indefinites

Spanish *algún* conveys that at least two individuals in its domain are possibilities — the
Modal Variation component (18), `ModalVariation` — where German *irgendein*
conveys the stronger Free Choice component (13c), `FreeChoice`: in the
hide-and-seek scenario (15) Pedro can use *algún* with the bathroom ruled out
(`hideAndSeek`), and under uniqueness Free Choice entails Modal Variation but not
conversely (`modalVariation_of_freeChoice`). The component is a conversational
implicature: as a presupposition it would make the negated (36) contradictory
(`not_modalVariation_of_box_empty`), and it is cancellable (42), absent under
downward entailing operators (43)–(44), and reinforceable (45d).

The paper derives it from an anti-singleton constraint (53)–(54) on the subset selection
function *algún* takes (`algún`), which excludes the singleton restrictors of (47)/(49)
(`algún_ne_one_of_singleton`). The competitors (58) are the singleton subdomains; their
falsity under a necessity modal (59) gives Modal Variation (`modalVariation_of_box`),
and under a possibility modal, where some competitor must be true
(`exists_singleton_of_diamond`), the anti-exhaustivity implicatures (67)–(68) do
(`modalVariation_of_singletons`). A domain widener competes with every proper
subdomain (70), and the same reasoning yields Free Choice (`freeChoice_of_proper`).
Without uniqueness the blocked exhaustivity inference (76) and the plural competitor (77)
give ignorance of number (`numberIgnorance_of_competition`), which uniqueness makes
unavailable (`not_numberIgnorance_of_uniqueness`) — the two parameters of Table 1. The
scenario truth-value judgments (28)–(30) are checked in `scenario_verdicts` and the felicity
rows (24)–(25) in `scenario_felicity`; the singleton-restrictor and identity-continuation rows
are read by `restrictor_rows` and `continuation_rows`, each rejected exactly under a determiner
with a modal component.

## References

* [alonso-ovalle-menendez-benito-2010]
* [kratzer-shimoyama-2002]
* [chierchia-2006]
* [von-fintel-2000-whatever]
* [dayal-1997]
* [schwarzschild-2002]
* [potts-2005]
* [zimmermann-2000]
* [jayez-tovena-2006]
-/

@[expose] public section

namespace AlonsoOvalleMenendezBenito2010

open Exhaustification ModalLogic
open SetRel

variable {E W : Type*}

/-! ### Subset selection functions (§4.1) -/

/-- A singleton subset selection function (52). -/
def IsSingleton (f : Finset E → Finset E) : Prop := ∀ P, (f P).card = 1

/-- An anti-singleton subset selection function (53). -/
def IsAntiSingleton (f : Finset E → Finset E) : Prop := ∀ P, (f P).card ≠ 1

open Classical in
/-- *un* (50) quantifies existentially over the subdomain that `f` selects from `P`. -/
noncomputable def un (f : Finset E → Finset E) (P : Finset E) (Q : W → E → Prop) :
    W → SignType :=
  fun w ↦ SignType.ofProp (∃ x ∈ f P, Q w x)

open Classical in
/-- *algún* (54) is *un*, defined only for an anti-singleton `f`. -/
noncomputable def algún (f : Finset E → Finset E) (P : Finset E) (Q : W → E → Prop) :
    W → SignType :=
  {_w | IsAntiSingleton f}.indicator (un f P Q)

/-- On a singleton restrictor (46)–(49) an anti-singleton selection returns no domain, so
*algún*'s claim cannot be true where *un*'s can. -/
theorem algún_ne_one_of_singleton {f : Finset E → Finset E} (hf : ∀ P, f P ⊆ P)
    {P : Finset E} (hP : P.card = 1) (Q : W → E → Prop) (w : W) : algún f P Q w ≠ 1 := by
  simp only [algún, un, ne_eq, Trivalent.indicator_apply_eq_one_iff, Set.mem_ofPred_eq,
    SignType.ofProp_eq_one_iff, not_and]
  intro h
  have : f P = ∅ := Finset.card_eq_zero.1 <|
    Nat.lt_one_iff.1 <| lt_of_le_of_ne (hP ▸ Finset.card_le_card (hf P)) (h P)
  simp [this]

/-! ### Non-uniqueness (§5) -/

variable (R : SetRel W W) (w : W) (D : Finset E) (Q : W → E → Prop) [∀ v, DecidablePred (Q v)]

/-- Ignorance with respect to number holds when the number of witnesses varies across the
accessible worlds. -/
def NumberIgnorance : Prop :=
  ∃ v, w ~[R] v ∧ ∃ v', w ~[R] v' ∧ (witnesses D Q v).card ≠ (witnesses D Q v').card

theorem modalVariation_of_numberIgnorance (h : NumberIgnorance R w D Q) :
    ModalVariation R w D Q :=
  let ⟨v, hv, v', hv', hne⟩ := h
  ⟨v, hv, v', hv', fun h => hne (h ▸ rfl)⟩

/-- With the exhaustivity inference of a singleton domain blocked and the plural competitor (77)
unassertable, a true claim conveys ignorance of number ((76)–(78)). -/
theorem numberIgnorance_of_competition (hc : □[R] (claim Q D) w)
    (h₁ : ¬ □[R] (fun v => (witnesses D Q v).card = 1) w)
    (h₂ : ¬ □[R] (fun v => 2 ≤ (witnesses D Q v).card) w) : NumberIgnorance R w D Q := by
  simp only [Box, not_forall] at h₁ h₂
  obtain ⟨v, hv, h₁⟩ := h₁
  obtain ⟨v', hv', h₂⟩ := h₂
  refine ⟨v, hv, v', hv', fun h => ?_⟩
  have := Finset.card_pos.2 ((claim_iff_witnesses_nonempty D Q v').1 (hc v' hv'))
  omega

theorem not_numberIgnorance_of_uniqueness (hU : Uniqueness R w D Q) (h : □[R] (claim Q D) w) :
    ¬ NumberIgnorance R w D Q := by
  rintro ⟨v, hv, v', hv', hne⟩
  have one : ∀ v, w ~[R] v → (witnesses D Q v).card = 1 := fun v hv =>
    le_antisymm (hU v hv) (Finset.card_pos.2 ((claim_iff_witnesses_nonempty D Q v).1 (h v hv)))
  exact hne ((one v hv).trans (one v' hv').symm)

/-- Naming the witness contradicts Modal Variation: with every accessible world agreeing on the
witness set, no two differ, so a determiner with a modal component rejects the *namely* and
which-question continuations of (2) and (8)–(9). -/
theorem not_modalVariation_of_box_witnesses {x : Finset E}
    (h : □[R] (fun v ↦ witnesses D Q v = x) w) : ¬ ModalVariation R w D Q :=
  fun ⟨v, hv, v', hv', hne⟩ ↦ hne ((h v hv).trans (h v' hv').symm)

/-! ### The scenarios -/

/-- The hiding places; the domain of *habitación de la casa* is the house. -/
inductive Room | bedroom | livingRoom | bathroom | kitchen | barn
  deriving DecidableEq, Fintype

/-- Worlds are Juan's hiding places. -/
def inRoom (w r : Room) : Prop := w = r

instance (w : Room) : DecidablePred (inRoom w) := fun r => inferInstanceAs (Decidable (w = r))

abbrev house : Finset Room := {.bedroom, .livingRoom, .bathroom, .kitchen}

/-- Pedro's epistemic alternatives, the rooms he takes to be possible from any world. -/
def epist (A : Finset Room) : SetRel Room Room := .ofSuccessors fun _ ↦ ↑A

instance (A : Finset Room) (w r : Room) : Decidable (w ~[epist A] r) :=
  inferInstanceAs (Decidable (r ∈ A))

/-- Pedro rules out the bathroom and the kitchen (15). -/
abbrev pedro15 : Finset Room := {.bedroom, .livingRoom}
/-- Pedro considers only the bathroom (23). -/
abbrev pedro23 : Finset Room := {.bathroom}
/-- Pedro considers the other rooms or the barn (27). -/
abbrev pedro27 : Finset Room := {.bedroom, .livingRoom, .barn}

/-- The candidates of (29); worlds are the permitted hires. -/
inductive Candidate | phdA | phdB | noPhd
  deriving DecidableEq, Fintype

def hires (w c : Candidate) : Prop := w = c

instance (w : Candidate) : DecidablePred (hires w) := fun c => inferInstanceAs (Decidable (w = c))

/-- The permitted hires, from any world. -/
def permitted : SetRel Candidate Candidate :=
  .ofSuccessors fun _ ↦ ↑({.phdA, .phdB} : Finset Candidate)

instance (w c : Candidate) : Decidable (w ~[permitted] c) :=
  inferInstanceAs (Decidable (c ∈ ({.phdA, .phdB} : Finset Candidate)))

/-- In (15) Modal Variation holds without Free Choice, the singleton competitors being false (59b)
with anti-exhaustivity implicatures (68b), unlike the widening competitor (72). -/
theorem hideAndSeek (w : Room) :
    ModalVariation (epist pedro15) w house inRoom ∧ ¬ FreeChoice (epist pedro15) w house inRoom ∧
      (∀ S ∈ subdomainAlternatives .singletons house, ¬ □[epist pedro15] (claim inRoom S) w) ∧
      (∀ S ∈ subdomainAlternatives .singletons house,
        AntiExhaustivity (epist pedro15) w house inRoom S) ∧
      ¬ AntiExhaustivity (epist pedro15) w house inRoom {.bedroom, .livingRoom} := by
  revert w; decide

/-! ### The paper's verdicts -/

/-- A row's predicted verdict, where *algún* needs Modal Variation, *cualquiera* Free Choice,
and *un* nothing. -/
def predicted (row : Datum) : Option Bool :=
  match row.feature? "scenario", row.feature? "determiner" with
  | some "hideAndSeek15", some d => verdictIn (epist pedro15) house inRoom d
  | some "oneRoom23", some d => verdictIn (epist pedro23) house inRoom d
  | some "barn27", some d => verdictIn (epist pedro27) house inRoom d
  | some "hiring29", some d => verdictIn permitted Finset.univ hires d
  | _, _ => none
where
  verdictIn {E W : Type} [DecidableEq E] [DecidableEq W] [Fintype W] (R : SetRel W W)
      [∀ x y, Decidable (x ~[R] y)] (D : Finset E) (Q : W → E → Prop) [∀ v, DecidablePred (Q v)] :
      String → Option Bool
    | "algún" => some (decide (∀ w, ModalVariation R w D Q))
    | "cualquiera" => some (decide (∀ w, FreeChoice R w D Q))
    | "un" => some true
    | _ => none

/-- The scenario rows with a truth-value judgment, (28) and (30), are true exactly where the
component the determiner needs holds in the scenario. -/
theorem scenario_verdicts : ∀ row ∈ Examples.all, row.FitsVerdict predicted id := by
  decide +kernel

/-- The scenario rows judged for felicity rather than truth. -/
def felicity? (row : Datum) : Option Bool :=
  match row.verdict with
  | some _ => none
  | none => predicted row

/-- The felicity rows (7) and (24)–(25): *algún* is felicitous in a scenario exactly where its
Modal Variation component holds. -/
theorem scenario_felicity :
    ∀ row ∈ Examples.all, row.Fits felicity? fun b ↦ .ofProp (b = true) := by
  decide +kernel

theorem scenario_read :
    Datum.ReadCount felicity? Examples.all 3 ∧
      (Examples.all.filter fun row => row.verdict.isSome ∧ (predicted row).isSome).length = 4 := by
  decide +kernel

/-- Whether a determiner carries a modal component, (13) and (18): *algún* and the
*irgend*-series do, *un* and plural *algunos* do not. -/
inductive DetClass where
  | modal
  | plain
  deriving DecidableEq, Repr

/-- The class of a row's determiner. -/
def detClass? (e : Datum) : Option DetClass :=
  e.parse? "determiner"
    [("algún", .modal), ("irgendwelche", .modal), ("un", .plain), ("algunos", .plain)]

/-- A row whose determiner heads a singleton restrictor, (46)–(49). -/
def singletonRestrictor? (e : Datum) : Option DetClass := do
  let c ← detClass? e
  let _ ← e.parse? "restrictor" [("singleton", ())]
  pure c

/-- A singleton restrictor is rejected exactly by a determiner with a modal component, whose
anti-singleton selection returns no domain (`algún_ne_one_of_singleton`), (46)–(49). -/
theorem restrictor_rows : ∀ e ∈ Examples.all, e.Fits singletonRestrictor? fun c ↦
    match c with
    | .modal => .rejected
    | .plain => .accepted := by
  decide +kernel

theorem restrictor_read : Datum.ReadCount singletonRestrictor? Examples.all 4 := by
  decide +kernel

/-- A row whose sentence carries an identity-revealing continuation, a *namely*-appositive or an
answered which-question. -/
def identityContinuation? (e : Datum) : Option DetClass := do
  let c ← detClass? e
  let _ ← e.parse? "continuation" [("namely", ()), ("which-question", ())]
  pure c

/-- An identity-revealing continuation is rejected exactly by a determiner with a modal
component, whose Modal Variation it contradicts (`not_modalVariation_of_box_witnesses`):
(2)–(3), (8)–(11) and the plurals of (82). -/
theorem continuation_rows : ∀ e ∈ Examples.all, e.Fits identityContinuation? fun c ↦
    match c with
    | .modal => .rejected
    | .plain => .accepted := by
  decide +kernel

theorem continuation_read : Datum.ReadCount identityContinuation? Examples.all 8 := by
  decide +kernel

end AlonsoOvalleMenendezBenito2010
