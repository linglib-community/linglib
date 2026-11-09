module

public import Studies.BarAsherSiegal2026
public import Linglib.Logic.Assignment

/-!
# Bar-Asher Siegal and Nadathur (2026): Modeling progress

An accomplishment predicate introduces a causal model with its culmination condition as a
dependent variable, and its progressive says that the reference situation has begun a culmination
procedure but completed neither a procedure nor a sufficient set for non-culmination. A sufficient
set is [a consistent situation that its effect's value singles out](##isSufficient_iff); with the
effect erased it [forces the effect](##IsSufficient.isSufficientSet), though the earlier minimal
sufficient sets [drop the door's button](##electronic_differs). *Nur is opening the door* comes out
[false when the door is realistically closed](##not_prog_realistic) and is
[defined just when the lock is settled](##defined_iff).

## Implementation notes

* An equation is read on a situation by `CausalModel.ForcedBy`: its value is the one on which every
  completion of the parents' settled values agrees in every context, the supervaluation. The paper
  calls its tables strong Kleene; the two readings differ on an equation such as $p \vee \neg p$.
* Necessity quantifies over the consistent situations over the same variables. These are the
  reassignments of the situation (`forall_domain_eq_iff`), which decides it.
* Times form any preorder; the door's histories put the reference time at 1 and the interval just
  before it at 0.
* Each sufficient set for non-culmination is the only consistent situation over its variables
  (`nonCulmination_unique`), so each of its facts is necessary because no consistent situation
  over the same variables changes it. In the mechanical procedure every consistent situation over
  its variables that turns the handle back also engages the lock (`handle_alternatives_lock`), so
  the handle is necessary there only by way of a locked door.

## Errata

* (26) prints the light's equation as $S_1 \wedge S_2$, but Figure 1b and (25a) give the
  biconditional $S_1 \leftrightarrow S_2$. The two disagree on Figure 1b's fifth line, both switches
  down with the light on, and on its fourth, the first switch down with the light undetermined,
  which the conjunction settles off (`Lifschitz.printed_contradicts`).
* (30a) quantifies over every consistent situation over the same variables that changes the cause,
  so a sufficient set must be the only consistent situation over its variables that gives the effect
  its value (`isSufficient_iff`). The circuit's two settings that light the lamp share their
  variables, as do the two that leave it off, so the light has no sufficient set at all, against the
  four listed after (30), and ⟨S₁,0⟩ is not necessary for the light off in (25b)
  (`Lifschitz.not_isSufficient`). The argument given there, that changing $S_1$ requires changing
  the light, holds once the other switch is held fixed (`Lifschitz.light_changes_of_s₂_fixed`).
  Holding fixed what does not descend from the cause does not repair (30a), though: on the door it
  leaves the handle of (38a) with no consistent alternative at all (`handle_alternatives_lock`), so
  the door's verdicts would hold only vacuously.
* (39b) and (39c) are printed without the effect fact ⟨O,0⟩, which (30b) puts in every sufficient
  set and (39a) includes; as printed they are not sufficient (`not_sufficient_as_printed`).
* After Table 2 the paper says the table shows a circuit known to be closed settling the door with
  the button unknown. No row of Table 2 settles the circuit with the button open, and by (29) no
  consistent situation does (`button_mem_domain_of_circuit`).

## TODO

* The paper's repair for the realistic context of (40), which lets a sufficient set for
  non-culmination be undone by updating a fungible background variable, is left open, as it is in
  the paper.
* (38) and (39) list every sufficient set of the door, as the paper says. This is checked by
  evaluation over its 729 situations but not proved; a proof needs a characterization of the
  door's consistent situations.
* That `CausalModel.ForcedBy` agrees with strong Kleene evaluation on the door's and the circuit's
  equations, as footnote 30 requires, is unproved; it needs the knowledge order of `Trivalent`
  related to `Flat Bool`.
* The variable distance scenario (44) has no model.

## References

* [bar-asher-siegal-nadathur-2026]
* [bar-asher-siegal-2026]
* [baglini-bar-asher-siegal-2025]
-/

@[expose] public section

namespace BarAsherSiegalNadathur2026

open CausalModel

/-! ### Situations and causal consistency

A situation (28b) is a partial assignment of truth values, `PartialAssign V Bool`, and its domain
(28c) is `PartialAssign.domain`. -/

section Model

variable {U V : Type*} (M : CausalModel U V fun _ ↦ Bool)

/-- Causal consistency (29): every settled dependent variable has the value that what `s` settles
about its parents forces. -/
def Consistent (s : PartialAssign V Bool) : Prop :=
  ∀ v, (∃ w, M.graph.Adj w v) → ∀ b : Bool, s v = ↑b → M.ForcedBy (s · = ↑·) v b

/-- Causal necessity (30a): the fact `s` settles at `x` is necessary for the one it settles at
`y` when `x` is a causal ancestor of `y` and every consistent situation over the same variables
that changes `x` changes `y`. -/
def Necessary (s : PartialAssign V Bool) (x y : V) : Prop :=
  Relation.TransGen M.graph.Adj x y ∧
    ∀ s', s'.domain = s.domain → Consistent M s' → s' x ≠ s x → s' y ≠ s y

/-- Causal sufficiency (30b): `s` is consistent, settles `y` at `b`, and each of its other facts
is necessary for that one. The kernel of `s` is then a sufficient set for ⟨y, b⟩. -/
def IsSufficient (s : PartialAssign V Bool) (y : V) (b : Bool) : Prop :=
  Consistent M s ∧ s y = ↑b ∧ ∀ x ∈ s.domain, x ≠ y → Necessary M s x y

/-! ### The progressive -/

section Progressive

variable {T : Type*} [Preorder T]

/-- Felicity (33a): the predicate has a culmination procedure, a sufficient set for its
culmination condition `c`. -/
def Felicitous (c : V) : Prop := ∃ S, IsSufficient M S c true

/-- INIT (36a): at time `t` the history `σ` settles some fact of a culmination procedure that it
did not settle throughout an interval just before `t`. -/
def Init (c : V) (σ : T → PartialAssign V Bool) (t : T) : Prop :=
  ∃ S, IsSufficient M S c true ∧ ∃ v, ∃ b : Bool, S v = ↑b ∧ σ t v = ↑b ∧
    ∃ t' < t, ∀ t'' ∈ Set.Ico t' t, σ t'' v ≠ ↑b

/-- CUL (36b-i): some culmination procedure is completely realized. -/
def Cul (c : V) (s : PartialAssign V Bool) : Prop := ∃ S, IsSufficient M S c true ∧ S ≤ s

/-- TERM (36b-ii): some sufficient set for non-culmination is completely realized. -/
def Term (c : V) (s : PartialAssign V Bool) : Prop := ∃ S, IsSufficient M S c false ∧ S ≤ s

/-- The progressive (35): initiated, and neither culminated nor terminated. -/
def Prog (c : V) (σ : T → PartialAssign V Bool) (t : T) : Prop :=
  Init M c σ t ∧ ¬ (Cul M c (σ t) ∨ Term M c (σ t))

variable [DecidableEq V]

/-- A globally necessary condition (42): the fact ⟨v, b⟩ is globally necessary for `c` when its
negation together with non-culmination is a sufficient set for non-culmination. -/
def GloballyNecessary (c v : V) (b : Bool) : Prop :=
  IsSufficient M [c ← false, v ← !b] c false

/-- Definedness (45): the progressive is defined when every globally necessary condition is
settled at reference time. -/
def Defined (c : V) (s : PartialAssign V Bool) : Prop :=
  ∀ v b, GloballyNecessary M c v b → v ∈ s.domain

end Progressive

variable {M}

/-- A sufficient set is a consistent situation over causal ancestors of its effect that is the only
consistent situation over its variables giving the effect its value. -/
theorem isSufficient_iff {s : PartialAssign V Bool} {y : V} {b : Bool} :
    IsSufficient M s y b ↔ Consistent M s ∧ s y = ↑b ∧
      (∀ x ∈ s.domain, x ≠ y → Relation.TransGen M.graph.Adj x y) ∧
        ∀ s', s'.domain = s.domain → Consistent M s' → s' y = s y → s' = s := by
  refine ⟨fun ⟨hc, hy, h⟩ ↦ ⟨hc, hy, fun x hx hxy ↦ (h x hx hxy).1,
    fun s' hd hc' hy' ↦ funext fun v ↦ ?_⟩, fun ⟨hc, hy, hanc, h⟩ ↦ ⟨hc, hy, fun x hx hxy ↦
      ⟨hanc x hx hxy, fun s' hd hc' hx' hy' ↦ hx' (congrFun (h s' hd hc' hy') x)⟩⟩⟩
  by_cases hv : v ∈ s.domain
  · rcases eq_or_ne v y with rfl | hvy
    · exact hy'
    · exact not_not.1 fun hne ↦ (h v hv hvy).2 s' hd hc' hne hy'
  · have hv' : v ∉ s'.domain := hd ▸ hv
    rw [not_not.1 hv, not_not.1 hv']

theorem IsSufficient.eq_of_le {S s : PartialAssign V Bool} {y : V} {b : Bool}
    (h : IsSufficient M S y b) (hle : S ≤ s) : s y = ↑b :=
  Flat.coe_le_iff.1 (h.2.1 ▸ hle y)

theorem not_cul_or_term {c : V} {s : PartialAssign V Bool} (h : s c = ⊥) :
    ¬ (Cul M c s ∨ Term M c s) := by
  rintro (⟨S, hS, hle⟩ | ⟨S, hS, hle⟩) <;> exact Flat.coe_ne_bot ((hS.eq_of_le hle).symm.trans h)

-- (36a): an unchanging history initiates nothing
theorem not_init_const {T : Type*} [Preorder T] {c : V} {s : PartialAssign V Bool} {t : T} :
    ¬ Init M c (fun _ ↦ s) t := by
  rintro ⟨-, -, v, b, -, hs, t', ht', h⟩
  exact h t' ⟨le_rfl, ht'⟩ hs

/-- The situation over the variables of `s` that gives them the values of `b`. -/
def reassign (s : PartialAssign V Bool) (b : s.domain → Bool) : PartialAssign V Bool :=
  fun v ↦ if h : v ∈ s.domain then ↑(b ⟨v, h⟩) else ⊥

theorem domain_reassign (s : PartialAssign V Bool) (b : s.domain → Bool) :
    (reassign s b).domain = s.domain := by
  ext v
  change reassign s b v ≠ ⊥ ↔ s v ≠ ⊥
  unfold reassign
  split_ifs with h
  · exact iff_of_true Flat.coe_ne_bot h
  · exact iff_of_false (· rfl) h

-- the situations over the variables of `s` are its reassignments
theorem forall_domain_eq_iff {s : PartialAssign V Bool} {P : PartialAssign V Bool → Prop} :
    (∀ s', s'.domain = s.domain → P s') ↔ ∀ b, P (reassign s b) := by
  refine ⟨fun h b ↦ h _ (domain_reassign s b), fun h s' hs' ↦ ?_⟩
  convert h fun v ↦ (s' v).unbotD false
  funext v
  have hv : s' v = ⊥ ↔ s v = ⊥ := not_iff_not.1 (Set.ext_iff.1 hs' v)
  unfold reassign
  split_ifs with h
  · obtain ⟨a, ha⟩ := Flat.ne_bot_iff_exists.1 (mt hv.1 h)
    simp [ha, Flat.unbotD_coe]
  · exact hv.2 (not_not.1 h)

variable [DecidableEq V]

/-- With its effect erased, a sufficient set forces the effect in the Kleene development, so it is
a sufficient set in the sense of Baglini and Bar-Asher Siegal. -/
theorem IsSufficient.isSufficientSet [M.IsAcyclic] {S : PartialAssign V Bool} {y : V} {b : Bool}
    (h : IsSufficient M S y b) (hy : ∃ w, M.graph.Adj w y) :
    BarAsherSiegal2026.IsSufficientSet M (Function.update S y ⊥) y b := by
  refine ⟨Function.update_self .., forced_iff.2 (.inr ⟨Function.update_self .., ?_⟩)⟩
  refine (h.1 y hy b h.2.1).mono fun w hw z hz ↦ forced_iff.2 (.inl ?_)
  rwa [Function.update_of_ne (by rintro rfl; exact _root_.asymm hw hw)]

section Decidable

variable [Fintype V]

instance (s : PartialAssign V Bool) (P : PartialAssign V Bool → Prop) [DecidablePred P] :
    Decidable (∀ s', s'.domain = s.domain → P s') :=
  decidable_of_iff _ forall_domain_eq_iff.symm

variable [Fintype U] [DecidableRel M.graph.Adj]

instance (s : PartialAssign V Bool) : Decidable (Consistent M s) := by
  unfold Consistent; infer_instance

instance (s : PartialAssign V Bool) (x y : V) : Decidable (Necessary M s x y) := by
  unfold Necessary; infer_instance

instance (s : PartialAssign V Bool) (y : V) (b : Bool) : Decidable (IsSufficient M s y b) :=
  decidable_of_iff _ isSufficient_iff.symm

instance (c v : V) (b : Bool) : Decidable (GloballyNecessary M c v b) := by
  unfold GloballyNecessary; infer_instance

end Decidable

end Model

/-! ### The Lifschitz circuit (Figure 1) -/

namespace Lifschitz

/-- The variables of Figure 1: two switches and a light. -/
inductive V | s₁ | s₂ | light
  deriving DecidableEq, Fintype, Repr

/-- Each switch bears on the light. -/
def edges : Finset (V × V) := {(.s₁, .light), (.s₂, .light)}

/-- The context settles the two switches. -/
structure Context where
  s₁ : Bool
  s₂ : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- The light is on just when the two switches are in the same position (Figure 1b). -/
def model : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn
    | .s₁ => fun u _ ↦ u.s₁
    | .s₂ => fun u _ ↦ u.s₂
    | .light => fun _ x ↦ x .s₁ == x .s₂

/-- The light with its equation as (26) prints it, the conjunction of the switches. -/
def printed : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn
    | .s₁ => fun u _ ↦ u.s₁
    | .s₂ => fun u _ ↦ u.s₂
    | .light => fun _ x ↦ x .s₁ && x .s₂

instance : DecidableRel model.graph.Adj := fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : DecidableRel printed.graph.Adj := fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ edges))

open V

/-- The situation of (25b): the first switch down, the second up, the light off. -/
def s25b : PartialAssign V Bool := [s₁ ← false, s₂ ← true, light ← false]

-- (25b), (29)
theorem consistent_25b : Consistent model s25b ∧
    ¬ Consistent model [s₁ ← false, s₂ ← true, light ← true] := by
  decide

section

attribute [local instance] fintypePartialAssignment

-- the sufficient sets listed after (30), and the necessity of the first switch in (25b)
theorem not_isSufficient :
    ¬ Necessary model s25b s₁ light ∧
      ∀ S b, ¬ IsSufficient model S light b := by
  decide +kernel

end

-- the argument after (30), with the second switch held fixed
theorem light_changes_of_s₂_fixed :
    ∀ s', s'.domain = s25b.domain → Consistent model s' → s' s₁ ≠ s25b s₁ →
      s' s₂ = s25b s₂ → s' light ≠ s25b light := by
  decide +kernel

-- (26), the fifth and fourth lines of Figure 1b
theorem printed_contradicts :
    Consistent model [s₁ ← false, s₂ ← false, light ← true] ∧
      ¬ Consistent printed [s₁ ← false, s₂ ← false, light ← true] ∧
      ¬ Consistent model [s₁ ← false, light ← false] ∧
      Consistent printed [s₁ ← false, light ← false] := by
  decide

end Lifschitz

/-! ### The dual-route door (Section 4.2) -/

section Door

open BarAsherSiegal2026 (V model manual automatic IsMinimalSufficientSet)
open BarAsherSiegal2026.V

/-- The mechanical procedure (38a): handle turned, door unlocked, door open. -/
def sMech : PartialAssign V Bool := [handle ← true, lock ← false, doorOpens ← true]

/-- The electronic procedure (38b): door unlocked, power on, button pressed, circuit closed, door
open. -/
def sElec : PartialAssign V Bool :=
  [lock ← false, electricity ← true, button ← true, circuit ← true, doorOpens ← true]

/-- Non-culmination by the lock (39a). -/
def sLock : PartialAssign V Bool := [lock ← true, doorOpens ← false]

/-- Non-culmination with the handle unturned and no power (39b), with the effect fact. -/
def sNotElec : PartialAssign V Bool := [handle ← false, electricity ← false, doorOpens ← false]

/-- Non-culmination with the handle unturned and the button unpressed (39c), with the effect
fact. -/
def sNotCirc : PartialAssign V Bool :=
  [handle ← false, button ← false, circuit ← false, doorOpens ← false]

theorem sMech_sufficient : IsSufficient model sMech doorOpens true := by decide +kernel

theorem sElec_sufficient : IsSufficient model sElec doorOpens true := by decide +kernel

theorem sLock_sufficient : IsSufficient model sLock doorOpens false := by decide +kernel

theorem sNotElec_sufficient : IsSufficient model sNotElec doorOpens false := by decide +kernel

theorem sNotCirc_sufficient : IsSufficient model sNotCirc doorOpens false := by decide +kernel

-- (39b), (30b)
theorem not_sufficient_as_printed :
    ¬ IsSufficient model [handle ← false, electricity ← false] doorOpens false := by
  decide

theorem nonCulmination_unique :
    ∀ S ∈ [sLock, sNotElec, sNotCirc], ∀ s', s'.domain = S.domain → Consistent model s' →
      s' = S := by
  decide +kernel

-- (38a)
theorem handle_alternatives_lock :
    ∀ s', s'.domain = sMech.domain → Consistent model s' → s' handle ≠ sMech handle →
      s' lock ≠ sMech lock := by
  decide +kernel

-- (33a)
theorem felicitous : Felicitous model doorOpens := ⟨sMech, sMech_sufficient⟩

-- footnote 39
theorem button_necessary :
    Necessary model sElec button circuit ∧ Necessary model sElec button doorOpens := by
  decide +kernel

-- the circuit's equation reads the button alone
theorem button_mem_domain_of_circuit {s : PartialAssign V Bool} (hs : Consistent model s)
    (hc : circuit ∈ s.domain) : button ∈ s.domain := by
  have hadj : ∀ w, model.graph.Adj w circuit → w = button := by decide
  obtain ⟨c, hc⟩ := Flat.ne_bot_iff_exists.1 hc
  by_contra hb
  have hb : s button = ⊥ := not_not.1 hb
  have := hs circuit ⟨button, by decide⟩ c hc default (fun _ ↦ !c) fun w hw z hz ↦ by
    obtain rfl := hadj w hw
    exact absurd (hb ▸ hz) Flat.bot_ne_coe
  simp [model] at this

/-- The two causal semantics agree on the mechanical route and part on the electronic one. The
electronic procedure without its effect is no minimal sufficient set of Baglini and Bar-Asher
Siegal, its button being redundant for forcing the door open, and their minimal set, which settles
the circuit without the button, is no procedure. -/
theorem electronic_differs :
    Function.update sMech doorOpens ⊥ = manual ∧
      ¬ IsMinimalSufficientSet model (Function.update sElec doorOpens ⊥) doorOpens true ∧
      ¬ IsSufficient model (Function.update automatic doorOpens ↑true) doorOpens true :=
  ⟨by decide +kernel, by decide +kernel,
    fun h ↦ absurd (button_mem_domain_of_circuit h.1 (by decide +kernel)) (by decide +kernel)⟩

/-- Before reference time the door is unlocked and the power off; at it, Nur has switched the
power on, leaving handle and button undetermined. -/
def switchingOn : ℕ → PartialAssign V Bool
  | 0 => [lock ← false, electricity ← false]
  | _ => [lock ← false, electricity ← true]

/-- The realistic context of (40): Nur switches the power on, having turned neither the handle
nor the button, so the door is closed. -/
def realistic : ℕ → PartialAssign V Bool
  | 0 => [handle ← false, lock ← false, electricity ← false, button ← false, circuit ← false,
      doorOpens ← false]
  | _ => [handle ← false, lock ← false, electricity ← true, button ← false, circuit ← false,
      doorOpens ← false]

-- (40), row `basn2026_40_switchedOn`
theorem prog_switchingOn : Prog model doorOpens switchingOn 1 := by
  refine ⟨⟨sElec, sElec_sufficient, electricity, true, by decide, by decide, 0, zero_lt_one,
    fun t ht ↦ ?_⟩, not_cul_or_term (by decide)⟩
  obtain rfl : t = 0 := Nat.lt_one_iff.1 ht.2
  decide

/-- In the realistic context *Nur is opening the door* comes out false, against the reported
judgment, as the paper observes: the unturned handle and unpressed button realize a sufficient set
for non-culmination. -/
theorem not_prog_realistic : ¬ Prog model doorOpens realistic 1 :=
  fun h ↦ h.2 (.inr ⟨sNotCirc, sNotCirc_sufficient, by decide⟩)

-- (42)
theorem globallyNecessary_iff {v : V} {b : Bool} :
    GloballyNecessary model doorOpens v b ↔ v = lock ∧ b = false := by
  revert v b
  decide +kernel

/-- The progressive of *open the door* is defined exactly when the lock is settled, the lock
being the door's only globally necessary condition. -/
theorem defined_iff {s : PartialAssign V Bool} : Defined model doorOpens s ↔ lock ∈ s.domain :=
  ⟨fun hd ↦ hd lock false (globallyNecessary_iff.2 ⟨rfl, rfl⟩),
    fun h _ _ hv ↦ (globallyNecessary_iff.1 hv).1 ▸ h⟩

/-- With the lock's state unknown, Nur has turned the handle. -/
def handleTurned : ℕ → PartialAssign V Bool
  | 0 => [handle ← false]
  | _ => [handle ← true]

-- (43a), row `basn2026_43a_handle`: the truth conditions hold, but the progressive is undefined
theorem prog_and_not_defined :
    Prog model doorOpens handleTurned 1 ∧ ¬ Defined model doorOpens (handleTurned 1) := by
  refine ⟨⟨⟨sMech, sMech_sufficient, handle, true, by decide, by decide, 0, zero_lt_one,
    fun t ht ↦ ?_⟩, not_cul_or_term (by decide)⟩, defined_iff.not.2 (by decide)⟩
  obtain rfl : t = 0 := Nat.lt_one_iff.1 ht.2
  decide

end Door

end BarAsherSiegalNadathur2026
