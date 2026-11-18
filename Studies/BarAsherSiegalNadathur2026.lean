module

public import Studies.BarAsherSiegal2026

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
* Necessity quantifies over the consistent situations defined on the same variables, which are
  decided through the total assignments restricted to those variables
  (`Part.forall_dom_iff_forall_pi`).
* Times form any preorder; the door's histories put the reference time at 1 and the interval just
  before it at 0.
* Each sufficient set for non-culmination is the only consistent situation over its variables
  (`nonCulmination_unique`), so each of its facts is necessary because no consistent situation
  over the same variables changes it. In the mechanical procedure every consistent situation over
  its variables that turns the handle back also engages the lock (`handle_alternatives_lock`), so
  the handle is necessary there only by way of a locked door.

## TODO

* The paper's repair for the realistic context of (40), which lets a sufficient set for
  non-culmination be undone by updating a fungible background variable, is left open, as it is in
  the paper.
* (38) and (39) list every sufficient set of the door, as the paper says. This is checked by
  evaluation over its 729 situations but not proved; a proof needs a characterization of the
  door's consistent situations.
* That `CausalModel.ForcedBy` agrees with strong Kleene evaluation on the door's and the circuit's
  equations, as footnote 30 requires, is unproved; it needs the knowledge order of `Trivalent`
  related to `Part Bool`.
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

A situation (28b) is a partial assignment of truth values, `V → Part Bool`, and its domain (28c)
is the set of variables `v` where `(s v).Dom`. -/

section Model

variable {U V : Type*} (M : CausalModel U V fun _ ↦ Bool)

/-- Causal consistency (29): every settled dependent variable has the value that what `s` settles
about its parents forces. -/
def Consistent (s : V → Part Bool) : Prop :=
  ∀ v, (∃ w, M.graph.Adj w v) → ∀ b : Bool, s v = Part.some b → M.ForcedBy (s · = Part.some ·) v b

/-- Causal necessity (30a): the fact `s` settles at `x` is necessary for the one it settles at
`y` when `x` is a causal ancestor of `y` and every consistent situation over the same variables
that changes `x` changes `y`. -/
def Necessary (s : V → Part Bool) (x y : V) : Prop :=
  Relation.TransGen M.graph.Adj x y ∧
    ∀ s', (∀ v, (s' v).Dom ↔ (s v).Dom) → Consistent M s' → s' x ≠ s x → s' y ≠ s y

/-- Causal sufficiency (30b): `s` is consistent, settles `y` at `b`, and each of its other facts
is necessary for that one. The kernel of `s` is then a sufficient set for ⟨y, b⟩. -/
def IsSufficient (s : V → Part Bool) (y : V) (b : Bool) : Prop :=
  Consistent M s ∧ s y = Part.some b ∧ ∀ x, (s x).Dom → x ≠ y → Necessary M s x y

/-! ### The progressive -/

section Progressive

variable {T : Type*} [Preorder T]

/-- Felicity (33a): the predicate has a culmination procedure, a sufficient set for its
culmination condition `c`. -/
def Felicitous (c : V) : Prop := ∃ S, IsSufficient M S c true

/-- INIT (36a): at time `t` the history `σ` settles some fact of a culmination procedure that it
did not settle throughout an interval just before `t`. -/
def Init (c : V) (σ : T → V → Part Bool) (t : T) : Prop :=
  ∃ S, IsSufficient M S c true ∧ ∃ v, ∃ b : Bool, S v = Part.some b ∧ σ t v = Part.some b ∧
    ∃ t' < t, ∀ t'' ∈ Set.Ico t' t, σ t'' v ≠ Part.some b

/-- CUL (36b-i): some culmination procedure is completely realized. -/
def Cul (c : V) (s : V → Part Bool) : Prop := ∃ S, IsSufficient M S c true ∧ S ≤ s

/-- TERM (36b-ii): some sufficient set for non-culmination is completely realized. -/
def Term (c : V) (s : V → Part Bool) : Prop := ∃ S, IsSufficient M S c false ∧ S ≤ s

/-- The progressive (35): initiated, and neither culminated nor terminated. -/
def Prog (c : V) (σ : T → V → Part Bool) (t : T) : Prop :=
  Init M c σ t ∧ ¬ (Cul M c (σ t) ∨ Term M c (σ t))

variable [DecidableEq V]

/-- A globally necessary condition (42): the fact ⟨v, b⟩ is globally necessary for `c` when its
negation together with non-culmination is a sufficient set for non-culmination. -/
def GloballyNecessary (c v : V) (b : Bool) : Prop :=
  IsSufficient M [c ← false, v ← !b] c false

/-- Definedness (45): the progressive is defined when every globally necessary condition is
settled at reference time. -/
def Defined (c : V) (s : V → Part Bool) : Prop :=
  ∀ v b, GloballyNecessary M c v b → (s v).Dom

end Progressive

variable {M}

/-- A sufficient set is a consistent situation over causal ancestors of its effect that is the only
consistent situation over its variables giving the effect its value. -/
theorem isSufficient_iff {s : V → Part Bool} {y : V} {b : Bool} :
    IsSufficient M s y b ↔ Consistent M s ∧ s y = Part.some b ∧
      (∀ x, (s x).Dom → x ≠ y → Relation.TransGen M.graph.Adj x y) ∧
        ∀ s', (∀ v, (s' v).Dom ↔ (s v).Dom) → Consistent M s' → s' y = s y → s' = s := by
  refine ⟨fun ⟨hc, hy, h⟩ ↦ ⟨hc, hy, fun x hx hxy ↦ (h x hx hxy).1,
    fun s' hd hc' hy' ↦ funext fun v ↦ ?_⟩, fun ⟨hc, hy, hanc, h⟩ ↦ ⟨hc, hy, fun x hx hxy ↦
      ⟨hanc x hx hxy, fun s' hd hc' hx' hy' ↦ hx' (congrFun (h s' hd hc' hy') x)⟩⟩⟩
  by_cases hv : (s v).Dom
  · rcases eq_or_ne v y with rfl | hvy
    · exact hy'
    · exact not_not.1 fun hne ↦ (h v hv hvy).2 s' hd hc' hne hy'
  · rw [Part.eq_bot_iff_not_dom.2 hv, Part.eq_bot_iff_not_dom.2 (mt (hd v).1 hv)]

theorem IsSufficient.eq_of_le {S s : V → Part Bool} {y : V} {b : Bool}
    (h : IsSufficient M S y b) (hle : S ≤ s) : s y = Part.some b :=
  Part.some_le_iff.1 (h.2.1 ▸ hle y)

theorem not_cul_or_term {c : V} {s : V → Part Bool} (h : s c = ⊥) :
    ¬ (Cul M c s ∨ Term M c s) := by
  rintro (⟨S, hS, hle⟩ | ⟨S, hS, hle⟩) <;> exact Part.some_ne_bot ((hS.eq_of_le hle).symm.trans h)

-- (36a): an unchanging history initiates nothing
theorem not_init_const {T : Type*} [Preorder T] {c : V} {s : V → Part Bool} {t : T} :
    ¬ Init M c (fun _ ↦ s) t := by
  rintro ⟨-, -, v, b, -, hs, t', ht', h⟩
  exact h t' ⟨le_rfl, ht'⟩ hs

variable [DecidableEq V]

/-- With its effect erased, a sufficient set forces the effect in the Kleene development, so it is
a sufficient set in the sense of Baglini and Bar-Asher Siegal. -/
theorem IsSufficient.isSufficientSet [M.IsAcyclic] {S : V → Part Bool} {y : V} {b : Bool}
    (h : IsSufficient M S y b) (hy : ∃ w, M.graph.Adj w y) :
    BarAsherSiegal2026.IsSufficientSet M (Function.update S y ⊥) y b := by
  refine ⟨Function.update_self .., forced_iff.2 (.inr ⟨Function.update_self .., ?_⟩)⟩
  refine (h.1 y hy b h.2.1).mono fun w hw z hz ↦ forced_iff.2 (.inl ?_)
  rwa [Function.update_of_ne (by rintro rfl; exact _root_.asymm hw hw)]

section Decidable

variable [Fintype V]

variable [Fintype U] [DecidableRel M.graph.Adj]

instance (s : V → Part Bool) [∀ v, Decidable (s v).Dom] : Decidable (Consistent M s) := by
  unfold Consistent; infer_instance

instance (s : V → Part Bool) [∀ v, Decidable (s v).Dom] (x y : V) :
    Decidable (Necessary M s x y) := by
  unfold Necessary; infer_instance

instance (s : V → Part Bool) [∀ v, Decidable (s v).Dom] (y : V) (b : Bool) :
    Decidable (IsSufficient M s y b) :=
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
abbrev s25b : V → Part Bool := [s₁ ← false, s₂ ← true, light ← false]

-- (25b), (29)
theorem consistent_25b : Consistent model s25b ∧
    ¬ Consistent model [s₁ ← false, s₂ ← true, light ← true] := by
  decide

-- the sufficient sets listed after (30), and the necessity of the first switch in (25b)
theorem not_isSufficient :
    ¬ Necessary model s25b s₁ light ∧
      ∀ S b, ¬ IsSufficient model S light b := by
  decide +kernel

-- the argument after (30), with the second switch held fixed
theorem light_changes_of_s₂_fixed :
    ∀ s', (∀ v, (s' v).Dom ↔ (s25b v).Dom) → Consistent model s' → s' s₁ ≠ s25b s₁ →
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
abbrev sMech : V → Part Bool := [handle ← true, lock ← false, doorOpens ← true]

/-- The electronic procedure (38b): door unlocked, power on, button pressed, circuit closed, door
open. -/
abbrev sElec : V → Part Bool :=
  [lock ← false, electricity ← true, button ← true, circuit ← true, doorOpens ← true]

/-- Non-culmination by the lock (39a). -/
abbrev sLock : V → Part Bool := [lock ← true, doorOpens ← false]

/-- Non-culmination with the handle unturned and no power (39b), with the effect fact. -/
abbrev sNotElec : V → Part Bool := [handle ← false, electricity ← false, doorOpens ← false]

/-- Non-culmination with the handle unturned and the button unpressed (39c), with the effect
fact. -/
abbrev sNotCirc : V → Part Bool :=
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
    ∀ S ∈ [sLock, sNotElec, sNotCirc], ∀ s', (∀ v, (s' v).Dom ↔ (S v).Dom) → Consistent model s' →
      s' = S := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro S (rfl | rfl | rfl) <;> decide +kernel

-- (38a)
theorem handle_alternatives_lock :
    ∀ s', (∀ v, (s' v).Dom ↔ (sMech v).Dom) → Consistent model s' → s' handle ≠ sMech handle →
      s' lock ≠ sMech lock := by
  decide +kernel

-- (33a)
theorem felicitous : Felicitous model doorOpens := ⟨sMech, sMech_sufficient⟩

-- footnote 39
theorem button_necessary :
    Necessary model sElec button circuit ∧ Necessary model sElec button doorOpens := by
  decide +kernel

-- the circuit's equation reads the button alone
theorem button_dom_of_circuit {s : V → Part Bool} (hs : Consistent model s)
    (hc : (s circuit).Dom) : (s button).Dom := by
  have hadj : ∀ w, model.graph.Adj w circuit → w = button := by decide
  obtain ⟨c, hc⟩ := Part.ne_bot_iff_exists.1 (mt Part.eq_bot_iff_not_dom.1 (not_not.2 hc))
  by_contra hb
  have hb : s button = ⊥ := Part.eq_bot_iff_not_dom.2 hb
  have := hs circuit ⟨button, by decide⟩ c hc default (fun _ ↦ !c) fun w hw z hz ↦ by
    obtain rfl := hadj w hw
    exact absurd (hb ▸ hz) Part.bot_ne_some
  simp [model] at this

/-- The two causal semantics agree on the mechanical route and part on the electronic one. The
electronic procedure without its effect is no minimal sufficient set of Baglini and Bar-Asher
Siegal, its button being redundant for forcing the door open, and their minimal set, which settles
the circuit without the button, is no procedure. -/
theorem electronic_differs :
    Function.update sMech doorOpens ⊥ = manual ∧
      ¬ IsMinimalSufficientSet model (Function.update sElec doorOpens ⊥) doorOpens true ∧
      ¬ IsSufficient model (Function.update automatic doorOpens (Part.some true)) doorOpens true :=
  ⟨by decide +kernel, by decide +kernel,
    fun h ↦ absurd (button_dom_of_circuit h.1 (by decide +kernel)) (by decide +kernel)⟩

/-- Before reference time the door is unlocked and the power off; at it, Nur has switched the
power on, leaving handle and button undetermined. -/
abbrev switchingOn (t : ℕ) : V → Part Bool := [lock ← false, electricity ← decide (0 < t)]

/-- The realistic context of (40): Nur switches the power on, having turned neither the handle
nor the button, so the door is closed. -/
abbrev realistic (t : ℕ) : V → Part Bool :=
  [handle ← false, lock ← false, electricity ← decide (0 < t), button ← false, circuit ← false,
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
theorem defined_iff {s : V → Part Bool} : Defined model doorOpens s ↔ (s lock).Dom :=
  ⟨fun hd ↦ hd lock false (globallyNecessary_iff.2 ⟨rfl, rfl⟩),
    fun h _ _ hv ↦ (globallyNecessary_iff.1 hv).1 ▸ h⟩

/-- With the lock's state unknown, Nur has turned the handle. -/
abbrev handleTurned (t : ℕ) : V → Part Bool := [handle ← decide (0 < t)]

-- (43a), row `basn2026_43a_handle`: the truth conditions hold, but the progressive is undefined
theorem prog_and_not_defined :
    Prog model doorOpens handleTurned 1 ∧ ¬ Defined model doorOpens (handleTurned 1) := by
  refine ⟨⟨⟨sMech, sMech_sufficient, handle, true, by decide, by decide, 0, zero_lt_one,
    fun t ht ↦ ?_⟩, not_cul_or_term (by decide)⟩, defined_iff.not.2 (by decide)⟩
  obtain rfl : t = 0 := Nat.lt_one_iff.1 ht.2
  decide

end Door

end BarAsherSiegalNadathur2026
