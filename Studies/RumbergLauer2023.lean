module

public import Linglib.Semantics.Modality.BranchingTime
public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Core.Order.Minimals
public import Linglib.Core.Order.TreePath
public import Mathlib.Tactic.DeriveFintype

/-!
# Rumberg and Lauer (2023): What if, and when? Conditionals, tense, and branching time

An isolated present tense sentence can talk about the future only when the eventuality is
settled: the game the Red Sox play tomorrow is scheduled, their winning it is not. In the
antecedent of an indicative conditional the constraint disappears, the consequent can be read
at a later moment than the utterance ([crouch-1993]'s *if I smile when I get out, the
interview went well*), and a past tense antecedent never shifts this way. The paper
reconstructs the accounts of [kaufmann-2005-truth] and [schulz-2008] in branching time and
measures them, and its own proposal, against these facts.

Both rivals instantiate Kratzer's recipe, the conditional as a universal quantifier over a
domain of antecedent possibilities, which this file renders with the library's conditional
operators. Kaufmann's conditional is the strict conditional over the forward extension of
historical accessibility, with the antecedent settled (`kaufmannCond`); Schulz's is the
ordering conditional over the later moments, preferring the earliest by time (`schulzCond`).
Both can place the antecedent at a future moment, so both wrongly shift past tense
antecedents. The paper's own account uses the transition semantics of [rumberg-2016]: truth
is relative to a moment and a course of events, the future operator quantifies only over the
histories the course admits (`Transition.future`), and the conditional reads its consequent
at the first moment of decidedness of each minimal course making the antecedent true
(`Transition.cond`). At the actual past the future operator is settledness; a present
antecedent can be true relative to a longer course without being settled; and a past
antecedent's only minimal course is the actual past, so its consequent never shifts.

## Main statements

* `Transition.future_atom_self`, `Transition.present_atom_self`: at the actual past, future
  truth is settledness, so the isolated futurate present requires it.
* `Transition.future_atom_of_lt`: relative to a course leading to a witness, a future claim
  is true without being settled, which frees the antecedent.
* `Transition.cond_past_atom`: a past antecedent's consequent is read at the utterance
  moment, so past antecedents never shift.
* `Transition.cond_eq_orderingImp`: the paper's conditional is Kratzer's recipe over the
  extensions of the actual past, except that the consequent is read at the first moment of
  decidedness.
* `Transition.future_atom_subset_stable`: future truth persists under extensions of the
  course, the stability behind the covert necessity operator.
* `Game.settledness_contrast`, `Game.antecedent_true_without_settledness`: the Red Sox
  minimal pair.
* `Trains.schulz_validates_arrival_at_two`, `Trains.kaufmann_rejects_both_arrivals`,
  `Trains.transition_rejects_both_arrivals`: on the two-trains scenario Schulz's minimality
  wrongly validates the early arrival, while Kaufmann with a permissive context and the
  transition account reject both.
* `Interview.smile_conditional_shifts_consequent`: Crouch's shifted reading, with the
  consequent read after the interview.
* `Interview.rivals_shift_past_antecedents`, `Interview.no_shifted_antecedent_moment`: the
  rivals shift a past tense antecedent where the transition account cannot.

## Implementation notes

The paper's transition sets with a last transition are represented by their first moment of
decidedness, as licensed by its Definition 18, where extending a course is moving up the
order and the actual past at a moment is the moment itself; the identification of course
extension with the order relies on the existence of branching points, the connectedness the
paper imposes for this purpose. Kaufmann's contextual parameter is carried as a set of
moments, following the paper's note that it is in effect a property of times. The clock time
of a moment in the finite scenarios is its depth in the tree of Gorn addresses. Claims on the
finite models are decided through the reduction of histories to maximal moments.

## References

* [rumberg-lauer-2023]
* [rumberg-2016]
* [kaufmann-2005-truth]
* [schulz-2008]
* [crouch-1993]
* [prior-1967]
-/

@[expose] public section

namespace RumbergLauer2023

open BranchingTime Conditional Core.Order

variable {M : Type*} [PartialOrder M]

/-! ### The present tense as non-pastness

All three accounts read the morphological present as non-pastness: truth now or in the
future, with the future operator of the respective postsemantics. -/

/-- The present tense under the Peircean future holds now or in the settled future. -/
def peirceanPresent (φ : Set M) : Set M := φ ∪ Peircean.future φ

/-- The present tense under the Ockhamist future holds now or later on the history. -/
def ockhamistPresent (φ : Set (M × Flag M)) : Set (M × Flag M) := φ ∪ Ockhamist.future φ

@[simp] theorem mem_peirceanPresent {φ : Set M} {m : M} :
    m ∈ peirceanPresent φ ↔ m ∈ φ ∨ m ∈ Peircean.future φ := Iff.rfl

@[simp] theorem mem_ockhamistPresent {φ : Set (M × Flag M)} {p : M × Flag M} :
    p ∈ ockhamistPresent φ ↔ p ∈ φ ∨ p ∈ Ockhamist.future φ := Iff.rfl

instance {φ : Set M} [DecidablePred (· ∈ φ)] [DecidablePred (· ∈ Peircean.future φ)]
    (m : M) : Decidable (m ∈ peirceanPresent φ) :=
  inferInstanceAs (Decidable (m ∈ φ ∨ m ∈ Peircean.future φ))

theorem settled_ockhamistPresent_atom (φ : Set M) :
    Ockhamist.settled (ockhamistPresent (Ockhamist.atom φ)) =
      Ockhamist.atom (peirceanPresent φ) := by
  ext ⟨m, h⟩
  simp only [Ockhamist.mem_settled, mem_ockhamistPresent, Ockhamist.mem_atom,
    mem_peirceanPresent, mem_histories]
  constructor
  · intro H
    by_cases hp : m ∈ φ
    · exact .inl hp
    · exact .inr fun h' hh' ↦ (H h' hh').resolve_left hp
  · rintro (hp | hf) h' hh'
    exacts [.inl hp, .inr (hf h' hh')]

/-! ### Transition semantics

Truth is relative to a moment and a course of events, represented by the moment whose past
the course is: the actual past at `m` is the pair `(m, m)`, and extending the course is
moving up the order. The future operator quantifies over the histories through the moment
that the course admits. -/

namespace Transition

variable (φ : Set (M × M))

/-- A proposition of moments read relative to any course. -/
def atom (φ : Set M) : Set (M × M) := Prod.fst ⁻¹' φ

/-- The transition past of a proposition holds where it held at an earlier moment, relative
to the same course. -/
def past : Set (M × M) := {p | ∃ m' < p.1, (m', p.2) ∈ φ}

/-- The transition future of a proposition holds where every history through the moment that
the course admits has a later witness. -/
def future : Set (M × M) :=
  {p | ∀ h ∈ histories p.1 ∩ histories p.2, ∃ m' ∈ h, p.1 < m' ∧ (m', p.2) ∈ φ}

/-- A proposition is stable where it holds under every extension of the course compatible
with the moment. -/
def stable : Set (M × M) :=
  {p | ∀ n, p.2 ≤ n → (histories p.1 ∩ histories n).Nonempty → (p.1, n) ∈ φ}

/-- The present tense under the transition future holds now or in the future the course
admits. -/
def present : Set (M × M) := φ ∪ future φ

variable {φ} {m n : M}

omit [PartialOrder M] in
@[simp] theorem mem_atom {φ : Set M} : (m, n) ∈ atom φ ↔ m ∈ φ := Iff.rfl

@[simp] theorem mem_past : (m, n) ∈ past φ ↔ ∃ m' < m, (m', n) ∈ φ := Iff.rfl

@[simp] theorem mem_future :
    (m, n) ∈ future φ ↔ ∀ h ∈ histories m ∩ histories n, ∃ m' ∈ h, m < m' ∧ (m', n) ∈ φ := Iff.rfl

@[simp] theorem mem_stable :
    (m, n) ∈ stable φ ↔ ∀ n', n ≤ n' → (histories m ∩ histories n').Nonempty → (m, n') ∈ φ :=
  Iff.rfl

@[simp] theorem mem_present : (m, n) ∈ present φ ↔ (m, n) ∈ φ ∨ (m, n) ∈ future φ := Iff.rfl

theorem past_atom (φ : Set M) : past (atom φ) = atom (Peircean.past φ) := rfl

theorem future_atom_self (φ : Set M) (m : M) :
    (m, m) ∈ future (atom φ) ↔ m ∈ Peircean.future φ := by
  rw [mem_future, Set.inter_self]; exact Iff.rfl

theorem present_atom_self (φ : Set M) (m : M) :
    (m, m) ∈ present (atom φ) ↔ m ∈ peirceanPresent φ :=
  or_congr Iff.rfl (future_atom_self φ m)

theorem future_atom_of_lt {φ : Set M} (hmn : m < n) (hn : n ∈ φ) : (m, n) ∈ future (atom φ) :=
  fun _ ⟨_, hn'⟩ ↦ ⟨n, hn', hmn, hn⟩

section LeftLinear

variable [IsLeftLinear M]

theorem mem_of_mem_stable (hmn : m ≤ n ∨ n ≤ m) (h : (m, n) ∈ stable φ) : (m, n) ∈ φ :=
  h n le_rfl (histories_inter_nonempty_iff.2 hmn)

theorem future_atom_subset_stable (φ : Set M) :
    future (atom φ) ⊆ stable (future (atom φ)) :=
  fun _ H _n hn _ h ⟨hm, hh⟩ ↦ H h ⟨hm, Flag.Iic_subset hh hn⟩

theorem future_atom_ofIsMax {x : M} (hx : IsMax x) (hmx : m ≤ x) (φ : Set M) :
    (m, x) ∈ future (atom φ) ↔
      (m, Flag.ofIsMax hx) ∈ Ockhamist.future (Ockhamist.atom φ) := by
  simp only [mem_future, histories_eq_singleton hx, Set.mem_inter_iff, mem_histories,
    Set.mem_singleton_iff, Ockhamist.mem_future, Ockhamist.mem_atom, mem_atom]
  exact ⟨fun H ↦ H _ ⟨hmx, rfl⟩, fun H h ⟨_, hh⟩ ↦ hh ▸ H⟩

end LeftLinear

/-! ### The conditional

A conditional is true at the utterance moment when every minimal extension of the actual past
making the antecedent true makes the consequent true at its first moment of decidedness. -/

/-- The paper's predictive conditional in transition semantics. -/
def cond (A C : Set (M × M)) : Set M :=
  {m | ∀ n, Minimal (fun n ↦ m ≤ n ∧ (m, n) ∈ A) n → (n, n) ∈ C}

@[simp] theorem mem_cond {A C : Set (M × M)} {m : M} :
    m ∈ cond A C ↔ ∀ n, Minimal (fun n ↦ m ≤ n ∧ (m, n) ∈ A) n → (n, n) ∈ C := Iff.rfl

theorem minimal_eq_of_mem {A : Set (M × M)} (hA : (m, m) ∈ A)
    (h : Minimal (fun n ↦ m ≤ n ∧ (m, n) ∈ A) n) : n = m :=
  (h.2 ⟨le_rfl, hA⟩ h.1.1).antisymm h.1.1

theorem minimal_past_atom_iff {φ : Set M} :
    Minimal (fun n ↦ m ≤ n ∧ (m, n) ∈ past (atom φ)) n ↔ n = m ∧ m ∈ Peircean.past φ :=
  ⟨fun h ↦ ⟨minimal_eq_of_mem h.1.2 h, h.1.2⟩, by
    rintro ⟨rfl, hA⟩
    exact ⟨⟨le_rfl, hA⟩, fun _ h _ ↦ h.1⟩⟩

theorem cond_past_atom (φ : Set M) (C : Set (M × M)) :
    cond (past (atom φ)) C = {m | m ∈ Peircean.past φ → (m, m) ∈ C} := by
  ext m
  simp only [mem_cond, minimal_past_atom_iff, Set.mem_ofPred_eq]
  exact ⟨fun h hA ↦ h m ⟨rfl, hA⟩, fun h n ⟨hn, hA⟩ ↦ hn ▸ h hA⟩

theorem cond_eq_orderingImp (A C : Set (M × M)) :
    cond A C = orderingImp (fun m ↦ {m} ×ˢ Set.Ici m) (fun _ ↦ Preorder.lift Prod.snd) A
      ((fun p : M × M ↦ (p.2, p.2)) ⁻¹' C) := by
  ext m
  simp only [mem_cond, mem_orderingImp, Set.subset_def, Preorder.mem_minimals_iff,
    Set.mem_inter_iff, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Ici, Set.mem_preimage,
    Preorder.lift_le_iff, and_imp, Prod.forall]
  constructor
  · rintro H m' n rfl hmn hA hmin
    exact H n ⟨⟨hmn, hA⟩, fun n' hn' hle ↦ hmin _ n' rfl hn'.1 hn'.2 hle⟩
  · rintro H n ⟨⟨hmn, hA⟩, hmin⟩
    exact H _ n rfl hmn hA fun _ n' h hmn' hA' hle ↦ hmin ⟨hmn', h ▸ hA'⟩ hle

/-! ### Decidability on finite frames -/

theorem mem_future_atom_iff [IsLeftLinear M] [Finite M] {φ : Set M} :
    (m, n) ∈ future (atom φ) ↔
      ∀ x, IsMax x → m ≤ x → n ≤ x → ∃ m', m < m' ∧ m' ≤ x ∧ m' ∈ φ := by
  have : Nonempty M := ⟨m⟩
  have h1 : (m, n) ∈ future (atom φ) ↔
      ∀ h : Flag M, m ∈ h → n ∈ h → ∃ m' ∈ h, m < m' ∧ m' ∈ φ := by
    simp only [mem_future, Set.mem_inter_iff, mem_histories, and_imp, mem_atom]
  rw [h1, Flag.forall_mem_iff]
  exact forall_congr' fun x ↦ forall_congr' fun hx ↦ imp_congr_right fun _ ↦
    imp_congr Flag.mem_ofIsMax <| exists_congr fun m' ↦
      ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h2, h1, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨h2, h1, h3⟩⟩

section Decidable

variable [IsLeftLinear M] [Fintype M] [DecidableEq M] [DecidableLE M] [DecidableLT M]

instance (φ : Set M) [DecidablePred (· ∈ φ)] (p : M × M) :
    Decidable (p ∈ future (atom φ)) :=
  decidable_of_iff _ mem_future_atom_iff.symm

instance (φ : Set M) [DecidablePred (· ∈ φ)] (p : M × M) : Decidable (p ∈ atom φ) :=
  inferInstanceAs (Decidable (p.1 ∈ φ))

instance (φ : Set M) [DecidablePred (· ∈ φ)] (p : M × M) : Decidable (p ∈ past (atom φ)) :=
  inferInstanceAs (Decidable (∃ m' < p.1, m' ∈ φ))

instance (φ : Set (M × M)) [DecidablePred (· ∈ φ)] [DecidablePred (· ∈ future φ)]
    (p : M × M) : Decidable (p ∈ present φ) :=
  inferInstanceAs (Decidable (p ∈ φ ∨ p ∈ future φ))

instance (A C : Set (M × M)) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ C)] (m : M) :
    Decidable (m ∈ cond A C) :=
  inferInstanceAs (Decidable (∀ n, (m ≤ n ∧ (m, n) ∈ A) ∧
    (∀ y, (m ≤ y ∧ (m, y) ∈ A) → y ≤ n → n ≤ y) → (n, n) ∈ C))

end Decidable

end Transition

/-! ### Kaufmann's conditional in branching time

The semantics of *if* forwards the historical accessibility relation: the relevant indices
are the later ones the contextual parameter admits, the antecedent is settled there by its
covert necessity operator, and the consequent is read at those indices. -/

/-- The forward extension of historical accessibility, restricted by the contextual
parameter, reaches the Ockhamist indices at or after the moment whose own moment the
parameter admits. -/
def forwardBase (e : Set M) (m : M) : Set (M × Flag M) :=
  {p | m ≤ p.1 ∧ p.1 ∈ p.2 ∧ p.1 ∈ e}

@[simp] theorem mem_forwardBase {e : Set M} {m m' : M} {h : Flag M} :
    (m', h) ∈ forwardBase e m ↔ m ≤ m' ∧ m' ∈ h ∧ m' ∈ e := Iff.rfl

/-- Kaufmann's conditional reconstructed in Ockhamist branching time holds when the
consequent holds at every later index the context admits at which the antecedent is settled.
Only the moment of evaluation matters, since no context fixes the history parameter. -/
def kaufmannCond (e : Set M) (A C : Set (M × Flag M)) : Set M :=
  strictImp (forwardBase e) (Ockhamist.settled A) C

theorem mem_kaufmannCond {e : Set M} {A C : Set (M × Flag M)} {m : M} :
    m ∈ kaufmannCond e A C ↔ ∀ (m' : M) (h : Flag M), m ≤ m' → m' ∈ h → m' ∈ e →
      (m', h) ∈ Ockhamist.settled A → (m', h) ∈ C := by
  simp only [kaufmannCond, mem_strictImp_forall, Prod.forall, mem_forwardBase, and_imp]

theorem mem_kaufmannCond_past_atom {e : Set M} {φ : Set M} {C : Set (M × Flag M)} {m : M} :
    m ∈ kaufmannCond e (Ockhamist.past (Ockhamist.atom φ)) C ↔
      ∀ (m' : M) (h : Flag M), m ≤ m' → m' ∈ h → m' ∈ e → m' ∈ Peircean.past φ →
        (m', h) ∈ C := by
  simp only [mem_kaufmannCond, Ockhamist.settled_past_atom, Ockhamist.mem_atom]

theorem mem_kaufmannCond_present_iff [IsLeftLinear M] [Finite M] {e : Set M} {φ ψ : Set M}
    {m : M} :
    m ∈ kaufmannCond e (ockhamistPresent (Ockhamist.atom φ))
        (ockhamistPresent (Ockhamist.atom ψ)) ↔
      ∀ m', m ≤ m' → m' ∈ e → m' ∈ peirceanPresent φ → ∀ x, IsMax x → m' ≤ x →
        (m' ∈ ψ ∨ ∃ m'' ≤ x, m' < m'' ∧ m'' ∈ ψ) := by
  have : Nonempty M := ⟨m⟩
  simp only [mem_kaufmannCond, settled_ockhamistPresent_atom, Ockhamist.mem_atom,
    mem_ockhamistPresent, Ockhamist.mem_future]
  constructor
  · intro H m' hm' he hφ x hx hm'x
    simpa only [Ockhamist.mem_atom, Ockhamist.mem_future, Flag.mem_ofIsMax] using
      H m' (Flag.ofIsMax hx) hm' hm'x he hφ
  · intro H m' h hm' hm'h he hφ
    obtain ⟨x, hx, rfl⟩ := Flag.exists_isMax_eq_ofIsMax h
    simpa only [Ockhamist.mem_atom, Ockhamist.mem_future, Flag.mem_ofIsMax] using
      H m' hm' he hφ x hx hm'h

/-! ### Schulz's conditional in branching time

The modal base is the set of later moments, the ordering prefers the earliest by time, and
the conditional quantifies over the minimal antecedent moments: the library's ordering
conditional under the pullback of the time projection. -/

/-- Schulz's conditional reconstructed in Peircean branching time. -/
def schulzCond {T : Type*} [LinearOrder T] (time : M → T) (A C : Set M) : Set M :=
  orderingImp Set.Ici (fun _ ↦ Preorder.lift time) A C

theorem mem_schulzCond_iff {T : Type*} [LinearOrder T] {time : M → T} {A C : Set M} {m : M} :
    m ∈ schulzCond time A C ↔
      ∀ m', m ≤ m' → m' ∈ A →
        (∀ m'', m ≤ m'' → m'' ∈ A → time m'' ≤ time m' → time m' ≤ time m'') → m' ∈ C := by
  simp only [schulzCond, mem_orderingImp, Set.subset_def, Preorder.mem_minimals_iff,
    Set.mem_inter_iff, Set.mem_Ici, Preorder.lift_le_iff, and_imp]

instance {T : Type*} [LinearOrder T] (time : M → T) (A C : Set M) [Fintype M] [DecidableLE M]
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ C)] (m : M) :
    Decidable (m ∈ schulzCond time A C) :=
  decidable_of_iff _ mem_schulzCond_iff.symm

omit [PartialOrder M] in
theorem time_eq_of_mem_minimals {T : Type*} [LinearOrder T] {time : M → T} {s : Set M}
    {a b : M} (ha : a ∈ (Preorder.lift time).minimals s)
    (hb : b ∈ (Preorder.lift time).minimals s) : time a = time b :=
  (le_total (time a) (time b)).elim (fun h ↦ le_antisymm h (hb.2 ha.1 h))
    fun h ↦ le_antisymm (ha.2 hb.1 h) h

/-! ### The game

*The Red Sox play the Yankees tomorrow* is felicitous because the game is scheduled; *#the
Red Sox beat the Yankees tomorrow* is odd because the outcome is open. -/

/-- The utterance moment, branching into the two outcomes of the game. -/
inductive Game | now | win | lose
  deriving DecidableEq, Fintype, Repr

namespace Game

/-- The tree of the scenario, by Gorn address. -/
def addr : Game → TreePath
  | now => ⟨[]⟩
  | win => ⟨[0]⟩
  | lose => ⟨[1]⟩

theorem addr_injective : Function.Injective addr := by decide

instance : PartialOrder Game := PartialOrder.lift addr addr_injective
instance : DecidableLE Game := fun a b ↦ inferInstanceAs (Decidable (addr a ≤ addr b))
instance : DecidableLT Game := decidableLTOfDecidableLE
instance : IsLeftLinear Game :=
  (OrderEmbedding.ofMapLEIff addr fun _ _ ↦ Iff.rfl).isLeftLinear

/-- *The Red Sox play the Yankees* holds at both outcomes. -/
def played : Set Game := {win, lose}

/-- *The Red Sox beat the Yankees* holds at the winning outcome. -/
def beat : Set Game := {win}

instance : DecidablePred (· ∈ played) :=
  fun m ↦ inferInstanceAs (Decidable (m = win ∨ m = lose))
instance : DecidablePred (· ∈ beat) := fun m ↦ inferInstanceAs (Decidable (m = win))

theorem settledness_contrast :
    now ∈ Peircean.future played ∧ now ∉ Peircean.future beat := by decide

theorem antecedent_true_without_settledness :
    (now, win) ∈ Transition.present (Transition.atom beat) ∧ now ∉ peirceanPresent beat := by
  decide

theorem future_truth_without_settledness :
    (now, Flag.ofIsMax (x := win) (by decide)) ∈ Ockhamist.future (Ockhamist.atom beat) ∧
      now ∉ Peircean.future beat :=
  ⟨(Transition.future_atom_ofIsMax (by decide) (by decide) beat).1 (by decide),
    settledness_contrast.2⟩

end Game

/-! ### The two trains

John decides at short notice whether to take the one o'clock train and arrive at two; if not,
he decides later whether to take the two o'clock train and arrive at three, or stay.
Intuitively both *if John comes today, he arrives at two* and *if John comes today, he
arrives at three* are false. -/

/-- The moments of the two-trains scenario. -/
inductive Trains | now | early | arriveTwo | wait | late | arriveThree | stay
  deriving DecidableEq, Fintype, Repr

namespace Trains

/-- The tree of the scenario, by Gorn address. The early decision leads to the two o'clock
arrival; waiting leads to the late decision, and then to the three o'clock arrival or to
staying. -/
def addr : Trains → TreePath
  | now => ⟨[]⟩
  | early => ⟨[0]⟩
  | arriveTwo => ⟨[0, 0]⟩
  | wait => ⟨[1]⟩
  | late => ⟨[1, 0]⟩
  | arriveThree => ⟨[1, 0, 0]⟩
  | stay => ⟨[1, 1]⟩

theorem addr_injective : Function.Injective addr := by decide

instance : PartialOrder Trains := PartialOrder.lift addr addr_injective
instance : DecidableLE Trains := fun a b ↦ inferInstanceAs (Decidable (addr a ≤ addr b))
instance : DecidableLT Trains := decidableLTOfDecidableLE
instance : IsLeftLinear Trains :=
  (OrderEmbedding.ofMapLEIff addr fun _ _ ↦ Iff.rfl).isLeftLinear

/-- The clock time of a moment is its depth in the tree, with the decisions at one and two
and the arrivals at two and three. -/
def time (m : Trains) : ℕ := (addr m).toList.length

/-- *John comes to Konstanz today* holds on arrival. -/
def come : Set Trains := {arriveTwo, arriveThree}

/-- *John arrives at two*. -/
def atTwo : Set Trains := {arriveTwo}

/-- *John arrives at three*. -/
def atThree : Set Trains := {arriveThree}

instance : DecidablePred (· ∈ come) :=
  fun m ↦ inferInstanceAs (Decidable (m = arriveTwo ∨ m = arriveThree))
instance : DecidablePred (· ∈ atTwo) := fun m ↦ inferInstanceAs (Decidable (m = arriveTwo))
instance : DecidablePred (· ∈ atThree) :=
  fun m ↦ inferInstanceAs (Decidable (m = arriveThree))

theorem schulz_ignores_the_late_decision :
    early ∈ (Preorder.lift time).minimals {m' | now ≤ m' ∧ m' ∈ peirceanPresent come} ∧
      late ∉ (Preorder.lift time).minimals {m' | now ≤ m' ∧ m' ∈ peirceanPresent come} ∧
      now ≤ late ∧ late ∈ peirceanPresent come := by
  decide

theorem schulz_validates_arrival_at_two :
    now ∈ schulzCond time (peirceanPresent come) (peirceanPresent atTwo) := by decide

theorem kaufmann_rejects_both_arrivals :
    now ∉ kaufmannCond Set.univ (ockhamistPresent (Ockhamist.atom come))
        (ockhamistPresent (Ockhamist.atom atTwo)) ∧
      now ∉ kaufmannCond Set.univ (ockhamistPresent (Ockhamist.atom come))
        (ockhamistPresent (Ockhamist.atom atThree)) := by
  simp only [mem_kaufmannCond_present_iff, Set.mem_univ, true_implies]
  constructor <;> decide

theorem transition_rejects_both_arrivals :
    now ∉ Transition.cond (Transition.present (Transition.atom come))
        (Transition.present (Transition.atom atTwo)) ∧
      now ∉ Transition.cond (Transition.present (Transition.atom come))
        (Transition.present (Transition.atom atThree)) := by
  decide

theorem decidedness_at_different_times :
    Minimal (fun n ↦ now ≤ n ∧ (now, n) ∈ Transition.present (Transition.atom come)) early ∧
      Minimal (fun n ↦ now ≤ n ∧ (now, n) ∈ Transition.present (Transition.atom come)) late ∧
      time early ≠ time late := by
  decide

end Trains

/-! ### The interview

Before tomorrow's job interview, *if I smile when I get out, the interview went well* has a
shifted past-in-the-future consequent, while *#if the interview went well, John gets the job*
cannot read its past antecedent in the future. -/

/-- The moments of the interview scenario. The interview starts, goes well or badly, and
after a good interview the speaker leaves smiling or not. -/
inductive Interview | now | start | good | bad | smile | frown
  deriving DecidableEq, Fintype, Repr

namespace Interview

/-- The tree of the scenario, by Gorn address. -/
def addr : Interview → TreePath
  | now => ⟨[]⟩
  | start => ⟨[0]⟩
  | good => ⟨[0, 0]⟩
  | bad => ⟨[0, 1]⟩
  | smile => ⟨[0, 0, 0]⟩
  | frown => ⟨[0, 0, 1]⟩

theorem addr_injective : Function.Injective addr := by decide

instance : PartialOrder Interview := PartialOrder.lift addr addr_injective
instance : DecidableLE Interview := fun a b ↦ inferInstanceAs (Decidable (addr a ≤ addr b))
instance : DecidableLT Interview := decidableLTOfDecidableLE
instance : IsLeftLinear Interview :=
  (OrderEmbedding.ofMapLEIff addr fun _ _ ↦ Iff.rfl).isLeftLinear

/-- The clock time of a moment, its depth in the tree. -/
def time (m : Interview) : ℕ := (addr m).toList.length

/-- *The interview went well*. -/
def wentWell : Set Interview := {good}

/-- *The interview went badly*. -/
def wentBadly : Set Interview := {bad}

/-- *I smile when I get out*. -/
def smiles : Set Interview := {smile}

/-- *John gets the job* is settled once a good interview is over. -/
def getsJob : Set Interview := {smile, frown}

instance : DecidablePred (· ∈ wentWell) := fun m ↦ inferInstanceAs (Decidable (m = good))
instance : DecidablePred (· ∈ wentBadly) := fun m ↦ inferInstanceAs (Decidable (m = bad))
instance : DecidablePred (· ∈ smiles) := fun m ↦ inferInstanceAs (Decidable (m = smile))
instance : DecidablePred (· ∈ getsJob) :=
  fun m ↦ inferInstanceAs (Decidable (m = smile ∨ m = frown))

theorem smile_conditional_shifts_consequent :
    now ∈ Transition.cond (Transition.present (Transition.atom smiles))
        (Transition.past (Transition.atom wentWell)) ∧
      now ∉ Transition.cond (Transition.present (Transition.atom smiles))
        (Transition.past (Transition.atom wentBadly)) ∧
      Minimal (fun n ↦ now ≤ n ∧ (now, n) ∈ Transition.present (Transition.atom smiles))
        smile ∧
      now < smile := by
  decide

theorem rivals_shift_past_antecedents :
    now ∉ Peircean.past wentWell ∧
      now ∈ schulzCond time (Peircean.past wentWell) (peirceanPresent getsJob) ∧
      now ∈ kaufmannCond Set.univ (Ockhamist.past (Ockhamist.atom wentWell))
        (ockhamistPresent (Ockhamist.atom getsJob)) := by
  refine ⟨by decide, by decide, mem_kaufmannCond_past_atom.2 fun m' h _ _ _ hpast ↦
    Set.mem_union_left _ ?_⟩
  have : ∀ m' : Interview, m' ∈ Peircean.past wentWell → m' ∈ getsJob := by decide
  exact this m' hpast

theorem no_shifted_antecedent_moment :
    ∀ n, ¬ Minimal
      (fun n ↦ now ≤ n ∧ (now, n) ∈ Transition.past (Transition.atom wentWell)) n := by
  decide

end Interview

end RumbergLauer2023
