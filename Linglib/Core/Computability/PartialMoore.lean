module

public import Mathlib.Order.Basic
public import Mathlib.Data.Option.Basic
public import Mathlib.Data.List.Induction

/-!
# Partial Moore machines

A partial Moore machine has a state type `σ`, an input alphabet `α` and an output type `β`: a
partial transition `step : σ → α → Option σ` and an output `out : σ → β` at each state. From a
state `s` it reads a word as far as its transitions are defined, `M.evalFrom s x`, and a state is
reached from `s` when it reads some word to it, `M.Reaches s q`.

Two things are observed of a machine started at `s`: the output at the end of each word it reads
to the end, `M.output? s x`, and which pairs of words it reads to the same state,
`M.Nerode s x y`.

For outputs ordered by `≤`, the machine `M` at `s` is simulated by `N` at `t`,
`M.SimulatedBy N s t`, when a map of the states reached from `s` sends `s` to `t`, does not
decrease the output, and preserves each transition that is defined. A simulation exists exactly
when `N` reads every word `M` does to an output at least as great, and reads to one state every
two words that `M` does (`PartialMoore.simulatedBy_iff`).

## Implementation notes

The machine has no start state, so that one machine can be run from each of its states; a
machine with a start state all of whose states are reached is a pointed one. The state type may
be infinite. A total machine is the case in which no transition is `none`; mathlib's `DFA` has a
total transition function and no outputs.
-/

@[expose] public section

/-- A partial Moore machine: a partial transition on states for each input letter, and an output
at each state. -/
structure PartialMoore (σ α β : Type*) where
  /-- The state a letter leads to, if the transition is defined. -/
  step : σ → α → Option σ
  /-- The output at a state. -/
  out : σ → β

namespace PartialMoore

variable {σ τ υ α β : Type*} (M : PartialMoore σ α β) (N : PartialMoore τ α β)
  (P : PartialMoore υ α β) {s q q' : σ} {t : τ} {u : υ} {a : α} {x y : List α}

/-! ### Reading a word -/

/-- The state a word leads to from `s`, if every transition along it is defined. -/
def evalFrom (s : σ) (x : List α) : Option σ := x.foldlM M.step s

@[simp] theorem evalFrom_nil (s : σ) : M.evalFrom s [] = some s := rfl

@[simp] theorem evalFrom_cons (s : σ) (a : α) (x : List α) :
    M.evalFrom s (a :: x) = (M.step s a).bind (M.evalFrom · x) :=
  List.foldlM_cons

theorem evalFrom_append (s : σ) (x y : List α) :
    M.evalFrom s (x ++ y) = (M.evalFrom s x).bind (M.evalFrom · y) :=
  List.foldlM_append

theorem evalFrom_append_singleton (s : σ) (x : List α) (a : α) :
    M.evalFrom s (x ++ [a]) = (M.evalFrom s x).bind (M.step · a) := by
  rw [evalFrom_append]
  congr 1
  funext q
  cases h : M.step q a <;> simp [h]

/-- The state `q` is reached from `s` when some word leads from `s` to it. -/
def Reaches (s q : σ) : Prop := ∃ x, M.evalFrom s x = some q

theorem Reaches.refl (s : σ) : M.Reaches s s := ⟨[], rfl⟩

variable {M} in
theorem Reaches.step (h : M.Reaches s q) (ha : M.step q a = some q') : M.Reaches s q' :=
  let ⟨x, hx⟩ := h
  ⟨x ++ [a], by rw [evalFrom_append_singleton, hx]; exact ha⟩

/-- The output at the end of a word read from `s`, if the word is read to the end. -/
def output? (s : σ) (x : List α) : Option β := (M.evalFrom s x).map M.out

/-- Two words are read from `s` to the same state. -/
def Nerode (s : σ) (x y : List α) : Prop := ∃ q, M.evalFrom s x = some q ∧ M.evalFrom s y = some q

variable {M N} in
private theorem evalFrom_map {h : σ → τ}
    (hA : ∀ a q q', M.Reaches s q → M.step q a = some q' → N.step (h q) a = some (h q'))
    (x : List α) : ∀ {q : σ}, M.evalFrom s x = some q → N.evalFrom (h s) x = some (h q) := by
  induction x using List.reverseRecOn with
  | nil =>
    intro q hq
    obtain rfl : s = q := Option.some.inj hq
    rfl
  | append_singleton x a ih =>
    intro q' hq'
    rw [evalFrom_append_singleton] at hq' ⊢
    obtain ⟨q, hq, ha⟩ := Option.bind_eq_some_iff.1 hq'
    rw [ih hq]
    exact hA a q q' ⟨x, hq⟩ ha

variable {M N} in
private theorem reaches_map {h : σ → τ}
    (hA : ∀ a q q', M.Reaches s q → M.step q a = some q' → N.step (h q) a = some (h q'))
    (hq : M.Reaches s q) : N.Reaches (h s) (h q) :=
  let ⟨x, hx⟩ := hq; ⟨x, evalFrom_map hA x hx⟩

/-! ### Simulation -/

section Preorder

variable [Preorder β]

/-- The machine `M` at `s` is simulated by `N` at `t` when a map of the states reached from `s`
sends `s` to `t`, does not decrease the output, and preserves each defined transition. -/
def SimulatedBy (s : σ) (t : τ) : Prop :=
  ∃ h : σ → τ, h s = t ∧ (∀ q, M.Reaches s q → M.out q ≤ N.out (h q)) ∧
    ∀ a q q', M.Reaches s q → M.step q a = some q' → N.step (h q) a = some (h q')

variable {M N P}

theorem SimulatedBy.refl (M : PartialMoore σ α β) (s : σ) : M.SimulatedBy M s s :=
  ⟨id, rfl, fun _ _ ↦ le_rfl, fun _ _ _ _ h ↦ h⟩

theorem SimulatedBy.trans (h₁ : M.SimulatedBy N s t) (h₂ : N.SimulatedBy P t u) :
    M.SimulatedBy P s u := by
  obtain ⟨f, rfl, hO, hA⟩ := h₁
  obtain ⟨g, rfl, hO', hA'⟩ := h₂
  exact ⟨g ∘ f, rfl, fun q hq ↦ (hO q hq).trans (hO' _ (reaches_map hA hq)),
    fun a q q' hq ha ↦ hA' a _ _ (reaches_map hA hq) (hA a q q' hq ha)⟩

/-- A simulation exists exactly when the second machine reads every word the first does, to an
output at least as great, and reads to one state every two words that the first does. -/
theorem simulatedBy_iff : M.SimulatedBy N s t ↔
    (∀ x b, M.output? s x = some b → ∃ c, N.output? t x = some c ∧ b ≤ c) ∧
      ∀ x y, M.Nerode s x y → N.Nerode t x y := by
  constructor
  · rintro ⟨h, rfl, hO, hA⟩
    refine ⟨fun x b hb ↦ ?_,
      fun x y ⟨q, hx, hy⟩ ↦ ⟨h q, evalFrom_map hA x hx, evalFrom_map hA y hy⟩⟩
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hb
    exact ⟨N.out (h q), by simp [output?, evalFrom_map hA x hq], hO q ⟨x, hq⟩⟩
  · rintro ⟨hout, hner⟩
    classical
    have key : ∀ x q, M.evalFrom s x = some q → ∃ q', N.evalFrom t x = some q' ∧
        M.out q ≤ N.out q' := fun x q hq ↦ by
      obtain ⟨c, hc, hle⟩ := hout x (M.out q) (by simp [output?, hq])
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.1 hc
      exact ⟨q', hq', hle⟩
    let h : σ → τ := fun q ↦
      if hq : ∃ x, M.evalFrom s x = some q then (key _ q hq.choose_spec).choose else t
    have hh : ∀ x q, M.evalFrom s x = some q → N.evalFrom t x = some (h q) := by
      intro x q hq
      have hex : ∃ x, M.evalFrom s x = some q := ⟨x, hq⟩
      obtain ⟨q'', h₁, h₂⟩ := hner hex.choose x ⟨q, hex.choose_spec, hq⟩
      have h₃ := (key _ q hex.choose_spec).choose_spec.1
      simp only [h, hex, ↓reduceDIte]
      exact h₂.trans (h₁.symm.trans h₃)
    refine ⟨h, Option.some.inj ((hh [] s rfl).symm.trans rfl), fun q ⟨x, hx⟩ ↦ ?_,
      fun a q q' ⟨x, hx⟩ ha ↦ ?_⟩
    · obtain ⟨q', hq', hle⟩ := key x q hx
      rwa [Option.some.inj ((hh x q hx).symm.trans hq')]
    · have h₁ := hh (x ++ [a]) q' (by rw [evalFrom_append_singleton, hx]; exact ha)
      rwa [evalFrom_append_singleton, hh x q hx] at h₁

end Preorder

end PartialMoore
