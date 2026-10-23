/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.Subsequential`.
-/
module

public import Mathlib.Computability.NFA
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Lattice.Fold
public import Linglib.Core.Computability.Mealy
public import Linglib.Core.Computability.Edge
public import Linglib.Core.Data.Fintype.List
public import Linglib.Core.Data.List.DropRight

/-!
# Subsequential functions and finite-state transducers

A subsequential transducer, in the sense of Schützenberger and Mohri, is a sequential
transducer together with a final block of output determined by the ending state. A sequential
transducer is a deterministic state machine emitting a block of output for each input symbol,
which is a `Mealy` machine over the output alphabet `List β`. The functions so computed,
*subsequential* with left- and right-scan variants, form a proper subclass of the rational
functions.

We show that each class is closed under composition, that the two are isomorphic under
reverse-conjugation, that both contain the Mealy-computable functions, and that
left-subsequential functions pull back regular languages; a subsequential function
withholds at most a bounded stretch of output (`bounded_delay`).

Like `DFA`, this definition allows for machines with infinite states; the
classification predicates require a `Fintype` instance.

## Main definitions

* `SubsequentialTransducer σ α β`: transducer over alphabets `α`, `β` and states `σ`
* `SubsequentialTransducer.run` / `SubsequentialTransducer.runRight`: the two passes
* `SubsequentialTransducer.comp`: the machine computing the composite function
* `SubsequentialTransducer.ofWindow`: the sliding-window transducer
* `DFA.comapSubsequential`: pulls an acceptor back along a transducer
* `IsLeftSubsequential f`, `IsRightSubsequential f`, `IsSubsequential d f`: some
  finite-state transducer computes `f` in the given scan direction

## Main theorems

* `IsLeftSubsequential.comp`, `IsRightSubsequential.comp`: closure under composition
* `IsMealyComputable.isLeftSubsequential`: Mealy-computable functions are
  left-subsequential
* `IsLeftSubsequential.isRegular_preimage`, `IsRightSubsequential.isRegular_preimage`:
  subsequential functions pull back regular languages
* `IsLeftSubsequential.bounded_delay`, `IsRightSubsequential.bounded_delay`: all but
  boundedly many symbols of `f u` survive extending the input on the far side

## Implementation notes

The name follows Choffrut and Mohri: *sequential* without state-final output,
*subsequential* with. Sakarovitch calls this class *sequential* (and the empty-flush case
*pure sequential*), flagging his usage as unconventional (compare Bruyère and Reutenauer); we
keep the Choffrut spelling. `Mealy` is the letter-to-letter case.

`step` is total, so only the *total* subsequential functions are modelled, since a sink state
does not recover partiality, and Sakarovitch's initial-output function is omitted. The state run
`evalFrom` and its lemmas are those of the underlying `Mealy` machine. There are two disjoint
sets of simp lemmas, one for `run` and another for `runFrom`; switch from the former to the
latter via `simp [run]`.

## TODO

* Choffrut's theorem: a rational function is subsequential iff it has
  bounded variation, decidably via twinning; `bounded_delay` is far weaker.
* Canonical forms and minimization; two-way transducers; p-subsequential functions.

## References

* [schutzenberger-1977]
* [choffrut-1977]
* [mohri-1997]
* [bruyere-reutenauer-1999]
* [sakarovitch-2009]
* [filiot-reynier-2016]
-/

@[expose] public section

variable {σ α β : Type*}

/-- A subsequential finite-state transducer is a sequential transducer — a `Mealy`
machine whose `output` is the block of symbols emitted on reading an input symbol in a
state — together with a state-final output (`finalOutput`). -/
@[ext]
structure SubsequentialTransducer (σ α β : Type*) extends Mealy σ α (List β) where
  /-- `finalOutput s` is the block emitted on terminating in the state `s`. -/
  finalOutput : σ → List β

instance [Inhabited σ] : Inhabited (SubsequentialTransducer σ α β) :=
  ⟨⟨default, fun _ ↦ []⟩⟩

namespace SubsequentialTransducer

variable (T : SubsequentialTransducer σ α β)

/-- `T.emitted s x` is the output emitted while consuming the input `x` from the
state `s` without the final flush, the concatenated blocks of the sequential run. -/
def emitted (s : σ) (xs : List α) : List β := (T.toMealy.runFrom s xs).flatten

/-- `T.runFrom s x` runs `T` on the input `x` from the state `s`, emitting the output followed
by the final flush. -/
def runFrom (s : σ) (xs : List α) : List β :=
  T.emitted s xs ++ T.finalOutput (T.evalFrom s xs)

/-- `T.run x` runs `T` on the input `x` from the state `T.start`. -/
def run : List α → List β := T.runFrom T.start

/-- `T.runRight x` runs `T` right-to-left on the input `x`. -/
def runRight (xs : List α) : List β := (T.run xs.reverse).reverse

theorem runRight_eq_revConj_run : T.runRight = List.revConj T.run := rfl

section
variable (s : σ) (x : α) (xs ys : List α)

@[simp] theorem emitted_nil : T.emitted s [] = [] := rfl
@[simp] theorem emitted_cons :
    T.emitted s (x :: xs) = T.output s x ++ T.emitted (T.step s x) xs := rfl

@[simp] theorem runFrom_nil : T.runFrom s [] = T.finalOutput s := rfl

@[simp] theorem runFrom_cons :
    T.runFrom s (x :: xs) = T.output s x ++ T.runFrom (T.step s x) xs := by
  simp [runFrom]

@[simp] theorem run_nil : T.run [] = T.finalOutput T.start := rfl

@[simp] theorem runRight_nil : T.runRight [] = (T.finalOutput T.start).reverse := rfl

@[simp] theorem runRight_reverse : T.runRight xs.reverse = (T.run xs).reverse := by
  simp [runRight]

theorem emitted_append :
    T.emitted s (xs ++ ys) = T.emitted s xs ++ T.emitted (T.evalFrom s xs) ys := by
  simp [emitted, Mealy.runFrom_append]

theorem runFrom_append :
    T.runFrom s (xs ++ ys) = T.emitted s xs ++ T.runFrom (T.evalFrom s xs) ys := by
  simp [runFrom, emitted_append, Mealy.evalFrom_append]

theorem run_append :
    T.run (xs ++ ys) = T.emitted T.start xs ++ T.runFrom (T.eval xs) ys :=
  T.runFrom_append T.start xs ys

end

/-! ### Transport along state equivalences -/

variable {τ : Type*}

/-- Transport a transducer along an equivalence on states. -/
@[simps toMealy finalOutput]
def map (g : σ ≃ τ) (T : SubsequentialTransducer σ α β) : SubsequentialTransducer τ α β where
  toMealy := T.toMealy.map g
  finalOutput t := T.finalOutput (g.symm t)

@[simp] theorem map_refl : map (Equiv.refl σ) T = T := rfl

@[simp] theorem map_map {υ : Type*} (g : σ ≃ τ) (h : τ ≃ υ) :
    map h (map g T) = map (g.trans h) T := rfl

@[simp] theorem emitted_map (g : σ ≃ τ) (t : τ) (xs : List α) :
    (map g T).emitted t xs = T.emitted (g.symm t) xs := by
  simp [emitted]

@[simp] theorem runFrom_map (g : σ ≃ τ) (t : τ) (xs : List α) :
    (map g T).runFrom t xs = T.runFrom (g.symm t) xs := by
  simp [runFrom]

@[simp] theorem run_map (g : σ ≃ τ) : (map g T).run = T.run := by
  funext xs; simp [run]

@[simp] theorem runRight_map (g : σ ≃ τ) : (map g T).runRight = T.runRight := by
  funext xs; simp [runRight]

/-! ### Composition -/

section Comp

variable {γ σ' : Type*} (T₂ : SubsequentialTransducer σ' β γ) (T₁ : SubsequentialTransducer σ α β)

/-- `T₂.comp T₁` feeds each output block of `T₁` to `T₂`, computing `T₂.run ∘ T₁.run`, which
is the construction behind the closure of the subsequential functions under composition
[mohri-1997]. -/
@[simps]
def comp : SubsequentialTransducer (σ' × σ) α γ where
  start := (T₂.start, T₁.start)
  step p x := (T₂.evalFrom p.1 (T₁.output p.2 x), T₁.step p.2 x)
  output p x := T₂.emitted p.1 (T₁.output p.2 x)
  finalOutput p := T₂.runFrom p.1 (T₁.finalOutput p.2)

@[simp] theorem runFrom_comp (p : σ' × σ) (xs : List α) :
    (T₂.comp T₁).runFrom p xs = T₂.runFrom p.1 (T₁.runFrom p.2 xs) := by
  induction xs generalizing p with
  | nil => simp
  | cons x xs ih => simp [ih, runFrom_append]

@[simp] theorem run_comp : (T₂.comp T₁).run = T₂.run ∘ T₁.run := by
  funext xs; simp [run, Function.comp]

end Comp

/-! ### Pulling back acceptors -/

section ComapSubsequential

variable {τ : Type*} (M : DFA β τ)

/-- `M.comapSubsequential T` pulls the acceptor `M` back along the transducer `T`. The
product machine runs `T`, feeds each output block to `M`, and accepts in a state from which `M`
accepts the final flush, so it accepts `x` if and only if `M` accepts `T.run x`. -/
@[simps]
def _root_.DFA.comapSubsequential : DFA α (σ × τ) where
  step p a := (T.step p.1 a, M.evalFrom p.2 (T.output p.1 a))
  start := (T.start, M.start)
  accept := {p | M.evalFrom p.2 (T.finalOutput p.1) ∈ M.accept}

@[simp] theorem _root_.DFA.evalFrom_comapSubsequential (p : σ × τ) (xs : List α) :
    (M.comapSubsequential T).evalFrom p xs
      = (T.evalFrom p.1 xs, M.evalFrom p.2 (T.emitted p.1 xs)) := by
  induction xs generalizing p <;> simp [DFA.evalFrom_of_append, *]

@[simp] theorem _root_.DFA.accepts_comapSubsequential :
    (M.comapSubsequential T).accepts = T.run ⁻¹' M.accepts := by
  ext xs
  rw [Set.mem_preimage, DFA.mem_accepts, DFA.mem_accepts]
  simp [DFA.eval, run, runFrom, DFA.evalFrom_of_append]

end ComapSubsequential

/-! ### Window transducers -/

section OfWindow

variable {γ : Type*}

/-- The transducer whose state is a window of the last `n` accumulated symbols. `out`
emits from the window and the current symbol, and `upd` chooses what the window accumulates
(`fun _ x ↦ [x]` for the input, `out` for the output). -/
@[simps]
def ofWindow (n : ℕ) (out : List γ → α → List β) (upd : List γ → α → List γ) :
    SubsequentialTransducer {l : List γ // l.length ≤ n} α β where
  start := ⟨[], Nat.zero_le _⟩
  step w x := ⟨(w.val ++ upd w.val x).rtake n, List.length_rtake_le _ _⟩
  output w x := out w.val x
  finalOutput _ := []

/-- The window recursion computed by `ofWindow`, each step of which emits `out` and extends the
window by `upd`, truncated to length `n`. -/
def windowRun (n : ℕ) (out : List γ → α → List β) (upd : List γ → α → List γ) :
    List γ → List α → List β
  | _, [] => []
  | w, x :: xs => out w x ++ windowRun n out upd ((w ++ upd w x).rtake n) xs

variable {n : ℕ} {out : List γ → α → List β} {upd : List γ → α → List γ}

theorem runFrom_ofWindow (w : {l : List γ // l.length ≤ n}) (xs : List α) :
    (ofWindow n out upd).runFrom w xs = windowRun n out upd w.val xs := by
  induction xs generalizing w with
  | nil => simp [windowRun]
  | cons x xs ih => rw [runFrom_cons, windowRun]; exact congrArg _ (ih _)

theorem run_ofWindow : (ofWindow n out upd).run = windowRun n out upd [] :=
  funext fun xs ↦ runFrom_ofWindow ⟨[], Nat.zero_le _⟩ xs

theorem windowRun_append_singleton {w : List γ} (hw : w.length ≤ n) (u : List α) (x : α) :
    windowRun n out upd w (u ++ [x]) =
      windowRun n out upd w u ++ out ((w ++ windowRun n upd upd w u).rtake n) x := by
  induction u generalizing w with
  | nil => simp [windowRun, List.rtake_of_length_le hw]
  | cons y ys ih =>
    simp only [List.cons_append, windowRun, List.append_assoc, ih (List.length_rtake_le _ _),
      List.rtake_append_rtake]

end OfWindow

end SubsequentialTransducer

/-! ### Letter-to-letter machines as block transducers

A `Mealy` machine is a `SubsequentialTransducer` emitting singleton blocks with an
empty final flush; `LetterToLetter` witnesses the singleton blocks, and the two views
are mutually inverse. -/

section LetterToLetter

/-- A Mealy machine as a block `SubsequentialTransducer`, with singleton outputs and an empty
flush. -/
@[simps]
def Mealy.toSubsequentialTransducer (T : Mealy σ α β) : SubsequentialTransducer σ α β where
  start := T.start
  step := T.step
  output s x := [T.output s x]
  finalOutput _ := []

@[simp] theorem Mealy.toSubsequentialTransducer_runFrom (T : Mealy σ α β) (s : σ) (xs : List α) :
    T.toSubsequentialTransducer.runFrom s xs = T.runFrom s xs := by
  induction xs generalizing s <;> simp [*]

@[simp] theorem Mealy.toSubsequentialTransducer_run (T : Mealy σ α β) :
    T.toSubsequentialTransducer.run = T.run :=
  funext fun xs ↦ T.toSubsequentialTransducer_runFrom T.start xs

/-- A witness that every output block of `T` is a singleton, named by `cell`. -/
structure SubsequentialTransducer.LetterToLetter (T : SubsequentialTransducer σ α β) where
  /-- `cell s a` is the symbol emitted on reading `a` in the state `s`. -/
  cell : σ → α → β
  /-- Every output block is that singleton. -/
  output_eq : ∀ s x, T.output s x = [cell s x]

namespace SubsequentialTransducer.LetterToLetter

variable {T : SubsequentialTransducer σ α β}

/-- Extract a witness from a bound on block lengths. -/
def ofLength (hs : ∀ s x, (T.output s x).length = 1) : T.LetterToLetter where
  cell s x := (T.output s x).head (List.ne_nil_of_length_pos (by rw [hs]; omega))
  output_eq s x := by
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hs s x)
    simp [ha]

/-- `w.toMealy` is the Mealy machine emitting each cell's symbol. -/
@[simps]
def toMealy (w : T.LetterToLetter) : Mealy σ α β where
  start := T.start
  step := T.step
  output := w.cell

theorem runFrom_toMealy (w : T.LetterToLetter) (hf : ∀ s, T.finalOutput s = [])
    (s : σ) (xs : List α) : w.toMealy.runFrom s xs = T.runFrom s xs := by
  induction xs generalizing s with
  | nil => simp [hf]
  | cons x xs ih => simp [w.output_eq, ih]

theorem run_toMealy (w : T.LetterToLetter) (hf : ∀ s, T.finalOutput s = []) :
    w.toMealy.run = T.run :=
  funext fun xs ↦ w.runFrom_toMealy hf T.start xs

theorem toSubsequentialTransducer_toMealy (w : T.LetterToLetter)
    (hf : ∀ s, T.finalOutput s = []) : w.toMealy.toSubsequentialTransducer = T :=
  SubsequentialTransducer.ext rfl rfl
    (funext₂ fun s x ↦ (w.output_eq s x).symm) (funext fun s ↦ (hf s).symm)

theorem isMealyComputable [Fintype σ] (w : T.LetterToLetter)
    (hf : ∀ s, T.finalOutput s = []) : IsMealyComputable T.run :=
  w.run_toMealy hf ▸ w.toMealy.isMealyComputable

end SubsequentialTransducer.LetterToLetter

/-- The canonical witness that a Mealy machine's block form is letter-to-letter. -/
def Mealy.letterToLetter (T : Mealy σ α β) : T.toSubsequentialTransducer.LetterToLetter :=
  ⟨T.output, fun _ _ ↦ rfl⟩

@[simp] theorem Mealy.toMealy_letterToLetter (T : Mealy σ α β) :
    T.letterToLetter.toMealy = T := rfl

end LetterToLetter

/-! ### Subsequential classification predicates -/

variable {γ : Type*} {f : List α → List β} {g : List β → List γ}

/-- A function `f : List α → List β` is *left-subsequential* if some finite-state
transducer computes it via left-to-right scan [mohri-1997]. -/
def IsLeftSubsequential (f : List α → List β) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (T : SubsequentialTransducer σ α β), T.run = f

/-- A function `f : List α → List β` is *right-subsequential* if its reverse-conjugate
is left-subsequential — equivalently, some finite-state transducer computes it via
right-to-left scan (`isRightSubsequential_iff`). -/
def IsRightSubsequential (f : List α → List β) : Prop :=
  IsLeftSubsequential (List.revConj f)

/-- A function `f : List α → List β` is *subsequential from the edge `d`* if some finite-state
transducer computes it by a scan starting from that edge. -/
def IsSubsequential (d : Edge) (f : List α → List β) : Prop :=
  match d with
  | .left => IsLeftSubsequential f
  | .right => IsRightSubsequential f

@[simp] theorem isSubsequential_left_iff :
    IsSubsequential .left f ↔ IsLeftSubsequential f := Iff.rfl

@[simp] theorem isSubsequential_right_iff :
    IsSubsequential .right f ↔ IsRightSubsequential f := Iff.rfl

theorem isRightSubsequential_iff :
    IsRightSubsequential f
      ↔ ∃ (σ : Type) (_ : Fintype σ) (T : SubsequentialTransducer σ α β), T.runRight = f :=
  exists₃_congr fun _ _ T ↦ by rw [T.runRight_eq_revConj_run, List.revConj_eq_iff]

/-- Every finite-state transducer computes a left-subsequential function, whatever the
universe of its state type. -/
theorem SubsequentialTransducer.isLeftSubsequential {σ : Type*} [Fintype σ]
    (T : SubsequentialTransducer σ α β) :
    IsLeftSubsequential T.run :=
  ⟨Shrink σ, inferInstance, T.map (equivShrink.{0} σ), T.run_map _⟩

/-! ### Reverse conjugation -/

theorem IsRightSubsequential.revConj (hf : IsRightSubsequential f) :
    IsLeftSubsequential (List.revConj f) := hf

theorem IsLeftSubsequential.revConj (hf : IsLeftSubsequential f) :
    IsRightSubsequential (List.revConj f) :=
  show IsLeftSubsequential _ from (List.revConj_revConj f).symm ▸ hf

theorem isLeftSubsequential_revConj_iff :
    IsLeftSubsequential (List.revConj f) ↔ IsRightSubsequential f := Iff.rfl

@[simp] theorem isRightSubsequential_revConj_iff :
    IsRightSubsequential (List.revConj f) ↔ IsLeftSubsequential f :=
  ⟨fun h ↦ List.revConj_revConj f ▸ h.revConj, IsLeftSubsequential.revConj⟩

theorem SubsequentialTransducer.isRightSubsequential {σ : Type*} [Fintype σ]
    (T : SubsequentialTransducer σ α β) :
    IsRightSubsequential T.runRight :=
  T.isLeftSubsequential.revConj

/-! ### Mealy-computable functions -/

/-- A Mealy-computable function is left-subsequential, since
`Mealy.toSubsequentialTransducer` presents a Mealy machine as a block transducer emitting
singleton blocks. -/
theorem IsMealyComputable.isLeftSubsequential (hf : IsMealyComputable f) :
    IsLeftSubsequential f := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact T.toSubsequentialTransducer_run ▸ T.toSubsequentialTransducer.isLeftSubsequential

/-- A finite Mealy machine computes a left-subsequential function. -/
theorem Mealy.isLeftSubsequential {σ : Type*} [Fintype σ] (T : Mealy σ α β) :
    IsLeftSubsequential T.run :=
  T.isMealyComputable.isLeftSubsequential

theorem Mealy.isRightSubsequential {σ : Type*} [Fintype σ] (T : Mealy σ α β) :
    IsRightSubsequential T.runRight :=
  T.isLeftSubsequential.revConj

theorem isLeftSubsequential_map (h : α → β) : IsLeftSubsequential (List.map h) :=
  (isMealyComputable_map h).isLeftSubsequential

theorem isLeftSubsequential_id : IsLeftSubsequential (id : List α → List α) :=
  isMealyComputable_id.isLeftSubsequential

theorem isRightSubsequential_map (h : α → β) : IsRightSubsequential (List.map h) :=
  List.revConj_map h ▸ (isLeftSubsequential_map h).revConj

theorem isRightSubsequential_id : IsRightSubsequential (id : List α → List α) :=
  List.revConj_id (α := α) ▸ isLeftSubsequential_id.revConj

theorem isSubsequential_map (d : Edge) (h : α → β) :
    IsSubsequential d (List.map h) :=
  match d with
  | .left => isLeftSubsequential_map h
  | .right => isRightSubsequential_map h

theorem isSubsequential_id (d : Edge) :
    IsSubsequential d (id : List α → List α) :=
  match d with
  | .left => isLeftSubsequential_id
  | .right => isRightSubsequential_id

/-! ### Window functions -/

section WindowRun

open SubsequentialTransducer

variable {δ : Type*} [Fintype δ] (n : ℕ) (out : List δ → α → List β)
  (upd : List δ → α → List δ)

theorem isLeftSubsequential_windowRun : IsLeftSubsequential (windowRun n out upd []) :=
  run_ofWindow (n := n) (out := out) (upd := upd) ▸ (ofWindow n out upd).isLeftSubsequential

theorem isMealyComputable_windowRun (hs : ∀ w x, (out w x).length = 1) :
    IsMealyComputable (windowRun n out upd []) :=
  run_ofWindow (n := n) (out := out) (upd := upd) ▸
    (LetterToLetter.ofLength fun w x ↦ hs w.val x).isMealyComputable fun _ ↦ rfl

end WindowRun

/-! ### Closure under composition -/

/-- Left-subsequential functions are closed under composition, by
`SubsequentialTransducer.comp` [mohri-1997]. -/
theorem IsLeftSubsequential.comp (hg : IsLeftSubsequential g)
    (hf : IsLeftSubsequential f) : IsLeftSubsequential (g ∘ f) := by
  obtain ⟨σ₁, _, T₁, rfl⟩ := hf
  obtain ⟨σ₂, _, T₂, rfl⟩ := hg
  exact ⟨σ₂ × σ₁, inferInstance, T₂.comp T₁, T₂.run_comp T₁⟩

/-- Right-subsequential functions are closed under composition, by conjugating the left
closure. -/
theorem IsRightSubsequential.comp (hg : IsRightSubsequential g)
    (hf : IsRightSubsequential f) : IsRightSubsequential (g ∘ f) := by
  show IsLeftSubsequential (List.revConj (g ∘ f))
  rw [List.revConj_comp]
  exact IsLeftSubsequential.comp hg hf

/-- Subsequential functions are closed under composition in either scan direction. -/
theorem IsSubsequential.comp {d : Edge} (hg : IsSubsequential d g)
    (hf : IsSubsequential d f) : IsSubsequential d (g ∘ f) :=
  match d, hg, hf with
  | .left, hg, hf => IsLeftSubsequential.comp hg hf
  | .right, hg, hf => IsRightSubsequential.comp hg hf

/-! ### Regular preimages -/

/-- Left-subsequential functions pull back regular languages (`DFA.comapSubsequential`). -/
theorem IsLeftSubsequential.isRegular_preimage (hf : IsLeftSubsequential f)
    {L : Language β} (hL : L.IsRegular) : Language.IsRegular (f ⁻¹' L) := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  obtain ⟨τ, _, M, rfl⟩ := hL
  exact ⟨σ × τ, inferInstance, M.comapSubsequential T, M.accepts_comapSubsequential T⟩

/-- Right-subsequential functions pull back regular languages, by conjugating the left case
through the closure of the regular languages under reversal. -/
theorem IsRightSubsequential.isRegular_preimage (hf : IsRightSubsequential f)
    {L : Language β} (hL : L.IsRegular) : Language.IsRegular (f ⁻¹' L) := by
  have h := (hf.revConj.isRegular_preimage hL.reverse).reverse
  rwa [← List.preimage_revConj, List.revConj_revConj] at h

/-- Subsequential functions pull back regular languages in either scan direction. -/
theorem IsSubsequential.isRegular_preimage {d : Edge} (hf : IsSubsequential d f)
    {L : Language β} (hL : L.IsRegular) : Language.IsRegular (f ⁻¹' L) :=
  match d, hf with
  | .left, hf => IsLeftSubsequential.isRegular_preimage hf hL
  | .right, hf => IsRightSubsequential.isRegular_preimage hf hL

/-! ### Bounded delay -/

/-- A left-subsequential function withholds at most the longest state-final output, so all but
the last `N` symbols of `f u` are a prefix of `f (u ++ v)`. This is much weaker than
[choffrut-1977]'s bounded-variation characterization, comparing `u` only with its own
extensions. -/
theorem IsLeftSubsequential.bounded_delay (hf : IsLeftSubsequential f) :
    ∃ N : ℕ, ∀ u v : List α, (f u).rdrop N <+: f (u ++ v) := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  refine ⟨Finset.univ.sup fun s ↦ (T.finalOutput s).length, fun u v ↦ ?_⟩
  rw [T.run_append, SubsequentialTransducer.run, SubsequentialTransducer.runFrom,
    List.rdrop_append, List.rdrop_of_length_le
      (Finset.le_sup (f := fun s ↦ (T.finalOutput s).length) (Finset.mem_univ _)),
    List.append_nil]
  exact (List.rdrop_prefix _ _).trans (List.prefix_append _ _)

/-- For a right-subsequential `f`, all but the first `N` symbols of `f u` are a suffix of
`f (v ++ u)`. -/
theorem IsRightSubsequential.bounded_delay (hf : IsRightSubsequential f) :
    ∃ N : ℕ, ∀ u v : List α, (f u).drop N <:+ f (v ++ u) := by
  obtain ⟨N, hN⟩ := IsLeftSubsequential.bounded_delay hf
  refine ⟨N, fun u v ↦ ?_⟩
  simpa [List.revConj, List.rdrop_eq_reverse_drop_reverse] using
    (hN u.reverse v.reverse).reverse

theorem IsLeftSubsequential.exists_getElem?_append_eq (hf : IsLeftSubsequential f) :
    ∃ N : ℕ, ∀ u v i, i + N < (f u).length → (f u)[i]? = (f (u ++ v))[i]? := by
  obtain ⟨N, hN⟩ := hf.bounded_delay
  refine ⟨N, fun u v i hi ↦ ?_⟩
  rw [List.prefix_iff_getElem?.mp (hN u v) i (by simp; omega),
    List.getElem?_eq_getElem (by omega)]
  simp [List.rdrop]

theorem IsLeftSubsequential.exists_getElem?_take_eq
    (hlen : ∀ w, (f w).length = w.length) (hf : IsLeftSubsequential f) :
    ∃ N, ∀ i w, (f (w.take (i + N + 1)))[i]? = (f w)[i]? := by
  obtain ⟨N, hN⟩ := hf.exists_getElem?_append_eq
  refine ⟨N, fun i w ↦ ?_⟩
  rcases lt_or_ge w.length (i + N + 1) with h | h
  · rw [List.take_of_length_le h.le]
  · conv_rhs => rw [← List.take_append_drop (i + N + 1) w]
    exact hN _ _ i (by rw [hlen, List.length_take]; omega)

theorem IsRightSubsequential.exists_getElem?_append_eq (hlen : ∀ w, (f w).length = w.length)
    (hf : IsRightSubsequential f) :
    ∃ N : ℕ, ∀ u v i, N ≤ i → (f u)[i]? = (f (v ++ u))[v.length + i]? := by
  obtain ⟨N, hN⟩ := hf.bounded_delay
  refine ⟨N, fun u v i hi ↦ ?_⟩
  have h := List.suffix_iff_eq_drop.mp (hN u v)
  rcases le_or_gt N u.length with hNu | hNu
  · have hk : (f (v ++ u)).length - ((f u).drop N).length = v.length + N := by
      simp [hlen]; omega
    rw [hk] at h
    simpa [List.getElem?_drop, Nat.add_sub_cancel' hi, Nat.add_assoc] using
      congrArg (·[i - N]?) h
  · rw [List.getElem?_eq_none (by rw [hlen]; omega),
      List.getElem?_eq_none (by rw [hlen, List.length_append]; omega)]

theorem IsRightSubsequential.exists_getElem?_drop_eq
    (hlen : ∀ w, (f w).length = w.length) (hf : IsRightSubsequential f) :
    ∃ N, ∀ i w, N ≤ i → (f (w.drop (i - N)))[N]? = (f w)[i]? := by
  obtain ⟨N, hN⟩ := hf.exists_getElem?_append_eq hlen
  refine ⟨N, fun i w hiN ↦ ?_⟩
  rcases le_or_gt (i - N) w.length with h | h
  · rw [hN (w.drop (i - N)) (w.take (i - N)) N le_rfl, List.take_append_drop,
      List.length_take, Nat.min_eq_left h, Nat.sub_add_cancel hiN]
  · rw [List.drop_of_length_le h.le, List.getElem?_eq_none (by simp [hlen]),
      List.getElem?_eq_none (by rw [hlen]; omega)]

theorem not_isLeftSubsequential_of_diverging
    (h : ∀ N, ∃ (u v : List α) (i : ℕ),
      i + N < (f u).length ∧ (f u)[i]? ≠ (f (u ++ v))[i]?) :
    ¬ IsLeftSubsequential f := by
  intro hf
  obtain ⟨N, hN⟩ := hf.exists_getElem?_append_eq
  obtain ⟨u, v, i, hi, hne⟩ := h N
  exact hne (hN u v i hi)
