/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Computability.NFA
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Lattice.Fold
public import Linglib.Core.Computability.Mealy
public import Linglib.Core.Computability.Edge
public import Linglib.Core.Data.List.DropRight

/-!
# Subsequential functions and finite-state transducers

A subsequential transducer is a sequential transducer, a `Mealy` machine over the output alphabet
`List β`, together with a final block of output determined by the ending state. The functions so
computed, scanning from either end of the word, form a proper subclass of the rational functions.
Each class is [closed under composition](##IsLeftSubsequential.comp), and [reversal exchanges
the two](##isRightSubsequential_revConj_iff). The left class contains the [Mealy-computable
functions](##IsMealyComputable.isLeftSubsequential) and the right class their mirror images, yet
[neither contains the other](##exists_isMealyComputable_not_isRightSubsequential). These functions
[pull back regular languages](##IsLeftSubsequential.isRegular_preimage) and [withhold at most a
bounded stretch of output](##IsLeftSubsequential.bounded_delay).

## Implementation notes

The name follows Schützenberger, Choffrut and Mohri: *sequential* without state-final output,
*subsequential* with. Sakarovitch calls this class *sequential* and the empty-flush case *pure
sequential*, flagging his usage as unconventional (Rem. V.1.2, Def. V.1.4); Filiot and Reynier also
say *sequential*. `Mealy` is the letter-to-letter case.

`step` is total, so only the *total* subsequential functions are modelled, since a sink state
does not recover partiality. Sakarovitch's initial-output function is omitted, which does not
shrink the class (his Exer. V.1.10): a fresh start state can carry the block. As with `DFA`, a
machine may have infinitely many states, and the classification predicates ask for a `Fintype`. The
state run `evalFrom` and its lemmas are those of the underlying `Mealy` machine. There are two
disjoint sets of simp lemmas, one for `run` and another for `runFrom`; switch from the former to
the latter via `simp [run]`.

[UPSTREAM] candidate: `Mathlib.Computability.Subsequential`.

## TODO

* Choffrut's theorem: over a finite alphabet, a rational function is subsequential iff it has
  bounded variation (Sakarovitch's *uniformly bounded*, Def. V.4.2), decidably by the twinning
  property. Bruyère and Reutenauer give a short proof.
* Minimality of the residual machine of `IsLeftSubsequential.of_finite_range_residual`;
  two-way transducers; Mohri's `p`-subsequential functions.

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

/-! ### Reindexing along state equivalences -/

section Reindex

variable {τ : Type*}

/-- Lifts an equivalence on states to an equivalence on transducers. -/
@[simps apply_toMealy apply_finalOutput]
def reindex (g : σ ≃ τ) : SubsequentialTransducer σ α β ≃ SubsequentialTransducer τ α β where
  toFun T := { Mealy.reindex g T.toMealy with finalOutput := T.finalOutput ∘ g.symm }
  invFun T := { Mealy.reindex g.symm T.toMealy with finalOutput := T.finalOutput ∘ g }
  left_inv T := by ext <;> simp
  right_inv T := by ext <;> simp

@[simp] theorem reindex_refl : reindex (Equiv.refl σ) T = T := rfl

@[simp] theorem symm_reindex (g : σ ≃ τ) : (reindex (α := α) (β := β) g).symm = reindex g.symm :=
  rfl

@[simp] theorem emitted_reindex (g : σ ≃ τ) (t : τ) (xs : List α) :
    (reindex g T).emitted t xs = T.emitted (g.symm t) xs := by
  simp [emitted]

@[simp] theorem runFrom_reindex (g : σ ≃ τ) (t : τ) (xs : List α) :
    (reindex g T).runFrom t xs = T.runFrom (g.symm t) xs := by
  simp [runFrom]

@[simp] theorem run_reindex (g : σ ≃ τ) : (reindex g T).run = T.run := by
  funext xs; simp [run]

end Reindex

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

end SubsequentialTransducer

/-! ### Mealy machines as block transducers -/

/-- A Mealy machine as a block `SubsequentialTransducer`, with singleton outputs and an empty
flush. -/
@[simps]
def Mealy.toSubsequentialTransducer (T : Mealy σ α β) : SubsequentialTransducer σ α β where
  start := T.start
  step := T.step
  output s x := [T.output s x]
  finalOutput _ := []

@[simp] theorem Mealy.runFrom_toSubsequentialTransducer (T : Mealy σ α β) (s : σ) (xs : List α) :
    T.toSubsequentialTransducer.runFrom s xs = T.runFrom s xs := by
  induction xs generalizing s <;> simp [*]

@[simp] theorem Mealy.run_toSubsequentialTransducer (T : Mealy σ α β) :
    T.toSubsequentialTransducer.run = T.run :=
  funext fun xs ↦ T.runFrom_toSubsequentialTransducer T.start xs

/-- A finite transducer emitting singleton blocks and no final output computes a
Mealy-computable function. -/
theorem SubsequentialTransducer.isMealyComputable_run {σ : Type*} [Fintype σ]
    (T : SubsequentialTransducer σ α β) (hs : ∀ s x, (T.output s x).length = 1)
    (hf : ∀ s, T.finalOutput s = []) : IsMealyComputable T.run := by
  choose cell hcell using fun s x ↦ List.length_eq_one_iff.mp (hs s x)
  have h : ∀ s xs, (Mealy.mk T.start T.step cell).runFrom s xs = T.runFrom s xs := fun s xs ↦ by
    induction xs generalizing s <;> simp [*]
  have hrun : (Mealy.mk T.start T.step cell).run = T.run := funext (h T.start)
  exact hrun ▸ (Mealy.mk T.start T.step cell).isMealyComputable

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
  ⟨Shrink σ, inferInstance, SubsequentialTransducer.reindex (equivShrink.{0} σ) T, T.run_reindex _⟩

/-! ### Reverse conjugation -/

theorem IsRightSubsequential.revConj (hf : IsRightSubsequential f) :
    IsLeftSubsequential (List.revConj f) := hf

theorem IsLeftSubsequential.revConj (hf : IsLeftSubsequential f) :
    IsRightSubsequential (List.revConj f) :=
  show IsLeftSubsequential _ from (List.revConj_revConj f).symm ▸ hf

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
  exact T.run_toSubsequentialTransducer ▸ T.toSubsequentialTransducer.isLeftSubsequential

/-- A finite Mealy machine computes a left-subsequential function. -/
theorem Mealy.isLeftSubsequential {σ : Type*} [Fintype σ] (T : Mealy σ α β) :
    IsLeftSubsequential T.run :=
  T.isMealyComputable.isLeftSubsequential

theorem Mealy.isRightSubsequential {σ : Type*} [Fintype σ] (T : Mealy σ α β) :
    IsRightSubsequential T.runRight :=
  T.isLeftSubsequential.revConj

theorem isLeftSubsequential_id : IsLeftSubsequential (id : List α → List α) :=
  isMealyComputable_id.isLeftSubsequential

theorem isRightSubsequential_id : IsRightSubsequential (id : List α → List α) :=
  List.revConj_id (α := α) ▸ isLeftSubsequential_id.revConj

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
  have hi' : i < ((f u).rdrop N).length := by simp; omega
  exact (List.prefix_iff_getElem?.mp (List.rdrop_prefix _ N) i hi').trans
    (List.prefix_iff_getElem?.mp (hN u v) i hi').symm

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

/-! ### Incomparability of the two scans -/

/-- A left-to-right Mealy machine can carry a bit from the start of the word to its end, which no
right-to-left transducer can do: reading from the far end, it would have to hold back a block of
unbounded length until the bit appears. -/
theorem exists_isMealyComputable_not_isRightSubsequential :
    ∃ f : List Bool → List Bool, IsMealyComputable f ∧ ¬ IsRightSubsequential f := by
  refine ⟨(Mealy.ofFlag id fun b _ ↦ b).run, Mealy.isMealyComputable _, fun hf ↦ ?_⟩
  obtain ⟨N, hN⟩ := hf.exists_getElem?_drop_eq (Mealy.length_run _)
  have h := hN (N + 1) (true :: List.replicate (N + 1) false) (by omega)
  rw [Mealy.getElem?_ofFlag_run, Mealy.getElem?_ofFlag_run] at h
  simp [show N + 1 - N = 1 by omega] at h

/-- The mirror image of `exists_isMealyComputable_not_isRightSubsequential`, so that neither
scan's class contains the other. -/
theorem exists_isRightSubsequential_not_isLeftSubsequential :
    ∃ f : List Bool → List Bool, IsRightSubsequential f ∧ ¬ IsLeftSubsequential f :=
  have ⟨f, hf, hnot⟩ := exists_isMealyComputable_not_isRightSubsequential
  ⟨List.revConj f, hf.isLeftSubsequential.revConj, hnot⟩
