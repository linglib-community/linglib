module

public import Linglib.Semantics.Dynamic.Partial
public import Linglib.Data.Examples.Beaver2001

/-!
# Beaver (2001): Presupposition and Assertion in Dynamic Semantics

The book reviews the linguistic theories of presupposition (Part I) and then builds a dynamic
one (Part II). This file formalizes the propositional core of Part II, the partial update logic
PUL of Chapter 6, and its trivalent counterpart of Chapter 10. A sentence denotes an update of
information states, sets of worlds, and the presupposition operator `∂φ` passes a state through
only if updating it with `φ` changes nothing. A state satisfies a sentence it is a fixed point
of and admits a sentence it can be updated with. A sentence presupposes what every state
admitting it satisfies, and entails what every output of an update with it satisfies. From
Part I, the file states Strawsonian presupposition and its Strong Kleene projection (Fact 2.1).

## Implementation notes

* The book's updates are relations between states. Every PUL relation is a partial function,
  so a sentence denotes a `CCP.Partial`.
* Facts 7.1, 8.1–8.3 and 8.5–8.8, with the tests of D61, are stated for ABLE, the first-order
  system of Chapters 7 and 8. Their proofs use only the propositional clauses, which ABLE shares
  with PUL, and they are proved here for PUL.
* Presupposition and its projection through negation, conjunction and *implies* are the
  substrate's `PartialUpdate.Presupposes` and its lemmas; the study adds *might*, *must* and
  `∂`.
* `Formula.tval` gives the modal sentences the junk value `0`; every theorem about it
  assumes the sentence non-modal.

## TODO

* The remark after Fact 2.1, that for bivalent `ψ` the presuppositions listed are maximal.
* Fact 10.4: the trivalent correspondence extends to Bochvar's assertion operator (D79).
* The hide-and-seek examples E178–E183, which motivate the order sensitivity of *might*.

## References

* [beaver-2001]
* [kleene-1952]
* [peters-1979]
* [veltman-1996]
-/

@[expose] public section

namespace Beaver2001

open DynamicSemantics Classical

variable {P W : Type*}

/-! ### Strawsonian presupposition under Strong Kleene (Fact 2.1) -/

/-- `φ` presupposes `π` in Strawson's sense (D1) when `π` is true wherever `φ` is
classical. -/
def StrawsonPresupposes (φ π : W → SignType) : Prop := ∀ w, φ w ≠ 0 → π w = 1

namespace StrawsonPresupposes

variable {φ ψ π : W → SignType}

private theorem of_table (f g : SignType → SignType → SignType)
    (t : ∀ a b c, (a ≠ 0 → c = 1) → f a b ≠ 0 → g b c = 1)
    (h : StrawsonPresupposes φ π) :
    StrawsonPresupposes (fun w ↦ f (φ w) (ψ w)) fun w ↦ g (ψ w) (π w) :=
  fun w ↦ t _ _ _ (h w)

/-! The rows of Fact 2.1, with the Strong Kleene connectives `⊓`, `⊔` and `-`, and
`φ → ψ` read as `¬φ ∨ ψ`. -/

theorem neg (h : StrawsonPresupposes φ π) : StrawsonPresupposes (fun w ↦ -φ w) π :=
  fun w hw ↦ h w (mt SignType.neg_eq_zero_iff.2 hw)

theorem and_left (h : StrawsonPresupposes φ π) :
    StrawsonPresupposes (fun w ↦ φ w ⊓ ψ w) fun w ↦ -ψ w ⊔ π w :=
  h.of_table (· ⊓ ·) (fun b c ↦ -b ⊔ c) (by decide)

theorem and_right (h : StrawsonPresupposes φ π) :
    StrawsonPresupposes (fun w ↦ ψ w ⊓ φ w) fun w ↦ -ψ w ⊔ π w :=
  h.of_table (fun a b ↦ b ⊓ a) (fun b c ↦ -b ⊔ c) (by decide)

theorem imp_left (h : StrawsonPresupposes φ π) :
    StrawsonPresupposes (fun w ↦ -φ w ⊔ ψ w) fun w ↦ ψ w ⊔ π w :=
  h.of_table (fun a b ↦ -a ⊔ b) (· ⊔ ·) (by decide)

theorem imp_right (h : StrawsonPresupposes φ π) :
    StrawsonPresupposes (fun w ↦ -ψ w ⊔ φ w) fun w ↦ -ψ w ⊔ π w :=
  h.of_table (fun a b ↦ -b ⊔ a) (fun b c ↦ -b ⊔ c) (by decide)

theorem or_left (h : StrawsonPresupposes φ π) :
    StrawsonPresupposes (fun w ↦ φ w ⊔ ψ w) fun w ↦ ψ w ⊔ π w :=
  h.of_table (· ⊔ ·) (· ⊔ ·) (by decide)

theorem or_right (h : StrawsonPresupposes φ π) :
    StrawsonPresupposes (fun w ↦ ψ w ⊔ φ w) fun w ↦ ψ w ⊔ π w :=
  h.of_table (fun a b ↦ b ⊔ a) (· ⊔ ·) (by decide)

end StrawsonPresupposes

/-! ### Partial update logic (Ch. 6) -/

/-- The sentences of PUL over the atomic formulae `P` (D22, D34). -/
inductive Formula (P : Type*) where
  | atom (p : P)
  | not (φ : Formula P)
  | and (φ ψ : Formula P)
  | might (φ : Formula P)
  | must (φ : Formula P)
  | presup (φ : Formula P)
  deriving DecidableEq

namespace Formula

/-- `φ implies ψ` is `not (φ and not ψ)` (D25). -/
def implies (φ ψ : Formula P) : Formula P := not (and φ (not ψ))

section Model

variable (F : P → Set W)

/-- The update a sentence denotes in the model interpreting each atom `p` as `F p` (D25, D35),
a partial function on information states that is defined for `∂φ` only at the fixed points of
`φ`. -/
noncomputable def eval : Formula P → CCP.Partial W
  | atom p => fun σ ↦ Part.some {w ∈ σ | w ∈ F p}
  | not φ => CCP.Partial.neg (eval φ)
  | and φ ψ => PartialUpdate.seq (eval φ) (eval ψ)
  | might φ => fun σ ↦ (eval φ σ).map fun υ ↦ if υ.Nonempty then σ else ∅
  | must φ => fun σ ↦ (eval φ σ).map fun υ ↦ if υ = σ then σ else ∅
  | presup φ => fun σ ↦ ⟨σ ∈ eval φ σ, fun _ ↦ σ⟩

/-- `σ` satisfies `φ` (D29) when `σ[φ]σ`. -/
def Satisfies (σ : Set W) (φ : Formula P) : Prop := PartialUpdate.supports σ (φ.eval F)

/-- `φ` presupposes `ψ` (D31) when every state admitting `φ` (D30) satisfies `ψ`. -/
def Presupposes (φ ψ : Formula P) : Prop := PartialUpdate.Presupposes (φ.eval F) (ψ.eval F)

/-- `φ` entails `ψ` (D26, with one premise) when every update with `φ` yields a state
satisfying `ψ` (`entails_iff_forall`), which is dynamic entailment between the two updates. -/
def Entails (φ ψ : Formula P) : Prop :=
  DynamicSemantics.Entails [(· >>= φ.eval F)] (· >>= ψ.eval F)

/-- `σ` is consistent with `φ` (Fact 8.5) when updating it does not reach the absurd state. -/
def ConsistentWith (σ : Set W) (φ : Formula P) : Prop := ∃ τ ∈ φ.eval F σ, τ.Nonempty

/-- A test (D61) has only the input and the absurd state as outputs. -/
def IsTest (φ : Formula P) : Prop := ∀ σ τ, τ ∈ φ.eval F σ → τ = σ ∨ τ = ∅

end Model

variable {F : P → Set W} {φ ψ χ : Formula P} {σ τ : Set W} {w : W}

theorem mem_eval_atom {p : P} : τ ∈ (atom p).eval F σ ↔ τ = {w ∈ σ | w ∈ F p} :=
  Part.mem_some_iff

theorem mem_eval_not : τ ∈ (not φ).eval F σ ↔ ∃ υ ∈ φ.eval F σ, σ \ υ = τ :=
  Part.mem_map_iff _

theorem mem_eval_and : τ ∈ (and φ ψ).eval F σ ↔ ∃ υ ∈ φ.eval F σ, τ ∈ ψ.eval F υ :=
  Part.mem_bind_iff

theorem mem_eval_might :
    τ ∈ (might φ).eval F σ ↔ ∃ υ ∈ φ.eval F σ, (if υ.Nonempty then σ else ∅) = τ :=
  Part.mem_map_iff _

theorem mem_eval_must :
    τ ∈ (must φ).eval F σ ↔ ∃ υ ∈ φ.eval F σ, (if υ = σ then σ else ∅) = τ :=
  Part.mem_map_iff _

theorem mem_eval_presup : τ ∈ (presup φ).eval F σ ↔ σ ∈ φ.eval F σ ∧ τ = σ :=
  Part.mem_mk_iff.trans ⟨fun ⟨h, e⟩ ↦ ⟨h, e.symm⟩, fun ⟨h, e⟩ ↦ ⟨h, e.symm⟩⟩

-- Fact 7.1
theorem eval_eliminative : ∀ (φ : Formula P) {σ τ : Set W}, τ ∈ φ.eval F σ → τ ⊆ σ
  | atom _, _, _, h => mem_eval_atom.1 h ▸ Set.sep_subset _ _
  | not _, _, _, h => CCP.Partial.isEliminative_neg _ _ _ h
  | and φ ψ, _, _, h =>
    PartialUpdate.IsEliminative.seq (fun _ _ ↦ eval_eliminative φ) (fun _ _ ↦ eval_eliminative ψ)
      _ _ h
  | might _, _, _, h => by obtain ⟨_, -, rfl⟩ := mem_eval_might.1 h; split_ifs <;> simp
  | must _, _, _, h => by obtain ⟨_, -, rfl⟩ := mem_eval_must.1 h; split_ifs <;> simp
  | presup _, _, _, h => (mem_eval_presup.1 h).2 ▸ le_rfl

theorem empty_mem_eval_empty : ∀ φ : Formula P, (∅ : Set W) ∈ φ.eval F ∅
  | atom _ => mem_eval_atom.2 (by ext; simp)
  | not φ => mem_eval_not.2 ⟨∅, empty_mem_eval_empty φ, Set.empty_sdiff _⟩
  | and φ ψ => mem_eval_and.2 ⟨∅, empty_mem_eval_empty φ, empty_mem_eval_empty ψ⟩
  | might φ => mem_eval_might.2 ⟨∅, empty_mem_eval_empty φ, by simp⟩
  | must φ => mem_eval_must.2 ⟨∅, empty_mem_eval_empty φ, by simp⟩
  | presup φ => mem_eval_presup.2 ⟨empty_mem_eval_empty φ, rfl⟩

theorem admits_of_mem (h : τ ∈ φ.eval F σ) : (φ.eval F).Admits σ := Part.dom_iff_mem.2 ⟨τ, h⟩

theorem presupposes_iff_forall :
    Presupposes F φ ψ ↔ ∀ σ, (φ.eval F).Admits σ → Satisfies F σ ψ := Iff.rfl

theorem entails_iff_forall : Entails F φ ψ ↔ ∀ σ τ, τ ∈ φ.eval F σ → Satisfies F τ ψ :=
  PartialUpdate.entails_bind_iff

theorem eval_implies : (implies φ ψ).eval F = CCP.Partial.cond (φ.eval F) (ψ.eval F) :=
  (CCP.Partial.cond_eq_neg_seq_neg _ _).symm

-- Fact 6.1
theorem eval_must (φ : Formula P) : (must φ).eval F = (not (might (not φ))).eval F := by
  funext σ
  change (φ.eval F σ).map _ = (((φ.eval F σ).map (σ \ ·)).map _).map (σ \ ·)
  rw [Part.map_map, Part.map_map]
  refine Part.ext fun τ ↦ ?_
  simp only [Part.mem_map_iff]
  refine exists_congr fun υ ↦ and_congr_right fun hυ ↦ ?_
  by_cases h : υ = σ
  · subst h; simp
  · have hne : (σ \ υ).Nonempty :=
      Set.sdiff_nonempty.2 fun hσ ↦ h ((eval_eliminative φ hυ).antisymm hσ)
    simp [h, hne]

/-! ### Projection (Facts 8.1–8.3, 8.8) -/

theorem Presupposes.not (h : Presupposes F φ ψ) : Presupposes F (not φ) ψ :=
  PartialUpdate.Presupposes.neg h

theorem Presupposes.and_left (h : Presupposes F φ ψ) : Presupposes F (and φ χ) ψ :=
  PartialUpdate.Presupposes.seq_left h

theorem Presupposes.implies_left (h : Presupposes F φ ψ) : Presupposes F (implies φ χ) ψ :=
  h.and_left.not

theorem Presupposes.might (h : Presupposes F φ ψ) : Presupposes F (might φ) ψ :=
  fun σ hσ ↦ h σ hσ

theorem Presupposes.must (h : Presupposes F φ ψ) : Presupposes F (must φ) ψ :=
  fun σ hσ ↦ h σ hσ

-- Fact 8.2
theorem Presupposes.trans (h₁ : Presupposes F φ ψ) (h₂ : Presupposes F ψ χ) :
    Presupposes F φ χ :=
  PartialUpdate.Presupposes.trans h₁ h₂

theorem presup_and_presupposes (ψ χ : Formula P) : Presupposes F (and (presup ψ) χ) ψ :=
  fun _ ⟨hσ, _⟩ ↦ hσ

/-- A presupposition of the second conjunct projects conditionalised on the first (Fact 8.3). -/
theorem Presupposes.and_right (h : Presupposes F φ ψ) :
    Presupposes F (and χ φ) (implies χ ψ) := by
  rw [Presupposes, eval_implies]
  exact PartialUpdate.Presupposes.seq_right h

/-- A presupposition of the consequent projects conditionalised on the antecedent (Fact 8.3). -/
theorem Presupposes.implies_right (h : Presupposes F φ ψ) :
    Presupposes F (implies χ φ) (implies χ ψ) := by
  rw [Presupposes, eval_implies, eval_implies]
  exact PartialUpdate.Presupposes.cond_right h

/-! ### Epistemic modality (Facts 8.5–8.7) -/

theorem might_isTest (φ : Formula P) : IsTest F (might φ) := fun _ _ h ↦ by
  obtain ⟨_, -, rfl⟩ := mem_eval_might.1 h
  split_ifs <;> simp

theorem must_isTest (φ : Formula P) : IsTest F (must φ) := fun _ _ h ↦ by
  obtain ⟨_, -, rfl⟩ := mem_eval_must.1 h
  split_ifs <;> simp

theorem IsTest.empty_mem_iff (ht : IsTest F φ) (hσ : σ.Nonempty) (h : (φ.eval F).Admits σ) :
    ∅ ∈ φ.eval F σ ↔ ¬Satisfies F σ φ := by
  have hget := Part.get_mem h
  rcases ht _ _ hget with e | e <;> rw [e] at hget
  · exact ⟨fun h₀ ↦ absurd (Part.mem_unique h₀ hget) hσ.ne_empty.symm, fun hn ↦ absurd hget hn⟩
  · exact ⟨fun _ hs ↦ hσ.ne_empty (Part.mem_unique hs hget), fun _ ↦ hget⟩

/-- *might* is a consistency test (Fact 8.5), passing a non-absurd state iff the state is
consistent with `φ`. -/
theorem satisfies_might_iff (hσ : σ.Nonempty) :
    Satisfies F σ (might φ) ↔ ConsistentWith F σ φ := by
  constructor
  · intro hs
    obtain ⟨υ, hυ, hif⟩ := mem_eval_might.1 hs
    refine ⟨υ, hυ, ?_⟩
    by_contra hne
    rw [ite_eq_right hne] at hif
    exact hσ.ne_empty hif.symm
  · rintro ⟨υ, hυ, hne⟩
    exact mem_eval_might.2 ⟨υ, hυ, ite_eq_left hne⟩

-- Fact 8.5
theorem empty_mem_eval_might_iff (hσ : σ.Nonempty) (h : (φ.eval F).Admits σ) :
    ∅ ∈ (might φ).eval F σ ↔ ¬ConsistentWith F σ φ := by
  rw [(might_isTest φ).empty_mem_iff hσ h, satisfies_might_iff hσ]

-- Lemma 8.6
theorem satisfies_iff_not_consistentWith_not (h : (φ.eval F).Admits σ) :
    Satisfies F σ φ ↔ ¬ConsistentWith F σ (not φ) := by
  constructor
  · rintro hs ⟨_, hτ, hne⟩
    obtain ⟨υ, hυ, rfl⟩ := mem_eval_not.1 hτ
    rw [Part.mem_unique hυ hs, Set.sdiff_self] at hne
    exact Set.not_nonempty_empty hne
  · intro hc
    have hsub : σ ⊆ (φ.eval F σ).get h := fun w hw ↦ by_contra fun hw' ↦
      hc ⟨_, mem_eval_not.2 ⟨_, Part.get_mem h, rfl⟩, w, hw, hw'⟩
    have hget := Part.get_mem h
    rw [(eval_eliminative φ hget).antisymm hsub] at hget
    exact hget

/-- *must* is a satisfaction test (Fact 8.7), passing a non-absurd state iff the state
satisfies `φ`. -/
theorem satisfies_must_iff (hσ : σ.Nonempty) : Satisfies F σ (must φ) ↔ Satisfies F σ φ := by
  constructor
  · intro hs
    obtain ⟨υ, hυ, hif⟩ := mem_eval_must.1 hs
    by_cases h : υ = σ
    · exact h ▸ hυ
    · rw [ite_eq_right h] at hif
      exact absurd hif.symm hσ.ne_empty
  · exact fun hs ↦ mem_eval_must.2 ⟨σ, hs, ite_eq_left rfl⟩

-- Fact 8.7
theorem empty_mem_eval_must_iff (hσ : σ.Nonempty) (h : (φ.eval F).Admits σ) :
    ∅ ∈ (must φ).eval F σ ↔ ¬Satisfies F σ φ := by
  rw [(must_isTest φ).empty_mem_iff hσ h, satisfies_must_iff hσ]

/-! ### The trivalent counterpart (Ch. 10) -/

/-- The non-modal sentences, the language PL+∂. -/
inductive NonModal : Formula P → Prop
  | atom (p : P) : NonModal (atom p)
  | not {φ : Formula P} : NonModal φ → NonModal (not φ)
  | and {φ ψ : Formula P} : NonModal φ → NonModal ψ → NonModal (and φ ψ)
  | presup {φ : Formula P} : NonModal φ → NonModal (presup φ)

theorem NonModal.implies (hφ : NonModal φ) (hψ : NonModal ψ) : NonModal (implies φ ψ) :=
  .not (.and hφ (.not hψ))

section Model

variable (F : P → Set W)

/-- The value of a sentence of PL+∂ at a world under Peters' trivalent semantics (D70, D71),
with bivalent atoms, the Peters connectives, and `∂φ` true where `φ` is true and undefined
elsewhere. -/
noncomputable def tval : Formula P → W → SignType
  | atom p, w => .ofProp (w ∈ F p)
  | not φ, w => -tval φ w
  | and φ ψ, w => (tval φ w).meetMiddle (tval ψ w)
  | presup φ, w => (tval φ w ⊔ 0)
  | might _, _ => 0
  | must _, _ => 0

/-- `φ` is true at `w` in the update semantics (D76) when `{w}[φ]{w}`. -/
def TrueAt (w : W) (φ : Formula P) : Prop := {w} ∈ φ.eval F {w}

/-- `φ` is false at `w` in the update semantics (D77) when `{w}[φ]∅`. -/
def FalseAt (w : W) (φ : Formula P) : Prop := ∅ ∈ φ.eval F {w}

end Model

private theorem meetMiddle_ne_zero_iff {a b : SignType} :
    a.meetMiddle b ≠ 0 ↔ a ≠ 0 ∧ (a = 1 → b ≠ 0) := by
  cases a <;> cases b <;> decide

/-- On PL+∂ an update is the Heimian update of the sentence's trivalent value (Lemma 10.1, with the
distributivity used for Lemma 10.2) (Fact 10.3). -/
theorem eval_eq_ofTrivalent (hφ : NonModal φ) :
    φ.eval F = CCP.Partial.ofTrivalent (φ.tval F) := by
  induction hφ with
  | atom p =>
    funext σ; refine Part.ext fun τ ↦ ?_
    simp [eval, tval, CCP.Partial.mem_ofTrivalent, Set.subset_def]
  | @not φ _ ih =>
    funext σ; refine Part.ext fun τ ↦ ?_
    rw [mem_eval_not, ih]
    simp only [CCP.Partial.mem_ofTrivalent, Set.subset_def, Function.mem_support, tval, ne_eq,
      SignType.neg_eq_zero_iff, SignType.neg_eq_one_iff]
    have e : ∀ t : W → SignType, (∀ w ∈ σ, t w ≠ 0) →
        σ \ {w ∈ σ | t w = 1} = {w ∈ σ | t w = -1} := fun t h ↦ Set.ext fun w ↦ by
      by_cases hw : w ∈ σ
      · have := h w hw; simp only [Set.mem_sdiff, Set.mem_ofPred_eq, hw, true_and]; revert this
        cases t w <;> decide
      · simp [hw]
    exact ⟨fun ⟨_, ⟨h, e'⟩, he⟩ ↦ ⟨h, by rw [← he, e', e _ h]⟩,
      fun ⟨h, he⟩ ↦ ⟨_, ⟨h, rfl⟩, by rw [he, e _ h]⟩⟩
  | @and φ ψ _ _ ihφ ihψ =>
    funext σ; refine Part.ext fun τ ↦ ?_
    rw [mem_eval_and, ihφ, ihψ]
    simp only [CCP.Partial.mem_ofTrivalent, Set.subset_def, Function.mem_support, tval,
      meetMiddle_ne_zero_iff, SignType.meetMiddle_eq_one_iff]
    constructor
    · rintro ⟨_, ⟨h₁, rfl⟩, h₂, rfl⟩
      exact ⟨fun w hw ↦ ⟨h₁ w hw, fun ht ↦ h₂ w ⟨hw, ht⟩⟩, by ext; simp [and_assoc]⟩
    · rintro ⟨h, rfl⟩
      exact ⟨_, ⟨fun w hw ↦ (h w hw).1, rfl⟩, fun w hw ↦ (h w hw.1).2 hw.2,
        by ext; simp [and_assoc]⟩
  | @presup φ _ ih =>
    funext σ; refine Part.ext fun τ ↦ ?_
    rw [mem_eval_presup, ih, CCP.Partial.mem_ofTrivalent_self]
    simp only [CCP.Partial.mem_ofTrivalent, Set.subset_def, Function.mem_support, tval, ne_eq,
      SignType.sup_zero_eq_zero_iff, not_not, SignType.sup_zero_eq_one_iff]
    exact and_congr_right fun h ↦ by rw [Set.sep_eq_self_iff_mem_true.2 h]

theorem admits_iff (hφ : NonModal φ) :
    (φ.eval F).Admits σ ↔ ∀ w ∈ σ, φ.tval F w ≠ 0 := by
  rw [eval_eq_ofTrivalent hφ]; rfl

-- Lemma 10.1
theorem trueAt_iff (hφ : NonModal φ) : TrueAt F w φ ↔ φ.tval F w = 1 := by
  rw [TrueAt, eval_eq_ofTrivalent hφ, CCP.Partial.mem_ofTrivalent_self]; simp

-- Lemma 10.1
theorem falseAt_iff (hφ : NonModal φ) : FalseAt F w φ ↔ φ.tval F w = -1 := by
  rw [FalseAt, eval_eq_ofTrivalent hφ, CCP.Partial.mem_ofTrivalent]
  simp only [Set.mem_singleton_iff, eq_comm (a := (∅ : Set W))]
  cases hv : φ.tval F w <;> simp [Set.eq_empty_iff_forall_notMem, hv]

-- Lemma 10.2
theorem satisfies_iff (hφ : NonModal φ) : Satisfies F σ φ ↔ ∀ w ∈ σ, TrueAt F w φ := by
  simp_rw [trueAt_iff hφ]
  rw [Satisfies, PartialUpdate.supports_iff_mem, eval_eq_ofTrivalent hφ,
    CCP.Partial.mem_ofTrivalent_self]

-- Lemma 10.2
theorem entails_iff (hφ : NonModal φ) (hψ : NonModal ψ) :
    Entails F φ ψ ↔ ∀ w, TrueAt F w φ → TrueAt F w ψ := by
  refine entails_iff_forall.trans ⟨fun h w hw ↦ h {w} {w} hw, fun h σ _ hτ ↦ ?_⟩
  rw [eval_eq_ofTrivalent hφ, CCP.Partial.mem_ofTrivalent] at hτ
  obtain ⟨-, rfl⟩ := hτ
  exact (satisfies_iff hψ).2 fun w hw ↦ h w ((trueAt_iff hφ).2 hw.2)

theorem entails_iff_satisfies (hφ : NonModal φ) (hψ : NonModal ψ) :
    Entails F φ ψ ↔ ∀ σ, Satisfies F σ φ → Satisfies F σ ψ :=
  ⟨fun h σ hs ↦ entails_iff_forall.1 h σ σ hs,
   fun h ↦ (entails_iff hφ hψ).2 fun w hw ↦ h {w} hw⟩

/-- The update and trivalent entailments coincide on PL+∂ (Fact 10.3). -/
theorem entails_iff_tval (hφ : NonModal φ) (hψ : NonModal ψ) :
    Entails F φ ψ ↔ ∀ w, φ.tval F w = 1 → ψ.tval F w = 1 := by
  rw [entails_iff hφ hψ]
  exact forall_congr' fun w ↦ imp_congr (trueAt_iff hφ) (trueAt_iff hψ)

theorem Presupposes.entails (h : Presupposes F φ ψ) (hψ : NonModal ψ) : Entails F φ ψ :=
  entails_iff_forall.2 fun σ _ hτ ↦ (satisfies_iff hψ).2 fun w hw ↦
    (satisfies_iff hψ).1 (h σ (admits_of_mem hτ)) w (eval_eliminative φ hτ hw)

theorem presupposes_iff_strawsonPresupposes (hφ : NonModal φ) (hψ : NonModal ψ) :
    Presupposes F φ ψ ↔ StrawsonPresupposes (φ.tval F) (ψ.tval F) := by
  rw [presupposes_iff_forall]
  simp only [StrawsonPresupposes, admits_iff hφ, satisfies_iff hψ, trueAt_iff hψ]
  exact ⟨fun h w hw ↦ h {w} (by simpa using hw) w rfl, fun h σ hσ w hw ↦ h w (hσ w hw)⟩

theorem presupposes_iff (hφ : NonModal φ) (hψ : NonModal ψ) :
    Presupposes F φ ψ ↔ Entails F φ ψ ∧ Entails F (not φ) ψ := by
  refine ⟨fun h ↦ ⟨h.entails hψ, h.not.entails hψ⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  rw [entails_iff_tval hφ hψ] at h₁
  rw [entails_iff_tval hφ.not hψ] at h₂
  rw [presupposes_iff_strawsonPresupposes hφ hψ]
  intro w hw
  cases hv : φ.tval F w with
  | pos => exact h₁ w hv
  | neg => exact h₂ w (show -φ.tval F w = 1 by rw [hv]; rfl)
  | zero => exact absurd hv hw

end Formula

/-! ### The book's examples -/

open Formula

/-- The atomic formulae of the examples, with the book's names where it prints a translation. -/
inductive Atom
  /-- Bertha is hiding, the book's `bih`. -/
  | hiding
  /-- Anna has come to believe that Bertha is hiding, `cb_a_bih`. -/
  | believesHiding
  /-- Anna will find Bertha, `awfb`. -/
  | findsHer
  /-- Bertha has negative vibes arising from her belief that Anna realises she is hiding,
  `NVB_B_(∂_bih&cb_a_bih)`. -/
  | regrets
  /-- Bertha is in the kitchen, which E175 writes `bc`. -/
  | inKitchen
  /-- Bertha is in the attic, `ba`. -/
  | inAttic
  /-- Anna has come to believe that Bertha is in the attic, `cb_a_ba`. -/
  | believesInAttic
  /-- Spaceman Spiff lands on Planet X. -/
  | lands
  /-- Spiff's weight is greater than it would be on Earth. -/
  | heavier
  /-- Spiff is bothered by it. -/
  | bothered
  /-- Spiff won't stay long. -/
  | leaves
  deriving DecidableEq

/-- The term model over the atomic formulae `P` (D23), whose worlds are sets of atoms, an atom
holding at the worlds containing it. -/
def termModel (P : Type*) : P → Set (Set P) := fun p ↦ {w | p ∈ w}

theorem e154 (F : Atom → Set W) :
    Presupposes F (implies (atom .lands) (and (presup (atom .heavier)) (atom .bothered)))
      (implies (atom .lands) (atom .heavier)) :=
  (presup_and_presupposes _ _).implies_right

theorem e154_not_unconditional :
    ¬Presupposes (termModel Atom)
      (implies (atom .lands) (and (presup (atom .heavier)) (atom .bothered))) (atom .heavier) := by
  rw [presupposes_iff_strawsonPresupposes
    ((NonModal.atom _).implies ((NonModal.atom _).presup.and (.atom _))) (.atom _)]
  intro h
  have := h ∅ (by simp [tval, implies, termModel])
  simp [tval, termModel] at this

theorem e156 (F : Atom → Set W) :
    Presupposes F
      (implies (and (atom .lands) (and (presup (atom .heavier)) (atom .bothered))) (atom .leaves))
      (implies (atom .lands) (atom .heavier)) :=
  (presup_and_presupposes _ _).and_right.implies_left

/-- The translations of §6.5, keyed by their printed form. -/
def translations : List (String × Formula Atom) :=
  let realises := and (presup (atom .hiding)) (atom .believesHiding)
  [("bih", atom .hiding),
   ("bih AND cb_a_bih", and (atom .hiding) (atom .believesHiding)),
   ("ba", atom .inAttic),
   ("(NOT bc) IMPLIES ba", implies (not (atom .inKitchen)) (atom .inAttic)),
   ("∂bih AND cb_a_bih", realises),
   ("NOT (∂bih AND cb_a_bih)", not realises),
   ("(∂bih AND cb_a_bih) IMPLIES awfb", implies realises (atom .findsHer)),
   ("MIGHT(∂bih AND cb_a_bih)", might realises),
   ("∂(∂bih AND cb_a_bih) AND NVB_B_(∂_bih&cb_a_bih)", and (presup realises) (atom .regrets)),
   ("(NOT bc) IMPLIES (∂ba AND cb_a_ba)",
     implies (not (atom .inKitchen)) (and (presup (atom .inAttic)) (atom .believesInAttic))),
   ("bih IMPLIES (∂bih AND cb_a_bih)", implies (atom .hiding) realises),
   ("MIGHT(bih AND ∂bih AND cb_a_bih)", might (and (atom .hiding) realises))]

/-- The entailments the book prints for its translations (E168c, E169c, E172c, E173c, E174c,
E175d) hold in every model, each translation presupposing what it entails. -/
theorem entailed_rows (F : Atom → Set W) : ∀ row ∈ Examples.all,
    ∀ φ ∈ row.parse? "translation" translations, ∀ ψ ∈ row.parse? "entails" translations,
      Entails F φ ψ := by
  have hR := (NonModal.atom Atom.hiding).presup.and (.atom .believesHiding)
  simp only [Examples.all, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  and_intros <;> simp [Datum.parse?, Datum.feature?, translations, List.lookup, Examples.e52,
    Examples.e154, Examples.e155, Examples.e156, Examples.e168, Examples.e169, Examples.e172,
    Examples.e173, Examples.e174, Examples.e175, Examples.e176, Examples.e177, Examples.e206,
    Examples.e207]
  exacts [(presup_and_presupposes _ _).entails (.atom _),
    (presup_and_presupposes _ _).not.entails (.atom _),
    (presup_and_presupposes _ _).implies_left.entails (.atom _),
    (presup_and_presupposes _ _).might.entails (.atom _),
    DynamicSemantics.Entails.trans ((presup_and_presupposes _ _).entails hR)
      ((entails_iff_tval hR ((NonModal.atom _).and (.atom _))).2 fun w ↦ by
        simp [tval, SignType.meetMiddle_eq_one_iff]),
    (presup_and_presupposes _ _).implies_right.entails
      ((NonModal.atom _).not.implies (.atom _))]

/-- The non-entailments it prints (E175c, E176c, E177c) fail in the term model. -/
theorem unentailed_rows : ∀ row ∈ Examples.all,
    ∀ φ ∈ row.parse? "translation" translations, ∀ ψ ∈ row.parse? "doesNotEntail" translations,
      ¬Entails (termModel Atom) φ ψ := by
  have hR := (NonModal.atom Atom.hiding).presup.and (.atom .believesHiding)
  simp only [Examples.all, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  and_intros <;> simp [Datum.parse?, Datum.feature?, translations, List.lookup, Examples.e52,
    Examples.e154, Examples.e155, Examples.e156, Examples.e168, Examples.e169, Examples.e172,
    Examples.e173, Examples.e174, Examples.e175, Examples.e176, Examples.e177, Examples.e206,
    Examples.e207]
  · rw [entails_iff_tval ((NonModal.atom _).not.implies ((NonModal.atom _).presup.and (.atom _)))
      (.atom _)]
    intro h
    have := h {.inKitchen} (by simp [tval, implies, termModel])
    simp [tval, termModel] at this
  · rw [entails_iff_tval ((NonModal.atom _).implies hR) (.atom _)]
    intro h
    have := h ∅ (by simp [tval, implies, termModel])
    simp [tval, termModel] at this
  · rw [entails_iff_forall]
    intro h
    obtain ⟨σ, hσ⟩ : ∃ σ : Set (Set Atom), σ = {∅, {.hiding, .believesHiding}} := ⟨_, rfl⟩
    have hs : Satisfies (termModel Atom) σ (atom .hiding) := by
      refine h σ σ ((satisfies_might_iff ⟨∅, by simp [hσ]⟩).2 ?_)
      rw [ConsistentWith, eval_eq_ofTrivalent ((NonModal.atom _).and hR)]
      simp only [CCP.Partial.mem_ofTrivalent]
      refine ⟨_, ⟨?_, rfl⟩, {.hiding, .believesHiding}, ?_⟩ <;>
        simp [hσ, tval, termModel, Set.insert_subset_iff]
    have := (satisfies_iff (.atom _)).1 hs ∅ (by simp [hσ])
    simp [trueAt_iff (NonModal.atom _), tval, termModel] at this

theorem e177_admits (F : Atom → Set W) (σ : Set W) :
    ∀ φ ∈ Examples.e177.parse? "translation" translations, (φ.eval F).Admits σ := by
  intro φ hφ
  simp [Datum.parse?, Datum.feature?, translations, List.lookup, Examples.e177] at hφ
  subst hφ
  refine (admits_iff ((NonModal.atom _).and ((NonModal.atom _).presup.and (.atom _)))).2
    fun w _ ↦ ?_
  by_cases hw : w ∈ F .hiding <;>
    simp [tval, hw, SignType.meetMiddle_one_left, SignType.meetMiddle_neg_one_left]

end Beaver2001
