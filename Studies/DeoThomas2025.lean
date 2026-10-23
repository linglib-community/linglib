module

public import Linglib.Semantics.Questions.Partition.Inquisitive
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Data.Examples.DeoThomas2025
public import Linglib.Semantics.Degree.Granularity
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Deo and Thomas (2025): Addressing the widest answerable question

Deo and Thomas analyse English *just* as a domain-widening strategy. Besides the uses it shares
with *only*, *just* has emphatic, precisifying, minimal-sufficiency, unexplanatory, unelaboratory
and counterexpectational uses, in some of which its prejacent answers no standard construal of the
current question. The account replaces the current question by an underspecified question, the
set of a question's construals at a context, and compares construals by width, which is weaker
than question entailment. *Just* presupposes that the current question is the widest construal
that the speaker can answer truthfully and relevantly, and asserts its prejacent.

## Main definitions

* `DeoThomas2025.WiderThan`: the width order on construals, (32).
* `DeoThomas2025.Context.IsOptimal`: the widest answerable construal, (35).
* `DeoThomas2025.just`: the lexical entry, (36).

## Main results

* `DeoThomas2025.Context.IsOptimal.widest_or_quality_or_relevance`: the three kinds of context in
  which a construal is optimal, (37).
* `DeoThomas2025.Context.isOptimal_ofSet_iff`: the unexplanatory and unelaboratory uses, §4.4
  and §4.5.
* `DeoThomas2025.widerThan_fromSetoid`: a finer partition is a wider construal, §4.2 and §4.7.
* `DeoThomas2025.widerThan_grain`, `DeoThomas2025.figure1`: a finer grain is wider without
  refining the coarser one, so width is not entailment, Figure 1 and fn. 20.
* `DeoThomas2025.widerThan_zone`: extreme adjectives, Figure 2 of §4.8.
* `DeoThomas2025.widerThan_mentionAll`: mention-all is wider than mention-some, §4.1.

## Implementation notes

A construal is a `Question`, whose alternatives `Question.alt` are the maximal resolving
states, so (30a) holds by construction and (30b) is `Question.info`. The context of (31)
carries the common ground, the construals, and the speaker's Quality and Relevance verdicts
as primitives, with the paper's requirements that every construal cover the common ground
and that any two construals be comparable by width, which is what makes the optimal construal
unique. Partition construals are `Question.fromSetoid`, so refinement is the order on
`Setoid`. Grains are `Degree.grain`, whose cells are centred on the multiples of
the width, so that a measure phrase denotes the cell it lies at the centre of, (24); Figure 1's
year and half-year grains are `grain 1` and `grain (1 / 2)` on `ℝ`. Worlds for the constituent
question of §4.1 are the extensions of its predicate. The exhaustive interpretation of the
prejacent is a mandatory implicature that the paper leaves to Gricean reasoning, §4.1 and §4.9,
and is not formalized; neither are the interpretation of the prejacent relative to the
granularity of the current question in (36), the minimal-sufficiency construal of §4.3, whose
alternatives are fixed by a causal structure, nor the Focus Principle, (21).

## References

* [deo-thomas-2025]
* [thomas-deo-2020]
* [beaver-clark-2008]
* [coppock-beaver-2014]
* [ciardelli-groenendijk-roelofsen-2018]
* [groenendijk-stokhof-1984]
* [morzycki-2012]
* [wiegand-2018]
* [warstadt-2020]
-/

@[expose] public section

namespace DeoThomas2025

open Question

variable {W : Type*}

/-! ### Width, (32) -/

/-- `P` is wider than `Q`, (32), when the two cover the same common ground, no alternative of `Q` is
properly contained in an alternative of `P`, and some alternative of `P` is properly contained in an
alternative of `Q`. -/
def WiderThan (P Q : Question W) : Prop :=
  P.info = Q.info ∧ (∀ q ∈ alt Q, ∀ p ∈ alt P, ¬ q ⊂ p) ∧ ∃ p ∈ alt P, ∃ q ∈ alt Q, p ⊂ q

theorem WiderThan.irrefl (P : Question W) : ¬ WiderThan P P :=
  fun ⟨_, h, p, hp, q, hq, hpq⟩ ↦ h p hp q hq hpq

theorem WiderThan.asymm {P Q : Question W} (h : WiderThan P Q) : ¬ WiderThan Q P :=
  fun ⟨_, h', _⟩ ↦ let ⟨p, hp, q, hq, hpq⟩ := h.2.2; h' p hp q hq hpq

/-- The trivial construal, the disjunction of all possible causes of §4.4, is narrower than any
other construal of the same common ground. -/
theorem widerThan_ofSet {P : Question W} {s p : Set W} (hs : P.info = s) (hp : p ∈ alt P)
    (hne : p ≠ s) : WiderThan P (ofSet s) := by
  have hsub : ∀ q ∈ alt P, q ⊆ s := fun q hq ↦
    hs ▸ (Set.subset_sUnion_of_mem hq).trans (sUnion_alt_subset_info P)
  refine ⟨by rw [hs, info_ofSet], ?_, p, hp, s, self_mem_alt_ofSet s,
    Set.ssubset_iff_subset_ne.2 ⟨hsub p hp, hne⟩⟩
  rw [alt_ofSet]
  rintro _ rfl q hq hlt
  exact hlt.2 (hsub q hq)

/-! ### The context, (31), and the optimal construal, (33) to (35) -/

/-- A context, (31), carries the common ground, the construals of the underspecified question, each
a cover of the common ground and any two comparable by width, and the speaker's verdicts on which
questions satisfy Quality and Relevance, (34). -/
structure Context (W : Type*) where
  /-- The common ground. -/
  info : Set W
  /-- The construals of the underspecified question. -/
  uq : Set (Question W)
  /-- The speaker has sufficient evidence that a true answer is accessible, (34a). -/
  quality : Question W → Prop
  /-- The speaker considers answering the question relevant to the discourse goals, (34b). -/
  relevance : Question W → Prop
  nonempty : uq.Nonempty
  info_eq : ∀ q ∈ uq, q.info = info
  comparable : ∀ q ∈ uq, ∀ q' ∈ uq, q ≠ q' → WiderThan q q' ∨ WiderThan q' q

namespace Context

variable (c : Context W) (q : Question W)

/-- A question is answerable when it satisfies Quality and Relevance, (34). -/
def Answerable : Prop := c.quality q ∧ c.relevance q

/-- A construal is the widest, (33), when none is wider. -/
def IsWidest : Prop := q ∈ c.uq ∧ ∀ q' ∈ c.uq, ¬ WiderThan q' q

/-- A construal is optimal, (35), when it is answerable and no wider construal is. -/
def IsOptimal : Prop :=
  q ∈ c.uq ∧ c.Answerable q ∧ ∀ q' ∈ c.uq, c.Answerable q' → ¬ WiderThan q' q

variable {c q}

theorem IsWidest.unique {q' : Question W} (h : c.IsWidest q) (h' : c.IsWidest q') : q = q' :=
  by_contra fun hne ↦ (c.comparable q h.1 q' h'.1 hne).elim (h'.2 q h.1) (h.2 q' h'.1)

/-- The optimal construal is unique, as the definite description of (35) requires. -/
theorem IsOptimal.unique {q' : Question W} (h : c.IsOptimal q) (h' : c.IsOptimal q') :
    q = q' :=
  by_contra fun hne ↦
    (c.comparable q h.1 q' h'.1 hne).elim (h'.2.2 q h.1 h.2.1) (h.2.2 q' h'.1 h'.2.1)

/-- The widest construal, when answerable, is the optimal one, (37a). -/
theorem IsWidest.isOptimal (h : c.IsWidest q) (ha : c.Answerable q) : c.IsOptimal q :=
  ⟨h.1, ha, fun q' hq' _ ↦ h.2 q' hq'⟩

theorem IsOptimal.not_answerable {q' : Question W} (h : c.IsOptimal q) (hq' : q' ∈ c.uq)
    (hw : WiderThan q' q) : ¬ c.Answerable q' :=
  fun ha ↦ h.2.2 q' hq' ha hw

/-- An optimal construal is the widest, or some wider one fails Quality, or some wider one satisfies
Quality but fails Relevance (37). -/
theorem IsOptimal.widest_or_quality_or_relevance (h : c.IsOptimal q) :
    c.IsWidest q ∨ (∃ q' ∈ c.uq, WiderThan q' q ∧ ¬ c.quality q') ∨
      ∃ q' ∈ c.uq, WiderThan q' q ∧ c.quality q' ∧ ¬ c.relevance q' := by
  by_cases hw : c.IsWidest q
  · exact Or.inl hw
  obtain ⟨q', hq', hw'⟩ : ∃ q' ∈ c.uq, WiderThan q' q := by
    by_contra h'
    exact hw ⟨h.1, fun q' hq' hw' ↦ h' ⟨q', hq', hw'⟩⟩
  by_cases hq : c.quality q'
  · exact Or.inr (Or.inr ⟨q', hq', hw', hq, fun hr ↦ h.not_answerable hq' hw' ⟨hq, hr⟩⟩)
  · exact Or.inr (Or.inl ⟨q', hq', hw', hq⟩)

/-- The trivial construal is optimal exactly when it alone is answerable, as in the unexplanatory
and unelaboratory uses (§4.4 and §4.5). -/
theorem isOptimal_ofSet_iff (hmem : ofSet c.info ∈ c.uq)
    (hnt : ∀ q ∈ c.uq, q ≠ ofSet c.info → ∃ p ∈ alt q, p ≠ c.info) :
    c.IsOptimal (ofSet c.info) ↔
      c.Answerable (ofSet c.info) ∧ ∀ q ∈ c.uq, q ≠ ofSet c.info → ¬ c.Answerable q := by
  refine ⟨fun h ↦ ⟨h.2.1, fun q hq hne ha ↦ ?_⟩, fun ⟨ha, h⟩ ↦ ⟨hmem, ha, fun q hq ha' hw ↦ ?_⟩⟩
  · obtain ⟨p, hp, hpne⟩ := hnt q hq hne
    exact h.2.2 q hq ha (widerThan_ofSet (c.info_eq q hq) hp hpne)
  · by_cases hne : q = ofSet c.info
    · exact WiderThan.irrefl _ (hne ▸ hw)
    · exact h q hq hne ha'

end Context

/-! ### The lexical entry, (36) -/

open Classical in
/-- *Just* with the current question `cq` and prejacent `p` presupposes that `cq` is the optimal
construal of the underspecified question and asserts `p`, (36). -/
noncomputable def just (c : Context W) (cq : Question W) (p : Set W) : W → SignType :=
  {_w | c.IsOptimal cq}.indicator fun w ↦ SignType.ofProp (w ∈ p)

variable {c : Context W} {cq cq' : Question W} {p p' : Set W} {w w' : W}

@[simp] theorem just_eq_zero_iff : just c cq p w = 0 ↔ ¬ c.IsOptimal cq := by simp [just]

@[simp] theorem just_eq_one_iff : just c cq p w = 1 ↔ c.IsOptimal cq ∧ w ∈ p := by simp [just]

theorem eq_of_just_ne_zero (h : just c cq p w ≠ 0) (h' : just c cq' p' w' ≠ 0) : cq = cq' := by
  simp only [ne_eq, just_eq_zero_iff, not_not] at h h'
  exact h.unique h'

/-! ### Partitions: refinement is width, §4.2 and §4.7 -/

/-- A finer partition of the common ground is a wider construal, (40b) against (40a). -/
theorem widerThan_fromSetoid {r s : Setoid W} (h : r < s) :
    WiderThan (fromSetoid r) (fromSetoid s) := by
  obtain ⟨hle, hnle⟩ := lt_iff_le_not_ge.1 h
  obtain ⟨x, y, hs, hr⟩ : ∃ x y, s x y ∧ ¬ r x y := by
    by_contra h'
    exact hnle (Setoid.le_def.2 fun {x y} hxy ↦ by_contra fun hr ↦ h' ⟨x, y, hxy, hr⟩)
  have : Nonempty W := ⟨x⟩
  refine ⟨by rw [info_fromSetoid, info_fromSetoid], ?_, {z | r z y},
    mem_alt_fromSetoid_of_mem_classes _ (Setoid.mem_classes r y), {z | s z y},
    mem_alt_fromSetoid_of_mem_classes _ (Setoid.mem_classes s y),
    fun z hz ↦ Setoid.le_def.1 hle hz, fun hsub ↦ hr (hsub hs)⟩
  rw [alt_fromSetoid, alt_fromSetoid]
  rintro _ ⟨v, rfl⟩ _ ⟨u, rfl⟩ hlt
  have huv : s u v := s.symm (Setoid.le_def.1 hle (hlt.1 (s.refl v)))
  exact hlt.2 fun z hz ↦ s.trans (Setoid.le_def.1 hle hz) huv

/-! ### Grains, (22) to (24), and Figure 1 -/

section Grain

open Degree

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

/-- The finer grain is the wider construal ((23), §4.7.1). -/
theorem widerThan_grain {ε₁ ε₂ : α} (h₁ : 0 < ε₁) (h : ε₁ < ε₂) :
    WiderThan (fromSetoid (grain ε₁)) (fromSetoid (grain ε₂)) := by
  have h₂ := h₁.trans h
  have h0 {ε : α} (hε : 0 < ε) : (grain ε).cell 0 = Set.Ico (-(ε / 2)) (ε / 2) := by
    rw [cell_grain hε, representative_eq_self_of_mem_zmultiples hε.ne' (zero_mem _), zero_sub,
      zero_add]
  refine ⟨by rw [info_fromSetoid, info_fromSetoid], ?_, (grain ε₁).cell 0,
    mem_alt_fromSetoid_of_mem_classes _ ((grain ε₁).cell_mem_classes 0), (grain ε₂).cell 0,
    mem_alt_fromSetoid_of_mem_classes _ ((grain ε₂).cell_mem_classes 0), ?_⟩
  · rw [alt_fromSetoid, alt_fromSetoid]
    rintro _ ⟨y, rfl⟩ _ ⟨z, rfl⟩ hlt
    exact (isGranularity_cell h₁).not_subset (isGranularity_cell h₂) h z y hlt.1
  · rw [h0 h₁, h0 h₂, Set.ssubset_iff_of_subset (Set.Ico_subset_Ico (by linarith) (by linarith))]
    exact ⟨ε₁ / 2, ⟨by linarith, by linarith⟩, fun hx ↦ lt_irrefl _ hx.2⟩

/-- In Figure 1, the half-year grain is wider than the year grain without refining it, so width is
not [groenendijk-stokhof-1984]'s entailment (fn. 20). -/
theorem figure1 :
    WiderThan (fromSetoid (grain (1 / 2 : ℝ))) (fromSetoid (grain 1)) ∧
      ¬ grain (1 / 2 : ℝ) ≤ grain 1 ∧ ¬ fromSetoid (grain (1 / 2 : ℝ)) ≤ fromSetoid (grain 1) := by
  have hle : ¬ grain (1 / 2 : ℝ) ≤ grain 1 := by
    simpa using not_grain_le_grain_of_even (ε := (1 / 2 : ℝ)) (by norm_num) one_pos
  exact ⟨widerThan_grain (by norm_num) (by norm_num), hle,
    fun h ↦ hle ((fromSetoid_le_iff _ _).1 h)⟩

end Grain

/-! ### Extreme adjectives, §4.8 -/

/-- The construal of a degree question whose zone of indifference, [morzycki-2012], begins at `m`
distinguishes the degrees below `m` and identifies those from `m` on. -/
def zone (m : ℕ) : Setoid ℕ := Setoid.ker (min · m)

/-- A construal whose zone of indifference begins later is wider (Figure 2). -/
theorem widerThan_zone {m m' : ℕ} (h : m < m') :
    WiderThan (fromSetoid (zone m')) (fromSetoid (zone m)) := by
  refine widerThan_fromSetoid
    (lt_iff_le_not_ge.2 ⟨Setoid.le_def.2 fun {x y} hxy ↦ ?_, fun hle ↦ ?_⟩)
  · have hxy : min x m' = min y m' := hxy
    show min x m = min y m
    omega
  · have hmm : zone m m m' := by
      show min m m = min m' m
      omega
    have := Setoid.le_def.1 hle hmm
    have : min m m' = min m' m' := this
    omega

/-! ### Constituent questions, §4.1 -/

variable {A : Type*}

/-- The mention-all construal of *which x is P?*, over worlds that are extensions of `P`, has one
alternative per nonempty extension. -/
def mentionAll : Question (Set A) := which {E : Set A | E.Nonempty} fun E ↦ {E}

/-- The mention-some construal has one alternative per individual, the worlds in which it is `P`. -/
def mentionSome : Question (Set A) := which Set.univ fun a ↦ {E | a ∈ E}

/-- The mention-all construal of a constituent question is wider than the mention-some one (§4.1).
-/
theorem widerThan_mentionAll [Nontrivial A] :
    WiderThan (mentionAll (A := A)) mentionSome := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  have hall : alt (mentionAll (A := A)) = (fun E ↦ {E}) '' {E : Set A | E.Nonempty} :=
    alt_which_of_forall_subset_eq ⟨{a}, Set.singleton_nonempty a⟩ fun E _ E' _ h ↦ by
      rw [Set.singleton_subset_singleton.1 h]
  have hsome : alt (mentionSome (A := A)) = (fun a ↦ {E | a ∈ E}) '' Set.univ :=
    alt_which_of_forall_subset_eq ⟨a, Set.mem_univ a⟩ fun a _ b _ h ↦ by
      have hba : b = a := h (Set.mem_singleton a)
      rw [hba]
  refine ⟨?_, ?_, {{a}}, hall ▸ ⟨{a}, Set.singleton_nonempty a, rfl⟩, {E | a ∈ E},
    hsome ▸ ⟨a, Set.mem_univ a, rfl⟩, Set.singleton_subset_iff.2 (Set.mem_singleton a),
    fun hsub ↦ ?_⟩
  · ext E
    simp only [mentionAll, mentionSome, info_which, Set.mem_iUnion, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, Set.mem_univ, true_and, exists_prop, exists_eq_right']
    exact Set.nonempty_def
  · rw [hall, hsome]
    rintro _ ⟨x, -, rfl⟩ _ ⟨E, -, rfl⟩ hlt
    have hlt' : {E : Set A | x ∈ E} = ∅ := Set.eq_empty_of_ssubset_singleton hlt
    have hmem : ({x} : Set A) ∈ {E : Set A | x ∈ E} := Set.mem_singleton x
    rw [hlt'] at hmem
    exact Set.notMem_empty _ hmem
  · have hab' : ({a, b} : Set A) = {a} := hsub (show ({a, b} : Set A) ∈ {E | a ∈ E} from
      Set.mem_insert a {b})
    exact hab (hab' ▸ Set.mem_insert_of_mem a (Set.mem_singleton b) : b ∈ ({a} : Set A)).symm

end DeoThomas2025
