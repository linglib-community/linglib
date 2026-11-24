module

public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Zwarts2005
public import Linglib.Semantics.Space.Denotation
public import Linglib.Languages.English.Adpositions
public import Mathlib.Data.List.Infix
public import Linglib.Semantics.Mereology.Basic
public import Mathlib.Tactic.FinCases

/-!
# Zwarts (2005): Prepositional Aspect and the Algebra of Paths

A directional prepositional phrase such as *to the house* denotes a set of paths. A *path* is a
finite sequence of locations, and two paths *concatenate* if the first ends where the second
starts. A set of paths is *cumulative* if it has two paths that concatenate and it is closed
under concatenation. It is *bounded* if it is not cumulative.

We define the denotations of goal, source and route phrases and of *towards* and *away from*. A
goal phrase holds of the paths that enter a region, a source phrase of the paths that leave it,
and a route phrase of the paths that cross it. We prove that these three denotations are bounded
and that the denotation of *towards* is cumulative. The main result,
`Zwarts2005.bounded_iff_telic`, says that a phrase among the paper's examples is bounded if and
only if the paper judges its sentence telic.

We also prove that a goal phrase is not quantized, and that the set of loops at a location is
cumulative although it is telic in Krifka's sense. Finally, suppose that the trace of events is a
homomorphism for concatenation. Then a verb phrase is bounded if its prepositional phrase has no
two paths that concatenate, as in *walk to the house*.

The goal and source phrases agree with the English language file. The paths that the spatial
functions
of *to* and *from* describe, as locatives, are the paths of the strict goal and source phrases.

## Implementation notes

The strict denotations of goal, source and route phrases are `Order.Enters`, `Order.Leaves` and
`Order.Crosses`, applied to a path and the region of the phrase. The positions of a path inside
the region form a proper nonempty interval.

The trace of events respects a partial concatenation of events and not an unrestricted sum.

## TODO

* The minimality operator and the grinder operator.

## References

* [zwarts-2005]
* [krifka-1998]
-/

@[expose] public section

namespace Zwarts2005

open Mereology (QUA)

variable {Loc α : Type*}

/-! ### Paths -/

/-- A path is the finite sequence of locations it visits, a series with no condition on its
steps. -/
abbrev Path (Loc : Type*) := RelSeries (Set.univ : SetRel Loc Loc)

/-- The path through the locations `a :: l`, in order. -/
def Path.ofPoints (a : Loc) (l : List Loc) : Path Loc where
  length := l.length
  toFun i := (a :: l).get ⟨i, by have := i.2; simp; omega⟩
  step _ := trivial

@[simp] theorem Path.head_ofPoints (a : Loc) (l : List Loc) : (Path.ofPoints a l).head = a := rfl

@[simp] theorem Path.toList_ofPoints (a : Loc) (l : List Loc) :
    (Path.ofPoints a l).toList = a :: l := by
  refine List.ext_getElem (by simp [RelSeries.toList, Path.ofPoints]) fun i h₁ h₂ ↦ ?_
  simp [RelSeries.toList, Path.ofPoints]

/-- `p` is a subpath of `q` when the locations of `p` are a stretch of those of `q`. -/
scoped instance instSubpathOrder : PartialOrder (Path Loc) where
  le p q := p.toList <:+: q.toList
  le_refl _ := List.infix_refl _
  le_trans _ _ _ := List.IsInfix.trans
  le_antisymm _ _ h h' := RelSeries.toList_injective (List.infix_antisymm h h')

theorem Path.le_iff_infix {p q : Path Loc} : p ≤ q ↔ p.toList <:+: q.toList := .rfl

theorem Path.singleton_le_iff {x : Loc} {p : Path Loc} : RelSeries.singleton _ x ≤ p ↔ x ∈ p := by
  rw [Path.le_iff_infix, RelSeries.toList_singleton, List.singleton_infix_iff,
    RelSeries.mem_toList]

/-! ### Cumulativity and boundedness (17b), (21)

Stated over an arbitrary ternary concatenation relation: §3.2 transfers closure properties along a
homomorphism from an event algebra with an operation of the same shape. -/

/-- A set is cumulative, (17b), when some concatenation exists within it, the non-vacuity clause
of fn. 7, and it is closed under concatenation. -/
def Cumulative (C : α → α → α → Prop) (X : Set α) : Prop :=
  (∃ p ∈ X, ∃ q ∈ X, ∃ r, C p q r) ∧
    ∀ p ∈ X, ∀ q ∈ X, ∀ r, C p q r → r ∈ X

/-- A set is bounded, (21), when it is not cumulative. -/
def Bounded (C : α → α → α → Prop) (X : Set α) : Prop :=
  ¬ Cumulative C X

theorem bounded_of_no_pairs {C : α → α → α → Prop} {X : Set α}
    (h : ¬ ∃ p ∈ X, ∃ q ∈ X, ∃ r, C p q r) : Bounded C X :=
  fun hc ↦ h hc.1

/-- Concatenation of paths as a relation: `Concat p q r` when `p` ends where `q` starts and `r`
is their concatenation, `RelSeries.smash`. -/
def Concat (p q r : Path Loc) : Prop := ∃ h : p.last = q.head, r = p.smash q h

/-! ### Quantization and Krifka-telicity are the wrong notions (§3.1)

(22) transplants [krifka-1998]'s quantization and telicity to path sets;
Zwarts shows neither characterizes boundedness. Quantization is
`Mereology.QUA` over the subpath order. -/

/-- A path set is telic in Krifka's sense, (22b), when comparable members share both endpoints. -/
def TelicK (X : Set (Path Loc)) : Prop :=
  ∀ p ∈ X, ∀ q ∈ X, p ≤ q → p.head = q.head ∧ p.last = q.last

theorem quantized_telicK {X : Set (Path Loc)} (h : QUA X) :
    TelicK X := by
  intro p hp q hq hle
  rcases eq_or_ne p q with rfl | hne
  · exact ⟨rfl, rfl⟩
  · exact absurd hle (h hp hq hne)

/-- `loops A` is the *round and round the block* set of non-constant loops at `A`, those that leave
`A` somewhere along the way. -/
def loops (A : Loc) : Set (Path Loc) :=
  {p | p.head = A ∧ p.last = A ∧ ∃ x ∈ p, x ≠ A}

theorem loops_telicK (A : Loc) : TelicK (loops (Loc := Loc) A) :=
  fun _ hp _ hq _ ↦ ⟨hp.1.trans hq.1.symm, hp.2.1.trans hq.2.1.symm⟩

/-- Loop sets are cumulative, so Krifka's telicity (22b) does not characterize boundedness. -/
theorem loops_cumulative [Nontrivial Loc] (A : Loc) :
    Cumulative Concat (loops (Loc := Loc) A) := by
  obtain ⟨B, hB⟩ := exists_ne A
  constructor
  · have h : Path.ofPoints A [B, A] ∈ loops A := ⟨rfl, rfl, B, ⟨1, rfl⟩, hB⟩
    exact ⟨_, h, _, h, _, ⟨rfl, rfl⟩⟩
  · rintro p hp q hq r ⟨h, rfl⟩
    obtain ⟨hs, -, x, hx, hxA⟩ := hp
    exact ⟨by simpa using hs, by simpa using hq.2.1, x, RelSeries.mem_smash_of_mem_left h hx, hxA⟩

-- p. 776
theorem const_le_const_iff {a b : Loc} :
    (RelSeries.singleton _ a : Path Loc) ≤ RelSeries.singleton _ b ↔ a = b :=
  Path.singleton_le_iff.trans (by simp [RelSeries.mem_def, eq_comm])

/-! ### Goal and source prepositions (§4.1.1) -/

/-- The weak goal-phrase denotation, (30c), (33), holds of the paths ending in the region. -/
def weakTo (R : Set Loc) : Set (Path Loc) := {p | p.last ∈ R}

theorem weakTo_cumulative {R : Set Loc} {x : Loc} (hx : x ∈ R) :
    Cumulative Concat (weakTo R) :=
  ⟨⟨RelSeries.singleton _ x, hx, RelSeries.singleton _ x, hx, _, rfl, rfl⟩,
    fun _ _ _ hq _ ⟨_, hr⟩ ↦ by subst hr; simpa [weakTo] using hq⟩

/-- The strict goal phrase, (35), (36): the positions in the region form an interval including the
last position and, being a proper interval, not the first. The goal prepositions differ only in
the region. -/
def toPP (R : Set Loc) : Set (Path Loc) := {p | Order.Enters p R}

/-- The strict source phrase, (36), including the first position and not the last. -/
def fromPP (R : Set Loc) : Set (Path Loc) := {p | Order.Leaves p R}

theorem toPP_subset_weakTo (R : Set Loc) : toPP R ⊆ weakTo R :=
  fun p hp ↦ (p.apply_top ▸ hp.2.2 : p.last ∈ R)

-- (35)
theorem toPP_no_pairs (R : Set Loc) :
    ¬ ∃ p ∈ toPP R, ∃ q ∈ toPP R, ∃ r, Concat p q r := by
  rintro ⟨p, hp, q, hq, r, hr⟩
  exact hq.2.1 (by rw [RelSeries.apply_bot, ← hr.fst, ← RelSeries.apply_top]; exact hp.2.2)

-- (36)
theorem fromPP_no_pairs (R : Set Loc) :
    ¬ ∃ p ∈ fromPP R, ∃ q ∈ fromPP R, ∃ r, Concat p q r := by
  rintro ⟨p, hp, q, hq, r, hr⟩
  exact hp.2.2 (by rw [RelSeries.apply_top, hr.fst, ← RelSeries.apply_bot]; exact hq.2.1)

-- (21)
theorem toPP_bounded (R : Set Loc) : Bounded Concat (toPP R) :=
  bounded_of_no_pairs (toPP_no_pairs R)

-- (12a), (36)
theorem fromPP_bounded (R : Set Loc) : Bounded Concat (fromPP R) :=
  bounded_of_no_pairs (fromPP_no_pairs R)

-- The spatial functions of English *to* and *from* describe the paths of the strict goal and
-- source phrases.
theorem mem_paths_to_from [Preorder α] (place : Option Locative.Configuration → Set Loc → Set Loc)
    (d : Loc → α) (G : Set Loc) (p : Path Loc) :
    (∀ f ∈ English.Adpositions.to_.functions, f.kind = .spatial →
      (⇑p ∈ Locative.paths place d (.ofFunction f) G ↔ p ∈ toPP (place (some .exterior) G))) ∧
    (∀ f ∈ English.Adpositions.from_.functions, f.kind = .spatial →
      (⇑p ∈ Locative.paths place d (.ofFunction f) G ↔
        p ∈ fromPP (place (some .exterior) G))) := by
  refine ⟨fun f hf hk ↦ ?_, fun f hf hk ↦ ?_⟩
  · simp only [English.Adpositions.to_, Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl
    · exact Iff.rfl
    · exact absurd hk (by decide)
    · exact absurd hk (by decide)
  · simp only [English.Adpositions.from_, Finset.mem_singleton] at hf
    subst hf
    exact Iff.rfl

/-! ### Route prepositions (§4.1.2) -/

/-- The strict route phrase, (39), (40): the positions in the region form an interval including
neither the first nor the last position. -/
def overPP (R : Set Loc) : Set (Path Loc) := {p | Order.Crosses p R}

-- (39)
theorem overPP_exists_pair {R : Set Loc} {x a : Loc} (hx : x ∈ R) (ha : a ∉ R) :
    ∃ p ∈ overPP R, ∃ q ∈ overPP R, ∃ r, Concat p q r := by
  have hp : Path.ofPoints a [x, a] ∈ overPP R := by
    have key : ∀ i : Fin 3, Path.ofPoints a [x, a] i ∈ R ↔ i = 1 := by
      intro i; fin_cases i <;> simp [Path.ofPoints, hx, ha]
    refine ⟨?_, ⟨1, hx⟩, ha, ha⟩
    rw [show (Path.ofPoints a [x, a]).toFun ⁻¹' R = {1} from Set.ext key]
    exact Set.ordConnected_singleton
  exact ⟨_, hp, _, hp, _, rfl, rfl⟩

/-- A route phrase is bounded, (39), since a concatenation of its paths enters the region
twice. -/
theorem overPP_bounded (R : Set Loc) : Bounded Concat (overPP R) := by
  rintro ⟨⟨p, hp, q, hq, _, h, rfl⟩, hc⟩
  have := Order.Crosses.entries_eq (hc p hp q hq _ ⟨h, rfl⟩)
  rw [RelSeries.entries_smash, Order.Crosses.entries_eq hp, Order.Crosses.entries_eq hq]
    at this
  exact absurd this (by decide)

/-! ### Towards and away from (§4.1.3)

The comparative definitions over a distance measure `d` to the reference object are cumulative,
hence unbounded, which grounds the atelic marking of the comparative prepositions. -/

/-- *Towards x*, (45), holds of a path that ends nearer to the reference object than it starts,
measured by `d`. -/
def towardsPP [Preorder α] (d : Loc → α) : Set (Path Loc) :=
  {p | d p.last < d p.head}

/-- *Away from x*, (48), holds of a path that ends further from the reference object than it
starts. -/
def awayFromPP [Preorder α] (d : Loc → α) : Set (Path Loc) :=
  {p | d p.head < d p.last}

theorem towardsPP_concat_closed [Preorder α] (d : Loc → α) :
    ∀ p ∈ towardsPP d, ∀ q ∈ towardsPP d, ∀ r, Concat p q r →
      r ∈ towardsPP d := by
  intro p hp q hq r hr
  show d r.last < d r.head
  obtain ⟨h, rfl⟩ := hr
  rw [RelSeries.last_smash, RelSeries.head_smash]
  exact hq.trans_le (h ▸ hp.le)

theorem awayFromPP_concat_closed [Preorder α] (d : Loc → α) :
    ∀ p ∈ awayFromPP d, ∀ q ∈ awayFromPP d, ∀ r, Concat p q r →
      r ∈ awayFromPP d := by
  intro p hp q hq r hr
  show d r.head < d r.last
  obtain ⟨h, rfl⟩ := hr
  rw [RelSeries.last_smash, RelSeries.head_smash]
  exact hp.trans_le (h ▸ hq.le)

-- (45)
theorem towardsPP_cumulative [Preorder α] {d : Loc → α} {a b c : Loc} (hab : d b < d a)
    (hbc : d c < d b) : Cumulative Concat (towardsPP d) :=
  ⟨⟨Path.ofPoints a [b], hab, Path.ofPoints b [c], hbc, _, rfl, rfl⟩, towardsPP_concat_closed d⟩

-- (45)
theorem toPP_subset_towardsPP [Preorder α] {d : Loc → α} {R : Set Loc}
    (hd : ∀ x ∈ R, ∀ y ∉ R, d x < d y) : toPP R ⊆ towardsPP d :=
  fun _ hp ↦ hd _ (toPP_subset_weakTo R hp) _ hp.2.1

/-- Bounded phrases are not quantized, (23)–(24), since a *to x* path has proper subpaths that are
also *to x*, against the [krifka-1998] characterization of telicity. -/
theorem toPP_not_quantized {x a b : Loc} (ha : a ≠ x) (hb : b ≠ x) :
    ¬ QUA (toPP ({x} : Set Loc)) := by
  intro h
  have hp : Path.ofPoints a [x] ∈ toPP {x} := by
    have key : ∀ i : Fin 2, Path.ofPoints a [x] i ∈ ({x} : Set Loc) ↔ i = ⊤ := by
      intro i; fin_cases i <;> simp [Path.ofPoints, ha, Fin.top_eq_last]
    exact Order.Reaches.enters ⟨Set.ext key, (by decide : (⊥ : Fin 2) ≠ ⊤)⟩
  have hq : Path.ofPoints b [a, x] ∈ toPP {x} := by
    have key : ∀ i : Fin 3, Path.ofPoints b [a, x] i ∈ ({x} : Set Loc) ↔ i = ⊤ := by
      intro i; fin_cases i <;> simp [Path.ofPoints, ha, hb, Fin.top_eq_last, Fin.ext_iff]
    exact Order.Reaches.enters ⟨Set.ext key, (by decide : (⊥ : Fin 3) ≠ ⊤)⟩
  exact h hp hq (fun he ↦ by simpa [Path.ofPoints] using congrArg RelSeries.length he)
    (Path.le_iff_infix.mpr ⟨[b], [], by simp⟩)

/-! ### The judgments (1), (23) -/

/-- The kinds of directional phrase among the paper's examples. -/
inductive Phrase
  | goal
  | source
  | route
  | towards
  deriving DecidableEq

/-- The denotation of a phrase, relative to the region of its locative basis and a measure of
distance to its reference object. -/
def Phrase.denotation [Preorder α] (R : Set Loc) (d : Loc → α) : Phrase → Set (Path Loc)
  | .goal => toPP R
  | .source => fromPP R
  | .route => overPP R
  | .towards => towardsPP d

/-- The kind of phrase a row's preposition heads. -/
def prepositions : List (String × Phrase) :=
  [("to", .goal), ("out of", .source), ("over", .route), ("towards", .towards)]

/-- A row's phrase is bounded exactly when the paper judges its sentence telic, given a region and
a measure on which *towards* has paths to concatenate. -/
theorem bounded_iff_telic [Preorder α] {d : Loc → α} {a b c : Loc} (hab : d b < d a)
    (hbc : d c < d b) (R : Set Loc) :
    ∀ e ∈ Examples.all, ∀ ph ∈ e.parse? "preposition" prepositions,
      ∀ t ∈ e.parse? "aspect" [("telic", true), ("atelic", false)],
        (Bounded Concat (ph.denotation R d) ↔ t = true) := by
  have key : ∀ ph : Phrase, Bounded Concat (ph.denotation R d) ↔ ph ≠ .towards := by
    rintro (_ | _ | _ | _)
    · exact iff_of_true (toPP_bounded R) (by decide)
    · exact iff_of_true (fromPP_bounded R) (by decide)
    · exact iff_of_true (overPP_bounded R) (by decide)
    · exact iff_of_false (not_not.2 (towardsPP_cumulative hab hbc)) (by decide)
  simp only [key]
  decide

/-! ### Plural PPs: the star operator (§4.2.2) -/

/-- The star closure of a path set, (58), closes it under concatenation, the prepositional
plurality of *round and round the house*. -/
inductive Star (X : Set (Path Loc)) : Path Loc → Prop
  | base {p} (hp : p ∈ X) : Star X p
  | concat {p q r} (hp : Star X p) (hq : Star X q) (h : Concat p q r) :
      Star X r

-- (58)
theorem star_cumulative {X : Set (Path Loc)}
    (h : ∃ p ∈ X, ∃ q ∈ X, ∃ r, Concat p q r) :
    Cumulative Concat {p | Star X p} := by
  obtain ⟨p, hp, q, hq, r, hr⟩ := h
  exact ⟨⟨p, .base hp, q, .base hq, r, hr⟩,
    fun _ hp' _ hq' _ hr' ↦ .concat hp' hq' hr'⟩

/-! ### Aspect transfer to the VP (§3.2) -/

section Transfer

variable {E : Type*} (σ : E → Path Loc) (C : E → E → E → Prop)

/-- The spatial trace `σ` is a homomorphism for concatenation when the trace of a fused event is
the concatenation of the traces. -/
def IsTraceHom : Prop :=
  ∀ e e' f, C e e' f → Concat (σ e) (σ e') (σ f)

/-- `⟦V PP⟧`, (25), holds of the verb's events whose trace lies in the phrase's denotation. -/
def vpp (V : Set E) (X : Set (Path Loc)) : Set E :=
  {e ∈ V | σ e ∈ X}

variable {σ C}

theorem vpp_concat_closed (hhom : IsTraceHom σ C) {V : Set E}
    {X : Set (Path Loc)}
    (hV : ∀ e ∈ V, ∀ e' ∈ V, ∀ f, C e e' f → f ∈ V)
    (hX : ∀ p ∈ X, ∀ q ∈ X, ∀ r, Concat p q r → r ∈ X) :
    ∀ e ∈ vpp σ V X, ∀ e' ∈ vpp σ V X, ∀ f, C e e' f → f ∈ vpp σ V X :=
  fun e he e' he' f hf ↦
    ⟨hV e he.1 e' he'.1 f hf, hX _ he.2 _ he'.2 _ (hhom e e' f hf)⟩

theorem vpp_bounded_of_no_pairs (hhom : IsTraceHom σ C) {V : Set E}
    {X : Set (Path Loc)}
    (hX : ¬ ∃ p ∈ X, ∃ q ∈ X, ∃ r, Concat p q r) :
    Bounded C (vpp σ V X) :=
  bounded_of_no_pairs fun ⟨e, he, e', he', f, hf⟩ ↦
    hX ⟨σ e, he.2, σ e', he'.2, σ f, hhom e e' f hf⟩

/-- *Walk to the house* is bounded, (26), by the negative transfer at the strict goal phrase. -/
theorem vpp_toPP_bounded (hhom : IsTraceHom σ C) {V : Set E} (R : Set Loc) :
    Bounded C (vpp σ V (toPP R)) :=
  vpp_bounded_of_no_pairs hhom (toPP_no_pairs R)

end Transfer

end Zwarts2005
