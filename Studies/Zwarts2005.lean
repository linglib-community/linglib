module

public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Zwarts2005
public import Linglib.Semantics.Events.Path
public import Linglib.Semantics.Mereology
public import Mathlib.Tactic.FinCases

/-!
# Zwarts (2005): Prepositional Aspect and the Algebra of Paths

Zwarts analyzes the aspect of directional prepositional phrases, which denote sets of paths. A
telic phrase like *to the house* differs from an atelic one like *towards the house* in closure
under the partial concatenation of paths: an atelic phrase is cumulative and a telic one bounded,
that is, not cumulative. [Goal and source phrases](##Zwarts2005.toPP_no_pairs) are bounded because
none of their paths concatenate, and [route phrases](##Zwarts2005.overPP_bounded) because their
concatenations pass through the region twice. Bounded phrases
[are not quantized](##Zwarts2005.toPP_not_quantized), and
[loops are cumulative](##Zwarts2005.loops_cumulative) yet telic in Krifka's sense, so neither
notion characterizes boundedness. A trace homomorphism for concatenation transfers closure from
the phrase to the verb phrase, so [*walk to the house* is bounded](##Zwarts2005.vpp_toPP_bounded).

## Implementation notes

* The strict goal, source and route denotations are the cofinal, coinitial and transitive shapes
  of `Spatial.Path`, relative to the region a preposition's locative basis picks out. Zwarts's
  intervals are proper and nonempty, as his glosses of them say.
* The paper's trace function respects Rothstein's partial event concatenation, not an
  unrestricted mereological sum.

## TODO

* The minimality and grinder operators (63) and (64).

## References

* [zwarts-2005]
* [krifka-1998]
-/

@[expose] public section

namespace Zwarts2005

open Mereology (QUA)
open Spatial
open scoped Spatial.Path

variable {Loc α : Type*}

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

/-! ### Quantization and Krifka-telicity are the wrong notions (§3.1)

(22) transplants [krifka-1998]'s quantization and telicity to path sets;
Zwarts shows neither characterizes boundedness. Quantization is
`Mereology.QUA` over the subpath order. -/

/-- A path set is telic in Krifka's sense, (22b), when comparable members share both endpoints. -/
def TelicK (X : Set (Path Loc)) : Prop :=
  ∀ p ∈ X, ∀ q ∈ X, p ≤ q → p.source = q.source ∧ p.goal = q.goal

theorem quantized_telicK {X : Set (Path Loc)} (h : QUA (· ∈ X)) :
    TelicK X := by
  intro p hp q hq hle
  rcases eq_or_ne p q with rfl | hne
  · exact ⟨rfl, rfl⟩
  · exact absurd hle (h hp hq hne)

/-- `loops A` is the *round and round the block* set of non-constant loops at `A`, those that leave
`A` somewhere along the way. -/
def loops (A : Loc) : Set (Path Loc) :=
  {p | p.source = A ∧ p.goal = A ∧ ∃ x ∈ p.steps, x ≠ A}

theorem loops_telicK (A : Loc) : TelicK (loops (Loc := Loc) A) :=
  fun _ hp _ hq _ ↦ ⟨hp.1.trans hq.1.symm, hp.2.1.trans hq.2.1.symm⟩

/-- Loop sets are cumulative, so Krifka's telicity (22b) does not characterize boundedness. -/
theorem loops_cumulative [Nontrivial Loc] (A : Loc) :
    Cumulative Path.IsConcat (loops (Loc := Loc) A) := by
  obtain ⟨B, hB⟩ := exists_ne A
  constructor
  · have h : (⟨A, [B, A]⟩ : Path Loc) ∈ loops A := ⟨rfl, rfl, B, by simp, hB⟩
    exact ⟨_, h, _, h, _, ⟨rfl, rfl⟩⟩
  · rintro p hp q hq r hr
    obtain ⟨hs, -, x, hx, hxA⟩ := hp
    exact ⟨hr.source_eq.trans hs, hr.goal_eq.trans hq.2.1,
      x, by rw [hr.2]; simp [hx], hxA⟩

-- p. 776
theorem const_le_const_iff {a b : Loc} : Path.const a ≤ Path.const b ↔ a = b :=
  Path.const_le_iff.trans List.mem_singleton

/-! ### Goal and source prepositions (§4.1.1) -/

/-- The weak goal-phrase denotation, (30c), (33), holds of the paths ending in the region. -/
def weakTo (R : Set Loc) : Set (Path Loc) := {p | p.goal ∈ R}

theorem weakTo_cumulative {R : Set Loc} {x : Loc} (hx : x ∈ R) :
    Cumulative Path.IsConcat (weakTo R) :=
  ⟨⟨_, hx, _, hx, _, Path.isConcat_const_left (.const x)⟩,
    fun _ _ _ hq r hr ↦ (hr.goal_eq.symm ▸ hq : r.goal ∈ R)⟩

/-- The strict goal phrase, (35), (36): the positions in the region form an interval including the
last position and, being a proper interval, not the first. The goal prepositions differ only in
the region. -/
def toPP (R : Set Loc) : Set (Path Loc) := {p | Path.IsCofinal R p}

/-- The strict source phrase, (36), including the first position and not the last. -/
def fromPP (R : Set Loc) : Set (Path Loc) := {p | Path.IsCoinitial R p}

theorem toPP_subset_weakTo (R : Set Loc) : toPP R ⊆ weakTo R :=
  fun p hp ↦ (p.coe_top ▸ hp.2.2 : p.goal ∈ R)

-- (35)
theorem toPP_no_pairs (R : Set Loc) :
    ¬ ∃ p ∈ toPP R, ∃ q ∈ toPP R, ∃ r, Path.IsConcat p q r := by
  rintro ⟨p, hp, q, hq, r, hr⟩
  exact hq.2.1 (by rw [Path.coe_bot, ← hr.1, ← Path.coe_top]; exact hp.2.2)

-- (36)
theorem fromPP_no_pairs (R : Set Loc) :
    ¬ ∃ p ∈ fromPP R, ∃ q ∈ fromPP R, ∃ r, Path.IsConcat p q r := by
  rintro ⟨p, hp, q, hq, r, hr⟩
  exact hp.2.2 (by rw [Path.coe_top, hr.1, ← Path.coe_bot]; exact hq.2.1)

-- (21)
theorem toPP_bounded (R : Set Loc) : Bounded Path.IsConcat (toPP R) :=
  bounded_of_no_pairs (toPP_no_pairs R)

-- (12a), (36)
theorem fromPP_bounded (R : Set Loc) : Bounded Path.IsConcat (fromPP R) :=
  bounded_of_no_pairs (fromPP_no_pairs R)

/-! ### Route prepositions (§4.1.2) -/

/-- The strict route phrase, (39), (40): the positions in the region form an interval including
neither the first nor the last position. -/
def overPP (R : Set Loc) : Set (Path Loc) := {p | Path.IsTransitive R p}

-- (39)
theorem overPP_exists_pair {R : Set Loc} {x a : Loc} (hx : x ∈ R) (ha : a ∉ R) :
    ∃ p ∈ overPP R, ∃ q ∈ overPP R, ∃ r, Path.IsConcat p q r := by
  have hp : (⟨a, [x, a]⟩ : Path Loc) ∈ overPP R := by
    refine ⟨?_, ⟨1, hx⟩, ha, ha⟩
    rw [show (⇑(⟨a, [x, a]⟩ : Path Loc)) ⁻¹' R = {1} by
      ext i; fin_cases i <;> simp [Path.toFun, Path.points, hx, ha, Fin.ext_iff]]
    exact Set.ordConnected_singleton
  exact ⟨_, hp, _, hp, _, rfl, rfl⟩

/-- A route phrase is bounded, (39), since a concatenation of its paths has more than one interval
in the region. -/
theorem overPP_bounded (R : Set Loc) : Bounded Path.IsConcat (overPP R) := by
  rintro ⟨⟨p, hp, q, hq, r, hr⟩, hc⟩
  obtain ⟨-, ⟨i, hi⟩, -, hg⟩ := id hp
  obtain ⟨-, ⟨j, hj⟩, -, -⟩ := id hq
  exact hr.not_ordConnected (p.coe_top ▸ hg) hi hj (hc p hp q hq r hr).1

/-! ### Towards and away from (§4.1.3)

The comparative definitions over a distance measure `d` to the reference object are cumulative,
hence unbounded, which grounds the atelic marking of the comparative prepositions. -/

/-- *Towards x*, (45), holds of a path that ends nearer to the reference object than it starts,
measured by `d`. -/
def towardsPP [Preorder α] (d : Loc → α) : Set (Path Loc) :=
  {p | d p.goal < d p.source}

/-- *Away from x*, (48), holds of a path that ends further from the reference object than it
starts. -/
def awayFromPP [Preorder α] (d : Loc → α) : Set (Path Loc) :=
  {p | d p.source < d p.goal}

theorem towardsPP_concat_closed [Preorder α] (d : Loc → α) :
    ∀ p ∈ towardsPP d, ∀ q ∈ towardsPP d, ∀ r, Path.IsConcat p q r →
      r ∈ towardsPP d := by
  intro p hp q hq r hr
  show d r.goal < d r.source
  rw [hr.goal_eq, hr.source_eq]
  exact hq.trans_le (hr.1 ▸ hp.le)

theorem awayFromPP_concat_closed [Preorder α] (d : Loc → α) :
    ∀ p ∈ awayFromPP d, ∀ q ∈ awayFromPP d, ∀ r, Path.IsConcat p q r →
      r ∈ awayFromPP d := by
  intro p hp q hq r hr
  show d r.source < d r.goal
  rw [hr.goal_eq, hr.source_eq]
  exact hp.trans_le (hr.1 ▸ hq.le)

-- (45)
theorem towardsPP_cumulative [Preorder α] {d : Loc → α} {a b c : Loc} (hab : d b < d a)
    (hbc : d c < d b) : Cumulative Path.IsConcat (towardsPP d) :=
  ⟨⟨⟨a, [b]⟩, hab, ⟨b, [c]⟩, hbc, _, rfl, rfl⟩, towardsPP_concat_closed d⟩

-- (45)
theorem toPP_subset_towardsPP [Preorder α] {d : Loc → α} {R : Set Loc}
    (hd : ∀ x ∈ R, ∀ y ∉ R, d x < d y) : toPP R ⊆ towardsPP d :=
  fun _ hp ↦ hd _ (toPP_subset_weakTo R hp) _ hp.2.1

/-- Bounded phrases are not quantized, (23)–(24), since a *to x* path has proper subpaths that are
also *to x*, against the [krifka-1998] characterization of telicity. -/
theorem toPP_not_quantized {x a b : Loc} (ha : a ≠ x) (hb : b ≠ x) :
    ¬ QUA (· ∈ toPP ({x} : Set Loc)) := by
  intro h
  have hp : (⟨a, [x]⟩ : Path Loc) ∈ toPP {x} := by
    refine Path.IsTerminative.isCofinal ⟨?_, by simp⟩
    ext i; fin_cases i <;> simp [Path.toFun, Path.points, ha, Fin.top_eq_last]
  have hq : (⟨b, [a, x]⟩ : Path Loc) ∈ toPP {x} := by
    refine Path.IsTerminative.isCofinal ⟨?_, by simp⟩
    ext i; fin_cases i <;> simp [Path.toFun, Path.points, ha, hb, Fin.top_eq_last, Fin.ext_iff]
  exact h hp hq (by simp) (Path.subpath_iff_infix.mpr ⟨[b], [], rfl⟩)

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
        (Bounded Path.IsConcat (ph.denotation R d) ↔ t = true) := by
  have key : ∀ ph : Phrase, Bounded Path.IsConcat (ph.denotation R d) ↔ ph ≠ .towards := by
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
  | concat {p q r} (hp : Star X p) (hq : Star X q) (h : Path.IsConcat p q r) :
      Star X r

-- (58)
theorem star_cumulative {X : Set (Path Loc)}
    (h : ∃ p ∈ X, ∃ q ∈ X, ∃ r, Path.IsConcat p q r) :
    Cumulative Path.IsConcat {p | Star X p} := by
  obtain ⟨p, hp, q, hq, r, hr⟩ := h
  exact ⟨⟨p, .base hp, q, .base hq, r, hr⟩,
    fun _ hp' _ hq' _ hr' ↦ .concat hp' hq' hr'⟩

/-! ### Aspect transfer to the VP (§3.2) -/

section Transfer

open Event (σ)

variable {E : Type*} [SpatialTrace E Loc] (C : E → E → E → Prop)

/-- The spatial trace is a homomorphism for concatenation when the trace of a fused event is the
concatenation of the traces. -/
def IsTraceHom : Prop :=
  ∀ e e' f, C e e' f → Path.IsConcat (σ e) (σ e') (σ f)

/-- `⟦V PP⟧`, (25), holds of the verb's events whose trace lies in the phrase's denotation. -/
def vpp (V : Set E) (X : Set (Path Loc)) : Set E :=
  {e ∈ V | σ e ∈ X}

variable {C}

theorem vpp_concat_closed (hhom : IsTraceHom (E := E) C) {V : Set E}
    {X : Set (Path Loc)}
    (hV : ∀ e ∈ V, ∀ e' ∈ V, ∀ f, C e e' f → f ∈ V)
    (hX : ∀ p ∈ X, ∀ q ∈ X, ∀ r, Path.IsConcat p q r → r ∈ X) :
    ∀ e ∈ vpp V X, ∀ e' ∈ vpp V X, ∀ f, C e e' f → f ∈ vpp V X :=
  fun e he e' he' f hf ↦
    ⟨hV e he.1 e' he'.1 f hf, hX _ he.2 _ he'.2 _ (hhom e e' f hf)⟩

theorem vpp_bounded_of_no_pairs (hhom : IsTraceHom (E := E) C) {V : Set E}
    {X : Set (Path Loc)}
    (hX : ¬ ∃ p ∈ X, ∃ q ∈ X, ∃ r, Path.IsConcat p q r) :
    Bounded C (vpp V X) :=
  bounded_of_no_pairs fun ⟨e, he, e', he', f, hf⟩ ↦
    hX ⟨σ e, he.2, σ e', he'.2, σ f, hhom e e' f hf⟩

/-- *Walk to the house* is bounded, (26), by the negative transfer at the strict goal phrase. -/
theorem vpp_toPP_bounded (hhom : IsTraceHom (E := E) C) {V : Set E} (R : Set Loc) :
    Bounded C (vpp V (toPP R)) :=
  vpp_bounded_of_no_pairs hhom (toPP_no_pairs R)

end Transfer

end Zwarts2005
