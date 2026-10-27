module

public import Linglib.Semantics.Events.Path
public import Linglib.Semantics.Mereology

/-!
# Zwarts (2005): Prepositional Aspect and the Algebra of Paths

Zwarts analyzes the aspect of directional prepositional phrases, which denote sets of paths. A
telic phrase like *to the house* differs from an atelic one like *towards the house* in closure
under the partial concatenation of paths: an atelic phrase is cumulative and a telic one
bounded, that is, not cumulative. Bounded phrases are not quantized, and loops are telic in
Krifka's sense yet cumulative, so neither quantization nor that telicity characterizes
boundedness. A trace homomorphism for concatenation transfers closure from the phrase to the
verb phrase, so *walk to the house* is bounded because no two *to the house* paths concatenate.
The path algebra is `Semantics/Events/Path`; closure is stated here over any ternary
concatenation relation.

## Main definitions

* `Cumulative`: closure under concatenation.
* `Bounded`: the absence of cumulativity.
* `toPP`: the endpoint content of the strict goal phrase.
* `towardsPP`: *towards*.
* `IsTraceHom`: a trace homomorphism for concatenation.

## Implementation notes

* The strict goal and source denotations enter through their endpoint content only.
* The paper's trace function respects Rothstein's partial event concatenation, not an
  unrestricted mereological sum.

## TODO

* The full single-phase definitions (35), (36), (39) and (40), and the minimality and grinder
  operators (63) and (64).

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

Stated over an arbitrary ternary concatenation relation: Appendix A pairs the
path algebra with an event algebra of the same shape, and §3.2 transfers
closure properties along a homomorphism between the two. -/

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
  λ hc => h hc.1

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

/-- `loops x` is the *round and round the block* set of non-constant loops at `x`. -/
def loops (A : Loc) : Set (Path Loc) :=
  {p | p.source = A ∧ p.goal = A ∧ p.steps ≠ []}

theorem loops_telicK (A : Loc) : TelicK (loops (Loc := Loc) A) :=
  λ _ hp _ hq _ => ⟨hp.1.trans hq.1.symm, hp.2.1.trans hq.2.1.symm⟩

/-- Loop sets are cumulative, so Krifka's telicity (22b) does not characterize boundedness. -/
theorem loops_cumulative (A : Loc) :
    Cumulative Path.IsConcat (loops (Loc := Loc) A) := by
  constructor
  · have h : (⟨A, [A]⟩ : Path Loc) ∈ loops A := ⟨rfl, rfl, by simp⟩
    exact ⟨_, h, _, h, _, ⟨rfl, rfl⟩⟩
  · rintro p hp q hq r hr
    exact ⟨hr.source_eq.trans hp.1, hr.goal_eq.trans hq.2.1,
      by rw [hr.2]; simp [hq.2.2]⟩

/-! ### Goal and source prepositions (§4.1.1) -/

/-- The weak goal-phrase denotation, (30c), holds of the paths ending at the reference object. -/
def weakTo (x : Loc) : Set (Path Loc) := {p | p.goal = x}

-- (30c), (34), (35)
theorem weakTo_cumulative (x : Loc) : Cumulative Path.IsConcat (weakTo x) :=
  ⟨⟨_, Path.goal_const x, _, Path.goal_const x, _, Path.isConcat_const x⟩,
    λ _ _ _ hq _ hr => hr.goal_eq.trans hq⟩

/-- The endpoint content of the strict goal phrase, (36), holds of a path that ends at the
reference object and does not start there. -/
def toPP (x : Loc) : Set (Path Loc) := {p | p.goal = x ∧ p.source ≠ x}

/-- The endpoint content of the strict source phrase, (36), holds of a path that starts at the
reference object and does not end there. -/
def fromPP (x : Loc) : Set (Path Loc) := {p | p.source = x ∧ p.goal ≠ x}

theorem toPP_no_pairs (x : Loc) :
    ¬ ∃ p ∈ toPP x, ∃ q ∈ toPP x, ∃ r, Path.IsConcat p q r := by
  rintro ⟨p, hp, q, hq, r, hr⟩
  exact hq.2 (hr.1 ▸ hp.1)

/-- Strict goal phrases are bounded, (21), so *to the house* is telic. -/
theorem toPP_bounded (x : Loc) : Bounded Path.IsConcat (toPP x) :=
  bounded_of_no_pairs (toPP_no_pairs x)

-- (12a)
theorem fromPP_bounded (x : Loc) : Bounded Path.IsConcat (fromPP x) := by
  rintro ⟨⟨p, hp, q, hq, r, hr⟩, -⟩
  exact hp.2 (hr.1.trans hq.1)

/-! ### Towards and away from (§4.1.3)

The comparative definitions over a distance measure `d` to the reference
object: cumulative, hence unbounded — grounding the atelic marking of the
comparative prepositions in the fragments' directionality × telicity data. -/

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

/-- On the rational line with the reference object at the origin, *towards* is
cumulative, with a concrete concatenable pair witnessing non-vacuity. -/
theorem towardsPP_cumulative :
    Cumulative Path.IsConcat (towardsPP (abs : ℚ → ℚ)) := by
  refine ⟨⟨⟨2, [1]⟩, ?_, ⟨1, [0]⟩, ?_, _, ⟨rfl, rfl⟩⟩,
    towardsPP_concat_closed abs⟩
  · show |(1 : ℚ)| < |(2 : ℚ)|
    norm_num
  · show |(0 : ℚ)| < |(1 : ℚ)|
    norm_num

/-- Bounded phrases are not quantized, (23)–(24), since a *to x* path has proper subpaths that are
also *to x*, against the [krifka-1998] characterization of telicity. -/
theorem toPP_not_quantized : ¬ QUA (· ∈ toPP (0 : ℚ)) := by
  intro h
  have hp : (⟨1, [0]⟩ : Path ℚ) ∈ toPP 0 := ⟨rfl, by norm_num⟩
  have hq : (⟨2, [1, 0]⟩ : Path ℚ) ∈ toPP 0 := ⟨rfl, by norm_num⟩
  have hle : (⟨1, [0]⟩ : Path ℚ) ≤ ⟨2, [1, 0]⟩ :=
    Path.subpath_iff_infix.mpr ⟨[2], [], rfl⟩
  exact h hp hq (by simp) hle

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
    λ _ hp' _ hq' _ hr' => .concat hp' hq' hr'⟩

/-! ### Aspect transfer to the VP (§3.2) -/

section Transfer

open Event (σ)

variable {E : Type*} [Event.SpatialTrace E Loc] (C : E → E → E → Prop)

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
  λ e he e' he' f hf =>
    ⟨hV e he.1 e' he'.1 f hf, hX _ he.2 _ he'.2 _ (hhom e e' f hf)⟩

theorem vpp_bounded_of_no_pairs (hhom : IsTraceHom (E := E) C) {V : Set E}
    {X : Set (Path Loc)}
    (hX : ¬ ∃ p ∈ X, ∃ q ∈ X, ∃ r, Path.IsConcat p q r) :
    Bounded C (vpp V X) :=
  bounded_of_no_pairs λ ⟨e, he, e', he', f, hf⟩ =>
    hX ⟨σ e, he.2, σ e', he'.2, σ f, hhom e e' f hf⟩

/-- *Walk to the house* is bounded, (26), by the negative transfer at the strict goal phrase. -/
theorem vpp_toPP_bounded (hhom : IsTraceHom (E := E) C) {V : Set E} (x : Loc) :
    Bounded C (vpp V (toPP x)) :=
  vpp_bounded_of_no_pairs hhom (toPP_no_pairs x)

end Transfer

end Zwarts2005
