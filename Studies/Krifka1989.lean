module

public import Linglib.Semantics.Aspect.Incremental
public import Mathlib.Order.Minimal
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Linglib.Semantics.Mereology.Extensive

/-!
# Krifka (1989): Nominal Reference, Temporal Constitution and Quantification in Event Semantics

Krifka relates the reference of nominal predicates to the temporal constitution of verbal
predicates. Objects, events and times form join semilattices, and a predicate is cumulative when
it is closed under join and quantized when no instance is a proper part of another, so that
[only a predicate of at most one thing is both](##Mereology.qua_and_cum_iff_subsingleton). A
measure phrase turns a predicate that is not quantized into one that is, which is why
[measure phrases do not iterate](##Krifka1989.not_qmod_inter_preimage): *five ounces of gold* is
already quantized. A thematic relation transfers the reference type of its nominal argument to
the verbal predicate. Summativity carries cumulativity across, and uniqueness of objects with
mapping to objects carries quantization across
[when no event is iterative on its object](##Krifka1989.qua_vp_of_not_iter), a condition that
[cannot be dropped](##Krifka1989.not_qua_vp_readTwice) and that for a summative relation
[is uniqueness of events](##Krifka1989.gue_iff_forall_not_iter). Even an iterative predicate
with a strictly quantized object is not divisive, since
[each of its events has a proper part outside it](##Krifka1989.exists_lt_not_vp). A durative
adverbial is a measure phrase for events and so
[rejects quantized predicates](##Krifka1989.qmod_durative_iff), and a time-span adverbial
[is upward entailing](##Krifka1989.inSpan_mono) in its measure.

## Implementation notes

The paper's relations are stated with the library's object-first thematic relations, so its
uniqueness of objects is `UP`, uniqueness of events `GUE`, mapping to objects `MO`, mapping to
events `ME`, and summativity `SUM`. Its part structures satisfy relative complementarity (D 9),
which the measure theorems assume as `Mereology.AdditiveRemainder`: a remainder exists, and
need not be unique. Theorem (T 3) needs a nonempty
predicate, since the empty predicate is both quantized and strictly cumulative.

Theorems (T 8) and (T 11) are stated for what their proofs establish. For (T 8) that is
iterativity of the sum of the given event with a second one; for (T 11) it is quantization when
no event is iterative on an object of the nominal predicate. The proof of (T 13) shows that every
verbal event has a proper part outside the predicate; its conclusion that the event contains an
atom holds of every predicate when the part order on events is well founded
(`atm_of_wellFoundedLT`).

An extensive measure function, (D 21)–(D 25), is `IsExtensiveMeasure`, stated for a total
function to the reals, with the preorder the one the function induces and the multiplier of the
Archimedean property a natural number. The concatenation is total, as (D 22) has it, so such a
function has no finite domain (`IsExtensiveMeasure.infinite`). One compatible with a part
structure, (D 26)–(D 27), is additive over non-overlapping individuals and positive
(`IsCompatible.isExtensive`), which is `Mereology.IsExtensive`, the hypothesis the theorems on
measure phrases use; the atom count of a finite model satisfies that and is no extensive
measure function in the sense of (D 23)–(D 24).

Measure functions are total here. The bare plural (8) binds the number argument of a count noun
existentially, so with a total measure it has the extension of the underlying predicate
(`iUnion_inter_preimage`) and is cumulative when that predicate is; Krifka derives its cumulativity
from additivity, for a measure function that may be partial. The measure of an event (D 41) is
the measure of its run time, which is additive over events whose run times do not overlap
(D 43) and not over all non-overlapping events, so the durative adverbial (15) is quantizing
for predicates on which the temporal trace is strictly monotone.

## TODO

* Maximal events (D 44)–(D 45), negation as the modifier (22), (28) to maximal events containing
  no event of the predicate, and the quantifiers of §7.
* The second step of the argument from (20), that an atomic predicate has smallest convex times
  containing its events.

## References

* [krifka-1989]
* [link-1983], [krifka-1998]
-/

@[expose] public section

namespace Krifka1989

open Mereology Aspect
open scoped SetRel

/-! ### Reference types (§2) -/

section Reference

variable {α : Type*} {P : Set α}

/-- (D 11): A predicate has singular reference if it holds of exactly one element. -/
abbrev SNG (P : Set α) : Prop := ∃! x, x ∈ P

theorem SNG.subsingleton (h : SNG P) : P.Subsingleton := fun _ hx _ hy ↦ h.unique hx hy

section PartialOrder

variable [PartialOrder α]

/-- (D 15): A predicate has strictly quantized reference if it is quantized and every instance
has a proper part. -/
structure SQUA (P : Set α) : Prop where
  qua : QUA P
  exists_lt : ∀ x ∈ P, ∃ y, y < x

/-- (D 18): A predicate has atomic reference if every instance has a part that is a `P`-atom
(D 17). -/
def ATM (P : Set α) : Prop := ∀ x ∈ P, ∃ y ≤ x, y ∈ atomize P

-- (T 1)
theorem SNG.qua (h : SNG P) : QUA P := h.subsingleton.isAntichain _

-- (T 4)
theorem atm_of_qua (h : QUA P) : ATM P := fun x hx ↦ ⟨x, le_rfl, h.minimal_mem_iff.2 hx⟩

theorem atm_of_wellFoundedLT [WellFoundedLT α] (P : Set α) : ATM P :=
  exists_minimal_le_of_wellFoundedLT (· ∈ P)

end PartialOrder

variable [SemilatticeSup α]

/-- (D 13): A predicate has strictly cumulative reference if it is cumulative and not
singular. -/
structure SCUM (P : Set α) : Prop where
  cum : CUM P
  not_sng : ¬ SNG P

-- (T 2)
theorem SNG.cum (h : SNG P) : CUM P := (qua_and_cum_iff_subsingleton.2 h.subsingleton).2

-- (T 3)
theorem not_scum_of_qua (hne : P.Nonempty) (h : QUA P) : ¬ SCUM P := fun hs ↦
  hs.not_sng <| existsUnique_of_exists_of_unique hne fun _ _ hx hy ↦
    qua_and_cum_iff_subsingleton.1 ⟨h, hs.cum⟩ hx hy

end Reference

/-! ### Extensive measure functions (§2) -/

section Measure

variable {α : Type*}

/-- (D 21)–(D 25): `m` is an extensive measure function relative to the concatenation `C`. The
preorder of (D 21) is the one `m` induces, `m x ≤ m y`. -/
structure IsExtensiveMeasure (C : α → α → α) (m : α → ℝ) : Prop where
  /-- (D 22): concatenation is commutative. -/
  comm (x y : α) : C x y = C y x
  /-- (D 23): an individual is below its concatenation with another in the preorder. -/
  le_map_conc (x y : α) : m x ≤ m (C x y)
  /-- (D 24): additivity. -/
  map_conc (x y : α) : m (C x y) = m x + m y
  /-- (D 25): the Archimedean property. -/
  archimedean ⦃x y : α⦄ : m x ≤ m y → ∃ n : ℕ, 0 < n ∧ m y < n • m x

variable {C : α → α → α} {m : α → ℝ}

-- (T 5): an extensive measure function has positive values.
theorem IsExtensiveMeasure.pos (h : IsExtensiveMeasure C m) (x : α) : 0 < m x := by
  obtain ⟨n, hn, hlt⟩ := h.archimedean (le_refl (m x))
  by_contra hx
  rw [nsmul_eq_mul] at hlt
  have : (n : ℝ) * m x ≤ 1 * m x :=
    mul_le_mul_of_nonpos_right (by exact_mod_cast hn) (not_lt.1 hx)
  linarith

theorem IsExtensiveMeasure.map_iterate (h : IsExtensiveMeasure C m) (x : α) (k : ℕ) :
    m ((fun y ↦ C y y)^[k] x) = 2 ^ k * m x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', h.map_conc, ih]; ring

-- An extensive measure function has no finite domain: concatenating an individual with itself
-- doubles its measure.
theorem IsExtensiveMeasure.infinite [Nonempty α] (h : IsExtensiveMeasure C m) : Infinite α := by
  obtain ⟨x⟩ := ‹Nonempty α›
  refine .of_injective (fun k ↦ (fun y ↦ C y y)^[k] x) fun i j hij ↦ ?_
  have hm : (2 : ℝ) ^ i * m x = 2 ^ j * m x := by
    rw [← h.map_iterate, ← h.map_iterate]; exact congrArg m hij
  exact Nat.pow_right_injective le_rfl
    (by exact_mod_cast mul_right_cancel₀ (h.pos x).ne' hm)

/-- (D 26), (D 27): an extensive measure function is compatible with a part structure if its
preorder continues parthood and its concatenation is the sum on individuals that do not
overlap. -/
structure IsCompatible [SemilatticeSup α] (C : α → α → α) (m : α → ℝ) : Prop
    extends IsExtensiveMeasure C m where
  /-- (D 26) -/
  mono : Monotone m
  /-- (D 27) -/
  conc_eq_sup ⦃x y : α⦄ : ¬ Overlap x y → C x y = x ⊔ y

-- A compatible extensive measure function is additive over individuals that do not overlap and
-- positive.
theorem IsCompatible.isExtensive [SemilatticeSup α] (h : IsCompatible C m) : IsExtensive m where
  map_sup _ _ hxy := h.conc_eq_sup hxy ▸ h.map_conc _ _
  pos := h.toIsExtensiveMeasure.pos

-- The positive natural numbers under addition, measured by their value, are an extensive
-- measure function compatible with their order.
theorem isCompatible_pnat : IsCompatible (· + ·) fun n : ℕ+ ↦ ((n : ℕ) : ℝ) where
  comm := add_comm
  le_map_conc x y := by push_cast; exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  map_conc x y := by push_cast; rfl
  archimedean x y _ := ⟨y + 1, Nat.succ_pos _, by
    rw [nsmul_eq_mul]
    have hx : (1 : ℝ) ≤ ((x : ℕ) : ℝ) := by exact_mod_cast (one_le : (1 : ℕ+) ≤ x)
    have hy : (0 : ℝ) ≤ ((y : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith⟩
  mono x y hxy := Nat.cast_le.2 (PNat.coe_le_coe x y |>.2 hxy)
  conc_eq_sup x y hxy := absurd ⟨x ⊓ y, inf_le_left, inf_le_right⟩ hxy

end Measure

-- (T 6)
theorem qua_measure_eq {α M : Type*} [SemilatticeSup α] [AddCommMonoid M] [PartialOrder M]
    [AddLeftStrictMono M] {μ : α → M} (hμ : IsExtensive μ) (hR : AdditiveRemainder α) (n : M) :
    QUA (μ ⁻¹' {n}) :=
  QUA.preimage (hμ.strictMono hR) (Set.subsingleton_singleton.isAntichain _)

/-! ### Nominal predicates (§3) -/

section Nominal

variable {α M : Type*} {P : Set α}

/-- (D 28): A modifier is quantizing for a predicate if the predicate is not quantized and the
modified predicate is. -/
structure QMOD [PartialOrder α] (P : Set α) (f : Set α → Set α) : Prop where
  not_qua : ¬ QUA P
  qua : QUA (f P)

theorem qmod_iff [PartialOrder α] {f : Set α → Set α} (h : QUA (f P)) :
    QMOD P f ↔ ¬ QUA P :=
  ⟨QMOD.not_qua, (⟨·, h⟩)⟩

-- (8)
theorem iUnion_inter_preimage (P : Set α) (μ : α → M) : ⋃ n, P ∩ μ ⁻¹' {n} = P := by
  ext x
  simp

variable [SemilatticeSup α] [AddCommMonoid M] [PartialOrder M]
  [AddLeftStrictMono M] {μ : α → M}

-- (6)
theorem qua_inter_preimage (hμ : IsExtensive μ) (hR : AdditiveRemainder α) (n : M)
    (P : Set α) : QUA (P ∩ μ ⁻¹' {n}) :=
  qua_inter_preimage_of_strictMonoOn ((hμ.strictMono hR).strictMonoOn _) n

-- (4)
theorem qmod_inter_preimage (hμ : IsExtensive μ) (hR : AdditiveRemainder α) (n : M)
    (hP : CUM P) {x y : α} (hx : x ∈ P)
    (hy : y ∈ P) (hxy : x ≠ y) : QMOD P (· ∩ μ ⁻¹' {n}) :=
  ⟨fun hQ ↦ hxy (qua_and_cum_iff_subsingleton.1 ⟨hQ, hP⟩ hx hy), qua_inter_preimage hμ hR n P⟩

/-- (3c): No modifier is quantizing for a measure phrase, which is already quantized, so
measure phrases do not iterate (*five ounces of seven cube centimeters of gold*). -/
theorem not_qmod_inter_preimage (hμ : IsExtensive μ) (hR : AdditiveRemainder α) (n : M)
    (P : Set α) (f : Set α → Set α) :
    ¬ QMOD (P ∩ μ ⁻¹' {n}) f :=
  fun h ↦ h.not_qua (qua_inter_preimage hμ hR n P)

end Nominal

/-! ### Transfer of reference from objects to events (§4)

The verbal predicate (12) of a verb, a nominal predicate `δ` and a thematic relation `θ` is the
verb conjoined with the verb phrase `VP θ δ`. Quantization and atomicity pass to the conjunction
from the verb phrase, for which the paper states them. -/

section Transfer

variable {O E : Type*} [SemilatticeSup O] [SemilatticeSup E] {θ : SetRel O E} {δ : Set O}

/-- (D 34): An event is iterative on an object if some part of the object is subjected to two
parts of the event. -/
def ITER (θ : SetRel O E) (e : E) (x : O) : Prop :=
  x ~[θ] e ∧ ∃ e' e'' x', e' ≤ e ∧ e'' ≤ e ∧ e' ≠ e'' ∧ x' ≤ x ∧ x' ~[θ] e' ∧ x' ~[θ] e''

/-- (D 35): A relation is gradual if it has uniqueness of objects and both mappings. -/
structure GRAD (θ : SetRel O E) : Prop where
  up : UP θ
  mo : MO θ
  me : ME θ

theorem GRAD.uo (h : GRAD θ) : UO θ := h.up.uo_of_mo h.mo

theorem GRAD.ue_of_gue (h : GRAD θ) (hg : GUE θ) : UE θ := hg.ue_of_me h.me

-- (T 7)
theorem cum_inter_vp {α : Set E} (hα : CUM α) (hδ : CUM δ) (hθ : SUM θ) :
    CUM (α ∩ VP θ δ) :=
  hα.inter (vp_cum hθ hδ)

theorem iter_sup (hθ : SUM θ) {x : O} {e₁ e₂ : E} (h₁ : x ~[θ] e₁) (h₂ : x ~[θ] e₂)
    (hne : e₁ ≠ e₂) : ITER θ (e₁ ⊔ e₂) x :=
  ⟨by simpa using hθ.sup h₁ h₂, e₁, e₂, x, le_sup_left, le_sup_right, hne, le_rfl, h₁, h₂⟩

-- (T 10)
theorem not_iter_of_gue (h : GUE θ) (e : E) (x : O) : ¬ ITER θ e x :=
  fun ⟨_, _, _, _, _, _, hne, _, h', h''⟩ ↦ hne (h.eq h' h'')

/-- A summative relation has uniqueness of events iff no event is iterative: uniqueness of
events excludes iteration (T 10), and two events of one object sum to an iterative event. -/
theorem gue_iff_forall_not_iter (hθ : SUM θ) : GUE θ ↔ ∀ e x, ¬ ITER θ e x :=
  ⟨not_iter_of_gue,
    fun h ↦ gue_iff.2 fun _ _ _ h₁ h₂ ↦ by_contra fun hne ↦ h _ _ (iter_sup hθ h₁ h₂ hne)⟩

-- (T 8)
theorem exists_iter (hδ : SNG δ) (hθ : SUM θ) (hs : SCUM (VP θ δ)) {x : O} {e : E} (hx : x ∈ δ)
    (he : x ~[θ] e) : ∃ e', ITER θ (e ⊔ e') x := by
  obtain ⟨e', ⟨y, hy, he'⟩, hne⟩ : ∃ e', e' ∈ VP θ δ ∧ e ≠ e' := by
    by_contra! h
    exact hs.not_sng ⟨e, ⟨x, hx, he⟩, fun e' he' ↦ (h e' he').symm⟩
  exact ⟨e', iter_sup hθ he (hδ.unique hy hx ▸ he') hne⟩

-- (T 9)
theorem not_scum_vp (hδ : SNG δ) (hθ : SUM θ) {x : O} {e : E} (hx : x ∈ δ) (he : x ~[θ] e)
    (hi : ∀ e', ¬ ITER θ (e ⊔ e') x) : ¬ SCUM (VP θ δ) := fun hs ↦
  let ⟨e', h⟩ := exists_iter hδ hθ hs hx he
  hi e' h

/-- (T 11): Uniqueness of objects and mapping to objects carry quantization from the object to
the verb phrase when no event is iterative on an object of the nominal predicate. -/
theorem qua_vp_of_not_iter (hδ : QUA δ) (hu : UP θ) (hm : MO θ)
    (hi : ∀ e, ∀ x ∈ δ, ¬ ITER θ e x) : QUA (VP θ δ) :=
  qua_of_forall fun e e' ⟨x, hx, hθ⟩ hlt ⟨x', hx', hθ'⟩ ↦
    let ⟨y, hy, hθy⟩ := hm hθ hlt.le
    have hyx' : y = x' := hu.eq (SetRel.mem_inv.1 hθy) hθ'
    hδ hx' hx
      (fun h ↦ hi e x hx ⟨hθ, e', e, x, hlt.le, le_rfl, hlt.ne, le_rfl, h ▸ hθ', hθ⟩)
      (hyx' ▸ hy)

-- (T 12)
theorem qua_vp_of_gue (hδ : QUA δ) (hu : UP θ) (hm : MO θ) (hg : GUE θ) : QUA (VP θ δ) :=
  qua_vp_of_not_iter hδ hu hm fun e x _ ↦ not_iter_of_gue hg e x

/-- (T 13): With a strictly quantized object, uniqueness of objects and mapping to events give
every event of the verb phrase a proper part outside it, the part subjected to a proper part of
the object. -/
theorem exists_lt_not_vp (hδ : SQUA δ) (hm : ME θ) (hu : UP θ) {e : E} (he : e ∈ VP θ δ) :
    ∃ e' < e, e' ∉ VP θ δ := by
  obtain ⟨x, hx, hθx⟩ := he
  obtain ⟨y, hyx⟩ := hδ.exists_lt x hx
  obtain ⟨e', he', hθy⟩ := hm hθx hyx.le
  have hn : e' ∉ VP θ δ := fun ⟨z, hz, hθz⟩ ↦ hδ.qua (hu.eq hθz hθy ▸ hz) hx hyx.ne hyx.le
  exact ⟨e', lt_of_le_of_ne he' fun h ↦ hn (h ▸ ⟨x, hx, hθx⟩), hn⟩

end Transfer

/-! ### Reading the letter twice

The classification (14) separates the gradual patient of *read a letter* from the effected and
consumed patients of *write a letter* and *eat an apple* by uniqueness of events. In the model
below one letter is read in two events, one a part of the other. -/

/-- The patient relation of a letter that every event reads, the event `true` containing the
event `false`. -/
def readTwice : SetRel Unit Bool := Set.univ

theorem readTwice_sum : SUM readTwice := supClosed_univ

theorem readTwice_grad : GRAD readTwice :=
  ⟨up_iff.2 fun _ _ _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ ⟨(), le_rfl, trivial⟩,
    fun _ e _ _ _ ↦ ⟨e, le_rfl, trivial⟩⟩

theorem iter_readTwice : ITER readTwice true () :=
  ⟨trivial, false, true, (), Bool.false_le _, le_rfl, Bool.false_ne_true, le_rfl, trivial,
    trivial⟩

/-- A gradual and summative relation does not carry quantization across when it is iterative:
*read the letter* holds of both readings of the one letter. -/
theorem not_qua_vp_readTwice : ¬ QUA (VP readTwice {()}) := fun h ↦
  h (show false ∈ VP readTwice {()} from ⟨(), rfl, trivial⟩)
    (show true ∈ VP readTwice {()} from ⟨(), rfl, trivial⟩) Bool.false_ne_true
    (Bool.false_le _)

/-! ### Temporal adverbials (§5) -/

section Adverbials

variable {E T M : Type*} {P : Set E} {τ : E → T}

section Durative

variable [PartialOrder E] [SemilatticeSup T] [AddCommMonoid M]
  [PartialOrder M] [AddLeftStrictMono M] {μ : T → M}

-- (D 41)
theorem qua_inter_preimage_comp (hμ : IsExtensive μ) (hR : AdditiveRemainder T) (n : M)
    (hτ : StrictMonoOn τ P) :
    QUA (P ∩ (μ ∘ τ) ⁻¹' {n}) :=
  qua_inter_preimage_of_strictMonoOn ((hμ.strictMono hR).comp_strictMonoOn hτ) n

-- (15): *for an hour* is quantizing for exactly the predicates that are not quantized
theorem qmod_durative_iff (hμ : IsExtensive μ) (hR : AdditiveRemainder T) (n : M)
    (hτ : StrictMonoOn τ P) :
    QMOD P (· ∩ (μ ∘ τ) ⁻¹' {n}) ↔ ¬ QUA P :=
  qmod_iff (qua_inter_preimage_comp hμ hR n hτ)

end Durative

variable [Preorder T]

/-- (16): A time-span adverbial holds of an event that lies within a convex time of the given
measure. -/
def inSpan (P : E → Prop) (τ : E → T) (Conv : T → Prop) (μ : T → M) (n : M) : E → Prop :=
  fun e ↦ P e ∧ ∃ t, Conv t ∧ μ t = n ∧ τ e ≤ t

-- (17), (20)
theorem inSpan_mono (P : E → Prop) (τ : E → T) (Conv : T → Prop) (μ : T → M) {n n' : M}
    (h : ∀ t, Conv t → μ t = n → ∃ t', Conv t' ∧ μ t' = n' ∧ t ≤ t') :
    ∀ e, inSpan P τ Conv μ n e → inSpan P τ Conv μ n' e := by
  rintro e ⟨hp, t, hc, hμ, hle⟩
  obtain ⟨t', hc', hμ', htt'⟩ := h t hc hμ
  exact ⟨hp, t', hc', hμ', hle.trans htt'⟩

end Adverbials

end Krifka1989
