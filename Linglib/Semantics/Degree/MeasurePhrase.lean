module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.GroupWithZero.OrderIso

/-!
# Measure phrases and the changes of scale they survive

A measure-phrase differential (*3 inches taller*) says that two measures differ by a given amount,
and a factor phrase (*twice as tall*) that one measure is a multiple of another. In measurement
theory a statement about measurements is meaningful when its truth survives every admissible change
of scale: a strictly monotone map on an ordinal scale, a positive affine map on an interval scale,
a positive scaling on a ratio scale. A differential survives translations, and under a change of
unit it holds once its amount is rescaled too. A factor phrase survives scalings but not
translations, so *twice as hot* in degrees Celsius is not meaningful. Neither survives an arbitrary
strictly monotone change of scale, which is why an ordinal adjective such as *beautiful* takes
neither.

## Main statements

* `differentialComparative_comp_iff_commute`, `factorEquative_comp_iff_commute`: a differential or
  a factor phrase survives an injective change of scale exactly when the change commutes with
  adding its amount or multiplying by its factor.
* `differentialComparative_const_mul_add_const`: a differential survives translations, and a
  change of unit rescales its amount.
* `factorEquative_add_const_iff`: a factor phrase survives a translation only when the factor fixes
  the translation, so in a domain only the trivial factor or translation.

## References

* [stevens-1946]
* [krantz-1971]
* [sassoon-2010]
* [van-rooij-2011]
* [schwarzschild-2005]
* [winter-2005]
-/

@[expose] public section

namespace Degree

open Function

/-! ### Differential and factor semantics -/

/-- The differential comparative *A is d-much Adj-er than B* holds when `μ A - μ B = d`. It needs
subtraction, not just an ordering, which makes measure-phrase differentials more restrictive than
bare comparatives. -/
def DifferentialComparative {Entity D : Type*} [Sub D]
    (μ : Entity → D) (a b : Entity) (diff : D) : Prop :=
  μ a - μ b = diff

/-- The factor-phrase equative *A is n times as tall as B* holds when `μ A = n * μ B`, which needs a
meaningful zero, a ratio scale. -/
def FactorEquative {Entity D : Type*} [Mul D]
    (μ : Entity → D) (a b : Entity) (factor : D) : Prop :=
  μ a = factor * μ b

theorem differentialComparative_lt_of_pos {Entity D : Type*}
    [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    (μ : Entity → D) (a b : Entity) {diff : D} (hdiff : 0 < diff)
    (h : DifferentialComparative μ a b diff) : μ b < μ a :=
  sub_pos.mp (h.symm ▸ hdiff)

/-! ### Differentials under a change of scale -/

section Differential

variable {E D : Type*}

theorem differentialComparative_comp_of_commute [AddGroup D] {g : D → D} (hg : Injective g)
    {d : D} (hc : Function.Commute g (d + ·)) (μ : E → D) (a b : E) :
    DifferentialComparative (g ∘ μ) a b d ↔ DifferentialComparative μ a b d := by
  have h : g (d + μ b) = d + g (μ b) := hc (μ b)
  rw [DifferentialComparative, DifferentialComparative, comp_apply, comp_apply,
    sub_eq_iff_eq_add, sub_eq_iff_eq_add, ← h, hg.eq_iff]

theorem differentialComparative_add_const [AddGroup D] (μ : E → D) (c : D) (a b : E) (d : D) :
    DifferentialComparative (fun x ↦ μ x + c) a b d ↔ DifferentialComparative μ a b d :=
  differentialComparative_comp_of_commute (g := (· + c)) (add_left_injective c)
    (fun x ↦ add_assoc d x c) μ a b

/-- Under a change of unit and origin, a differential holds once its amount is rescaled by the
same unit. -/
theorem differentialComparative_const_mul_add_const {k : Type*} [CommRing k] [IsDomain k]
    (μ : E → k) {a : k} (ha : a ≠ 0) (b : k) (x y : E) (d : k) :
    DifferentialComparative (fun e ↦ a * μ e + b) x y (a * d) ↔
      DifferentialComparative μ x y d := by
  rw [differentialComparative_add_const (μ := fun e ↦ a * μ e)]
  simp only [DifferentialComparative, ← mul_sub, (mul_right_injective₀ ha).eq_iff]

/-- A differential survives an injective change of scale for every measure exactly when the change
commutes with adding its amount, so it is not meaningful on an ordinal scale. -/
theorem differentialComparative_comp_iff_commute [AddGroup D] [Nontrivial E] {g : D → D}
    (hg : Injective g) {d : D} :
    (∀ (μ : E → D) a b, DifferentialComparative (g ∘ μ) a b d ↔ DifferentialComparative μ a b d) ↔
      Function.Commute g (d + ·) := by
  refine ⟨fun h x ↦ ?_, fun hc μ a b ↦ differentialComparative_comp_of_commute hg hc μ a b⟩
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  have := (h (fun e ↦ if e = a then d + x else x) a b).2 (by
    simp [DifferentialComparative, hab.symm])
  simpa [DifferentialComparative, hab.symm, sub_eq_iff_eq_add] using this

end Differential

/-! ### Factor phrases under a change of scale -/

section Factor

variable {E D : Type*}

theorem factorEquative_comp_of_commute [Mul D] {g : D → D} (hg : Injective g) {n : D}
    (hc : Function.Commute g (n * ·)) (μ : E → D) (a b : E) :
    FactorEquative (g ∘ μ) a b n ↔ FactorEquative μ a b n := by
  have h : g (n * μ b) = n * g (μ b) := hc (μ b)
  simp only [FactorEquative, comp_apply, ← h, hg.eq_iff]

theorem factorEquative_const_mul [CommMonoidWithZero D] [IsCancelMulZero D] (μ : E → D) {c : D}
    (hc : c ≠ 0) (a b : E) (n : D) :
    FactorEquative (fun x ↦ c * μ x) a b n ↔ FactorEquative μ a b n :=
  factorEquative_comp_of_commute (g := (c * ·)) (mul_right_injective₀ hc)
    (fun x ↦ mul_left_comm c n x) μ a b

/-- A factor phrase survives an injective change of scale for every measure exactly when the change
commutes with multiplying by its factor. -/
theorem factorEquative_comp_iff_commute [Mul D] [Nontrivial E] {g : D → D} (hg : Injective g)
    {n : D} :
    (∀ (μ : E → D) a b, FactorEquative (g ∘ μ) a b n ↔ FactorEquative μ a b n) ↔
      Function.Commute g (n * ·) := by
  refine ⟨fun h x ↦ ?_, fun hc μ a b ↦ factorEquative_comp_of_commute hg hc μ a b⟩
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  have := (h (fun e ↦ if e = a then n * x else x) a b).2 (by simp [FactorEquative, hab.symm])
  simpa [FactorEquative, hab.symm] using this

/-- A factor phrase survives translating the scale by `c` for every measure exactly when the factor
fixes `c`, since moving the zero point destroys ratios. -/
theorem factorEquative_add_const_iff [Ring D] [Nontrivial E] (c n : D) :
    (∀ (μ : E → D) a b, FactorEquative (fun x ↦ μ x + c) a b n ↔ FactorEquative μ a b n) ↔
      n * c = c := by
  refine (factorEquative_comp_iff_commute (E := E) (add_left_injective c)).trans
    ⟨fun h ↦ by simpa using (h 0).symm, fun h x ↦ by simp [mul_add, h]⟩

end Factor

end Degree
