module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Set.Semiring
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Writer monads

A computation of the writer monad `Writer ω` over a monoid `ω` yields a value, `Writer.val`, and
logs output in `ω`, `Writer.log`: `pure` logs `1` and `m >>= f` has the value of `f` at the value
of `m` and the product of the two logs. The log of `m >>= f` is therefore a right multiple of the
log of `m` (`Writer.log_dvd_bind`), and a value can feed later logging while a log never feeds a
value.

A monoid homomorphism `φ : ω →* ω'` changes the log of a computation by `WriterT.adapt φ`, which
commutes with `pure` and `bind` (`WriterT.adapt_pure`, `WriterT.adapt_bind`), and so does lifting
a computation of the underlying monad (`WriterT.instLawfulMonadLift`).

Logs that are sets under union are `Writer.SetLog P`, with `Writer.ofSet` and `Writer.logSet`
converting to and from `Set P`. In a complete Boolean algebra, taking the infimum of a logged set
is a monoid homomorphism to the algebra under meet, `Writer.SetLog.sInfMonoidHom`.

## Implementation notes

* Sets are a monoid under union through the synonym `SetSemiring`, so `Writer.SetLog P` has
  mathlib's monad laws; an instance on `Set P` itself would also apply to relation types, which
  are sets with composition as their monoid.
* A Boolean algebra is a monoid under meet through the synonym `AsBoolRing`.
-/

@[expose] public section

universe u v

namespace WriterT

variable {M : Type u → Type v} {ω ω' α β : Type u} [Monad M]

@[simp] theorem run_adapt (φ : ω → ω') (m : WriterT ω M α) :
    (WriterT.adapt φ m).run = Prod.map id φ <$> m.run := rfl

variable [LawfulMonad M] [Monoid ω] [Monoid ω']

/-- Lifting a computation into a writer monad with monoid logs commutes with `pure` and `bind`. -/
instance instLawfulMonadLift : LawfulMonadLift M (WriterT ω M) where
  monadLift_pure a := by
    ext
    change (fun a ↦ (a, (1 : ω))) <$> pure a = pure (a, 1)
    simp
  monadLift_bind m f := by
    ext
    change (fun a ↦ (a, (1 : ω))) <$> (m >>= f) = (fun a ↦ (a, 1)) <$> m >>= fun x ↦
      (fun y ↦ (y.1, x.2 * y.2)) <$> (fun a ↦ (a, (1 : ω))) <$> f x.1
    simp

/-- Changing the log along a monoid homomorphism commutes with `pure`. -/
theorem adapt_pure (φ : ω →* ω') (a : α) :
    WriterT.adapt φ (pure a : WriterT ω M α) = pure a := by
  ext
  simp

/-- Changing the log along a monoid homomorphism commutes with `bind`. -/
theorem adapt_bind (φ : ω →* ω') (m : WriterT ω M α) (f : α → WriterT ω M β) :
    WriterT.adapt φ (m >>= f) = WriterT.adapt φ m >>= fun a ↦ WriterT.adapt φ (f a) := by
  ext
  simp

end WriterT

namespace Writer

variable {ω A B : Type u}

/-- The computation with value `a` and log `w`. -/
protected def mk (a : A) (w : ω) : Writer ω A := WriterT.mk (a, w)

/-- The value of a computation is the first component of its run. -/
def val (m : Writer ω A) : A := m.run.1

/-- The log of a computation is the second component of its run. -/
def log (m : Writer ω A) : ω := m.run.2

@[ext]
protected theorem ext {m₁ m₂ : Writer ω A} (hv : m₁.val = m₂.val) (hl : m₁.log = m₂.log) :
    m₁ = m₂ :=
  WriterT.ext _ _ (Prod.ext hv hl)

@[simp] theorem val_mk (a : A) (w : ω) : (Writer.mk a w).val = a := rfl

@[simp] theorem log_mk (a : A) (w : ω) : (Writer.mk a w).log = w := rfl

@[simp] theorem val_tell (w : ω) : (tell w : Writer ω PUnit).val = ⟨⟩ := rfl

@[simp] theorem log_tell (w : ω) : (tell w : Writer ω PUnit).log = w := rfl

section Monoid

variable [Monoid ω]

@[simp] theorem val_pure (a : A) : (pure a : Writer ω A).val = a := rfl

@[simp] theorem log_pure (a : A) : (pure a : Writer ω A).log = 1 := rfl

/-- The value of `m >>= f` is the value of `f` at the value of `m`, so the log of `m` never
reaches it. -/
@[simp] theorem val_bind (m : Writer ω A) (f : A → Writer ω B) :
    (m >>= f).val = (f m.val).val := rfl

@[simp] theorem log_bind (m : Writer ω A) (f : A → Writer ω B) :
    (m >>= f).log = m.log * (f m.val).log := rfl

@[simp] theorem val_map (f : A → B) (m : Writer ω A) : (f <$> m).val = f m.val := rfl

@[simp] theorem log_map (f : A → B) (m : Writer ω A) : (f <$> m).log = m.log := rfl

@[simp] theorem val_seq (f : Writer ω (A → B)) (m : Writer ω A) :
    (f <*> m).val = f.val m.val := rfl

@[simp] theorem log_seq (f : Writer ω (A → B)) (m : Writer ω A) :
    (f <*> m).log = f.log * m.log := rfl

/-- The log of `m >>= f` is a right multiple of the log of `m`, so composition is isotone for the
divisibility preorder of a monoid of logs. -/
theorem log_dvd_bind (m : Writer ω A) (f : A → Writer ω B) : m.log ∣ (m >>= f).log :=
  Dvd.intro _ rfl

end Monoid

section adapt

variable {ω' : Type u}

@[simp] theorem val_adapt (φ : ω → ω') (m : Writer ω A) :
    val (WriterT.adapt φ m : Writer ω' A) = m.val := rfl

@[simp] theorem log_adapt (φ : ω → ω') (m : Writer ω A) :
    log (WriterT.adapt φ m : Writer ω' A) = φ m.log := rfl

end adapt

/-! ### Set logs -/

/-- Sets under union, as a monoid of logs: mathlib's `SetSemiring P` read multiplicatively. -/
abbrev SetLog (P : Type u) := Multiplicative (SetSemiring P)

section SetLog

variable {P : Type u}

/-- The computation with value `a` that logs the set `s`. -/
def ofSet (a : A) (s : Set P) : Writer (SetLog P) A := .mk a (.ofAdd (.ofSet s))

/-- The set a computation logs. -/
def logSet (m : Writer (SetLog P) A) : Set P := m.log.toAdd.toSet

theorem ext_logSet {m₁ m₂ : Writer (SetLog P) A} (hv : m₁.val = m₂.val)
    (hl : m₁.logSet = m₂.logSet) : m₁ = m₂ :=
  Writer.ext hv (congrArg (fun s : Set P ↦ (.ofAdd (.ofSet s) : SetLog P)) hl)

@[simp] theorem val_ofSet (a : A) (s : Set P) : (ofSet a s).val = a := rfl

@[simp] theorem logSet_ofSet (a : A) (s : Set P) : (ofSet a s).logSet = s := rfl

@[simp] theorem logSet_pure (a : A) : (pure a : Writer (SetLog P) A).logSet = ∅ := rfl

@[simp] theorem logSet_bind (m : Writer (SetLog P) A) (f : A → Writer (SetLog P) B) :
    (m >>= f).logSet = m.logSet ∪ (f m.val).logSet := rfl

@[simp] theorem logSet_map (f : A → B) (m : Writer (SetLog P) A) :
    (f <$> m).logSet = m.logSet := rfl

@[simp] theorem logSet_seq (f : Writer (SetLog P) (A → B)) (m : Writer (SetLog P) A) :
    (f <*> m).logSet = f.logSet ∪ m.logSet := rfl

/-- The log of `m >>= f` includes the log of `m`. -/
theorem logSet_subset_bind (m : Writer (SetLog P) A) (f : A → Writer (SetLog P) B) :
    m.logSet ⊆ (m >>= f).logSet :=
  Set.subset_union_left

/-- The infimum of a set, as a monoid homomorphism from sets under union to a complete Boolean
algebra under meet. -/
def SetLog.sInfMonoidHom (α : Type u) [CompleteBooleanAlgebra α] : SetLog α →* AsBoolRing α where
  toFun s := toBoolRing (sInf s.toAdd.toSet)
  map_one' := by simp
  map_mul' s t := by simp [sInf_union]

@[simp] theorem SetLog.sInfMonoidHom_apply {α : Type u} [CompleteBooleanAlgebra α]
    (s : SetLog α) : SetLog.sInfMonoidHom α s = toBoolRing (sInf s.toAdd.toSet) := rfl

end SetLog

end Writer
