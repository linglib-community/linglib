module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Set.Semiring

/-!
# Writer monads

A computation of the writer monad `Writer ω` over a monoid `ω` yields a value, `Writer.val`, and
logs output in `ω`, `Writer.log`: `pure` logs `1` and `m >>= f` has the value of `f` at the value
of `m` and the product of the two logs. A value can therefore feed later logging, while a log
never feeds a value.

A monoid homomorphism `φ : ω →* ω'` changes the log of a computation by `WriterT.adapt φ`, which
commutes with `pure` and `bind` (`WriterT.adapt_pure`, `WriterT.adapt_bind`).

Logs that are sets under union are `Writer.SetLog P`, with `Writer.ofSet` and `Writer.logSet`
converting to and from `Set P`.

## Implementation notes

* `Writer.val`, `Writer.log` and the `SetLog` functions are conveniences over mathlib's
  `WriterT.run`, which returns a pair, and over the synonym below.
* Sets are a monoid under union through the synonym `SetSemiring`, so `Writer.SetLog P` has
  mathlib's monad laws; an instance on `Set P` itself would also apply to relation types, which
  are sets with composition as their monoid.
-/

@[expose] public section

universe u v

namespace WriterT

variable {M : Type u → Type v} {ω ω' α β : Type u} [Monad M]

@[simp] theorem run_adapt (φ : ω → ω') (m : WriterT ω M α) :
    (WriterT.adapt φ m).run = Prod.map id φ <$> m.run := rfl

variable [LawfulMonad M] [Monoid ω] [Monoid ω']

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

end Monoid

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

end SetLog

end Writer
