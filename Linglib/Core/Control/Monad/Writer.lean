module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Control.Monad.Writer

/-!
# Writer monads

A computation of the writer monad `Writer ω` yields a value and logs output in `ω`: `pure` logs
nothing and `bind` appends the logs. [Forgetting the log](##val_bind) is a monad morphism to `Id`,
and [`bind` only extends the log](##log_prefix_bind), so a value can feed later logging while the
log never feeds a value.

## Main definitions

* `Writer.val`, `Writer.log`: the value and the log of a computation.
* `WriterT.instLawfulMonadList`: the monad laws for list logs, over any lawful monad.
* `WriterT.instLawfulMonadLift`: lifting into a writer monad with monoid logs is a monad morphism.
* `Writer.adapt_pure`, `Writer.adapt_bind`: changing the log along a monoid homomorphism is a
  monad morphism.

## Implementation notes

* Mathlib's two `Monad` instances on `Writer ω`, for `[Monoid ω]` and for
  `[EmptyCollection ω] [Append ω]`, are both `WriterT.monad empty append`; the projection lemmas
  are stated for that monad, as mathlib states `WriterT.run_bind`, and apply under either.
* Mathlib proves the monad laws for monoid logs only, and lists are not a monoid there.
-/

@[expose] public section

universe u v

namespace WriterT

variable {M : Type u → Type v} {P : Type u} [Monad M] [LawfulMonad M]

/-- A writer monad with list logs is lawful over any lawful monad. -/
instance instLawfulMonadList : LawfulMonad (WriterT (List P) M) := LawfulMonad.mk'
  (id_map := fun _ ↦ by ext; simp)
  (pure_bind := fun _ _ ↦ by ext; simp)
  (bind_assoc := fun _ _ _ ↦ by ext; simp)
  (bind_pure_comp := fun _ _ ↦ by ext; simp)

/-- Lifting a computation into a writer monad with monoid logs commutes with `pure` and `bind`. -/
instance instLawfulMonadLift {ω : Type u} [Monoid ω] : LawfulMonadLift M (WriterT ω M) where
  monadLift_pure a := by
    ext
    change (fun a ↦ (a, (1 : ω))) <$> pure a = pure (a, 1)
    simp
  monadLift_bind m f := by
    ext
    change (fun a ↦ (a, (1 : ω))) <$> (m >>= f) = (fun a ↦ (a, 1)) <$> m >>= fun x ↦
      (fun y ↦ (y.1, x.2 * y.2)) <$> (fun a ↦ (a, (1 : ω))) <$> f x.1
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

section Monad

variable (empty : ω) (append : ω → ω → ω)

@[simp] theorem val_pure (a : A) :
    letI := WriterT.monad (M := Id) empty append
    (pure a : Writer ω A).val = a := rfl

@[simp] theorem log_pure (a : A) :
    letI := WriterT.monad (M := Id) empty append
    (pure a : Writer ω A).log = empty := rfl

/-- The value of `m >>= f` is the value of `f` at the value of `m`, so the log of `m` never
reaches it. -/
@[simp] theorem val_bind (m : Writer ω A) (f : A → Writer ω B) :
    letI := WriterT.monad (M := Id) empty append
    (m >>= f).val = (f m.val).val := rfl

@[simp] theorem log_bind (m : Writer ω A) (f : A → Writer ω B) :
    letI := WriterT.monad (M := Id) empty append
    (m >>= f).log = append m.log (f m.val).log := rfl

@[simp] theorem val_map (f : A → B) (m : Writer ω A) :
    letI := WriterT.monad (M := Id) empty append
    (f <$> m).val = f m.val := rfl

@[simp] theorem log_map (f : A → B) (m : Writer ω A) :
    letI := WriterT.monad (M := Id) empty append
    (f <$> m).log = m.log := rfl

@[simp] theorem val_seq (f : Writer ω (A → B)) (m : Writer ω A) :
    letI := WriterT.monad (M := Id) empty append
    (f <*> m).val = f.val m.val := rfl

@[simp] theorem log_seq (f : Writer ω (A → B)) (m : Writer ω A) :
    letI := WriterT.monad (M := Id) empty append
    (f <*> m).log = append f.log m.log := rfl

end Monad

/-- The log of `m >>= f` extends the log of `m`, so composition is isotone for the prefix order
on list logs. -/
theorem log_prefix_bind {P : Type u} (m : Writer (List P) A) (f : A → Writer (List P) B) :
    m.log <+: (m >>= f).log :=
  ⟨(f m.val).log, rfl⟩

section adapt

variable {ω' : Type u}

@[simp] theorem val_adapt (φ : ω → ω') (m : Writer ω A) :
    val (WriterT.adapt φ m : Writer ω' A) = m.val := rfl

@[simp] theorem log_adapt (φ : ω → ω') (m : Writer ω A) :
    log (WriterT.adapt φ m : Writer ω' A) = φ m.log := rfl

variable [Monoid ω] [Monoid ω'] (φ : ω →* ω')

/-- Changing the log along a monoid homomorphism commutes with `pure`. -/
theorem adapt_pure (a : A) : (WriterT.adapt φ (pure a : Writer ω A) : Writer ω' A) = pure a :=
  Writer.ext rfl (map_one φ)

/-- Changing the log along a monoid homomorphism commutes with `bind`. -/
theorem adapt_bind (m : Writer ω A) (f : A → Writer ω B) :
    (WriterT.adapt φ (m >>= f) : Writer ω' B) =
      (WriterT.adapt φ m : Writer ω' A) >>= fun a ↦ WriterT.adapt φ (f a) :=
  Writer.ext rfl (map_mul φ _ _)

end adapt

/-- The log of `m >>= f` is a right multiple of the log of `m`, so composition is isotone for the
divisibility preorder of a monoid of logs. -/
theorem log_dvd_bind [Monoid ω] (m : Writer ω A) (f : A → Writer ω B) : m.log ∣ (m >>= f).log :=
  Dvd.intro _ rfl

end Writer
