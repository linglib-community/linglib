module

public import Mathlib.Control.Monad.Writer

/-!
# Writer monads for side-issue meaning

A computation of the writer monad `Writer ω` yields a value and logs output in `ω`. Giorgolo and
Asudeh model conventional implicature this way, in Shan's monadic program: the value of an
expression is its at-issue content, the log collects the side-issue propositions of its parts,
`pure` logs nothing and `bind` appends the logs. Forgetting the log is a monad morphism to `Id`,
and `bind` only extends the log, so content flows from the at-issue dimension into the side-issue
one and never back.

## Main definitions

* `Writer.val`, `Writer.log`: the value and the log of a computation.
* `WriterT.instLawfulMonadList`: the monad laws for list logs, over any lawful monad.

## Main results

* `Writer.val_pure`, `Writer.val_bind`: forgetting the log is a monad morphism.
* `Writer.log_prefix_bind`: the log of `m` is a prefix of the log of `m >>= f`.

## Implementation notes

* Mathlib's two `Monad` instances on `Writer ω`, for `[Monoid ω]` and for
  `[EmptyCollection ω] [Append ω]`, are both `WriterT.monad empty append`; the projection lemmas
  are stated for that monad, as mathlib states `WriterT.run_bind`, and apply under either.
* Mathlib proves the monad laws for monoid logs only, and lists are not a monoid there.
* Giorgolo and Asudeh take the log to be a monoid of propositions and fix it to sets under union.
  They require the arrows to be isotone in the log for the preorder `x ≤ y ↔ ∃ z, x * z = y`,
  which is `x ∣ y` in mathlib. The consumers here log lists, the free monoid, on which this
  preorder is the prefix order.

## References

* [giorgolo-asudeh-2012]
* [shan-2001]
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

end WriterT

namespace Writer

variable {ω A B : Type u}

/-- `Writer.mk a w` is the computation with value `a` and log `w`. -/
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

end Writer
