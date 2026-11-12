module

public import Mathlib.Control.Monad.Writer
public import Mathlib.Control.Traversable.Basic
public import Mathlib.Data.Part

/-!
# Writer monads

A computation of the writer monad `Writer ω` yields a value and logs output in `ω`: `pure` logs
nothing and `bind` appends the logs. [Forgetting the log](##val_bind) is a monad morphism to `Id`,
and [`bind` only extends the log](##log_prefix_bind), so a value can feed later logging while the
log never feeds a value. With truth values for logs, combined by conjunction, a computation is
[a partial value](##Writer.toPart) defined where its log holds, and that passage is
[a morphism of applicative functors](##Writer.toPartHom).

## Main definitions

* `Writer.val`, `Writer.log`: the value and the log of a computation.
* `WriterT.instLawfulMonadList`: the monad laws for list logs, over any lawful monad.

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

end Writer

/-! ### Truth-value logs and partiality -/

namespace Writer

variable {α : Type}

/-- The writer monad over truth values under conjunction. -/
abbrev propMonad : Monad (Writer Prop) := WriterT.monad (M := Id) True And

attribute [local instance] propMonad

/-- A value with a logged truth value is the partial value defined where the log holds. -/
def toPart (m : Writer Prop α) : Part α := ⟨m.log, fun _ ↦ m.val⟩

@[simp] theorem toPart_dom (m : Writer Prop α) : m.toPart.Dom = m.log := rfl

@[simp] theorem mem_toPart {m : Writer Prop α} {a : α} : a ∈ m.toPart ↔ m.log ∧ m.val = a :=
  ⟨fun ⟨h, e⟩ ↦ ⟨h, e⟩, fun ⟨h, e⟩ ↦ ⟨h, e⟩⟩

/-- `Writer.toPart` as a morphism of applicative functors: it preserves the unit and
application. -/
def toPartHom : ApplicativeTransformation (Writer Prop) Part where
  app _ := toPart
  preserves_pure' _ := Part.ext' (iff_of_true trivial trivial) fun _ _ ↦ rfl
  preserves_seq' _ _ := Part.ext' ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩ fun _ _ ↦ rfl

/-- Two computations give the same partial value when their logs agree and their values agree
where the log holds: `toPart` forgets the value where the log fails. -/
theorem toPart_eq_iff {m n : Writer Prop α} :
    m.toPart = n.toPart ↔ (m.log ↔ n.log) ∧ (m.log → m.val = n.val) := by
  refine ⟨fun h ↦ ?_, fun ⟨hd, hv⟩ ↦ Part.ext' hd fun hx _ ↦ hv hx⟩
  have hd : m.log ↔ n.log := iff_of_eq (congrArg Part.Dom h)
  exact ⟨hd, fun hx ↦ ((mem_toPart (m := n)).1 (h ▸ mem_toPart.2 ⟨hx, rfl⟩)).2.symm⟩

end Writer
