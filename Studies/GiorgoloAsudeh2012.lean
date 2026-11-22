module

public import Linglib.Core.Control.Monad.Writer
public import Linglib.Data.Examples.GiorgoloAsudeh2012
public import Linglib.Semantics.ConventionalImplicature

/-!
# Giorgolo and Asudeh (2012): ⟨M, η, ⋆⟩ Monads for Conventional Implicatures

A meaning is a computation of a writer monad: it yields an at-issue value and logs a set of
side-issue propositions. The unit `η` logs nothing, and `m ⋆ f` has the value of `f` at the value
of `m` and the union of the two logs, `⟨x, P⟩ ⋆ f = ⟨π₁ (f x), P ∪ π₂ (f x)⟩`. A second writer
layer logs the conditions that presupposition triggers impose, to be checked once composition has
ended. In "John, who likes cats, likes dogs also" the logged implicature then entails the logged
presupposition, although no step of the composition reads either log.

## Main definitions

* `M`: the two-channel monad, conventional implicatures over presuppositions.
* `write`, `check`: logging an implicature and a presuppositional condition.
* `comma`, `also`: the lexical entries that log, a non-restrictive relative clause and an
  additive presupposition trigger.
* `toTwoDim`: the two-dimensional meaning of a computation, whose not-at-issue content is the meet
  of the logged implicatures; it changes the log along `TwoDim.sInfHom`.

## Implementation notes

* The paper allows any monoid of collections and fixes sets of propositions under union, which
  is `Writer.SetLog T`. `M T` is the transformer
  `WriterT (SetLog T) (Writer (SetLog T))`, with `check` lifted from the presupposition monad, and
  `ciLog` and `presupLog` return the underlying sets. The paper's condition that arrows be
  isotone for the preorder `x ≤ y ↔ ∃ z, x · z = y`, which is `Writer.log_dvd_bind` for any
  monoid, is then inclusion of logs.
* Glue's `⊸` elimination is the monad's `<*>`, and `⊸*` elimination is application of a function
  to monadic arguments. The introduction rules, which reason hypothetically, are not formalized.
* `comma` and `also` take monadic arguments, so their isotonicity is not an instance of
  `ciLog_subset_bind`; it is read off `ciLog_comma` and `ciLog_also`.
* The examples the paper discusses are the rows of `Data/Examples/GiorgoloAsudeh2012.json`. The
  worked sentence is `Examples.ga2012_20`; the paper's account of the binding contrast
  `Examples.ga2012_9` and `Examples.ga2012_10` and of the ellipsis and anaphora cases rests on
  discourse-level resolution after composition, which is not formalized.

## References

* [giorgolo-asudeh-2012]
* [shan-2001]
* [potts-2005]
* [anderbois-brasoveanu-henderson-2010]
* [barker-bernardi-shan-2010]
-/

@[expose] public section

namespace GiorgoloAsudeh2012

open ConventionalImplicature Writer

universe u

variable {T W A B : Type u}

/-! ### The two channels -/

/-- The two-channel monad over propositions `T` logs conventional implicatures in the transformer
and presuppositional conditions in the monad it transforms, so that a computation's result is
`⟨⟨value, implicatures⟩, presuppositions⟩`. -/
abbrev M (T : Type u) := WriterT (SetLog T) (Writer (SetLog T))

/-- The at-issue value of a computation. -/
def atIssue (m : M T A) : A := m.run.val.1

/-- The conventional implicatures a computation logs. -/
def ciLog (m : M T A) : Set T := m.run.val.2.toAdd.toSet

/-- The presuppositional conditions a computation logs. -/
def presupLog (m : M T A) : Set T := m.run.logSet

/-- `write t` logs the conventional implicature `t`, as `⟨⊥, {t}⟩`. -/
def write (t : T) : M T PUnit := tell (.ofAdd (.ofSet {t}))

/-- `check t` logs the condition `t`, to be checked once the computation has ended; it is
`⟨⊥, {t}⟩` in the presupposition monad, lifted to the transformer. -/
def check (t : T) : M T PUnit := monadLift (Writer.ofSet ⟨⟩ {t})

@[simp] theorem atIssue_pure (a : A) : atIssue (pure a : M T A) = a := rfl

@[simp] theorem ciLog_pure (a : A) : ciLog (pure a : M T A) = ∅ := rfl

@[simp] theorem presupLog_pure (a : A) : presupLog (pure a : M T A) = ∅ := rfl

@[simp] theorem atIssue_bind (m : M T A) (f : A → M T B) :
    atIssue (m >>= f) = atIssue (f (atIssue m)) := rfl

@[simp] theorem ciLog_bind (m : M T A) (f : A → M T B) :
    ciLog (m >>= f) = ciLog m ∪ ciLog (f (atIssue m)) := rfl

@[simp] theorem presupLog_bind (m : M T A) (f : A → M T B) :
    presupLog (m >>= f) = presupLog m ∪ presupLog (f (atIssue m)) := rfl

@[simp] theorem atIssue_map (g : A → B) (m : M T A) : atIssue (g <$> m) = g (atIssue m) := rfl

@[simp] theorem ciLog_map (g : A → B) (m : M T A) : ciLog (g <$> m) = ciLog m := rfl

@[simp] theorem presupLog_map (g : A → B) (m : M T A) : presupLog (g <$> m) = presupLog m := rfl

@[simp] theorem ciLog_write (t : T) : ciLog (write t) = {t} := rfl

@[simp] theorem presupLog_write (t : T) : presupLog (write t) = ∅ := rfl

@[simp] theorem ciLog_check (t : T) : ciLog (check t) = ∅ := rfl

@[simp] theorem presupLog_check (t : T) : presupLog (check t) = {t} := rfl

/-- The log of `m >>= f` includes the log of `m`, so no item composed by `⋆` removes or revises
an implicature already logged. -/
theorem ciLog_subset_bind (m : M T A) (f : A → M T B) : ciLog m ⊆ ciLog (m >>= f) :=
  Set.subset_union_left

theorem presupLog_subset_bind (m : M T A) (f : A → M T B) :
    presupLog m ⊆ presupLog (m >>= f) :=
  Set.subset_union_left

/-! ### Shan's application

Glue's `⊸` elimination composes at-issue items by the application of [shan-2001],
`A(f)(x) = f ⋆ λg. x ⋆ λy. η(g y)`, which is the monad's `<*>`; the value is the application and
both logs are threaded. -/

theorem seq_eq_bind_bind (f : M T (A → B)) (x : M T A) :
    f <*> x = f >>= fun g ↦ x >>= fun y ↦ pure (g y) := by
  simp only [seq_eq_bind_map, map_eq_pure_bind]

@[simp] theorem atIssue_seq (f : M T (A → B)) (x : M T A) :
    atIssue (f <*> x) = atIssue f (atIssue x) := rfl

@[simp] theorem ciLog_seq (f : M T (A → B)) (x : M T A) :
    ciLog (f <*> x) = ciLog f ∪ ciLog x := rfl

@[simp] theorem presupLog_seq (f : M T (A → B)) (x : M T A) :
    presupLog (f <*> x) = presupLog f ∪ presupLog x := rfl

/-! ### The entries that log -/

/-- The prosodic element `comma`, `λj λl. j ⋆ λx. l ⋆ λf. write(f x) ⋆ λ_. η(x)`, introduces a
non-restrictive relative clause: it logs the clause's content about its anchor and returns the
anchor. -/
def comma (j : M T A) (l : M T (A → T)) : M T A :=
  j >>= fun x ↦ l >>= fun f ↦ write (f x) >>= fun _ ↦ pure x

/-- The presupposition trigger `also`,
`λv λo λs. s ⋆ λx. v ⋆ λf. o ⋆ λy. check(∃z. f z x ∧ z ≠ y) ⋆ λ_. η(f y x)`, logs the condition
that the subject bears the relation to something other than the object and returns the at-issue
proposition. -/
def also (v : M (W → Prop) (B → A → W → Prop)) (o : M (W → Prop) B) (s : M (W → Prop) A) :
    M (W → Prop) (W → Prop) :=
  s >>= fun x ↦ v >>= fun f ↦ o >>= fun y ↦
    check (fun w ↦ ∃ z, f z x w ∧ z ≠ y) >>= fun _ ↦ pure (f y x)

section comma

variable (j : M T A) (l : M T (A → T))

@[simp] theorem atIssue_comma : atIssue (comma j l) = atIssue j := rfl

@[simp] theorem ciLog_comma :
    ciLog (comma j l) = ciLog j ∪ ciLog l ∪ {atIssue l (atIssue j)} := by
  simp [comma]

@[simp] theorem presupLog_comma : presupLog (comma j l) = presupLog j ∪ presupLog l := by
  simp [comma]

end comma

section also

variable (v : M (W → Prop) (B → A → W → Prop)) (o : M (W → Prop) B) (s : M (W → Prop) A)

@[simp] theorem atIssue_also :
    atIssue (also v o s) = atIssue v (atIssue o) (atIssue s) := rfl

@[simp] theorem ciLog_also : ciLog (also v o s) = ciLog s ∪ ciLog v ∪ ciLog o := by
  simp [also, Set.union_assoc]

@[simp] theorem presupLog_also :
    presupLog (also v o s) = presupLog s ∪ presupLog v ∪ presupLog o ∪
      {fun w ↦ ∃ z, atIssue v z (atIssue s) w ∧ z ≠ atIssue o} := by
  simp [also, Set.union_assoc]

end also

/-! ### Two-dimensional meanings -/

/-- The two-dimensional meaning of a computation forgets its presuppositions and takes the meet
of the implicatures it logs. -/
def toTwoDim (m : M (W → Prop) A) : TwoDim W A := .ofSetLog (.mk (atIssue m) m.run.val.2)

@[simp] theorem toTwoDim_atIssue (m : M (W → Prop) A) : (toTwoDim m).atIssue = atIssue m := by
  simp [toTwoDim]

@[simp] theorem toTwoDim_notAtIssue (m : M (W → Prop) A) :
    (toTwoDim m).notAtIssue = sInf (ciLog m) := rfl

@[simp] theorem toTwoDim_pure (a : A) : toTwoDim (pure a : M (W → Prop) A) = pure a :=
  TwoDim.ext (by simp) (by simp)

/-- `toTwoDim` commutes with `⋆`, the union of logs becoming the meet of not-at-issue content. -/
theorem toTwoDim_bind (m : M (W → Prop) A) (f : A → M (W → Prop) B) :
    toTwoDim (m >>= f) = toTwoDim m >>= fun a ↦ toTwoDim (f a) :=
  TwoDim.ext (by simp) (by simp [sInf_union])

/-- The two-dimensional meaning of `comma` applied to an at-issue predicate is the CI application
of [potts-2005]. -/
theorem toTwoDim_comma_pure (j : M (W → Prop) A) (f : A → W → Prop) :
    toTwoDim (comma j (pure f)) = (toTwoDim j).ciApply f :=
  TwoDim.ext (by simp) (by simp [inf_comm])

/-! ### "John, who likes cats, likes dogs also" -/

namespace Ex20

/-- John, the cats and the dogs. -/
inductive E
  | john
  | cats
  | dogs
  deriving DecidableEq, Repr

variable {W : Type} (like : E → E → W → Prop)

/-- The at-issue items, η-lifted. -/
def john : M (W → Prop) E := pure .john

def who : M (W → Prop) ((E → W → Prop) → E → W → Prop) := pure id

def likes : M (W → Prop) (E → E → W → Prop) := pure fun y x ↦ like x y

def cats : M (W → Prop) E := pure .cats

def dogs : M (W → Prop) E := pure .dogs

/-- "who likes cats", by `⊸` elimination. -/
def whoLikesCats : M (W → Prop) (E → W → Prop) := who <*> (likes like <*> cats)

/-- The sentence, by `⊸*` elimination. -/
def sentence : M (W → Prop) (W → Prop) :=
  also (likes like) dogs (comma john (whoLikesCats like))

theorem atIssue_sentence : atIssue (sentence like) = like .john .dogs := rfl

theorem ciLog_sentence : ciLog (sentence like) = {like .john .cats} := by
  simp [sentence, whoLikesCats, john, who, likes, cats, dogs]

theorem presupLog_sentence :
    presupLog (sentence like) = {fun w ↦ ∃ z, like .john z w ∧ z ≠ .dogs} := by
  simp [sentence, whoLikesCats, john, who, likes, cats, dogs]

/-- Once both logs are exposed, the conventional implicatures entail the presuppositions: John
likes cats, and cats are not dogs. -/
theorem sInf_ciLog_le_sInf_presupLog :
    sInf (ciLog (sentence like)) ≤ sInf (presupLog (sentence like)) := by
  rw [ciLog_sentence, presupLog_sentence, sInf_singleton, sInf_singleton]
  exact fun w h ↦ ⟨.cats, h, by decide⟩

end Ex20

end GiorgoloAsudeh2012
