module

public import Linglib.Semantics.Composition.Writer

/-!
# Giorgolo and Asudeh (2012): ⟨M, η, ⋆⟩ Monads for Conventional Implicatures

Giorgolo and Asudeh treat conventional implicature as the side effect of a Writer monad: an
expression denotes a computation that yields its at-issue value and logs the side-issue
propositions of its parts. Since bind passes its continuation only the value and only extends the
log, no lexical item can read or revise the side-issue dimension, as Potts's restriction on the
flow of information demands and as the impossible modifier *negex* of Barker, Bernardi and Shan
would. Presupposition triggers log their conditions in a second Writer layer. In "John, who likes
cats, likes dogs also" the implicature entails the presupposition once the computation has ended,
which is the paper's reply to the case of AnderBois, Brasoveanu and Henderson against
multidimensionality.

## Main definitions

* `M`: the two-channel monad, conventional implicatures over presuppositions.
* `write`, `check`: logging an implicature and a presuppositional condition.

## Main results

* `seq_eq_bind_bind`: Shan's application (15) is the monad's `<*>`.
* `Ex20.atIssue_sentence`, `Ex20.ciLog_sentence`, `Ex20.presupLog_sentence`: the three
  dimensions of Figure 1.
* `Ex20.presupposition_of_ci`: the implicature entails the presupposition.
* `Ex20.atIssue_sentence_congr`: the relative clause never reaches the at-issue value.

## Implementation notes

* The two channels are the transformer `WriterT (List CI) (Writer (List Presup))`, over the Writer
  surface of `Semantics/Composition/Writer.lean`, with `check` lifted from the presupposition
  monad as fn. 4 prescribes. The paper's logs are sets under union; these are lists.
* Glue's `⊸` elimination is the monad's `<*>`, and `⊸*` elimination plain application to monadic
  arguments; the introduction rules, which reason hypothetically, are not needed.
* The extension of *like* is a parameter: the presupposition of *also* follows from the logged
  implicature alone, given that cats are not dogs.

## References

* [giorgolo-asudeh-2012]
* [shan-2001]
* [potts-2005]
* [anderbois-brasoveanu-henderson-2010]
* [barker-bernardi-shan-2010]
-/

@[expose] public section

namespace GiorgoloAsudeh2012

universe u

variable {CI Presup A B : Type u}

/-! ### The two channels -/

/-- The two-channel monad logs conventional implicatures in the transformer and presuppositional
conditions in the monad it transforms, so that a computation's result is the paper's
⟨⟨value, implicatures⟩, presuppositions⟩. -/
abbrev M (CI Presup : Type u) := WriterT (List CI) (Writer (List Presup))

/-- The at-issue value of a computation. -/
def atIssue (m : M CI Presup A) : A := m.run.val.1

/-- The conventional implicatures a computation logs. -/
def ciLog (m : M CI Presup A) : List CI := m.run.val.2

/-- The presuppositional conditions a computation logs. -/
def presupLog (m : M CI Presup A) : List Presup := m.run.log

/-- `write t` logs the conventional implicature `t`, the paper's `write(t) = ⟨⊥, {t}⟩`. -/
def write (p : CI) : M CI Presup PUnit := tell [p]

/-- `check t` logs a condition to be checked once the computation has ended, lifted from the
presupposition monad as the paper's fn. 4 prescribes. -/
def check (p : Presup) : M CI Presup PUnit := monadLift (tell [p] : Writer (List Presup) PUnit)

@[simp] theorem atIssue_pure (a : A) : atIssue (pure a : M CI Presup A) = a := rfl

@[simp] theorem ciLog_pure (a : A) : ciLog (pure a : M CI Presup A) = [] := rfl

@[simp] theorem presupLog_pure (a : A) : presupLog (pure a : M CI Presup A) = [] := rfl

@[simp] theorem atIssue_bind (m : M CI Presup A) (f : A → M CI Presup B) :
    atIssue (m >>= f) = atIssue (f (atIssue m)) := rfl

@[simp] theorem ciLog_bind (m : M CI Presup A) (f : A → M CI Presup B) :
    ciLog (m >>= f) = ciLog m ++ ciLog (f (atIssue m)) := rfl

@[simp] theorem presupLog_bind (m : M CI Presup A) (f : A → M CI Presup B) :
    presupLog (m >>= f) = presupLog m ++ presupLog (f (atIssue m)) := rfl

@[simp] theorem ciLog_write (p : CI) : ciLog (write p : M CI Presup PUnit) = [p] := rfl

@[simp] theorem presupLog_write (p : CI) : presupLog (write p : M CI Presup PUnit) = [] := rfl

@[simp] theorem ciLog_check (p : Presup) : ciLog (check p : M CI Presup PUnit) = [] := rfl

@[simp] theorem presupLog_check (p : Presup) : presupLog (check p : M CI Presup PUnit) = [p] :=
  rfl

theorem ciLog_prefix_bind (m : M CI Presup A) (f : A → M CI Presup B) :
    ciLog m <+: ciLog (m >>= f) :=
  ⟨ciLog (f (atIssue m)), rfl⟩

/-! ### Shan's application

Glue's `⊸` elimination composes at-issue items by Shan's application (15),
`A(f)(x) = f ⋆ λg. x ⋆ λy. η(g y)`, which is the monad's `<*>`; the value is the application and
both logs are threaded. -/

/-- Shan's application (15) is the monad's `<*>`. -/
theorem seq_eq_bind_bind (f : M CI Presup (A → B)) (x : M CI Presup A) :
    f <*> x = f >>= fun g ↦ x >>= fun y ↦ pure (g y) := by
  simp only [seq_eq_bind_map, map_eq_pure_bind]

@[simp] theorem atIssue_seq (f : M CI Presup (A → B)) (x : M CI Presup A) :
    atIssue (f <*> x) = atIssue f (atIssue x) := rfl

@[simp] theorem ciLog_seq (f : M CI Presup (A → B)) (x : M CI Presup A) :
    ciLog (f <*> x) = ciLog f ++ ciLog x := rfl

@[simp] theorem presupLog_seq (f : M CI Presup (A → B)) (x : M CI Presup A) :
    presupLog (f <*> x) = presupLog f ++ presupLog x := rfl

/-! ### "John, who likes cats, likes dogs also" (20) -/

namespace Ex20

/-- John, the cats and the dogs. -/
inductive E
  | john
  | cats
  | dogs
  deriving DecidableEq, Repr

variable (like : E → E → Prop)

/-- The prosodic element `comma` of Table 1, `λj λl. j ⋆ λx. l ⋆ λf. write(f x) ⋆ λ_. η(x)`,
introduces the non-restrictive relative clause; it logs the clause's content about its anchor and
returns the anchor. -/
def comma (j : M Prop Prop E) (l : M Prop Prop (E → Prop)) : M Prop Prop E :=
  j >>= fun x ↦ l >>= fun f ↦ write (f x) >>= fun _ ↦ pure x

/-- The presupposition trigger `also` of Table 1,
`λv λo λs. s ⋆ λx. v ⋆ λf. o ⋆ λy. check(∃z. f z x ∧ z ≠ y) ⋆ λ_. η(f y x)`, logs the
presupposition that the subject bears the relation to something other than the object and returns
the at-issue proposition. -/
def also (v : M Prop Prop (E → E → Prop)) (o s : M Prop Prop E) : M Prop Prop Prop :=
  s >>= fun x ↦ v >>= fun f ↦ o >>= fun y ↦ check (∃ z, f z x ∧ z ≠ y) >>= fun _ ↦ pure (f y x)

/-- The at-issue items of Table 1, η-lifted. -/
def john : M Prop Prop E := pure .john

def who : M Prop Prop ((E → Prop) → E → Prop) := pure id

def likes : M Prop Prop (E → E → Prop) := pure fun y x ↦ like x y

def cats : M Prop Prop E := pure .cats

def dogs : M Prop Prop E := pure .dogs

/-- "who likes cats", by `⊸` elimination. -/
def whoLikesCats : M Prop Prop (E → Prop) := who <*> (likes like <*> cats)

/-- The sentence, by `⊸*` elimination. -/
def sentence : M Prop Prop Prop := also (likes like) dogs (comma john (whoLikesCats like))

/-- The at-issue proposition of Figure 1 is that John likes dogs. -/
theorem atIssue_sentence : atIssue (sentence like) = like .john .dogs := rfl

/-- The side-issue log of Figure 1 holds that John likes cats. -/
theorem ciLog_sentence : ciLog (sentence like) = [like .john .cats] := rfl

/-- The presupposition of *also* in Figure 1 is that John likes something other than the
dogs. -/
theorem presupLog_sentence :
    presupLog (sentence like) = [∃ z, like .john z ∧ z ≠ .dogs] := rfl

theorem presupposition_of_ci (h : ∀ q ∈ ciLog (sentence like), q) :
    ∀ p ∈ presupLog (sentence like), p := by
  simp only [presupLog_sentence, List.mem_singleton, forall_eq]
  exact ⟨.cats, h _ (by simp [ciLog_sentence]), by decide⟩

theorem atIssue_sentence_congr (l l' : M Prop Prop (E → Prop)) :
    atIssue (also (likes like) dogs (comma john l)) =
      atIssue (also (likes like) dogs (comma john l')) := rfl

end Ex20

end GiorgoloAsudeh2012
