module

public import Linglib.Data.Examples.Stalnaker1978
public import Linglib.Semantics.Dynamic.Update
public import Linglib.Semantics.Reference.Kaplan
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Basic.Sign.Defs
public import Linglib.Data.Examples.Readers

/-!
# Stalnaker (1978): Assertion

Stalnaker represents what an utterance says as a matrix of truth values. A *propositional
concept* takes each possible world, in its role as the context that determines what is said, to
the proposition expressed there, so a concept is a character whose contexts are the worlds
themselves. Its *diagonal proposition*, true at a world when what is said there is true there,
is the character's diagonal. The *dagger* expresses the diagonal at every context. A sentence is
a priori, true as uttered in every context, when its diagonal is necessary, which is what
[necessity applied to the dagger](##box_dagger_iff) says. The dagger evaluates its argument at
the context given by the world of evaluation, so it is a two-dimensional operator, one that
[no operation on propositions can match](##isMonster_dagger).

A context is represented by its *context set*, the worlds compatible with what the speaker
presupposes, and the essential effect of an assertion is to eliminate the worlds of the context
set incompatible with what is said. Three principles constrain assertion. What is asserted is
true in some but not all worlds of the context set. What is said at each world of the context set
has a truth value at each of them, so that
[a semantic presupposition is presupposed by the speaker](##subset_of_secondPrinciple). And what is
said is the same within the context set, which is exactly
[what makes the essential effect independent of which world is actual](##thirdPrinciple_iff). An
utterance that violates the third principle is reinterpreted as asserting its diagonal. With
rigid designators, *That is either Zsa Zsa Gabor or Elizabeth Anscombe* expresses a necessary
truth or a necessary falsehood at each world, so that
[only its diagonal can be asserted](##gaborOrAnscombe_diag), and the same reinterpretation
[makes *Sherlock Holmes does not exist* true at the actual world alone](##holmesDoesNotExist_diag).

Under the third principle the essential effect is intersection with the diagonal proposition, and
under the dagger it always is. Taking assertion as an eliminative and distributive update of
context sets, the diagonal is forced: it is
[the only such update with the essential effect of what is said wherever the actual world is
known](##eq_up_diag), so that Stalnaker's reinterpretation is the update by the diagonal.

## Implementation notes

* A propositional concept is a `Kaplan.Character W W Prop`, and its diagonal proposition is
  `Kaplan.Character.diag id`. The dagger is the substrate's `Kaplan.shiftBy` with the context
  shifted to the world of evaluation. The upside-down dagger of note 6, which projects the
  diagonal onto the vertical, is `Kaplan.Character.dthat` of the diagonal.
* The worlds `i`, `j` and `k` of each example are one type, `World`. Each example's matrix is
  derived from the facts the paper stipulates for it. Demonstratives, indexicals and terms whose
  reference is fixed by a description are `Kaplan.Character.dthat`, and proper names are constant
  characters, which is the paper's assumption that both are rigid designators.
* A truth-value gap, for the second principle, is the value `0` of a `SignType`-valued concept, as
  in `Semantics/Presupposition/Basic.lean`. A sentence that fails to express a proposition at a
  world has a row of gaps there.
* The third principle is stated with the clarification of note 13: what is said at two worlds of
  the context set need coincide only within the context set.
* The paper proposes the essential effect, not an update rule. That the diagonal is the only
  eliminative and distributive update agreeing with it where the actual world is known is this
  file's reconstruction, through `DynamicSemantics.CCP.isClassical_iff_up_down_eq`.
* Locators are to the 1978 printing.

## Errata

* On p. 330, *Sherlock Holmes does not exist*, if the name does not refer, is said to express a
  necessarily false proposition, by the rule that the sentence is true at the worlds whose domain
  does not contain the person the name refers to. That rule makes it necessarily true, as the
  first row of matrix G, true throughout, shows (`holmesDoesNotExist_diag`). The 1999 reprint in
  *Context and Content* reads "necessarily true".

## TODO

* *Hesperus is identical with Phosphorus*, *it is now three o'clock* and *an ophthalmologist is
  an eye doctor* (p. 328) are diagonalized because what the words say varies across the context
  set. Their concepts need a model of that variation.
* The counterfactual *If Aristotle hadn't existed, the history of philosophy would have been very
  different from the way it was* (p. 331) needs no diagonalization, since every context
  appropriate to it presupposes that Aristotle exists. Stating this needs a conditional over
  propositional concepts.
* Nondefective contexts, the effect of the fact that an utterance occurred, and rejection, which
  blocks only the essential effect (pp. 322–324), are not formalized.

## References

* [stalnaker-1978]
-/

@[expose] public section

namespace Stalnaker1978

open Kaplan DynamicSemantics
open Kaplan.Character (dthat const dthat_isDirectlyReferential const_isDirectlyReferential)

/-! ### Two-dimensional operators -/

section Operators

variable {W C V α β : Type*}

/-- The dagger takes the diagonal proposition and projects it onto the horizontal: `†P` expresses
the diagonal of `P` relative to every context. It evaluates `P` at the context given by the world
of evaluation. -/
def dagger : Character W W α → Character W W α := shiftBy fun _ w ↦ w

@[simp] theorem dagger_apply (χ : Character W W α) (v w : W) : dagger χ v w = χ w w := rfl

-- p. 319
theorem dagger_apply_eq_diag (χ : Character W W α) (v : W) : dagger χ v = χ.diag id := rfl

-- p. 319: the dagger keeps a constant propositional concept as it is
theorem dagger_eq_self {χ : Character W W α} (h : ∀ v v', χ v = χ v') : dagger χ = χ :=
  funext fun v ↦ funext fun w ↦ congrFun (h w v) w

-- p. 319: the dagger yields a constant propositional concept
theorem dagger_dagger (χ : Character W W α) : dagger (dagger χ) = dagger χ :=
  dagger_eq_self fun _ _ ↦ rfl

/-- An operator is extensional when its value at a point depends only on the value of its
argument there. -/
def IsExtensional (O : Character C V α → Character C V β) : Prop :=
  ∃ o : α → β, ∀ χ c v, O χ c v = o (χ c v)

/-- An operator is one-dimensional when the proposition it yields at a context depends only on
the proposition its argument expresses there. -/
def IsOneDimensional (O : Character C V α → Character C V β) : Prop :=
  ∃ o : Content V α → Content V β, ∀ χ c, O χ c = o (χ c)

-- p. 320: each kind of operator generalizes the kind before it
theorem IsExtensional.isOneDimensional {O : Character C V α → Character C V β}
    (h : IsExtensional O) : IsOneDimensional O :=
  h.elim fun o ho ↦ ⟨fun p v ↦ o (p v), fun χ c ↦ funext (ho χ c)⟩

theorem IsOneDimensional.not_isMonster {O : Character C V α → Character C V β}
    (h : IsOneDimensional O) : ¬ IsMonster O :=
  fun hO ↦ h.elim fun o ho ↦ hO ⟨fun _ ↦ o, ho⟩

/-- Propositional necessity: `□P` expresses at a context the proposition true at a world iff what
`P` expresses there is the necessary proposition. -/
def box (χ : Character C V Prop) : Character C V Prop := fun c _ ↦ ∀ v, χ c v

-- p. 320
theorem isOneDimensional_box : IsOneDimensional (box : Character C V Prop → _) :=
  ⟨fun p _ ↦ ∀ v, p v, fun _ _ ↦ rfl⟩

-- p. 319: the dagger is two-dimensional, not a function of what its argument expresses
theorem isMonster_dagger [Nontrivial W] [Nontrivial α] :
    IsMonster (dagger : Character W W α → Character W W α) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne W
  exact (isMonster_shiftBy_iff _).2 ⟨a, b, hab.symm⟩

-- p. 320: the square-dagger is the a priori truth operator
theorem box_dagger_iff (χ : Character W W Prop) (v w : W) :
    box (dagger χ) v w ↔ χ.IsAPriori id :=
  Iff.rfl

end Operators

/-! ### Context sets and the three principles -/

section Principles

variable {W α : Type*} {cs : Set W}

/-- The first principle: a proposition asserted is true in some but not all of the worlds of the
context set. -/
def FirstPrinciple (cs p : Set W) : Prop := (cs ∩ p).Nonempty ∧ ¬ cs ⊆ p

/-- The second principle: an assertive utterance expresses, relative to each world of the context
set, a proposition with a truth value at each world of the context set. -/
def SecondPrinciple (cs : Set W) (χ : Character W W SignType) : Prop :=
  ∀ v ∈ cs, cs ⊆ Function.support (χ v)

/-- The third principle: the proposition expressed at any world of the context set coincides
within the context set with the proposition expressed at any other. -/
def ThirdPrinciple (cs : Set W) (χ : Character W W α) : Prop :=
  ∀ v ∈ cs, ∀ v' ∈ cs, Set.EqOn (χ v) (χ v') cs

/-- The second principle turns semantic presupposition into speaker presupposition: if the
sentence has a truth value only where `φ` is true, then `φ` is true throughout the context set
(p. 326). -/
theorem subset_of_secondPrinciple {χ : Character W W SignType} {φ : Set W}
    (h : SecondPrinciple cs χ) (hφ : ∀ v, Function.support (χ v) ⊆ φ) : cs ⊆ φ :=
  fun w hw ↦ hφ w (h w hw hw)

/-- The third principle holds exactly when the essential effect of the assertion, eliminating the
worlds incompatible with what is said, does not depend on which world of the context set is
actual (p. 327). -/
theorem thirdPrinciple_iff {χ : Character W W Prop} :
    ThirdPrinciple cs χ ↔
      ∀ v ∈ cs, ∀ v' ∈ cs, CCP.up {w | χ v w} cs = CCP.up {w | χ v' w} cs := by
  simp [ThirdPrinciple, Set.EqOn, CCP.up, Set.ext_iff, and_congr_right_iff]

-- pp. 327–328: under the third principle, what is said reduces the context set as the diagonal does
theorem up_eq_up_diag {χ : Character W W Prop} (h : ThirdPrinciple cs χ) {v : W} (hv : v ∈ cs) :
    CCP.up {w | χ v w} cs = CCP.up {w | χ.diag id w} cs := by
  ext w
  simp only [CCP.up, Set.mem_inter_iff, Set.mem_ofPred_eq, Character.diag_apply, id_eq]
  exact and_congr_right fun hw ↦ Iff.of_eq (h v hv w hw hw)

-- p. 328: the dagger brings every utterance into conformity with the third principle
theorem thirdPrinciple_dagger (cs : Set W) (χ : Character W W α) : ThirdPrinciple cs (dagger χ) :=
  fun _ _ _ _ _ _ ↦ rfl

/-- Diagonalization is forced: an eliminative and distributive update of context sets that has
the essential effect of what is said wherever the actual world is known is intersection with the
diagonal proposition. -/
theorem eq_up_diag {u : CCP W} {χ : Character W W Prop} (hu : u.IsClassical)
    (h : ∀ w, u {w} = CCP.up {w' | χ w w'} {w}) : u = CCP.up {w | χ.diag id w} := by
  rw [← CCP.isClassical_iff_up_down_eq.1 hu]
  congr 1
  ext w
  simp [CCP.down, h, CCP.up, Set.singleton_inter_nonempty]

end Principles

/-! ### The examples -/

/-- The three worlds of each example. -/
inductive World where
  | i
  | j
  | k
  deriving DecidableEq, Fintype

section Fool

/-- O'Leary, to whom I said *You are a fool*, and Daniels, who was standing nearby. -/
inductive Person where
  | oLeary
  | daniels
  deriving DecidableEq

/-- Who is a fool: O'Leary in `i`, the world as it is, and in `k`, the world Daniels thinks we
are in; Daniels in `j`, the world O'Leary thinks we are in. -/
def IsFool (w : World) (x : Person) : Prop := x = if w = .j then .daniels else .oLeary

/-- The addressee: O'Leary in `i` and `j`, and Daniels, who thinks I am talking to him, in `k`. -/
def addressee (v : World) : Person := if v = .k then .daniels else .oLeary

/-- The propositional concept of my *You are a fool*, *you* referring rigidly to the addressee. -/
def youAreAFool : Character World World Prop :=
  fun v w ↦ IsFool w ((dthat addressee : Character World World Person) v w)

instance : DecidableRel youAreAFool := fun _ _ ↦ by unfold youAreAFool IsFool; infer_instance

-- p. 318: matrix B. O'Leary and I agree about what was said, Daniels and I about the truth values
theorem youAreAFool_matrix :
    (∀ w, youAreAFool .i w ↔ youAreAFool .j w) ∧ (∀ v, youAreAFool v .i ↔ youAreAFool v .k) ∧
      ∀ w, youAreAFool.diag id w ↔ w = .i := by
  simp only [Character.diag_apply, id_eq]
  decide

end Fool

section Meter

/-- The length in meters of the metal bar: one, two and three in `i`, `j` and `k`. -/
def barLength : World → ℕ
  | .i => 1
  | .j => 2
  | .k => 3

/-- The propositional concept of an authority's *This bar is one meter long*, which fixes the
reference of *one meter* as the length the bar has in the context. -/
def oneMeterLong : Character World World Prop :=
  fun v w ↦ barLength w = (dthat barLength : Character World World ℕ) v w

instance : DecidableRel oneMeterLong := fun _ _ ↦ by unfold oneMeterLong; infer_instance

-- p. 321: matrix C is the identity
theorem oneMeterLong_iff : ∀ v w, oneMeterLong v w ↔ v = w := by decide

-- p. 321: the proposition expressed might have been false, but the utterance could not express a
-- false one
theorem oneMeterLong_isAPriori : oneMeterLong.IsAPriori id ∧ ¬ oneMeterLong.IsNecessary :=
  ⟨fun _ ↦ rfl, fun h ↦ absurd (h .i .j) (by decide)⟩

end Meter

section Anscombe

/-- Zsa Zsa Gabor, Elizabeth Anscombe, and Tricia Nixon Cox. -/
inductive Woman where
  | gabor
  | anscombe
  | cox
  deriving DecidableEq

/-- The woman talking in the next room: Miss Gabor in `i`, Professor Anscombe in `j`, and
Tricia Nixon Cox in `k`. -/
def inNextRoom : World → Woman
  | .i => .gabor
  | .j => .anscombe
  | .k => .cox

/-- *That is either Zsa Zsa Gabor or Elizabeth Anscombe*, with a demonstrative and two proper
names. -/
def gaborOrAnscombe : Character World World Prop := fun v w ↦
  (dthat inNextRoom : Character World World Woman) v w = const .gabor v w ∨
    (dthat inNextRoom : Character World World Woman) v w = const .anscombe v w

instance : DecidableRel gaborOrAnscombe := fun _ _ ↦ by unfold gaborOrAnscombe; infer_instance

-- p. 328: with rigid designators, *that is either `a` or `b`* expresses a necessary truth or a
-- necessary falsehood at each context
theorem isRigid_eq_or_eq {C W E : Type*} {t a b : Character C W E}
    (ht : t.IsDirectlyReferential) (ha : a.IsDirectlyReferential)
    (hb : b.IsDirectlyReferential) (c : C) : IsRigid fun w ↦ t c w = a c w ∨ t c w = b c w :=
  fun w₁ w₂ ↦ by simp only [ht c w₁ w₂, ha c w₁ w₂, hb c w₁ w₂]

theorem not_firstPrinciple_of_isRigid {W : Type*} {p : W → Prop} (hp : IsRigid p) (cs : Set W) :
    ¬ FirstPrinciple cs {w | p w} :=
  fun ⟨⟨w, _, hw⟩, hn⟩ ↦ hn fun w' _ ↦ cast (hp w w') hw

/-- With rigid designators, what *That is either Zsa Zsa Gabor or Elizabeth Anscombe* expresses
at any world violates the first principle in every context set, and its concept violates the
third principle in the context set of all three worlds. What the speaker means to communicate is
the diagonal proposition, that the woman is one of the two, which the first principle allows
there (p. 328). -/
theorem gaborOrAnscombe_diag :
    (∀ v cs, ¬ FirstPrinciple cs {w | gaborOrAnscombe v w}) ∧
      ¬ ThirdPrinciple Set.univ gaborOrAnscombe ∧
      (∀ w, gaborOrAnscombe.diag id w ↔ w ≠ .k) ∧
      FirstPrinciple Set.univ {w | gaborOrAnscombe.diag id w} := by
  refine ⟨fun v ↦ not_firstPrinciple_of_isRigid (isRigid_eq_or_eq
    (dthat_isDirectlyReferential _) (const_isDirectlyReferential _)
    (const_isDirectlyReferential _) v), fun h ↦ ?_, ?_, ?_⟩
  · exact absurd (cast (h .i (Set.mem_univ _) .k (Set.mem_univ _) (Set.mem_univ .i))
      (show gaborOrAnscombe .i .i by decide)) (by decide)
  · simp only [Character.diag_apply, id_eq]
    decide
  · exact ⟨⟨.i, Set.mem_univ _, show gaborOrAnscombe .i .i by decide⟩,
      fun h ↦ absurd (h (Set.mem_univ .k)) (show ¬ gaborOrAnscombe .k .k by decide)⟩

-- p. 328: what is said at `i` is a necessary truth, yet the sentence is not a priori
theorem gaborOrAnscombe_isNecessaryAt :
    gaborOrAnscombe.IsNecessaryAt .i ∧ ¬ gaborOrAnscombe.IsAPriori id :=
  ⟨fun w ↦ by cases w <;> decide, fun h ↦ (gaborOrAnscombe_diag.2.2.1 .k).1 (h .k) rfl⟩

end Anscombe

section Holmes

/-- Arthur Conan Doyle, and the famous detective named Sherlock Holmes of world `j`. -/
inductive Individual where
  | doyle
  | holmes
  deriving DecidableEq, Fintype

/-- Whom *Sherlock Holmes* refers to as used in each world: no one in `i`, the actual world; the
detective in `j`; and in `k`, Conan Doyle, a famous detective who wrote of his own cases under
the pseudonym *Sir Arthur Conan Doyle*. -/
def holmesRef : World → Option Individual
  | .i => none
  | .j => some .holmes
  | .k => some .doyle

/-- Conan Doyle exists in every world, and the detective of `j` only in `j`. -/
def ExistsIn (w : World) (x : Individual) : Prop := x = .doyle ∨ w = .j

/-- *Sherlock Holmes does not exist* on the straightforward semantic account: it is true at the
worlds whose domain does not contain the individual the name refers to. -/
def holmesDoesNotExist : Character World World Prop :=
  fun v w ↦ ∀ x, holmesRef v = some x → ¬ ExistsIn w x

instance : DecidableRel holmesDoesNotExist :=
  fun _ _ ↦ by unfold holmesDoesNotExist ExistsIn; infer_instance

/-- With no referent, *Sherlock Holmes does not exist* expresses the necessary proposition, the
first row of matrix G. The concept violates the third principle in the context set of a speaker
who does not know which of the three worlds is actual, and diagonalization makes the sentence
true at the actual world alone (pp. 330–331). -/
theorem holmesDoesNotExist_diag :
    (∀ w, holmesDoesNotExist .i w) ∧ ¬ ThirdPrinciple Set.univ holmesDoesNotExist ∧
      ∀ w, holmesDoesNotExist.diag id w ↔ w = .i := by
  refine ⟨by decide, fun h ↦ ?_, ?_⟩
  · exact absurd (cast (h .i (Set.mem_univ _) .j (Set.mem_univ _) (Set.mem_univ .j))
      (show holmesDoesNotExist .i .j by decide)) (by decide)
  · simp only [Character.diag_apply, id_eq]
    decide

end Holmes

/-! ### Violations of the third principle -/

section Violations

/-- The concept `D`, whose rows differ within the context set of all three worlds. -/
def conceptD : Character World World Prop :=
  fun v w ↦ v = .i ∨ (v = .j ∧ w = .k) ∨ (v = .k ∧ w ≠ .i)

/-- The concept of note 13, whose rows at `i` and `j` differ only at `k`. -/
def conceptNote13 : Character World World Prop :=
  fun v w ↦ (v = .i ∧ w ≠ .j) ∨ (v = .j ∧ w = .i) ∨ (v = .k ∧ w ≠ .i)

instance : DecidableRel conceptD := fun _ _ ↦ by unfold conceptD; infer_instance

instance : DecidableRel conceptNote13 := fun _ _ ↦ by unfold conceptNote13; infer_instance

-- p. 327: with `D`, the essential effect depends on which world is actual: in `i` nothing is
-- eliminated, in `j` the worlds `i` and `j`, in `k` the world `i`
theorem up_conceptD :
    CCP.up {w | conceptD .i w} .univ = .univ ∧ CCP.up {w | conceptD .j w} .univ = {.k} ∧
      CCP.up {w | conceptD .k w} .univ = {.j, .k} := by
  refine ⟨?_, ?_, ?_⟩ <;> ext w <;> cases w <;> simp [CCP.up, conceptD]

-- note 13: the third principle holds in the context set `{i, j}`, though `i` and `j` express
-- different propositions
theorem thirdPrinciple_conceptNote13 :
    ThirdPrinciple {.i, .j} conceptNote13 ∧ conceptNote13 .i ≠ conceptNote13 .j := by
  refine ⟨?_, fun h ↦ absurd (cast (congrFun h .k) (show conceptNote13 .i .k by decide))
    (by decide)⟩
  simp only [ThirdPrinciple, Set.EqOn, Set.mem_insert_iff, Set.mem_singleton_iff, eq_iff_iff]
  decide

end Violations

/-! ### The judgments -/

-- pp. 317, 321, 330: what I said to O'Leary is true at the actual world, the authority's
-- statement is true in every context, and *Sherlock Holmes does not exist* is true at the
-- actual world
theorem judgments :
    (youAreAFool.diag id .i ↔ Examples.fool.feature? "truthValue" = some "true") ∧
      (oneMeterLong.IsAPriori id ↔ Examples.meter.feature? "truthValue" = some "true") ∧
      (holmesDoesNotExist.diag id .i ↔ Examples.holmes.feature? "truthValue" = some "true") :=
  ⟨iff_of_true (show youAreAFool .i .i by decide) (by decide),
    iff_of_true oneMeterLong_isAPriori.1 (by decide),
    iff_of_true (show holmesDoesNotExist .i .i by decide) (by decide)⟩

end Stalnaker1978
