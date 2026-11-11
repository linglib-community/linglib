module

public import Linglib.Data.Examples.Rooth1992
public import Linglib.Pragmatics.NeoGricean.Basic
public import Linglib.Semantics.Focus.Control
public import Linglib.Semantics.Focus.Marking
public import Linglib.Semantics.Focus.Particles
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.Composition.Constituency
public import Linglib.Semantics.Composition.Mode.Combine
public import Linglib.Semantics.Composition.Mode.Pointwise
public import Linglib.Semantics.Composition.Rules

/-!
# Rooth (1992): A theory of focus interpretation

Rooth unifies the effects of intonational focus. Alternative semantics gives a phrase a focus
semantic value beside its ordinary one, the set of substitution instances at the focused position,
computed here by mapping a predicate over an F-marked constituent whose alternatives are the whole
domain (`WithAlternatives.focused`). Association with *only*, contrasting phrases, scalar
implicature and question-answer congruence each require some object to be a subset or an element
of a focus semantic value, and the focus interpretation principle keeps only that requirement: the
operator ~ presupposes `Focus.SquiggleSet` or `Focus.SquiggleInd` of a free variable whose
antecedent is a `Focus.Antecedent`. In the logical form of an *only* sentence, with ~ adjoined to
the VP and its variable the domain of *only*, the two-dimensional grammar puts the words together
in one way, and the sentence is [defined where the domain satisfies the presupposition of ~ and
then says what *only* says](##Rooth1992.meanings_lf_object).

## Implementation notes

* Worlds of the relational models are sets of atomic facts, so that distinct facts denote
  distinct propositions; the quiz model assigns each person a grade, acing entailing passing,
  with groups as finite sets of people.
* The rows carry the paper's examples with the truth values of the introduction scenario and
  the question-answer judgments, which the theorems derive. A row's focus position marks the
  arguments of its predication, and its focus semantic value is their composition
  (`WithAlternatives.map₂`).
* The logical form (31) is interpreted by the effect-driven grammar that is pointwise at
  alternatives: every word carries an ordinary value with its alternatives, sisters combine by
  Structured App, and ~ is the one word whose type takes a meaning with alternatives as its
  argument. The presupposition of ~ is partiality of its value.
* *Only* is the substrate's exclusive assertion on the identity scale,
  `Focus.atMost (· = ·)`, which is (4b) with the equation reversed. Footnote 2 leaves
  open whether the prejacent belongs in the presupposition or the assertion, and suggests that
  the property may only need to be the strongest in the domain, the entailment scale.

## References

* [rooth-1992]
* [rooth-1985]
* [bumford-charlow-2026]
* [hamblin-1973b]
* [sauerland-2004]
-/

@[expose] public section

namespace Rooth1992

open Exhaustification Focus WithAlternatives

/-! ### Focus semantic values (2) -/

section Values

universe u

variable {α β : Type u}

theorem atMost_eq_empty_of_univ_mem {W : Type*} {C : Set (Set W)} {p : Set W}
    (hC : Set.univ ∈ C) (hp : p ≠ Set.univ) : atMost (· = ·) C id p = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun w hw ↦ hp (hw _ hC (Set.mem_univ w))

end Values

/-! ### Relational models

A world is a set of atomic facts and a fact denotes the proposition that it holds. -/

section Atoms

variable {A : Type}

/-- The proposition that the fact `a` holds. -/
def atom (a : A) : Set (Set A) := {w | a ∈ w}

@[simp] theorem mem_atom {a : A} {w : Set A} : w ∈ atom a ↔ a ∈ w := Iff.rfl

theorem atom_injective : Function.Injective (atom (A := A)) := fun a _ h ↦
  (Set.mem_singleton_iff.1 ((Set.ext_iff.1 h {a}).1 (Set.mem_singleton a))).symm

theorem atom_ne_univ (a : A) : atom a ≠ Set.univ := fun h ↦
  Set.notMem_empty a ((Set.ext_iff.1 h ∅).2 (Set.mem_univ ∅))

end Atoms

/-! ### Focusing adverbs (§2.1)

*Only* quantifies over a domain `C` of properties: if Mary has a property in `C`, it is the one
the VP expresses ((4b), (30b)). Focus constrains `C` to lie inside the focus semantic value of
the VP ((9c)). At the propositional level the assertion is the exclusive's assertion on the
identity scale, `Focus.atMost (· = ·)`, which is the entailment-scale exclusion where
the prejacent entails no other member of the domain
(`Focus.atMost_eq_eq_atMost_subset`). -/

section Only

variable {E : Type} (m b t s c : E)

/-- The fact that `x` introduced `y` to `z`. -/
def intro (x y z : E) : Set (Set (E × E × E)) := atom (x, y, z)

/-- In the introduction scenario Mary introduced Bill and Tom to Sue, and there were no other
introductions. -/
def scenario : Set (E × E × E) := {(m, b, s), (m, t, s)}

-- (5a)
theorem vp_objectFocus :
    ((fun y ↦ intro m y s) <$> focused b).alternatives = Set.range fun y ↦ intro m y s :=
  alternatives_map_focused _ _

/-- (3a) is false in the scenario, since 'Mary introduced Tom to Sue' is a true member of the
domain distinct from the prejacent. -/
theorem three_a (hbt : b ≠ t) :
    scenario m b t s ∉ atMost (· = ·) (Set.range fun y ↦ intro m y s) id (intro m b s) :=
  notMem_atMost (j := intro m t s) ⟨t, rfl⟩ (by simp [scenario, intro])
    fun h ↦ hbt (Prod.mk.inj (Prod.mk.inj (atom_injective h)).2).1

/-- (3b) is true in the scenario, since the only true proposition of the form 'Mary introduced
Bill to z' is the prejacent. -/
theorem three_b (hbt : b ≠ t) :
    scenario m b t s ∈ atMost (· = ·) (Set.range fun z ↦ intro m b z) id (intro m b s) := by
  rintro q ⟨z, rfl⟩ hw
  simp only [id, scenario, intro, mem_atom, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq] at hw
  rcases hw with ⟨-, -, rfl⟩ | ⟨-, hb, -⟩
  · rfl
  · exact absurd hb hbt

/-- The relations a focused transitive verb ranges over. -/
inductive Verb where
  | read
  | understand
  deriving DecidableEq

/-- The fact that `x` stands in relation `v` to `y`. -/
def rel (v : Verb) (x y : E) : Set (Set (Verb × E × E)) := atom (v, x, y)

-- (8)
theorem univ_mem_vp_verbFocus :
    Set.univ ∈ ((fun R : E → E → Set (Set (Verb × E × E)) ↦ R m c) <$>
      focused (rel .read)).alternatives := by
  rw [alternatives_map_focused]; exact ⟨fun _ _ ↦ Set.univ, rfl⟩

/-- (7) with the domain fixed to the full focus semantic value, as in [rooth-1985], is
unsatisfiable. -/
theorem recognitions_fixed :
    atMost (· = ·) ((fun R : E → E → Set (Set (Verb × E × E)) ↦ R m c) <$>
      focused (rel .read)).alternatives id (rel .read m c) = ∅ :=
  atMost_eq_empty_of_univ_mem (univ_mem_vp_verbFocus m c) (atom_ne_univ _)

/-- With the domain constrained to reading and understanding (37c), (7) is true where Mary read
without understanding. -/
theorem recognitions_constrained :
    {(Verb.read, m, c)} ∈
      atMost (· = ·) {rel .read m c, rel .understand m c} id (rel .read m c) := by
  rintro q (rfl | rfl) hw
  · rfl
  · simp [rel] at hw

end Only

/-! ### Contrasting phrases (§2.2)

(14): construe `α` as contrasting with `β` if the ordinary value of `β` is a member of the focus
semantic value of `α`; the paper derives it from the individual case of the focus
interpretation principle, where the ordinary value of any phrase can be the antecedent. -/

section Contrast

variable {E W : Type} (farmer american canadian : E → Set W)

/-- The intersective N' *P farmer*. -/
def nbar (P : E → Set W) : E → Set W := fun x ↦ P x ∩ farmer x

-- (15), (41b)
theorem farmer_contrast (h : nbar farmer canadian ≠ nbar farmer american) :
    (Antecedent.phrase (nbar farmer canadian)).Resolves (nbar farmer american)
      (nbar farmer <$> focused american).alternatives := by
  rw [alternatives_map_focused]; exact ⟨⟨canadian, rfl⟩, h⟩

end Contrast

/-! ### Scalar implicature (§2.3)

Asserting a member of a scale implicates the negation of the members that entail it. The
constraint on scales (22) requires the underlying set to lie inside the focus semantic value of
the assertion, so the two placements of focus in (16) and (17) license different scales. -/

section Scale

variable {E : Type} (m : E)

/-- In the quiz world everyone has a grade, failed, passed or aced. -/
abbrev Grades (E : Type) := E → Fin 3

/-- The group `g` passed. -/
def pass (g : Finset E) : Set (Grades E) := {w | ∀ x ∈ g, 1 ≤ w x}

/-- `x` aced. -/
def ace (x : E) : Set (Grades E) := {w | 2 ≤ w x}

-- (18)
theorem ace_ssubset_pass : ace m ⊂ pass {m} := by
  refine ⟨fun w h ↦ ?_, fun h ↦ ?_⟩
  · intro x hx
    rw [Finset.mem_singleton] at hx
    exact hx ▸ le_trans (by decide) h
  · have := h (show (fun _ ↦ (1 : Fin 3)) ∈ pass {m} by simp [pass])
    exact absurd this (by simp [ace])

theorem pass_union [DecidableEq E] (g g' : Finset E) : pass (g ∪ g') = pass g ∩ pass g' := by
  ext w; simp [pass, or_imp, forall_and]

/-- The focus semantic value of *I [passed]F* contains the scale of acing and passing, so asserting
passing implicates not acing (16). -/
theorem verbFocus_scale :
    {ace m, pass {m}} ⊆ ((fun V : Finset E → Set (Grades E) ↦ V {m}) <$>
      focused pass).alternatives ∧
    NeoGricean.IsSecondaryImplicature {ace m} (pass {m}) (ace m) := by
  refine ⟨?_, NeoGricean.isSecondaryImplicature_singleton.2 (ace_ssubset_pass m)⟩
  rw [alternatives_map_focused]
  rintro q (rfl | rfl)
  · exact ⟨fun _ ↦ ace m, rfl⟩
  · exact ⟨pass, rfl⟩

-- (21)
theorem subjectFocus_scale :
    Set.range pass ⊆ ((pass (E := E)) <$> focused {m}).alternatives := by
  rw [alternatives_map_focused]

/-- The focus semantic value of *[I]F passed* does not contain acing, so (17) suggests nothing about
acing. -/
theorem ace_notMem_subjectFocus : ace m ∉ ((pass (E := E)) <$> focused {m}).alternatives := by
  rw [alternatives_map_focused]
  rintro ⟨g, hg⟩
  have := (Set.ext_iff.1 hg (fun _ ↦ 1)).1 (fun _ _ ↦ le_rfl)
  simp [ace] at this

/-- In the roommate implicature, asserting that Mats passed implicates the negation of the group
proposition that Mats and Paul passed, which with Mats passing is Paul not passing. -/
theorem roommate_implicature [DecidableEq E] (p : E) (w : Grades E) (hm : w ∈ pass {m})
    (hmp : w ∉ pass {m, p}) : w ∉ pass {p} := fun hp ↦
  hmp (by rw [show ({m, p} : Finset E) = {m} ∪ {p} from rfl, pass_union]; exact ⟨hm, hp⟩)

end Scale

/-! ### Questions and answers (§2.4)

The ordinary semantic value of a question is its set of potential answers ([hamblin-1973b]),
which the question-answer constraint (26d) requires to lie inside the focus semantic value of
the answer. -/

section Questions

variable {E : Type} (P : Set E) (m b : E)

/-- The fact that `x` cut `y` down to size. -/
def cut (x y : E) : Set (Set (E × E)) := atom (x, y)

/-- The question *Who cut Bill down to size?* (25a) over the persons `P`. -/
def whoCut (b : E) : Set (Set (Set (E × E))) := (fun x ↦ cut x b) '' P

theorem subjectFocus_value :
    ((fun x ↦ cut x b) <$> focused m).alternatives = Set.range fun x ↦ cut x b :=
  alternatives_map_focused _ _

/-- (23Aa) answers (23Qa), since the question fully resolves the focus on the subject, with any
other person supplying the contrasting alternative. -/
theorem question_resolves_subjectFocus {x : E} (hm : m ∈ P) (hx : x ∈ P) (hxm : x ≠ m) :
    (Antecedent.question (whoCut P b)).Resolves (cut m b) (Set.range fun x ↦ cut x b) :=
  ⟨Set.image_subset_range _ _, ⟨m, hm, rfl⟩,
    cut x b, ⟨x, hx, rfl⟩, fun h ↦ hxm (Prod.mk.inj (atom_injective h)).1⟩

/-- (23Ab) does not answer (23Qa), since another person's cutting Bill down to size is not of the
form 'Mary cut y down to size'. -/
theorem question_rejects_objectFocus {x : E} (hx : x ∈ P) (hxm : x ≠ m) :
    ¬ (Antecedent.question (whoCut P b)).Admits (Set.range fun y ↦ cut m y) := fun h ↦
  let ⟨_, hy⟩ := h ⟨x, hx, rfl⟩
  hxm (Prod.mk.inj (atom_injective hy)).1.symm

end Questions

/-! ### Bare remnant ellipsis (§7–§8)

*She beats [me]F more often than Sue* has two logical forms, with the object or the subject as
the correlate of the remnant; focus does not enter the grammar of ellipsis but filters the two,
since the ~ operator at the main clause needs the *than*-clause as an antecedent of the right
form (64)–(66). -/

section Ellipsis

variable {E : Type} (she me sue : E)

/-- The fact that `x` beats `y`. -/
def beats (x y : E) : Set (Set (E × E)) := atom (x, y)

/-- Which phrase of the main clause the remnant *Sue* corresponds to. -/
inductive Correlate where
  | object
  | subject
  deriving DecidableEq, Repr

/-- The *than*-clause under each correlate is 'she beats Sue' or 'Sue beats me'. -/
def thanClause : Correlate → Set (Set (E × E))
  | .object => beats she sue
  | .subject => beats sue me

/-- Where the focus falls in the main clause. -/
inductive FocusSite where
  | onObject
  | onSubject
  deriving DecidableEq, Repr

/-- The marks a placement of focus puts on the subject and the object. -/
def FocusSite.marks : FocusSite → Mark × Mark
  | .onObject => (.unfeatured, .focused)
  | .onSubject => (.focused, .unfeatured)

/-- The focus semantic value of the main clause under a placement of focus. -/
def mainClause (f : FocusSite) : Set (Set (Set (E × E))) :=
  (map₂ beats ((unfeatured she).mark f.marks.1) ((unfeatured me).mark f.marks.2)).alternatives

/-- The *than*-clause antecedes the main-clause focus iff the correlate is the focused phrase (66).
-/
theorem ellipsis_filter (hsm : sue ≠ me) (hss : sue ≠ she) (r : Correlate) (f : FocusSite) :
    (Antecedent.phrase (thanClause she me sue r)).Resolves (beats she me)
        (mainClause she me f) ↔
      (r = .object ↔ f = .onObject) := by
  cases r <;> cases f <;>
    simp only [Antecedent.Resolves, thanClause, mainClause, FocusSite.marks,
      alternatives_map₂_focused_unfeatured, alternatives_map₂_unfeatured_focused]
  · exact iff_of_true ⟨⟨sue, rfl⟩, fun h ↦ hsm (Prod.mk.inj (atom_injective h)).2⟩ (by decide)
  · exact iff_of_false (fun ⟨⟨_, hx⟩, _⟩ ↦ hsm (Prod.mk.inj (atom_injective hx)).2.symm)
      (by decide)
  · exact iff_of_false (fun ⟨⟨_, hy⟩, _⟩ ↦ hss (Prod.mk.inj (atom_injective hy)).1.symm)
      (by decide)
  · exact iff_of_true ⟨⟨sue, rfl⟩, fun h ↦ hss (Prod.mk.inj (atom_injective h)).1⟩ (by decide)

end Ellipsis

/-! ### The rows -/

/-- The individuals of the paper's scenarios. -/
inductive Person where
  | mary
  | bill
  | tom
  | sue
  | monique
  | bjorn
  deriving DecidableEq, Repr

/-- The focus positions of the *only* rows. -/
inductive OnlyFocus where
  | bill
  | sue
  deriving DecidableEq, Repr

/-- The marks a focus position puts on the object and the goal of *Mary introduced Bill to
Sue*. -/
def OnlyFocus.marks : OnlyFocus → Mark × Mark
  | .bill => (.focused, .unfeatured)
  | .sue => (.unfeatured, .focused)

/-- The domain of *only* a focus position constrains, over the introduction scenario, is the
focus semantic value of the VP. -/
def OnlyFocus.domain (f : OnlyFocus) : Set (Set (Set (Person × Person × Person))) :=
  (map₂ (intro Person.mary) ((unfeatured Person.bill).mark f.marks.1)
    ((unfeatured Person.sue).mark f.marks.2)).alternatives

/-- The focus position and the truth value an *only* row reports. -/
def onlyRow (r : Datum) : Option (OnlyFocus × Bool) := do
  let f ← r.parse? "focus" [("Bill", OnlyFocus.bill), ("Sue", .sue)]
  let v ← r.verdict
  pure (f, v)

/-- The *only* rows have (3a) false and (3b) true. -/
def onlyData : List (OnlyFocus × Bool) := Examples.all.filterMap onlyRow

/-- A row of (3a) and (3b) is true in the introduction scenario iff *only* over the domain its
focus constrains holds there. -/
theorem only_rows : ∀ d ∈ onlyData, (d.2 = true ↔
    scenario Person.mary .bill .tom .sue ∈
      atMost (· = ·) d.1.domain id (intro Person.mary .bill .sue)) := by
  intro d hd
  rw [show onlyData = [(.bill, false), (.sue, true)] by decide] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl <;>
    simp only [OnlyFocus.domain, OnlyFocus.marks, alternatives_map₂_focused_unfeatured,
      alternatives_map₂_unfeatured_focused]
  · exact ⟨fun h ↦ absurd h Bool.false_ne_true, fun h ↦ absurd h (three_a _ _ _ _ (by decide))⟩
  · exact ⟨fun _ ↦ three_b _ _ _ _ (by decide), fun _ ↦ trivial⟩

/-- The questions of (23). -/
inductive Q where
  | whoCutBill
  | whoDidMaryCut
  deriving DecidableEq, Repr

/-- The denotation of a question, over all persons. -/
def Q.den : Q → Set (Set (Set (Person × Person)))
  | .whoCutBill => whoCut Set.univ .bill
  | .whoDidMaryCut => (fun y ↦ cut Person.mary y) '' Set.univ

/-- The focus positions of the answers of (23). -/
inductive AnswerFocus where
  | mary
  | bill
  deriving DecidableEq, Repr

/-- The marks a focus position puts on the subject and the object of *Mary cut Bill down to
size*. -/
def AnswerFocus.marks : AnswerFocus → Mark × Mark
  | .mary => (.focused, .unfeatured)
  | .bill => (.unfeatured, .focused)

/-- The focus semantic value of an answer. -/
def AnswerFocus.value (f : AnswerFocus) : Set (Set (Set (Person × Person))) :=
  (map₂ cut ((unfeatured Person.mary).mark f.marks.1)
    ((unfeatured Person.bill).mark f.marks.2)).alternatives

/-- The question, the answer's focus position, and the judgment of a question-answer row. -/
def qaRow (r : Datum) : Option (Q × AnswerFocus × Bool) := do
  let q ← r.parse? "question" [("whoCutBill", Q.whoCutBill), ("whoDidMaryCut", .whoDidMaryCut)]
  let f ← r.parse? "focus" [("Mary", AnswerFocus.mary), ("Bill", .bill)]
  pure (q, f, decide (r.judgment = .acceptable))

/-- The question-answer rows of (23). -/
def qaData : List (Q × AnswerFocus × Bool) := Examples.all.filterMap qaRow

/-- An answer is appropriate iff the question denotation lies inside its focus semantic value
(23). -/
theorem qa_rows : ∀ d ∈ qaData,
    (d.2.2 = true ↔ (Antecedent.question d.1.den).Admits d.2.1.value) := by
  intro d hd
  rw [show qaData = [(.whoCutBill, .mary, true), (.whoCutBill, .bill, false),
    (.whoDidMaryCut, .bill, true), (.whoDidMaryCut, .mary, false)] by decide] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp only [AnswerFocus.value, AnswerFocus.marks, alternatives_map₂_focused_unfeatured,
      alternatives_map₂_unfeatured_focused]
  · exact ⟨fun _ ↦ Set.image_subset_range _ _, fun _ ↦ trivial⟩
  · exact ⟨fun h ↦ absurd h Bool.false_ne_true,
      fun h ↦ absurd h (question_rejects_objectFocus _ _ _ (Set.mem_univ Person.monique)
        (by decide))⟩
  · exact ⟨fun _ ↦ Set.image_subset_range _ _, fun _ ↦ trivial⟩
  · refine ⟨fun h ↦ absurd h Bool.false_ne_true, fun h ↦ ?_⟩
    obtain ⟨_, hy⟩ := h ⟨Person.bjorn, Set.mem_univ _, rfl⟩
    exact absurd (Prod.mk.inj (atom_injective hy)).2 (by decide)

/-! ### The logical form of association with *only* (§3–§4)

(31): `[S Mary [VP only(C) [VP [VP introduced Bill to Sue] ~ C]]]`, with F on *Bill* or on *Sue*.
Every word has an ordinary value and its alternatives, and ~ closes them off: its value has the
VP's ordinary value alone, and is defined where the presupposition (40) holds of `C`. -/

section LogicalForm

open Interpreter PhraseStructure PhraseStructure.Tree

/-- The base sorts: individuals and propositions. -/
inductive Sort' where
  | e
  | p
  deriving DecidableEq

/-- The domains of the base sorts: individuals, and sets of the worlds of the relational model. -/
abbrev Sort'.Dom (E : Type) : Sort' → Type
  | .e => E
  | .p => Set (Set (E × E × E))

local notation "e" => (Ty.base Sort'.e : Ty Sort')
local notation "p" => (Ty.base Sort'.p : Ty Sort')
local notation "F" => Ty.comp Eff.F
local notation "M" => Ty.comp Eff.M

variable {E : Type}

/-- The words of (31) by type. A name and an F-marked name each carry alternatives; *only* and ~
come with the value of their variable `C`. -/
inductive Item (E : Type) : Ty Sort' → Type
  | name (x : E) : Item E (F e)
  | focus (x : E) : Item E (F e)
  | introduced : Item E (F (e ⇒ e ⇒ e ⇒ p))
  | only (C : Set (E → Set (Set (E × E × E)))) : Item E (F ((e ⇒ p) ⇒ e ⇒ p))
  | squiggle (C : Set (E → Set (Set (E × E × E)))) : Item E (F (e ⇒ p) ⇒ F (M (e ⇒ p)))

/-- A leaf is a typed word. -/
def items : (Σ a, Item E a) ⊕ ℕ → List (Σ a, Item E a)
  | .inl w => [w]
  | .inr _ => []

/-- The lexicon. An unfocused word evokes its own value and an F-marked one every value of its
type (2); *only* is (30b); and ~ presupposes (40) of `C` and returns the ordinary value of its
phrase with no alternatives (42). -/
def Item.val : {a : Ty Sort'} → Item E a → a.Dom (Sort'.Dom E)
  | _, .name x => .unfeatured x
  | _, .focus x => .focused x
  | _, .introduced => .unfeatured fun y z x ↦ intro x y z
  | _, .only C => .unfeatured fun VP x ↦ {w | ∀ P ∈ C, w ∈ P x → P = VP}
  | _, .squiggle C => fun φ ↦
    .unfeatured ⟨SquiggleSet φ.ordinary φ.alternatives C, fun _ ↦ φ.ordinary⟩

/-- The grammar: functional application, pointwise at alternatives. -/
def grammar : Interpreter (effectGrammar (application (B := Sort'))) ℕ :=
  effectDrivenWithin (MetaMode.pointwise (· = .F)) application

/-- (31), with the object and the goal as given. -/
def lf (C : Set (E → Set (Set (E × E × E)))) (m : E) (obj goal : Item E (F e)) :
    Tree Unit (Σ a, Item E a) :=
  .bin (.leaf ⟨_, .name m⟩)
    (.bin (.leaf ⟨_, .only C⟩)
      (.bin (.bin (.bin (.leaf ⟨_, .introduced⟩) (.leaf ⟨_, obj⟩)) (.leaf ⟨_, goal⟩))
        (.leaf ⟨_, .squiggle C⟩)))

/-- The meanings of a tree. -/
def meanings (t : Tree Unit (Σ a, Item E a)) : List (Σ a : Ty Sort', a.Dom (Sort'.Dom E)) :=
  t.values grammar effectGrammar.structure Item.val items

private theorem binary_fa₃ : grammar.binary (F (e ⇒ e ⇒ e ⇒ p)) (F e) =
    [⟨F (e ⇒ e ⇒ p), .ap trivial (.basic .fa)⟩] := rfl

private theorem binary_fa₂ : grammar.binary (F (e ⇒ e ⇒ p)) (F e) =
    [⟨F (e ⇒ p), .ap trivial (.basic .fa)⟩] := rfl

private theorem binary_squiggle : grammar.binary (F (e ⇒ p)) (F (e ⇒ p) ⇒ F (M (e ⇒ p))) =
    [⟨F (M (e ⇒ p)), .basic .ba⟩] := rfl

private theorem binary_only : grammar.binary (F ((e ⇒ p) ⇒ e ⇒ p)) (F (M (e ⇒ p))) =
    [⟨F (M (e ⇒ p)), .ap trivial (.mapR (.basic .fa))⟩] := rfl

private theorem binary_subject : grammar.binary (F e) (F (M (e ⇒ p))) =
    [⟨F (M p), .ap trivial (.mapR (.basic .ba))⟩] := rfl

variable (C : Set (E → Set (Set (E × E × E)))) (m b s : E)

/-- (31) with F on the object has one meaning. It is defined where `C` is a set of properties of
the form 'introducing y to Sue' that contains 'introducing Bill to Sue' and another, and it is
then the proposition that any property in `C` that Mary has is that one: (6), with (5a)
constraining `C`. -/
theorem meanings_lf_object : ∀ d ∈ meanings (lf C m (.focus b) (.name s)),
    ∃ v : WithAlternatives (Part (Set (Set (E × E × E)))), d = ⟨F (M p), v⟩ ∧
      (v.ordinary.Dom ↔
        SquiggleSet (fun x ↦ intro x b s) (Set.range fun y x ↦ intro x y s) C) ∧
      ∀ h, v.ordinary.get h = {w | ∀ P ∈ C, w ∈ P m → P = fun x ↦ intro x b s} := by
  simp only [meanings, lf, Tree.values_phrase_binary, Tree.values_terminal, items,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    binary_fa₃, binary_fa₂, binary_squiggle, binary_only, binary_subject, List.mem_singleton]
  rintro _ rfl
  refine ⟨_, rfl, Iff.of_eq (congrArg (SquiggleSet _ · C) (Set.ext fun P ↦ ?_)), fun _ ↦ rfl⟩
  show P ∈ WithAlternatives.alternatives
    (_ <$> (_ <$> WithAlternatives.unfeatured _ <*> WithAlternatives.focused b) <*>
      WithAlternatives.unfeatured s) ↔ _
  simp only [mem_alternatives_seq, mem_alternatives_map, unfeatured_alternatives,
    focused_alternatives, Set.mem_singleton_iff, Set.mem_univ, true_and, exists_eq_left,
    Set.mem_range]
  constructor
  · rintro ⟨_, ⟨_, ⟨_, rfl, y, rfl⟩, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, ⟨_, ⟨_, rfl, y, rfl⟩, rfl⟩, rfl⟩

/-- (31) with F on the goal: the same tree and the same assertion, with `C` constrained to
properties of the form 'introducing Bill to z', (5b). -/
theorem meanings_lf_goal : ∀ d ∈ meanings (lf C m (.name b) (.focus s)),
    ∃ v : WithAlternatives (Part (Set (Set (E × E × E)))), d = ⟨F (M p), v⟩ ∧
      (v.ordinary.Dom ↔
        SquiggleSet (fun x ↦ intro x b s) (Set.range fun z x ↦ intro x b z) C) ∧
      ∀ h, v.ordinary.get h = {w | ∀ P ∈ C, w ∈ P m → P = fun x ↦ intro x b s} := by
  simp only [meanings, lf, Tree.values_phrase_binary, Tree.values_terminal, items,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    binary_fa₃, binary_fa₂, binary_squiggle, binary_only, binary_subject, List.mem_singleton]
  rintro _ rfl
  refine ⟨_, rfl, Iff.of_eq (congrArg (SquiggleSet _ · C) (Set.ext fun P ↦ ?_)), fun _ ↦ rfl⟩
  show P ∈ WithAlternatives.alternatives
    (_ <$> (_ <$> WithAlternatives.unfeatured _ <*> WithAlternatives.unfeatured b) <*>
      WithAlternatives.focused s) ↔ _
  simp only [mem_alternatives_seq, mem_alternatives_map, unfeatured_alternatives,
    focused_alternatives, Set.mem_singleton_iff, Set.mem_univ, true_and, exists_eq_left,
    Set.mem_range]
  constructor
  · rintro ⟨_, ⟨_, ⟨_, rfl, rfl⟩, rfl⟩, z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨_, ⟨_, rfl, rfl⟩, rfl⟩, z, rfl⟩

end LogicalForm

end Rooth1992
