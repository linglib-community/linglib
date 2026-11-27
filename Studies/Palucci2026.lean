module

public import Mathlib.Basic.Rel
public import Mathlib.Data.Set.Subsingleton
public import Linglib.Semantics.Reference.Iota
public import Linglib.Syntax.Tree.Cat
public import Linglib.Syntax.Tree.QuantifierRaising
public import Linglib.Data.Examples.Palucci2026

/-!
# Palucci (2026): Pseudo-scoping out of relative clauses

*The supervisor that each volunteer reported to* has a reading on which the supervisor varies
with the volunteer, which [barker-2022b] derives by scoping the universal out of the relative
clause. Following [sharvit-1999], Palucci derives it with the universal in place: the description
denotes the function from volunteers to supervisors, and a covert universal binds its argument.
The article over functions presupposes that [each volunteer has exactly one
supervisor](##Palucci2026.functional_dom), and the closed function [has the meaning of the
scoped-out universal](##Palucci2026.closure_eq_raised). With the universal inside the complement
of *claim*, one step of raising [fits the judgments neither with that complement an island nor
without islands](##Palucci2026.not_fits_finiteComplement).

## Implementation notes

* The function's domain is the restrictor of the embedded universal, a subtype, and the relation
  it selects from holds between a member of the restrictor and an individual: for the opening
  example, between a volunteer and a supervisor of theirs that they reported to. The article over
  functions is `iota` at the type of functions.
* The paper composes the description from a predicate of partial functions (`candidates`), whose
  domains may be larger than the restrictor, and a silent operator `Min`. `Min` is formalized as
  the least element, as its definition is printed; the least candidate is the function on the
  restrictor (`isLeast_candidates_iff`).
* A sentence meaning is a partial truth value, undefined where the presupposition fails.
* *Varied* holds of a function with two values. An entry for a plurality, which the paper
  considers, is not formalized.
* A tree's words are strings. The finite complement of *claim* has the category `S` and is an
  island for a constituent containing *each*; the relative clause is a projection of *that*, so
  that it is not one. The universal can take wide scope by raising when one step takes it to the
  edge of the sentence.

## TODO

* The logical forms are not derived by the composition engine: the meanings of the description,
  of the saturated function and of the two closures are given as the paper's formulas.
* The trees have no gap, so the paper's condition that the universal bind into the trace of
  relativization, which excludes the varying reading where the gap is outside the complement of
  *claim*, is not stated.
* That the island confines the universal under every sequence of raising steps, and not only
  the one step to the edge of the sentence, is not proved, and the theories of islands compared
  are two; the paper's argument is over any theory that does not lift the island inside a
  relative clause.
* The rows are the three examples of the argument from the complement of *claim*. The readings
  with a contextually given domain and under a negative quantifier are not formalized.

## References

* [palucci-2026]
* [sharvit-1999]
* [barker-2022b]
-/

@[expose] public section

namespace Palucci2026

open scoped SetRel

variable {E : Type*} {A : Set E}

/-! ### The function a relativized description denotes -/

/-- (15), (31) The denotation of a relativized description under the article over functions: the
function on the restrictor `A` that takes each member to something `R` relates it to, where
there is exactly one such function. -/
noncomputable def functional (R : SetRel A E) : Part (A → E) := iota {f | ∀ a, a ~[R] f a}

/-- (3a), (30), (45a) The uniqueness the article presupposes of the function is uniqueness for
each member of the restrictor separately: the description is defined exactly when each volunteer
has exactly one supervisor they reported to. -/
theorem functional_dom (R : SetRel A E) : (functional R).Dom ↔ ∀ a, ∃! b, a ~[R] b := by
  classical
  refine ⟨fun ⟨f, hf, hu⟩ a ↦ ⟨f a, hf a, fun b hb ↦ ?_⟩, fun h ↦ ?_⟩
  · have hg := hu (Function.update f a b) fun c ↦ by
      obtain rfl | hne := eq_or_ne c a
      · simpa using hb
      · simpa [Function.update_of_ne hne] using hf c
    simpa using congrFun hg a
  · choose f hf hu using h
    exact ⟨f, hf, fun g hg ↦ funext fun a ↦ hu a _ (hg a)⟩

theorem mem_functional {R : SetRel A E} {f : A → E} :
    f ∈ functional R ↔ ∀ a b, a ~[R] b ↔ f a = b := by
  rw [functional, mem_iota]
  refine ⟨fun h a b ↦ ⟨fun hab ↦ ((functional_dom R).1 ⟨f, h⟩ a).unique (h.1 a) hab,
    fun e ↦ e ▸ h.1 a⟩, fun h ↦ ⟨fun a ↦ (h a _).2 rfl, fun g hg ↦ funext fun a ↦
      ((h a _).1 (hg a)).symm⟩⟩

/-! ### The composition of the description -/

/-- (27) The predicate of partial functions that the head noun and the relative clause compose
to: the functions defined at every member of the restrictor `A`, whose values all satisfy the
head noun `S`, and whose values on the restrictor satisfy the relative clause `T`. -/
def candidates (A : Set E) (S T : E → E → Prop) : Set (E → Part E) :=
  {g | (∀ x ∈ A, (g x).Dom) ∧ (∀ x, ∀ y ∈ g x, S x y) ∧ ∀ x ∈ A, ∀ y ∈ g x, T x y}

/-- (28), (29) The least candidate, the one every other candidate extends, is the function on
the restrictor that the description denotes, undefined off the restrictor. -/
theorem isLeast_candidates_iff {S T : E → E → Prop} {g : E → Part E} :
    IsLeast (candidates A S T) g ↔
      ∃ f ∈ functional ({p | S p.1 p.2 ∧ T p.1 p.2} : SetRel A E),
        g = fun x ↦ ⟨x ∈ A, fun h ↦ f ⟨x, h⟩⟩ := by
  classical
  simp only [mem_functional]
  constructor
  · rintro ⟨⟨hdom, hS, hT⟩, hle⟩
    have hA : ∀ x, (g x).Dom → x ∈ A := fun x hx ↦ by
      have hmem : (fun x ↦ (⟨x ∈ A ∧ (g x).Dom, fun h ↦ (g x).get h.2⟩ : Part E)) ∈
          candidates A S T :=
        ⟨fun x hx ↦ ⟨hx, hdom x hx⟩, fun x y ⟨h, e⟩ ↦ e ▸ hS x _ (Part.get_mem h.2),
          fun x hx y ⟨h, e⟩ ↦ e ▸ hT x hx _ (Part.get_mem h.2)⟩
      exact (hle hmem x _ (Part.get_mem hx)).1.1
    refine ⟨fun a ↦ (g a).get (hdom a a.2), fun a b ↦ ⟨fun hab ↦ ?_, ?_⟩,
      funext fun x ↦ Part.ext' ⟨hA x, hdom x⟩ fun _ _ ↦ rfl⟩
    · have hmem : Function.update g (a : E) (Part.some b) ∈ candidates A S T := by
        refine ⟨fun x hx ↦ ?_, fun x y hy ↦ ?_, fun x hx y hy ↦ ?_⟩
        · obtain rfl | hne := eq_or_ne x a
          · simp
          · simpa [Function.update_of_ne hne] using hdom x hx
        · obtain rfl | hne := eq_or_ne x a
          · rw [Function.update_self, Part.mem_some_iff] at hy
            exact hy ▸ hab.1
          · rw [Function.update_of_ne hne] at hy
            exact hS x y hy
        · obtain rfl | hne := eq_or_ne x a
          · rw [Function.update_self, Part.mem_some_iff] at hy
            exact hy ▸ hab.2
          · rw [Function.update_of_ne hne] at hy
            exact hT x hx y hy
      simpa using hle hmem a _ (Part.get_mem (hdom a a.2))
    · rintro rfl
      exact ⟨hS a _ (Part.get_mem _), hT a a.2 _ (Part.get_mem _)⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨⟨fun x hx ↦ hx, fun x y ⟨h, e⟩ ↦ e ▸ ((hf ⟨x, h⟩ _).2 rfl).1,
      fun x _ y ⟨h, e⟩ ↦ e ▸ ((hf ⟨x, h⟩ _).2 rfl).2⟩, fun h ⟨hdom, hS, hT⟩ x y ⟨hx, e⟩ ↦ ?_⟩
    have hz := Part.get_mem (hdom x hx)
    subst e
    show f ⟨x, hx⟩ ∈ h x
    rw [(hf ⟨x, hx⟩ _).1 ⟨hS x _ hz, hT x hx _ hz⟩]
    exact hz

/-! ### Closing the function -/

variable (R : SetRel A E)

/-- (37), (57) The saturated function with its pronoun bound by a quantifier over the restrictor,
as a distributive subject or *mostly* binds it: `P x y` is what is said of a member `x` of the
restrictor and the function's value `y` there. -/
noncomputable def bound (P : A → E → Prop) (Q : Set A → Prop) : Part Prop :=
  (functional R).map fun f ↦ Q {x | P x (f x)}

variable (P : E → Prop)

/-- (46) The pseudo-scope logical form: the saturated function with its pronoun bound by a
covert universal. -/
noncomputable def closure : Part Prop := bound R (fun _ ↦ P) fun s ↦ ∀ x, x ∈ s

/-- (4) The logical form with the universal scoped out of the relative clause and above the
article, which is then the article over individuals at each member of the restrictor. -/
noncomputable def raised : Part Prop :=
  ⟨∀ x, (iota {y | x ~[R] y}).Dom, fun _ ↦ ∀ x, ∀ y ∈ iota {y | x ~[R] y}, P y⟩

/-- (47) The pseudo-scope logical form has the meaning of the logical form with the universal
scoped out: the same presupposition, that each volunteer has exactly one supervisor, and the same
assertion about each of them. -/
theorem closure_eq_raised : closure R P = raised R P := by
  refine Part.ext' (functional_dom R) fun h _ ↦ propext ?_
  have hf := mem_functional.1 (Part.get_mem (o := functional R) h)
  exact ⟨fun hP x y hy ↦ (hf x y).1 (mem_iota.1 hy).1 ▸ hP x,
    fun hP x ↦ hP x _ (mem_iota.2 ⟨(hf x _).2 rfl, fun z hz ↦ ((hf x z).1 hz).symm⟩)⟩

/-! ### Predicates of the function -/

variable {f : A → E}

/-- (14) *Varied* holds of a function with two values. -/
def Vary (f : A → E) : Prop := (Set.range f).Nontrivial

theorem vary_iff : Vary f ↔ ∃ y z, f y ≠ f z := by
  simp [Vary, Set.Nontrivial]

-- (12), (13)
theorem not_exists_forall_vary_iff [Nontrivial A] [Nontrivial E] :
    ¬ ∃ P : E → Prop, ∀ f : A → E, Vary f ↔ ∀ x, P (f x) := by
  classical
  rintro ⟨P, hP⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  obtain ⟨x, y, hxy⟩ := exists_pair_ne A
  have ha : ¬ P a := fun h ↦
    let ⟨_, _, hne⟩ := vary_iff.1 ((hP fun _ ↦ a).2 fun _ ↦ h)
    hne rfl
  have hv : Vary fun z ↦ if z = x then a else b :=
    vary_iff.2 ⟨x, y, by simp [hxy.symm, hab]⟩
  exact ha (by simpa using (hP _).1 hv x)

-- (17)
theorem exists_vary_not_vary_comp_inclusion [Nontrivial E] {B : Set E} (h : A ⊆ B)
    (hA : A.Nonempty) (hB : ¬ B ⊆ A) :
    ∃ g : B → E, Vary g ∧ ¬ Vary (g ∘ Set.inclusion h) := by
  classical
  obtain ⟨e₁, e₂, he⟩ := exists_pair_ne E
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb, hbA⟩ := Set.not_subset.1 hB
  refine ⟨fun x ↦ if (x : E) ∈ A then e₁ else e₂,
    vary_iff.2 ⟨⟨a, h ha⟩, ⟨b, hb⟩, by simp [ha, hbA, he]⟩, fun hv ↦ ?_⟩
  obtain ⟨y, z, hne⟩ := vary_iff.1 hv
  simp at hne

-- (37), (38)
theorem forall_imp_cross_iff :
    (∀ r : E → A → Prop, (∀ y, r (f y) y) → ∀ x y, r (f x) y) ↔ ¬ Vary f := by
  rw [vary_iff]
  refine ⟨fun h ⟨y, z, hne⟩ ↦ hne (h (fun p y ↦ p = f y) (fun _ ↦ rfl) y z), fun h r hr x y ↦ ?_⟩
  rw [not_not.1 fun hne ↦ h ⟨x, y, hne⟩]
  exact hr y

/-! ### Raising out of the complement of *claim*

The function is read off the relation the relative clause gives when the universal binds into
the trace of relativization, so the description of (6a) has its varying reading as that of (2)
does, with nothing raised. Raising has it only if the universal can leave the complement of
*claim*, which (5a) shows it cannot. -/

section Islands

open PhraseStructure PhraseStructure.Tree

/-- A row with its tree, the embedded universal, and the reading the universal has by taking
scope over the rest of the sentence. -/
structure Case where
  /-- The paper's example. -/
  row : Datum
  /-- The sentence as it is pronounced. -/
  tree : Tree Cat String
  /-- The embedded universal. -/
  mover : Tree Cat String
  /-- The reading with the universal over the rest of the sentence. -/
  reading : String

/-- The embedded universal can raise to the edge of the sentence in one step. -/
def Case.CanRaise (I : Tree Cat String → Tree Cat String → Prop) (c : Case) : Prop :=
  ∃ p ∈ c.tree.addressOf? c.mover, c.tree.PassesNoIsland I p

instance (I : Tree Cat String → Tree Cat String → Prop) [∀ a b, Decidable (I a b)] (c : Case) :
    Decidable (c.CanRaise I) :=
  inferInstanceAs (Decidable (∃ p ∈ c.tree.addressOf? c.mover, c.tree.PassesNoIsland I p))

/-- A finite complement clause is an island for a constituent containing *each*. -/
def finiteComplement (a b : Tree Cat String) : Prop := "each" ∈ a.yield ∧ b.cat = .S

instance (a b : Tree Cat String) : Decidable (finiteComplement a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- *Each volunteer*. -/
def eachVolunteer : Tree Cat String := ltree% [N [Det "each"] [N "volunteer"]]

/-- *Each invited speaker*. -/
def eachSpeaker : Tree Cat String := ltree% [N [Det "each"] [Adj "invited"] [N "speaker"]]

/-- (2) *John included the supervisor [that each volunteer reported to]*. -/
def ex2 : Case where
  row := Examples.ex_2
  tree := ltree% [S [N "John"] [V [V "included"] [N [Det "the"] [N [N "supervisor"]
    [C [C "that"] (eachVolunteer) [V [V "reported"] [P "to"]]]]]]]
  mover := eachVolunteer
  reading := "varying definite"

/-- (5a) *A student claimed [each invited speaker was wrong]*. -/
def ex5a : Case where
  row := Examples.ex_5a
  tree := ltree% [S [N [Det "a"] [N "student"]]
    [V [V "claimed"] [S (eachSpeaker) [V [V "was"] [Adj "wrong"]]]]]
  mover := eachSpeaker
  reading := "∀ > ∃"

/-- (6a) *I included the supervisor [that you claimed [each volunteer reported to]]*. -/
def ex6a : Case where
  row := Examples.ex_6a
  tree := ltree% [S [Pron "I"] [V [V "included"] [N [Det "the"] [N [N "supervisor"]
    [C [C "that"] [Pron "you"]
      [V [V "claimed"] [S (eachVolunteer) [V [V "reported"] [P "to"]]]]]]]]]
  mover := eachVolunteer
  reading := "varying definite"

/-- The examples with trees. -/
def cases : List Case := [ex2, ex5a, ex6a]

-- (8)
theorem canRaise_finiteComplement : ex2.CanRaise finiteComplement ∧
    ¬ ex5a.CanRaise finiteComplement ∧ ¬ ex6a.CanRaise finiteComplement := by
  decide

/-- With the finite complement of *claim* an island, one step of raising does not give each
example its judgment: the universal of (6a) is inside that complement, and its varying reading
is acceptable. -/
theorem not_fits_finiteComplement : ¬ ∀ c ∈ cases,
    (c.row.readings.lookup c.reading = some .acceptable ↔ c.CanRaise finiteComplement) := by
  decide

/-- With no islands, raising does not give each example its judgment either: the universal of
(5a) raises, and its wide reading is unacceptable. -/
theorem not_fits_bot : ¬ ∀ c ∈ cases,
    (c.row.readings.lookup c.reading = some .acceptable ↔ c.CanRaise ⊥) := fun h ↦
  absurd ((h ex5a (by simp [cases])).2 ⟨_, rfl, passesNoIsland_bot _ _⟩) (by decide)

end Islands

end Palucci2026
