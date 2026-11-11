module

public import Linglib.Semantics.Composition.CallByValue
public import Linglib.Semantics.Composition.Constituency
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Percus2000
public import Linglib.Data.Examples.Readers

/-!
# Percus (2000): Constraints on Some Other Variables in Syntax

Situation pronouns are covert variables over situations: a predicate selects one, a description
contains one, and a λ binding situations tops the complement of an attitude verb and the scope of
an adverbial quantifier. Percus argues that the pronoun a verb or an adverbial quantifier selects
must be coindexed with the nearest λ above it, while the pronoun in a description may be bound from
higher up. His interpretation procedure is Heim and Kratzer's with partial functions: an
assignment gives an index an object of any kind, a situation pronoun has a value only where its
index is given a situation, and an indexed λ makes the function defined at the objects at which
its sister has a value. So [the structures he considers have his
interpretations](##Percus2000.holds_lf_iff), his two generalizations are [one condition on
trees](##Percus2000.locallyBound_lf), and the indexings it admits match the judgments [for the
attitude report](##Percus2000.judgments_26a) and [for the adverbial
quantifier](##Percus2000.judgments_35a).

## Implementation notes

A situation is a world, a round of the game and the individuals in it, and Mary's candidates for a
situation are the situations of her belief world with its round and its individuals. Each world
has one brother of the speaker, so *my brother* has a value at a situation just when that brother
is in it. The context gives `ssh₈` the proposition true of the rounds with every player in them
and gives no other index a value.

A situation pronoun counts as selected when its sister denotes a function of situations into truth
values. This covers the pronoun a verb selects and the one an adverbial quantifier selects at
once, where Percus states the two generalizations separately; the pronoun inside *my brother* has
a sister of another type and is not selected. Every λ of the structures here binds situation
pronouns, so the nearest λ is the nearest one of the kind Percus means.

## References

* [percus-2000]
* [von-fintel-heim-2011]
* [heim-kratzer-1998]
-/

@[expose] public section

namespace Percus2000

open Interpreter ManySorted PhraseStructure Tree

/-! ### The model -/

/-- The actual world and Mary's belief world. -/
inductive World where
  | actual
  | belief
  deriving DecidableEq, Fintype

inductive Person where
  | mary
  | allon
  | pierre
  deriving DecidableEq, Fintype

/-- The rounds of the game. -/
inductive Round where
  | r1
  | r2
  | r3
  deriving DecidableEq, Fintype

/-- A situation: a part of a world, with the temporal extent of a round and the individuals in
it. -/
structure Sit where
  world : World
  round : Round
  members : Finset Person
  deriving DecidableEq, Fintype

/-- The speaker's brother in a world: Allon in fact, Pierre in Mary's belief world, where she
takes Pierre to be the brother. -/
def brother : World → Person
  | .actual => .allon
  | .belief => .pierre

/-- A believer's candidates for a situation: the situation of the belief world with its round
and its individuals. -/
def dox (_ : Person) (s : Sit) : List Sit := [⟨.belief, s.round, s.members⟩]

/-- The proposition the context makes salient: the rounds of the game, the situations with every
player in them. -/
def gameRound (s : Sit) : Prop := s.members = Finset.univ

instance : DecidablePred gameRound := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The paper's scenarios: three for (26a), two for (35a). -/
inductive Scenario where
  | allon
  | pierreCanadian
  | pierreAmerican
  | unaware
  | deluded
  deriving DecidableEq

/-- Who is Canadian in which world under each scenario. -/
def IsCanadian : Scenario → Person → World → Prop
  | .allon, .allon, .belief => True
  | .pierreCanadian, .pierre, _ => True
  | .pierreAmerican, .pierre, .actual => True
  | _, _, _ => False

instance (sc : Scenario) (x : Person) (w : World) : Decidable (IsCanadian sc x w) := by
  cases sc <;> cases x <;> cases w <;> unfold IsCanadian <;> infer_instance

/-- Who won the game of a situation under each scenario. -/
def Won : Scenario → Person → Sit → Prop
  | .unaware, .pierre, ⟨.actual, _, _⟩ => True
  | .deluded, .pierre, ⟨.belief, _, _⟩ => True
  | _, _, _ => False

instance (sc : Scenario) (x : Person) (s : Sit) : Decidable (Won sc x s) := by
  obtain ⟨w, r, m⟩ := s
  cases sc <;> cases x <;> cases w <;> unfold Won <;> infer_instance

/-! ### The lexicon and the structures -/

/-- The objects an assignment may give an index: an individual, a situation, or a proposition. -/
inductive Obj where
  | ind (x : Person)
  | sit (s : Sit)
  | prop (p : Sit → Prop)

/-- The base sorts: individuals, situations, and the objects of assignments. -/
inductive Atom
  | e
  | s
  | o
  deriving DecidableEq

/-- The domains of the base sorts. -/
abbrev Dom : Atom → Type
  | .e => Person
  | .s => Sit
  | .o => Obj

/-- The situation an object is, if it is one. -/
def Obj.sit? : Obj → Part Sit
  | .sit s => .some s
  | _ => .none

@[simp] theorem Obj.sit?_sit (s : Sit) : (Obj.sit s).sit? = .some s := rfl

@[simp] theorem Obj.sit?_ind (x : Person) : (Obj.ind x).sit? = .none := rfl

@[simp] theorem Obj.sit?_prop (p : Sit → Prop) : (Obj.prop p).sit? = .none := rfl

/-- The proposition an object is, if it is one: a function defined at the situations alone. -/
def Obj.prop? : Obj → Part (Obj → Part Prop)
  | .prop p => .some fun x ↦ x.sit?.map p
  | _ => .none

/-- A function of objects is a proposition when its domain consists only of situations. -/
def IsProposition (P : Obj → Part Prop) : Prop := ∀ x, (P x).Dom → (x.sit?).Dom

/-- The words of (26a) and (35a); *won* includes its object *the game*. -/
inductive Word where
  | mary
  | thinks
  | myBrother
  | isCanadian
  | always
  | won

/-- The type of a proposition: a function of objects into truth values. -/
abbrev propTy : Ty Atom := .base .o ⇒ .t

/-- The lexical items by type. An indexed item is a situation pronoun or the silent restrictor
`ssh` of an adverbial quantifier. -/
inductive Item : Ty Atom → Type
  | mary : Item (.base .e)
  | thinks : Item (propTy ⇒ .base .e ⇒ .base .s ⇒ .t)
  | myBrother : Item (.base .s ⇒ .base .e)
  | isCanadian : Item (.base .e ⇒ .base .s ⇒ .t)
  | always : Item (propTy ⇒ propTy ⇒ .base .s ⇒ .t)
  | won : Item (.base .e ⇒ .base .s ⇒ .t)
  | pro (n : ℕ) : Item (.base .s)
  | ssh (n : ℕ) : Item propTy

/-- The item of a word, and the two items an index may be. -/
def items : Word ⊕ ℕ → List (Σ a, Item a)
  | .inl .mary => [⟨_, .mary⟩]
  | .inl .thinks => [⟨_, .thinks⟩]
  | .inl .myBrother => [⟨_, .myBrother⟩]
  | .inl .isCanadian => [⟨_, .isCanadian⟩]
  | .inl .always => [⟨_, .always⟩]
  | .inl .won => [⟨_, .won⟩]
  | .inr n => [⟨_, .pro n⟩, ⟨_, .ssh n⟩]

/-- An assignment gives an index an object, or nothing. -/
abbrev Assignment : Type := ℕ → Part Obj

/-- The denotations, partial functions throughout. With *thinks* (18c) a believer is in the
situation and the complement is true at each of her candidates for it; *always* (20) is
universal over the situations of the world of its situation that its
restrictor is true of; *my brother* (24b) is the brother, in the world of its situation, who is
in the situation; a winner (15b) is in the situation; a situation pronoun has a value where its
index is given a situation, and `ssh` where it is given a proposition. -/
def Item.val (sc : Scenario) : {a : Ty Atom} → Item a → Assignment → Ty.PDom Dom a
  | _, .mary => fun _ ↦ .some Person.mary
  | _, .thinks => fun _ ↦ .some fun P ↦ .some fun x ↦ .some fun s ↦
      .some (x ∈ s.members ∧ ∀ s' ∈ dox x s, True ∈ P (.sit s'))
  | _, .myBrother => fun _ ↦ .some fun s ↦
      ⟨brother s.world ∈ s.members, fun _ ↦ brother s.world⟩
  | _, .isCanadian => fun _ ↦ .some fun x ↦ .some fun s ↦ .some (IsCanadian sc x s.world)
  | _, .always => fun _ ↦ .some fun Q ↦ .some fun P ↦ .some fun s ↦
      .some (∀ s' : Sit, s'.world = s.world → True ∈ P (.sit s') → True ∈ Q (.sit s'))
  | _, .won => fun _ ↦ .some fun x ↦ .some fun s ↦ .some (x ∈ s.members ∧ Won sc x s)
  | _, .pro n => fun g ↦ (g n).bind Obj.sit?
  | _, .ssh n => fun g ↦ (g n).bind Obj.prop?

/-- The typing of the indices: an indexed λ abstracts over objects of any kind. -/
abbrev indexTy : ℕ → Ty Atom := fun _ ↦ .base .o

/-- The grammar: Functional Application, and abstraction over an index. -/
abbrev grammar : ManySorted.Language (Ty Atom) := application.withAbstraction indexTy

/-- An indexed λ admits abstraction over its index, and sisters Functional Application. -/
abbrev rules : Interpreter grammar Node := (typeDriven application).withAbstraction indexTy

/-- The denotations of a structure, relative to an assignment. -/
def meanings (sc : Scenario) (t : Tree Unit Word) :
    List (Σ a : Ty Atom, Assignment → Ty.PDom Dom a) :=
  t.values rules (ManySorted.Language.withAbstraction.structure (Assignments.partial Dom indexTy))
    (Item.val sc) items

/-- The context's assignment: `ssh₈` is the rounds of the game, and no other index has a
value. -/
def g₀ : Assignment := fun n ↦ if n = 8 then .some (.prop gameRound) else .none

/-- The two λ's of (26b) and (35b): `upper` is the λ adjoined to the root, index 1, and `lower` the
λ below *thinks*, index 2. -/
inductive Binder where
  | upper
  | lower
  deriving DecidableEq, Fintype

/-- The index of a λ. -/
def Binder.index : Binder → ℕ
  | .upper => 1
  | .lower => 2

/-- The situation a pronoun coindexed with a λ denotes, at the situation of evaluation `s` and
Mary's candidate `s'` for it. -/
def Binder.sit : Binder → Sit → Sit → Sit
  | .upper, s, _ => s
  | .lower, _, s' => s'

/-- The world of the situations a pronoun coindexed with a λ ranges over: the actual world for
the upper λ, Mary's belief world for the lower. -/
def Binder.world : Binder → World
  | .upper => .actual
  | .lower => .belief

/-- The matrix [λ₁ [s₁ [Mary [thinks _]]]] of (26b) and (35b), over the complement of *thinks*. -/
def matrix (X : Tree Unit Word) : Tree Unit Word := tree% [λ 1 [(.tr 1) [mary [thinks (X)]]]]

/-- The embedded clause of (26b), [λ₂ [S [[my brother T] is Canadian]]]. -/
def vpb (S T : Binder) : Tree Unit Word :=
  tree% [λ 2 [(.tr S.index) [[myBrother (.tr T.index)] isCanadian]]]

/-- The embedded clause of (35b), [λ₂ [S [ssh₈ [always [λ₃ [s₃ [[my brother s₂] won]]]]]]]. -/
def advp (S : Binder) : Tree Unit Word :=
  tree% [λ 2 [(.tr S.index) [(.tr 8) [always [λ 3 [(.tr 3) [[myBrother (.tr 2)] won]]]]]]]

/-- (26b), with the pronoun that *is Canadian* selects coindexed with `S` and the pronoun in *my
brother* with `T`: (27) is `lf .lower .upper`, (31) `lf .lower .lower` and (33)
`lf .upper .lower`. -/
def lf (S T : Binder) : Tree Unit Word := matrix (vpb S T)

/-- (35b), with the pronoun that *always* selects coindexed with `S`: (37) is `lfAlways .upper` and
(38) `lfAlways .lower`. -/
def lfAlways (S : Binder) : Tree Unit Word := matrix (advp S)

/-- A structure is true in a scenario when it denotes a proposition true, under the context's
assignment, of some situation of the actual world. -/
def Holds (sc : Scenario) (t : Tree Unit Word) : Prop :=
  ∃ u : Sit, u.world = .actual ∧ ∃ v : Assignment → Ty.PDom Dom propTy,
    ⟨propTy, v⟩ ∈ meanings sc t ∧
    ∃ P, v g₀ = .some P ∧ True ∈ P (.sit u)

-- (26b)
theorem derivs_lf (S T : Binder) : Tree.derivs rules items (lf S T) =
    [⟨propTy, .unary (.inr (.index 1 .t)) (.binary (.inl .ba) (.leaf (.pro 1)) (.binary (.inl .ba)
        (.leaf .mary)
      (.binary (.inl .fa) (.leaf .thinks) (.unary (.inr (.index 2 .t)) (.binary (.inl .ba)
        (.leaf (.pro S.index)) (.binary (.inl .ba) (.binary (.inl .fa) (.leaf .myBrother)
          (.leaf (.pro T.index))) (.leaf .isCanadian)))))))⟩] := by
  cases S <;> cases T <;> rfl

theorem holds_lf {sc : Scenario} {S T : Binder} :
    Holds sc (lf S T) ↔ ∃ u : Sit, u.world = .actual ∧ .mary ∈ u.members ∧
      ∀ s' ∈ dox .mary u, brother (T.sit u s').world ∈ (T.sit u s').members ∧
        IsCanadian sc (brother (T.sit u s').world) (S.sit u s').world := by
  simp only [Holds, meanings, Tree.values, derivs_lf, List.map_cons, List.map_nil,
    List.mem_singleton, Sigma.mk.injEq, heq_eq_eq, true_and, exists_eq_left]
  simp [Item.val, Assignments.partial]
  cases S <;> cases T <;> simp [Binder.index, Binder.sit, dox, Function.update]

-- (35b)
theorem derivs_lfAlways (S : Binder) : Tree.derivs rules items (lfAlways S) =
    [⟨propTy, .unary (.inr (.index 1 .t)) (.binary (.inl .ba) (.leaf (.pro 1)) (.binary (.inl .ba)
        (.leaf .mary)
      (.binary (.inl .fa) (.leaf .thinks) (.unary (.inr (.index 2 .t)) (.binary (.inl .ba)
        (.leaf (.pro S.index)) (.binary (.inl .ba) (.leaf (.ssh 8)) (.binary (.inl .fa) (.leaf
            .always)
          (.unary (.inr (.index 3 .t)) (.binary (.inl .ba) (.leaf (.pro 3)) (.binary (.inl .ba)
            (.binary (.inl .fa) (.leaf .myBrother) (.leaf (.pro 2))) (.leaf .won)))))))))))⟩] := by
  cases S <;> rfl

theorem holds_lfAlways {sc : Scenario} {S : Binder} :
    Holds sc (lfAlways S) ↔ ∃ u : Sit, u.world = .actual ∧ .mary ∈ u.members ∧
      ∀ s' ∈ dox .mary u, ∀ r : Sit, r.world = (S.sit u s').world → gameRound r →
        brother s'.world ∈ s'.members ∧ brother s'.world ∈ r.members ∧
          Won sc (brother s'.world) r := by
  simp only [Holds, meanings, Tree.values, derivs_lfAlways, List.map_cons, List.map_nil,
    List.mem_singleton, Sigma.mk.injEq, heq_eq_eq, true_and, exists_eq_left]
  simp [Item.val, Assignments.partial]
  cases S <;> simp [Binder.index, Binder.sit, dox, Function.update, g₀, Obj.prop?]

/-- (26b) is true in a scenario iff the brother in the world the description's pronoun `T`
ranges over is Canadian in the world the predicate's pronoun `S` ranges over: the actual brother
in Mary's belief world for (28b), her candidate brother in her belief world for (32b), and her
candidate brother in the actual world for the indexing (33) that (34b) interprets. A situation of
the actual world with every individual in it is a witness. -/
theorem holds_lf_iff {sc : Scenario} {S T : Binder} :
    Holds sc (lf S T) ↔ IsCanadian sc (brother T.world) S.world := by
  rw [holds_lf]
  constructor
  · rintro ⟨u, hu, -, h⟩
    have h' := (h ⟨.belief, u.round, u.members⟩ (by simp [dox])).2
    cases S <;> cases T <;> simpa [Binder.sit, Binder.world, hu] using h'
  · intro h
    refine ⟨⟨.actual, .r1, Finset.univ⟩, rfl, Finset.mem_univ _, fun s' hs' ↦ ?_⟩
    obtain rfl : s' = ⟨.belief, .r1, Finset.univ⟩ := by simpa [dox] using hs'
    cases S <;> cases T <;> simpa [Binder.sit, Binder.world] using h

-- (35b), (37b), (38b)
theorem holds_lfAlways_iff {sc : Scenario} {S : Binder} :
    Holds sc (lfAlways S) ↔ ∀ r : Round, Won sc .pierre ⟨S.world, r, Finset.univ⟩ := by
  rw [holds_lfAlways]
  constructor
  · rintro ⟨u, hu, -, h⟩ r
    have h' := (h ⟨.belief, u.round, u.members⟩ (by simp [dox]) ⟨S.world, r, Finset.univ⟩
      (by cases S <;> simp [Binder.sit, Binder.world, hu]) rfl).2.2
    simpa [brother] using h'
  · intro h
    refine ⟨⟨.actual, .r1, Finset.univ⟩, rfl, Finset.mem_univ _, fun s' hs' r hr hg ↦ ?_⟩
    obtain rfl : s' = ⟨.belief, .r1, Finset.univ⟩ := by simpa [dox] using hs'
    obtain ⟨w, n, m⟩ := r
    obtain rfl : m = Finset.univ := hg
    obtain rfl : w = S.world := by cases S <;> simpa [Binder.sit, Binder.world] using hr
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, by simpa [brother] using h n⟩

/-! ### Propositions

Percus takes a situation pronoun to have a value only where its index is given a situation, so
that a λ over a constituent with such a pronoun makes a function whose domain consists only of
situations, and he sets aside the indexing of (26b) with both pronouns bound by the higher λ
because the sister of *thinks* is then defined at other objects too. -/

-- (26b)
theorem derivs_vpb (S T : Binder) : Tree.derivs rules items (vpb S T) =
    [⟨propTy, .unary (.inr (.index 2 .t)) (.binary (.inl .ba) (.leaf (.pro S.index)) (.binary (.inl
        .ba)
      (.binary (.inl .fa) (.leaf .myBrother) (.leaf (.pro T.index))) (.leaf .isCanadian)))⟩] := by
  cases S <;> cases T <;> rfl

-- (35b)
theorem derivs_advp (S : Binder) : Tree.derivs rules items (advp S) =
    [⟨propTy, .unary (.inr (.index 2 .t)) (.binary (.inl .ba) (.leaf (.pro S.index)) (.binary (.inl
        .ba)
      (.leaf (.ssh 8)) (.binary (.inl .fa) (.leaf .always) (.unary (.inr (.index 3 .t)) (.binary
          (.inl .ba)
        (.leaf (.pro 3)) (.binary (.inl .ba) (.binary (.inl .fa) (.leaf .myBrother) (.leaf (.pro
            2)))
          (.leaf .won)))))))⟩] := by
  cases S <;> rfl

/-- The assignment under which the sister of *thinks* is interpreted: the context's, with the
situation `u` for the index of the higher λ. -/
def gAt (u : Sit) : Assignment := Function.update g₀ 1 (.some (.sit u))

-- (26b)
theorem not_isProposition_vpb_upper_upper (sc : Scenario) {u : Sit}
    (h : brother u.world ∈ u.members) : ∃ v P, ⟨propTy, v⟩ ∈ meanings sc (vpb .upper .upper) ∧
      v (gAt u) = .some P ∧ ¬ IsProposition P := by
  simp only [meanings, Tree.values, derivs_vpb, List.map_cons, List.map_nil,
    List.mem_singleton, Sigma.mk.injEq, heq_eq_eq, true_and]
  refine ⟨_, _, rfl, rfl, fun hP ↦ ?_⟩
  have := hP (.ind .mary)
  simp [Item.val, Assignments.partial, Binder.index, gAt, Function.update, h,
    Part.bind_dom] at this
  exact this trivial

-- (26b)
theorem isProposition_vpb (sc : Scenario) {S T : Binder} (hST : S = .lower ∨ T = .lower)
    (u : Sit) : ∃ v P, ⟨propTy, v⟩ ∈ meanings sc (vpb S T) ∧ v (gAt u) = .some P ∧
      IsProposition P := by
  simp only [meanings, Tree.values, derivs_vpb, List.map_cons, List.map_nil,
    List.mem_singleton, Sigma.mk.injEq, heq_eq_eq, true_and]
  refine ⟨_, _, rfl, rfl, fun x hx ↦ ?_⟩
  rcases hST with rfl | rfl <;> cases x <;>
    simp_all [Item.val, Assignments.partial, Binder.index, gAt, Function.update,
      Part.bind_dom]

/-- In (35b) with the pronoun of *always* bound by the higher λ, the indexing (37), the sister of
*thinks* is not a proposition either: the only pronoun the lower λ binds is in the scope of the
λ below *always*, which makes a function, empty where that pronoun has no value. -/
theorem not_isProposition_advp_upper (sc : Scenario) (u : Sit) :
    ∃ v P, ⟨propTy, v⟩ ∈ meanings sc (advp .upper) ∧ v (gAt u) = .some P ∧ ¬ IsProposition P := by
  simp only [meanings, Tree.values, derivs_advp, List.map_cons, List.map_nil,
    List.mem_singleton, Sigma.mk.injEq, heq_eq_eq, true_and]
  refine ⟨_, _, rfl, rfl, fun hP ↦ ?_⟩
  have := hP (.ind .mary)
  simp [Item.val, Assignments.partial, Binder.index, gAt, Function.update, g₀, Obj.prop?] at this

/-! ### Generalizations X and Y -/

/-- The situation pronoun a binary node selects, if one daughter is an indexed item whose sister
denotes a function of situations into truth values, paired with the index `k` of the nearest λ
above it. -/
def selectedAt (k : Option ℕ) : List (Tree Unit Word) → List (ℕ × Option ℕ)
  | [Tree.trace n _, b] | [b, Tree.trace n _] =>
    if (b.derivs rules items).map (·.1) = [.base .s ⇒ .t] then [(n, k)] else []
  | _ => []

mutual

/-- The selected situation pronouns of a tree, each paired with the index of the nearest λ above
it, given that index `k` above the tree. -/
def selected : Tree Unit Word → Option ℕ → List (ℕ × Option ℕ)
  | RoseTree.node (.bind n _) cs, _ => selectedList cs (some n)
  | RoseTree.node _ cs, k => selectedAt k cs ++ selectedList cs k

/-- The selected situation pronouns of a list of sisters. -/
def selectedList : List (Tree Unit Word) → Option ℕ → List (ℕ × Option ℕ)
  | [], _ => []
  | t :: ts, k => selected t k ++ selectedList ts k

end

/-- Generalizations X and Y: every selected situation pronoun is coindexed with the nearest λ
above it. -/
def LocallyBound (t : Tree Unit Word) : Prop := ∀ p ∈ selected t none, p.2 = some p.1

instance : DecidablePred LocallyBound := fun t ↦
  inferInstanceAs (Decidable (∀ p ∈ selected t none, p.2 = some p.1))

/-- Generalization X admits exactly the structures of (26b) whose predicate pronoun is coindexed
with the lower λ, (27) and (31), whatever λ binds the pronoun in the description. -/
theorem locallyBound_lf (S T : Binder) : LocallyBound (lf S T) ↔ S = .lower := by
  revert S T; decide

-- Generalization Y (39)
theorem locallyBound_lfAlways (S : Binder) : LocallyBound (lfAlways S) ↔ S = .lower := by
  revert S; decide

/-! ### The judgments -/

open Examples in
/-- The structures Generalization X admits make (26a) true in exactly the scenarios where it is
judged true, while the excluded indexing (33) would make it true where it is judged false. -/
theorem judgments_26a :
    ((∃ S T, LocallyBound (lf S T) ∧ Holds .allon (lf S T)) ↔
      ex26a_allon.verdict = some true) ∧
    ((∃ S T, LocallyBound (lf S T) ∧ Holds .pierreCanadian (lf S T)) ↔
      ex26a_pierreCanadian.verdict = some true) ∧
    ((∃ S T, LocallyBound (lf S T) ∧ Holds .pierreAmerican (lf S T)) ↔
      ex26a_pierreAmerican.verdict = some true) ∧
    Holds .pierreAmerican (lf .upper .lower) := by
  simp only [holds_lf_iff]
  decide

open Examples in
/-- The structure Generalization Y admits makes (35a) true in exactly the scenario where it is
judged true, while the excluded indexing (37) would make it true where it is judged false. -/
theorem judgments_35a :
    ((∃ S, LocallyBound (lfAlways S) ∧ Holds .unaware (lfAlways S)) ↔
      ex35a_unaware.verdict = some true) ∧
    ((∃ S, LocallyBound (lfAlways S) ∧ Holds .deluded (lfAlways S)) ↔
      ex35a_deluded.verdict = some true) ∧
    Holds .unaware (lfAlways .upper) := by
  simp only [holds_lfAlways_iff]
  decide

end Percus2000
