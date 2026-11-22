module

public import Linglib.Semantics.Exhaustification.Trivalent
public import Linglib.Semantics.Focus.Particles
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.DeriveFintype

/-!
# Chow and Erlewine (2022): Restrictions on the position of exh

A clause is a scalar item under a spine of overt operators, and the covert exhaustifier *exh* may
adjoin at any site of the spine. Predicates of the focused individual denote trivalent
propositions `F → W → Trivalent`. Negation is `ᶜ`, a presupposition hole. The additive `also C`
asserts its scope of the focused individual and presupposes `Focus.additivePresup` on the
identity scale: its scope is true of some other individual among the salient ones `C`. The spine
denotes by `spine C : FreeMonoid ClauseOp →* Function.End (F → W → Trivalent)`, so the
alternative to a clause is the same spine over the scale-mate of its scalar item, and *exh* at
site `i` is Spector and Sudo's strong-negation `Exhaustification.Trivalent.exh2` of the material
below `i` against that alternative, under the operators above `i`.

Since `exh2` inherits the presuppositions of the alternatives it excludes, *exh* above *also*
presupposes what *also* presupposes of the scalar item and of its scale-mate
(`exh2_also_eq_undefined_iff`), where *also* above *exh* presupposes that the exhaustified scope
holds of a salient individual. A site is vacuous when *exh* there leaves the clause's denotation
unchanged, and `BaseClause.IsLowestSite` picks out the lowest site commanding the scalar item
that is not vacuous. A scalar item with the strong feature requires its *exh* at that site, one
with the weak feature allows any site up to the edge of its finite clause, and an unmarked one
allows any site (`ExhFeature.Allows`).

Ignorance inferences are computed over belief states by innocent exclusion above a necessity
operator, and the three parses of *also* with two instances of *exh* are separated by the four
kinds of antecedent of Marty and Romoli (`antecedent_pattern`).

## Implementation notes

A scalar item that has moved above an operator is interpreted in its base position, and movement
changes only which sites command it. The embedding verb denotes the identity, and matters only to
the edge of the finite clause. The higher *exh* of the ignorance parses takes as alternatives the
two exhaustified disjuncts under the necessity operator. The presupposition of the parse with
*also* between the two instances of *exh* is stated as `presupBetween`, not derived from `exh2`.
The examples with *again* are not modelled.

## References

* [chow-erlewine-2022]
* [spector-sudo-2017]
* [marty-romoli-2021]
* [fox-2007]
* [chierchia-2013]
* [meyer-2013]
-/

@[expose] public section

namespace ChowErlewine2022

open Exhaustification Exhaustification.Trivalent

/-! ### Operators -/

section Operators

variable {F W : Type*} [Fintype F] [DecidableEq F] (C : Set F) [DecidablePred (· ∈ C)]

instance (P : F → W → Trivalent) (x : F) :
    DecidablePred (· ∈ Focus.additivePresup (· = ·) C (fun y ↦ Trivalent.posExt (P y)) x) :=
  fun w ↦ inferInstanceAs (Decidable (∃ j ∈ C, w ∈ Trivalent.posExt (P j) ∧ ¬ x = j))

/-- *Also* asserts its scope of the focused individual and presupposes that the scope is true of
another individual among the salient ones `C`. -/
def also (P : F → W → Trivalent) (x : F) (w : W) : Trivalent :=
  .transplication
    (.ofProp (w ∈ Focus.additivePresup (· = ·) C (fun y ↦ Trivalent.posExt (P y)) x)) (P x w)

variable {C} {P Q : F → W → Trivalent} {x : F} {w : W}

theorem also_eq_undefined_iff :
    also C P x w = .undefined ↔
      w ∉ Focus.additivePresup (· = ·) C (fun y ↦ Trivalent.posExt (P y)) x ∨
        P x w = .undefined := by
  simp [also]

theorem also_eq_true_iff :
    also C P x w = .true ↔
      w ∈ Focus.additivePresup (· = ·) C (fun y ↦ Trivalent.posExt (P y)) x ∧ P x w = .true := by
  simp [also]

/-- (5): *exh* above *also* that excludes the alternative is defined only where the additive
presuppositions of both the scalar item and its scale-mate hold. -/
theorem exh2_also_eq_undefined_iff [Fintype W]
    (h : Excluded (·ᶜ) (fun _ : Unit ↦ also C Q x) (also C P x) ()) :
    exh2 (fun _ : Unit ↦ also C Q x) (also C P x) w = .undefined ↔
      also C P x w = .undefined ∨ also C Q x w = .undefined := by
  simp [exh2_eq_undefined_iff, h]

end Operators

/-! ### Clauses and adjunction sites -/

/-- An overt operator on the spine of a clause. -/
inductive ClauseOp where
  | also
  | not
  | embed
  deriving DecidableEq, Repr

section Clauses

variable {F W : Type*} [Fintype F] [DecidableEq F] (C : Set F) [DecidablePred (· ∈ C)]

/-- The denotation of an overt operator. -/
def ClauseOp.denote : ClauseOp → Function.End (F → W → Trivalent)
  | .also => ChowErlewine2022.also C
  | .not => fun P x w ↦ (P x w)ᶜ
  | .embed => id

/-- The denotation of a spine of operators, the highest first, is the composition of their
denotations. -/
def spine : FreeMonoid ClauseOp →* Function.End (F → W → Trivalent) :=
  FreeMonoid.lift (ClauseOp.denote C)

@[simp] theorem spine_of (o : ClauseOp) :
    spine (W := W) C (FreeMonoid.of o) = o.denote C := rfl

/-- A base clause is a scalar item and its scale-mate, predicated of the focused individual, under
the overt operators `ops`, the highest first. Site `i` is the adjunction position with `i`
operators above it, and it commands the scalar item when `i ≤ triggerDepth`. -/
structure BaseClause (F W : Type*) where
  /-- The scalar item. -/
  item : F → W → Trivalent
  /-- The scale-mate of the scalar item. -/
  mate : F → W → Trivalent
  /-- The overt operators above the predicate, the highest first. -/
  ops : List ClauseOp
  /-- The number of overt operators above the surface position of the scalar item. -/
  triggerDepth : ℕ

variable [Fintype W] (b : BaseClause F W) (i : ℕ)

/-- The clause without *exh*. -/
def BaseClause.plain : F → W → Trivalent := spine C (FreeMonoid.ofList b.ops) b.item

/-- The clause with *exh* adjoined at site `i`. -/
def BaseClause.withExhAt : F → W → Trivalent :=
  spine C (FreeMonoid.ofList (b.ops.take i)) fun x ↦
    exh2 (fun _ : Unit ↦ spine C (FreeMonoid.ofList (b.ops.drop i)) b.mate x)
      (spine C (FreeMonoid.ofList (b.ops.drop i)) b.item x)

/-- *Exh* at site `i` is vacuous when it leaves the denotation of the clause unchanged. -/
def BaseClause.Vacuous : Prop := b.withExhAt C i = b.plain C

instance : Decidable (b.Vacuous C i) := inferInstanceAs (Decidable (b.withExhAt C i = b.plain C))

/-- (9): the lowest site commanding the scalar item at which *exh* is not vacuous. -/
@[mk_iff]
structure BaseClause.IsLowestSite : Prop where
  /-- The site commands the scalar item. -/
  le : i ≤ b.triggerDepth
  /-- *Exh* at the site is not vacuous. -/
  not_vacuous : ¬ b.Vacuous C i
  /-- *Exh* at every lower site commanding the scalar item is vacuous. -/
  vacuous_of_lt : ∀ j ≤ b.triggerDepth, i < j → b.Vacuous C j

instance : Decidable (b.IsLowestSite C i) :=
  decidable_of_iff' _ (BaseClause.isLowestSite_iff C b i)

/-- The site just above the verb embedding the finite clause of the scalar item, or the root in a
single clause. -/
def BaseClause.clauseEdge : ℕ :=
  (((List.range b.triggerDepth).filter (b.ops[·]? = some .embed)).max?).getD 0

/-- The exhaustification feature of a scalar item. -/
inductive ExhFeature where
  | strong
  | weak
  | none
  deriving DecidableEq, Repr

/-- The sites at which a feature allows the *exh* of its scalar item: the strong feature only
the lowest non-vacuous site, the weak feature the commanding sites up to the edge of the finite
clause, and no feature every commanding site. -/
def ExhFeature.Allows : ExhFeature → Prop
  | .strong => b.IsLowestSite C i
  | .weak => b.clauseEdge ≤ i ∧ i ≤ b.triggerDepth
  | .none => i ≤ b.triggerDepth

instance (f : ExhFeature) : Decidable (f.Allows C b i) := by
  cases f <;> unfold ExhFeature.Allows <;> infer_instance

end Clauses

/-- The scalar items classified. -/
inductive SITrigger where
  | disj
  | conj
  | univAll
  | unstressedSome
  | bareNumeral
  | stressedSome
  | scalarAdj
  deriving DecidableEq, Repr

/-- (30): disjunction, conjunction, *all*, unstressed *some* and bare numerals bear the strong
feature, stressed *some* the weak one, and scalar adjectives none. -/
def SITrigger.feature : SITrigger → ExhFeature
  | .stressedSome => .weak
  | .scalarAdj => .none
  | _ => .strong

/-! ### The teaching model -/

/-- The two languages. -/
inductive Lang where
  | arabic
  | basque
  deriving DecidableEq, Fintype, Repr

/-- The focused individual and the salient antecedent. -/
inductive Individual where
  | nina
  | mira
  deriving DecidableEq, Fintype, Repr

/-- A world fixes the languages each individual teaches. -/
abbrev TeachWorld := Individual → Finset Lang

/-- The salient individuals. -/
abbrev salient : Set Individual := {.mira}

/-- "teaches Arabic or Basque". -/
def orLex : Individual → TeachWorld → Trivalent := fun x w ↦ .ofProp (w x).Nonempty

/-- "teaches Arabic and Basque". -/
def andLex : Individual → TeachWorld → Trivalent := fun x w ↦ .ofProp (w x = Finset.univ)

/-- (3): *[Nina]F also teaches Arabic or Basque*. -/
def teachOr : BaseClause Individual TeachWorld := ⟨orLex, andLex, [.also], 1⟩

/-- (7): *Arabic or Basque is also taught by [Nina]F*, the disjunction above *also*. -/
def passiveOr : BaseClause Individual TeachWorld := { teachOr with triggerDepth := 0 }

/-- (16): *[Nina]F also doesn't teach Arabic and Basque*. -/
def negConj : BaseClause Individual TeachWorld := ⟨andLex, orLex, [.also, .not], 2⟩

/-- (28): matrix *also* above the verb embedding the clause of the scalar item. -/
def embedded : BaseClause Individual TeachWorld :=
  { teachOr with ops := [.also, .embed], triggerDepth := 2 }

/-! ### The additive diagnostic -/

-- (1)
theorem exh2_orLex_eq_true_iff :
    ∀ w, exh2 (fun _ : Unit ↦ andLex .nina) (orLex .nina) w = .true ↔ (w .nina).card = 1 := by
  decide

/-- (4): *also* above *exh* presupposes that the salient individual teaches exactly one of the
two languages. -/
theorem also_exh_ne_undefined_iff :
    ∀ w, teachOr.withExhAt salient 1 .nina w ≠ .undefined ↔ (w .mira).card = 1 := by decide

-- (5)
theorem exh_also_ne_undefined_iff :
    ∀ w, teachOr.withExhAt salient 0 .nina w ≠ .undefined ↔ w .mira = Finset.univ := by decide

-- (5)
theorem exh_also_eq_true_iff :
    ∀ w, teachOr.withExhAt salient 0 .nina w = .true ↔
      w .mira = Finset.univ ∧ (w .nina).card = 1 := by decide

/-- (8): the *exh* of disjunction adjoins below *also* when the disjunction is below it, and
above *also* when the disjunction has moved above it. -/
theorem allows_disj :
    (∀ i ≤ 1, SITrigger.disj.feature.Allows salient teachOr i ↔ i = 1) ∧
      SITrigger.disj.feature.Allows salient passiveOr 0 := by decide

/-! ### Indirect scalar implicatures under negation -/

-- (18c)
theorem vacuous_negConj : negConj.Vacuous salient 2 := by decide

-- (19)
theorem isLowestSite_negConj : negConj.IsLowestSite salient 1 := by decide

-- (18b)
theorem also_exh_not_eq_true_iff :
    ∀ w, negConj.withExhAt salient 1 .nina w = .true ↔
      (w .mira).card = 1 ∧ (w .nina).card = 1 := by decide

-- (18a)
theorem exh_also_not_ne_undefined_iff :
    ∀ w, negConj.withExhAt salient 0 .nina w ≠ .undefined ↔ w .mira = ∅ := by decide

-- (18c)
theorem also_not_exh_ne_undefined_iff :
    ∀ w, negConj.withExhAt salient 2 .nina w ≠ .undefined ↔ w .mira ≠ Finset.univ := by decide

/-! ### Variation by scalar item

The scale of *some* and *all* over a domain of two is that of disjunction and conjunction, so the
clauses with *some* are those of the teaching model. -/

-- (14a), (26a)
theorem allows_some :
    ¬ SITrigger.unstressedSome.feature.Allows salient teachOr 0 ∧
      SITrigger.stressedSome.feature.Allows salient teachOr 0 := by decide

-- (28)
theorem allows_stressedSome_embedded :
    ∀ i ≤ 2, SITrigger.stressedSome.feature.Allows salient embedded i ↔ i ≠ 0 := by decide

/-- The two cities of (24a). -/
inductive City where
  | paris
  | newYork
  deriving DecidableEq, Fintype, Repr

/-- The temperatures, of which freezing is also cold. -/
inductive Temp where
  | mild
  | cold
  | freezing
  deriving DecidableEq, Fintype, Repr

/-- (24a): *it's also cold in [Paris]F*. -/
def coldClause : BaseClause City (City → Temp) :=
  ⟨fun c w ↦ .ofProp (w c ≠ .mild), fun c w ↦ .ofProp (w c = .freezing), [.also], 1⟩

-- (24a)
theorem allows_scalarAdj :
    SITrigger.scalarAdj.feature.Allows ({.newYork} : Set City) coldClause 0 ∧
      (∀ w, w .newYork = .freezing →
        coldClause.withExhAt ({.newYork} : Set City) 0 .paris w ≠ .undefined) ∧
      ∃ w, w .newYork = .freezing ∧
        coldClause.withExhAt ({.newYork} : Set City) 1 .paris w = .undefined := by decide

/-! ### Ignorance implicatures

A belief state about an individual is the set of teaching profiles the speaker leaves open, and
the necessity operator holds of a property true throughout the state. -/

/-- (31): *exh* above the necessity operator above *exh*, by innocent exclusion with prejacent
"believed to teach exactly one" and alternatives "believed to teach only `l`". -/
def ignorance : Set (Finset (Finset Lang)) :=
  exhIE (Set.range fun l : Lang ↦ {s | ∀ t ∈ s, t = {l}}) {s | ∀ t ∈ s, t.card = 1}

instance : DecidablePred (· ∈ ignorance) := fun s ↦
  inferInstanceAs (Decidable (s ∈ exhIE _ _))

-- (31)
theorem ignorance_eq :
    ignorance = {s | (∀ t ∈ s, t.card = 1) ∧ ∀ l : Lang, ∃ t ∈ s, l ∉ t} := by
  ext s; revert s; decide

/-- (34): *also* above both instances of *exh* presupposes that the speaker's state about some
salient individual is one of ignorance. -/
def presupAbove (ctx : List (Finset (Finset Lang))) : Prop := ∃ s ∈ ctx, s ∈ ignorance

instance (ctx : List (Finset (Finset Lang))) : Decidable (presupAbove ctx) :=
  inferInstanceAs (Decidable (∃ s ∈ ctx, s ∈ ignorance))

/-- (35): *also* between the two instances of *exh* presupposes a salient individual believed
to teach exactly one language and, for each language, one believed to teach only it. -/
def presupBetween (ctx : List (Finset (Finset Lang))) : Prop :=
  (∃ s ∈ ctx, ∀ t ∈ s, t.card = 1) ∧ ∀ l : Lang, ∃ s ∈ ctx, ∀ t ∈ s, t = {l}

instance (ctx : List (Finset (Finset Lang))) : Decidable (presupBetween ctx) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- (33): of the disjunctive, conjunctive, split and simple antecedents, given as the speaker's
state about each salient individual, the disjunctive one satisfies only the presupposition of
*also* above both instances of *exh*, the split one only that of *also* between them, and the
other two neither. -/
theorem antecedent_pattern :
    (presupAbove [{{.arabic}, {.basque}}] ∧ ¬ presupBetween [{{.arabic}, {.basque}}]) ∧
    (¬ presupAbove [{Finset.univ}] ∧ ¬ presupBetween [{Finset.univ}]) ∧
    (¬ presupAbove [{{.arabic}}, {{.basque}}] ∧ presupBetween [{{.arabic}}, {{.basque}}]) ∧
    (¬ presupAbove [{{.arabic}}] ∧ ¬ presupBetween [{{.arabic}}]) := by decide

/-- An operator of the parses of (37): *also*, the higher *exh*, the necessity operator, and the
*exh* of the disjunction. -/
inductive IgnOp where
  | also
  | ignExh
  | nec
  | siExh
  deriving DecidableEq, Repr

/-- The site of the *exh* of the disjunction, the number of overt operators above it. -/
def siExhSite (p : List IgnOp) : ℕ := (p.takeWhile (· ≠ .siExh)).count .also

/-- (37): a parse is grammatical exactly when the *exh* of the disjunction is at the site its
strong feature requires, so *also* may be above both instances of *exh* or between them, and not
below both. -/
theorem parse37_grammaticality :
    SITrigger.disj.feature.Allows salient teachOr (siExhSite [.also, .ignExh, .nec, .siExh]) ∧
    SITrigger.disj.feature.Allows salient teachOr (siExhSite [.ignExh, .nec, .also, .siExh]) ∧
    ¬ SITrigger.disj.feature.Allows salient teachOr (siExhSite [.ignExh, .nec, .siExh, .also]) := by
  decide

end ChowErlewine2022
