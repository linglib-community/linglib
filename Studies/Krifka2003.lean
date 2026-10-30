module

public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Reference.Kind
public import Mathlib.Data.Set.Card
public import Mathlib.Order.SupClosed

/-!
# Krifka (2003): Bare NPs: Kind-referring, Indefinites, Both, or Neither?

Krifka treats bare noun phrases as properties that type shifts, applied locally, turn into
indefinites or kinds: in the terms of the title, they are neither, but can become both. A count
noun relates numbers to individuals, so a singular count noun cannot be an argument, and the
semantic plural fills the number argument without requiring more than one, since *Yes, one*
answers *Do you have dogs?*. The existential shift applies where a predicate meets a verbal
predicate, so a bare plural takes narrow scope under negation even when moved over it, while a
determiner phrase scopes wide. Kind reference is Chierchia's down operator, which Krifka does not
confine to cumulative properties.

## Implementation notes

* Composition is stated on extensions at a world. The composition rule (51) is `Den.app`:
  functional application whichever way is well formed, and otherwise the existential shift of
  a predicate meeting a verbal predicate. Movement over negation binds a type-neutral
  variable, which substitutes the moved denotation at its trace, or an entity variable, which
  abstracts over the trace; a property has no rule for meeting the abstract, which is the
  paper's requirement that the trace of a bare noun phrase be untyped.
* Individuals are finite sets of atoms, and a count noun holds of nonempty ones only: the
  non-overlap of (53b), ¬∃z[z ≤ x ∧ z ≤ y], presupposes a domain without a null individual, so
  [no individual consists of zero dogs](##ofAtoms_zero) and without dogs
  [the semantic plural holds of nothing](##pluralize_ofAtoms_eq_empty). Counting atoms is the
  extensive measure `Finset.card` of `Mereology.IsExtensiveMeasure`, so the count of an
  individual is unique and [adds over non-overlapping individuals](##sup_mem_ofAtoms), (53),
  numeral phrases are quantized, and the semantic plural is cumulative. Link's nonempty sets of
  atoms (`Mereology.Individual`) would also exclude the null individual, but their cardinality,
  `Set.ncard`, is no extensive measure, being `0` on infinite sets.
* The down operator is `Kind.down`, the largest member of the extension at each world, which
  Krifka defines wherever there is one, as for *one dog* in a world with one dog
  (`down_withNumber_one`).
* The topic condition on kind reference, the choice-function reading of *some*, and the
  singular definite generics of the paper's last section are not formalized.

## References

* [krifka-2003]
* [chierchia-1998] — the type-shift framework, blocking, and derived kind predication
* [partee-1987] — the type shifts ∃, ι and BE
* [krifka-1989] — count nouns as measure functions
-/

@[expose] public section

namespace Krifka2003

open Mereology

variable {World Atom : Type*}

/-! ### Count nouns as measure relations -/

/-- A count noun (52a) sends each world and number `n` to the individuals that consist of `n`
instances. -/
abbrev CountNoun (World Atom : Type*) := World → ℕ → Set (Finset Atom)

/-- A number word fills the number argument (54). -/
def withNumber (n : ℕ) (den : CountNoun World Atom) : World → Set (Finset Atom) := fun w ↦ den w n

/-- The semantic plural (59b) binds the number argument existentially, with no condition that
the number exceed one. -/
def pluralize (den : CountNoun World Atom) : World → Set (Finset Atom) :=
  fun w ↦ {x | ∃ n, x ∈ den w n}

theorem mem_pluralize_of_withNumber {den : CountNoun World Atom} {n : ℕ} {w : World}
    {x : Finset Atom} (h : x ∈ withNumber n den w) : x ∈ pluralize den w :=
  ⟨n, h⟩

/-- The count noun `ofAtoms D` counts atoms: `x` consists of `n` `D`s when it is a nonempty
individual of `D`-atoms whose extensive measure `Finset.card` is `n`, the measure phrase of
`Mereology.QMOD`. -/
def ofAtoms (D : World → Set Atom) : CountNoun World Atom :=
  fun w n ↦ {x | QMOD (fun x : Finset Atom ↦ x.Nonempty ∧ ↑x ⊆ D w) Finset.card n x}

variable {D : World → Set Atom} {w : World} {x y : Finset Atom} {n m : ℕ}

-- (53a)
theorem eq_of_mem_ofAtoms (hn : x ∈ ofAtoms D w n) (hm : x ∈ ofAtoms D w m) : n = m :=
  hn.2.symm.trans hm.2

/-- The counts of non-overlapping individuals add, (53b), since atom counting is an extensive
measure. -/
theorem sup_mem_ofAtoms [DecidableEq Atom] (hx : x ∈ ofAtoms D w n) (hy : y ∈ ofAtoms D w m)
    (hxy : ¬ Overlap x y) : x ⊔ y ∈ ofAtoms D w (n + m) := by
  refine ⟨⟨hx.1.1.mono le_sup_left, ?_⟩, ?_⟩
  · rw [Finset.sup_eq_union, Finset.coe_union]
    exact Set.union_subset hx.1.2 hy.1.2
  · rw [IsExtensiveMeasure.additive (μ := Finset.card) x y hxy, hx.2, hy.2]

theorem ofAtoms_zero : ofAtoms D w 0 = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hx ↦ hx.1.1.ne_empty (Finset.card_eq_zero.1 hx.2)

theorem mem_pluralize_ofAtoms : x ∈ pluralize (ofAtoms D) w ↔ x.Nonempty ∧ ↑x ⊆ D w :=
  ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦ ⟨_, h, rfl⟩⟩

/-- Without dogs the semantic plural holds of nothing, so the existential shift of a bare plural
is false whatever it meets. -/
theorem pluralize_ofAtoms_eq_empty (hD : D w = ∅) : pluralize (ofAtoms D) w = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hx ↦ by
    obtain ⟨⟨a, ha⟩, hxD⟩ := mem_pluralize_ofAtoms.1 hx
    simpa [hD] using hxD (Finset.mem_coe.2 ha)

/-- Numeral phrases are quantized: a proper part of `n` dogs is not `n` dogs. -/
theorem qua_withNumber_ofAtoms [DecidableEq Atom] (D : World → Set Atom) (n : ℕ) (w : World) :
    QUA (· ∈ withNumber n (ofAtoms D) w) :=
  qmod_qua ((IsExtensiveMeasure.strictMono Finset.card).strictMonoOn _) n

theorem cum_pluralize_ofAtoms [DecidableEq Atom] (D : World → Set Atom) (w : World) :
    CUM (· ∈ pluralize (ofAtoms D) w) := fun x hx y hy ↦ by
  obtain ⟨hx, hxD⟩ := mem_pluralize_ofAtoms.1 hx
  obtain ⟨-, hyD⟩ := mem_pluralize_ofAtoms.1 hy
  refine mem_pluralize_ofAtoms.2 ⟨hx.mono le_sup_left, ?_⟩
  rw [Finset.sup_eq_union, Finset.coe_union]
  exact Set.union_subset hxD hyD

/-! ### Kind reference -/

-- (77)
theorem down_withNumber_one {a : Atom} (h : D w = {a}) :
    Kind.down (withNumber 1 (ofAtoms D)) w = some {a} :=
  Kind.down_eq_some_iff.2
    ⟨⟨⟨Finset.singleton_nonempty a, by simp [h]⟩, Finset.card_singleton a⟩,
      fun _ hx ↦ Finset.coe_subset.1 (by simpa [h] using hx.1.2)⟩

/-! ### Composition and narrow scope -/

/-- The extensions that composition manipulates (51) are entities, predicates, verbal
predicates, quantifiers and truth values. -/
inductive Den (E : Type*)
  | ent (x : E)
  | pred (P : E → Prop)
  | vp (V : E → Prop)
  | quant (Q : (E → Prop) → Prop)
  | tv (p : Prop)

namespace Den

variable {E : Type*}

/-- The composition rule (51) is functional application whichever way is well formed, and
otherwise Partee's existential shift (30a) of a predicate meeting a verbal predicate. -/
def app : Den E → Den E → Option (Den E)
  | pred P, ent x | ent x, pred P | vp P, ent x | ent x, vp P => some (tv (P x))
  | quant Q, vp V | vp V, quant Q | quant Q, pred V | pred V, quant Q => some (tv (Q V))
  | pred P, vp V | vp V, pred P => some (tv (Quantifier.Det.some P V))
  | _, _ => none

/-- Negation applies to truth values only. -/
def neg : Den E → Option (Den E)
  | tv p => some (tv (¬ p))
  | _ => none

/-- In movement over negation that binds a type-neutral variable (70), the moved denotation is
substituted at its trace, where it meets the verbal predicate. -/
def movedNeutral (d : Den E) (V : E → Prop) : Option (Den E) := (d.app (vp V)).bind neg

/-- In movement over negation that binds an entity variable (71), the moved denotation applies
to the abstract over the trace. -/
def movedEntity (d : Den E) (V : E → Prop) : Option (Den E) := d.app (pred fun x ↦ ¬ V x)

-- (69)
theorem app_pred_vp (P V : E → Prop) : (pred P).app (vp V) = some (tv (∃ x, P x ∧ V x)) := rfl

-- (70)
theorem movedNeutral_pred (P V : E → Prop) :
    movedNeutral (pred P) V = some (tv (¬ ∃ x, P x ∧ V x)) := rfl

theorem movedEntity_pred (P V : E → Prop) : movedEntity (pred P) V = none := rfl

theorem movedNeutral_quant (Q : (E → Prop) → Prop) (V : E → Prop) :
    movedNeutral (quant Q) V = some (tv (¬ Q V)) := rfl

theorem movedEntity_quant (Q : (E → Prop) → Prop) (V : E → Prop) :
    movedEntity (quant Q) V = some (tv (Q fun x ↦ ¬ V x)) := rfl

end Den

/-- A bare plural denotes, at each world, the property that the semantic plural yields. -/
def bare (den : CountNoun World Atom) (w : World) : Den (Finset Atom) :=
  .pred (· ∈ pluralize den w)

/-- A determiner phrase with a number word ((67), (72)) has existential force; the indefinite
article is the number word *one* as a determiner. -/
def indefinite (n : ℕ) (den : CountNoun World Atom) (w : World) : Den (Finset Atom) :=
  .quant fun P ↦ ∃ x, x ∈ den w n ∧ P x

/-- A noun phrase with a number word (54) is a predicate, so it scopes like a bare plural. -/
def numeral (n : ℕ) (den : CountNoun World Atom) (w : World) : Den (Finset Atom) :=
  .pred (· ∈ den w n)

/-- Bare plurals scope below negation whether moved or not, and cannot scope above it. -/
theorem bare_narrow (den : CountNoun World Atom) (w : World) (V : Finset Atom → Prop) :
    (bare den w).movedNeutral V = some (.tv (¬ ∃ x, (∃ n, x ∈ den w n) ∧ V x)) ∧
      (bare den w).movedEntity V = none :=
  ⟨rfl, rfl⟩

/-- In *Two dogs aren't barking* (72)–(73), a numeral phrase scopes over negation as a
determiner phrase but not as a noun phrase. -/
theorem indefinite_wide_numeral_narrow (n : ℕ) (den : CountNoun World Atom) (w : World)
    (V : Finset Atom → Prop) :
    (indefinite n den w).movedEntity V = some (.tv (∃ x, x ∈ den w n ∧ ¬ V x)) ∧
      (numeral n den w).movedEntity V = none :=
  ⟨rfl, rfl⟩

end Krifka2003
