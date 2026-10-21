module

public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Reference.Iota
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

## Main results

* `Krifka2003.isExtensiveMeasure_ofAtoms`: atom-counting nouns are extensive measures (53).
* `Krifka2003.qua_withNumber_ofAtoms`, `Krifka2003.cum_pluralize_ofAtoms`: numeral phrases are
  quantized and the semantic plural is cumulative.
* `Krifka2003.iota_withNumber_one`: in a world with exactly one dog, ∩ of *one dog* is that dog.
* `Krifka2003.bare_narrow`, `Krifka2003.indefinite_wide_numeral_narrow`: bare plurals scope
  below negation, and *two dogs* scopes over it only as a determiner phrase.

## Implementation notes

* Composition is stated on extensions at a world. The composition rule (51) is `Den.app`:
  functional application whichever way is well formed, and otherwise the existential shift of
  a predicate meeting a verbal predicate. Movement over negation binds a type-neutral
  variable, which substitutes the moved denotation at its trace, or an entity variable, which
  abstracts over the trace; a property has no rule for meeting the abstract, which is the
  paper's requirement that the trace of a bare noun phrase be untyped.
* Count nouns that count atoms (`ofAtoms`) witness the measure laws and yield the
  quantization of numeral phrases and the cumulativity of the semantic plural.
* The down operator at a world is `iota` of `IsGreatest`, the largest member of the
  extension.
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
abbrev CountNoun (World Atom : Type*) := World → ℕ → Set (Set Atom)

/-- A count noun is an extensive measure function in its number argument (53) when the count of
an individual is unique and the counts of non-overlapping individuals add. -/
def IsExtensiveMeasure (den : CountNoun World Atom) : Prop :=
  (∀ w n m x, x ∈ den w n → x ∈ den w m → n = m) ∧
  (∀ w n m x y, x ∈ den w n → y ∈ den w m → Disjoint x y → x ∪ y ∈ den w (n + m))

/-- A number word fills the number argument (54). -/
def withNumber (n : ℕ) (den : CountNoun World Atom) : World → Set (Set Atom) := fun w ↦ den w n

/-- The semantic plural (59b) binds the number argument existentially, with no condition that
the number exceed one. -/
def pluralize (den : CountNoun World Atom) : World → Set (Set Atom) :=
  fun w ↦ {x | ∃ n, x ∈ den w n}

/-- The semantic plural is true of a single instance, so *Yes, one* answers *Do you have dogs?*. -/
theorem mem_pluralize_of_withNumber {den : CountNoun World Atom} {n : ℕ} {w : World}
    {x : Set Atom} (h : x ∈ withNumber n den w) : x ∈ pluralize den w :=
  ⟨n, h⟩

/-- The count noun `ofAtoms D` counts atoms, so that `x` consists of `n` `D`s when it is a
finite set of `n` atoms of `D`. -/
def ofAtoms (D : World → Set Atom) : CountNoun World Atom :=
  fun w n ↦ {x | x ⊆ D w ∧ x.Finite ∧ x.ncard = n}

theorem isExtensiveMeasure_ofAtoms (D : World → Set Atom) : IsExtensiveMeasure (ofAtoms D) :=
  ⟨fun _ _ _ _ ⟨_, _, h⟩ ⟨_, _, h'⟩ ↦ h.symm.trans h',
    fun _ _ _ _ _ ⟨hx, hfx, hnx⟩ ⟨hy, hfy, hny⟩ hd ↦
      ⟨Set.union_subset hx hy, hfx.union hfy, by rw [Set.ncard_union_eq hd hfx hfy, hnx, hny]⟩⟩

/-- Numeral phrases are quantized: a proper part of `n` dogs is not `n` dogs. -/
theorem qua_withNumber_ofAtoms (D : World → Set Atom) (n : ℕ) (w : World) :
    QUA (· ∈ withNumber n (ofAtoms D) w) :=
  qua_of_forall fun _ _ ⟨_, hf, hn⟩ hlt ⟨_, _, hn'⟩ ↦
    (Set.ncard_lt_ncard hlt hf).ne (hn'.trans hn.symm)

/-- The semantic plural of an atom-counting noun is cumulative. -/
theorem cum_pluralize_ofAtoms (D : World → Set Atom) (w : World) :
    CUM (· ∈ pluralize (ofAtoms D) w) :=
  fun _ ⟨_, hx, hfx, _⟩ _ ⟨_, hy, hfy, _⟩ ↦ ⟨_, Set.union_subset hx hy, hfx.union hfy, rfl⟩

/-! ### Kind reference -/

/-- The down operator (77) is not confined to cumulative properties: in a world with exactly one
dog, `∩[one dog]` is that dog. -/
theorem iota_isGreatest_withNumber_one {D : World → Set Atom} {w : World} {a : Atom}
    (h : D w = {a}) :
    iota (IsGreatest (withNumber 1 (ofAtoms D) w)) = some {a} :=
  iota_isGreatest_eq_some_iff.2
    ⟨⟨h ▸ subset_rfl, Set.finite_singleton a, Set.ncard_singleton a⟩, fun _ ⟨hx, _, _⟩ ↦ h ▸ hx⟩

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
  | pred P, vp V | vp V, pred P => some (tv (Quantifier.GQ.some P V))
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

/-- In *Dogs are barking* (69), a bare noun phrase meets the verbal predicate by the existential
shift. -/
theorem app_pred_vp (P V : E → Prop) : (pred P).app (vp V) = some (tv (∃ x, P x ∧ V x)) := rfl

/-- In *Dogs aren't barking* (70), a bare noun phrase moved over negation still scopes below it,
since the shift applies at the trace. -/
theorem movedNeutral_pred (P V : E → Prop) :
    movedNeutral (pred P) V = some (tv (¬ ∃ x, P x ∧ V x)) := rfl

/-- A property cannot bind an entity variable: there is no wide-scope derivation for a bare
noun phrase. -/
theorem movedEntity_pred (P V : E → Prop) : movedEntity (pred P) V = none := rfl

/-- In *A dog isn't barking* with a quantifier variable (71.c.ii), negation scopes over the
quantifier. -/
theorem movedNeutral_quant (Q : (E → Prop) → Prop) (V : E → Prop) :
    movedNeutral (quant Q) V = some (tv (¬ Q V)) := rfl

/-- In *A dog isn't barking* with an entity variable (71.c.i), the quantifier scopes over
negation. -/
theorem movedEntity_quant (Q : (E → Prop) → Prop) (V : E → Prop) :
    movedEntity (quant Q) V = some (tv (Q fun x ↦ ¬ V x)) := rfl

end Den

/-- A bare plural denotes, at each world, the property that the semantic plural yields. -/
def bare (den : CountNoun World Atom) (w : World) : Den (Set Atom) :=
  .pred (· ∈ pluralize den w)

/-- A determiner phrase with a number word ((67), (72)) has existential force; the indefinite
article is the number word *one* as a determiner. -/
def indefinite (n : ℕ) (den : CountNoun World Atom) (w : World) : Den (Set Atom) :=
  .quant fun P ↦ ∃ x, x ∈ den w n ∧ P x

/-- A noun phrase with a number word (54) is a predicate, so it scopes like a bare plural. -/
def numeral (n : ℕ) (den : CountNoun World Atom) (w : World) : Den (Set Atom) :=
  .pred (· ∈ den w n)

/-- Bare plurals scope below negation whether moved or not, and cannot scope above it. -/
theorem bare_narrow (den : CountNoun World Atom) (w : World) (V : Set Atom → Prop) :
    (bare den w).movedNeutral V = some (.tv (¬ ∃ x, (∃ n, x ∈ den w n) ∧ V x)) ∧
      (bare den w).movedEntity V = none :=
  ⟨rfl, rfl⟩

/-- In *Two dogs aren't barking* (72)–(73), a numeral phrase scopes over negation as a
determiner phrase but not as a noun phrase. -/
theorem indefinite_wide_numeral_narrow (n : ℕ) (den : CountNoun World Atom) (w : World)
    (V : Set Atom → Prop) :
    (indefinite n den w).movedEntity V = some (.tv (∃ x, x ∈ den w n ∧ ¬ V x)) ∧
      (numeral n den w).movedEntity V = none :=
  ⟨rfl, rfl⟩

end Krifka2003
