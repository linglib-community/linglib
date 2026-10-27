module

public import Linglib.Semantics.Modification.Coercion
public import Studies.Kamp1975
public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Partee2010
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Partee (2010): Privative Adjectives: Subsective plus Coercion

Partee argues that no adjective is privative in Kamp's sense. A privative adjective is vacuous
within its literal head, so Kamp and Partee's non-vacuity principle shifts the head to include
the adjective's value, *fur* to real or fake fur, and on the shifted head *fake* is subsective;
the tautologous *real* needs the same shift. Nowak's Polish NP-splitting data motivate the move.
The adjectives that split are the intersective, subsective and privative ones, which form no
natural class of the traditional scale, while the modal ones do not, and once the privatives are
reanalysed the adjectives that split are exactly the subsective ones. *Former*, normally
privative, does not split, a puzzle Partee leaves open.

## Implementation notes

The classes are the paper's labels for the meaning postulates, ordered by the traditional scale
that its footnote 1 says the postulates do not give, and a natural class is read as an interval
of that scale. Each Polish adjective's class is the paper's, recorded in the rows'
`paperFeatures`; for most adjectives of its lists the paper gives only the English. The shift is
`Modifier.ShiftsHead`, and *real* is the identity modifier.

## References

* [partee-2010]
* [kamp-1975]
* [kamp-partee-1995]
* [nowak-2000]
-/

@[expose] public section

namespace Partee2010

open Modifier Modifier Examples

variable {W E : Type*}

/-! ### The traditional classification -/

/-- The four labels of the traditional classification, which the paper reads as labels for the
meaning postulates (7)–(9); `nonsubsective` is the plain, modal class. -/
inductive AdjectiveClass where
  | intersective
  | subsective
  | nonsubsective
  | privative
  deriving DecidableEq, Fintype, Repr

namespace AdjectiveClass

/-- The position of a class on the traditional scale, intersective to privative. -/
def rank : AdjectiveClass → Fin 4
  | .intersective => 0
  | .subsective => 1
  | .nonsubsective => 2
  | .privative => 3

/-- The traditional scale, which footnote 1 (p. 277) says the postulates do not give. -/
instance : LinearOrder AdjectiveClass := LinearOrder.lift' rank (by decide)

/-- The meaning postulate each class stands for; the plain non-subsective class has none. -/
def postulate : AdjectiveClass → Modifier (W → E → Prop) → Prop
  | .intersective => IsIntersective
  | .subsective => IsSubsective
  | .nonsubsective => fun _ ↦ True
  | .privative => IsPrivative

/-- The reanalysis moves the privatives into the subsective class. -/
def reanalyse : AdjectiveClass → AdjectiveClass
  | .privative => .subsective
  | c => c

end AdjectiveClass

/-- The paper's class labels as the rows record them. -/
def classTable : List (String × AdjectiveClass) :=
  [("intersective", .intersective), ("subsective", .subsective), ("modal", .nonsubsective),
   ("privative", .privative)]

/-- The meaning postulates do not order the subsective and privative classes, as Kamp's *skillful*
and *fake* show (footnote 1). -/
theorem postulates_not_linear :
    ¬ (∀ adj : Modifier (Kamp1975.W2 → Kamp1975.E3 → Prop),
        AdjectiveClass.subsective.postulate adj → AdjectiveClass.privative.postulate adj) ∧
      ¬ (∀ adj : Modifier (Kamp1975.W2 → Kamp1975.E3 → Prop),
        AdjectiveClass.privative.postulate adj → AdjectiveClass.subsective.postulate adj) :=
  ⟨fun h ↦ Modifier.isPrivative_iff_forall.1 (h _ Kamp1975.skillful_subsective) (fun _ _ ↦ True) .w₁ .a
      ⟨trivial, trivial⟩ trivial,
    fun h ↦ Modifier.IsPrivative.not_isSubsective Kamp1975.fake_privative
      ⟨fun _ _ ↦ False, .w₁, .b, trivial, id⟩ (h _ Kamp1975.fake_privative)⟩

/-! ### The splitting data -/

/-- A class splits when some adjective the paper assigns to it splits. -/
def Splittable (c : AdjectiveClass) : Prop :=
  ∃ e ∈ all, e.parse? "class" classTable = some c ∧ e.judgment = .acceptable

instance : DecidablePred Splittable :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ all, _))

/-- Modal adjectives never split (16b). -/
theorem modal_no_split :
    ∀ e ∈ all, e.parse? "class" classTable = some .nonsubsective →
      e.judgment = .ungrammatical := by
  decide

/-- Every other adjective of the paper's classes splits (15c)–(15e), except *former* (14), the
puzzle that remains (p. 282). -/
theorem nonmodal_split_except_former :
    ∀ e ∈ all, ∀ c ∈ e.parse? "class" classTable, c ≠ .nonsubsective →
      (e.judgment = .acceptable ↔ e.feature? "adjective" ≠ some "former") := by
  decide

/-- The adjective classes that split form no convex region of the traditional scale (p. 279). -/
theorem splittable_not_ordConnected :
    ¬ ({c | Splittable c} : Set AdjectiveClass).OrdConnected :=
  fun h ↦ (show ¬ Splittable .nonsubsective by decide)
    (h.out (show Splittable .subsective by decide) (show Splittable .privative by decide)
      ⟨by decide, by decide⟩)

/-- Once the privatives are reanalysed as subsective, the classes that split are exactly the
subsective ones, an initial segment of the scale. -/
theorem reanalyse_splittable_iff (c : AdjectiveClass) :
    (∃ c', Splittable c' ∧ c'.reanalyse = c) ↔ c ≤ .subsective := by
  revert c
  decide

/-! ### *real* and *fake* on the shifted head -/

/-- *real* is vacuous on its literal head, and on a privatively shifted head non-vacuous iff there
are both Ns and things in the privative's value (p. 280). -/
theorem real_isNonVacuous_iff {adj : Modifier (W → E → Prop)} (hp : IsPrivative adj)
    (N : W → E → Prop) (w : W) :
    ¬ IsNonVacuous (id N) w (N w) ∧
      (IsNonVacuous (id N) w (N w ⊔ adj N w) ↔ (∃ x, N w x) ∧ ∃ x, adj N w x) := by
  refine ⟨not_isNonVacuous_self N w, ?_⟩
  change IsNonVacuous N w _ ↔ _
  rw [sup_comm, isNonVacuous_sup_self_iff]
  exact and_congr_right fun _ ↦ exists_congr fun x ↦
    ⟨And.left, fun h ↦ ⟨h, Modifier.isPrivative_iff_forall.1 hp N w x h⟩⟩

/-- On the head a privative shifts, everything is real or fake and not both, as *Is that gun real or
fake?* (10b) presupposes. -/
theorem real_xor_fake {adj : Modifier (W → E → Prop)} (hp : IsPrivative adj)
    {N : W → E → Prop} {w : W} {x : E} (hx : (N w ⊔ adj N w) x) : Xor (N w x) (adj N w x) := by
  rcases hx with h | h
  · exact Or.inl ⟨h, fun h' ↦ Modifier.isPrivative_iff_forall.1 hp N w x h' h⟩
  · exact Or.inr ⟨h, Modifier.isPrivative_iff_forall.1 hp N w x h⟩

/-- Kamp's privative *fake* shifts a noun with one real instance, the fur of (17). -/
example (w : Kamp1975.W2) : Modifier.ShiftsHead Kamp1975.fakeAdj (fun _ x ↦ x = .a) w :=
  (Modifier.IsPrivative.shiftsHead_iff Kamp1975.fake_privative).2
    ⟨⟨.b, trivial, fun h ↦ nomatch h⟩, ⟨.a, rfl⟩⟩

end Partee2010
