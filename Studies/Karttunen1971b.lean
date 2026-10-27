module

public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Semantics.Presupposition.FamilyVariant
public import Linglib.Logic.Trivalent.Basic
public import Linglib.Logic.Modal.Basic
public import Linglib.Data.Examples.Karttunen1971b

/-!
# Karttunen (1971): Some observations on factivity

Karttunen describes a factive verb by meaning postulates rather than by a presupposition split
off from its sentence. A sentence is true, false or neither, and one sentence necessitates
another, in van Fraassen's term, when the second is true wherever the first is. For a
semi-factive such as *discover*, the sentence and its negation each necessitate the complement.
For a true factive such as *regret*, so do the possibility of the sentence and the possibility
of its negation, which Karttunen proposes as the definition of presupposition in general.

An assertion commits its speaker to the sentence and a negative assertion to its negation, while
a question and the antecedent of a conditional conversationally imply only that the sentence is
possible. The two classes therefore agree in assertions and come apart in the other
environments.

## Implementation notes

* Possibility is read on an accessibility relation, of which the paper assumes only that what is
  the case is possible, so the relation is reflexive and otherwise arbitrary.
* A question and a conditional antecedent are represented by the possibility they conversationally
  imply.
* The subjunctive *poss-ing* complements of section 2 are not represented.

## References

* [karttunen-1971b]
* [van-fraassen-1968]
* [kiparsky-kiparsky-1970]
-/

@[expose] public section

namespace Karttunen1971b

open Presupposition ModalLogic

variable {W : Type*} {R : SetRel W W} {A : W → SignType} {s : W → Prop}
  {c : Factivity} {e : FamilyVariant}

private theorem eq_one_sup_neg_eq_one (A : W → SignType) :
    ((A · = 1) ⊔ (-A · = 1) : W → Prop) = (A · ≠ 0) :=
  funext fun w ↦ propext <| by simp only [Pi.sup_apply, sup_Prop_eq]; cases A w <;> simp

/-! ### The meaning postulates -/

/-- The meaning postulates of a factivity class, for a sentence `A` with complement `s`. A
semi-factive sentence and its negation each necessitate the complement, (11). For a true factive
the possibility of the sentence and the possibility of its negation do, (11′), which is to say
that the sentence presupposes its complement (fn. 8). -/
def Postulates (c : Factivity) (R : SetRel W W) (A : W → SignType) (s : W → Prop) : Prop :=
  match c with
  | .semi => (A · = 1) ≤ s ∧ (-A · = 1) ≤ s
  | .full => ◇[R] (A · = 1) ≤ s ∧ ◇[R] (-A · = 1) ≤ s

theorem postulates_semi_iff : Postulates .semi R A s ↔ (A · ≠ 0) ≤ s := by
  rw [← eq_one_sup_neg_eq_one, sup_le_iff]; rfl

theorem postulates_full_iff : Postulates .full R A s ↔ ◇[R] (A · ≠ 0) ≤ s := by
  rw [← eq_one_sup_neg_eq_one, diamond_sup, sup_le_iff]; rfl

theorem postulates_full_iff_le_box : Postulates .full R A s ↔ (A · ≠ 0) ≤ □[R.inv] s :=
  postulates_full_iff.trans (diamond_box_gc R _ _)

-- fn. 9
theorem Postulates.semi [R.IsRefl] (h : Postulates .full R A s) : Postulates .semi R A s :=
  postulates_semi_iff.2 <| (diamond_T_iff.2 ‹_› _).trans (postulates_full_iff.1 h)

/-! ### Environments -/

/-- What the speaker of a sentence in an environment is committed to. An assertion commits her
to the sentence and a negative assertion to its negation. A question and the antecedent of a
conditional conversationally imply that the sentence is possible (fn. 5), which a possibility
statement asserts, (26). -/
def commitment (R : SetRel W W) (A : W → SignType) : FamilyVariant → W → Prop
  | .unembedded => (A · = 1)
  | .negation => (-A · = 1)
  | .question | .conditionalAntecedent | .epistemicModal => ◇[R] (A · = 1)

/-- The complement of a factive of class `c` follows in environment `e` when, in every model
where what is the case is possible, the complement of a sentence obeying the postulates of `c`
is true wherever the speaker's commitment is. -/
def Projects (c : Factivity) (e : FamilyVariant) : Prop :=
  ∀ (W : Type) (R : SetRel W W) [R.IsRefl] (A : W → SignType) (s : W → Prop),
    Postulates c R A s → commitment R A e ≤ s

theorem Postulates.commitment_le [R.IsRefl] (h : Postulates c R A s)
    (hce : c = .full ∨ e = .unembedded ∨ e = .negation) : commitment R A e ≤ s := by
  obtain rfl | rfl | rfl := hce
  · cases e; exacts [h.semi.1, h.semi.2, h.1, h.1, h.1]
  · cases c; exacts [h.semi.1, h.1]
  · cases c; exacts [h.semi.2, h.2]

-- (26b), (26c)
theorem exists_semi_not_diamond_le :
    ∃ (R : SetRel Bool Bool) (_ : R.IsRefl) (A : Bool → SignType) (s : Bool → Prop),
      Postulates .semi R A s ∧ ¬ ◇[R] (A · = 1) ≤ s :=
  ⟨.univ, inferInstance, fun b ↦ cond b 1 0, (· = true),
    postulates_semi_iff.2 fun b ↦ by cases b <;> simp,
    fun h ↦ Bool.false_ne_true (h false ⟨true, trivial, rfl⟩)⟩

/-- The complement follows exactly when the verb is a true factive or the sentence is asserted or
negated. -/
theorem projects_iff : Projects c e ↔ c = .full ∨ e = .unembedded ∨ e = .negation := by
  refine ⟨fun h ↦ ?_, fun h W R _ A s hA ↦ hA.commitment_le h⟩
  obtain ⟨R, _, A, s, hA, hn⟩ := exists_semi_not_diamond_le
  cases c
  · exact .inl rfl
  cases e
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)
  all_goals exact absurd (h Bool R A s hA) hn

instance (c : Factivity) (e : FamilyVariant) : Decidable (Projects c e) :=
  decidable_of_iff' _ projects_iff

theorem Projects.commitment_le [R.IsRefl] (hp : Projects c e) (h : Postulates c R A s) :
    commitment R A e ≤ s :=
  h.commitment_le (projects_iff.1 hp)

-- (5), (14)
theorem exists_complement {ι : Type*} {S : ι → Prop} {A : ι → W → SignType} {s : ι → W → Prop}
    [R.IsRefl] (hp : Projects c e) (hA : ∀ x, Postulates c R (A x) (s x)) {w : W}
    (h : ∃ x, S x ∧ commitment R (A x) e w) : ∃ x, S x ∧ s x w :=
  let ⟨x, hx, hw⟩ := h; ⟨x, hx, hp.commitment_le (hA x) w hw⟩

/-! ### The rows -/

/-- The judgments of (2), (22) and (24)–(26) are the postulates' predictions for each verb's English
entry. -/
theorem projection_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "projection" →
      ∀ e ∈ row.environment?, ∀ b ∈ row.projective?,
        ∃ v ∈ English.Verbs.verbs, row.feature? "verb" = some v.form ∧
          ∃ c ∈ v.factivity, (b = true ↔ Projects c e) := by
  decide

/-! ### The emphatic denial -/

/-- The emphatic denial of a true factive sentence is consistent with the falsity of its complement
((23), fn. 7). -/
theorem emphatic_denial :
    ∃ (R : SetRel Unit Unit) (_ : R.IsRefl) (A : Unit → SignType) (s : Unit → Prop),
      Postulates .full R A s ∧ -SignType.ofProp (A () = 1) = 1 ∧ ¬ ◇[R] (A · ≠ 0) () ∧ ¬ s () :=
  ⟨.univ, inferInstance, 0, fun _ ↦ False, postulates_full_iff.2 fun _ ⟨_, _, h⟩ ↦ h rfl,
    by simp, fun ⟨_, _, h⟩ ↦ h rfl, id⟩

end Karttunen1971b
