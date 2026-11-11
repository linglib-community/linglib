module

public import Studies.GroenendijkStokhof1984
public import Linglib.Data.Examples.Heim1994b
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.TFAE

/-!
# Heim (1994): Interrogative Semantics and Karttunen's Semantics for *know*

This file compares Karttunen's entry for *know* with a question complement, on which the agent
believes the intersection of the true answers and, if there are none, that there are none, with
Groenendijk and Stokhof's. Heim's generalization, on which the agent believes the answer set to be
what it is, [makes the first clause redundant](##Karttunen.simplifiedKnows_of_generalizedKnows) and
is Groenendijk and Stokhof's entry on the kernel of the question's intension: [their partition for
*which students called*](##ker_wh) when no two individuals call in the same worlds, but
[whether there are students](##Karttunen.ker_wh_identicalWithSelf) for a universally necessary
property. Structured answers [give their partition for every predicate](##ker_whichStructured), as
[living with one's actual spouse](##Spouses.verdict_row) requires.

## Implementation notes

* Belief is `SetRel.core` over the agent's doxastic alternatives, with no frame conditions; the
  agent is left implicit.
* Predicates are topical properties `E → Set W` over individuals, not the groups of the paper's
  plural semantics, and a restrictor is read at the world of evaluation.

## References

* [heim-1994]
* [karttunen-1977]
* [groenendijk-stokhof-1982]
* [groenendijk-stokhof-1984]
-/

@[expose] public section

namespace Heim1994b

open Question
open GroenendijkStokhof1984 (extension whichDeDicto who who_iff)
open scoped SetRel

variable {W E : Type*}

/-! ### Karttunen intensions

Karttunen's intension for *which students called*, (3), is `Karttunen1977.wh`, which reads the
common noun at the world of evaluation. -/

-- (6)
theorem Karttunen.wh_univ (C : E → Set W) :
    Karttunen1977.wh (fun _ ↦ Set.univ) C = trueAnswers (Set.range C) := by
  funext w
  simp [Karttunen1977.wh]

-- §3
theorem Karttunen.wh_mono {S P : E → Set W} (C : E → Set W) (h : ∀ x, S x ⊆ P x) (w : W) :
    Karttunen1977.wh S C w ⊆ Karttunen1977.wh P C w :=
  fun _ hq ↦ ⟨Set.image_mono (fun x hx ↦ h x hx) hq.1, hq.2⟩

/-! ### The answer in the two senses -/

/-- The answer in the first sense, (15), is the intersection of the answer set. -/
def ans₁ (q : W → Set (Set W)) (w : W) : Set W := ⋂₀ q w

/-- The answer in the second sense, (16), is the proposition that the answer in the first sense is
what it is. -/
def ans₂ (q : W → Set (Set W)) (w : W) : Set W := {v | ans₁ q v = ans₁ q w}

theorem ans₁_trueAnswers (H : Set (Set W)) : ans₁ (trueAnswers H) = weakAnswer H := rfl

-- §6
theorem ans₂_trueAnswers (H : Set (Set W)) (w : W) :
    ans₂ (trueAnswers H) w = strongAnswer H w := by
  rw [ans₂, ans₁_trueAnswers, strongAnswer_eq_cell, ← ker_weakAnswer]
  rfl

theorem self_mem_ans₁ {q : W → Set (Set W)} (hq : IsVeridical q) (w : W) : w ∈ ans₁ q w :=
  Set.mem_sInter.2 (hq w)

theorem ker_le_ker_ans₁ (q : W → Set (Set W)) : Setoid.ker q ≤ Setoid.ker (ans₁ q) :=
  Setoid.ker_le_ker_comp q Set.sInter

-- §6
theorem ans₂_subset_ans₁ {q : W → Set (Set W)} (hq : IsVeridical q) (w : W) :
    ans₂ q w ⊆ ans₁ q w :=
  fun v hv ↦ (show ans₁ q v = ans₁ q w from hv) ▸ self_mem_ans₁ hq v

/-! ### The entries for *know*

Karttunen's actual entry (5) is his meaning postulate `Karttunen1977.Knows`. -/

/-- On the simplified Karttunen analysis, (4), the agent believes the answer in the first sense. -/
def Karttunen.SimplifiedKnows (q : W → Set (Set W)) (w : W) (R : SetRel W W) : Prop :=
  w ∈ R.core (ans₁ q w)

/-- On the generalized Karttunen analysis, (9), the agent believes that the answer set is what it
is, for answer sets of any type, as §8 applies the entry to structured answers. -/
def GeneralizedKnows {α : Type*} (q : W → α) (w : W) (R : SetRel W W) : Prop :=
  w ∈ R.core {v | q v = q w}

variable {q : W → Set (Set W)} {w : W} {R : SetRel W W}

theorem generalizedKnows_iff_knows_ker {α : Type*} {q : W → α} :
    GeneralizedKnows q w R ↔ GroenendijkStokhof1984.Knows (Setoid.ker q) w R := Iff.rfl

-- §3
theorem Karttunen.simplifiedKnows_of_subset {q' : W → Set (Set W)} (h : q w ⊆ q' w)
    (hk : SimplifiedKnows q' w R) : SimplifiedKnows q w R :=
  SetRel.core_mono (Set.sInter_subset_sInter h) hk

/-- Under Karttunen's semantics for questions, an agent who believes the answer set to be what it
is believes the answer in the first sense, so that clause (i) of (8) is redundant (§4). -/
theorem Karttunen.simplifiedKnows_of_generalizedKnows (hq : IsVeridical q)
    (h : GeneralizedKnows q w R) : SimplifiedKnows q w R :=
  SetRel.core_mono (fun _ hv ↦ ans₂_subset_ans₁ hq w (ker_le_ker_ans₁ q hv)) h

-- (8), (9)
theorem Karttunen.knows_of_generalizedKnows (hq : IsVeridical q) (h : GeneralizedKnows q w R) :
    Karttunen1977.Knows q w R :=
  ⟨simplifiedKnows_of_generalizedKnows hq h, fun e ↦ by rwa [GeneralizedKnows, e] at h⟩

-- (5), (7)
theorem Karttunen.knows_iff_generalizedKnows_of_eq_empty (h : q w = ∅) :
    Karttunen1977.Knows q w R ↔ GeneralizedKnows q w R := by
  simp [Karttunen1977.Knows, GeneralizedKnows, h]

-- §4: the de re reading, quantifying in the common noun
theorem generalizedKnows_deRe (S C : E → Set W) (u : W) :
    GeneralizedKnows (trueAnswers (C '' extension S u)) w R ↔
      GroenendijkStokhof1984.Knows (GroenendijkStokhof1984.whichDeRe S C u) w R := by
  rw [GroenendijkStokhof1984.whichDeRe_eq_partition]
  rfl

/-! ### *Whether*-questions -/

-- (2), (12), footnote 11
theorem ker_trueAnswers_pair (φ : Set W) :
    Setoid.ker (trueAnswers {φ, φᶜ}) = Setoid.polar φ := by
  show partition {φ, φᶜ} = _
  ext v u
  rw [partition_iff, Setoid.polar_iff]
  simp [not_iff_not]

theorem trueAnswers_pair_nonempty (φ : Set W) (w : W) : (trueAnswers {φ, φᶜ} w).Nonempty := by
  by_cases h : w ∈ φ
  · exact ⟨φ, Set.mem_insert _ _, h⟩
  · exact ⟨φᶜ, Set.mem_insert_of_mem _ rfl, h⟩

-- §4, footnote 11
theorem knows_whether_tfae (φ : Set W) :
    [Karttunen.SimplifiedKnows (trueAnswers {φ, φᶜ}) w R,
      Karttunen1977.Knows (trueAnswers {φ, φᶜ}) w R,
      GeneralizedKnows (trueAnswers {φ, φᶜ}) w R,
      GroenendijkStokhof1984.Knows (Setoid.polar φ) w R].TFAE := by
  tfae_have 1 ↔ 2 :=
    (and_iff_left fun h ↦ absurd h (trueAnswers_pair_nonempty φ w).ne_empty).symm
  tfae_have 3 ↔ 4 := by rw [generalizedKnows_iff_knows_ker, ker_trueAnswers_pair]
  tfae_have 2 ↔ 4 := by
    rw [Karttunen1977.knows_pair_iff]
    simp [GroenendijkStokhof1984.Knows, iff_comm]
  tfae_finish

/-! ### Constituent questions -/

/-- When no two individuals call in the same worlds, the kernel of Karttunen's intension for
*which students called* is Groenendijk and Stokhof's de dicto partition, so that (10) is
(11) (§4). -/
theorem ker_wh {S C : E → Set W} (hC : Function.Injective C) :
    Setoid.ker (Karttunen1977.wh S C) = whichDeDicto S C := by
  rw [show Karttunen1977.wh S C = Set.image C ∘ extension (fun x ↦ S x ∩ C x) from
    funext (Karttunen1977.wh_eq_image · S C)]
  exact Setoid.ker_comp_of_injective _ hC.image_injective

theorem generalizedKnows_wh_iff {S C : E → Set W} (hC : Function.Injective C) :
    GeneralizedKnows (Karttunen1977.wh S C) w R ↔
      GroenendijkStokhof1984.Knows (whichDeDicto S C) w R := by
  rw [generalizedKnows_iff_knows_ker, ker_wh hC]

-- §6
theorem whichDeDicto_comm (S C : E → Set W) : whichDeDicto S C = whichDeDicto C S :=
  congrArg Setoid.ker (funext fun w ↦ Set.ext fun x ↦ by simp [Set.inter_comm])

-- §6
theorem ker_wh_comm {S C : E → Set W} (hS : Function.Injective S)
    (hC : Function.Injective C) :
    Setoid.ker (Karttunen1977.wh S C) = Setoid.ker (Karttunen1977.wh C S) := by
  rw [ker_wh hC, ker_wh hS, whichDeDicto_comm]

/-! ### Exhaustiveness (§2)

Bill and Mary are students in both worlds; Bill called in both and Mary only in `true`. At
`false` John believes that Bill called but is agnostic about Mary. -/

namespace Exhaustiveness

inductive Student | bill | mary

/-- Both are students in every world. -/
def student : Student → Set Bool := fun _ ↦ Set.univ

/-- Bill called in every world; Mary only in `true`. -/
def called : Student → Set Bool
  | .bill => Set.univ
  | .mary => {true}

/-- John's beliefs rule out no world. -/
def agnostic : SetRel Bool Bool := Set.univ

theorem called_injective : Function.Injective called := by
  rintro (_ | _) (_ | _) h <;> simp_all [called, Set.ext_iff]

theorem wh_false : Karttunen1977.wh student called false = {Set.univ} := by
  ext p
  rw [Karttunen1977.mem_wh_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨(_ | _), -, hc, rfl⟩
    · rfl
    · simp [called] at hc
  · rintro rfl
    exact ⟨.bill, trivial, trivial, rfl⟩

-- (1)
theorem karttunen_knows : Karttunen1977.Knows (Karttunen1977.wh student called) false agnostic := by
  refine ⟨?_, fun h ↦ absurd h (by rw [wh_false]; exact Set.singleton_ne_empty _)⟩
  rw [wh_false, Set.sInter_singleton, SetRel.core_univ]
  trivial

-- (1)
theorem not_knows_whichDeDicto :
    ¬ GroenendijkStokhof1984.Knows (whichDeDicto student called) false agnostic := fun h ↦ by
  have := who_iff.1 (h (show false ~[agnostic] true from trivial)) .mary
  simp [student, called] at this

-- (1)
theorem not_generalizedKnows :
    ¬ GeneralizedKnows (Karttunen1977.wh student called) false agnostic :=
  (generalizedKnows_wh_iff called_injective).not.2 not_knows_whichDeDicto

-- (1)
theorem verdict_row :
    (GeneralizedKnows (Karttunen1977.wh student called) false agnostic ↔
        Examples.ex1_exhaustive.verdict = some true) ∧
      ¬ (Karttunen1977.Knows (Karttunen1977.wh student called) false agnostic ↔
        Examples.ex1_exhaustive.verdict = some true) :=
  ⟨iff_of_false not_generalizedKnows (by decide), fun h ↦ absurd (h.1 karttunen_knows) (by decide)⟩

end Exhaustiveness

/-! ### De dicto readings (§3, §4)

Mary, the only individual, called in both worlds but is a student only in the actual world
`true`, and John is agnostic. Karttunen's actual entry gives the de dicto reading of (1) only at
`false`, where no student called. -/

namespace DeDicto

/-- Mary is a student only in `true`. -/
def student : Unit → Set Bool := fun _ ↦ {true}

/-- Mary called in every world. -/
def called : Unit → Set Bool := fun _ ↦ Set.univ

/-- John's beliefs rule out no world. -/
def agnostic : SetRel Bool Bool := Set.univ

theorem wh_true : Karttunen1977.wh student called true = {Set.univ} := by
  ext p
  simp [Karttunen1977.mem_wh_iff, student, called, eq_comm]

theorem wh_false : Karttunen1977.wh student called false = ∅ :=
  (Karttunen1977.wh_eq_empty_iff _ _ _).2 fun _ h ↦ absurd h (by simp [student])

theorem wh_who (v : Bool) : Karttunen1977.wh (fun _ ↦ Set.univ) called v = {Set.univ} := by
  ext p
  simp [Karttunen1977.mem_wh_iff, called]

-- (1)
theorem karttunen_knows : Karttunen1977.Knows (Karttunen1977.wh student called) true agnostic := by
  refine ⟨?_, fun h ↦ absurd h (by rw [wh_true]; exact Set.singleton_ne_empty _)⟩
  rw [wh_true, Set.sInter_singleton, SetRel.core_univ]
  trivial

-- (1)
theorem not_generalizedKnows : ¬ GeneralizedKnows (Karttunen1977.wh student called) true agnostic :=
  (generalizedKnows_wh_iff (Function.injective_of_subsingleton _)).not.2 fun h ↦ by
    have := who_iff.1 (h (show true ~[agnostic] false from trivial)) ()
    simp [student, called] at this

-- (6)
theorem generalizedKnows_who :
    GeneralizedKnows (Karttunen1977.wh (fun _ ↦ Set.univ) called) true agnostic :=
  fun v _ ↦ (wh_who v).trans (wh_who true).symm

-- (6)
theorem karttunen_knows_who :
    Karttunen1977.Knows (Karttunen1977.wh (fun _ ↦ Set.univ) called) false agnostic := by
  refine ⟨?_, fun h ↦ absurd h (by rw [wh_who]; exact Set.singleton_ne_empty _)⟩
  rw [wh_who, Set.sInter_singleton, SetRel.core_univ]
  trivial

-- (1), (6)
theorem not_karttunen_knows_of_no_student :
    ¬ Karttunen1977.Knows (Karttunen1977.wh student called) false agnostic := fun ⟨_, hii⟩ ↦
  have e : Karttunen1977.wh student called true = ∅ :=
    hii wh_false (show false ~[agnostic] true from trivial)
  Set.singleton_ne_empty _ (wh_true ▸ e)

-- (1), (6)
theorem verdict_rows :
    (GeneralizedKnows (Karttunen1977.wh student called) true agnostic ↔
        Examples.ex1_dedicto.verdict = some true) ∧
      ¬ (Karttunen1977.Knows (Karttunen1977.wh student called) true agnostic ↔
        Examples.ex1_dedicto.verdict = some true) ∧
      (GeneralizedKnows (Karttunen1977.wh (fun _ ↦ Set.univ) called) true agnostic ↔
        Examples.ex6.verdict = some true) :=
  ⟨iff_of_false not_generalizedKnows (by decide), fun h ↦ absurd (h.1 karttunen_knows) (by decide),
    iff_of_true generalizedKnows_who (by decide)⟩

end DeDicto

/-! ### Identity with oneself (§7) -/

/-- The universally necessary property, which every individual has in every world. -/
def identicalWithSelf : E → Set W := fun _ ↦ Set.univ

theorem Karttunen.wh_identicalWithSelf_of_exists {S : E → Set W} (h : ∃ x, w ∈ S x) :
    Karttunen1977.wh S identicalWithSelf w = {Set.univ} := by
  obtain ⟨x, hx⟩ := h
  rw [Karttunen1977.wh_eq_image]
  exact Set.Nonempty.image_const (s := {x | w ∈ S x ∧ w ∈ identicalWithSelf x}) ⟨x, hx, trivial⟩
    Set.univ

theorem Karttunen.wh_identicalWithSelf_of_not_exists {S : E → Set W} (h : ¬ ∃ x, w ∈ S x) :
    Karttunen1977.wh S identicalWithSelf w = ∅ :=
  (Karttunen1977.wh_eq_empty_iff w S _).2 fun x hx _ ↦ h ⟨x, hx⟩

-- (21), (22)
theorem whichDeDicto_identicalWithSelf (S : E → Set W) :
    whichDeDicto S identicalWithSelf = who S := by
  simp [whichDeDicto, identicalWithSelf]

/-- On the generalized analysis, knowing which students are identical with themselves is knowing
whether there are students, (23) (§7). -/
theorem Karttunen.ker_wh_identicalWithSelf (S : E → Set W) :
    Setoid.ker (Karttunen1977.wh S identicalWithSelf) = Setoid.polar {w | ∃ x, w ∈ S x} := by
  ext v w
  rw [Setoid.ker_def, Setoid.polar_iff]
  by_cases hv : ∃ x, v ∈ S x <;> by_cases hw : ∃ x, w ∈ S x <;>
    simp [hv, hw, wh_identicalWithSelf_of_exists, wh_identicalWithSelf_of_not_exists]

theorem ans₁_wh_identicalWithSelf (S : E → Set W) (w : W) :
    ans₁ (Karttunen1977.wh S identicalWithSelf) w = Set.univ :=
  Set.sInter_eq_univ.2 fun _ ⟨⟨_, _, h⟩, _⟩ ↦ h.symm

-- §6, §8
theorem ans₂_wh_identicalWithSelf (S : E → Set W) (w : W) :
    ans₂ (Karttunen1977.wh S identicalWithSelf) w = Set.univ := by
  simp [ans₂, ans₁_wh_identicalWithSelf]

/-! A world fixes the one student, if there is any. Where John believes that there is a student
but not which, the generalized analysis ascribes knowledge of (21) and Groenendijk and Stokhof's
does not; where he has no idea, neither does, though (21) ascribes trivial knowledge. -/

namespace Identity

inductive Student | bill | mary

/-- The student in `some x` is `x`; there is none in `none`. -/
def student : Student → Set (Option Student) := fun x ↦ {some x}

/-- John believes that there is a student, but not which. -/
def someStudent : SetRel (Option Student) (Option Student) := {p | p.2.isSome}

/-- John has no idea who, if anyone, is a student. -/
def agnostic : SetRel (Option Student) (Option Student) := Set.univ

-- (21)
theorem generalizedKnows_someStudent :
    GeneralizedKnows (Karttunen1977.wh student identicalWithSelf) (some .bill) someStudent := by
  rw [generalizedKnows_iff_knows_ker, Karttunen.ker_wh_identicalWithSelf]
  rintro (_ | x) h
  · simp [someStudent] at h
  · simp [student]

-- (21), (22)
theorem not_knows_whichDeDicto {R : SetRel (Option Student) (Option Student)}
    (h : (some .bill, some .mary) ∈ R) :
    ¬ GroenendijkStokhof1984.Knows (whichDeDicto student identicalWithSelf) (some .bill) R :=
  fun hk ↦ by
    have := who_iff.1 (hk h) .mary
    simp [student, identicalWithSelf] at this

-- (21)
theorem not_generalizedKnows_agnostic :
    ¬ GeneralizedKnows (Karttunen1977.wh student identicalWithSelf) (some .bill) agnostic := by
  rw [generalizedKnows_iff_knows_ker, Karttunen.ker_wh_identicalWithSelf]
  intro h
  have := h (show some .bill ~[agnostic] none from trivial)
  simp [student] at this

-- (21)
theorem verdict_row :
    ¬ (GeneralizedKnows (Karttunen1977.wh student identicalWithSelf) (some .bill) agnostic ↔
        Examples.ex21.verdict = some true) ∧
      ¬ (GroenendijkStokhof1984.Knows (whichDeDicto student identicalWithSelf) (some .bill)
          agnostic ↔ Examples.ex21.verdict = some true) :=
  ⟨fun h ↦ not_generalizedKnows_agnostic (h.2 (by decide)),
    fun h ↦ not_knows_whichDeDicto (R := agnostic) trivial (h.2 (by decide))⟩

end Identity

/-! ### Living with one's actual spouse (§7)

Bill is married to Sue, and the proposition that either lives with their actual spouse is the
proposition that they live together. A world records whether Sue is a student and whether the
couple live together; in the actual world both hold, and John's one false belief is that Sue is
not a student. -/

namespace Spouses

inductive Person | bill | sue

/-- A world records whether Sue is a student and whether Bill and Sue live together. -/
abbrev World := Bool × Bool

/-- Bill is a student everywhere; Sue where the first coordinate holds. -/
def student : Person → Set World
  | .bill => Set.univ
  | .sue => {w | w.1 = true}

/-- Each lives with their actual spouse exactly where they live together. -/
def livesWithSpouse : Person → Set World := fun _ ↦ {w | w.2 = true}

/-- The actual world, where Sue is a student and the couple live together. -/
def actual : World := (true, true)

/-- John's only doxastic alternative is the world where Sue is not a student and they live
together. -/
def john : SetRel World World := {p | p.2 = (false, true)}

theorem not_injective_livesWithSpouse : ¬ Function.Injective livesWithSpouse :=
  fun h ↦ Person.noConfusion (h (a₁ := .bill) (a₂ := .sue) rfl)

theorem extension_actual :
    extension (fun x ↦ student x ∩ livesWithSpouse x) actual = Set.univ := by
  ext x
  cases x <;> simp [student, livesWithSpouse, actual]

theorem extension_alt :
    extension (fun x ↦ student x ∩ livesWithSpouse x) (false, true) = {.bill} := by
  ext x
  cases x <;> simp [student, livesWithSpouse]

-- (26)
theorem wh_eq :
    Karttunen1977.wh student livesWithSpouse (false, true) =
      Karttunen1977.wh student livesWithSpouse actual := by
  ext p
  simp only [Karttunen1977.mem_wh_iff]
  exact ⟨fun ⟨_, _, _, h⟩ ↦ ⟨.bill, trivial, rfl, h⟩, fun ⟨_, _, _, h⟩ ↦ ⟨.bill, trivial, rfl, h⟩⟩

-- (24), (26)
theorem generalizedKnows_holds :
    GeneralizedKnows (Karttunen1977.wh student livesWithSpouse) actual john := by
  rintro v (rfl : v = (false, true))
  exact wh_eq

-- (24), (25)
theorem not_knows_whichDeDicto :
    ¬ GroenendijkStokhof1984.Knows (whichDeDicto student livesWithSpouse) actual john := by
  intro h
  have := who_iff.1 (h (show actual ~[john] ((false : Bool), (true : Bool)) from rfl)) .sue
  simp [student, livesWithSpouse, actual] at this

end Spouses

/-! ### Which particles had not been discovered (footnotes 8 and 9) -/

/-- Karttunen's rejected remedy for exhaustiveness, (i) of footnote 8, adds the proposition that
`x` did not call for each student `x` who did not call. -/
def Karttunen.whichWithNegations (S C : E → Set W) (w : W) : Set (Set W) :=
  Karttunen1977.wh S C w ∪ Karttunen1977.wh S (fun x ↦ (C x)ᶜ) w

-- footnote 8
theorem Karttunen.whichWithNegations_compl (S C : E → Set W) :
    whichWithNegations S (fun x ↦ (C x)ᶜ) = whichWithNegations S C := by
  funext w
  simp only [whichWithNegations, compl_compl]
  exact Set.union_comm _ _

-- footnote 8
theorem Karttunen.ans₁_whichWithNegations (S C : E → Set W) (w : W) :
    ans₁ (whichWithNegations S C) w = strongAnswer (C '' {x | w ∈ S x}) w := by
  rw [← weakAnswer_union_image_compl, Set.image_image, weakAnswer, ans₁, whichWithNegations,
    Karttunen1977.wh, Karttunen1977.wh]
  congr 1
  ext p
  simp [or_and_right]

/-! Of the particles `x` and `y`, only `x` had been discovered by 1978; Feynman's beliefs are
compatible with the actual world `true` and with `false`, where `x` is the only particle. -/

namespace Feynman

inductive Particle | x | y

/-- `x` is an elementary particle in both worlds, `y` only in `true`. -/
def particle : Particle → Set Bool
  | .x => Set.univ
  | .y => {true}

/-- `x` had been discovered by 1978 in both worlds, `y` in neither. -/
def discovered : Particle → Set Bool
  | .x => Set.univ
  | .y => ∅

/-- Both worlds are compatible with Feynman's beliefs. -/
def feynman : SetRel Bool Bool := Set.univ

theorem discovered_injective : Function.Injective discovered := by
  rintro (_ | _) (_ | _) h <;> simp_all [discovered, Set.ext_iff]

theorem wh_discovered (v : Bool) : Karttunen1977.wh particle discovered v = {Set.univ} := by
  ext p
  rw [Karttunen1977.mem_wh_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨(_ | _), -, hd, rfl⟩
    · rfl
    · simp [discovered] at hd
  · rintro rfl
    exact ⟨.x, trivial, trivial, rfl⟩

-- footnote 9
theorem generalizedKnows_discovered :
    GeneralizedKnows (Karttunen1977.wh particle discovered) true feynman :=
  fun v _ ↦ (wh_discovered v).trans (wh_discovered true).symm

-- footnote 9
theorem not_generalizedKnows_undiscovered :
    ¬ GeneralizedKnows (Karttunen1977.wh particle fun z ↦ (discovered z)ᶜ) true feynman := by
  intro h
  have e := h (show true ~[feynman] false from trivial)
  have hy : (discovered .y)ᶜ ∈ Karttunen1977.wh particle (fun z ↦ (discovered z)ᶜ) true :=
    (Karttunen1977.mem_wh_iff _ _ _).2 ⟨.y, rfl, Set.notMem_empty true, rfl⟩
  rw [← show Karttunen1977.wh particle (fun z ↦ (discovered z)ᶜ) false = _ from e] at hy
  obtain ⟨(_ | _), hx, hd, -⟩ := (Karttunen1977.mem_wh_iff _ _ _).1 hy <;>
    simp [particle, discovered] at hx hd

-- footnote 9
theorem knows_discovered_not_undiscovered :
    GroenendijkStokhof1984.Knows (whichDeDicto particle discovered) true feynman ∧
      ¬ GroenendijkStokhof1984.Knows (whichDeDicto particle fun z ↦ (discovered z)ᶜ) true
        feynman :=
  ⟨(generalizedKnows_wh_iff discovered_injective).1 generalizedKnows_discovered,
    (generalizedKnows_wh_iff (compl_injective.comp discovered_injective)).not.1
      not_generalizedKnows_undiscovered⟩

-- footnote 8
theorem verdict_row :
    (GeneralizedKnows (Karttunen1977.wh particle discovered) true feynman ∧
          ¬ GeneralizedKnows (Karttunen1977.wh particle fun z ↦ (discovered z)ᶜ) true feynman ↔
        Examples.fn8ii.verdict = some true) ∧
      ∀ K : (Bool → Set (Set Bool)) → Prop,
        ¬ (K (Karttunen.whichWithNegations particle discovered) ∧
            ¬ K (Karttunen.whichWithNegations particle fun z ↦ (discovered z)ᶜ) ↔
          Examples.fn8ii.verdict = some true) := by
  refine ⟨iff_of_true ⟨generalizedKnows_discovered, not_generalizedKnows_undiscovered⟩ (by decide),
    fun K h ↦ ?_⟩
  rw [Karttunen.whichWithNegations_compl] at h
  exact (h.2 (by decide)).2 (h.2 (by decide)).1

end Feynman

/-! ### Structured answers (§8) -/

/-- The structured intension, (27), pairs each student who called with the property of
calling. -/
def whichStructured (S C : E → Set W) (w : W) : Set (E × (E → Set W)) :=
  (fun x ↦ (x, C)) '' extension (fun x ↦ S x ∩ C x) w

/-- Since pairing each individual with the property is injective whatever the property, the
kernel of the structured intension is Groenendijk and Stokhof's de dicto partition for every
predicate, so that (28) is (11) (§8). -/
theorem ker_whichStructured (S C : E → Set W) :
    Setoid.ker (whichStructured S C) = whichDeDicto S C :=
  Setoid.ker_comp_of_injective (extension _) (Prod.mk_left_injective C).image_injective

theorem generalizedKnows_whichStructured_iff {S C : E → Set W} :
    GeneralizedKnows (whichStructured S C) w R ↔
      GroenendijkStokhof1984.Knows (whichDeDicto S C) w R := by
  rw [generalizedKnows_iff_knows_ker, ker_whichStructured]

-- §8
theorem Karttunen.wh_eq_image_whichStructured (S C : E → Set W) (w : W) :
    Karttunen1977.wh S C w = (fun p : E × (E → Set W) ↦ p.2 p.1) '' whichStructured S C w := by
  rw [Karttunen1977.wh_eq_image, whichStructured, Set.image_image]
  rfl

-- (21)
theorem Identity.not_generalizedKnows_structured :
    ¬ GeneralizedKnows (whichStructured Identity.student identicalWithSelf) (some .bill)
      Identity.someStudent :=
  generalizedKnows_whichStructured_iff.not.2 (Identity.not_knows_whichDeDicto rfl)

-- §8
theorem Spouses.whichStructured_ne :
    whichStructured Spouses.student Spouses.livesWithSpouse (false, true) ≠
      whichStructured Spouses.student Spouses.livesWithSpouse Spouses.actual := by
  intro h
  have := congrArg ((Spouses.Person.sue, Spouses.livesWithSpouse) ∈ ·) h
  simp [whichStructured, Spouses.extension_actual, Spouses.extension_alt] at this

/-- Living with one's actual spouse separates the analyses: John, who believes Sue not to be a
student, knows which students live with their actual spouses on the generalized analysis, but not
on Groenendijk and Stokhof's or with structured answers, and the paper judges (24) false (§7,
§8). -/
theorem Spouses.verdict_row :
    ¬ (GeneralizedKnows (Karttunen1977.wh Spouses.student Spouses.livesWithSpouse) Spouses.actual
        Spouses.john ↔ Examples.ex24.verdict = some true) ∧
      (GroenendijkStokhof1984.Knows (whichDeDicto Spouses.student Spouses.livesWithSpouse)
          Spouses.actual Spouses.john ↔ Examples.ex24.verdict = some true) ∧
      (GeneralizedKnows (whichStructured Spouses.student Spouses.livesWithSpouse) Spouses.actual
          Spouses.john ↔ Examples.ex24.verdict = some true) :=
  ⟨fun h ↦ absurd (h.1 Spouses.generalizedKnows_holds) (by decide),
    iff_of_false Spouses.not_knows_whichDeDicto (by decide),
    iff_of_false (generalizedKnows_whichStructured_iff.not.2 Spouses.not_knows_whichDeDicto)
      (by decide)⟩

end Heim1994b
