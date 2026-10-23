module

public import Studies.GroenendijkStokhof1984
public import Linglib.Data.Examples.Heim1994b
public import Mathlib.Tactic.TFAE

/-!
# Heim (1994): Interrogative Semantics and Karttunen's Semantics for *know*

This file formalizes [heim-1994]. A [karttunen-1977] intension assigns each world a set of
true answers; `IsKarttunen` is the property that every member of the answer set at `w` holds
at `w`, true of the substrate's Karttunen denotation (`isKarttunen_trueAnswers`). Karttunen's
simplified entry for *know* (4) has the agent believe the answer in Heim's first sense (15),
the intersection of the true answers; his actual entry (5) adds that an empty answer set be
believed empty; and the generalized entry (9) has the agent believe that the answer set is
what it is, which makes the first clause redundant
(`Karttunen.simplifiedKnow_of_generalizedKnow`). Believing the answer set to be what it is is
believing the cell of the kernel of the intension (`generalizedKnow_iff_know_ker`), so the
generalized analysis is [groenendijk-stokhof-1982]'s entry (14) on the kernel question; for
*whether*-questions all four entries coincide (`knows_whether_tfae`).

The comparison for constituent questions rests on one observation: the which-intension (3)
is the image of the extension of *student who called* under the propositional concept `C`,
while Groenendijk and Stokhof's (13) is the kernel of the extension map, so the two agree
exactly when `C` is injective — the paper's premise that no two individuals call in exactly
the same possible worlds (`ker_which`). The two divergences of §7 are the two ways
injectivity fails: identity with oneself (21) is constant, reducing the generalized analysis
to knowing whether there are students (`Karttunen.ker_which_identicalWithSelf`), and living
with one's actual spouse (24) identifies Bill with Sue (`Spouses`). Structured propositions
(27) restore the agreement for every predicate, since tagging each individual with the
property is injective outright (`ker_whichStructured`), while the unstructured answers stay
recoverable (`Karttunen.which_eq_image_whichStructured`) though not conversely
(`Spouses.whichStructured_ne`). The answer in the second sense (16) entails the answer in
the first (`ans₂_subset_ans₁`), and on a Hamblin set it is the substrate's strongly
exhaustive answer (`ans₂_trueAnswers`).

## Implementation notes

Belief is `w ∈ (Dox x).core p` over doxastic alternatives `Dox : E → SetRel W W`, with no
frame conditions, as the paper assumes none. Groenendijk and Stokhof's entries (13) and (14) are
`GroenendijkStokhof1984.whichDeDicto` and `GroenendijkStokhof1984.Knows`, their 1982 paper
being chapter II of the dissertation. Predicates are topical properties `E → Set W`,
the substrate's `trueAnswers_range` shape, so the restrictorless *who called* (6) is the
Karttunen denotation of `Set.range C` (`Karttunen.which_univ`) and the superset argument of
§3 is `Karttunen.which_mono`. `E` ranges over individuals, not the groups of the paper's
footnote on plurals. `identicalWithSelf` is the universally necessary property, which every
individual has in every world. The scenarios are the paper's own two-world models: in
`Spouses` the worlds record whether Sue is a student and whether the couples live together,
and John holds the single false belief that Sue is not a student (§7). The ambiguity of
*answer* in (17)–(20) is a row. The Feynman sentence of §4's footnote is not modelled; the
general negation case is `George2011`.

## TODO

* §6 identifies the proposition of (9) with the answer in the second sense (16), but in
  general only `Setoid.ker q ≤ Setoid.ker (ans₁ q)` holds (`ker_le_ker_ans₁`): on identity
  with oneself, `ans₂` is trivial while the kernel of the intension asks whether there are
  students.

## References

* [heim-1994]
* [karttunen-1977]
* [groenendijk-stokhof-1982]
* [groenendijk-stokhof-1984]
-/

@[expose] public section

namespace Heim1994b

open Question

variable {W E : Type*}

/-! ### Karttunen intensions -/

/-- An interrogative intension is Karttunen's, in the sense of [karttunen-1977], when each
member of its answer set at `w` is true at `w`; the redundancy proof of §4 rests on this. -/
def IsKarttunen (q : W → Set (Set W)) : Prop := ∀ w, ∀ p ∈ q w, w ∈ p

theorem isKarttunen_trueAnswers (H : Set (Set W)) : IsKarttunen (trueAnswers H) :=
  fun _ _ h ↦ h.2

/-- The intension of "whether φ" is the true one of `φ` and its negation, (2). -/
def Karttunen.whether (φ : Set W) : W → Set (Set W) := trueAnswers {φ, φᶜ}

theorem Karttunen.whether_nonempty (φ : Set W) (w : W) : (whether φ w).Nonempty := by
  by_cases h : w ∈ φ
  · exact ⟨φ, Set.mem_insert _ _, h⟩
  · exact ⟨φᶜ, Set.mem_insert_of_mem _ rfl, h⟩

/-- The students who called at `w`, the extension behind the colon in (3) and (13). -/
def extension (S C : E → Set W) (w : W) : Set E := {x | w ∈ S x ∩ C x}

/-- The intension of "which students called", (3), gives the propositions that `x` called for
the students `x` who called, the image of the extension under the propositional concept. -/
def Karttunen.which (S C : E → Set W) (w : W) : Set (Set W) := C '' extension S C w

theorem Karttunen.isKarttunen_which (S C : E → Set W) : IsKarttunen (which S C) := by
  rintro w p ⟨x, hx, rfl⟩
  exact hx.2

/-- Without a restrictor, "who called", (6), is the Karttunen denotation of the Hamblin set
of the propositions that each individual called. -/
theorem Karttunen.which_univ (C : E → Set W) :
    which (fun _ ↦ Set.univ) C = trueAnswers (Set.range C) := by
  funext w
  simp [which, extension, trueAnswers_range]

/-- Widening the restrictor widens the answer set, the superset argument of §3. -/
theorem Karttunen.which_mono {S P : E → Set W} (C : E → Set W) (h : ∀ x, S x ⊆ P x) (w : W) :
    which S C w ⊆ which P C w :=
  Set.image_mono fun _ hx ↦ ⟨h _ hx.1, hx.2⟩

/-! ### The answer in the two senses -/

/-- The answer in the first sense, (15), is the intersection of the true answers. -/
def ans₁ (q : W → Set (Set W)) (w : W) : Set W := ⋂₀ q w

/-- The answer in the second sense, (16), is the proposition that the answer in the first
sense is what it is. -/
def ans₂ (q : W → Set (Set W)) (w : W) : Set W := {w' | ans₁ q w' = ans₁ q w}

theorem ans₁_trueAnswers (H : Set (Set W)) : ans₁ (trueAnswers H) = weakAnswer H := rfl

theorem ans₂_trueAnswers (H : Set (Set W)) (w : W) :
    ans₂ (trueAnswers H) w = strongAnswer H w := by
  rw [strongAnswer_eq_cell, ← ker_weakAnswer]
  rfl

theorem IsKarttunen.self_mem_ans₁ {q : W → Set (Set W)} (hq : IsKarttunen q) (w : W) :
    w ∈ ans₁ q w :=
  Set.mem_sInter.2 (hq w)

theorem ker_le_ker_ans₁ (q : W → Set (Set W)) : Setoid.ker q ≤ Setoid.ker (ans₁ q) :=
  Setoid.ker_le_ker_comp q Set.sInter

/-- The answer in the second sense always entails the answer in the first (§6). -/
theorem ans₂_subset_ans₁ {q : W → Set (Set W)} (hq : IsKarttunen q) (w : W) :
    ans₂ q w ⊆ ans₁ q w :=
  fun v hv ↦ (show ans₁ q v = ans₁ q w from hv) ▸ hq.self_mem_ans₁ v

/-! ### The entries for *know* -/

variable (Dox : E → SetRel W W) (x : E) (w : W)

/-- On the simplified Karttunen analysis, (4), `x` believes the answer in the first sense. -/
def Karttunen.simplifiedKnow (q : W → Set (Set W)) : Prop := w ∈ (Dox x).core (ans₁ q w)

/-- On the actual Karttunen analysis, (5), `x` believes the answer as in (4) and, if the
answer set is empty, believes that it is empty. -/
def Karttunen.know (q : W → Set (Set W)) : Prop :=
  simplifiedKnow Dox x w q ∧ (q w = ∅ → w ∈ (Dox x).core {w' | q w' = ∅})

/-- On the generalized Karttunen analysis, (9), `x` believes that the answer set is what it
is, for answer sets of any type, as §8 applies the same entry to structured intensions. -/
def generalizedKnow {α : Type*} (q : W → α) : Prop := w ∈ (Dox x).core {w' | q w' = q w}

variable {Dox x w}

theorem generalizedKnow_iff_know_ker {α : Type*} {q : W → α} :
    generalizedKnow Dox x w q ↔ GroenendijkStokhof1984.Knows (Dox x) (Setoid.ker q) w := Iff.rfl

theorem Karttunen.simplifiedKnow_trueAnswers (H : Set (Set W)) :
    simplifiedKnow Dox x w (trueAnswers H) ↔ KnowsAnswer H w (Dox x) := Iff.rfl

theorem generalizedKnow_trueAnswers (H : Set (Set W)) :
    generalizedKnow Dox x w (trueAnswers H) ↔
      GroenendijkStokhof1984.Knows (Dox x) (partition H) w := Iff.rfl

/-- Knowing a bigger answer set is knowing the smaller one (§3). -/
theorem Karttunen.simplifiedKnow_of_subset {q q' : W → Set (Set W)} (h : q w ⊆ q' w)
    (hk : simplifiedKnow Dox x w q') : simplifiedKnow Dox x w q :=
  SetRel.core_mono (Set.sInter_subset_sInter h) hk

/-- Clause (i) of (8) is redundant given clause (ii), since an alternative with the same
answer set lies in the answer in the second sense, hence in the first (§4). -/
theorem Karttunen.simplifiedKnow_of_generalizedKnow {q : W → Set (Set W)}
    (hq : IsKarttunen q) (h : generalizedKnow Dox x w q) : simplifiedKnow Dox x w q :=
  SetRel.core_mono (fun _ hv ↦ ans₂_subset_ans₁ hq w (ker_le_ker_ans₁ q hv)) h

/-- Hence (8) and (9) are equivalent, and the generalized analysis implies the actual one. -/
theorem Karttunen.know_of_generalizedKnow {q : W → Set (Set W)} (hq : IsKarttunen q)
    (h : generalizedKnow Dox x w q) : know Dox x w q :=
  ⟨simplifiedKnow_of_generalizedKnow hq h, fun e ↦ by unfold generalizedKnow at h; rwa [e] at h⟩

/-- With an empty answer set the actual analysis is the generalized one, (7). -/
theorem Karttunen.know_iff_generalizedKnow_of_eq_empty {q : W → Set (Set W)} (h : q w = ∅) :
    know Dox x w q ↔ generalizedKnow Dox x w q := by
  simp [know, simplifiedKnow, generalizedKnow, ans₁, h]

/-! ### *Whether*-questions -/

/-- Karttunen's *whether* has [groenendijk-stokhof-1982]'s (12) as its kernel. -/
theorem Karttunen.ker_whether (φ : Set W) : Setoid.ker (whether φ) = Setoid.polar φ := by
  show partition {φ, φᶜ} = _
  ext v w
  rw [partition_iff, Setoid.polar_iff]
  simp [not_iff_not]

theorem ans₁_whether (φ : Set W) (w : W) :
    ans₁ (Karttunen.whether φ) w = (Setoid.polar φ).cell w := by
  show weakAnswer {φ, φᶜ} w = _
  ext v
  simp only [mem_weakAnswer, Setoid.mem_cell, Setoid.polar_iff, Set.forall_mem_insert,
    Set.forall_mem_singleton, Set.mem_compl_iff]
  by_cases h : w ∈ φ <;> simp [h]

/-- The simplified, actual, and generalized analyses and Groenendijk and Stokhof's all agree
on "NP knows whether φ", the proof §4 leaves to the reader and the paper's footnote 11. -/
theorem knows_whether_tfae (φ : Set W) :
    [Karttunen.simplifiedKnow Dox x w (Karttunen.whether φ),
      Karttunen.know Dox x w (Karttunen.whether φ),
      generalizedKnow Dox x w (Karttunen.whether φ),
      GroenendijkStokhof1984.Knows (Dox x) (Setoid.polar φ) w].TFAE := by
  tfae_have 1 ↔ 2 :=
    (and_iff_left fun h ↦ absurd h (Karttunen.whether_nonempty φ w).ne_empty).symm
  tfae_have 3 ↔ 4 := by rw [generalizedKnow_iff_know_ker, Karttunen.ker_whether]
  tfae_have 1 ↔ 4 := by rw [Karttunen.simplifiedKnow, ans₁_whether]; rfl
  tfae_finish

/-! ### Constituent questions: Karttunen against Groenendijk and Stokhof -/

/-- Groenendijk and Stokhof's partition by which students called, (13), is the kernel of the
extension map. -/
theorem whichDeDicto_eq_ker (S C : E → Set W) :
    GroenendijkStokhof1984.whichDeDicto S C = Setoid.ker (extension S C) := rfl

/-- When no two individuals call in exactly the same possible worlds, the kernel of
Karttunen's intension is Groenendijk and Stokhof's partition, so that (10) is (11). -/
theorem ker_which {S C : E → Set W} (hC : Function.Injective C) :
    Setoid.ker (Karttunen.which S C) = GroenendijkStokhof1984.whichDeDicto S C :=
  Setoid.ker_comp_of_injective (extension S C) hC.image_injective

theorem generalizedKnow_which_iff {S C : E → Set W} (hC : Function.Injective C) :
    generalizedKnow Dox x w (Karttunen.which S C) ↔
      GroenendijkStokhof1984.Knows (Dox x) (GroenendijkStokhof1984.whichDeDicto S C) w := by
  rw [generalizedKnow_iff_know_ker, ker_which hC]

/-- "Which A are B" and "which B are A" raise the same partition, §6's neutralization. -/
theorem whichDeDicto_comm (S C : E → Set W) :
    GroenendijkStokhof1984.whichDeDicto S C = GroenendijkStokhof1984.whichDeDicto C S :=
  congrArg Setoid.ker (funext fun w ↦ Set.ext fun x ↦ by simp [Set.inter_comm])

/-! ### The exhaustiveness scenario (§2)

Bill and Mary, both of them people; Bill called in every world and Mary only in the world
`true`. In the world `false`, where Mary did not call, John is agnostic. -/

namespace Exhaustiveness

inductive Student | bill | mary

/-- Bill called in every world; Mary only in `true`. -/
def called : Student → Set Bool
  | .bill => Set.univ
  | .mary => {true}

/-- John's doxastic alternatives at every world are all the worlds. -/
def agnostic : Unit → SetRel Bool Bool := fun _ ↦ Set.univ

theorem which_false : Karttunen.which (fun _ ↦ Set.univ) called false = {Set.univ} := by
  ext p
  simp only [Karttunen.which, extension, Set.mem_image, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    cases x
    · rfl
    · simp [called] at hx
  · rintro rfl
    exact ⟨.bill, by simp [called], rfl⟩

theorem singleton_true_mem_which_true :
    ({true} : Set Bool) ∈ Karttunen.which (fun _ ↦ Set.univ) called true :=
  ⟨.mary, by simp [called, extension], rfl⟩

/-- The actual analysis makes (1) true at `false`, where Mary did not call, since the only
true answer, that Bill called, is believed, and the answer set is not empty. -/
theorem karttunen_know :
    Karttunen.know agnostic () false (Karttunen.which (fun _ ↦ Set.univ) called) := by
  refine ⟨?_, fun h ↦ absurd h (by rw [which_false]; exact Set.singleton_ne_empty _)⟩
  show false ∈ (agnostic ()).core (⋂₀ Karttunen.which (fun _ ↦ Set.univ) called false)
  rw [which_false, Set.sInter_singleton, SetRel.core_univ]
  trivial

/-- The generalized analysis makes (1) false there, since in the alternative `true` Mary
called too, so the answer set differs. -/
theorem not_generalizedKnow :
    ¬ generalizedKnow agnostic () false (Karttunen.which (fun _ ↦ Set.univ) called) := by
  intro h
  have := h (show (false, true) ∈ agnostic () from trivial)
  simp only [Set.mem_ofPred_eq, which_false] at this
  have h1 : ({true} : Set Bool) = Set.univ :=
    Set.mem_singleton_iff.1 (this ▸ singleton_true_mem_which_true)
  exact absurd (Set.ext_iff.1 h1 false) (by simp)

theorem not_groenendijkStokhof_know :
    ¬ GroenendijkStokhof1984.Knows (agnostic ())
      (GroenendijkStokhof1984.whichDeDicto (fun _ ↦ Set.univ) called) false := by
  intro h
  have := h (show (false, true) ∈ agnostic () from trivial)
  simp only [Setoid.mem_cell, whichDeDicto_eq_ker, Setoid.ker_def] at this
  have := congrArg (Student.mary ∈ ·) this
  simp [extension, called] at this

end Exhaustiveness

/-! ### The de dicto scenario (§3–§4)

Mary, the sole individual, called in every world but is a student only in the actual world
`true`; John is agnostic. The generalized analysis delivers the de dicto reading: (1) comes
out false because John does not know that Mary is a student, while Karttunen's entries make
it true. At the other world, where there are no student callers, Karttunen's actual entry
correctly blocks the entailment from "John knows who called" (6) to (1). -/

namespace DeDicto

/-- Mary is a student only in `true`. -/
def student : Unit → Set Bool := fun _ ↦ {true}

/-- Mary called in every world. -/
def called : Unit → Set Bool := fun _ ↦ Set.univ

def agnostic : Unit → SetRel Bool Bool := fun _ ↦ Set.univ

/-- Karttunen's actual analysis makes (1) true at `true`, where the one true answer is
believed. -/
theorem karttunen_know : Karttunen.know agnostic () true (Karttunen.which student called) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · intro v _
    simp [ans₁, Karttunen.which, extension, student, called]
  · exact absurd h (Set.Nonempty.ne_empty ⟨_, (), by simp [student, called, extension], rfl⟩)

/-- The generalized analysis makes (1) false, since in the alternative `false` Mary is not a
student, so the answer set differs. -/
theorem not_generalizedKnow :
    ¬ generalizedKnow agnostic () true (Karttunen.which student called) := by
  intro h
  have e : Karttunen.which student called false = Karttunen.which student called true :=
    h (show (true, false) ∈ agnostic () from trivial)
  have h1 : (Set.univ : Set Bool) ∈ Karttunen.which student called true :=
    ⟨(), by simp [extension, student, called], rfl⟩
  rw [← e] at h1
  simp [Karttunen.which, extension, student] at h1

/-- (6) "John knows who called" stays true on the generalized analysis. -/
theorem generalizedKnow_who :
    generalizedKnow agnostic () true (Karttunen.which (fun _ ↦ Set.univ) called) := by
  intro v _
  simp [Karttunen.which, extension, called]

/-- At `false` there are callers but no student callers, and (6) is true on the actual
analysis. -/
theorem karttunen_know_who :
    Karttunen.know agnostic () false (Karttunen.which (fun _ ↦ Set.univ) called) := by
  refine ⟨fun v _ ↦ ?_, fun h ↦ ?_⟩
  · simp [ans₁, Karttunen.which, extension, called]
  · exact absurd h (Set.Nonempty.ne_empty ⟨_, (), by simp [called, extension], rfl⟩)

/-- But (1) is false there on the actual analysis, since the answer set is empty and John
does not believe it empty, so (6) does not entail (1). -/
theorem not_karttunen_know_of_no_student :
    ¬ Karttunen.know agnostic () false (Karttunen.which student called) := by
  rintro ⟨-, hii⟩
  have h0 : Karttunen.which student called false = ∅ := by
    simp [Karttunen.which, extension, student]
  have e : Karttunen.which student called true = ∅ :=
    hii h0 (show (false, true) ∈ agnostic () from trivial)
  have h1 : (Set.univ : Set Bool) ∈ Karttunen.which student called true :=
    ⟨(), by simp [extension, student, called], rfl⟩
  rw [e] at h1
  exact Set.notMem_empty _ h1

end DeDicto

/-! ### Non-equivalence: identity with oneself (§7) -/

/-- The universally necessary property, which every individual has in every world. -/
def identicalWithSelf : E → Set W := fun _ ↦ Set.univ

theorem extension_identicalWithSelf (S : E → Set W) (w : W) :
    extension S identicalWithSelf w = {x | w ∈ S x} := by
  simp [extension, identicalWithSelf]

theorem Karttunen.which_identicalWithSelf_of_exists {S : E → Set W} {w : W}
    (h : ∃ x, w ∈ S x) : which S identicalWithSelf w = {Set.univ} := by
  rw [which, extension_identicalWithSelf]
  exact Set.Nonempty.image_const h _

theorem Karttunen.which_identicalWithSelf_of_not_exists {S : E → Set W} {w : W}
    (h : ¬ ∃ x, w ∈ S x) : which S identicalWithSelf w = ∅ := by
  rw [which, extension_identicalWithSelf, Set.image_eq_empty]
  exact Set.eq_empty_of_forall_notMem fun x hx ↦ h ⟨x, hx⟩

/-- Groenendijk and Stokhof read (21) as knowing what students there are, (22). -/
theorem whichDeDicto_identicalWithSelf (S : E → Set W) :
    GroenendijkStokhof1984.whichDeDicto S identicalWithSelf = Setoid.ker fun w ↦ {x | w ∈ S x} :=
  congrArg Setoid.ker (funext (extension_identicalWithSelf S))

/-- The generalized analysis reads (21) as knowing whether there are students, (23). -/
theorem Karttunen.ker_which_identicalWithSelf (S : E → Set W) :
    Setoid.ker (which S identicalWithSelf) = Setoid.polar {w | ∃ x, w ∈ S x} := by
  ext v w
  rw [Setoid.ker_def, Setoid.polar_iff]
  by_cases hv : ∃ x, v ∈ S x <;> by_cases hw : ∃ x, w ∈ S x <;>
    simp [hv, hw, which_identicalWithSelf_of_exists, which_identicalWithSelf_of_not_exists]

/-! Two worlds with one student each, Bill in `true` and Mary in `false`; John agnostic.
There are students either way, so the generalized analysis ascribes knowledge of (21) while
Groenendijk and Stokhof's does not. -/

namespace Identity

inductive Student | bill | mary

/-- Bill is the student in `true`, Mary in `false`. -/
def student : Student → Set Bool
  | .bill => {true}
  | .mary => {false}

def agnostic : Unit → SetRel Bool Bool := fun _ ↦ Set.univ

theorem generalizedKnow_holds :
    generalizedKnow agnostic () true (Karttunen.which student identicalWithSelf) := by
  intro v _
  simp only [Set.mem_ofPred_eq]
  cases v
  · rw [Karttunen.which_identicalWithSelf_of_exists (S := student) ⟨Student.mary, rfl⟩,
      Karttunen.which_identicalWithSelf_of_exists (S := student) ⟨Student.bill, rfl⟩]
  · rfl

theorem not_groenendijkStokhof_know :
    ¬ GroenendijkStokhof1984.Knows (agnostic ())
      (GroenendijkStokhof1984.whichDeDicto student identicalWithSelf) true := by
  intro h
  have := h (show (true, false) ∈ agnostic () from trivial)
  simp only [Setoid.mem_cell, whichDeDicto_eq_ker, Setoid.ker_def] at this
  have := congrArg (Student.mary ∈ ·) this
  simp [extension, student, identicalWithSelf] at this

end Identity

/-! ### Non-equivalence: living with one's actual spouse (§7) -/

/-! Bill is married to Sue, and the proposition that either lives with their actual spouse
is the proposition that they live together, so the two answers coincide. A world records
whether Sue is a student and whether the couple live together; in the actual world both
hold, and John's one false belief is that Sue is not a student. -/

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

def actual : World := (true, true)

/-- John's only doxastic alternative is the world where Sue is not a student and they live
together. -/
def john : Unit → SetRel World World := fun _ ↦ {p | p.2 = (false, true)}

theorem not_injective_livesWithSpouse : ¬ Function.Injective livesWithSpouse :=
  fun h ↦ Person.noConfusion (h (a₁ := .bill) (a₂ := .sue) rfl)

theorem extension_actual : extension student livesWithSpouse actual = Set.univ := by
  ext x
  cases x <;> simp [extension, student, livesWithSpouse, actual]

theorem extension_alt : extension student livesWithSpouse (false, true) = {.bill} := by
  ext x
  cases x <;> simp [extension, student, livesWithSpouse]

/-- The answer sets at the actual world and at John's alternative coincide, although Sue is a
student in one and not the other, (26). -/
theorem which_eq :
    Karttunen.which student livesWithSpouse (false, true) =
      Karttunen.which student livesWithSpouse actual := by
  simp only [Karttunen.which, extension_actual, extension_alt, livesWithSpouse]
  ext p
  simp only [Set.image_singleton, Set.mem_singleton_iff, Set.image_univ, Set.mem_range]
  exact ⟨fun h ↦ ⟨.bill, h.symm⟩, fun ⟨_, h⟩ ↦ h.symm⟩

/-- The generalized analysis wrongly makes (24) true. -/
theorem generalizedKnow_holds :
    generalizedKnow john () actual (Karttunen.which student livesWithSpouse) := by
  rintro v (rfl : v = (false, true))
  exact which_eq

/-- Groenendijk and Stokhof make (24) false, (25). -/
theorem not_groenendijkStokhof_know :
    ¬ GroenendijkStokhof1984.Knows (john ())
      (GroenendijkStokhof1984.whichDeDicto student livesWithSpouse) actual := by
  intro h
  have := h (show (actual, ((false : Bool), (true : Bool))) ∈ john () from rfl)
  simp only [Setoid.mem_cell, whichDeDicto_eq_ker, Setoid.ker_def, extension_actual,
    extension_alt] at this
  have := congrArg (Person.sue ∈ ·) this
  simp at this

end Spouses

/-! ### Structured propositions (§8) -/

/-- The structured intension, (27), pairs each student who called with the property of
calling. -/
def whichStructured (S C : E → Set W) (w : W) : Set (E × (E → Set W)) :=
  (fun x ↦ (x, C)) '' extension S C w

/-- (28) is Groenendijk and Stokhof's (11) for any predicate, since tagging each individual
with the property is injective whatever the property. -/
theorem ker_whichStructured (S C : E → Set W) :
    Setoid.ker (whichStructured S C) = GroenendijkStokhof1984.whichDeDicto S C :=
  Setoid.ker_comp_of_injective (extension S C) (Prod.mk_left_injective C).image_injective

theorem generalizedKnow_whichStructured_iff {S C : E → Set W} :
    generalizedKnow Dox x w (whichStructured S C) ↔
      GroenendijkStokhof1984.Knows (Dox x) (GroenendijkStokhof1984.whichDeDicto S C) w := by
  rw [generalizedKnow_iff_know_ker, ker_whichStructured]

theorem Karttunen.which_eq_image_whichStructured (S C : E → Set W) (w : W) :
    which S C w = (fun p : E × (E → Set W) ↦ p.2 p.1) '' whichStructured S C w := by
  simp [which, whichStructured, Set.image_image]

/-- On (21), structured answers withdraw the knowledge ascription. -/
theorem Identity.not_generalizedKnow_structured :
    ¬ generalizedKnow Identity.agnostic () true
      (whichStructured Identity.student identicalWithSelf) := by
  rw [generalizedKnow_iff_know_ker, ker_whichStructured]
  exact Identity.not_groenendijkStokhof_know

/-- On (24), structured answers withdraw the knowledge ascription. -/
theorem Spouses.not_generalizedKnow_structured :
    ¬ generalizedKnow Spouses.john () Spouses.actual
      (whichStructured Spouses.student Spouses.livesWithSpouse) := by
  rw [generalizedKnow_iff_know_ker, ker_whichStructured]
  exact Spouses.not_groenendijkStokhof_know

theorem Spouses.whichStructured_ne :
    whichStructured Spouses.student Spouses.livesWithSpouse (false, true) ≠
      whichStructured Spouses.student Spouses.livesWithSpouse Spouses.actual := by
  intro h
  have := congrArg ((Spouses.Person.sue, Spouses.livesWithSpouse) ∈ ·) h
  simp [whichStructured, Spouses.extension_actual, Spouses.extension_alt] at this

end Heim1994b
