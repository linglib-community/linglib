module

public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Composition.Writer
public import Linglib.Logic.Modal.Defs
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Order.Filter.Basic

/-!
# Karttunen (1973): Presuppositions of Compound Sentences

This file formalizes Karttunen's paper, which asks how the presuppositions of a compound sentence
are determined by those of its parts. The cumulative hypothesis of Langendoen and Savin adds them
up; Karttunen keeps it for the *holes*, factives, aspectuals and implicatives, which let every
presupposition of their complement through, and sets against them the *plugs*, verbs of saying,
which let none through, and the *filters*, the connectives, which let a presupposition of their
second clause through unless the first clause filters it: `if A then B` (13) and `A and B` (17)
presuppose what `A` presupposes and each presupposition of `B` that `A` does not entail, and
`A or B` (24) each presupposition of `B` that `¬A` does not entail.

A sentence is a computation of the Writer monad whose value is its assertion and whose log lists
its presuppositions, each filtered on its own (`Presupposing`), the side-effect carrier of
Giorgolo and Asudeh. The monad's own composition concatenates the logs, and is the cumulative
hypothesis (`conj_false`); a hole maps the value and keeps the log, internal negation among them;
a plug keeps the value and drops the log; and a filter drops from the second clause's log what the
first clause filters. The connectives take the filtering relation as a parameter: entailment in
the original conditions, entailment from assumed facts in the revisions of §9 (`Filters`).

§8 derives the rule for conjunction and the rule for disjunction from the rule for conditionals by
Harman's principles, that internal negation keeps presuppositions and that the classical
equivalences of `A ⊃ B` with `¬A ∨ B` and of `A & B` with `¬(¬A ∨ ¬B)` keep them
(`harman_conj`, `harman_disj`), and the rules satisfy the principles. The rules are not
commutative ((16), (22)), so the principle that equivalent sentences share presuppositions can
hold only of such chosen equivalences. §9's Geraldine example (25) presupposes (27) absolutely but
not given (28), and does again in the contrary context the paper sketches; the Nixon examples (30)
call for the same relativization with every connective. §10 finds no truth-functional three-valued
conjunction that behaves like a filter: Bochvar's internal conjunction is a hole, his external one
a plug, and Łukasiewicz's filters by the falsity of the other conjunct, so that (35b) comes out
presupposition-free and (35a) does not. §11 finds that a hole *believe* survives (37) only through
the equivalence (38), and fails on (42), whence the tentative verdict that attitude verbs are
plugs.

## Implementation notes

* A sentence's presuppositions are a list, the finite list of basic presuppositions of (5) in
  Karttunen's 1974 paper; only membership matters.
* The entailment a filter uses is from the truth of the first clause, which requires its
  presuppositions as well as its assertion (`Presupposing.truth`), so a presupposition that both
  clauses share is filtered as the second clause's and kept as the first's, as fn. 10 says. A
  filter thus reads the first clause's log, which no composition in Giorgolo and Asudeh's monad
  can.
* The per-presupposition rule is tested on *Jack has children, and Jack's children regret that
  baldness is hereditary*, built from the presuppositions of (1a) and (1b): it filters the first
  presupposition of the second conjunct and keeps the second, where a single conjoined
  presupposition would keep both.
* Murphy's restrictions on the assumed facts of §9 are read set-theoretically: some set of the
  facts, possibly empty, entails the presupposition together with the premise, is consistent with
  the premise, and does not entail the presupposition alone. On this reading the empty set filters
  only a presupposition the premise entails, of a consistent premise, that is not a tautology
  (`filters_empty_iff`), so the revised condition keeps the tautological presupposition of fn. 13
  (`univ_mem_log_disj_filters`), which the footnote counts as filtered under the revised condition
  as well as the original.
* The assumed facts are a set of propositions, not a deductively closed common ground: over the
  propositions a closed context accepts, Murphy's first restriction blocks nothing, since a
  context that entails `¬A` accepts `A ⊃ C` too (`filters_sets_of_compl_mem`).
* Van Fraassen's conjunction (34c), which the paper finds to behave as Łukasiewicz's on (35), is
  left out.

## References

* [karttunen-1973]
* [karttunen-1974-presupposition]
* [giorgolo-asudeh-2012]
* [bochvar-1938]
* [hintikka-1962]
-/

@[expose] public section

namespace Karttunen1973

open SignType Trivalent

universe u

variable {W : Type u}

/-! ### Sentences -/

/-- The Writer monad of presuppositions, in which a computation yields a value and logs the
propositions over `W` it presupposes. A sentence, as the projection rules see it, is a computation
whose value is its assertion. -/
abbrev Presupposing (W : Type u) := Writer (List (Set W))

namespace Presupposing

variable (A : Presupposing W (Set W)) {C : Set W}

/-- The worlds where the sentence is true, those where its presuppositions and its assertion
hold. -/
def truth : Set W := A.val ∩ {w | ∀ C ∈ A.log, w ∈ C}

theorem compl_map_compl : (·ᶜ) <$> (·ᶜ) <$> A = A :=
  Writer.ext (compl_compl A.val) rfl

/-- A sentence entails each of its presuppositions (fn. 10). -/
theorem truth_subset_of_mem (h : C ∈ A.log) : A.truth ⊆ C :=
  fun _ hw ↦ hw.2 C h

/-- The sentence of a trivalent proposition asserts its positive extension and presupposes its
support. -/
def ofTrivalent (p : W → SignType) : Presupposing W (Set W) :=
  Writer.mk (posSupport p) [Function.support p]

end Presupposing

/-! ### The filters (§5–§7) -/

section Filters

variable (φ : Set W → Set W → Prop) (A B : Presupposing W (Set W)) {C : Set W}

open Classical in
/-- Under rule (13), `if A then B` presupposes what `A` presupposes and each presupposition of `B`
that `A` does not filter, by the relation `φ` from the truth of `A`. -/
noncomputable def cond : Presupposing W (Set W) :=
  Writer.mk (A.valᶜ ∪ B.val) (A.log ++ B.log.filter fun C ↦ ¬ φ A.truth C)

open Classical in
/-- Under rule (17), `A and B` presupposes what `A` presupposes and each presupposition of `B`
that `A` does not filter. -/
noncomputable def conj : Presupposing W (Set W) :=
  Writer.mk (A.val ∩ B.val) (A.log ++ B.log.filter fun C ↦ ¬ φ A.truth C)

open Classical in
/-- Under rule (24), `A or B` presupposes what `A` presupposes and each presupposition of `B` that
the negation of `A` does not filter. -/
noncomputable def disj : Presupposing W (Set W) :=
  Writer.mk (A.val ∪ B.val) (A.log ++ B.log.filter fun C ↦ ¬ φ ((·ᶜ) <$> A).truth C)

@[simp] theorem mem_log_cond : C ∈ (cond φ A B).log ↔ C ∈ A.log ∨ C ∈ B.log ∧ ¬ φ A.truth C := by
  simp [cond]

@[simp] theorem mem_log_conj : C ∈ (conj φ A B).log ↔ C ∈ A.log ∨ C ∈ B.log ∧ ¬ φ A.truth C := by
  simp [conj]

@[simp] theorem mem_log_disj :
    C ∈ (disj φ A B).log ↔ C ∈ A.log ∨ C ∈ B.log ∧ ¬ φ ((·ᶜ) <$> A).truth C := by
  simp [disj]

/-- The cumulative hypothesis of Langendoen and Savin (§1) is conjunction filtering nothing, the
Writer monad's own conjunction. -/
theorem conj_false : conj (fun _ _ ↦ False) A B = (· ∩ ·) <$> A <*> B := by
  ext <;> simp [conj, seq_eq_bind_map]

theorem truth_conj : (conj (· ⊆ ·) A B).truth = A.truth ∩ B.truth := by
  ext w
  simp only [Presupposing.truth, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_log_conj]
  constructor
  · rintro ⟨hv, h⟩
    have hA : w ∈ A.truth := ⟨hv.1, fun C hC ↦ h C (.inl hC)⟩
    refine ⟨hA, hv.2, fun C hC ↦ ?_⟩
    by_cases hf : A.truth ⊆ C
    · exact hf hA
    · exact h C (.inr ⟨hC, hf⟩)
  · rintro ⟨⟨ha, hA⟩, hb, hB⟩
    exact ⟨⟨ha, hb⟩, fun C ↦ by rintro (hC | ⟨hC, -⟩) <;> simp_all⟩

/-! ### Harman's derivation (§8) -/

theorem log_cond : (cond φ A B).log = (disj φ ((·ᶜ) <$> A) B).log := by
  simp only [cond, disj, Writer.log_mk, Writer.log_map]
  rw [Presupposing.compl_map_compl]

theorem log_conj :
    (conj φ A B).log = ((·ᶜ) <$> disj φ ((·ᶜ) <$> A) ((·ᶜ) <$> B)).log := by
  simp only [conj, disj, Writer.log_mk, Writer.log_map]
  rw [Presupposing.compl_map_compl]

theorem log_disj : (disj φ A B).log = (cond φ ((·ᶜ) <$> A) B).log := rfl

end Filters

section Harman

variable {S : Type*} {neg : S → S} {cond conj disj : S → S → S} {π : S → Set (Set W)}
  {f : S → Set W → Prop}

/-- Given these presupposition equivalences, the conditional rule (13) yields the conjunction rule
(17), as in Harman's derivation (§8). -/
theorem harman_conj (hneg : ∀ A, π (neg A) = π A)
    (hcond : ∀ A B, π (cond A B) = π (disj (neg A) B))
    (hconj : ∀ A B, π (conj A B) = π (neg (disj (neg A) (neg B))))
    (h13 : ∀ A B, π (cond A B) = π A ∪ {C ∈ π B | ¬ f A C}) (A B : S) :
    π (conj A B) = π A ∪ {C ∈ π B | ¬ f A C} := by
  rw [hconj, hneg, ← hcond, h13, hneg]

/-- If `A ∨ B` shares its presuppositions with `¬A ⊃ B`, the conditional rule yields the disjunction
rule (24) (§8). -/
theorem harman_disj (hneg : ∀ A, π (neg A) = π A)
    (hdisj : ∀ A B, π (disj A B) = π (cond (neg A) B))
    (h13 : ∀ A B, π (cond A B) = π A ∪ {C ∈ π B | ¬ f A C}) (A B : S) :
    π (disj A B) = π A ∪ {C ∈ π B | ¬ f (neg A) C} := by
  rw [hdisj, h13, hneg]

end Harman

/-! ### Jack's children (§5–§7) -/

/-- `Jack has children`, over whether he does and whether baldness is hereditary. -/
def hasChildren : Presupposing (Bool × Bool) (Set (Bool × Bool)) := Writer.mk {w | w.1} []

/-- `All of Jack's children are bald`, which presupposes that Jack has children; the assertion is
idealized. -/
def allBald : Presupposing (Bool × Bool) (Set (Bool × Bool)) := Writer.mk Set.univ [{w | w.1}]

/-- `Jack's children regret that baldness is hereditary`, which presupposes that Jack has
children, as (1a) does, and that baldness is hereditary, as (1b) does. -/
def regretHereditary : Presupposing (Bool × Bool) (Set (Bool × Bool)) :=
  Writer.mk Set.univ [{w | w.1}, {w | w.2}]

private theorem truth_hasChildren : hasChildren.truth = {w | w.1} := by
  simp [Presupposing.truth, hasChildren]

private theorem truth_compl_hasChildren : ((·ᶜ) <$> hasChildren).truth = {w | w.1 = false} := by
  ext w; simp [Presupposing.truth, hasChildren]

/-- (16a) presupposes nothing and (16b) that Jack has children, so conjunction is not commutative
on presuppositions. -/
theorem log_conj_16 :
    (conj (· ⊆ ·) hasChildren allBald).log = [] ∧
      (conj (· ⊆ ·) allBald hasChildren).log = [{w | w.1}] := by
  refine ⟨List.eq_nil_iff_forall_not_mem.2 fun C hC ↦ ?_, by simp [conj, allBald, hasChildren]⟩
  rcases (mem_log_conj _ _ _).1 hC with h | ⟨hC, h⟩
  · simp [hasChildren] at h
  · have hC : C = {w | w.1} := by simpa [allBald] using hC
    exact h (by rw [truth_hasChildren, hC])

/-- (22a) presupposes nothing, and by (24a) (22b) presupposes that Jack has children, a sentence
the paper leaves undecided (fn. 11). -/
theorem log_disj_22 :
    (disj (· ⊆ ·) ((·ᶜ) <$> hasChildren) allBald).log = [] ∧
      (disj (· ⊆ ·) allBald ((·ᶜ) <$> hasChildren)).log = [{w | w.1}] := by
  refine ⟨List.eq_nil_iff_forall_not_mem.2 fun C hC ↦ ?_, by simp [disj, allBald, hasChildren]⟩
  rcases (mem_log_disj _ _ _).1 hC with h | ⟨hC, h⟩
  · simp [hasChildren] at h
  · have hC : C = {w | w.1} := by simpa [allBald] using hC
    exact h (by rw [Presupposing.compl_map_compl, truth_hasChildren, hC])

/-- The conditional rule does not carry over to disjunction, since (11a) presupposes nothing but its
disjunctive counterpart presupposes that Jack has children (§8). -/
theorem log_cond_11a_disj :
    (cond (· ⊆ ·) hasChildren allBald).log = [] ∧
      {w | w.1} ∈ (disj (· ⊆ ·) hasChildren allBald).log := by
  refine ⟨List.eq_nil_iff_forall_not_mem.2 fun C hC ↦ ?_, ?_⟩
  · rcases (mem_log_cond _ _ _).1 hC with h | ⟨hC, h⟩
    · simp [hasChildren] at h
    · have hC : C = {w | w.1} := by simpa [allBald] using hC
      exact h (by rw [truth_hasChildren, hC])
  · refine (mem_log_disj _ _ _).2 (.inr ⟨by simp [allBald], fun h ↦ ?_⟩)
    rw [truth_compl_hasChildren] at h
    exact absurd (h (show (false, false) ∈ {w : Bool × Bool | w.1 = false} from rfl)) (by simp)

/-- Rule (17) filters the second conjunct's presupposition that Jack has children and keeps the
presupposition that baldness is hereditary. -/
theorem mem_log_conj_regret :
    {w | w.2} ∈ (conj (· ⊆ ·) hasChildren regretHereditary).log ∧
      {w | w.1} ∉ (conj (· ⊆ ·) hasChildren regretHereditary).log := by
  refine ⟨(mem_log_conj _ _ _).2 (.inr ⟨by simp [regretHereditary], fun h ↦ ?_⟩), fun h ↦ ?_⟩
  · rw [truth_hasChildren] at h
    exact absurd (h (show (true, false) ∈ {w : Bool × Bool | w.1} from rfl)) (by simp)
  · rcases (mem_log_conj _ _ _).1 h with h | ⟨-, h⟩
    · simp [hasChildren] at h
    · exact h truth_hasChildren.le

/-! ### Assumed facts (§9) -/

/-- Under (24b′) and (17b′), given the assumed facts `F`, the premise `P` filters `C` when some set
of them, possibly empty, entails `C` together with `P`, though it does not entail the negation of
`P` nor `C` alone (Murphy's restrictions). -/
def Filters (F : Set (Set W)) (P C : Set W) : Prop :=
  ∃ X ⊆ F, ⋂₀ X ∩ P ⊆ C ∧ ¬ ⋂₀ X ⊆ Pᶜ ∧ ¬ ⋂₀ X ⊆ C

theorem filters_empty_iff {P C : Set W} :
    Filters ∅ P C ↔ P ⊆ C ∧ P.Nonempty ∧ C ≠ Set.univ := by
  simp [Filters, Set.subset_empty_iff, Set.not_subset, Set.eq_univ_iff_forall, Set.nonempty_def]

theorem not_filters_univ (F : Set (Set W)) (P : Set W) : ¬ Filters F P Set.univ :=
  fun ⟨_, _, _, _, h⟩ ↦ h (Set.subset_univ _)

theorem filters_sets_of_compl_mem {G : Filter W} {P C : Set W} (hP : Pᶜ ∈ G)
    (hPC : (P ∩ C).Nonempty) (hC : ¬ Pᶜ ⊆ C) : Filters G.sets P C := by
  refine ⟨{Pᶜ ∪ C}, Set.singleton_subset_iff.2 (G.mem_of_superset hP Set.subset_union_left), ?_,
    ?_, ?_⟩ <;> simp only [Set.sInter_singleton]
  · rintro w ⟨hw | hw, hP⟩
    · exact absurd hP hw
    · exact hw
  · obtain ⟨w, hwP, hwC⟩ := hPC
    exact fun h ↦ h (.inr hwC) hwP
  · exact fun h ↦ hC (Set.subset_union_left.trans h)

/-- Whether Geraldine is a Mormon and whether she has worn holy underwear. -/
inductive Geraldine where
  | mormonWorn
  | mormonUnworn
  | gentileWorn
  | gentileUnworn

/-- (26) `Geraldine is a Mormon`. -/
abbrev mormon : Set Geraldine := {.mormonWorn, .mormonUnworn}

/-- (27) `Geraldine has worn holy underwear`. -/
abbrev worn : Set Geraldine := {.mormonWorn, .gentileWorn}

/-- (25) `Either Geraldine is not a Mormon or she has given up wearing her holy underwear`,
whose second disjunct presupposes (27); its assertion is idealized. -/
noncomputable def geraldine (φ : Set Geraldine → Set Geraldine → Prop) :
    Presupposing Geraldine (Set Geraldine) :=
  disj φ (Writer.mk mormonᶜ []) (Writer.mk Set.univ [worn])

private theorem mem_log_geraldine {φ : Set Geraldine → Set Geraldine → Prop} :
    worn ∈ (geraldine φ).log ↔ ¬ φ mormon worn := by
  have : Presupposing.truth ((·ᶜ) <$> (Writer.mk mormonᶜ [] : Presupposing Geraldine _)) =
      mormon := by
    simp [Presupposing.truth]
  simp [geraldine, this]

/-- Absolutely, (25) presupposes (27), since (26) does not entail it. -/
theorem worn_mem_log_geraldine : worn ∈ (geraldine (· ⊆ ·)).log :=
  mem_log_geraldine.2 fun h ↦ absurd (h (show Geraldine.mormonUnworn ∈ mormon by simp)) (by simp)

/-- Given (28) `All Mormons have worn holy underwear`, (25) does not presuppose (27), since (26)
and (28) together entail it. -/
theorem worn_not_mem_log_geraldine_28 :
    worn ∉ (geraldine (Filters {{Geraldine.mormonUnworn}ᶜ})).log := by
  rw [mem_log_geraldine, not_not]
  refine ⟨{{Geraldine.mormonUnworn}ᶜ}, le_rfl, ?_, ?_, ?_⟩ <;> simp only [Set.sInter_singleton]
  · rintro (_ | _ | _ | _) ⟨h1, h2⟩ <;> simp_all
  · intro h'
    exact absurd (h' (show Geraldine.mormonWorn ∈ ({.mormonUnworn}ᶜ : Set Geraldine) by simp))
      (by simp)
  · intro h'
    exact absurd (h' (show Geraldine.gentileUnworn ∈ ({.mormonUnworn}ᶜ : Set Geraldine) by simp))
      (by simp)

/-- In the contrary context the paper sketches, where Mormons must not wear holy underwear, (25)
presupposes (27). -/
theorem worn_mem_log_geraldine_contrary :
    worn ∈ (geraldine (Filters {{Geraldine.mormonWorn}ᶜ})).log := by
  rw [mem_log_geraldine]
  rintro ⟨X, hX, h, -, -⟩
  rcases Set.subset_singleton_iff_eq.1 hX with rfl | rfl
  · simp only [Set.sInter_empty, Set.univ_inter] at h
    exact absurd (h (show Geraldine.mormonUnworn ∈ mormon by simp)) (by simp)
  · simp only [Set.sInter_singleton] at h
    exact absurd (h (show Geraldine.mormonUnworn ∈ ({.mormonWorn}ᶜ ∩ mormon : Set Geraldine) by
      simp)) (by simp)

/-- By Murphy's first restriction, (25) presupposes (27) relative to the assumption `Geraldine is
not a Mormon`. -/
theorem worn_mem_log_geraldine_notMormon : worn ∈ (geraldine (Filters {mormonᶜ})).log := by
  rw [mem_log_geraldine]
  rintro ⟨X, hX, h, hc, -⟩
  rcases Set.subset_singleton_iff_eq.1 hX with rfl | rfl
  · simp only [Set.sInter_empty, Set.univ_inter] at h
    exact absurd (h (show Geraldine.mormonUnworn ∈ mormon by simp)) (by simp)
  · exact hc (by simp)

/-- `Nixon will appoint J. Edgar Hoover to the Cabinet`, over whether he will and whether Hoover is
a homosexual (32). -/
def appoint : Presupposing (Bool × Bool) (Set (Bool × Bool)) := Writer.mk {w | w.1} []

/-- `He will regret having appointed a homosexual`, which presupposes (31). -/
def regret : Presupposing (Bool × Bool) (Set (Bool × Bool)) := Writer.mk Set.univ [{w | w.1 ∧ w.2}]

private theorem truth_appoint : appoint.truth = {w | w.1} := by
  simp [Presupposing.truth, appoint]

private theorem truth_compl_compl_appoint : ((·ᶜ) <$> (·ᶜ) <$> appoint).truth = {w | w.1} := by
  simp [Presupposing.truth, appoint]

private theorem filters_32 : Filters {{w : Bool × Bool | w.2}} {w | w.1} {w | w.1 ∧ w.2} := by
  refine ⟨_, le_rfl, ?_, fun h ↦ ?_, fun h ↦ ?_⟩ <;> simp only [Set.sInter_singleton] at *
  · exact fun w ⟨h2, h1⟩ ↦ ⟨h1, h2⟩
  · exact absurd (h (show (true, true) ∈ {w : Bool × Bool | w.2} from rfl)) (by simp)
  · exact absurd (h (show (false, true) ∈ {w : Bool × Bool | w.2} from rfl)) (by simp)

/-- With no assumed facts, each of (30a–c) presupposes (31), which (33) alone does not entail. -/
theorem mem_log_30 :
    {w | w.1 ∧ w.2} ∈ (cond (Filters ∅) appoint regret).log ∧
      {w | w.1 ∧ w.2} ∈ (conj (Filters ∅) appoint regret).log ∧
      {w | w.1 ∧ w.2} ∈ (disj (Filters ∅) ((·ᶜ) <$> appoint) regret).log := by
  have h : ¬ Filters ∅ {w : Bool × Bool | w.1} {w | w.1 ∧ w.2} := fun h ↦ by
    simpa using filters_empty_iff.1 h |>.1 (show (true, false) ∈ {w : Bool × Bool | w.1} from rfl)
  simp only [mem_log_cond, mem_log_conj, mem_log_disj, truth_appoint, truth_compl_compl_appoint]
  exact ⟨.inr ⟨by simp [regret], h⟩, .inr ⟨by simp [regret], h⟩, .inr ⟨by simp [regret], h⟩⟩

/-- Given (32), none of the conditional, the conjunction and the disjunction of (30a–c)
presupposes (31), since (32) and (33) together entail it. -/
theorem not_mem_log_30 :
    {w | w.1 ∧ w.2} ∉ (cond (Filters {{w | w.2}}) appoint regret).log ∧
      {w | w.1 ∧ w.2} ∉ (conj (Filters {{w | w.2}}) appoint regret).log ∧
      {w | w.1 ∧ w.2} ∉ (disj (Filters {{w | w.2}}) ((·ᶜ) <$> appoint) regret).log := by
  simp only [mem_log_cond, mem_log_conj, mem_log_disj, truth_appoint, truth_compl_compl_appoint]
  simp [appoint, filters_32]

/-- `John is dumb`, over whether he is. -/
def johnDumb : Presupposing Bool (Set Bool) := Writer.mk {true} []

/-- `He knows that if it rains, it rains`, which presupposes a tautology (fn. 13). -/
def knowsTautology : Presupposing Bool (Set Bool) := Writer.mk Set.univ [Set.univ]

/-- The original condition (24b) filters the tautology presupposed by the second disjunct (fn. 13).
-/
theorem univ_not_mem_log_disj : Set.univ ∉ (disj (· ⊆ ·) johnDumb knowsTautology).log := by
  intro h
  rcases (mem_log_disj _ _ _).1 h with h | ⟨-, h⟩
  · simp [johnDumb] at h
  · exact h (Set.subset_univ _)

/-- The revised condition (24b′) keeps fn. 13's tautology, since with Murphy's restrictions no
set of assumed facts filters it. -/
theorem univ_mem_log_disj_filters (F : Set (Set Bool)) :
    Set.univ ∈ (disj (Filters F) johnDumb knowsTautology).log :=
  (mem_log_disj _ _ _).2 (.inr ⟨by simp [knowsTautology], not_filters_univ F _⟩)

/-! ### Truth-functional conjunction (§10) -/

section TruthFunctional

variable (p q : W → SignType) (w : W)

/-- Bochvar's internal conjunction (34a) ([bochvar-1938]), the substrate's `SignType.meetWeak`, is
a hole, defined only where both conjuncts are. -/
theorem meetWeak_ne_zero_iff : (p w).meetWeak (q w) ≠ 0 ↔ p w ≠ 0 ∧ q w ≠ 0 := by
  simp

/-- Bochvar's external conjunction (34d), the conjunction of the conjuncts' truth, `t(A) & t(B)`
(fn. 18), is a plug, defined everywhere. -/
theorem meetWeak_ofProp_ne_zero : (ofProp (p w = 1)).meetWeak (ofProp (q w = 1)) ≠ 0 := by
  simp

/-- Łukasiewicz's conjunction (34b), Strong Kleene `⊓`, is defined wherever a conjunct is false,
whatever the other conjunct presupposes. -/
theorem inf_ne_zero_of_eq_neg_one (hf : p w = -1) : (p ⊓ q) w ≠ 0 := by
  simp [hf]

end TruthFunctional

/-- Whether Paris is the capital of France and whether France has a king. -/
inductive France where
  | parisKing
  | parisNoKing
  | marseilleKing
  | marseilleNoKing
  deriving DecidableEq

/-- `Paris is the capital of France`. -/
abbrev capitalParis : Set France := {.parisKing, .parisNoKing}

/-- `France has a king`. -/
abbrev hasKing : Set France := {.parisKing, .marseilleKing}

/-- `The king of France is bald`, which presupposes a king; the assertion is idealized. -/
noncomputable def kingBald : France → SignType := hasKing.indicator 1

private theorem support_kingBald : Function.support kingBald = hasKing := by
  ext w; by_cases h : w ∈ hasKing <;> simp [kingBald, h]

/-- At the kingless world of (35), Łukasiewicz's conjunction makes (35a) undefined and (35b) false.
-/
theorem inf_kingBald_35 :
    ofProp (France.parisNoKing ∈ capitalParis) ⊓ kingBald .parisNoKing = 0 ∧
      ofProp (France.parisNoKing ∉ capitalParis) ⊓ kingBald .parisNoKing = -1 := by
  simp [kingBald]

/-- By (17) both sentences of (35) presuppose a king, since neither capital entails one. -/
theorem hasKing_mem_log_conj_35 :
    hasKing ∈ (conj (· ⊆ ·) (.ofTrivalent fun w ↦ ofProp (w ∈ capitalParis))
        (.ofTrivalent kingBald)).log ∧
      hasKing ∈ (conj (· ⊆ ·) (.ofTrivalent fun w ↦ ofProp (w ∉ capitalParis))
        (.ofTrivalent kingBald)).log := by
  have hk : hasKing ∈ (Presupposing.ofTrivalent kingBald).log := by
    simp [Presupposing.ofTrivalent, support_kingBald]
  refine ⟨(mem_log_conj _ _ _).2 (.inr ⟨hk, fun h ↦ ?_⟩),
    (mem_log_conj _ _ _).2 (.inr ⟨hk, fun h ↦ ?_⟩)⟩
  · exact absurd (h (show France.parisNoKing ∈ _ by
      simp [Presupposing.truth, Presupposing.ofTrivalent])) (by simp)
  · exact absurd (h (show France.marseilleNoKing ∈ _ by
      simp [Presupposing.truth, Presupposing.ofTrivalent])) (by simp)

/-- Like Łukasiewicz's conjunction, Middle Kleene `SignType.meetMiddle` makes (35b) false. -/
theorem meetMiddle_35b :
    (ofProp (France.parisNoKing ∉ capitalParis)).meetMiddle (kingBald .parisNoKing) = -1 := by
  simp [kingBald]

/-! ### Propositional attitudes (§11)

A hole maps the complement's value and keeps its log, `att <$> A`; a plug keeps the value and drops
the log, `pure (att A.val)`. -/

section Attitudes

variable (φ : Set W → Set W → Prop) (att att₁ att₂ : Set W → Set W) (a c : Set W)

/-- With hole attitudes, (37) and (42) presuppose that Fred has been beating Zelda unless believing
it filters it. -/
theorem mem_log_conj_hole :
    a ∈ (conj φ (att₁ <$> Writer.mk a []) (att₂ <$> Writer.mk c [a])).log ↔ ¬ φ (att₁ a) a := by
  simp [Presupposing.truth]

/-- The sentence (39) presupposes nothing, whether the attitude verb is a hole or a plug. -/
theorem log_map_conj : (att <$> conj (· ⊆ ·) (Writer.mk a []) (Writer.mk c [a])).log = [] := by
  simp [conj, Presupposing.truth]

/-- With belief as necessity over doxastic alternatives ([hintikka-1962]), (37) and (39) assert the
same, the equivalence (38). -/
theorem val_map_box_conj (R : SetRel W W) (A B : Presupposing W (Set W)) :
    (R.core <$> conj φ A B).val = (conj φ (R.core <$> A) (R.core <$> B)).val :=
  SetRel.core_inter R _ _

/-- As plugs, the two distinct attitudes of (42), conjoined as (43), presuppose nothing. -/
theorem log_conj_pure (A B : Presupposing W (Set W)) :
    (conj φ (pure (att₁ A.val)) (pure (att₂ B.val))).log = [] := by
  simp [conj]

end Attitudes

end Karttunen1973
