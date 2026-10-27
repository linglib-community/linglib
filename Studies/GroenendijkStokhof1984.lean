module

public import Studies.Karttunen1977

/-!
# Groenendijk and Stokhof (1984): Studies on the Semantics of Questions

Groenendijk and Stokhof take a question to be a partition of the indices, here a `Setoid`. *Who
walks* relates two indices when the same individuals walk at both (`who`), so that at an index it
denotes the proposition true exactly where the walkers are those of that index, and *whether p*
is the bipartition by `p`. *Know* and *tell* relate an individual to the proposition denoted, so
to know who walks is to have one's alternatives inside the actual cell (`Knows`). An
individual's information at an index is a set of indices compatible with what they believe
inside a set compatible with what they know, which contains the index (`InformationSets`). A
proposition answers a question for the individual when adding it to their information leaves
the information inside one cell, and answers it partially when it rules out a cell.

## Main statements

* `Knows.mem_core`: to know the answer is to know every true proposition the question decides.
* `not_knows_who_of_believes`: believing that someone walks who does not excludes knowing who
  walks.
* `who_compl`: *who walks* and *who doesn't walk* are one question.
* `who_le_whichDeRe`, `whichDeRe_compl`, `Men.readings_independent`: *which man walks* read de
  re follows from *who walks* and is *which man doesn't walk* read de re, while the de dicto
  reading is independent of it.
* `karttunen_knows_of_knows`, `Walkers.karttunen_knows`: Karttunen's postulate for *know*
  follows from this one, but holds of someone who wrongly believes that Suzy walks.
* `InformationSets.update`, `InformationSets.LetsKnow.givesTrueAnswer`: updating with a
  proposition keeps information well formed, and a proposition that lets one know an answer
  gives a true one.
* `Figure13.letsKnow_byName`: of a name and a description that answer alike on someone's
  beliefs, only the name, which is true, lets them know the answer.
* `better_or_inter_or_union`: of two compatible partial answers, one is better, or their
  conjunction or their disjunction is better than both.
* `knowsSomeAnswer_of_knows`: knowing who has a pen gives the mention-some knowledge once someone
  has a pen.

## Implementation notes

Extensions are topical properties `E → Set W` and attitudes are `SetRel W W` read through
`SetRel.core`. Mathlib's order on `Setoid` is the dissertation's inclusion of questions
(`Setoid.le_iff_forall_classes`), whose dual atoms are the bipartitions (`Setoid.isCoatom_iff`).
The domain of individuals is fixed across indices, as the dissertation assumes in accepting (X);
the update of information is classical, and giving an answer leaves out chapter IV's
presupposition that the question is open. The mention-some question is `Question.which`. Two
printed claims are corrected, the equation for the answers compatible with a conjunction
(`TwoCells.determined_inter_ne`) and the cells that *(at least) an M G's* rules out in figure 15
(`Figure15.indefinite_partial_false`). Page numbers are the dissertation's printed ones.

## TODO

* Chapter IV's indirect answers and its comparison and correctness of answers (sections 7 to 9),
  the pragmatic comparison of appendix 2 of chapter V, and the claim that a partial answer to a
  bipartition is complete (chapter IV, p. 235).
* Chapter V's linguistic answers and the pragmatic properties of terms, and chapter VI's choice
  readings, whose examples are rows of `Data.Examples.GroenendijkStokhof1984`.
* Chapter III's functional readings.

## References

* [groenendijk-stokhof-1984]
* [groenendijk-stokhof-1982]
* [karttunen-1977]
-/

@[expose] public section

open Question Setoid
open scoped SetRel

namespace GroenendijkStokhof1984

variable {W E : Type*}

/-! ### Questions -/

/-- The extension of `P` at `w` is the set of individuals that have `P` there. -/
def extension (P : E → Set W) (w : W) : Set E := {x | w ∈ P x}

@[simp] theorem mem_extension {P : E → Set W} {w : W} {x : E} :
    x ∈ extension P w ↔ w ∈ P x := Iff.rfl

/-- *Who P?* relates two indices at which `P` has the same extension (chapter II, p. 85). -/
def who (P : E → Set W) : Setoid W := Setoid.ker (extension P)

theorem who_iff {P : E → Set W} {v w : W} : who P v w ↔ ∀ x, (v ∈ P x ↔ w ∈ P x) :=
  Setoid.ker_def.trans Set.ext_iff

/-- *Which G P?* read de dicto asks for the extension of `G` and `P` together (chapter II,
p. 112). -/
def whichDeDicto (G P : E → Set W) : Setoid W := who fun x ↦ G x ∩ P x

/-- *Which G P?* read de re at `w` asks for the extension of `P` among the individuals that are
`G` at `w` (chapter II, p. 114). -/
def whichDeRe (G P : E → Set W) (w : W) : Setoid W :=
  Setoid.ker fun v ↦ extension G w ∩ extension P v

theorem whichDeRe_iff {G P : E → Set W} {w v u : W} :
    whichDeRe G P w v u ↔ ∀ x, w ∈ G x → (v ∈ P x ↔ u ∈ P x) := by
  simp only [Setoid.ker_def, Set.ext_iff, Set.mem_inter_iff, mem_extension,
    and_congr_right_iff]

theorem who_eq_partition (P : E → Set W) : who P = partition (Set.range P) :=
  Setoid.ext fun _ _ ↦ by rw [who_iff, partition_iff, Set.forall_mem_range]

theorem whichDeRe_eq_partition (G P : E → Set W) (w : W) :
    whichDeRe G P w = partition (P '' extension G w) := by
  ext v u
  simp only [whichDeRe_iff, partition_iff, Set.forall_mem_image, mem_extension]

-- p. 220
theorem who_eq_iInf_polar (P : E → Set W) : who P = ⨅ x, Setoid.polar (P x) :=
  Setoid.ext fun _ _ ↦
    who_iff.trans (Setoid.iInf_iff.trans (forall_congr' fun _ ↦ Setoid.polar_iff)).symm

-- (5)
theorem who_le_polar (P : E → Set W) (x : E) : who P ≤ Setoid.polar (P x) :=
  who_eq_iInf_polar P ▸ iInf_le _ x

theorem who_decides (P : E → Set W) (x : E) : (who P).Decides (P x) := who_le_polar P x

/-- *Who walks* and *who doesn't walk* are one question, so that knowing the answer to either is
knowing the answer to the other (chapter II, (X)). -/
theorem who_compl (P : E → Set W) : who (fun x ↦ (P x)ᶜ) = who P :=
  Setoid.ker_comp_of_injective (extension P) compl_injective

theorem who_comp_of_surjective {E' : Type*} {f : E' → E} (hf : Function.Surjective f)
    (P : E → Set W) : who (P ∘ f) = who P :=
  Setoid.ker_comp_of_injective (extension P) (Set.preimage_injective.2 hf)

/-- *Who walks* entails *which girl walks* read de re (chapter II, (XI)). -/
theorem who_le_whichDeRe (G P : E → Set W) (w : W) : who P ≤ whichDeRe G P w :=
  Setoid.ker_le_ker_comp (extension P) (extension G w ∩ ·)

/-- *Which man walks* and *which man doesn't walk*, both read de re, are one question (chapter
II, (XII)). -/
theorem whichDeRe_compl (G P : E → Set W) (w : W) :
    whichDeRe G (fun x ↦ (P x)ᶜ) w = whichDeRe G P w := by
  ext v u
  simp only [whichDeRe_iff, Set.mem_compl_iff, not_iff_not]

-- (8)
theorem whichDeDicto_inf_who_le (G P : E → Set W) :
    whichDeDicto G P ⊓ who G ≤ whichDeDicto G fun x ↦ (P x)ᶜ := fun _ _ ⟨h, hG⟩ ↦
  who_iff.2 fun x ↦ by
    have := who_iff.1 h x
    have := who_iff.1 hG x
    grind

-- pp. 447–449
theorem iInf_who (R : E → E → Set W) : ⨅ x, who (R x) = who fun p : E × E ↦ R p.1 p.2 := by
  ext v u
  simp only [Setoid.iInf_iff, who_iff, Prod.forall]

/-! ### Knowing the answer -/

/-- An individual whose alternatives at `w` are given by `R` knows the answer to `Q` at `w` when
every alternative lies in the cell of `w`, the proposition the question denotes at `w`. -/
def Knows (Q : Setoid W) (w : W) (R : SetRel W W) : Prop := w ∈ R.core (Q.cell w)

variable {R : SetRel W W} {Q Q' : Setoid W} {w : W} {p q : Set W}

theorem Knows.mono (hQ : Q ≤ Q') (h : Knows Q w R) : Knows Q' w R :=
  fun _ hv ↦ hQ (h hv)

theorem knows_inf_iff : Knows (Q ⊓ Q') w R ↔ Knows Q w R ∧ Knows Q' w R :=
  ⟨fun h ↦ ⟨h.mono inf_le_left, h.mono inf_le_right⟩, fun h _ hv ↦ ⟨h.1 hv, h.2 hv⟩⟩

/-- To know the answer is to know every true proposition the question decides, which uses no
factivity, so that the arguments (I) to (VII) of chapter II hold for *tell* as for *know*. -/
theorem Knows.mem_core (h : Knows Q w R) (hp : Q.Decides p) (hw : w ∈ p) : w ∈ R.core p :=
  SetRel.core_mono (hp.cell_subset hw) h

/-- Knowing whether Mary walks is knowing that she walks when she does (chapter II, (I)). -/
example (h : Knows (Setoid.polar p) w R) (hw : w ∈ p) : w ∈ R.core p :=
  h.mem_core polar_decides hw

/-- Knowing whether Mary walks is knowing that she doesn't when she doesn't (chapter II, (II)). -/
example (h : Knows (Setoid.polar p) w R) (hw : w ∉ p) : w ∈ R.core pᶜ :=
  h.mem_core polar_decides.compl hw

/-- Knowing whether Mary walks or Bill sleeps, when Mary doesn't walk and Bill sleeps, is knowing
that Mary doesn't walk and Bill sleeps (chapter II, (IX)). -/
example (h : Knows (Setoid.polar p ⊓ Setoid.polar q) w R) (hp : w ∉ p) (hq : w ∈ q) :
    w ∈ R.core (pᶜ ∩ q) :=
  h.mem_core ((polar_decides.mono inf_le_left).compl.inter (polar_decides.mono inf_le_right))
    ⟨hp, hq⟩

-- p. 87
theorem knows_who_iff {P : E → Set W} :
    Knows (who P) w R ↔
      (∀ x, w ∈ P x → w ∈ R.core (P x)) ∧ ∀ x, w ∉ P x → w ∈ R.core (P x)ᶜ := by
  simp only [Knows, SetRel.mem_core, Setoid.mem_cell, who_iff, Set.mem_compl_iff]
  grind

theorem knows_nobody {P : E → Set W} (h : Knows (who P) w R) (hw : ∀ x, w ∉ P x) :
    w ∈ R.core {v | ∀ x, v ∉ P x} :=
  fun _ hv x ↦ (knows_who_iff.1 h).2 x (hw x) hv

/-- Someone with consistent beliefs within their knowledge who believes of a non-walker that they
walk doesn't know who walks (chapter II, (VIII) and p. 109). -/
theorem not_knows_who_of_believes {D K : SetRel W W} {P : E → Set W} {x : E} (hDK : D ⊆ K)
    (hD : ∃ v, w ~[D] v) (hbel : w ∈ D.core (P x)) (hx : w ∉ P x) : ¬ Knows (who P) w K :=
  fun h ↦ let ⟨_, hv⟩ := hD; (knows_who_iff.1 h).2 x hx (hDK hv) (hbel hv)

/-! ### Karttunen's postulate for *know* -/

/-- Knowing the answer to a partition satisfies Karttunen's meaning postulate for *know* on the
Hamblin set, both its clause for the true answers and its clause for an empty set of them. -/
theorem karttunen_knows_of_knows {H : Set (Set W)} (h : Knows (partition H) w R) :
    Karttunen1977.Knows H w R := by
  refine ⟨knowsAnswer_of_mem_core_strongAnswer (by rwa [strongAnswer_eq_cell]), fun h₀ v hv ↦ ?_⟩
  show trueAnswers H v = ∅
  rw [show trueAnswers H v = trueAnswers H w from h hv, h₀]

-- pp. 92–93
theorem knowsAnswer_of_forall_notMem {P : E → Set W} (h : ∀ x, w ∉ P x) :
    KnowsAnswer (Set.range P) w R := fun _ _ ↦ by
  rintro p ⟨⟨x, rfl⟩, hx⟩
  exact absurd hx (h x)

/-! Bill and Suzy at two indices. At `true` only Bill walks and at `false` both do; John cannot
tell the indices apart, and believes that both walk. -/

namespace Walkers

inductive Person | bill | suzy

/-- Bill walks at both indices, Suzy only at `false`. -/
def walk : Person → Set Bool
  | .bill => Set.univ
  | .suzy => {false}

/-- John's knowledge leaves both indices open. -/
def john : SetRel Bool Bool := Set.univ

/-- John believes that Bill and Suzy walk. -/
def johnBelieves : SetRel Bool Bool := {p | p.2 = false}

/-- Karttunen's postulate counts John as knowing who walks though he believes Suzy walks too,
against (VIII), and not as knowing who doesn't walk, against (X) (chapter II, pp. 86–88). -/
theorem karttunen_knows :
    Karttunen1977.Knows (Set.range walk) true john ∧ true ∈ johnBelieves.core (walk .suzy) ∧
      ¬ Karttunen1977.Knows (Set.range fun x ↦ (walk x)ᶜ) true john := by
  refine ⟨⟨fun v _ ↦ ?_, fun h ↦ absurd h (Set.nonempty_iff_ne_empty.1
      ⟨walk .bill, ⟨.bill, rfl⟩, trivial⟩)⟩, fun _ h ↦ h, fun ⟨h, _⟩ ↦ ?_⟩
  · rintro p ⟨⟨x, rfl⟩, hx⟩
    cases x
    · trivial
    · simp [walk] at hx
  · have := h (show true ~[john] false from trivial) (walk .suzy)ᶜ ⟨⟨.suzy, rfl⟩, by simp [walk]⟩
    simp [walk] at this

theorem not_knows : ¬ Knows (who walk) true john :=
  not_knows_who_of_believes (D := johnBelieves) (x := .suzy) (Set.subset_univ _) ⟨false, rfl⟩
    (fun _ h ↦ h) (by simp [walk])

end Walkers

/-! ### De dicto and de re readings

One individual at four indices, which record whether it is a man and whether it walks. The
actual index is `(true, false)` or `(true, true)`; each relation lists the indices John cannot
exclude. -/

namespace Men

/-- It is a man at the indices `(true, _)`. -/
def man : Unit → Set (Bool × Bool) := fun _ ↦ {w | w.1}

/-- It walks at the indices `(_, true)`. -/
def walk : Unit → Set (Bool × Bool) := fun _ ↦ {w | w.2}

/-- John knows that it does not walk but not that it is a man, the counter-model of chapter II,
p. 112. -/
def notMan : SetRel (Bool × Bool) (Bool × Bool) := {p | p.2 = (true, false) ∨ p.2 = (false, false)}

/-- John knows neither that it is a man nor that it does not walk. -/
def notManWalks : SetRel (Bool × Bool) (Bool × Bool) :=
  {p | p.2 = (true, false) ∨ p.2 = (false, true)}

/-- John knows that it walks but not that it is a man, the situation of chapter II, p. 89. -/
def notManButWalks : SetRel (Bool × Bool) (Bool × Bool) :=
  {p | p.2 = (true, true) ∨ p.2 = (false, true)}

theorem who_not_whichDeDicto :
    Knows (who walk) (true, true) notManButWalks ∧
      ¬ Knows (whichDeDicto man walk) (true, true) notManButWalks ∧
      ¬ who walk ≤ whichDeDicto man walk := by
  have hw : Knows (who walk) (true, true) notManButWalks := fun v hv ↦ by
    rcases hv with rfl | rfl <;> exact who_iff.2 fun _ ↦ by simp [walk]
  have hn : ¬ Knows (whichDeDicto man walk) (true, true) notManButWalks := fun h ↦ by
    have := who_iff.1 (h (show (true, true) ~[notManButWalks] (false, true) from Or.inr rfl)) ()
    simp [man, walk] at this
  exact ⟨hw, hn, fun h ↦ hn (hw.mono h)⟩

theorem whichDeDicto_compl_invalid :
    Knows (whichDeDicto man walk) (true, false) notMan ∧
      Knows (whichDeRe man walk (true, false)) (true, false) notMan ∧
      ¬ Knows (whichDeDicto man fun x ↦ (walk x)ᶜ) (true, false) notMan := by
  refine ⟨fun v hv ↦ ?_, fun v hv ↦ ?_, fun h ↦ ?_⟩
  · rcases hv with rfl | rfl <;> exact who_iff.2 fun _ ↦ by simp [man, walk]
  · rcases hv with rfl | rfl <;> exact whichDeRe_iff.2 fun _ _ ↦ by simp [walk]
  · have := who_iff.1 (h (show (true, false) ~[notMan] (false, false) from Or.inr rfl)) ()
    simp [man, walk] at this

theorem whichDeDicto_whichDeRe_compl_invalid :
    Knows (whichDeDicto man walk) (true, false) notManWalks ∧
      ¬ Knows (whichDeRe man (fun x ↦ (walk x)ᶜ) (true, false)) (true, false) notManWalks := by
  refine ⟨fun v hv ↦ ?_, fun h ↦ ?_⟩
  · rcases hv with rfl | rfl <;> exact who_iff.2 fun _ ↦ by simp [man, walk]
  · have := whichDeRe_iff.1
      (h (show (true, false) ~[notManWalks] (false, true) from Or.inr rfl)) () rfl
    simp [walk] at this

/-- The de dicto and de re readings of *John knows which man walks* are logically independent
(chapter II, p. 90). -/
theorem readings_independent :
    (Knows (whichDeRe man walk (true, true)) (true, true) notManButWalks ∧
        ¬ Knows (whichDeDicto man walk) (true, true) notManButWalks) ∧
      Knows (whichDeDicto man walk) (true, false) notManWalks ∧
        ¬ Knows (whichDeRe man walk (true, false)) (true, false) notManWalks := by
  refine ⟨⟨(who_not_whichDeDicto.1).mono (who_le_whichDeRe man walk _),
    who_not_whichDeDicto.2.1⟩, whichDeDicto_whichDeRe_compl_invalid.1, fun h ↦ ?_⟩
  have := whichDeRe_iff.1 (h (show (true, false) ~[notManWalks] (false, true) from Or.inr rfl))
    () rfl
  simp [walk] at this

-- (7)
theorem whichDeDicto_not_le :
    ¬ whichDeDicto man walk ≤ whichDeDicto man (fun x ↦ (walk x)ᶜ) ∧
      ¬ whichDeDicto man (fun x ↦ (walk x)ᶜ) ≤ whichDeDicto man walk := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := who_iff.1 (h (x := (true, false)) (y := (false, false))
      (who_iff.2 fun _ ↦ by simp [man, walk])) ()
    simp [man, walk] at this
  · have := who_iff.1 (h (x := (true, true)) (y := (false, true))
      (who_iff.2 fun _ ↦ by simp [man, walk])) ()
    simp [man, walk] at this

end Men

/-! ### Information and answers -/

section Information

variable {J K : Set W} {i : W}

/-- The semantic answers to `Q` compatible with the information `J` (chapter IV, (14)). -/
def compatible (Q : Setoid W) (J : Set W) : Set (Set W) := {X ∈ Q.classes | (X ∩ J).Nonempty}

/-- The partition that `Q` makes on `J`, whose blocks are the traces on `J` of the compatible
answers (chapter IV, (15)). -/
def restrict (Q : Setoid W) (J : Set W) : Set (Set W) := (· ∩ J) '' compatible Q J

/-- `J` offers an answer to `Q` when the partition `Q` makes on `J` has the single block `J`
(chapter IV, (20)). -/
def OffersAnswer (Q : Setoid W) (J : Set W) : Prop := restrict Q J = {J}

theorem cell_inter_mem_restrict (hw : w ∈ J) : Q.cell w ∩ J ∈ restrict Q J :=
  ⟨Q.cell w, ⟨Q.mem_classes w, w, Q.refl' w, hw⟩, rfl⟩

theorem offersAnswer_iff : OffersAnswer Q J ↔ J.Nonempty ∧ ∃ w, J ⊆ Q.cell w := by
  refine ⟨fun h ↦ ?_, fun ⟨⟨w, hw⟩, u, hu⟩ ↦ ?_⟩
  · obtain ⟨X, ⟨⟨u, rfl⟩, w, -, hwJ⟩, hXJ⟩ : J ∈ restrict Q J := h ▸ Set.mem_singleton J
    exact ⟨⟨w, hwJ⟩, u, fun v hv ↦ by rw [← hXJ] at hv; exact hv.1⟩
  · refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
    · have e : Q.cell w ∩ J = J :=
        Set.inter_eq_right.2 fun v hv ↦ Q.trans' (hu hv) (Q.symm' (hu hw))
      have := cell_inter_mem_restrict (Q := Q) hw
      rwa [e] at this
    · rintro _ ⟨X, ⟨⟨z, rfl⟩, y, hyX, hyJ⟩, rfl⟩
      exact Set.inter_eq_right.2 fun v hv ↦ Q.trans' (hu hv) (Q.trans' (Q.symm' (hu hyJ)) hyX)

theorem offersAnswer_iff_of_mem (hi : i ∈ J) : OffersAnswer Q J ↔ J ⊆ Q.cell i := by
  rw [offersAnswer_iff]
  refine ⟨fun ⟨_, v, hJ⟩ ↦ ?_, fun h ↦ ⟨⟨i, hi⟩, i, h⟩⟩
  rwa [cell_eq_of_rel (hJ hi)]

theorem offersAnswer_iff_mem_fromSetoid : OffersAnswer Q J ↔ J.Nonempty ∧ J ∈ fromSetoid Q := by
  rw [offersAnswer_iff, mem_fromSetoid]
  exact and_congr_right fun ⟨w, hw⟩ ↦ ⟨fun ⟨u, hu⟩ a ha b hb ↦ Q.trans' (hu ha) (Q.symm' (hu hb)),
    fun h ↦ ⟨w, fun a ha ↦ h a ha w hw⟩⟩

-- (18)
theorem OffersAnswer.anti (h : OffersAnswer Q K) (hJK : J ⊆ K) (hJ : J.Nonempty) :
    OffersAnswer Q J :=
  let ⟨_, u, hu⟩ := offersAnswer_iff.1 h
  offersAnswer_iff.2 ⟨hJ, u, hJK.trans hu⟩

/-- `J` offers a true answer at `i` when `J` with `i` added still offers an answer (chapter IV,
(23)). -/
def OffersTrueAnswer (Q : Setoid W) (J : Set W) (i : W) : Prop := OffersAnswer Q (insert i J)

theorem offersTrueAnswer_iff : OffersTrueAnswer Q J i ↔ J ⊆ Q.cell i := by
  rw [OffersTrueAnswer, offersAnswer_iff_of_mem (Set.mem_insert i J), Set.insert_subset_iff]
  exact and_iff_right (mem_cell_self i)

theorem offersTrueAnswer_iff_of_mem (hi : i ∈ J) : OffersTrueAnswer Q J i ↔ OffersAnswer Q J := by
  rw [OffersTrueAnswer, Set.insert_eq_of_mem hi]

/-- `J` is closer to an answer to `Q` than `K` when it lies within `K` and fewer semantic answers
are compatible with it (chapter IV, (30)). -/
def CloserToAnswer (Q : Setoid W) (J K : Set W) : Prop := J ⊆ K ∧ compatible Q J ⊂ compatible Q K

/-- `J` gives access to the true answer at `i` when the cell of `i` is compatible with it
(chapter IV, (31)). -/
def GivesAccess (Q : Setoid W) (J : Set W) (i : W) : Prop := Q.cell i ∈ compatible Q J

theorem givesAccess_iff : GivesAccess Q J i ↔ (Q.cell i ∩ J).Nonempty :=
  and_iff_right (Q.mem_classes i)

theorem closerToAnswer_iff :
    CloserToAnswer Q J K ↔ (∀ v ∈ J, v ∈ K) ∧
      (∀ w, (Q.cell w ∩ J).Nonempty → (Q.cell w ∩ K).Nonempty) ∧
      ∃ w, (Q.cell w ∩ K).Nonempty ∧ ¬ (Q.cell w ∩ J).Nonempty := by
  refine and_congr_right fun _ ↦ ?_
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · rintro ⟨hsub, hne⟩
    refine ⟨fun w hw ↦ (hsub ⟨Q.mem_classes w, hw⟩).2, ?_⟩
    by_contra h
    refine hne (hsub.antisymm ?_)
    rintro X ⟨⟨w, rfl⟩, hX⟩
    exact ⟨Q.mem_classes w, by_contra fun hn ↦ h ⟨w, hX, hn⟩⟩
  · rintro ⟨hmono, w, hK, hJ⟩
    refine ⟨?_, fun heq ↦ hJ ?_⟩
    · rintro X ⟨⟨u, rfl⟩, hX⟩
      exact ⟨Q.mem_classes u, hmono u hX⟩
    · exact (show Q.cell w ∈ compatible Q J from heq ▸ ⟨Q.mem_classes w, hK⟩).2

instance [Fintype W] {s : Set W} [DecidablePred (· ∈ s)] : Decidable s.Nonempty :=
  decidable_of_iff (∃ v, v ∈ s) Iff.rfl

instance [Fintype E] (P : E → Set W) [∀ x, DecidablePred (· ∈ P x)] : DecidableRel (who P) :=
  fun _ _ ↦ decidable_of_iff _ who_iff.symm

instance [Fintype W] [DecidableRel Q] [DecidablePred (· ∈ J)] : Decidable (OffersAnswer Q J) :=
  decidable_of_iff (J.Nonempty ∧ ∃ w, ∀ v, v ∈ J → Q v w) offersAnswer_iff.symm

instance [Fintype W] [DecidableRel Q] [DecidablePred (· ∈ J)] [DecidablePred (· ∈ K)] :
    Decidable (CloserToAnswer Q J K) :=
  decidable_of_iff _ closerToAnswer_iff.symm

instance [Fintype W] [DecidableRel Q] [DecidablePred (· ∈ J)] : Decidable (GivesAccess Q J i) :=
  decidable_of_iff _ givesAccess_iff.symm

variable (i) in
/-- An individual's information at the index `i` consists of the indices compatible with what
they believe, a nonempty set, among those compatible with what they know, which contain `i`
(chapter IV, (21)). -/
structure InformationSets where
  /-- The indices compatible with what the individual believes. -/
  doxastic : Set W
  /-- The indices compatible with what the individual knows. -/
  epistemic : Set W
  doxastic_subset : doxastic ⊆ epistemic
  doxastic_nonempty : doxastic.Nonempty
  mem_epistemic : i ∈ epistemic

namespace InformationSets

variable (S : InformationSets i) (Q : Setoid W)

/-- The individual has an answer when their beliefs offer one (chapter IV, (24)). -/
def HasAnswer : Prop := OffersAnswer Q S.doxastic

/-- The individual has a true answer when their beliefs offer a true one. -/
def HasTrueAnswer : Prop := OffersTrueAnswer Q S.doxastic i

/-- The individual knows an answer when their knowledge offers one. -/
def KnowsAnswer : Prop := OffersAnswer Q S.epistemic

variable {S Q}

theorem knowsAnswer_iff : S.KnowsAnswer Q ↔ S.epistemic ⊆ Q.cell i :=
  offersAnswer_iff_of_mem S.mem_epistemic

theorem offersTrueAnswer_epistemic_iff : OffersTrueAnswer Q S.epistemic i ↔ S.KnowsAnswer Q :=
  offersTrueAnswer_iff_of_mem S.mem_epistemic

-- p. 226
theorem KnowsAnswer.hasTrueAnswer (h : S.KnowsAnswer Q) : S.HasTrueAnswer Q :=
  offersTrueAnswer_iff.2 (S.doxastic_subset.trans (knowsAnswer_iff.1 h))

-- p. 226
theorem HasTrueAnswer.hasAnswer (h : S.HasTrueAnswer Q) : S.HasAnswer Q :=
  OffersAnswer.anti h (Set.subset_insert i S.doxastic) S.doxastic_nonempty

theorem knows_iff_knowsAnswer (hR : R.image {i} = S.epistemic) :
    Knows Q i R ↔ S.KnowsAnswer Q := by
  rw [knowsAnswer_iff, ← hR, SetRel.image_subset_iff, Knows, Set.singleton_subset_iff]

open Classical in
/-- Updating with `P` adds `P` to the beliefs when they are consistent with it, and to the
knowledge when, further, `P` is true (chapter IV, (25)). -/
noncomputable def update (S : InformationSets i) (P : Set W) : InformationSets i where
  doxastic := if (S.doxastic ∩ P).Nonempty then S.doxastic ∩ P else S.doxastic
  epistemic := if i ∈ P ∧ (S.doxastic ∩ P).Nonempty then S.epistemic ∩ P else S.epistemic
  doxastic_subset := by
    split_ifs with hD hE hE
    exacts [Set.inter_subset_inter_left P S.doxastic_subset,
      Set.inter_subset_left.trans S.doxastic_subset, absurd hE.2 hD, S.doxastic_subset]
  doxastic_nonempty := by split_ifs with h; exacts [h, S.doxastic_nonempty]
  mem_epistemic := by split_ifs with h; exacts [⟨S.mem_epistemic, h.1⟩, S.mem_epistemic]

variable {P : Set W}

theorem update_doxastic_of_nonempty (h : (S.doxastic ∩ P).Nonempty) :
    (S.update P).doxastic = S.doxastic ∩ P := by
  simp [update, h]

theorem update_doxastic_of_not_nonempty (h : ¬ (S.doxastic ∩ P).Nonempty) :
    (S.update P).doxastic = S.doxastic := by
  simp [update, h]

theorem update_epistemic_of_mem (hi : i ∈ P) (h : (S.doxastic ∩ P).Nonempty) :
    (S.update P).epistemic = S.epistemic ∩ P := by
  simp [update, hi, h]

theorem update_epistemic_of_notMem (hi : i ∉ P) : (S.update P).epistemic = S.epistemic := by
  simp [update, hi]

/-- `P` gives the individual an answer to `Q` when updating with it gives them one (chapter IV,
(27) and (29)). -/
def GivesAnswer (S : InformationSets i) (P : Set W) (Q : Setoid W) : Prop :=
  (S.update P).HasAnswer Q

/-- `P` gives the individual a true answer when updating with it gives them a true one. -/
def GivesTrueAnswer (S : InformationSets i) (P : Set W) (Q : Setoid W) : Prop :=
  (S.update P).HasTrueAnswer Q

/-- `P` lets the individual know an answer when updating with it lets them know one. -/
def LetsKnow (S : InformationSets i) (P : Set W) (Q : Setoid W) : Prop :=
  (S.update P).KnowsAnswer Q

/-- What lets one know an answer gives a true answer (chapter IV, (28)). -/
theorem LetsKnow.givesTrueAnswer (h : S.LetsKnow P Q) : S.GivesTrueAnswer P Q :=
  KnowsAnswer.hasTrueAnswer h

-- (28)
theorem GivesTrueAnswer.givesAnswer (h : S.GivesTrueAnswer P Q) : S.GivesAnswer P Q :=
  HasTrueAnswer.hasAnswer h

/-- `P` gives the individual a partial answer to `Q` when updating their beliefs with it brings
them closer to an answer (chapter IV, (33)). -/
def GivesPartialAnswer (S : InformationSets i) (P : Set W) (Q : Setoid W) : Prop :=
  CloserToAnswer Q (S.update P).doxastic S.doxastic

/-- `P` gives a true partial answer when, further, the updated beliefs still give access to the
true answer (chapter IV, (32) and (33)). -/
def GivesTruePartialAnswer (S : InformationSets i) (P : Set W) (Q : Setoid W) : Prop :=
  S.GivesPartialAnswer P Q ∧ GivesAccess Q (S.update P).doxastic i

-- p. 235
theorem GivesAnswer.givesPartialAnswer (hQ : ¬ OffersAnswer Q S.doxastic)
    (h : S.GivesAnswer P Q) : S.GivesPartialAnswer P Q := by
  by_cases hne : (S.doxastic ∩ P).Nonempty
  swap
  · exact absurd (update_doxastic_of_not_nonempty hne ▸ h) hQ
  have h' : OffersAnswer Q (S.doxastic ∩ P) := update_doxastic_of_nonempty hne ▸ h
  rw [GivesPartialAnswer, update_doxastic_of_nonempty hne]
  refine ⟨Set.inter_subset_left, ?_⟩
  obtain ⟨-, u, hu⟩ := offersAnswer_iff.1 h'
  refine ⟨fun X ⟨hX, y, hyX, hyD, _⟩ ↦ ⟨hX, y, hyX, hyD⟩, fun hsub ↦ hQ ?_⟩
  obtain ⟨z, hzD, _⟩ := hne
  refine offersAnswer_iff.2 ⟨⟨z, hzD⟩, u, fun v hv ↦ ?_⟩
  obtain ⟨_, y, hyv, hyD, hyP⟩ := hsub ⟨Q.mem_classes v, v, Q.refl' v, hv⟩
  exact Q.trans' (Q.symm' hyv) (hu ⟨hyD, hyP⟩)

end InformationSets

end Information

/-! ### Figure 13 of chapter IV

Two individuals, `0` and `1`. An index records which of them is the F, a property true of
exactly one individual, and which of them G. At the actual index `1` is the F and only `0` G's.
The individual believes, wrongly, that `0` is the F, and knows, rightly, that exactly one
individual G's. -/

namespace Figure13

/-- An index records who is the F and who G's. -/
abbrev Index := Fin 2 × Finset (Fin 2)

/-- *Who G's?* -/
abbrev whoGs : Setoid Index := who fun a ↦ {w : Index | a ∈ w.2}

/-- *Who is the F?* -/
abbrev whoIsTheF : Setoid Index := who fun a ↦ {w : Index | w.1 = a}

theorem whoGs_iff {v w : Index} : whoGs v w ↔ v.2 = w.2 := by
  rw [who_iff, Finset.ext_iff]; rfl

theorem whoIsTheF_iff {v w : Index} : whoIsTheF v w ↔ v.1 = w.1 := by
  rw [who_iff]
  exact ⟨fun h ↦ (h w.1).2 rfl, fun h a ↦ by simp only [Set.mem_ofPred_eq, h]⟩

/-- The actual index. -/
def actual : Index := (1, {0})

/-- The individual's information at the actual index. -/
def info : InformationSets actual where
  doxastic := {(0, {0}), (0, {1})}
  epistemic := {(0, {0}), (0, {1}), (1, {0}), (1, {1})}
  doxastic_subset := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
    tauto
  doxastic_nonempty := ⟨(0, {0}), Set.mem_insert _ _⟩
  mem_epistemic := by simp [actual]

/-- That `0` is the one who G's, an answer that names the individual. -/
def byName : Set Index := {w | w.2 = {0}}

/-- That the F is the one who G's, an answer that describes the individual. -/
def byDescription : Set Index := {w | w.2 = {w.1}}

/-- That if anyone G's, the F does. -/
def ifAnyoneThenTheF : Set Index := {w | w.2.Nonempty → w.1 ∈ w.2}

/-- That nobody G's. -/
def nobody : Set Index := {w | w.2 = ∅}

/-- That everybody G's. -/
def everybody : Set Index := {w | w.2 = Finset.univ}

theorem not_offersAnswer :
    ¬ OffersAnswer whoGs info.doxastic ∧ ¬ OffersAnswer whoGs info.epistemic := by
  have hD : ¬ OffersAnswer whoGs info.doxastic := fun h ↦ by
    obtain ⟨-, v, h⟩ := offersAnswer_iff.1 h
    have h₀ := whoGs_iff.1 (h (show ((0 : Fin 2), ({0} : Finset (Fin 2))) ∈ info.doxastic from
      Set.mem_insert _ _))
    have h₁ := whoGs_iff.1 (h (show ((0 : Fin 2), ({1} : Finset (Fin 2))) ∈ info.doxastic from
      Set.mem_insert_of_mem _ rfl))
    exact absurd (h₀.trans h₁.symm) (by decide)
  exact ⟨hD, fun h ↦ hD (h.anti info.doxastic_subset info.doxastic_nonempty)⟩

theorem hasAnswer_whoIsTheF : info.HasAnswer whoIsTheF ∧ ¬ info.HasTrueAnswer whoIsTheF := by
  refine ⟨offersAnswer_iff.2 ⟨info.doxastic_nonempty, (0, {0}), ?_⟩, fun h ↦ ?_⟩
  · rintro w (rfl | rfl) <;> exact whoIsTheF_iff.2 rfl
  · have := whoIsTheF_iff.1 (offersTrueAnswer_iff.1 h (Set.mem_insert _ _))
    exact absurd this (by decide)

theorem independent :
    (byName ∩ byDescription).Nonempty ∧ (byName \ byDescription).Nonempty ∧
      (byDescription \ byName).Nonempty ∧ (byNameᶜ ∩ byDescriptionᶜ).Nonempty :=
  ⟨⟨(0, {0}), rfl, rfl⟩, ⟨(1, {0}), rfl, by simp [byDescription]⟩,
    ⟨(1, {1}), rfl, by simp [byName]⟩, ⟨(0, ∅), by simp [byName], by simp [byDescription]⟩⟩

theorem doxastic_inter_eq {P : Set Index} (h₀ : ((0 : Fin 2), ({0} : Finset (Fin 2))) ∈ P)
    (h₁ : ((0 : Fin 2), ({1} : Finset (Fin 2))) ∉ P) : info.doxastic ∩ P = {(0, {0})} := by
  ext w
  simp only [info, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  grind

theorem doxastic_inter_byName : info.doxastic ∩ byName = {(0, {0})} :=
  doxastic_inter_eq rfl (by simp [byName])

theorem doxastic_inter_byDescription : info.doxastic ∩ byDescription = {(0, {0})} :=
  doxastic_inter_eq rfl (by simp [byDescription])

theorem pragmatically_equivalent : info.doxastic ∩ byName = info.doxastic ∩ byDescription := by
  rw [doxastic_inter_byName, doxastic_inter_byDescription]

/-- Both answers give the individual a true answer to who G's. -/
theorem givesTrueAnswer :
    info.GivesTrueAnswer byName whoGs ∧ info.GivesTrueAnswer byDescription whoGs := by
  refine ⟨?_, ?_⟩ <;>
  · rw [InformationSets.GivesTrueAnswer, InformationSets.HasTrueAnswer,
      InformationSets.update_doxastic_of_nonempty
        (by simp [doxastic_inter_byName, doxastic_inter_byDescription])]
    simp only [doxastic_inter_byName, doxastic_inter_byDescription, offersTrueAnswer_iff,
      Set.singleton_subset_iff, mem_cell, whoGs_iff]
    rfl

/-- Only the answer by name lets the individual know who G's, since the description is false at
the actual index and so does not reach their knowledge. -/
theorem letsKnow_byName :
    info.LetsKnow byName whoGs ∧ ¬ info.LetsKnow byDescription whoGs := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rw [InformationSets.LetsKnow, InformationSets.knowsAnswer_iff,
      InformationSets.update_epistemic_of_mem (show actual ∈ byName from rfl)
        (by simp [doxastic_inter_byName])]
    exact fun w hw ↦ whoGs_iff.2 hw.2
  · rw [InformationSets.LetsKnow, InformationSets.knowsAnswer_iff,
      InformationSets.update_epistemic_of_notMem (by simp [byDescription, actual])] at h
    have := whoGs_iff.1 (h (show ((0 : Fin 2), ({1} : Finset (Fin 2))) ∈ info.epistemic by
      simp [info]))
    exact absurd this (by decide)

theorem givesTrueAnswer_ifAnyoneThenTheF : info.GivesTrueAnswer ifAnyoneThenTheF whoGs := by
  have h : info.doxastic ∩ ifAnyoneThenTheF = {(0, {0})} :=
    doxastic_inter_eq (fun _ ↦ by decide) (by simp [ifAnyoneThenTheF])
  rw [InformationSets.GivesTrueAnswer, InformationSets.HasTrueAnswer,
    InformationSets.update_doxastic_of_nonempty (by simp [h]), h, offersTrueAnswer_iff,
    Set.singleton_subset_iff]
  exact whoGs_iff.2 rfl

theorem not_givesAnswer_nobody_everybody :
    ¬ info.GivesAnswer nobody whoGs ∧ ¬ info.GivesAnswer everybody whoGs := by
  refine ⟨fun h ↦ not_offersAnswer.1 ?_, fun h ↦ not_offersAnswer.1 ?_⟩ <;>
  · rwa [InformationSets.GivesAnswer, InformationSets.HasAnswer,
      InformationSets.update_doxastic_of_not_nonempty] at h
    rintro ⟨w, hw, hP⟩
    simp only [info, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    simp only [nobody, everybody, Set.mem_ofPred_eq] at hP
    rcases hw with rfl | rfl <;> exact absurd hP (by decide)

/-- The description gives a true answer without letting the individual know one, so having a
true answer does not imply knowing one, and the belief that `0` is the F is an answer to who is
the F that is not true, so having an answer does not imply having a true one. -/
example : info.GivesTrueAnswer byDescription whoGs ∧ ¬ info.LetsKnow byDescription whoGs ∧
    info.HasAnswer whoIsTheF ∧ ¬ info.HasTrueAnswer whoIsTheF :=
  ⟨givesTrueAnswer.2, letsKnow_byName.2, hasAnswer_whoIsTheF⟩

end Figure13

/-! ### Figure 15 of chapter IV

Three individuals, `0` and `1` the M's and `2` the only F; an index is the set of individuals
who G there. The individual believes that someone but not everyone G's, and only `2` G's at the
actual index. -/

namespace Figure15

/-- An index records who G's. -/
abbrev Index := Finset (Fin 3)

/-- The proposition that `x` G's. -/
def G (x : Fin 3) : Set Index := {w | x ∈ w}

instance (x : Fin 3) : DecidablePred (· ∈ G x) := fun w ↦ inferInstanceAs (Decidable (x ∈ w))

/-- The actual index. -/
def actual : Index := {2}

/-- The indices at which someone but not everyone G's. -/
def someNotAll : Set Index := {w | w ≠ ∅ ∧ w ≠ Finset.univ}

instance : DecidablePred (· ∈ someNotAll) :=
  fun w ↦ inferInstanceAs (Decidable (w ≠ ∅ ∧ w ≠ Finset.univ))

/-- The individual's information at the actual index, with the same beliefs and knowledge. -/
def info : InformationSets actual where
  doxastic := someNotAll
  epistemic := someNotAll
  doxastic_subset := subset_rfl
  doxastic_nonempty := ⟨actual, by decide⟩
  mem_epistemic := by decide

theorem info_doxastic : info.doxastic = someNotAll := rfl

theorem update_doxastic {P : Set Index} (h : (someNotAll ∩ P).Nonempty) :
    (info.update P).doxastic = someNotAll ∩ P :=
  info.update_doxastic_of_nonempty h

theorem conditional_true_partial :
    info.GivesTruePartialAnswer {w | 0 ∈ w → 1 ∈ w} (who G) := by
  rw [InformationSets.GivesTruePartialAnswer, InformationSets.GivesPartialAnswer,
    update_doxastic ⟨actual, by decide, by decide⟩, info_doxastic]
  decide

theorem exhaustive_indefinite_partial_false :
    info.GivesPartialAnswer {w | ∃ x, x ≠ 2 ∧ w = {x}} (who G) ∧
      ¬ GivesAccess (who G) (info.update {w | ∃ x, x ≠ 2 ∧ w = {x}}).doxastic actual := by
  rw [InformationSets.GivesPartialAnswer, update_doxastic ⟨{0}, by decide, by decide⟩,
    info_doxastic]
  decide

-- p. 236
theorem indefinite_partial_false :
    info.GivesPartialAnswer {w | 0 ∈ w ∨ 1 ∈ w} (who G) ∧
      ¬ GivesAccess (who G) (info.update {w | 0 ∈ w ∨ 1 ∈ w}).doxastic actual := by
  rw [InformationSets.GivesPartialAnswer, update_doxastic ⟨{0}, by decide, by decide⟩,
    info_doxastic]
  decide

theorem exhaustive_indefinite_complete_true :
    info.GivesTrueAnswer {w | w = {2}} (who G) := by
  rw [InformationSets.GivesTrueAnswer, InformationSets.HasTrueAnswer,
    update_doxastic (P := {w | w = {2}}) ⟨actual, by decide, rfl⟩, offersTrueAnswer_iff]
  rintro _ ⟨-, rfl⟩
  exact (who G).refl' actual

end Figure15

/-! ### Comparing answers, appendix 2 of chapter V -/

/-- The union of the semantic answers to `Q` compatible with `P` (chapter V, appendix 2, (1)). -/
def determined (Q : Setoid W) (P : Set W) : Set W := ⋃₀ compatible Q P

/-- `P` gives a partial semantic answer to `Q` when it is compatible with some but not all of its
answers (chapter V, appendix 2, (2)). -/
def GivesPartialSemanticAnswer (P : Set W) (Q : Setoid W) : Prop :=
  determined Q P ≠ ∅ ∧ determined Q P ≠ Set.univ

/-- `P₁` is a more informative answer than `P₂` when it is compatible with fewer answers
(chapter V, appendix 2, (11)). -/
def MoreInformative (Q : Setoid W) (P₁ P₂ : Set W) : Prop := determined Q P₁ ⊂ determined Q P₂

/-- Of two equally informative answers, the weaker is the more standard (chapter V, appendix 2,
(12)). -/
def MoreStandard (Q : Setoid W) (P₁ P₂ : Set W) : Prop :=
  determined Q P₁ = determined Q P₂ ∧ P₂ ⊂ P₁

/-- `P₁` is a quantitatively better answer than `P₂` when it is more informative, or equally
informative and more standard (chapter V, appendix 2, (13)). -/
def Better (Q : Setoid W) (P₁ P₂ : Set W) : Prop := MoreInformative Q P₁ P₂ ∨ MoreStandard Q P₁ P₂

theorem determined_mono {P₁ P₂ : Set W} (h : P₁ ⊆ P₂) : determined Q P₁ ⊆ determined Q P₂ :=
  Set.sUnion_subset_sUnion fun _ ⟨hX, y, hyX, hyP⟩ ↦ ⟨hX, y, hyX, h hyP⟩

-- (4)
theorem determined_union (P₁ P₂ : Set W) :
    determined Q (P₁ ∪ P₂) = determined Q P₁ ∪ determined Q P₂ := by
  ext v
  simp only [determined, compatible, Set.mem_sUnion, Set.mem_sep_iff, Set.mem_union,
    Set.Nonempty, Set.mem_inter_iff]
  grind

-- (3)
theorem determined_inter_subset (P₁ P₂ : Set W) :
    determined Q (P₁ ∩ P₂) ⊆ determined Q P₁ ∩ determined Q P₂ :=
  Set.subset_inter (determined_mono Set.inter_subset_left) (determined_mono Set.inter_subset_right)

/-- Of two distinct compatible propositions, the first a partial answer, one is better, or their
conjunction or disjunction is a partial answer better than both (chapter V, appendix 2, (18)). -/
theorem better_or_inter_or_union {P₁ P₂ : Set W} (h₁ : GivesPartialSemanticAnswer P₁ Q)
    (h : (P₁ ∩ P₂).Nonempty) (hne : P₁ ≠ P₂) :
    Better Q P₁ P₂ ∨ Better Q P₂ P₁ ∨
      (GivesPartialSemanticAnswer (P₁ ∩ P₂) Q ∧ Better Q (P₁ ∩ P₂) P₁ ∧ Better Q (P₁ ∩ P₂) P₂) ∨
      (GivesPartialSemanticAnswer (P₁ ∪ P₂) Q ∧ Better Q (P₁ ∪ P₂) P₁ ∧
        Better Q (P₁ ∪ P₂) P₂) := by
  have hsub := determined_inter_subset (Q := Q) P₁ P₂
  have hu := determined_union (Q := Q) P₁ P₂
  have hne₁₂ : determined Q (P₁ ∩ P₂) ≠ ∅ := by
    obtain ⟨z, hz⟩ := h
    exact Set.nonempty_iff_ne_empty.1 ⟨z, _, ⟨Q.mem_classes z, z, Q.refl' z, hz⟩, Q.refl' z⟩
  unfold Better MoreInformative MoreStandard GivesPartialSemanticAnswer at *
  -- the paper's four cases (16): the conjunction compatible with as many answers as either
  -- conjunct, or fewer
  rcases eq_or_ne (determined Q (P₁ ∩ P₂)) (determined Q P₁) with e₁ | n₁ <;>
  rcases eq_or_ne (determined Q (P₁ ∩ P₂)) (determined Q P₂) with e₂ | n₂
  · by_cases u₁ : P₂ ⊆ P₁
    · grind [Set.ssubset_iff_subset_ne]
    by_cases u₂ : P₁ ⊆ P₂
    · grind [Set.ssubset_iff_subset_ne]
    grind [Set.ssubset_iff_subset_ne, Set.subset_union_left, Set.subset_union_right,
      Set.union_self, Set.subset_inter_iff]
  all_goals grind [Set.ssubset_iff_subset_ne, Set.subset_inter_iff, Set.eq_univ_of_univ_subset]

/-! Four indices in two cells, `{0, 1}` and `{2, 3}`. -/

namespace TwoCells

/-- The question whose cells are `{0, 1}` and `{2, 3}`. -/
abbrev cells : Setoid (Fin 4) := Setoid.ker fun i ↦ decide (i.val < 2)

theorem determined_inter_ne :
    determined cells ({0, 2} ∩ {1, 2}) ≠ determined cells {0, 2} ∩ determined cells {1, 2} :=
  fun h ↦ by
    have h₀ : (0 : Fin 4) ∈ determined cells ({0, 2} ∩ {1, 2}) := by
      rw [h]
      exact ⟨⟨_, ⟨cells.mem_classes 0, 0, cells.refl' 0, by simp⟩, cells.refl' 0⟩,
        ⟨_, ⟨cells.mem_classes 1, 1, cells.refl' 1, by simp⟩, show cells 0 1 by decide⟩⟩
    obtain ⟨X, ⟨⟨y, rfl⟩, z, hzX, hz₁, hz₂⟩, h₀X⟩ := h₀
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz₁ hz₂
    rcases hz₁ with rfl | rfl
    · exact absurd hz₂ (by decide)
    · exact absurd (cells.trans' h₀X (cells.symm' hzX) : cells 0 2) (by decide)

end TwoCells

/-! ### Mention-some knowledge, chapter VI, section 5.3

Someone knows who P's on the mention-some reading, (25) and (28), when of someone who P's they
know that they P, which is `Question.KnowsSomeAnswer` on the Hamblin set `Set.range P`. -/

/-- Knowing who has a pen gives the mention-some knowledge once someone has a pen (chapter VI,
p. 538). -/
theorem knowsSomeAnswer_of_knows {P : E → Set W} {x : E} (h : Knows (who P) w R)
    (hx : w ∈ P x) : KnowsSomeAnswer (Set.range P) w R :=
  ⟨P x, ⟨⟨x, rfl⟩, hx⟩, h.mem_core (who_decides P x) hx⟩

-- p. 538
theorem not_knowsSomeAnswer {P : E → Set W} (h : ∀ x, w ∉ P x) :
    ¬ KnowsSomeAnswer (Set.range P) w R :=
  fun ⟨_, ⟨⟨x, rfl⟩, hx⟩, _⟩ ↦ h x hx

-- p. 538
theorem mem_which_of_mem_fromSetoid {P : E → Set W} {s : Set W} {x : E}
    (hs : s ∈ fromSetoid (who P)) (hw : w ∈ s) (hx : w ∈ P x) : s ∈ which Set.univ P :=
  mem_which.2 (Or.inr ⟨x, trivial, fun v hv ↦ (who_iff.1 ((mem_fromSetoid.1 hs) v hv w hw) x).2 hx⟩)

-- p. 538
theorem givesPartialSemanticAnswer_of_subset {P : E → Set W} {s : Set W} {x : E} {v : W}
    (hs : s ⊆ P x) (hw : w ∈ s) (hv : v ∉ P x) :
    GivesPartialSemanticAnswer s (who P) ∧ w ∈ determined (who P) s := by
  have hmem : w ∈ determined (who P) s :=
    ⟨_, ⟨(who P).mem_classes w, w, (who P).refl' w, hw⟩, (who P).refl' w⟩
  refine ⟨⟨Set.nonempty_iff_ne_empty.1 ⟨w, hmem⟩, fun hu ↦ ?_⟩, hmem⟩
  have : v ∈ determined (who P) s := hu ▸ Set.mem_univ v
  obtain ⟨X, ⟨⟨y, rfl⟩, z, hzX, hzs⟩, hvX⟩ := this
  exact hv ((who_iff.1 ((who P).trans' hvX ((who P).symm' hzX)) x).2 (hs hzs))

end GroenendijkStokhof1984
