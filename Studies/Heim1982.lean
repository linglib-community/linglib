module

public import Mathlib.Data.Fin.VecNotation
public import Linglib.Semantics.Dynamic.FileChange
public import Linglib.Data.Examples.Heim1982

/-!
# Heim (1982): The Semantics of Definite and Indefinite Noun Phrases

This file formalizes the file change semantics of Chapter III of [heim-1982]: indefinites
and definites are alike variables, and they differ in a felicity condition on files, the
Extended Novelty-Familiarity-Condition (§2.4, §5.1): an indefinite's card must be new to the
file, a definite's already present and, if it has descriptive content, entailed by it.
Logical forms are interpreted by their file change potentials, the four rules of §4.4: an
atom filters the file and adds its cards, a cumulative formula updates in sequence, the
universal quantifier tests the file against its two auxiliary updates, and negation tests it
against one. The truth of an utterance is the truth of the resulting file, the truth half of
criterion (C) of §3.2, so Existential Closure is dispensable. The logical forms `LF` and the
rules `LF.fcp` are stated over the substrate's file change potentials. Principle (A) holds of
every rule at once (`fcp_isEliminative`), so an established card persists (`familiar_of_mem`)
and a card a formula does not introduce stays novel (`novel_of_mem`); the claims the
dissertation draws are proved on its own texts: felicity conditions project through the
elementary steps of file change (`admits_pretzel`), a card introduced under `every` or `not`
does not outlive its sentence (`not_admits_everyDog`), and criterion (C) gives a free indefinite
existential force (`trueIn_indef`).

## Implementation notes

A file is the substrate's `State` of world–assignment points, with felicity its
`Part`-definedness, satisfaction sets in place of `Sat(F)` and domains in place of `Dom(F)`;
principle (A) of §1.2, that an update only filters the satisfaction set, is the
informativeness order. Quantifier Indexing and Existential Closure are not represented, as
the revised rules make them dispensable. Accommodating a novel definite (§5.2) is modelled
by placing its indefinite card either inside the auxiliary file of a negation or in the
initial file. Examples are numbered as in the dissertation, by chapter and section.

A state has no domain apart from its points, so at the empty, false file every card is both
familiar and novel. Heim's files keep `Dom(F)` apart from `Sat(F)`, and her (16) and (17) are
infelicitous whether or not they are true; here `not_admits_everyDog` and `not_admits_noDog`
assume that the universal or negated first sentence is true in `F`, since a false one leaves an
empty file, at which the pronoun's card is vacuously familiar. Truth with respect to a file
(`FCP.trueIn`) is the consistency of the updated file. That is the truth clause of (C) for the
files of Chapter III, which carry no worlds; on points that carry worlds it is truth at some
world, and the falsity clause is not stated.

## References

* [heim-1982]
-/

@[expose] public section

namespace Heim1982

open DynamicSemantics

variable {W M : Type*} {n : ℕ}

/-- A file (Ch. III): a referential information state with numbered cards. -/
abbrev File (W M : Type*) := State W ℕ M

/-- Logical forms of the revised theory (Ch. III §4.4, §5.1): atomic formulas
over indexed variables, indefinite and definite noun phrases with their
descriptive content, cumulative (sequenced), universally quantified and
negated formulas. Predicates are interpreted directly. -/
inductive LF (M : Type*)
  | atom {n : ℕ} (ζ : (Fin n → M) → Prop) (args : Fin n → ℕ)
  | indef (i : ℕ) (N : M → Prop)
  | defNP (i : ℕ) (N : M → Prop)
  | seq (φ ψ : LF M)
  | every (φ₁ φ₂ : LF M)
  | neg (ψ : LF M)

namespace LF

/-- A pronoun or trace: a definite without descriptive content. -/
def pro (i : ℕ) : LF M := defNP i fun _ ↦ True

/-- A one-place predication at card `i`. -/
def pred₁ (N : M → Prop) (i : ℕ) : LF M := atom (fun m ↦ N (m 0)) fun _ : Fin 1 ↦ i

/-- A two-place predication at cards `i`, `j`. -/
def pred₂ (R : M → M → Prop) (i j : ℕ) : LF M := atom (fun m ↦ R (m 0) (m 1)) ![i, j]

/-- The proposition state of an atomic formula: the points with exactly the
atom's cards, whose values stand in `ζ`. -/
def atomState (ζ : (Fin n → M) → Prop) (args : Fin n → ℕ) : File W M :=
  {q | q.domain = Set.range args ∧ ∃ m : Fin n → M, (∀ k, q.assignment (args k) = ↑(m k)) ∧ ζ m}

/-- The file change of a one-place atom. -/
def unary (N : M → Prop) (i : ℕ) : FCP W ℕ M :=
  FCP.ofState (atomState (fun m ↦ N (m 0)) fun _ : Fin 1 ↦ i)

/-- Rules (I)–(IV) of Ch. III §4.4 with the Extended Novelty-Familiarity-
Condition of §5.1: an atom merges the file with its proposition state
(filtering at familiar cards, adding novel ones); an indefinite is defined
only if its card is novel and then introduces it; a definite is defined only
if its card is familiar and the file entails its content, and then changes
nothing; sequencing composes; `every` keeps the points of `F` all of whose
extensions in `F + φ₁` extend to `(F + φ₁) + φ₂`; `not` keeps the points of
`F` with no extension in `F + ψ`. -/
def fcp : LF M → FCP W ℕ M
  | atom ζ args => FCP.ofState (atomState ζ args)
  | indef i N => FCP.indef i (unary N i)
  | defNP i N => FCP.def_ i (unary N i)
  | seq φ ψ => φ.fcp.seq ψ.fcp
  | every φ₁ φ₂ => fun F ↦ (φ₁.fcp F).bind fun F₁ ↦ (φ₂.fcp F₁).map fun F₂ ↦
      {p ∈ F | ∀ q ∈ F₁, p ≤ q → ∃ r ∈ F₂, q ≤ r}
  | neg ψ => FCP.neg ψ.fcp

/-- The cards a logical form adds to the file: those of its atoms and
indefinites outside the scope of `every` and `not`, whose auxiliary files are
discarded. -/
def cards : LF M → Set ℕ
  | atom _ args => Set.range args
  | indef i _ => {i}
  | defNP _ _ => ∅
  | seq φ ψ => φ.cards ∪ ψ.cards
  | every _ _ => ∅
  | neg _ => ∅

theorem unary_eq_atomVar (N : M → Prop) (i : ℕ) : (unary N i : FCP W ℕ M) = FCP.atomVar N i := by
  refine congrArg FCP.ofState (Set.ext fun q ↦ ?_)
  constructor
  · rintro ⟨hd, m, hm, hN⟩
    exact ⟨hd.trans Set.range_const, m 0, hm 0, hN⟩
  · rintro ⟨hd, m, hm, hN⟩
    exact ⟨hd.trans Set.range_const.symm, fun _ ↦ m, fun _ ↦ hm, hN⟩

/-! ### The Extended Novelty-Familiarity-Condition -/

theorem admits_indef (i : ℕ) (N : M → Prop) (F : File W M) :
    (indef i N).fcp.Admits F ↔ State.Novel F i :=
  (FCP.admits_indef _).trans ⟨fun ⟨h, _⟩ ↦ h, fun h ↦ ⟨h, trivial⟩⟩

theorem admits_defNP (i : ℕ) (N : M → Prop) (F : File W M) :
    (defNP i N).fcp.Admits F ↔
      State.Familiar F i ∧ (unary N i).supports F :=
  FCP.admits_def_ _

theorem supports_unary_true (F : File W M) {i : ℕ} (h : State.Familiar F i) :
    (unary (fun _ ↦ True) i).supports F := by
  rw [PartialUpdate.supports_iff_eq_some, unary_eq_atomVar, FCP.atomVar_eq_of_familiar _ h]
  exact congrArg Part.some (Set.sep_eq_self_iff_mem_true.mpr fun p hp ↦
    let ⟨m, hm⟩ := Flat.ne_bot_iff_exists.1 (h p hp); ⟨m, hm, trivial⟩)

theorem fcp_pro (F : File W M) {i : ℕ} (h : State.Familiar F i) : (pro i).fcp F = Part.some F :=
  FCP.def_apply _ ⟨h, supports_unary_true F h⟩

theorem admits_pro (F : File W M) (i : ℕ) : (pro i).fcp.Admits F ↔ State.Familiar F i :=
  ⟨fun ⟨h, _⟩ ↦ h.1, fun h ↦ by rw [PartialUpdate.Admits, fcp_pro F h]; trivial⟩

theorem fcp_indef {F : File W M} {i : ℕ} (N : M → Prop) (h : State.Novel F i) :
    (indef i N).fcp F = Part.some {p ∈ F.randomAssign i | ∃ m : M, p.assignment i = ↑m ∧ N m} := by
  show FCP.indef i (unary N i) F = _
  rw [FCP.indef_apply _ h, unary_eq_atomVar,
    FCP.atomVar_eq_of_familiar _ (State.familiar_randomAssign F i)]

theorem mem_fcp_indef {F F' : File W M} {i : ℕ} {N : M → Prop} :
    F' ∈ (indef i N).fcp F ↔
      State.Novel F i ∧ F' = {p ∈ F.randomAssign i | ∃ m : M, p.assignment i = ↑m ∧ N m} :=
  ⟨fun h ↦ have hn : State.Novel F i := (Part.mem_assert_iff.mp h).1
    ⟨hn, Part.mem_some_iff.mp (fcp_indef N hn ▸ h)⟩,
   fun ⟨hn, hF⟩ ↦ hF ▸ fcp_indef N hn ▸ Part.mem_some _⟩

/-! ### Membership and projection through the rules -/

theorem mem_fcp_seq {φ ψ : LF M} {F F' : File W M} :
    F' ∈ (φ.seq ψ).fcp F ↔ ∃ F₁ ∈ φ.fcp F, F' ∈ ψ.fcp F₁ :=
  Part.mem_bind_iff

theorem mem_fcp_every {φ₁ φ₂ : LF M} {F F' : File W M} :
    F' ∈ (every φ₁ φ₂).fcp F ↔ ∃ F₁ ∈ φ₁.fcp F, ∃ F₂ ∈ φ₂.fcp F₁,
      F' = {p ∈ F | ∀ q ∈ F₁, p ≤ q → ∃ r ∈ F₂, q ≤ r} := by
  simp only [fcp, Part.mem_bind_iff, Part.mem_map_iff]
  exact exists_congr fun _ ↦ and_congr_right fun _ ↦ exists_congr fun _ ↦
    and_congr_right fun _ ↦ eq_comm

theorem subset_of_mem_fcp_every {φ₁ φ₂ : LF M} {F F' : File W M}
    (h : F' ∈ (every φ₁ φ₂).fcp F) : F' ⊆ F := by
  obtain ⟨_, -, _, -, rfl⟩ := mem_fcp_every.mp h
  exact fun _ hp ↦ hp.1

theorem admits_seq_of_mem {φ ψ : LF M} {F F' : File W M} (h : F' ∈ φ.fcp F)
    (h' : ψ.fcp.Admits F') : (φ.seq ψ).fcp.Admits F :=
  Part.dom_iff_mem.mpr ⟨_, mem_fcp_seq.mpr ⟨F', h, Part.get_mem h'⟩⟩

theorem admits_pro_seq {ψ : LF M} {F : File W M} {i : ℕ} (h : State.Familiar F i)
    (h' : ψ.fcp.Admits F) : ((pro i).seq ψ).fcp.Admits F :=
  admits_seq_of_mem (by rw [fcp_pro F h]; exact Part.mem_some F) h'

theorem admits_every_of_mem {φ₁ φ₂ : LF M} {F F₁ : File W M} (h : F₁ ∈ φ₁.fcp F)
    (h' : φ₂.fcp.Admits F₁) : (every φ₁ φ₂).fcp.Admits F :=
  Part.dom_iff_mem.mpr ⟨_, mem_fcp_every.mpr ⟨F₁, h, _, Part.get_mem h', rfl⟩⟩

theorem every_eq_cond (φ₁ φ₂ : LF M) :
    (every φ₁ φ₂).fcp = FCP.cond (W := W) φ₁.fcp φ₂.fcp := by
  funext F
  simp only [fcp, FCP.cond, FCP.neg, PartialUpdate.seq, PFun.comp_apply, Part.map_bind,
    Part.map_map]
  refine congrArg (Part.bind _) (funext fun F₁ ↦
    congrArg (fun g ↦ Part.map g (φ₂.fcp F₁)) (funext fun F₂ ↦ Set.ext fun p ↦ ?_))
  simp only [Function.comp, Set.mem_ofPred_eq, mem_lowerClosure, not_exists, not_and]
  exact and_congr_right fun _ ↦ forall_congr' fun q ↦
    ⟨fun h ⟨hq, hno⟩ hpq ↦ let ⟨r, hr, hqr⟩ := h hq hpq; hno r hr hqr,
     fun h hq hpq ↦ Classical.byContradiction fun hne ↦
      h ⟨hq, fun r hr hqr ↦ hne ⟨r, hr, hqr⟩⟩ hpq⟩

theorem admits_every (φ₁ φ₂ : LF M) (F : File W M) :
    (every φ₁ φ₂).fcp.Admits F ↔ ∃ h : φ₁.fcp.Admits F, φ₂.fcp.Admits ((φ₁.fcp F).get h) := by
  rw [every_eq_cond]; exact FCP.admits_cond

/-! ### Principle (A) of §1.2 and the cards through the rules

Every rule only adds information, so a card once established stays
established; the cards a rule can add are those the logical form introduces,
so a card it does not introduce stays novel. -/

theorem fcp_isEliminative : ∀ φ : LF M, (φ.fcp : FCP W ℕ M).IsEliminative
  | atom _ _ => FCP.isEliminative_ofState _
  | indef i _ => (FCP.isEliminative_ofState _).indef i
  | defNP i _ => FCP.isEliminative_def_ i _
  | seq φ ψ => (fcp_isEliminative φ).seq (fcp_isEliminative ψ)
  | every φ₁ φ₂ => by rw [every_eq_cond]; exact FCP.isEliminative_cond _ _
  | neg _ => FCP.isEliminative_neg _

-- §3.2
theorem fcp_empty (φ : LF M) {F' : File W M} (h : F' ∈ φ.fcp ∅) : F' = ∅ :=
  (fcp_isEliminative φ).eq_empty_of_mem h

theorem familiar_of_mem {φ : LF M} {F F' : File W M} {j : ℕ} (hj : State.Familiar F j)
    (h : F' ∈ φ.fcp F) : State.Familiar F' j :=
  (fcp_isEliminative φ).familiar hj h

theorem familiar_of_mem_indef {F F' : File W M} {i : ℕ} {N : M → Prop}
    (h : F' ∈ (indef i N).fcp F) : State.Familiar F' i := by
  obtain ⟨-, rfl⟩ := mem_fcp_indef.mp h
  exact (State.familiar_randomAssign F i).mono fun _ hp ↦ hp.1

theorem novel_atomState {ζ : (Fin n → M) → Prop} {args : Fin n → ℕ} {j : ℕ}
    (hj : j ∉ Set.range args) : State.Novel (atomState (W := W) ζ args) j :=
  fun _ ⟨hq, _⟩ ↦ by_contra fun hd ↦ hj (hq ▸ Possibility.mem_domain.mpr hd)

theorem novel_of_mem : ∀ {φ : LF M} {F F' : File W M} {j : ℕ}, j ∉ φ.cards →
    State.Novel F j → F' ∈ φ.fcp F → State.Novel F' j
  | atom _ _, _, _, _, hj, hF, h => FCP.mem_ofState.mp h ▸ hF.mul (novel_atomState hj)
  | indef _ _, F, _, _, hj, hF, h => by
    obtain ⟨-, rfl⟩ := mem_fcp_indef.mp h
    exact (hF.randomAssign (Set.notMem_singleton_iff.mp hj)).mono fun _ hp ↦ hp.1
  | defNP _ _, _, _, _, _, hF, h => by
    obtain ⟨-, h⟩ := Part.mem_assert_iff.mp h
    exact Part.mem_some_iff.mp h ▸ hF
  | seq φ ψ, _, _, _, hj, hF, h => by
    obtain ⟨_, h₁, h₂⟩ := mem_fcp_seq.mp h
    exact novel_of_mem (fun hψ ↦ hj (Set.mem_union_right _ hψ))
      (novel_of_mem (fun hφ ↦ hj (Set.mem_union_left _ hφ)) hF h₁) h₂
  | every _ _, _, _, _, _, hF, h => hF.mono (subset_of_mem_fcp_every h)
  | neg _, _, _, _, _, hF, h => hF.mono (FCP.subset_of_mem_neg h)

/-! ### Truth (§3.2)

Criterion (C): an utterance is true with respect to a file iff the resulting
file is true, i.e. has a satisfying point (`FCP.trueIn`). No existential
closure is needed: a novel card ranges over the whole domain, a familiar one
over the values its card admits. -/

theorem trueIn_indef {F : File W M} {i : ℕ} (N : M → Prop) (h : State.Novel F i) :
    FCP.trueIn F (indef i N).fcp ↔ F.Nonempty ∧ ∃ m, N m := by
  simp only [FCP.trueIn, fcp_indef N h, Part.mem_some_iff, exists_eq_left]
  constructor
  · rintro ⟨p, hp, m', hm', hN⟩
    obtain ⟨q, hq, m, rfl⟩ := hp
    obtain rfl : m = m' := by simpa [Possibility.update] using hm'
    exact ⟨⟨q, hq⟩, _, hN⟩
  · rintro ⟨⟨q, hq⟩, m, hN⟩
    exact ⟨q.update i ↑m, ⟨q, hq, m, rfl⟩, m, by simp [Possibility.update], hN⟩

theorem trueIn_pro_pred {F : File W M} {i : ℕ} (N : M → Prop) (h : State.Familiar F i) :
    FCP.trueIn F ((pro i).seq (pred₁ N i)).fcp ↔ ∃ p ∈ F, ∃ m : M, p.assignment i = ↑m ∧ N m := by
  have : ((pro i).seq (pred₁ N i)).fcp F = FCP.atomVar N i F := by
    show ((pro i).fcp F).bind _ = _
    rw [fcp_pro F h, Part.bind_some]
    exact congrFun (unary_eq_atomVar N i) F
  simp only [FCP.trueIn, this, FCP.atomVar_eq_of_familiar _ h, Part.mem_some_iff,
    exists_eq_left, Set.Nonempty, Set.mem_ofPred_eq]

end LF

/-! ### The book's texts -/

section Texts

open LF

variable (dog cameIn layDown woman person pretzel king : M → Prop)
  (bit hit bought ate lunch : M → M → Prop)

/-- Ch. I §1 (9): "A dog₁ came in. It₁ lay down under the table." -/
def aDog : LF M := (indef 1 dog).seq ((pred₁ cameIn 1).seq ((pro 1).seq (pred₁ layDown 1)))

/-- Ch. I §1 (16): "Every dog₁ came in. It₁ lay down under the table." -/
def everyDog : LF M :=
  (every (indef 1 dog) (pred₁ cameIn 1)).seq ((pro 1).seq (pred₁ layDown 1))

/-- Ch. I §1 (17): "No dog₁ came in. It₁ lay down under the table." -/
def noDog : LF M := (neg ((indef 1 dog).seq (pred₁ cameIn 1))).seq ((pro 1).seq (pred₁ layDown 1))

/-- Ch. III §2.4 (5): "A woman₁ was bitten by a dog₂. She₁ hit him₂." -/
def womanDog : LF M :=
  (indef 1 woman).seq ((indef 2 dog).seq ((pred₂ bit 2 1).seq ((pro 1).seq
    ((pro 2).seq (pred₂ hit 1 2)))))

/-- Ch. III §4.1 (2): "Everyone₁ bought a pretzel₂ and ate it₂." -/
def pretzelText : LF M :=
  every (indef 1 person) ((indef 2 pretzel).seq ((pred₂ bought 1 2).seq ((pro 2).seq
    (pred₂ ate 1 2))))

/-- Ch. III §5.2 (10) with the king's card accommodated in the auxiliary file of the
negation. -/
def kingLocal (m i : ℕ) : LF M := neg ((indef i king).seq (pred₂ lunch m i))

/-- Ch. III §5.2 (10) with the king's card accommodated in the initial file. -/
def kingGlobal (m i : ℕ) : LF M := (indef i king).seq (neg (pred₂ lunch m i))

variable {dog cameIn layDown woman person pretzel king bit hit bought ate lunch}

-- (9)
theorem admits_aDog {F : File W M} (h : State.Novel F 1) :
    (aDog dog cameIn layDown).fcp.Admits F := by
  unfold aDog
  have m1 := mem_fcp_indef (F := F) (N := dog).mpr ⟨h, rfl⟩
  exact admits_seq_of_mem m1 (admits_seq_of_mem (Part.mem_some _) (admits_pro_seq
    (familiar_of_mem (φ := pred₁ cameIn 1) (familiar_of_mem_indef m1) (Part.mem_some _)) trivial))

/-- (16) is infelicitous whenever card 1 is novel and the universal sentence is true. -/
theorem not_admits_everyDog {F : File W M} (h : State.Novel F 1)
    (ht : FCP.trueIn F (every (indef 1 dog) (pred₁ cameIn 1)).fcp) :
    ¬ (everyDog dog cameIn layDown).fcp.Admits F := by
  rintro ⟨hd, hrest⟩
  obtain ⟨F', hF', p, hp⟩ := ht
  obtain rfl := Part.get_eq_of_mem hF' hd
  obtain ⟨hpro, -⟩ := hrest
  have hf : State.Familiar _ 1 := hpro.1.1
  exact hf p hp (h p (subset_of_mem_fcp_every hF' hp))

-- (17)
theorem not_admits_noDog {F : File W M} (h : State.Novel F 1)
    (ht : FCP.trueIn F (neg ((indef 1 dog).seq (pred₁ cameIn 1))).fcp) :
    ¬ (noDog dog cameIn layDown).fcp.Admits F := by
  rintro ⟨hd, hrest⟩
  obtain ⟨F', hF', p, hp⟩ := ht
  obtain rfl := Part.get_eq_of_mem hF' hd
  obtain ⟨hpro, -⟩ := hrest
  have hf : State.Familiar _ 1 := hpro.1.1
  exact hf p hp (h p (FCP.subset_of_mem_neg hF' hp))

-- §2.4, (5)
theorem admits_womanDog {F : File W M} (h1 : State.Novel F 1) (h2 : State.Novel F 2) :
    (womanDog dog woman bit hit).fcp.Admits F := by
  unfold womanDog
  have m1 := mem_fcp_indef (F := F) (N := woman).mpr ⟨h1, rfl⟩
  have m2 := mem_fcp_indef (N := dog).mpr ⟨novel_of_mem (by simp [cards]) h2 m1, rfl⟩
  have f1 := familiar_of_mem (φ := pred₂ bit 2 1)
    (familiar_of_mem (φ := indef 2 dog) (familiar_of_mem_indef m1) m2) (Part.mem_some _)
  have f2 := familiar_of_mem (φ := pred₂ bit 2 1) (familiar_of_mem_indef m2) (Part.mem_some _)
  exact admits_seq_of_mem m1 (admits_seq_of_mem m2 (admits_seq_of_mem (Part.mem_some _)
    (admits_pro_seq f1 (admits_pro_seq f2 trivial))))

/-- §4.1 (2) is felicitous against a file at which cards 1 and 2 are novel. -/
theorem admits_pretzel {F : File W M} (h1 : State.Novel F 1) (h2 : State.Novel F 2) :
    (pretzelText person pretzel bought ate).fcp.Admits F := by
  unfold pretzelText
  have m1 := mem_fcp_indef (F := F) (N := person).mpr ⟨h1, rfl⟩
  have m2 := mem_fcp_indef (N := pretzel).mpr ⟨novel_of_mem (by simp [cards]) h2 m1, rfl⟩
  have f2 := familiar_of_mem (φ := pred₂ bought 1 2) (familiar_of_mem_indef m2) (Part.mem_some _)
  exact admits_every_of_mem m1 (admits_seq_of_mem m2 (admits_seq_of_mem (Part.mem_some _)
    (admits_pro_seq f2 trivial)))

-- §5.2
theorem novel_of_mem_kingLocal {F F' : File W M} {m i : ℕ} (h : State.Novel F i)
    (hF' : F' ∈ (kingLocal king lunch m i).fcp F) : State.Novel F' i :=
  novel_of_mem (φ := kingLocal king lunch m i) (Set.notMem_empty i) h hF'

-- §5.2
theorem familiar_of_mem_kingGlobal {F F' : File W M} {m i : ℕ}
    (hF' : F' ∈ (kingGlobal king lunch m i).fcp F) :
    State.Familiar F' i ∧ ∀ p ∈ F', ∃ x : M, p.assignment i = ↑x ∧ king x := by
  obtain ⟨F₁, h₁, h₂⟩ := mem_fcp_seq.mp hF'
  have hsub := FCP.subset_of_mem_neg h₂
  refine ⟨(familiar_of_mem_indef h₁).mono hsub, fun p hp ↦ ?_⟩
  obtain ⟨-, rfl⟩ := mem_fcp_indef.mp h₁
  exact (hsub hp).2

end Texts

end Heim1982
