module

public import Mathlib.Data.Fin.VecNotation
public import Linglib.Semantics.Dynamic.FileChange
public import Linglib.Data.Examples.Heim1982

/-!
# Heim (1982): The Semantics of Definite and Indefinite Noun Phrases

This file formalizes the file change semantics of Chapter III of [heim-1982]. Indefinites and
definites are alike variables. They differ in a felicity condition on files, the Extended
Novelty-Familiarity-Condition: the card of an indefinite must be new to the file, and the card of
a definite must be in the file, which must entail the definite's descriptive content.

A logical form `LF` is interpreted by its file change potential `LF.fcp`, which gives the
satisfaction set and the domain of the changed file together. An atomic formula removes the
sequences that falsify it and adds the cards of its variables. A cumulative formula updates with
its parts in order. A universal formula keeps the sequences of the file each of whose variants
that satisfies the file updated with the restrictor has a variant that satisfies that file
updated with the nuclear scope, and a negated formula keeps the sequences no variant of which
satisfies the file updated with its scope; neither adds a card.

The domain of the changed file is the domain of the file together with the cards of the atoms and
indefinites of the formula outside every universal and negated formula (`LF.dom_of_mem`), so a
card introduced under `every` or `not` does not outlive its formula, and a pronoun for it in the
next sentence is infelicitous whatever the file (`not_admits_everyDog`, `not_admits_noDog`). The
universal formula is the conditional `¬(φ₁ ∧ ¬φ₂)` (`LF.every_eq_cond`). A formula is true with
respect to a file in a world when the changed file is true there, and an indefinite at a new card
is then true exactly where the file is true and something has its descriptive content
(`trueWrt_indef`), and its negation where the file is true and nothing has it
(`trueWrt_neg_indef`): the truth criterion gives a free indefinite existential force, with no
existential quantifier in the logical form.

## Implementation notes

The rules are those of the summary in §4.4 with the felicity condition of §5.1. Predicates are
interpreted directly and do not vary with the world, as in the extensional semantics of the
chapter; files carry worlds so that entailment, which compares satisfaction sets world by world,
can be stated. Quantifier Indexing and Existential Closure are not represented, since the revised
rules make them dispensable. Accommodating a novel definite (§5.2) is modelled by placing its
indefinite either inside the auxiliary file of a negation or in the initial file.

The truth criterion is not defined for a file false in the world of evaluation; `TrueWrt` is
false there and `FalseWrt` requires the file to be true. Examples are numbered as in the
dissertation, by chapter and section.

## References

* [heim-1982]
-/

@[expose] public section

namespace Heim1982

open DynamicSemantics

variable {W M : Type*} {n : ℕ}

/-- Logical forms of the revised theory (Ch. III §4.4, §5.1): atomic formulas over indexed
variables, indefinite and definite noun phrases with their descriptive content, and cumulative,
universally quantified and negated formulas. -/
inductive LF (M : Type*)
  | atom {n : ℕ} (ζ : (Fin n → M) → Prop) (args : Fin n → ℕ)
  | indef (i : ℕ) (N : M → Prop)
  | defNP (i : ℕ) (N : M → Prop)
  | seq (φ ψ : LF M)
  | every (φ₁ φ₂ : LF M)
  | neg (ψ : LF M)

/-- (III): the file that keeps the cards of `F` and the sequences of `F` each of whose variants
in `F₁` on the cards of `F` has a variant in `F₂` on the cards of `F₁`. -/
def universal (F F₁ F₂ : File W ℕ M) : File W ℕ M where
  dom := F.dom
  sat := {p ∈ F.sat | ∀ q ∈ F₁.sat, q.AgreeOn F.dom p → ∃ r ∈ F₂.sat, r.AgreeOn F₁.dom q}
  mem_sat_of_agreeOn := fun _ _ h ⟨hp, hall⟩ ↦
    ⟨F.mem_sat_of_agreeOn h hp, fun q hq hqp ↦ hall q hq (hqp.trans h.symm)⟩

theorem universal_eq_sdiff (F F₁ F₂ : File W ℕ M) : universal F F₁ F₂ = F \ (F₁ \ F₂) :=
  File.ext rfl (Set.ext fun _ ↦ File.mem_sat_sdiff_sdiff.symm)

namespace LF

variable {F F' : File W ℕ M} {φ ψ φ₁ φ₂ : LF M} {i j : ℕ} {N : M → Prop}
  {ζ : (Fin n → M) → Prop} {args : Fin n → ℕ}

/-- A pronoun or trace: a definite without descriptive content. -/
def pro (i : ℕ) : LF M := defNP i fun _ ↦ True

/-- A one-place predication at card `i`. -/
def pred₁ (N : M → Prop) (i : ℕ) : LF M := atom (fun m ↦ N (m 0)) fun _ : Fin 1 ↦ i

/-- A two-place predication at cards `i`, `j`. -/
def pred₂ (R : M → M → Prop) (i j : ℕ) : LF M := atom (fun m ↦ R (m 0) (m 1)) ![i, j]

/-- Rules (I)–(IV) of Ch. III §4.4 with the Extended Novelty-Familiarity-Condition of §5.1. An
atom takes the meet with its file. An indefinite is defined on the files that lack its card and a
definite on those that have its card and entail its content, and each then updates with its
content. Sequencing composes, `every` is rule (III), and `not` takes the difference of the file
from its update. -/
def fcp : LF M → FCP W ℕ M
  | atom ζ args => FCP.ofFile (File.atom (fun _ ↦ ζ) args)
  | indef i N => FCP.indefinite i (FCP.ofFile (File.atomAt i fun _ ↦ N))
  | defNP i N => FCP.definite i (FCP.ofFile (File.atomAt i fun _ ↦ N))
  | seq φ ψ => φ.fcp.seq ψ.fcp
  | every φ₁ φ₂ => fun F ↦ (φ₁.fcp F).bind fun F₁ ↦ (φ₂.fcp F₁).map fun F₂ ↦ universal F F₁ F₂
  | neg ψ => PartialUpdate.neg ψ.fcp

/-- The cards a logical form adds to the file: those of its atoms and indefinites outside the
scope of `every` and `not`. -/
def cards : LF M → Set ℕ
  | atom _ args => Set.range args
  | indef i _ => {i}
  | defNP _ _ => ∅
  | seq φ ψ => φ.cards ∪ ψ.cards
  | every _ _ => ∅
  | neg _ => ∅

/-! ### The Extended Novelty-Familiarity-Condition -/

theorem admits_atom : (atom ζ args).fcp.Admits F := trivial

theorem admits_indef : (indef i N).fcp.Admits F ↔ i ∉ F.dom :=
  FCP.admits_indefinite.trans (and_iff_left (FCP.admits_ofFile _ _))

theorem admits_defNP : (defNP i N).fcp.Admits F ↔ i ∈ F.dom ∧ ∀ p ∈ F.sat, N (p.assignment i) :=
  FCP.admits_definite_ofFile

theorem admits_pro : (pro i).fcp.Admits F ↔ i ∈ F.dom :=
  admits_defNP.trans (and_iff_left fun _ _ ↦ trivial)

theorem fcp_pro (h : i ∈ F.dom) : (pro i).fcp F = Part.some F :=
  FCP.definite_ofFile_apply (File.le_atomAt_iff.mpr ⟨h, fun _ _ ↦ trivial⟩) h

theorem fcp_indef (h : i ∉ F.dom) :
    (indef i N).fcp F = Part.some (F ⊓ File.atomAt i fun _ ↦ N) :=
  FCP.indefinite_apply h

theorem mem_fcp_indef :
    F' ∈ (indef i N).fcp F ↔ i ∉ F.dom ∧ F' = F ⊓ File.atomAt i fun _ ↦ N :=
  FCP.mem_indefinite.trans (and_congr_right fun _ ↦ FCP.mem_ofFile)

-- §5.1, p. 369
theorem mem_dom_of_entails (h : F.Entails (FCP.ofFile (File.atomAt i fun _ ↦ N)))
    (hF : F.sat.Nonempty) (hN : ∃ m, ¬ N m) : i ∈ F.dom :=
  let ⟨p, hp⟩ := hF
  let ⟨m, hm⟩ := hN
  File.mem_dom_of_forall_mem_sat (N := fun _ ↦ N) (File.entails_ofFile.mp h) ⟨p, hp, m, hm⟩

/-! ### Membership and projection through the rules -/

theorem mem_fcp_seq : F' ∈ (φ.seq ψ).fcp F ↔ ∃ F₁ ∈ φ.fcp F, F' ∈ ψ.fcp F₁ :=
  Part.mem_bind_iff

theorem mem_fcp_every :
    F' ∈ (every φ₁ φ₂).fcp F ↔ ∃ F₁ ∈ φ₁.fcp F, ∃ F₂ ∈ φ₂.fcp F₁, universal F F₁ F₂ = F' := by
  simp only [fcp, Part.mem_bind_iff, Part.mem_map_iff]

/-- Rule (III) is the conditional: the negation of the restrictor followed by the negated
nuclear scope. -/
theorem every_eq_cond (φ₁ φ₂ : LF M) :
    (every φ₁ φ₂).fcp = PartialUpdate.cond (φ₁.fcp : FCP W ℕ M) φ₂.fcp :=
  funext fun _ ↦ Part.ext fun _ ↦ by
    simp only [mem_fcp_every, PartialUpdate.mem_cond, universal_eq_sdiff]

theorem admits_seq : (φ.seq ψ).fcp.Admits F ↔ ∃ F₁ ∈ φ.fcp F, ψ.fcp.Admits F₁ :=
  ⟨fun ⟨h, h'⟩ ↦ ⟨_, Part.get_mem h, h'⟩,
    fun ⟨_, h, h'⟩ ↦ Part.dom_iff_mem.mpr ⟨_, mem_fcp_seq.mpr ⟨_, h, Part.get_mem h'⟩⟩⟩

theorem admits_every : (every φ₁ φ₂).fcp.Admits F ↔ ∃ F₁ ∈ φ₁.fcp F, φ₂.fcp.Admits F₁ :=
  ⟨fun ⟨h, h'⟩ ↦ ⟨_, Part.get_mem h, h'⟩,
    fun ⟨_, h, h'⟩ ↦
      Part.dom_iff_mem.mpr ⟨_, mem_fcp_every.mpr ⟨_, h, _, Part.get_mem h', rfl⟩⟩⟩

theorem admits_atom_seq :
    ((atom ζ args).seq ψ).fcp.Admits F ↔ ψ.fcp.Admits (F ⊓ File.atom (fun _ ↦ ζ) args) :=
  admits_seq.trans ⟨fun ⟨_, h, h'⟩ ↦ FCP.mem_ofFile.mp h ▸ h', fun h ↦ ⟨_, Part.mem_some _, h⟩⟩

theorem admits_indef_seq :
    ((indef i N).seq ψ).fcp.Admits F ↔
      i ∉ F.dom ∧ ψ.fcp.Admits (F ⊓ File.atomAt i fun _ ↦ N) := by
  simp [admits_seq, mem_fcp_indef]

theorem admits_every_indef :
    (every (indef i N) ψ).fcp.Admits F ↔
      i ∉ F.dom ∧ ψ.fcp.Admits (F ⊓ File.atomAt i fun _ ↦ N) := by
  simp [admits_every, mem_fcp_indef]

theorem admits_pro_seq : ((pro i).seq ψ).fcp.Admits F ↔ i ∈ F.dom ∧ ψ.fcp.Admits F := by
  refine admits_seq.trans ⟨fun ⟨F₁, h₁, h⟩ ↦ ?_, fun ⟨hi, h⟩ ↦ ⟨F, fcp_pro hi ▸ Part.mem_some F, h⟩⟩
  have hi := admits_pro.mp (Part.dom_iff_mem.mpr ⟨F₁, h₁⟩)
  exact ⟨hi, Part.mem_some_iff.mp (fcp_pro hi ▸ h₁) ▸ h⟩

/-! ### Satisfaction sets and domains through the rules

Every rule descends in the information order, so no card is removed and no sequence is added.
The cards a rule adds are those the logical form introduces. -/

theorem fcp_isEliminative : ∀ φ : LF M, (φ.fcp : FCP W ℕ M).IsEliminative
  | atom _ _ => FCP.isEliminative_ofFile _
  | indef i _ => (FCP.isEliminative_ofFile _).indefinite i
  | defNP i _ => (FCP.isEliminative_ofFile _).definite i
  | seq φ ψ => (fcp_isEliminative φ).seq (fcp_isEliminative ψ)
  | every φ₁ φ₂ => by rw [every_eq_cond]; exact FCP.isEliminative_cond _ _
  | neg _ => FCP.isEliminative_neg _

/-- The domain of the changed file is the domain of the file with the cards of the logical
form. -/
theorem dom_of_mem : ∀ {φ : LF M} {F F' : File W ℕ M}, F' ∈ φ.fcp F → F'.dom = F.dom ∪ φ.cards
  | atom _ _, _, _, h => FCP.mem_ofFile.mp h ▸ rfl
  | indef _ _, _, _, h => by
    obtain ⟨-, rfl⟩ := mem_fcp_indef.mp h
    simp [cards]
  | defNP _ _, _, _, h => by
    obtain ⟨hi, -, h⟩ := FCP.mem_definite.mp h
    obtain rfl := FCP.mem_ofFile.mp h
    simpa [cards] using hi
  | seq φ ψ, _, _, h => by
    obtain ⟨_, h₁, h₂⟩ := mem_fcp_seq.mp h
    rw [dom_of_mem h₂, dom_of_mem h₁, cards, Set.union_assoc]
  | every _ _, _, _, h => by
    obtain ⟨_, -, _, -, rfl⟩ := mem_fcp_every.mp h
    simp [cards, universal]
  | neg _, _, _, h => by simp [cards, FCP.dom_eq_of_mem_neg h]

-- §3.2
theorem sat_eq_empty_of_mem (h : F' ∈ φ.fcp F) (hF : F.sat = ∅) : F'.sat = ∅ :=
  Set.eq_empty_of_subset (File.sat_mono (fcp_isEliminative φ _ _ h)) hF

end LF

/-! ### Truth (§3.2)

A file is true in a world when some sequence satisfies it there. A formula is true with respect
to a file when the changed file is true, and false when the file is true and the changed file is
false. -/

section Truth

variable {F : File W ℕ M} {φ : FCP W ℕ M} {i : ℕ} {N : M → Prop} {w : W}

/-- (C): `φ` is true with respect to `F` in `w` when `F + φ` is true in `w`. -/
def TrueWrt (φ : FCP W ℕ M) (F : File W ℕ M) (w : W) : Prop := ∃ F' ∈ φ F, w ∈ F'.worlds

/-- (C): `φ` is false with respect to `F` in `w` when `F` is true in `w` and `F + φ` is false in
`w`. -/
structure FalseWrt (φ : FCP W ℕ M) (F : File W ℕ M) (w : W) : Prop where
  /-- The file is true in the world. -/
  mem_worlds : w ∈ F.worlds
  /-- The changed file is false in the world. -/
  exists_notMem : ∃ F' ∈ φ F, w ∉ F'.worlds

theorem not_trueWrt_of_falseWrt (h : FalseWrt φ F w) : ¬ TrueWrt φ F w :=
  fun ⟨_, hF', hw⟩ ↦ let ⟨_, hG, hw'⟩ := h.exists_notMem; hw' (Part.mem_unique hG hF' ▸ hw)

-- §3.2, p. 330
theorem TrueWrt.mem_worlds (h : TrueWrt φ F w) (hφ : φ.IsEliminative) : w ∈ F.worlds :=
  let ⟨_, hF', hw⟩ := h
  File.worlds_mono (hφ _ _ hF') hw

theorem trueWrt_or_falseWrt (h : φ.Admits F) (hw : w ∈ F.worlds) :
    TrueWrt φ F w ∨ FalseWrt φ F w :=
  (Classical.em (w ∈ ((φ F).get h).worlds)).imp (fun h' ↦ ⟨_, Part.get_mem h, h'⟩)
    fun h' ↦ ⟨hw, _, Part.get_mem h, h'⟩

/-- An indefinite at a new card is true with respect to a file in the worlds where the file is
true, provided something has its descriptive content. -/
theorem trueWrt_indef (h : i ∉ F.dom) :
    TrueWrt (LF.indef i N).fcp F w ↔ w ∈ F.worlds ∧ ∃ m, N m := by
  simp only [TrueWrt, LF.fcp_indef h, Part.mem_some_iff, exists_eq_left, File.mem_worlds,
    File.sat_inf, Set.mem_inter_iff, File.mem_sat_atomAt]
  constructor
  · rintro ⟨p, ⟨hp, hN⟩, rfl⟩
    exact ⟨⟨p, hp, rfl⟩, _, hN⟩
  · rintro ⟨⟨p, hp, rfl⟩, m, hN⟩
    exact ⟨p.update i m, ⟨F.mem_sat_of_agreeOn (Possibility.agreeOn_update h m) hp, by simpa⟩, rfl⟩

-- (IV)
theorem trueWrt_neg_indef (h : i ∉ F.dom) :
    TrueWrt (LF.neg (LF.indef i N)).fcp F w ↔ w ∈ F.worlds ∧ ¬ ∃ m, N m := by
  have : (LF.neg (LF.indef i N)).fcp F = Part.some (F \ (F ⊓ File.atomAt i fun _ ↦ N)) := by
    show ((LF.indef i N).fcp F).map _ = _
    rw [LF.fcp_indef h, Part.map_some]
  simp only [TrueWrt, this, Part.mem_some_iff, exists_eq_left, File.mem_worlds,
    File.mem_sat_sdiff, File.sat_inf, Set.mem_inter_iff, File.mem_sat_atomAt]
  constructor
  · rintro ⟨p, ⟨hp, hno⟩, rfl⟩
    have hu (m : M) := Possibility.agreeOn_update (p := p) h m
    exact ⟨⟨p, hp, rfl⟩, fun ⟨m, hm⟩ ↦
      hno _ ⟨F.mem_sat_of_agreeOn (hu m) hp, by simpa⟩ (hu m).symm⟩
  · rintro ⟨⟨p, hp, rfl⟩, hno⟩
    exact ⟨p, ⟨hp, fun _ ⟨_, hN⟩ _ ↦ hno ⟨_, hN⟩⟩, rfl⟩

theorem trueWrt_pro_pred (h : i ∈ F.dom) :
    TrueWrt ((LF.pro i).seq (LF.pred₁ N i)).fcp F w ↔
      ∃ p ∈ F.sat, N (p.assignment i) ∧ p.world = w := by
  have : ((LF.pro i).seq (LF.pred₁ N i)).fcp F =
      Part.some (F ⊓ File.atom (fun _ m ↦ N (m 0)) fun _ : Fin 1 ↦ i) := by
    show ((LF.pro i).fcp F).bind _ = _
    rw [LF.fcp_pro h, Part.bind_some]
    rfl
  simp only [TrueWrt, this, Part.mem_some_iff, exists_eq_left, File.mem_worlds, File.sat_inf,
    Set.mem_inter_iff, File.mem_sat_atom, Function.comp_apply, and_assoc]

end Truth

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
  {F F' : File W ℕ M}

-- (9), row `heim1982_indefinite_persists`
theorem admits_aDog : (aDog dog cameIn layDown).fcp.Admits F ↔ 1 ∉ F.dom := by
  simp [aDog, pred₁, admits_indef_seq, admits_atom_seq, admits_pro_seq, admits_atom]

/-- (16) is infelicitous with respect to every file: the card of *every dog* is new to the file
and is not added to it, so the pronoun's card is missing. -/
theorem not_admits_everyDog (F : File W ℕ M) : ¬ (everyDog dog cameIn layDown).fcp.Admits F := by
  intro h
  obtain ⟨F₁, h₁, h₂⟩ := admits_seq.mp h
  have hd : F₁.dom = F.dom := by simpa [cards] using dom_of_mem h₁
  obtain ⟨hnew, -⟩ := admits_every_indef.mp (Part.dom_iff_mem.mpr ⟨F₁, h₁⟩)
  obtain ⟨hold, -⟩ := admits_pro_seq.mp h₂
  exact hnew (hd ▸ hold)

-- (17), row `heim1982_negative_blocks`
theorem not_admits_noDog (F : File W ℕ M) : ¬ (noDog dog cameIn layDown).fcp.Admits F := by
  intro h
  obtain ⟨F₁, h₁, h₂⟩ := admits_seq.mp h
  have hd : F₁.dom = F.dom := FCP.dom_eq_of_mem_neg h₁
  have hn : ((indef 1 dog).seq (pred₁ cameIn 1)).fcp.Admits F :=
    (PartialUpdate.admits_neg _ _).mp (Part.dom_iff_mem.mpr ⟨F₁, h₁⟩)
  obtain ⟨hnew, -⟩ := admits_indef_seq.mp hn
  obtain ⟨hold, -⟩ := admits_pro_seq.mp h₂
  exact hnew (hd ▸ hold)

-- §2.4 (5), row `heim1982_woman_dog`
theorem admits_womanDog :
    (womanDog dog woman bit hit).fcp.Admits F ↔ 1 ∉ F.dom ∧ 2 ∉ F.dom := by
  simp [womanDog, pred₂, admits_indef_seq, admits_atom_seq, admits_pro_seq, admits_atom]

/-- §4.1 (2) is felicitous with respect to the files that have neither card: the pretzel's card
is in the auxiliary file by the time the pronoun is evaluated. -/
theorem admits_pretzel :
    (pretzelText person pretzel bought ate).fcp.Admits F ↔ 1 ∉ F.dom ∧ 2 ∉ F.dom := by
  simp [pretzelText, pred₂, admits_every_indef, admits_indef_seq, admits_atom_seq,
    admits_pro_seq, admits_atom]

-- §5.2
theorem dom_of_mem_kingLocal {m i : ℕ} (hF' : F' ∈ (kingLocal king lunch m i).fcp F) :
    F'.dom = F.dom :=
  FCP.dom_eq_of_mem_neg hF'

-- §5.2
theorem mem_dom_of_mem_kingGlobal {m i : ℕ} (hF' : F' ∈ (kingGlobal king lunch m i).fcp F) :
    i ∈ F'.dom ∧ ∀ p ∈ F'.sat, king (p.assignment i) := by
  obtain ⟨F₁, h₁, h₂⟩ := mem_fcp_seq.mp hF'
  obtain ⟨-, rfl⟩ := mem_fcp_indef.mp h₁
  obtain ⟨G, -, rfl⟩ := PartialUpdate.mem_neg.mp h₂
  exact ⟨by simp, fun p hp ↦ let ⟨⟨_, hking⟩, _⟩ := File.mem_sat_sdiff.mp hp; hking⟩

end Texts

end Heim1982
