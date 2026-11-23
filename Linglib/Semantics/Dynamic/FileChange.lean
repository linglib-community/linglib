module

public import Linglib.Semantics.Dynamic.File
public import Linglib.Semantics.Dynamic.Partial

/-!
# File change semantics

A *file change potential* is a partial function on files, the meaning of a sentence: the change
its utterance makes to the file, defined where the sentence is felicitous. The update by an
atomic formula is the meet with the formula's file `File.atom`, which adds the cards of its
variables and removes the points that falsify it. An indefinite is felicitous where its card is
new, and a definite where its card is present and the file entails its descriptive content,
where `F` entails an update that removes no point of `F` (`File.Entails`). For a one-place
content at the definite's own card, the condition is that the file lies below the content's file
(`FCP.admits_definite_ofFile_atomAt`). Negation is `PartialUpdate.neg` at the difference of
files, the negation of [heim-1983] where the update adds no card, and the cards introduced under
it are forgotten (`FCP.dom_eq_of_mem_neg`).

The update by a file, negation and the conditional descend in the information order, and an
indefinite or a definite does when its content does (`PartialUpdate.IsEliminative`). Under such
an update no card is removed, no point is added, and a file false in a world stays false in it,
since `File.dom` is antitone and `File.sat` and `File.worlds` are monotone.

## References

* [heim-1982]
* [heim-1983]
-/

@[expose] public section

namespace DynamicSemantics

variable {W V M : Type*}

/-! ### File change potentials -/

/-- A file change potential: a partial update of files, defined where the sentence is
felicitous. -/
abbrev FCP (W V M : Type*) := PartialUpdate (File W V M)

/-- A file entails an update that is defined on it and removes none of its points. -/
def File.Entails (F : File W V M) (φ : FCP W V M) : Prop := ∃ F' ∈ φ F, F.sat ⊆ F'.sat

namespace FCP

variable {A B F F' : File W V M} {φ ψ : FCP W V M} {x : V}

/-- The assertive update by a file takes the meet with it. -/
def ofFile (A : File W V M) : FCP W V M := PFun.lift (· ⊓ A)

@[simp] theorem ofFile_apply : ofFile A F = Part.some (F ⊓ A) := rfl

theorem mem_ofFile : F' ∈ ofFile A F ↔ F' = F ⊓ A := Part.mem_some_iff

@[simp] theorem admits_ofFile (A F : File W V M) : (ofFile A).Admits F := trivial

@[simp] theorem ofFile_top : ofFile (⊤ : File W V M) = PFun.id _ := funext fun _ ↦ by simp

/-- Updating by two files in sequence is updating by their meet. -/
theorem ofFile_inf : ofFile (A ⊓ B) = (ofFile A).seq (ofFile B) :=
  funext fun _ ↦ by simp [PartialUpdate.seq, PFun.comp_apply, inf_assoc]

/-- A file supports the update by a file it lies below. -/
@[simp] theorem supports_ofFile : (ofFile A).supports F ↔ F ≤ A := by
  rw [PartialUpdate.supports_iff_mem, mem_ofFile, eq_comm, inf_eq_left]

theorem isEliminative_ofFile (A : File W V M) : (ofFile A).IsEliminative :=
  fun _ _ h ↦ mem_ofFile.mp h ▸ inf_le_left

/-! ### Entailment -/

theorem _root_.DynamicSemantics.File.Entails.admits (h : F.Entails φ) : φ.Admits F :=
  let ⟨F', hF', _⟩ := h
  Part.dom_iff_mem.mpr ⟨F', hF'⟩

theorem _root_.DynamicSemantics.PartialUpdate.supports.entails (h : φ.supports F) : F.Entails φ :=
  ⟨F, h, subset_rfl⟩

@[simp] theorem _root_.DynamicSemantics.File.entails_ofFile :
    F.Entails (ofFile A) ↔ F.sat ⊆ A.sat := by
  simp [File.Entails]

/-- Under an eliminative update, a file entails the update iff the update keeps its satisfaction
set. -/
theorem _root_.DynamicSemantics.File.entails_iff_of_isEliminative (h : φ.IsEliminative) :
    F.Entails φ ↔ ∃ F' ∈ φ F, F'.sat = F.sat :=
  exists_congr fun F' ↦ and_congr_right fun hF' ↦
    ⟨fun hsub ↦ (File.sat_mono (h F F' hF')).antisymm hsub, fun heq ↦ heq.ge⟩

/-! ### Felicity conditions -/

/-- An indefinite at the card `x`, felicitous on the files that lack the card. -/
def indefinite (x : V) (φ : FCP W V M) : FCP W V M :=
  fun F ↦ Part.assert (x ∉ F.dom) fun _ ↦ φ F

/-- A definite at the card `x`, felicitous on the files that have the card and entail its
content. -/
def definite (x : V) (φ : FCP W V M) : FCP W V M :=
  fun F ↦ Part.assert (x ∈ F.dom ∧ F.Entails φ) fun _ ↦ φ F

theorem mem_indefinite : F' ∈ indefinite x φ F ↔ x ∉ F.dom ∧ F' ∈ φ F :=
  Part.mem_assert_iff.trans exists_prop

theorem mem_definite : F' ∈ definite x φ F ↔ x ∈ F.dom ∧ F.Entails φ ∧ F' ∈ φ F :=
  Part.mem_assert_iff.trans (exists_prop.trans and_assoc)

theorem indefinite_apply (h : x ∉ F.dom) : indefinite x φ F = φ F := Part.assert_pos h

theorem definite_apply (hx : x ∈ F.dom) (h : F.Entails φ) : definite x φ F = φ F :=
  Part.assert_pos ⟨hx, h⟩

theorem admits_indefinite : (indefinite x φ).Admits F ↔ x ∉ F.dom ∧ φ.Admits F := exists_prop

theorem admits_definite : (definite x φ).Admits F ↔ x ∈ F.dom ∧ F.Entails φ :=
  ⟨fun ⟨h, _⟩ ↦ h, fun ⟨hx, h⟩ ↦ ⟨⟨hx, h⟩, h.admits⟩⟩

/-- A definite whose content is a file is felicitous on the files that have its card and whose
points all satisfy the content. -/
theorem admits_definite_ofFile :
    (definite x (ofFile A)).Admits F ↔ x ∈ F.dom ∧ F.sat ⊆ A.sat := by
  rw [admits_definite, File.entails_ofFile]

/-- A definite with a one-place content at its own card is felicitous on the files below the
content's file. -/
theorem admits_definite_ofFile_atomAt {N : W → M → Prop} :
    (definite x (ofFile (File.atomAt x N))).Admits F ↔ F ≤ File.atomAt x N := by
  rw [admits_definite_ofFile, File.le_atomAt_iff]

theorem definite_ofFile_apply (h : F ≤ A) (hx : x ∈ F.dom) :
    definite x (ofFile A) F = Part.some F := by
  rw [definite_apply hx (File.entails_ofFile.mpr (File.sat_mono h)), ofFile_apply,
    inf_eq_left.mpr h]

theorem _root_.DynamicSemantics.PartialUpdate.IsEliminative.indefinite (h : φ.IsEliminative)
    (x : V) : (indefinite x φ).IsEliminative :=
  fun F F' hF' ↦ let ⟨_, h'⟩ := mem_indefinite.mp hF'; h F F' h'

theorem _root_.DynamicSemantics.PartialUpdate.IsEliminative.definite (h : φ.IsEliminative)
    (x : V) : (definite x φ).IsEliminative :=
  fun F F' hF' ↦ let ⟨_, _, h'⟩ := mem_definite.mp hF'; h F F' h'

/-! ### Negation and the conditional -/

/-- Negation adds no card. -/
theorem dom_eq_of_mem_neg (h : F' ∈ PartialUpdate.neg φ F) : F'.dom = F.dom := by
  obtain ⟨_, -, rfl⟩ := PartialUpdate.mem_neg.mp h
  rfl

theorem isEliminative_neg (φ : FCP W V M) : (PartialUpdate.neg φ).IsEliminative := fun F _ h ↦ by
  obtain ⟨G, -, rfl⟩ := PartialUpdate.mem_neg.mp h
  exact File.sdiff_le F G

theorem isEliminative_cond (φ ψ : FCP W V M) : (PartialUpdate.cond φ ψ).IsEliminative :=
  fun F _ h ↦ by
    obtain ⟨_, -, _, -, rfl⟩ := PartialUpdate.mem_cond.mp h
    exact File.sdiff_le F _

end FCP

end DynamicSemantics
