/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ShuffleIdeal

/-!
# Strictly piecewise languages (SP_k)

A language `L` is **strictly `k`-piecewise** when membership is determined by which
*subsequences* (scattered, non-contiguous selections) of length at most `k` the input
contains. Where SL_k constrains adjacent material via contiguous
factors, SP_k constrains long-distance co-occurrence — the subregular class of
unbounded-distance phonotactics. The class is the program's vocabulary for the sublist-closed
languages of `Linglib.Core.Computability.ShuffleIdeal`: a language is SP at *some* width iff
it is sublist-closed.

## Main definitions

* `StrictlyPiecewiseGrammar α`: a set of permitted subsequences; the width `k` is supplied to
  `language`, not baked into the carrier.
* `StrictlyPiecewiseGrammar.language k`: the `Language α` it generates: every subsequence of `w`
  of length at most `k` must be permitted.
* `Language.IsStrictlyPiecewise L k`: `L` is a fixed point of the width-`k` test with itself
  as grammar; `isStrictlyPiecewise_iff` recovers the ∃-grammar form.

## Main results

* `Language.IsStrictlyPiecewise.isSublistClosed`: SP languages are sublist-closed.
* `Language.IsStrictlyPiecewise.preimage_map`: SP languages are closed under inverse images of
  letter-to-letter maps.
* `Language.IsStrictlyPiecewise.mono`: `SP_k ⊆ SP_k'` for `k ≤ k'`.
* `Language.IsStrictlyPiecewise.toIsPiecewiseTestable`: `SP_k ⊆ PT_k`.
* `Language.IsStrictlyPiecewise.isStarFree`: `SP_k ⊆ SF` over a finite alphabet.
* `Language.isStrictlyPiecewise_compl_shuffleIdeal`: shuffle-ideal complements are SP.
* `Language.exists_isStrictlyPiecewise_iff_isSublistClosed`: SP at some width is exactly
  sublist-closure.

## Implementation notes

`List.Sublist` (`<+`) is mathlib's non-contiguous "is a subsequence of", exactly the SP
primitive. Unlike SL no boundary augmentation is needed, since subsequences are blind to
position; the "≤ k" (rather than "exactly k") bound is instead what keeps words shorter than
`k` distinguishable, matching `subseqSet`.

## References

* [rogers-heinz-et-al-2010]
-/

@[expose] public section

open List

/-- A **strictly-piecewise grammar** over `α` is a set of *permitted* subsequences. Unlike SL
grammars it uses no boundary alphabet, since subsequences are insensitive to position. The width
`k` is an argument of `language`. -/
abbrev StrictlyPiecewiseGrammar (α : Type*) := Set (List α)

namespace StrictlyPiecewiseGrammar

variable {α : Type*}

/-- The language generated at width `k` consists of the strings whose every subsequence of
length at most `k` is permitted. -/
def language (k : ℕ) (G : StrictlyPiecewiseGrammar α) : Language α :=
  {w | ∀ s, s.length ≤ k → s <+ w → s ∈ G}

@[simp] lemma mem_language (k : ℕ) (G : StrictlyPiecewiseGrammar α) (w : List α) :
    w ∈ G.language k ↔ ∀ s, s.length ≤ k → s <+ w → s ∈ G :=
  Iff.rfl

/-- SP languages are **sublist-closed**, since deleting symbols cannot create a subsequence
that was not already there. -/
theorem isSublistClosed_language (k : ℕ) (G : StrictlyPiecewiseGrammar α) :
    (G.language k).IsSublistClosed :=
  fun _ _ hvw hw s hlen hs ↦ hw s hlen (hs.trans hvw)

/-- Conjoining grammars conjoins their languages. -/
theorem language_inter (k : ℕ) (G₁ G₂ : StrictlyPiecewiseGrammar α) :
    (G₁ ∩ G₂).language k = G₁.language k ⊓ G₂.language k := by
  ext w
  exact ⟨fun h ↦ ⟨fun s hl hs ↦ (h s hl hs).1, fun s hl hs ↦ (h s hl hs).2⟩,
    fun h s hl hs ↦ ⟨h.1 s hl hs, h.2 s hl hs⟩⟩

/-- The grammar of the subsequences whose images are permitted generates the preimage of the
language under a letter-to-letter map. -/
theorem language_preimage_map {β : Type*} (k : ℕ) (G : StrictlyPiecewiseGrammar α) (f : β → α) :
    language k (List.map f ⁻¹' G) = List.map f ⁻¹' G.language k := by
  ext w
  show _ ↔ w.map f ∈ G.language k
  simp only [mem_language, Set.mem_preimage, List.sublist_map_iff]
  refine ⟨fun h t ht ⟨s, hs, e⟩ ↦ e ▸ h s (by simpa [e] using ht) hs,
    fun h s hs hsw ↦ h _ (by simpa using hs) ⟨s, hsw, rfl⟩⟩

/-- SP membership reduces to a check against `List.sublistsLen` — a `decide`-friendly
characterisation used by the decidable-membership instance below. -/
theorem mem_language_iff_forall_mem_sublistsLen (k : ℕ) (G : StrictlyPiecewiseGrammar α)
    (w : List α) :
    w ∈ G.language k ↔ ∀ j ≤ k, ∀ s ∈ w.sublistsLen j, s ∈ G := by
  refine ⟨fun h j hj s hs ↦ ?_, fun h s hlen hs ↦ h s.length hlen s ?_⟩
  · obtain ⟨hsub, rfl⟩ := List.mem_sublistsLen.mp hs
    exact h s hj hsub
  · exact List.mem_sublistsLen.mpr ⟨hs, rfl⟩

instance decidableMemLanguage (k : ℕ) (G : StrictlyPiecewiseGrammar α)
    [DecidablePred (· ∈ G)] (w : List α) : Decidable (w ∈ G.language k) :=
  decidable_of_iff' _ (mem_language_iff_forall_mem_sublistsLen k G w)

end StrictlyPiecewiseGrammar

namespace Language

variable {α : Type*} {L : Language α} {k : ℕ}

/-- A language `L` is **strictly `k`-piecewise** when the width-`k` subsequence test with
`L` itself as the permitted set recovers `L` — the canonical-grammar fixed point;
`isStrictlyPiecewise_iff` recovers the ∃-grammar form. -/
def IsStrictlyPiecewise (L : Language α) (k : ℕ) : Prop :=
  StrictlyPiecewiseGrammar.language k L = L

/-- Some grammar generates `L` at width `k` iff `L` is its own grammar. -/
theorem isStrictlyPiecewise_iff :
    L.IsStrictlyPiecewise k ↔ ∃ G : StrictlyPiecewiseGrammar α, G.language k = L := by
  refine ⟨fun h ↦ ⟨L, h⟩, ?_⟩
  rintro ⟨G, rfl⟩
  show StrictlyPiecewiseGrammar.language k _ = _
  exact le_antisymm (fun w hw s hlen hs ↦ hw s hlen hs s hlen (Sublist.refl s))
    fun w hw s hlen hs ↦ G.isSublistClosed_language k hs hw

/-- Strictly piecewise languages are closed under inverse images of letter-to-letter maps. -/
theorem IsStrictlyPiecewise.preimage_map {β : Type*} (h : L.IsStrictlyPiecewise k) (f : β → α) :
    IsStrictlyPiecewise (List.map f ⁻¹' L) k := by
  obtain ⟨G, rfl⟩ := isStrictlyPiecewise_iff.1 h
  exact isStrictlyPiecewise_iff.2 ⟨_, StrictlyPiecewiseGrammar.language_preimage_map k G f⟩

/-- SP languages are sublist-closed. -/
theorem IsStrictlyPiecewise.isSublistClosed (h : L.IsStrictlyPiecewise k) : L.IsSublistClosed :=
  h ▸ StrictlyPiecewiseGrammar.isSublistClosed_language k L

/-- A nonempty SP language contains the empty word. -/
theorem IsStrictlyPiecewise.nil_mem (h : L.IsStrictlyPiecewise k) {w : List α}
    (hw : w ∈ L) : [] ∈ L :=
  h.isSublistClosed (nil_sublist w) hw

/-- The complement of a shuffle ideal is strictly `k`-piecewise as soon as the forbidden pattern
fits in the window. -/
theorem isStrictlyPiecewise_compl_shuffleIdeal {p : List α} (hp : p.length ≤ k) :
    (shuffleIdeal p)ᶜ.IsStrictlyPiecewise k :=
  le_antisymm (fun _ hw hpw ↦ hw p hp hpw (Sublist.refl p))
    fun _ hw _ _ hs hps ↦ hw (hps.trans hs)

/-- Widening the window loses nothing, `SP_k ⊆ SP_k'` for `k ≤ k'`. -/
theorem IsStrictlyPiecewise.mono {k' : ℕ} (h : L.IsStrictlyPiecewise k) (hk : k ≤ k') :
    L.IsStrictlyPiecewise k' :=
  le_antisymm (fun _ hw ↦ h ▸ fun s hs ↦ hw s (hs.trans hk)) fun _ hw _ _ hs ↦
    h.isSublistClosed hs hw

/-- The strictly-piecewise test, that every subsequence of length at most `k` is permitted,
depends only on `subseqSet k`, so `SP_k ⊆ PT_k`. -/
theorem IsStrictlyPiecewise.toIsPiecewiseTestable (h : L.IsStrictlyPiecewise k) :
    L.IsPiecewiseTestable k := by
  obtain ⟨G, rfl⟩ := isStrictlyPiecewise_iff.mp h
  refine fun w₁ w₂ heq ↦ propext ⟨fun hw s hlen hs ↦ ?_, fun hw s hlen hs ↦ ?_⟩
  · exact hw s hlen ((subseqSet_eq_iff heq hlen).mpr hs)
  · exact hw s hlen ((subseqSet_eq_iff heq hlen).mp hs)

/-- Over a finite alphabet strictly piecewise languages are star-free. -/
theorem IsStrictlyPiecewise.isStarFree [Finite α] (h : L.IsStrictlyPiecewise k) : L.IsStarFree :=
  h.toIsPiecewiseTestable.isStarFree

/-- A language is strictly piecewise at some width iff it is sublist-closed
[rogers-heinz-et-al-2010]. Backwards, `L` is its own grammar at the width bounding the
finite forbidden basis, so that any word outside `L` is already refuted by a basis word it
contains. -/
theorem exists_isStrictlyPiecewise_iff_isSublistClosed [Finite α] :
    (∃ k, L.IsStrictlyPiecewise k) ↔ L.IsSublistClosed := by
  refine ⟨fun ⟨_, hk⟩ ↦ hk.isSublistClosed, fun hL ↦ ?_⟩
  obtain ⟨F, hF⟩ := hL.exists_finset_compl_eq_biSup_shuffleIdeal
  have hFmem (w : List α) : w ∈ Lᶜ ↔ ∃ m ∈ F, m <+ w := by rw [hF]; simp [mem_iSup]
  refine ⟨F.sup length, le_antisymm (fun w h ↦ by_contra fun hwL ↦ ?_) fun _ hw _ _ hs ↦ hL hs hw⟩
  obtain ⟨m, hm, hmw⟩ := (hFmem w).mp hwL
  exact (hFmem m).mpr ⟨m, hm, .refl m⟩ (h m (F.le_sup hm) hmw)

end Language
