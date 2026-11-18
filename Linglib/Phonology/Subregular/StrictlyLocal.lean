/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Computability.Language
public import Linglib.Phonology.Subregular.Boundary
public import Linglib.Core.Computability.LocallyTestable
public import Linglib.Core.Relation.SetRel

/-!
# Strictly local languages (SL_k)

A language `L` is **strictly `k`-local** when membership is determined by the
length-`k` substrings of the boundary-augmented input: a grammar is a set `G` of
permitted `k`-factors, and `w ∈ L` iff every `k`-factor of `boundary k w` lies in
`G`. The grammar may be any set, finite or not. Over a finite alphabet only the finitely many
`k`-factors matter, so this agrees with the usual finite grammars; over an infinite alphabet it
admits languages that no finite set of permitted or forbidden factors defines, such as the
strictly increasing sequences of natural numbers, strictly `2`-local here. A finite set `F` of
forbidden factors presents its language as `ofForbidden F`, whose grammar `Fᶜ` is infinite over
an infinite alphabet.

The language of a grammar is the core of the relation between a word and its `k`-factors, the
upper adjoint of the map taking a set of words to the factors they contain
(`StrictlyLocalGrammar.language_eq_core`). Intersection and monotonicity are then mathlib's
facts about the core, and a language is strictly `k`-local exactly when the factors of its
members regenerate it (`Language.isStrictlyLocal_iff_language_image`).

## Main definitions

* `StrictlyLocalGrammar α`: a grammar is just a set of permitted factors over
  `Augmented α`; the locality width `k` is supplied to `language`, not baked in.
* `StrictlyLocalGrammar.language k`: the `Language α` it generates at width `k`.
* `StrictlyLocalGrammar.ofForbidden`: the grammar of a forbidden-factor set (its
  complement).
* `Language.IsStrictlyLocal L k`: `L` is strictly `k`-local.
* `Language.SuffixSubstitutionClosed L k`: members sharing a length-`(k − 1)` window
  admit suffix crossover.

## Main results

* `StrictlyLocalGrammar.language_eq_core`: the language is `SetRel.core` of the factor relation.
* `Language.isStrictlyLocal_iff_language_image`: the canonical grammar, the factors of the
  members, regenerates every strictly local language.
* `Language.isStrictlyLocal_iff_suffixSubstitutionClosed`: for `k ≥ 2`, strict
  `k`-locality is exactly closure under suffix substitution: the crossover's factors
  split into the two members' shared parts, and conversely a member is marched along a word
  whose factors are licensed (`Language.SuffixSubstitutionClosed.mem_of_exists_infix`), the
  argument the word models of `Subregular.WordModel` share.

* `Language.IsStrictlyLocal.toIsLocallyTestable`: `SL_k ⊆ LT_k`.
* `Language.IsStrictlyLocal.isStarFree`: `SL_k ⊆ SF` over a finite alphabet.

## Implementation notes

Grammars are arbitrary sets over an arbitrary alphabet rather than finite sets over a finite one.
Only star-freeness assumes a finite alphabet (`Language.IsStrictlyLocal.isStarFree`). Learning from
positive data needs finite grammars: at a fixed width the languages of arbitrary grammars are
identifiable in the limit only over a finite alphabet
(`HeinzKasprzikKotzing2012.identifiable_isStrictlyLocal_iff`).

## References

* [rogers-pullum-2011]
* [mcnaughton-papert-1971]
-/

@[expose] public section

variable {α : Type*}

/-- A **strictly-local grammar** over `α` is a set of *permitted* factors over the
boundary-augmented alphabet `Option α`, with `none` the boundary. The locality width `k` is an
argument of `language`. -/
abbrev StrictlyLocalGrammar (α : Type*) := Set (Augmented α)

namespace StrictlyLocalGrammar

/-- The language generated at width `k` consists of the strings whose boundary-augmented form
has every infix of length `k` permitted. -/
def language (k : ℕ) (G : StrictlyLocalGrammar α) : Language α :=
  {w | ∀ f, f.length = k → f <:+: boundary k w → f ∈ G}

@[simp] lemma mem_language (k : ℕ) (G : StrictlyLocalGrammar α) (w : List α) :
    w ∈ G.language k ↔ ∀ f, f.length = k → f <:+: boundary k w → f ∈ G :=
  Iff.rfl

/-- The grammar of a **forbidden**-factor set is its complement: a string is
accepted iff none of its `k`-factors are forbidden. -/
def ofForbidden (forbidden : Set (Augmented α)) : StrictlyLocalGrammar α := forbiddenᶜ

@[simp] lemma mem_ofForbidden_language (forbidden : Set (Augmented α)) (k : ℕ)
    (w : List α) :
    w ∈ (ofForbidden forbidden).language k
      ↔ ∀ f, f.length = k → f <:+: boundary k w → f ∉ forbidden :=
  Iff.rfl

theorem mem_language_iff_window {k : ℕ} {G : StrictlyLocalGrammar α} {w : List α} (hk : 1 ≤ k) :
    w ∈ G.language k ↔ ∀ i : ℤ, 1 - k ≤ i → i < w.length → window k w i ∈ G := by
  rw [mem_language]
  constructor
  · intro h i h1 h2
    obtain ⟨hf, hl⟩ := (infix_boundary_and_length_eq_iff hk).mpr ⟨i, h1, h2, rfl⟩
    exact h _ hl hf
  · intro h f hl hf
    obtain ⟨i, h1, h2, rfl⟩ := (infix_boundary_and_length_eq_iff hk).mp ⟨hf, hl⟩
    exact h i h1 h2

/-! ### The factor relation -/

/-- The language at width `k` is the core of the relation taking a word to its `k`-factors. -/
theorem language_eq_core (k : ℕ) (G : StrictlyLocalGrammar α) :
    G.language k =
      (SetRel.ofSuccessors fun w : List α ↦ {f | f <:+: boundary k w ∧ f.length = k}).core G :=
  Set.ext fun _ ↦ ⟨fun h _ hf ↦ h _ hf.2 hf.1, fun h _ hl hf ↦ h ⟨hf, hl⟩⟩

theorem language_inter (k : ℕ) (G₁ G₂ : StrictlyLocalGrammar α) :
    (G₁ ∩ G₂).language k = G₁.language k ⊓ G₂.language k := by
  simp only [language_eq_core]
  exact SetRel.core_inter _ _ _

theorem language_mono (k : ℕ) : Monotone (language k : StrictlyLocalGrammar α → Language α) :=
  fun G₁ G₂ h ↦ by
    simp only [language_eq_core]
    exact SetRel.core_subset_core h

end StrictlyLocalGrammar

namespace Language

variable {α : Type*}


/-- A language `L` is **strictly `k`-local** iff some `StrictlyLocalGrammar α` generates it at
width `k`. Witness-style, mirroring `Language.IsRegular`/`Language.IsContextFree`
("L is regular iff some DFA accepts L"). -/
def IsStrictlyLocal (L : Language α) (k : ℕ) : Prop :=
  ∃ G : StrictlyLocalGrammar α, G.language k = L

/-- A language is strictly `k`-local iff its canonical grammar, the `k`-factors of its members,
generates it. -/
theorem isStrictlyLocal_iff_language_image {L : Language α} {k : ℕ} :
    L.IsStrictlyLocal k ↔
      StrictlyLocalGrammar.language k {f | ∃ z ∈ L, f <:+: boundary k z ∧ f.length = k} = L := by
  refine ⟨?_, fun h ↦ ⟨_, h⟩⟩
  rintro ⟨G, rfl⟩
  simp only [StrictlyLocalGrammar.language_eq_core]
  exact SetRel.image_core_gc.u_l_u_eq_u G

/-! ### Suffix substitution closure -/

/-- `L` is closed under *suffix substitution* at width `k` when two members sharing a
length-`(k − 1)` window admit the crossover of their suffixes at it. -/
def SuffixSubstitutionClosed (L : Language α) (k : ℕ) : Prop :=
  ∀ u₁ v₁ u₂ v₂ x : List α, x.length = k - 1 →
    u₁ ++ x ++ v₁ ∈ L → u₂ ++ x ++ v₂ ∈ L → u₁ ++ x ++ v₂ ∈ L

theorem IsStrictlyLocal.suffixSubstitutionClosed {L : Language α} {k : ℕ}
    (h : L.IsStrictlyLocal k) : L.SuffixSubstitutionClosed k := by
  obtain ⟨G, rfl⟩ := h
  intro u₁ v₁ u₂ v₂ x hx h₁ h₂ f hk hf
  have hb (u v : List α) : boundary k (u ++ x ++ v) = (List.replicate (k - 1) none ++ u.map some) ++
      x.map some ++ (v.map some ++ List.replicate (k - 1) none) := by
    simp [boundary, List.append_assoc]
  have hl : f.length ≤ (x.map some).length + 1 := by simp only [List.length_map]; omega
  rw [hb, List.infix_append_append_iff hl] at hf
  rcases hf with hf | hf
  · exact h₁ f hk (by rw [hb, List.infix_append_append_iff hl]; exact .inl hf)
  · exact h₂ f hk (by rw [hb, List.infix_append_append_iff hl]; exact .inr hf)

/-- A language closed under suffix substitution contains a word of at least `k - 1` symbols
once members show its first `k - 1` symbols as a prefix, each of its infixes of `k` symbols, and
its last `k - 1` symbols as a suffix: a member is marched along the word, its suffix exchanged at
each step. -/
theorem SuffixSubstitutionClosed.mem_of_exists_infix {L : Language α} {k : ℕ}
    (hL : L.SuffixSubstitutionClosed k) (hk : 2 ≤ k) {w : List α} (hw : k - 1 ≤ w.length)
    (hpre : ∃ v ∈ L, w.take (k - 1) <+: v)
    (hmid : ∀ s, s <:+: w → s.length = k → ∃ v ∈ L, s <:+: v)
    (hsuf : ∃ v ∈ L, w.rtake (k - 1) <:+ v) : w ∈ L := by
  have march (j : ℕ) (hj : k - 1 ≤ j) (hjw : j ≤ w.length) : ∃ y, w.take j ++ y ∈ L := by
    induction j, hj using Nat.le_induction with
    | base =>
      obtain ⟨v, hv, y, rfl⟩ := hpre
      exact ⟨y, hv⟩
    | succ j hj ih =>
      obtain ⟨y, hy⟩ := ih (by omega)
      have hjlt : j < w.length := by omega
      have hx : ((w.take j).drop (j - (k - 1))).length = k - 1 := by simp; omega
      have hinf : (w.take j).drop (j - (k - 1)) ++ [(w[j])] <:+: w := by
        rw [← List.drop_append_of_le_length (by simp; omega),
          ← List.take_succ_eq_append_getElem hjlt]
        exact (List.drop_suffix _ _).isInfix.trans (List.take_prefix _ _).isInfix
      obtain ⟨v, hv, u₂, v₂, rfl⟩ := hmid _ hinf (by simp; omega)
      refine ⟨v₂, ?_⟩
      have := hL ((w.take j).take (j - (k - 1))) y u₂ ([(w[j])] ++ v₂) _ hx
        (by rwa [List.take_append_drop]) (by simpa only [List.append_assoc] using hv)
      rw [List.take_append_drop] at this
      rwa [List.take_succ_eq_append_getElem hjlt, List.append_assoc]
  obtain ⟨y, hy⟩ := march w.length hw le_rfl
  rw [List.take_length] at hy
  have hx : (w.rtake (k - 1)).length = k - 1 := by simp; omega
  obtain ⟨v, hv, u₂, rfl⟩ := hsuf
  have := hL (w.rdrop (k - 1)) y u₂ [] _ hx (by rwa [List.rdrop_append_rtake])
    (by simpa using hv)
  simpa using this

theorem SuffixSubstitutionClosed.isStrictlyLocal {L : Language α} {k : ℕ} (hk : 2 ≤ k)
    (h : L.SuffixSubstitutionClosed k) : L.IsStrictlyLocal k := by
  refine isStrictlyLocal_iff_language_image.2 (le_antisymm (fun w hw ↦ ?_) ?_)
  swap
  · simp only [StrictlyLocalGrammar.language_eq_core]
    exact SetRel.image_core_gc.le_u_l (L : Set (List α))
  have hwin (f : Augmented α) (hf : f <:+: boundary k w) (hlen : f.length ≤ k) :
      ∃ z ∈ L, f <:+: boundary k z := by
    obtain ⟨g, hg, hgk, hfg⟩ :=
      List.exists_infix_length_eq hf hlen (by rw [length_boundary]; omega)
    obtain ⟨z, hz, hgz, -⟩ := hw g hgk hg
    exact ⟨z, hz, hfg.trans hgz⟩
  have htwo : boundary 2 w = none :: (w.map some ++ [none]) := by simp [boundary]
  rcases lt_or_ge w.length (k - 1) with hshort | hlong
  · rcases eq_or_ne w [] with rfl | hne
    · obtain ⟨z, hz, hfz⟩ := hwin (List.replicate k none)
        ⟨[], List.replicate (k - 2) none, by
          simp only [boundary, List.map_nil, List.append_nil, List.nil_append,
            ← List.replicate_add]
          congr 1
          omega⟩ (by simp)
      exact eq_nil_of_replicate_none_infix_boundary (by omega) hfz ▸ hz
    · obtain ⟨z, hz, hfz⟩ := hwin _ (boundary_two_infix_boundary hk w)
        (by simp [length_boundary]; omega)
      exact eq_of_boundary_two_infix_boundary hne hfz ▸ hz
  · have hne : w.take (k - 1) ≠ [] := fun h0 ↦ by
      have := congrArg List.length h0
      rw [List.length_take, List.length_nil] at this
      omega
    refine h.mem_of_exists_infix hk hlong ?_ (fun s hs hlen ↦ ?_) ?_
    · have hinf : none :: (w.take (k - 1)).map some <:+: boundary 2 w := by
        rw [htwo]
        exact (List.cons_prefix_cons.2 ⟨rfl, ((List.take_prefix _ w).map _).trans
          (List.prefix_append _ _)⟩).isInfix
      obtain ⟨z, hz, hfz⟩ := hwin _ (hinf.trans (boundary_two_infix_boundary hk w))
        (by simp; omega)
      exact ⟨z, hz, prefix_of_cons_none_infix_boundary hne hfz⟩
    · obtain ⟨z, hz, hfz⟩ := hwin (s.map some)
        ((hs.map _).trans (map_some_infix_boundary k w)) (by simp [hlen])
      exact ⟨z, hz, infix_of_map_some_infix_boundary hfz⟩
    · have hlen : (w.rtake (k - 1)).length = k - 1 := by simp; omega
      have hne' : w.rtake (k - 1) ≠ [] := fun h0 ↦ by
        rw [h0, List.length_nil] at hlen
        omega
      have hinf : (w.rtake (k - 1)).map some ++ [none] <:+: boundary 2 w := by
        obtain ⟨t, ht⟩ := (List.rtake_suffix w (k - 1)).map (some : α → Option α)
        exact ⟨none :: t, [], by rw [htwo, ← ht]; simp⟩
      obtain ⟨z, hz, hfz⟩ := hwin _ (hinf.trans (boundary_two_infix_boundary hk w))
        (by simp; omega)
      exact ⟨z, hz, suffix_of_concat_none_infix_boundary hne' hfz⟩

/-- For widths `k ≥ 2`, a language is strictly `k`-local if and only if it is closed under
suffix substitution at `k`. -/
theorem isStrictlyLocal_iff_suffixSubstitutionClosed {L : Language α} {k : ℕ}
    (hk : 2 ≤ k) : L.IsStrictlyLocal k ↔ L.SuffixSubstitutionClosed k :=
  ⟨IsStrictlyLocal.suffixSubstitutionClosed, fun hL ↦ hL.isStrictlyLocal hk⟩

/-! ### Local testability -/

/-- A strictly `k`-local language is locally `k`-testable. Padding a word with boundary markers
pulls it back from the words over the augmented alphabet whose factors of length `k` are all
permitted, and that language is locally `k`-testable outright. -/
theorem IsStrictlyLocal.toIsLocallyTestable {L : Language α} {k : ℕ} (h : L.IsStrictlyLocal k) :
    L.IsLocallyTestable k := by
  obtain ⟨G, rfl⟩ := h
  rw [StrictlyLocalGrammar.language_eq_core]
  exact (((isLocallyTestable_setOf_factors k {S | S ⊆ G}).rightQuotient
    (List.replicate (k - 1) none)).leftQuotient (List.replicate (k - 1) none)).preimage_map some

/-- Over a finite alphabet strictly local languages are star-free. -/
theorem IsStrictlyLocal.isStarFree [Finite α] {L : Language α} {k : ℕ}
    (h : L.IsStrictlyLocal k) : L.IsStarFree :=
  h.toIsLocallyTestable.isStarFree

end Language
