module

public import Linglib.Logic.Orthologic.ModalFrame
public import Mathlib.Order.BooleanAlgebra.Basic

/-!
# The epistemic frame of a Boolean algebra

This file defines Holliday and Mandelkern's lifting of a possible-worlds model to a possibility
model for epistemic modals. The possibilities of the *epistemic frame* of a Boolean algebra `B`
are the pairs `(a, i)` with `⊥ ≠ a ≤ i`, where `a` records how things are and might be and `i`
what must be the case. Two possibilities are compatible when their first components overlap and
each lies within the other's second component, and `(a, i)` accesses `(a', i')` when `a ≤ a'`
and `i' ≤ i`. Access is reflexive, R-regular and knowable, so the regular propositions form an
epistemic ortholattice, and `B` embeds into it.

## Main definitions

* `Orthologic.Possibility`: the possibilities `(a, i)` of the epistemic frame.
* `Orthologic.epistemicFrame`: the compatibility frame on possibilities.
* `Orthologic.embed`, `Orthologic.eB`: the embedding of `B` into the regular propositions.

## Main results

* `Orthologic.refines_iff`: refinement is componentwise.
* `Orthologic.mem_core_embed`, `Orthologic.mem_diamond_embed`: `b` must be the case at `(a, i)`
  iff `i ≤ b`, and might be iff `a ⊓ b ≠ ⊥`.
* `Orthologic.eB_le_iff`, `Orthologic.eB_compl`: the embedding is an order embedding preserving
  `⊤`, `⊥`, meets and complements.
* `Orthologic.diamondHom_necHom_le`: the regular propositions form an S5 epistemic ortholattice.
* `Orthologic.not_diamond_embed_subset`: `◇` does not collapse on non-trivial embedded
  propositions.

## References

* [holliday-mandelkern-2024]
-/

@[expose] public section

namespace Orthologic

open SetRel ModalLogic

variable {B : Type*} [BooleanAlgebra B]

/-- A possibility of the epistemic frame of `B` is a pair `(a, i)` with `⊥ ≠ a ≤ i`
([holliday-mandelkern-2024] Definition 5.1). -/
abbrev Possibility (B : Type*) [BooleanAlgebra B] : Type _ :=
  {p : B × B // p.1 ≠ ⊥ ∧ p.1 ≤ p.2}

namespace Possibility

variable (x y : Possibility B)

/-- The first component of `(a, i)` records how things are and might be. -/
abbrev truth : B := x.1.1

/-- The second component of `(a, i)` records what must be the case. -/
abbrev info : B := x.1.2

theorem truth_ne_bot : x.truth ≠ ⊥ := x.2.1

theorem truth_le_info : x.truth ≤ x.info := x.2.2

theorem info_ne_bot : x.info ≠ ⊥ := ne_bot_of_le_ne_bot x.truth_ne_bot x.truth_le_info

/-- Two possibilities are compatible when their truths overlap and each lies within the other's
information ([holliday-mandelkern-2024] Definition 5.1.2). -/
def compat : Prop := x.truth ⊓ y.truth ≠ ⊥ ∧ x.truth ≤ y.info ∧ y.truth ≤ x.info

/-- A possibility accesses another when both components of the target lie between the
components of the source ([holliday-mandelkern-2024] Definition 5.1.3). -/
def access : SetRel (Possibility B) (Possibility B) :=
  {p | p.1.truth ≤ p.2.truth ∧ p.2.info ≤ p.1.info}

instance [DecidableEq B] [DecidableLE B] : Decidable (compat x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance [DecidableEq B] [DecidableLE B] : Decidable (x ~[access] y) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `diag a` is the possibility `(a, a)`, which knows everything it settles. -/
def diag (a : B) (ha : a ≠ ⊥) : Possibility B := ⟨(a, a), ha, le_rfl⟩

@[simp] theorem diag_truth (a : B) (ha : a ≠ ⊥) : (diag a ha).truth = a := rfl

@[simp] theorem diag_info (a : B) (ha : a ≠ ⊥) : (diag a ha).info = a := rfl

theorem compat_diag_truth : compat x (diag x.truth x.truth_ne_bot) :=
  ⟨by simp only [diag_truth, inf_idem]; exact x.truth_ne_bot, le_rfl, x.truth_le_info⟩

theorem compat_diag_info : compat x (diag x.info x.info_ne_bot) :=
  ⟨by simp only [diag_truth, inf_of_le_left x.truth_le_info]; exact x.truth_ne_bot,
    x.truth_le_info, le_rfl⟩

theorem access_diag_info : x ~[access] diag x.info x.info_ne_bot := ⟨x.truth_le_info, le_rfl⟩

end Possibility

open Possibility

/-- The epistemic frame of `B` is the compatibility frame on `Possibility B`
([holliday-mandelkern-2024] Definition 5.1). -/
def epistemicFrame (B : Type*) [BooleanAlgebra B] : CompatFrame (Possibility B) where
  compat := compat
  compat_refl := ⟨fun x ↦ ⟨by rw [inf_idem]; exact x.truth_ne_bot, x.truth_le_info,
    x.truth_le_info⟩⟩
  compat_symm := ⟨fun _ _ h ↦ ⟨by rw [inf_comm]; exact h.1, h.2.2, h.2.1⟩⟩

instance : (access (B := B)).IsRefl := ⟨fun _ ↦ ⟨le_rfl, le_rfl⟩⟩

/-- Epistemic access is R-regular, witnessed by `(a ⊔ d, a ⊔ d)` ([holliday-mandelkern-2024]
Theorem 5.7.1). -/
instance : IsRRegular (epistemicFrame B) access where
  rRegular := by
    rintro x y' y ⟨hab, hki⟩ ⟨_, hbl, hdk⟩
    have hne : x.truth ⊔ y.truth ≠ ⊥ := ne_bot_of_le_ne_bot x.truth_ne_bot le_sup_left
    refine ⟨diag _ hne, ⟨?_, le_sup_left, sup_le x.truth_le_info (hdk.trans hki)⟩,
      fun x'' ⟨_, hx', hx''⟩ ↦ ⟨diag _ hne, ⟨hx'', hx'⟩, ?_, sup_le (hab.trans hbl)
        y.truth_le_info, le_sup_right⟩⟩
    · simp only [diag_truth, inf_sup_self]; exact x.truth_ne_bot
    · simp only [diag_truth, inf_of_le_right (le_sup_right : y.truth ≤ x.truth ⊔ y.truth)]
      exact y.truth_ne_bot

/-- Epistemic access satisfies Knowability, witnessed by `(a, a)` ([holliday-mandelkern-2024]
Theorem 5.7.1). -/
instance : IsKnowable (epistemicFrame B) access where
  knowable x := ⟨diag x.truth x.truth_ne_bot, fun z ⟨haz, hza⟩ w ⟨hzw, hzw', hwz⟩ ↦ by
    have hz : z.truth = x.truth := le_antisymm (z.truth_le_info.trans hza) haz
    exact ⟨by rwa [← hz], hz ▸ hzw', hwz.trans (hza.trans x.truth_le_info)⟩⟩

section Decidable

variable [DecidableEq B] [DecidableLE B]

instance : DecidableRel (epistemicFrame B).compat :=
  inferInstanceAs (DecidableRel (compat (B := B)))

end Decidable

/-- Refinement in the epistemic frame is componentwise, `(a, i) ⊑ (a', i')` iff `a = a'` and
`i ≤ i'` ([holliday-mandelkern-2024] Lemma 5.2). -/
theorem refines_iff (y x : Possibility B) :
    refines (epistemicFrame B) y x ↔ y.truth = x.truth ∧ y.info ≤ x.info := by
  constructor
  · intro h
    by_contra hne
    rcases not_and_or.mp hne with hne | hii
    · rcases not_and_or.mp (mt (fun h : y.truth ≤ x.truth ∧ x.truth ≤ y.truth ↦
          le_antisymm h.1 h.2) hne) with hyx | hxy
      · have hne' : y.truth ⊓ x.truthᶜ ≠ ⊥ := by rwa [← sdiff_eq, Ne, sdiff_eq_bot_iff]
        refine (h ⟨(y.truth ⊓ x.truthᶜ, y.truth), hne', inf_le_left⟩
          ⟨?_, le_rfl, inf_le_left.trans y.truth_le_info⟩).1 ?_
        · show y.truth ⊓ (y.truth ⊓ x.truthᶜ) ≠ ⊥
          rwa [inf_of_le_right inf_le_left]
        · show x.truth ⊓ (y.truth ⊓ x.truthᶜ) = ⊥
          rw [inf_comm y.truth, ← inf_assoc, inf_compl_eq_bot, bot_inf_eq]
      · exact hxy (h (diag y.truth y.truth_ne_bot) y.compat_diag_truth).2.1
    · exact hii (h (diag y.info y.info_ne_bot) y.compat_diag_info).2.2
  · rintro ⟨ha, hi⟩ z ⟨hz, hz', hz''⟩
    exact ⟨by rwa [← ha], ha ▸ hz', hz''.trans hi⟩

/-- `embed b` is the set of possibilities whose truth entails `b`, the underlying set of the
embedding `e_B` ([holliday-mandelkern-2024] Theorem 5.7.2). -/
def embed (b : B) : Set (Possibility B) := {x | x.truth ≤ b}

@[simp] theorem mem_embed {b : B} {x : Possibility B} : x ∈ embed b ↔ x.truth ≤ b := Iff.rfl

instance [DecidableLE B] (b : B) : DecidablePred (· ∈ embed b) :=
  fun x ↦ inferInstanceAs (Decidable (x.truth ≤ b))

instance [DecidableLE B] (b : B) : DecidablePred (embed b) :=
  fun x ↦ inferInstanceAs (Decidable (x.truth ≤ b))

/-- `b` must be the case at `(a, i)` iff `i ≤ b`. [holliday-mandelkern-2024] Lemma 5.8.2. -/
theorem mem_core_embed {b : B} {x : Possibility B} :
    x ∈ access.core (embed b) ↔ x.info ≤ b :=
  ⟨fun h ↦ h x.access_diag_info, fun h y hy ↦ (y.truth_le_info.trans hy.2).trans h⟩

/-- `b` might be the case at `(a, i)` iff `a ⊓ b ≠ ⊥`. [holliday-mandelkern-2024] Lemma 5.8.3. -/
theorem mem_diamond_embed {b : B} {x : Possibility B} :
    x ∈ diamond (epistemicFrame B) access (embed b) ↔ x.truth ⊓ b ≠ ⊥ := by
  constructor
  · intro h
    have := h _ x.compat_diag_truth
    simp only [mem_core, not_forall] at this
    obtain ⟨y', ⟨-, hy'a⟩, hy'⟩ := this
    simp only [mem_orthoNeg, not_forall, not_not] at hy'
    obtain ⟨y'', ⟨hne, -, -⟩, hy''⟩ := hy'
    exact ne_bot_of_le_ne_bot hne (inf_le_inf (y'.truth_le_info.trans hy'a) hy'')
  · intro h x' ⟨_, hx', _⟩ hbox
    have hle : x.truth ⊓ b ≤ x'.info := inf_le_left.trans hx'
    refine @hbox ⟨(x'.truth ⊔ x.truth ⊓ b, x'.info), ne_bot_of_le_ne_bot x'.truth_ne_bot
      le_sup_left, sup_le x'.truth_le_info hle⟩ ⟨le_sup_left, le_rfl⟩
      ⟨(x.truth ⊓ b, x'.info), h, hle⟩ ⟨?_, sup_le x'.truth_le_info hle, hle⟩ inf_le_right
    show (x'.truth ⊔ x.truth ⊓ b) ⊓ (x.truth ⊓ b) ≠ ⊥
    rwa [inf_of_le_right le_sup_right]

/-- Embedded propositions are regular, witnessed at `(a, i) ∉ e(b)` by `(a ⊓ bᶜ, i)`
([holliday-mandelkern-2024] Theorem 5.7.2). -/
theorem embed_isRegular (b : B) : IsRegular (epistemicFrame B) (embed b) := by
  intro x
  by_cases hx : x.truth ≤ b
  · exact Or.inl hx
  · right
    have hne : x.truth ⊓ bᶜ ≠ ⊥ := by rwa [← sdiff_eq, Ne, sdiff_eq_bot_iff]
    refine ⟨⟨(x.truth ⊓ bᶜ, x.info), hne, inf_le_left.trans x.truth_le_info⟩,
      ⟨?_, x.truth_le_info, inf_le_left.trans x.truth_le_info⟩, fun z ⟨hz, _, _⟩ hzb ↦ hz ?_⟩
    · show x.truth ⊓ (x.truth ⊓ bᶜ) ≠ ⊥
      rwa [inf_of_le_right inf_le_left]
    · show x.truth ⊓ bᶜ ⊓ z.truth = ⊥
      have : bᶜ ⊓ z.truth = ⊥ :=
        le_bot_iff.mp ((inf_le_inf_left _ hzb).trans compl_inf_eq_bot.le)
      rw [inf_assoc, this, inf_bot_eq]

/-- The embedding sends complements to orthocomplements.
[holliday-mandelkern-2024] Theorem 5.7.2. -/
theorem embed_compl (b : B) :
    embed bᶜ = orthoNeg (epistemicFrame B) (embed b) := by
  ext x
  simp only [mem_embed, mem_orthoNeg]
  constructor
  · intro hx y ⟨hne, _, _⟩ hy
    exact hne (le_bot_iff.mp ((inf_le_inf hx hy).trans compl_inf_eq_bot.le))
  · intro h
    by_contra hx
    have hne : x.truth ⊓ b ≠ ⊥ := by
      rwa [← compl_compl b, ← sdiff_eq, Ne, sdiff_eq_bot_iff]
    refine h ⟨(x.truth ⊓ b, x.info), hne, inf_le_left.trans x.truth_le_info⟩
      ⟨?_, x.truth_le_info, inf_le_left.trans x.truth_le_info⟩ inf_le_right
    show x.truth ⊓ (x.truth ⊓ b) ≠ ⊥
    rwa [inf_of_le_right inf_le_left]

/-- The embedding preserves meets. [holliday-mandelkern-2024] Theorem 5.7.2. -/
theorem embed_inf (b c : B) : embed (b ⊓ c) = embed b ∩ embed c := by
  ext x; exact le_inf_iff

/-- For embedded propositions, what is the case and compatible with `c` is compatible with
both, the inheritance principle of [holliday-mandelkern-2024] Proposition 5.12.3. -/
theorem embed_inter_diamond_embed_subset (b c : B) :
    embed b ∩ diamond (epistemicFrame B) access (embed c) ⊆
      diamond (epistemicFrame B) access (embed (b ⊓ c)) := by
  rintro x ⟨hb, hc⟩
  rw [mem_diamond_embed] at hc ⊢
  rwa [← inf_assoc, inf_of_le_left hb]

/-! ### The embedding into the regular propositions -/

/-- `eB b` is the regular proposition `e_B(b)` of the embedding of `B` into the regular
propositions of its epistemic frame ([holliday-mandelkern-2024] Theorem 5.7.2). -/
def eB (b : B) : (epistemicFrame B).Regular :=
  (epistemicFrame B).regOf (embed b) (embed_isRegular b)

@[simp] theorem coe_eB (b : B) : (eB b : Set (Possibility B)) = embed b := rfl

theorem eB_mono {b c : B} (h : b ≤ c) : eB b ≤ eB c := fun _ hx ↦ le_trans hx h

/-- `e_B` reflects order, as the possibility `(b, ⊤)` witnesses `b ≤ c` from
`e_B b ≤ e_B c`. -/
theorem eB_le_iff {b c : B} : eB b ≤ eB c ↔ b ≤ c := by
  refine ⟨fun h ↦ ?_, eB_mono⟩
  rcases eq_or_ne b ⊥ with rfl | hb
  · exact bot_le
  · exact @h ⟨(b, ⊤), hb, le_top⟩ le_rfl

theorem eB_injective : Function.Injective (eB : B → (epistemicFrame B).Regular) :=
  fun _ _ h ↦ le_antisymm (eB_le_iff.mp h.le) (eB_le_iff.mp h.ge)

theorem eB_top : eB (⊤ : B) = ⊤ := by
  apply SetLike.coe_injective
  rw [coe_eB, CompatFrame.Regular.coe_top]
  ext x; simp [embed]

theorem eB_bot : eB (⊥ : B) = ⊥ := by
  apply SetLike.coe_injective
  rw [coe_eB, CompatFrame.Regular.coe_bot]
  ext x; simp [embed, le_bot_iff, x.truth_ne_bot]

theorem eB_inf (b c : B) : eB (b ⊓ c) = eB b ⊓ eB c := by
  apply SetLike.coe_injective
  rw [coe_eB, CompatFrame.Regular.coe_inf, coe_eB, coe_eB, embed_inf]

theorem eB_compl (b : B) : eB bᶜ = (eB b)ᶜ := by
  apply SetLike.coe_injective
  rw [coe_eB, CompatFrame.Regular.coe_compl, coe_eB, embed_compl]

/-- The diamond of an embedded proposition strictly extends it unless the proposition is
trivial, since `(⊤, ⊤)` lies in `◇e(b)` but not in `e(b)` ([holliday-mandelkern-2024]
Theorem 5.7.4). -/
theorem not_diamond_embed_subset {b : B} (hb : b ≠ ⊥) (hb' : b ≠ ⊤) :
    ¬ diamond (epistemicFrame B) access (embed b) ⊆ embed b := by
  intro h
  have htop : (⊤ : B) ≠ ⊥ := ne_bot_of_le_ne_bot hb le_top
  have := h (a := ⟨(⊤, ⊤), htop, le_rfl⟩) (mem_diamond_embed.mpr (by rwa [top_inf_eq]))
  exact hb' (top_le_iff.mp this)

/-! ### The epistemic extension is S5 -/

instance : (access (B := B)).IsTrans := ⟨fun _ _ _ h h' ↦ ⟨h.1.trans h'.1, h'.2.trans h.2⟩⟩

/-- Whatever is the case must be possible, `U ⊆ □◇U` for every set `U`, witnessed by
`(a ⊔ a'', a ⊔ a'')` for `(a, i) ∈ U` (the proof of [holliday-mandelkern-2024]
Theorem 5.7.3). -/
theorem subset_core_diamond (U : Set (Possibility B)) :
    U ⊆ access.core (diamond (epistemicFrame B) access U) := by
  intro x hx x' hxx' x'' hc hbox
  have hne : x.truth ⊔ x''.truth ≠ ⊥ := ne_bot_of_le_ne_bot x.truth_ne_bot le_sup_left
  refine @hbox (diag _ hne) ⟨le_sup_right, sup_le (hxx'.1.trans hc.2.1) x''.truth_le_info⟩ x
    ⟨?_, sup_le x.truth_le_info (hc.2.2.trans hxx'.2), le_sup_left⟩ hx
  simp only [diag_truth, inf_of_le_right (le_sup_left : x.truth ≤ x.truth ⊔ x''.truth)]
  exact x.truth_ne_bot

/-- The 5 principle `◇U ≤ □◇U` in the epistemic extension of `B`, which is therefore an S5
epistemic ortholattice ([holliday-mandelkern-2024] Theorem 5.7.3). -/
theorem diamondHom_necHom_le (U : (epistemicFrame B).Regular) :
    diamondHom ((epistemicFrame B).necHom access) U ≤
      (epistemicFrame B).necHom access (diamondHom ((epistemicFrame B).necHom access) U) := by
  refine diamondHom_le_box_diamondHom (CompatFrame.necHom_le_necHom_necHom access) (fun V ↦ ?_) U
  rw [← SetLike.coe_subset_coe, CompatFrame.coe_necHom, CompatFrame.coe_diamondHom_necHom]
  exact subset_core_diamond (V : Set (Possibility B))

end Orthologic
