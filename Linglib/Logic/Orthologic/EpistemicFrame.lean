module

public import Linglib.Logic.Orthologic.ModalFrame
public import Linglib.Core.Order.Interval.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.BooleanAlgebra.Basic

/-!
# The epistemic extension of a Boolean algebra

This file builds Holliday and Mandelkern's possibility model for epistemic modals out of a Boolean
algebra `B` of non-modal propositions. A possibility is an interval `[a, i]` of `B` with `a ≠ ⊥`:
`a` settles how things are and might be, and the information state `i` settles what must be the
case. Two possibilities are compatible when their lower ends are consistent and their intervals
overlap, and a possibility accesses the possibilities whose intervals lie within its own. Access
is then reflexive and transitive, R-regular and knowable, so the regular propositions of this
*epistemic frame* form an S5 epistemic ortholattice, the *epistemic extension* of `B`.

`B` embeds into its epistemic extension, preserving every meet and join that exists in `B` and
sending complements to orthocomplements. On an embedded proposition the modals reduce to `B`:
`b` must be the case at `[a, i]` iff `i ≤ b`, and might be iff `a` is not disjoint from `b`. So
`◇b` strictly extends `b` whenever `b` is neither `⊥` nor `⊤`, a modality that Wittgenstein's
Law rules out on a Boolean algebra (`Orthologic.WittgensteinLaw.eq_id`). On embedded propositions
the extension also validates principles that the logic EO+ does not derive, among them
restricted diamond distributivity.

## Main definitions

* `Orthologic.Possibility B`: the intervals `[a, i]` of `B` with `a ≠ ⊥`.
* `Orthologic.epistemicFrame B`, `Orthologic.Possibility.access`: the epistemic frame of `B`.
* `Orthologic.embed`: the embedding of `B` into the regular propositions.

## Main statements

* `Orthologic.isLUB_embed_image`: `embed` preserves the joins that exist in `B`.
* `Orthologic.mem_diamond_embed`: `b` might be the case at `[a, i]` iff `a` meets `b`.
* `Orthologic.diamondHom_le_necHom_diamondHom`: the epistemic extension is S5.
* `Orthologic.not_diamond_embed_subset`: `◇` does not collapse on embedded propositions.
* `Orthologic.restricted_diamond_distributivity_embed`: a principle beyond EO+.

## Implementation notes

A possibility is a `NonemptyInterval` with nonzero lower end. The order on intervals is inclusion,
so access is `≥` and its reflexivity and transitivity are those of the order, and the second
clause of compatibility is `NonemptyInterval.Overlaps`.

## References

* [holliday-mandelkern-2024]
-/

@[expose] public section

namespace Orthologic

open SetRel ModalLogic

variable {B : Type*} [BooleanAlgebra B]

variable (B) in
/-- A possibility of the epistemic frame of `B` is an interval `[a, i]` of `B` with `a ≠ ⊥`
([holliday-mandelkern-2024] Definition 5.1). -/
abbrev Possibility : Type _ := {s : NonemptyInterval B // s.fst ≠ ⊥}

namespace Possibility

variable (x y : Possibility B)

/-- The lower end `a` of `[a, i]` settles how things are and might be. -/
abbrev truth : B := x.1.fst

/-- The upper end `i` of `[a, i]`, its information state, settles what must be the case. -/
abbrev info : B := x.1.snd

theorem truth_ne_bot : x.truth ≠ ⊥ := x.2

theorem truth_le_info : x.truth ≤ x.info := x.1.fst_le_snd

theorem info_ne_bot : x.info ≠ ⊥ := ne_bot_of_le_ne_bot x.truth_ne_bot x.truth_le_info

/-- Two possibilities are compatible when their lower ends are consistent and their intervals
overlap ([holliday-mandelkern-2024] Definition 5.1.2). -/
def compat : Prop := ¬ Disjoint x.truth y.truth ∧ x.1.Overlaps y.1

/-- A possibility accesses the possibilities whose intervals lie within its own
([holliday-mandelkern-2024] Definition 5.1.3). -/
def access : SetRel (Possibility B) (Possibility B) := {p | p.2 ≤ p.1}

variable {x y}

@[simp] theorem access_iff : x ~[access] y ↔ y ≤ x := Iff.rfl

instance [DecidableEq B] [DecidableLE B] : Decidable (compat x y) :=
  haveI : Decidable (Disjoint x.truth y.truth) := decidable_of_iff' _ disjoint_iff
  inferInstanceAs (Decidable (¬ _ ∧ _))

instance [DecidableLE B] : Decidable (x ~[access] y) := inferInstanceAs (Decidable (y ≤ x))

/-- A possibility is compatible with any possibility whose interval contains its lower end. -/
theorem compat_of_truth_mem (h : x.truth ∈ y.1) : compat x y :=
  ⟨fun hd ↦ y.truth_ne_bot (hd.eq_bot_of_ge h.1), h.2, h.1.trans x.truth_le_info⟩

/-- `x.withTruth c` is `[c, i]` for `x = [a, i]` and a nonzero `c ≤ a`. -/
def withTruth (x : Possibility B) (c : B) (hc : c ≤ x.truth) (hc' : c ≠ ⊥) : Possibility B :=
  ⟨⟨(c, x.info), hc.trans x.truth_le_info⟩, hc'⟩

@[simp] theorem truth_withTruth {c : B} (hc : c ≤ x.truth) (hc' : c ≠ ⊥) :
    (x.withTruth c hc hc').truth = c := rfl

@[simp] theorem info_withTruth {c : B} (hc : c ≤ x.truth) (hc' : c ≠ ⊥) :
    (x.withTruth c hc hc').info = x.info := rfl

theorem compat_withTruth {c : B} (hc : c ≤ x.truth) (hc' : c ≠ ⊥) :
    compat x (x.withTruth c hc hc') :=
  compat_of_truth_mem ⟨hc, x.truth_le_info⟩

/-- `pure a ha` is the point interval `[a, a]`, which knows everything it settles. -/
def pure (a : B) (ha : a ≠ ⊥) : Possibility B := ⟨.pure a, ha⟩

@[simp] theorem truth_pure (a : B) (ha : a ≠ ⊥) : (pure a ha).truth = a := rfl

@[simp] theorem info_pure (a : B) (ha : a ≠ ⊥) : (pure a ha).info = a := rfl

/-- A possibility is compatible with the point `[c, c]` iff `c` lies in its interval. -/
theorem compat_pure_iff {c : B} (hc : c ≠ ⊥) : compat x (pure c hc) ↔ c ∈ x.1 :=
  ⟨And.right, fun h ↦ ⟨fun hd ↦ x.truth_ne_bot (hd.eq_bot_of_le h.1), h⟩⟩

theorem compat_pure_truth : compat x (pure x.truth x.truth_ne_bot) :=
  (compat_pure_iff _).2 ⟨le_rfl, x.truth_le_info⟩

theorem compat_pure_info : compat x (pure x.info x.info_ne_bot) :=
  (compat_pure_iff _).2 ⟨x.truth_le_info, le_rfl⟩

end Possibility

open Possibility

variable (B) in
/-- The epistemic frame of `B` is the compatibility frame on `Possibility B`
([holliday-mandelkern-2024] Definition 5.1). -/
def epistemicFrame : CompatFrame (Possibility B) where
  compat := compat
  compat_refl := ⟨fun x ↦ ⟨mt disjoint_self.1 x.truth_ne_bot, NonemptyInterval.overlaps_refl x.1⟩⟩
  compat_symm := ⟨fun _ _ h ↦ ⟨fun hd ↦ h.1 hd.symm, NonemptyInterval.overlaps_symm h.2⟩⟩

instance [DecidableEq B] [DecidableLE B] : DecidableRel (epistemicFrame B).compat :=
  inferInstanceAs (DecidableRel (compat (B := B)))

/-- Refinement in the epistemic frame keeps the lower end and narrows the information state,
`[a, i] ⊑ [a', i']` iff `a = a'` and `i ≤ i'` ([holliday-mandelkern-2024] Lemma 5.2). -/
theorem refines_iff (y x : Possibility B) :
    refines (epistemicFrame B) y x ↔ y.truth = x.truth ∧ y.info ≤ x.info := by
  refine ⟨fun h ↦ ⟨le_antisymm (by_contra fun hyx ↦ ?_) ?_, ?_⟩, fun ⟨ht, hi⟩ z hz ↦ ?_⟩
  · exact (h _ (y.compat_withTruth sdiff_le (mt sdiff_eq_bot_iff.1 hyx))).1
      disjoint_sdiff_self_right
  · exact ((compat_pure_iff _).1 (h _ y.compat_pure_truth)).1
  · exact ((compat_pure_iff _).1 (h _ y.compat_pure_info)).2
  · exact ⟨fun hd ↦ hz.1 (hd.mono_left ht.le), ht.ge.trans hz.2.1, hz.2.2.trans hi⟩

instance : (access (B := B)).IsRefl := ⟨fun _ ↦ access_iff.2 le_rfl⟩

instance : (access (B := B)).IsTrans :=
  ⟨fun _ _ _ h h' ↦ access_iff.2 ((access_iff.1 h').trans (access_iff.1 h))⟩

/-- Epistemic access is R-regular, witnessed by the point `[a ⊔ d, a ⊔ d]`
([holliday-mandelkern-2024] Theorem 5.7.1). -/
instance : IsRRegular (epistemicFrame B) access where
  rRegular x y' y hxy' hy'y := by
    let z := pure (x.truth ⊔ y.truth) (ne_bot_of_le_ne_bot x.truth_ne_bot le_sup_left)
    refine ⟨z, (compat_pure_iff _).2 ⟨le_sup_left, sup_le x.truth_le_info
      (hy'y.2.2.trans hxy'.2)⟩, fun x'' hx'' ↦ ⟨z, ⟨hx''.2.2, hx''.2.1⟩, compat_of_truth_mem ?_⟩⟩
    exact ⟨le_sup_right, sup_le (hxy'.1.trans hy'y.2.1) y.truth_le_info⟩

/-- Epistemic access is knowable, witnessed by the point `[a, a]` ([holliday-mandelkern-2024]
Theorem 5.7.1). -/
instance : IsKnowable (epistemicFrame B) access where
  knowable x := ⟨pure x.truth x.truth_ne_bot, fun z hz ↦ (refines_iff z x).2
    ⟨le_antisymm (z.truth_le_info.trans hz.2) hz.1, hz.2.trans x.truth_le_info⟩⟩

/-! ### The embedding of `B` -/

/-- `embed b` is the regular proposition `e_B(b)` of the possibilities whose lower end entails
`b`, regular since a possibility `[a, i]` outside it is compatible with `[a \ b, i]`, which is
compatible with nothing inside it ([holliday-mandelkern-2024] Theorem 5.7.2). -/
def embed (b : B) : (epistemicFrame B).Regular :=
  (epistemicFrame B).regOf {x | x.truth ≤ b} fun x ↦ or_iff_not_imp_left.2 fun hx ↦
    ⟨_, x.compat_withTruth sdiff_le (mt sdiff_eq_bot_iff.1 hx),
      fun _ hz hzb ↦ hz.1 (disjoint_sdiff_self_left.mono_right hzb)⟩

@[simp] theorem mem_embed {b : B} {x : Possibility B} : x ∈ embed b ↔ x.truth ≤ b := Iff.rfl

@[simp] theorem coe_embed (b : B) : (embed b : Set (Possibility B)) = {x | x.truth ≤ b} := rfl

instance [DecidableLE B] (b : B) : DecidablePred (· ∈ (embed b : Set (Possibility B))) :=
  fun x ↦ inferInstanceAs (Decidable (x.truth ≤ b))

theorem embed_mono : Monotone (embed (B := B)) := fun _ _ h _ hx ↦ hx.trans h

/-- `embed` reflects the order, as the possibility `[b, ⊤]` witnesses. -/
@[simp] theorem embed_le_embed {b c : B} : embed b ≤ embed c ↔ b ≤ c := by
  refine ⟨fun h ↦ ?_, fun h ↦ embed_mono h⟩
  rcases eq_or_ne b ⊥ with rfl | hb
  · exact bot_le
  · exact @h ⟨⟨(b, ⊤), le_top⟩, hb⟩ le_rfl

theorem embed_injective : Function.Injective (embed (B := B)) :=
  fun _ _ h ↦ le_antisymm (embed_le_embed.1 h.le) (embed_le_embed.1 h.ge)

/-- `embed` preserves every meet that exists in `B` ([holliday-mandelkern-2024] Theorem 5.7.2). -/
theorem isGLB_embed_image {s : Set B} {a : B} (h : IsGLB s a) :
    IsGLB (embed '' s) (embed a) :=
  ⟨Set.forall_mem_image.2 fun _ hb ↦ embed_mono (h.1 hb),
    fun _ hU _ hx ↦ h.2 fun _ hb ↦ hU (Set.mem_image_of_mem _ hb) hx⟩

/-- `embed` preserves every join that exists in `B`: a possibility compatible with one below the
join is compatible with one below a joinand ([holliday-mandelkern-2024] Theorem 5.7.2). -/
theorem isLUB_embed_image {s : Set B} {a : B} (h : IsLUB s a) :
    IsLUB (embed '' s) (embed a) := by
  refine ⟨Set.forall_mem_image.2 fun _ hb ↦ embed_mono (h.1 hb), fun U hU x hx ↦
    (U.isRegular x).resolve_right fun ⟨y, hxy, hy⟩ ↦ ?_⟩
  obtain ⟨b, hb, hcb⟩ : ∃ b ∈ s, ¬ Disjoint (x.truth ⊓ y.truth) b := by
    by_contra! hc
    have hca : Disjoint (x.truth ⊓ y.truth) a :=
      le_compl_iff_disjoint_left.1 (h.2 fun b hb ↦ (hc b hb).le_compl_left)
    exact hxy.1 (disjoint_iff.2 (hca.eq_bot_of_le (inf_le_left.trans hx)))
  exact hy _ (y.compat_withTruth (inf_le_left.trans inf_le_right) (mt disjoint_iff.2 hcb))
    (hU (Set.mem_image_of_mem _ hb) (show _ ≤ b from inf_le_right))

theorem embed_inf (b c : B) : embed (b ⊓ c) = embed b ⊓ embed c :=
  SetLike.coe_injective (Set.ext fun _ ↦ le_inf_iff)

theorem embed_sup (b c : B) : embed (b ⊔ c) = embed b ⊔ embed c :=
  (isLUB_embed_image isLUB_pair).unique (Set.image_pair embed b c ▸ isLUB_pair)

theorem embed_top : embed (⊤ : B) = ⊤ :=
  SetLike.coe_injective (Set.eq_univ_of_forall fun _ ↦ le_top)

theorem embed_bot : embed (⊥ : B) = ⊥ :=
  SetLike.coe_injective <| by ext x; simp [x.truth_ne_bot]

/-- `embed` sends complements to orthocomplements ([holliday-mandelkern-2024] Theorem 5.7.2). -/
theorem embed_compl (b : B) : embed bᶜ = (embed b)ᶜ := by
  refine SetLike.coe_injective (Set.ext fun x ↦ ?_)
  simp only [CompatFrame.Regular.coe_compl, coe_embed, Set.mem_ofPred_eq, mem_orthoNeg]
  refine ⟨fun hx y hxy hy ↦ hxy.1 (disjoint_compl_left.mono hx hy), fun h ↦ ?_⟩
  refine le_compl_iff_disjoint_right.2 (by_contra fun hd ↦ ?_)
  exact h _ (x.compat_withTruth inf_le_left (mt disjoint_iff.2 hd)) inf_le_right

/-- `b` must be the case at `[a, i]` iff `i ≤ b` ([holliday-mandelkern-2024] Lemma 5.8.2). -/
theorem mem_core_embed {b : B} {x : Possibility B} :
    x ∈ access.core (embed b) ↔ x.info ≤ b :=
  ⟨fun h ↦ @h (pure x.info x.info_ne_bot) ⟨x.truth_le_info, le_rfl⟩,
    fun h y hy ↦ (y.truth_le_info.trans hy.2).trans h⟩

/-- `b` cannot be the case at `[a, i]` iff `i` is disjoint from `b`, since `¬◇b = □bᶜ`. -/
theorem mem_orthoNeg_diamond_embed {b : B} {x : Possibility B} :
    x ∈ orthoNeg (epistemicFrame B) (diamond (epistemicFrame B) access (embed b)) ↔
      Disjoint x.info b := by
  rw [orthoNeg_diamond, ← CompatFrame.Regular.coe_compl, ← embed_compl, mem_core_embed,
    le_compl_iff_disjoint_right]

/-- `b` might be the case at `[a, i]` iff `a` is not disjoint from `b`
([holliday-mandelkern-2024] Lemma 5.8.3). -/
theorem mem_diamond_embed {b : B} {x : Possibility B} :
    x ∈ diamond (epistemicFrame B) access (embed b) ↔ ¬ Disjoint x.truth b := by
  rw [diamond, ← orthoNeg_diamond, mem_orthoNeg]
  simp only [mem_orthoNeg_diamond_embed]
  exact ⟨fun h hd ↦ h _ compat_pure_truth hd, fun h _ hxy hd ↦ h (hd.mono_left hxy.2.1)⟩

/-- The diamond of an embedded proposition other than `⊥` and `⊤` strictly extends it, as the
point `[⊤, ⊤]` witnesses ([holliday-mandelkern-2024] Theorem 5.7.4). -/
theorem not_diamond_embed_subset {b : B} (hb : b ≠ ⊥) (hb' : b ≠ ⊤) :
    ¬ diamond (epistemicFrame B) access (embed b) ⊆ embed b := fun h ↦
  hb' <| top_le_iff.1 <| @h (pure ⊤ (ne_bot_of_le_ne_bot hb le_top)) <|
    mem_diamond_embed.2 <| mt top_disjoint.1 hb

section Modalities

/-- `□` on the epistemic extension. -/
local notation "□ₑ" => CompatFrame.necHom (epistemicFrame _) access

/-- `◇` on the epistemic extension. -/
local notation "◇ₑ" => diamondHom (CompatFrame.necHom (epistemicFrame _) access)

/-! ### The epistemic extension is S5 -/

/-- Whatever is the case must be possible, `U ⊆ □◇U` (the proof of [holliday-mandelkern-2024]
Theorem 5.7.3). -/
theorem subset_core_diamond (U : Set (Possibility B)) :
    U ⊆ access.core (diamond (epistemicFrame B) access U) := by
  intro x hx x' hxx' x'' hc hbox
  refine @hbox (pure (x.truth ⊔ x''.truth) (ne_bot_of_le_ne_bot x.truth_ne_bot le_sup_left))
    ⟨le_sup_right, sup_le (hxx'.1.trans hc.2.1) x''.truth_le_info⟩ x
    (compat_of_truth_mem ⟨le_sup_left, sup_le x.truth_le_info (hc.2.2.trans hxx'.2)⟩) hx

/-- The 5 principle `◇U ≤ □◇U` in the epistemic extension of `B`, which is with T and 4 an S5
epistemic ortholattice ([holliday-mandelkern-2024] Theorem 5.7.3). -/
theorem diamondHom_le_necHom_diamondHom (U : (epistemicFrame B).Regular) : ◇ₑ U ≤ □ₑ (◇ₑ U) := by
  refine diamondHom_le_box_diamondHom (CompatFrame.necHom_le_necHom_necHom access) (fun V ↦ ?_) U
  rw [← SetLike.coe_subset_coe, CompatFrame.coe_necHom, CompatFrame.coe_diamondHom_necHom]
  exact subset_core_diamond (V : Set (Possibility B))

/-! ### Principles beyond EO+

The epistemic extension validates principles on embedded propositions that EO+ does not derive
([holliday-mandelkern-2024] Proposition 5.12). -/

/-- Restricted diamond distributivity: when each `Vⱼₖ ≤ Uⱼ`,
`(⋁ⱼ Uⱼ) ∧ ⋀ⱼ (◇Vⱼ₁ ∧ ⋯ ∧ ◇Vⱼₘ) ≤ ⋁ⱼ (Uⱼ ∧ ◇Vⱼ₁ ∧ ⋯ ∧ ◇Vⱼₘ)`, for any number of disjuncts
([holliday-mandelkern-2024] Proposition 5.12.1). -/
theorem restricted_diamond_distributivity_embed {ι : Sort*} {κ : ι → Type*} [∀ j, Finite (κ j)]
    (b : ι → B) (c : ∀ j, κ j → B) (hc : ∀ j k, c j k ≤ b j) :
    (⨆ j, embed (b j)) ⊓ ⨅ j, ⨅ k, ◇ₑ (embed (c j k)) ≤
      ⨆ j, embed (b j) ⊓ ⨅ k, ◇ₑ (embed (c j k)) := by
  have := fun j ↦ Fintype.ofFinite (κ j)
  rw [← SetLike.coe_subset_coe]
  simp only [CompatFrame.Regular.coe_inf, CompatFrame.Regular.coe_iInf,
    CompatFrame.Regular.coe_iSup, CompatFrame.coe_diamondHom_necHom]
  rintro x ⟨hb, hd⟩
  simp only [Set.mem_iInter, mem_diamond_embed, mem_orthoNeg, SetLike.mem_coe, mem_embed,
    not_forall, not_not, exists_prop, Set.mem_inter_iff] at hb hd ⊢
  intro y hxy
  obtain ⟨j, z, hwz, hzb⟩ := hb _ (x.compat_withTruth inf_le_left (mt disjoint_iff.2 hxy.1))
  have hj : x.truth ⊓ y.truth ⊓ b j ≠ ⊥ := fun h ↦ hwz.1 ((disjoint_iff.2 h).mono_right hzb)
  have hle : x.truth ⊓ y.truth ⊓ b j ⊔ Finset.univ.sup (fun k ↦ x.truth ⊓ c j k) ≤ y.info :=
    sup_le ((inf_le_left.trans inf_le_right).trans y.truth_le_info)
      (Finset.sup_le fun _ _ ↦ inf_le_left.trans hxy.2.1)
  refine ⟨j, ⟨⟨(_, y.info), hle⟩, ne_bot_of_le_ne_bot hj le_sup_left⟩,
    ⟨fun h ↦ hj (disjoint_self.1 (h.mono (inf_le_left.trans inf_le_right) le_sup_left)),
      y.truth_le_info, hle⟩,
    sup_le inf_le_right (Finset.sup_le fun k _ ↦ inf_le_right.trans (hc j k)), fun k h ↦ ?_⟩
  refine hd j k (disjoint_iff.2 (disjoint_self.1 (h.mono ?_ inf_le_right)))
  exact (Finset.le_sup (f := fun k ↦ x.truth ⊓ c j k) (Finset.mem_univ k)).trans le_sup_right

/-- Box distributivity: `(U₁ ∨ U₂) ∧ □V ≤ (U₁ ∧ □V) ∨ (U₂ ∧ □V)`
([holliday-mandelkern-2024] Proposition 5.12.2). -/
theorem box_distributivity_embed (b₁ b₂ c : B) :
    (embed b₁ ⊔ embed b₂) ⊓ □ₑ (embed c) ≤ embed b₁ ⊓ □ₑ (embed c) ⊔ embed b₂ ⊓ □ₑ (embed c) := by
  rw [← SetLike.coe_subset_coe]
  simp only [CompatFrame.Regular.coe_inf, CompatFrame.Regular.coe_sup, CompatFrame.coe_necHom,
    disj_eq_regularClosure_union]
  rintro x ⟨hx, hc⟩ x' hxx'
  obtain ⟨x'', hx'x'', hb⟩ := hx x' hxx'
  let z : Possibility B :=
    ⟨⟨(x'.truth ⊓ x''.truth, x'.truth), inf_le_left⟩, mt disjoint_iff.2 hx'x''.1⟩
  have hz : z ∈ access.core (embed c) := mem_core_embed.2 (hxx'.2.2.trans (mem_core_embed.1 hc))
  exact ⟨z, compat_of_truth_mem ⟨inf_le_left, le_rfl⟩,
    hb.imp (⟨inf_le_right.trans ·, hz⟩) (⟨inf_le_right.trans ·, hz⟩)⟩

/-- Inheritance: `U ∧ ◇V ≤ ◇(U ∧ V)` ([holliday-mandelkern-2024] Proposition 5.12.3). -/
theorem inheritance_embed (b c : B) : embed b ⊓ ◇ₑ (embed c) ≤ ◇ₑ (embed b ⊓ embed c) := by
  rw [← embed_inf, ← SetLike.coe_subset_coe]
  simp only [CompatFrame.Regular.coe_inf, CompatFrame.coe_diamondHom_necHom]
  rintro x ⟨hb, hc⟩
  rw [mem_diamond_embed] at hc ⊢
  rwa [← disjoint_assoc, inf_of_le_left hb]

/-- Diamond disjunctive syllogism A: `(U ∨ ◇V) ∧ ¬◇V ≤ U`
([holliday-mandelkern-2024] Proposition 5.12.4). -/
theorem diamond_disjunctive_syllogism_a_embed (b c : B) :
    (embed b ⊔ ◇ₑ (embed c)) ⊓ (◇ₑ (embed c))ᶜ ≤ embed b := by
  rw [← SetLike.coe_subset_coe]
  simp only [CompatFrame.Regular.coe_inf, CompatFrame.Regular.coe_sup,
    CompatFrame.Regular.coe_compl, CompatFrame.coe_diamondHom_necHom,
    disj_eq_regularClosure_union]
  rintro x ⟨hx, hc⟩
  rw [mem_orthoNeg_diamond_embed] at hc
  refine by_contra fun hxb ↦ ?_
  obtain ⟨z, hwz, hz | hz⟩ := hx _ (x.compat_withTruth sdiff_le (mt sdiff_eq_bot_iff.1 hxb))
  · exact hwz.1 (disjoint_sdiff_self_left.mono_right hz)
  · exact mem_diamond_embed.1 hz (hc.mono_left hwz.2.2)

/-- Diamond disjunctive syllogism B: `(U ∨ ◇V) ∧ ¬U ≤ ◇V`
([holliday-mandelkern-2024] Proposition 5.12.5). -/
theorem diamond_disjunctive_syllogism_b_embed (b c : B) :
    (embed b ⊔ ◇ₑ (embed c)) ⊓ (embed b)ᶜ ≤ ◇ₑ (embed c) := by
  rw [← embed_compl, ← SetLike.coe_subset_coe]
  simp only [CompatFrame.Regular.coe_inf, CompatFrame.Regular.coe_sup,
    CompatFrame.coe_diamondHom_necHom, disj_eq_regularClosure_union]
  rintro x ⟨hx, hb : x.truth ≤ bᶜ⟩
  refine mem_diamond_embed.2 fun hd ↦ ?_
  obtain ⟨z, hz, hzb | hzc⟩ := hx _ compat_pure_truth
  · exact hz.1 (disjoint_compl_left.mono hb hzb)
  · exact mem_diamond_embed.1 hzc (hd.mono_left hz.2.2)

end Modalities

end Orthologic
