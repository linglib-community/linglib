/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Factors
public import Linglib.Phonology.Autosegmental.Realization

/-!
# Two-tier autosegmental representations

A two-tier representation has a melody tier over `true` and a timing tier over `false`,
labelled by `TwoTier α β`. `AR.ofWords as bs L` presents one by its two tier words and a
relation `L` between their positions, the form in which the tone studies write
representations; `AR.primitive` is Jardine's autosegmental graph primitive, a melody over one
timing slot. On these presentations the No-Crossing Constraint is order-respecting
association, factor embedding is a bounded search over a pair of tier offsets, and the
realization of a string of presentations is again one.

## Main definitions

* `TwoTier α β`, `AR.ofWords`: the two-tier alphabet, and a representation from words.
* `AR.primitive`: a melody fully associated to one timing slot.
* `BlockLinks`: the lines of a realized string of presentations.
* `AR.SurfacesWith`: a timing slot linked to a given melody label.

## Main results

* `AR.noCrossing_ofWords_iff`, `AR.noCrossing_primitive`: the NCC on presentations, and
  for primitives (Theorem 4 of Jardine's dissertation).
* `AR.factorEmbeds_ofWords_iff`: factor embedding between presentations, hence decidable.
* `AR.prod_ofWords`: a realized string of presentations is one presentation.

## References

* [jardine-2016b]
* [jardine-2019]
-/

@[expose] public section

namespace Autosegmental

universe u
variable {α β : Type u}

/-- The two-tier alphabet puts melody labels over `true` and timing labels over `false`. -/
abbrev TwoTier (α β : Type u) : Bool → Type u := fun b => bif b then α else β

instance [DecidableEq α] [DecidableEq β] : ∀ b, DecidableEq (TwoTier α β b)
  | true => inferInstanceAs (DecidableEq α)
  | false => inferInstanceAs (DecidableEq β)

namespace TwoTier

/-- The tier words of a melody word and a timing word. -/
def words (as : List α) (bs : List β) : ∀ b : Bool, List (TwoTier α β b)
  | true => (as : List (TwoTier α β true))
  | false => (bs : List (TwoTier α β false))

@[simp] theorem words_true (as : List α) (bs : List β) : words as bs true = as := rfl

@[simp] theorem words_false (as : List α) (bs : List β) : words as bs false = bs := rfl

/-- Lines from melody position `p` to timing position `q` under `L`. -/
def Links (L : ℕ → ℕ → Prop) (i j : Bool) (p q : ℕ) : Prop := i = true ∧ j = false ∧ L p q

instance (L : ℕ → ℕ → Prop) [DecidableRel L] (i j : Bool) (p q : ℕ) :
    Decidable (Links L i j p q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end TwoTier

namespace AR

/-! ### Representations from words -/

variable {as as' : List α} {bs bs' : List β} {L L' : ℕ → ℕ → Prop} [DecidableRel L]
  [DecidableRel L']

variable (as bs L) in
/-- The representation of a melody `as` over a timing word `bs`, associated by `L` on
positions. -/
def ofWords : AR (TwoTier α β) :=
  fromRel (TwoTier.words as bs) (TwoTier.Links L)

@[simp] theorem word_ofWords_true : (ofWords as bs L).word true = as := rfl

@[simp] theorem word_ofWords_false : (ofWords as bs L).word false = bs := rfl

@[simp] theorem link_ofWords {p q : ℕ} :
    (ofWords as bs L).Link true false p q ↔ p < as.length ∧ q < bs.length ∧ L p q := by
  simp [ofWords, TwoTier.Links]

theorem not_link_ofWords_false (i j : Bool) (p q : ℕ) :
    ¬ (ofWords as bs fun _ _ ↦ False).Link i j p q := by
  simp [ofWords, TwoTier.Links]

/-- Two-tier lines are determined by the melody-to-timing case. -/
theorem link_iff_of_true_false {τ : Bool → Type*} {X Y : AR τ}
    (h : ∀ p q, X.Link true false p q ↔ Y.Link true false p q) (i j : Bool) (p q : ℕ) :
    X.Link i j p q ↔ Y.Link i j p q := by
  cases i <;> cases j
  · exact iff_of_false (fun h ↦ h.ne rfl) (fun h ↦ h.ne rfl)
  · exact link_comm.trans ((h q p).trans link_comm)
  · exact h p q
  · exact iff_of_false (fun h ↦ h.ne rfl) (fun h ↦ h.ne rfl)

/-- Two-tier representations are equal when their words and melody-to-timing lines are. -/
theorem ext_of_true_false {τ : Bool → Type*} {X Y : AR τ} (ht : X.word true = Y.word true)
    (hf : X.word false = Y.word false)
    (h : ∀ p q, X.Link true false p q ↔ Y.Link true false p q) : X = Y :=
  ext (funext fun b ↦ by cases b <;> assumption) (link_iff_of_true_false h)

variable (as) in
/-- The autosegmental graph primitive of [jardine-2019] Definition 1 has one timing slot `b`,
with every node of the melody `as` associated to it, as in the primitives of `gT`. -/
abbrev primitive (b : β) : AR (TwoTier α β) :=
  ofWords as [b] fun _ _ ↦ True

/-! ### The No-Crossing Constraint on two tiers -/

/-- On two tiers, the NCC is order-respecting association from melody to timing. -/
theorem noCrossing_iff_two_tier {τ : Bool → Type*} {X : AR τ} :
    X.NoCrossing ↔ IsNonCrossing (X.lines true false) := by
  refine ⟨fun h ↦ h true false, fun h i j ↦ ?_⟩
  cases i <;> cases j
  exacts [isNonCrossing_lines_self _, isNonCrossing_lines_comm.1 h, h, isNonCrossing_lines_self _]

theorem noCrossing_ofWords_iff : (ofWords as bs L).NoCrossing ↔
    IsNonCrossing {x : ℕ × ℕ | x.1 < as.length ∧ x.2 < bs.length ∧ L x.1 x.2} := by
  simp only [noCrossing_iff_two_tier, isNonCrossing_lines_iff_link, link_ofWords]

/-- A two-tier representation with at most one timing slot obeys the NCC. -/
theorem noCrossing_of_length_false_le_one {τ : Bool → Type*} {X : AR τ}
    (h : (X.word false).length ≤ 1) : X.NoCrossing :=
  noCrossing_iff_two_tier.2 <| isNonCrossing_lines_iff.2 fun _ _ _ _ h₁ h₂ _ ↦ by
    have := h₁.lt_right
    have := h₂.lt_right
    omega

/-- Primitives obey the NCC, having one timing slot ([jardine-2016b] Theorem 4). -/
theorem noCrossing_primitive (b : β) : (primitive as b).NoCrossing :=
  noCrossing_of_length_false_le_one (by simp)

/-! ### Factor embedding -/

private theorem forall_getElem?_add_iff_prefix_drop {γ : Type*} {l l' : List γ} {o : ℕ} :
    (∀ p < l.length, l'[p + o]? = l[p]?) ↔ l <+: l'.drop o := by
  rw [List.prefix_iff_getElem?]
  refine forall_congr' fun p => ⟨fun h hp => ?_, fun h hp => ?_⟩
  · rw [List.getElem?_drop, Nat.add_comm o p, h hp, List.getElem?_eq_getElem hp]
  · rw [Nat.add_comm p o, ← List.getElem?_drop, h hp, List.getElem?_eq_getElem hp]

/-- One presentation embeds in another as a factor iff its words occur in the host's at a pair
of bounded offsets and its lines transport there. -/
theorem factorEmbeds_ofWords_iff :
    (ofWords as bs L).FactorEmbeds (ofWords as' bs' L') ↔
      ∃ ot ≤ as'.length, ∃ of ≤ bs'.length, as <+: as'.drop ot ∧ bs <+: bs'.drop of ∧
        ∀ p < as.length, ∀ q < bs.length, L p q → L' (p + ot) (q + of) := by
  rw [factorEmbeds_iff_bounded]
  constructor
  · rintro ⟨o, hb, hw, hl⟩
    exact ⟨o true, hb true, o false, hb false,
      forall_getElem?_add_iff_prefix_drop.mp (hw true), forall_getElem?_add_iff_prefix_drop.mp
        (hw false), fun p hp q hq hpq ↦
          (link_ofWords.mp (hl true false p q (link_ofWords.mpr ⟨hp, hq, hpq⟩))).2.2⟩
  · rintro ⟨ot, hot, of, hof, hwt, hwf, hlk⟩
    have hwt' := forall_getElem?_add_iff_prefix_drop.mpr hwt
    have hwf' := forall_getElem?_add_iff_prefix_drop.mpr hwf
    have key (p q : ℕ) (h : (ofWords as bs L).Link true false p q) :
        (ofWords as' bs' L').Link true false (p + ot) (q + of) := by
      obtain ⟨hp, hq, hpq⟩ := link_ofWords.mp h
      exact link_ofWords.mpr
        ⟨(List.getElem?_eq_some_iff.mp ((hwt' p hp).trans (List.getElem?_eq_getElem hp))).1,
          (List.getElem?_eq_some_iff.mp ((hwf' q hq).trans (List.getElem?_eq_getElem hq))).1,
          hlk p hp q hq hpq⟩
    refine ⟨fun b ↦ bif b then ot else of, fun b ↦ by cases b <;> simpa, ⟨?_, ?_⟩⟩
    · rintro (_ | _) p hp
      exacts [hwf' p hp, hwt' p hp]
    · rintro (_ | _) (_ | _) p q hl
      · exact absurd rfl hl.ne
      · exact (key q p hl.symm).symm
      · exact key p q hl
      · exact absurd rfl hl.ne

instance [DecidableEq α] [DecidableEq β] :
    Decidable ((ofWords as bs L).FactorEmbeds (ofWords as' bs' L')) :=
  decidable_of_iff _ factorEmbeds_ofWords_iff.symm

end AR

/-! ### Realization of strings of presentations -/

section Realize

variable {S : Type*} (as : S → List α) (bs : S → List β) (L : S → ℕ → ℕ → Prop)

/-- A line of a string of presentations lies inside the first symbol's presentation, or past
its tier lengths inside the rest. -/
def BlockLinks : List S → ℕ → ℕ → Prop
  | [], _, _ => False
  | s :: w, p, q => p < (as s).length ∧ q < (bs s).length ∧ L s p q ∨
      (as s).length ≤ p ∧ (bs s).length ≤ q ∧
        BlockLinks w (p - (as s).length) (q - (bs s).length)

instance [∀ s, DecidableRel (L s)] : ∀ w, DecidableRel (BlockLinks as bs L w)
  | [], _, _ => inferInstanceAs (Decidable False)
  | _ :: w, _, _ =>
    haveI := instDecidableRelNatBlockLinks w
    inferInstanceAs (Decidable (_ ∨ _))

theorem BlockLinks.lt {w : List S} {p q : ℕ} (h : BlockLinks as bs L w p q) :
    p < (w.map as).flatten.length ∧ q < (w.map bs).flatten.length := by
  induction w generalizing p q with
  | nil => exact h.elim
  | cons s w ih => grind [BlockLinks, List.flatten_cons, List.length_append]

namespace AR

variable [∀ s, DecidableRel (L s)]

theorem word_prod_ofWords_true (w : List S) :
    (w.map fun s ↦ ofWords (as s) (bs s) (L s)).prod.word true = (w.map as).flatten := by
  simp [word_prod, Function.comp_def]

theorem word_prod_ofWords_false (w : List S) :
    (w.map fun s ↦ ofWords (as s) (bs s) (L s)).prod.word false = (w.map bs).flatten := by
  simp [word_prod, Function.comp_def]

theorem link_prod_ofWords (w : List S) (p q : ℕ) :
    (w.map fun s ↦ ofWords (as s) (bs s) (L s)).prod.Link true false p q ↔
      BlockLinks as bs L w p q := by
  induction w generalizing p q with
  | nil => simp [BlockLinks]
  | cons s w ih =>
    rw [List.map_cons, List.prod_cons, link_mul, ih]
    simp [BlockLinks]

/-- A realized string of presentations is one presentation. -/
theorem prod_ofWords (w : List S) :
    (w.map fun s ↦ ofWords (as s) (bs s) (L s)).prod =
      ofWords (w.map as).flatten (w.map bs).flatten (BlockLinks as bs L w) :=
  ext_of_true_false (word_prod_ofWords_true as bs L w) (word_prod_ofWords_false as bs L w)
    fun p q ↦ by grind [link_prod_ofWords, link_ofWords, BlockLinks.lt]

end AR

end Realize

/-- Timing slot `j` surfaces with melody label `a` when some `a`-labelled melody node links to
it. -/
def AR.SurfacesWith (X : AR (TwoTier α β)) (a : α) (j : ℕ) : Prop :=
  ∃ k, X.Link true false k j ∧ (X.word true)[k]? = some a

end Autosegmental
