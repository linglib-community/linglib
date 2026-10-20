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
* `AR.free_realize_ofWords_iff`: a realized string of presentations reads as one.

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

instance [DecidableEq α] : DecidableEq (TwoTier α β true) := inferInstanceAs (DecidableEq α)

instance [DecidableEq β] : DecidableEq (TwoTier α β false) := inferInstanceAs (DecidableEq β)

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

/-- The representation of a melody `as` over a timing word `bs`, associated by `L` on
positions. -/
def ofWords (as : List α) (bs : List β) (L : ℕ → ℕ → Prop) : TieredAR Bool (TwoTier α β) :=
  ofData (TwoTier.words as bs) (TwoTier.Links L)

variable {as as' : List α} {bs bs' : List β} {L L' : ℕ → ℕ → Prop}

instance : Finite (ofWords as bs L).obj.V := inferInstanceAs (Finite ((_ : Bool) × Fin _))

@[simp] theorem tierWord_ofWords_true : (ofWords as bs L).tierWord true = as :=
  tierWord_ofData true

@[simp] theorem tierWord_ofWords_false : (ofWords as bs L).tierWord false = bs :=
  tierWord_ofData false

@[simp] theorem tierLength_ofWords_true : (ofWords as bs L).tierLength true = as.length :=
  tierLength_ofData true

@[simp] theorem tierLength_ofWords_false : (ofWords as bs L).tierLength false = bs.length :=
  tierLength_ofData false

@[simp] theorem link_ofWords {p q : ℕ} :
    (ofWords as bs L).link true false p q ↔ p < as.length ∧ q < bs.length ∧ L p q := by
  simp [ofWords, link_ofData, TwoTier.Links]

theorem not_link_ofWords_false (i j : Bool) (p q : ℕ) :
    ¬ (ofWords as bs fun _ _ => False).link i j p q := by
  grind [ofWords, link_ofData, TwoTier.Links]

/-- Two-tier links are determined by the melody-to-timing case. -/
theorem link_iff_of_true_false {τ : Bool → Type*} {X Y : TieredAR Bool τ}
    [Finite X.obj.V] [Finite Y.obj.V]
    (h : ∀ p q, X.link true false p q ↔ Y.link true false p q) (i j : Bool) (p q : ℕ) :
    X.link i j p q ↔ Y.link i j p q := by
  cases i <;> cases j <;> grind [not_link_self_tier, link_symm]

/-- The autosegmental graph primitive of [jardine-2019] Definition 1 has one timing slot `b`,
with every node of the melody `as` associated to it, as in the primitives of `gT`. -/
abbrev primitive (as : List α) (b : β) : TieredAR Bool (TwoTier α β) :=
  ofWords as [b] fun _ _ => True

/-! ### The No-Crossing Constraint on two tiers -/

/-- On two tiers, the NCC is order-respecting association from melody to timing. -/
theorem noCrossing_iff_two_tier {τ : Bool → Type*} (X : TieredAR Bool τ) [Finite X.obj.V] :
    NoCrossing X.obj.edges X.obj.arcs ↔ IsNonCrossing {x : ℕ × ℕ | X.link true false x.1 x.2} := by
  refine (noCrossing_iff X).trans ⟨fun h ↦ h true false, fun h i j ↦ ?_⟩
  cases i <;> cases j
  · exact fun a ha ↦ (X.not_link_self_tier _ _ _ ha).elim
  · exact (isNonCrossing_inv.2 h).subset fun _ hx ↦ X.link_symm hx
  · exact h
  · exact fun a ha ↦ (X.not_link_self_tier _ _ _ ha).elim

theorem noCrossing_ofWords_iff :
    NoCrossing (ofWords as bs L).obj.edges (ofWords as bs L).obj.arcs ↔
      IsNonCrossing {x : ℕ × ℕ | x.1 < as.length ∧ x.2 < bs.length ∧ L x.1 x.2} := by
  simp only [noCrossing_iff_two_tier, link_ofWords]

/-- A two-tier representation with at most one timing slot obeys the NCC. -/
theorem noCrossing_of_tierLength_false_le_one {τ : Bool → Type*} (X : TieredAR Bool τ)
    [Finite X.obj.V] (h : X.tierLength false ≤ 1) : NoCrossing X.obj.edges X.obj.arcs := by
  rw [noCrossing_iff_two_tier]
  rintro ⟨p, q⟩ ⟨-, hq, -⟩ ⟨p', q'⟩ ⟨-, hq', -⟩ -
  grind

/-- Primitives obey the NCC, having one timing slot ([jardine-2016b] Theorem 4). -/
theorem noCrossing_primitive (as : List α) (b : β) :
    NoCrossing (primitive as b).obj.edges (primitive as b).obj.arcs :=
  noCrossing_of_tierLength_false_le_one _ (by simp)

/-! ### Factor embedding -/

private theorem forall_getElem?_add_iff_prefix_drop {γ : Type*} {l l' : List γ} {o : ℕ} :
    (∀ p < l.length, l'[p + o]? = l[p]?) ↔ l <+: l'.drop o := by
  rw [List.prefix_iff_getElem?]
  refine forall_congr' fun p => ⟨fun h hp => ?_, fun h hp => ?_⟩
  · rw [List.getElem?_drop, Nat.add_comm o p, h hp, List.getElem?_eq_getElem hp]
  · rw [Nat.add_comm p o, ← List.getElem?_drop, h hp, List.getElem?_eq_getElem hp]

/-- One presentation embeds in another as a factor iff its tier words occur in the host's at
a pair of bounded offsets and its lines transport there. -/
theorem factorEmbeds_ofWords_iff :
    (ofWords as bs L).FactorEmbeds (ofWords as' bs' L') ↔
      ∃ ot ≤ as'.length, ∃ of ≤ bs'.length, as <+: as'.drop ot ∧ bs <+: bs'.drop of ∧
        ∀ p < as.length, ∀ q < bs.length, L p q → L' (p + ot) (q + of) := by
  rw [factorEmbeds_iff_bounded]
  constructor
  · rintro ⟨o, hb, hw, hl⟩
    refine ⟨o true, by simpa using hb true, o false, by simpa using hb false,
      forall_getElem?_add_iff_prefix_drop.mp fun p hp => ?_,
      forall_getElem?_add_iff_prefix_drop.mp fun p hp => ?_,
      fun p hp q hq hpq => (link_ofWords.mp (hl true false p q (link_ofWords.mpr
        ⟨hp, hq, hpq⟩))).2.2⟩
    · have := hw true p (by simpa using hp)
      simp only [tierWord_ofWords_true] at this
      exact this
    · have := hw false p (by simpa using hp)
      simp only [tierWord_ofWords_false] at this
      exact this
  · rintro ⟨ot, hot, of, hof, hwt, hwf, hlk⟩
    have hwt' := forall_getElem?_add_iff_prefix_drop.mpr hwt
    have hwf' := forall_getElem?_add_iff_prefix_drop.mpr hwf
    have key (p q : ℕ) (h : (ofWords as bs L).link true false p q) :
        (ofWords as' bs' L').link true false (p + ot) (q + of) := by
      obtain ⟨hp, hq, hpq⟩ := link_ofWords.mp h
      exact link_ofWords.mpr
        ⟨(List.getElem?_eq_some_iff.mp ((hwt' p hp).trans (List.getElem?_eq_getElem hp))).1,
          (List.getElem?_eq_some_iff.mp ((hwf' q hq).trans (List.getElem?_eq_getElem hq))).1,
          hlk p hp q hq hpq⟩
    refine ⟨fun b => bif b then ot else of, fun b => by cases b <;> simpa, ⟨?_, ?_⟩⟩
    · rintro (_ | _) p hp <;> simp at hp ⊢ <;> [exact hwf' p hp; exact hwt' p hp]
    · rintro (_ | _) (_ | _) p q hl
      · exact (not_link_self_tier _ _ _ hl).elim
      · exact link_symm (key q p (link_symm hl))
      · exact key p q hl
      · exact (not_link_self_tier _ _ _ hl).elim

instance [DecidableEq α] [DecidableEq β] [DecidableRel L] [DecidableRel L'] :
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

open scoped CategoryTheory.MonoidalCategory

theorem tierWord_realize_ofWords_true (w : List S) :
    (realize (fun s => ofWords (as s) (bs s) (L s)) w).tierWord true = (w.map as).flatten := by
  simp [tierWord_realize]

theorem tierWord_realize_ofWords_false (w : List S) :
    (realize (fun s => ofWords (as s) (bs s) (L s)) w).tierWord false = (w.map bs).flatten := by
  simp [tierWord_realize]

theorem link_realize_ofWords (w : List S) (p q : ℕ) :
    (realize (fun s => ofWords (as s) (bs s) (L s)) w).link true false p q ↔
      BlockLinks as bs L w p q := by
  induction w generalizing p q with
  | nil => simp [BlockLinks]
  | cons s w ih =>
    show (ofWords (as s) (bs s) (L s) ⊗ realize _ w).link true false p q ↔ _
    rw [link_tensor, ih]
    simp [BlockLinks]

/-- A realized string of presentations has the links of one presentation. -/
theorem link_realize_iff_link_ofWords (w : List S) (i j : Bool) (p q : ℕ) :
    (realize (fun s => ofWords (as s) (bs s) (L s)) w).link i j p q ↔
      (ofWords (w.map as).flatten (w.map bs).flatten (BlockLinks as bs L w)).link i j p q :=
  link_iff_of_true_false (fun p q => by grind [link_realize_ofWords, link_ofWords, BlockLinks.lt])
    i j p q

theorem free_realize_ofWords_iff
    (B : List {F : TieredAR Bool (TwoTier α β) // Finite F.obj.V}) (w : List S) :
    (realize (fun s => ofWords (as s) (bs s) (L s)) w).Free B ↔
      (ofWords (w.map as).flatten (w.map bs).flatten (BlockLinks as bs L w)).Free B :=
  free_congr (fun i => by
    cases i <;> simp [tierWord_realize_ofWords_true, tierWord_realize_ofWords_false])
    (link_realize_iff_link_ofWords as bs L w) B

end AR

end Realize

/-- Timing slot `j` surfaces with melody label `a` when some `a`-labelled melody node links to
it. -/
def AR.SurfacesWith (X : TieredAR Bool (TwoTier α β)) [Finite X.obj.V] (a : α) (j : ℕ) :
    Prop :=
  ∃ k, X.link true false k j ∧ (X.tierWord true)[k]? = some a

end Autosegmental
