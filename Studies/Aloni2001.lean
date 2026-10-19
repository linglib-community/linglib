module

public import Linglib.Semantics.Attitudes.Acquaintance
public import Linglib.Semantics.Reference.Rigidity
public import Studies.GroenendijkStokhof1984
public import Mathlib.Data.Finite.Perm
public import Mathlib.Logic.Equiv.Set
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Aloni (2001): Quantification under Conceptual Covers

An individual concept is a function from worlds to individuals, and a conceptual cover is a set
of concepts such that in each world each individual is the value of exactly one of them. Each
cover is a way of identifying the individuals across worlds; the name cover identifies each by its
constant concept. Aloni lets quantifiers range over the concepts of a contextually given cover, so
that a question partitions the worlds by which concepts of the cover have the questioned
property, and a de re report is true when some concept of the cover picks out the res and has the
property in every belief world.

## Main definitions

* `Aloni2001.IsCover`: conceptual covers.
* `Aloni2001.names`: the name cover.
* `Aloni2001.whoUnder`: a constituent question under a cover.
* `Aloni2001.DeReUnder`: a de re belief report under a cover.

## Main statements

* `Aloni2001.isCover_iff_existsUnique`: the existence and uniqueness conditions.
* `Aloni2001.IsCover.equiv`: Proposition 4.1.2.
* `Aloni2001.coverEquivPerm`, `Aloni2001.card_covers`: covers are the families of permutations
  trivial at a base world, and Proposition 4.1.3.
* `Aloni2001.IsCover.eq_names`, `Aloni2001.isCover_iff_eq_names`: a cover of rigid concepts is the
  name cover, and Corollary 4.1.4.
* `Aloni2001.whoUnder_names`: under the name cover a question is Groenendijk and Stokhof's.
* `Aloni2001.deReUnder_iff_exists_ascribesUnder`: a de re report under a cover is ascription
  under one of its concepts.
* `Aloni2001.Cards`: the cards of Sections 1.4.1 and 4.1, with their two covers, the
  identification question (186), the de re report (189), and the collapse of the covers once
  the cards are known.

## Implementation notes

* Worlds and individuals are types and concepts total functions, as in Definition 4.1.1.
* A question or a report takes its cover as an argument. The conceptual perspectives of
  Definition 1.4.1, which assign covers to variable indices, multiple-constituent questions, the
  dynamic semantics of Chapter 3 and the pragmatics of cover selection of Chapter 4 are not
  formalized.
* Questions are partitions, `Setoid`s, as in `GroenendijkStokhof1984`.

## References

* [aloni-2001]
* [groenendijk-stokhof-1984]
* [lewis-1979-attitudes]
-/

@[expose] public section

namespace Aloni2001

open Set Reference Acquaintance

variable {W D : Type*} {C : Set (W → D)} {c c' : W → D}

/-! ### Conceptual covers -/

/-- A conceptual cover (Definition 4.1.1) is a set of individual concepts such that in each
world each individual is the instantiation of one and only one of them. -/
def IsCover (C : Set (W → D)) : Prop := ∀ w, BijOn (· w) C univ

/-- The existence and uniqueness conditions of Section 1.4.1 say that in each world each
individual is the instantiation of exactly one concept of the cover. -/
theorem isCover_iff_existsUnique : IsCover C ↔ ∀ w d, ∃! c ∈ C, c w = d := by
  refine forall_congr' fun w ↦ ⟨fun h d ↦ ?_, fun h ↦ ⟨mapsTo_univ _ _, fun c hc c' hc' e ↦ ?_,
    fun d _ ↦ ?_⟩⟩
  · obtain ⟨c, hc, rfl⟩ := h.surjOn (mem_univ d)
    exact ⟨c, ⟨hc, rfl⟩, fun c' ⟨hc', e⟩ ↦ h.injOn hc' hc e⟩
  · exact (h (c w)).unique ⟨hc, rfl⟩ ⟨hc', e.symm⟩
  · obtain ⟨c, ⟨hc, e⟩, -⟩ := h d
    exact ⟨c, hc, e⟩

/-- Two concepts of a cover that coincide in one world coincide everywhere, so that they are
identical or separated. -/
theorem IsCover.eq_of_apply_eq (h : IsCover C) (hc : c ∈ C) (hc' : c' ∈ C) {w : W}
    (e : c w = c' w) : c = c' :=
  (h w).injOn hc hc' e

/-- In each world, instantiation is a one-to-one correspondence between a cover and the domain
(Proposition 4.1.2). -/
noncomputable def IsCover.equiv (h : IsCover C) (w : W) : C ≃ D :=
  ((h w).equiv _).trans (Equiv.Set.univ D)

@[simp] theorem IsCover.equiv_apply (h : IsCover C) (w : W) (c : C) : h.equiv w c = c.1 w := rfl

/-- A cover restricts to a cover of any set of worlds, the information state that remains when
the others are excluded. -/
theorem IsCover.image_domRestrict (h : IsCover C) (s : Set W) : IsCover (s.domRestrict '' C) := by
  intro w
  refine ⟨mapsTo_univ _ _, ?_, fun d _ ↦ ?_⟩
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ e
    rw [h.eq_of_apply_eq hc hc' e]
  · obtain ⟨c, hc, e⟩ := (h w).surjOn (mem_univ d)
    exact ⟨_, ⟨c, hc, rfl⟩, e⟩

/-! ### The name cover -/

/-- The name cover identifies each individual by its constant concept. -/
def names : Set (W → D) := range (Function.const W)

theorem isRigid_of_mem_names (h : c ∈ names) : IsRigid c := by
  obtain ⟨d, rfl⟩ := h
  exact isRigid_const d

theorem isCover_names : IsCover (names : Set (W → D)) := fun _ ↦
  ⟨mapsTo_univ _ _, by rintro _ ⟨d, rfl⟩ _ ⟨d', rfl⟩ (e : d = d'); rw [e],
    fun d _ ↦ ⟨_, ⟨d, rfl⟩, rfl⟩⟩

/-- A cover of rigid concepts is the name cover, the one rigid cover, against which the others
identify the individuals descriptively (Section 4.1). -/
theorem IsCover.eq_names [Nonempty W] (h : IsCover C) (hr : ∀ c ∈ C, IsRigid c) :
    C = names := by
  obtain ⟨w⟩ := ‹Nonempty W›
  ext c
  refine ⟨fun hc ↦ ⟨c w, ((hr c hc).eq_const w).symm⟩, ?_⟩
  rintro ⟨d, rfl⟩
  obtain ⟨c, hc, e⟩ := (h w).surjOn (mem_univ d)
  have hc' := (hr c hc).eq_const w
  rw [show c w = d from e] at hc'
  rwa [hc'] at hc

/-- Over a single world the name cover is the only cover (Corollary 4.1.4). -/
theorem isCover_iff_eq_names [Unique W] : IsCover C ↔ C = names :=
  ⟨fun h ↦ h.eq_names fun c _ ↦ isRigid_of_subsingleton c, fun h ↦ h ▸ isCover_names⟩

/-! ### Covers as cross-identifications -/

/-- The concepts that follow an individual through a family of permutations, one per world. -/
def ofPerm (σ : W → Equiv.Perm D) : Set (W → D) := range fun d w ↦ σ w d

theorem isCover_ofPerm (σ : W → Equiv.Perm D) : IsCover (ofPerm σ) := fun w ↦
  ⟨mapsTo_univ _ _,
    by rintro _ ⟨d, rfl⟩ _ ⟨d', rfl⟩ (e : σ w d = σ w d'); rw [(σ w).injective e],
    fun d _ ↦ ⟨_, ⟨(σ w).symm d, rfl⟩, (σ w).apply_symm_apply d⟩⟩

/-- The name cover follows each individual through the identity permutations. -/
theorem ofPerm_one : ofPerm (1 : W → Equiv.Perm D) = names := rfl

/-- Relative to a base world `w₀`, a cover is the family of permutations taking the individual each
of its concepts picks out at `w₀` to the one it picks out in each world, and every family trivial
at `w₀` comes from exactly one cover. A cover is thus a way of cross-identifying the individuals
of different worlds. -/
noncomputable def coverEquivPerm (w₀ : W) :
    {C : Set (W → D) // IsCover C} ≃ {σ : W → Equiv.Perm D // σ w₀ = 1} where
  toFun C := ⟨fun w ↦ (C.2.equiv w₀).symm.trans (C.2.equiv w), Equiv.symm_trans_self _⟩
  invFun σ := ⟨ofPerm σ.1, isCover_ofPerm σ.1⟩
  left_inv C := by
    obtain ⟨C, h⟩ := C
    refine Subtype.ext (Set.ext fun c ↦ ⟨?_, fun hc ↦ ⟨c w₀, ?_⟩⟩)
    · rintro ⟨d, rfl⟩
      exact ((h.equiv w₀).symm d).2
    · have : (h.equiv w₀).symm (c w₀) = ⟨c, hc⟩ := (h.equiv w₀).symm_apply_eq.2 rfl
      ext w
      simp [this]
  right_inv σ := by
    obtain ⟨σ, hσ⟩ := σ
    refine Subtype.ext (funext fun w ↦ Equiv.ext fun d ↦ ?_)
    have : ((isCover_ofPerm σ).equiv w₀).symm d = ⟨fun w ↦ σ w d, d, rfl⟩ :=
      Equiv.symm_apply_eq _ |>.2 (by simp [hσ])
    simp [this]

/-- The families of permutations of `G` trivial at `w₀` are the families over the other
worlds. -/
private def fixEquiv [DecidableEq W] (w₀ : W) (G : Type*) [One G] :
    {σ : W → G // σ w₀ = 1} ≃ ({w // w ≠ w₀} → G) where
  toFun σ w := σ.1 w
  invFun τ := ⟨fun w ↦ if h : w = w₀ then 1 else τ ⟨w, h⟩, dite_eq_left rfl⟩
  left_inv σ := Subtype.ext <| funext fun w ↦ by
    by_cases h : w = w₀
    · subst h; simp [σ.2]
    · simp [h]
  right_inv τ := funext fun w ↦ dite_eq_right w.2

open scoped Nat in
/-- Over finitely many worlds and individuals there are `(|D|!)^(|W|-1)` covers
(Proposition 4.1.3). -/
theorem card_covers [Finite W] [Finite D] [Nonempty W] :
    Nat.card {C : Set (W → D) // IsCover C} = (Nat.card D)! ^ (Nat.card W - 1) := by
  classical
  obtain ⟨w₀⟩ := ‹Nonempty W›
  have := Fintype.ofFinite W
  rw [Nat.card_congr ((coverEquivPerm w₀).trans (fixEquiv w₀ _)), Nat.card_fun, Nat.card_perm,
    Nat.card_eq_fintype_card (α := {w // w ≠ w₀}), Nat.card_eq_fintype_card (α := W)]
  simp

/-! ### Questions under cover -/

/-- The question *who has `P`?* under the cover `C` (Definition 1.4.2) relates two worlds when the
concepts of `C` that have `P` in the one are those that have it in the other. -/
def whoUnder (C : Set (W → D)) (P : D → Set W) : Setoid W :=
  Setoid.ker fun w ↦ {c ∈ C | w ∈ P (c w)}

theorem whoUnder_iff {P : D → Set W} {v w : W} :
    whoUnder C P v w ↔ ∀ c ∈ C, (v ∈ P (c v) ↔ w ∈ P (c w)) := by
  simp only [Setoid.ker_def, Set.ext_iff, Set.mem_ofPred_eq, and_congr_right_iff]

/-- Under the name cover, a question under cover is the question of [groenendijk-stokhof-1984]. -/
theorem whoUnder_names (P : D → Set W) : whoUnder names P = GroenendijkStokhof1984.who P :=
  Setoid.ext fun _ _ ↦ by
    rw [whoUnder_iff, GroenendijkStokhof1984.who_iff]
    simp [names]

/-! ### De re belief under cover -/

/-- The de re report `∃xₙ (xₙ = y ∧ □ P xₙ)` under the cover `C` with belief worlds `R` holds in
`w` (Definition 2.4.2) when some concept of the cover picks out `y` in `w` and has `P` in every
belief world. -/
def DeReUnder (C : Set (W → D)) (R : Set W) (y : D) (P : D → Set W) (w : W) : Prop :=
  ∃ c ∈ C, c w = y ∧ ∀ v ∈ R, v ∈ P (c v)

/-- A de re report under a cover holds when the believer ascribes the property to the res under
one of the cover's concepts, in the sense of [lewis-1979-attitudes] with worlds as centers. -/
theorem deReUnder_iff_exists_ascribesUnder {R : Set W} {y : D} {P : D → Set W} {w : W} :
    DeReUnder C R y P w ↔ ∃ c ∈ C, AscribesUnder R w (ofConcept c) y P := by
  unfold DeReUnder
  exact exists_congr fun _ ↦
    and_congr_right' (ascribesUnder_ofConcept.trans (and_congr_left' eq_comm)).symm

/-! ### The cards (Sections 1.4.1 and 4.1) -/

namespace Cards

/-- The Ace of Hearts and the Ace of Spades, lying face down. -/
inductive Card where
  | hearts
  | spades
  deriving DecidableEq, Fintype

/-- In `w₁` the Ace of Hearts is the card on the left, in `w₂` the card on the right. -/
inductive World where
  | w₁
  | w₂
  deriving DecidableEq, Fintype, Inhabited

open Card World

/-- The card on the left. -/
def left : World → Card
  | w₁ => hearts
  | w₂ => spades

/-- The card on the right. -/
def right : World → Card
  | w₁ => spades
  | w₂ => hearts

/-- The cover `A`, identifying the cards by their position on the table. -/
def byPosition : Set (World → Card) := {left, right}

/-- The cover `B`, identifying the cards by their suit, is the name cover. -/
def bySuit : Set (World → Card) := names

theorem isCover_byPosition : IsCover byPosition := by
  intro w
  refine ⟨mapsTo_univ _ _, ?_, fun d _ ↦ ?_⟩
  · rintro c (rfl | rfl) c' (rfl | rfl) e <;> first | rfl | (cases w <;> cases e)
  · cases w <;> cases d
    exacts [⟨left, .inl rfl, rfl⟩, ⟨right, .inr rfl, rfl⟩, ⟨right, .inr rfl, rfl⟩,
      ⟨left, .inl rfl, rfl⟩]

theorem left_notMem_names : left ∉ (names : Set (World → Card)) := by
  rintro ⟨d, e⟩
  exact absurd ((congrFun e w₁).symm.trans (congrFun e w₂)) (by decide : left w₁ ≠ left w₂)

/-- The set `C` of the card on the left and the Ace of Hearts is not a cover, since in `w₁` no
concept of it picks out the Ace of Spades and the Ace of Hearts is counted twice. -/
theorem not_isCover_mixed : ¬ IsCover {left, Function.const World hearts} := fun h ↦ by
  obtain ⟨c, hc | hc, e⟩ := (h w₁).surjOn (mem_univ spades) <;> subst hc <;> cases e

/-- There are exactly two covers, by position and by suit (Section 1.4.1), as Proposition 4.1.3
counts. -/
theorem isCover_iff {C : Set (World → Card)} : IsCover C ↔ C = byPosition ∨ C = bySuit := by
  refine ⟨fun h ↦ ?_, by rintro (rfl | rfl); exacts [isCover_byPosition, isCover_names]⟩
  have h2 : Nat.card {C : Set (World → Card) // IsCover C} = 2 := by
    rw [card_covers, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' ⟨byPosition, isCover_byPosition⟩).1 h2
  refine or_iff_not_imp_left.2 fun hC ↦ congrArg Subtype.val <|
    (hy ⟨C, h⟩ fun e ↦ hC (congrArg Subtype.val e)).trans
      (hy ⟨bySuit, isCover_names⟩ fun e ↦ left_notMem_names ?_).symm
  have : bySuit = byPosition := congrArg Subtype.val e
  change left ∈ bySuit
  rw [this]
  exact .inl rfl

/-- *Which card is the Ace of Hearts?* (186) asks who has the property of being the Ace of
Hearts. -/
def isHearts (d : Card) : Set World := {_w | d = hearts}

/-- Under the cover by position, (186) partitions the worlds into two blocks. -/
theorem whoUnder_byPosition : whoUnder byPosition isHearts = ⊥ :=
  Setoid.ext fun v w ↦ by
    rw [Setoid.bot_def, whoUnder_iff]
    cases v <;> cases w <;> simp [byPosition, isHearts, left, right]

/-- Under the cover by suit, (186) is vacuous. -/
theorem whoUnder_bySuit : whoUnder bySuit isHearts = ⊤ :=
  Setoid.eq_top_iff.2 fun v w ↦ whoUnder_iff.2 fun c ⟨d, e⟩ ↦ by
    subst e
    exact Iff.rfl

/-- The card on the left is marked. -/
def marked (d : Card) : Set World := {w | left w = d}

/-- Ralph believes that the Ace of Hearts is on the left. -/
def ralph : Set World := {w₁}

/-- *Ralph believes the Ace of Spades to be marked* (189), in the world `w₂` where the Ace of Spades
is on the left, is true under the cover by position. -/
theorem deReUnder_byPosition : DeReUnder byPosition ralph spades marked w₂ :=
  ⟨left, .inl rfl, rfl, by rintro _ rfl; rfl⟩

/-- (189) is false under the cover by suit, since Ralph does not take the Ace of Spades to be the
card on the left. -/
theorem not_deReUnder_bySuit : ¬ DeReUnder bySuit ralph spades marked w₂ := by
  rintro ⟨_, ⟨d, rfl⟩, hd, h⟩
  obtain rfl : d = spades := hd
  have h₁ : left w₁ = spades := h w₁ rfl
  exact absurd h₁ (by decide)

/-- Once you learn that the Ace of Hearts is on the right, the covers by position and by suit,
restricted to the information state `{w₂}`, are one and the same set of concepts, the only cover
over a single world (Section 4.1). -/
theorem restrict_byPosition_eq_restrict_bySuit :
    ({w₂} : Set World).domRestrict '' byPosition = ({w₂} : Set World).domRestrict '' bySuit :=
  (isCover_iff_eq_names.1 (isCover_byPosition.image_domRestrict _)).trans
    (isCover_iff_eq_names.1 (isCover_names.image_domRestrict _)).symm

end Cards

end Aloni2001
