module

public import Linglib.Logic.Team.BSML.Properties
public import Linglib.Logic.Team.Closure
public import Studies.Aloni2022

/-!
# Aloni, Anttila and Yang (2024): state-based modal logics for free choice

Aloni, Anttila and Yang extend bilateral state-based modal logic (BSML) in two ways. BSML⨼ adds
the global disjunction `⨼`, supported when either disjunct is, and BSML⊘ adds the emptiness
operator `⊘`, supported when its argument is or the state is empty. `NE` is the only obstruction
to downward closure and to the empty-state property, and `⨼` the only obstruction to union
closure. All three logics are invariant under bounded bisimulation, and BSML, though union
closed, cannot express every union-closed bisimulation-invariant property.

## Implementation notes

The three logics are fragments of one syntax: `Formula` carries `⊥`, `NE`, `⨼` and `⊘`
together, and `NEFree`, `GDFree` and `EmptFree` cut out the languages, so each closure property
is one theorem under its fragment hypothesis. Expressive completeness (Theorems 3.15 and 3.17)
and the natural-deduction systems of §4 are not formalized here; the BSML system lives in
`Logic/Team/BSML/NaturalDeduction.lean`.

## References

* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [anttila-2025] Anttila, Not Nothing: Nonemptiness in Team Semantics
-/

@[expose] public section

open scoped SetFamily

namespace AloniAnttilaYang2024

variable {W W' : Type*} [DecidableEq W] [DecidableEq W'] {Atom : Type*}

open ModalLogic (KripkeModel WorldBisim)
open Truthmaker (BilProp)

/-! ### Syntax and semantics -/

/-- The formulas of the joint syntax of BSML, BSML⨼ and BSML⊘ (Definition 2.1) are those of
    BSML together with the weak contradiction `⊥`, the global disjunction `⨼` and the
    emptiness operator `⊘`. -/
inductive Formula (Atom : Type*) where
  | atom (p : Atom)
  /-- Weak contradiction `⊥`, supported by the empty state only. -/
  | bot
  /-- Nonemptiness atom `NE`. -/
  | ne
  | neg (φ : Formula Atom)
  | conj (φ ψ : Formula Atom)
  /-- Tensor (local) disjunction. -/
  | disj (φ ψ : Formula Atom)
  /-- Global disjunction `⨼`. -/
  | gdisj (φ ψ : Formula Atom)
  /-- Emptiness operator `⊘`. -/
  | empt (φ : Formula Atom)
  | poss (φ : Formula Atom)
  deriving Repr, DecidableEq

namespace Formula

/-- `□φ := ¬◇¬φ`. -/
def nec (φ : Formula Atom) : Formula Atom := .neg (.poss (.neg φ))

/-- `φ.NEFree` holds when `φ` contains no `NE`. -/
def NEFree : Formula Atom → Prop
  | .ne => False
  | .neg φ | .empt φ | .poss φ => φ.NEFree
  | .conj φ ψ | .disj φ ψ | .gdisj φ ψ => φ.NEFree ∧ ψ.NEFree
  | _ => True

/-- `φ.GDFree` holds when `φ` contains no `⨼`, that is, when `φ` is a BSML⊘ formula. -/
def GDFree : Formula Atom → Prop
  | .gdisj _ _ => False
  | .neg φ | .empt φ | .poss φ => φ.GDFree
  | .conj φ ψ | .disj φ ψ => φ.GDFree ∧ ψ.GDFree
  | _ => True

/-- `φ.EmptFree` holds when `φ` contains no `⊘`, that is, when `φ` is a BSML⨼ formula. -/
def EmptFree : Formula Atom → Prop
  | .empt _ => False
  | .neg φ | .poss φ => φ.EmptFree
  | .conj φ ψ | .disj φ ψ | .gdisj φ ψ => φ.EmptFree ∧ ψ.EmptFree
  | _ => True

instance : (φ : Formula Atom) → Decidable φ.NEFree
  | .atom _ | .bot => isTrue trivial
  | .ne => isFalse id
  | .neg φ | .empt φ | .poss φ => by unfold NEFree; exact instDecidableNEFree φ
  | .conj φ ψ | .disj φ ψ | .gdisj φ ψ => by
    unfold NEFree; exact @instDecidableAnd _ _ (instDecidableNEFree φ) (instDecidableNEFree ψ)

instance : (φ : Formula Atom) → Decidable φ.GDFree
  | .atom _ | .bot | .ne => isTrue trivial
  | .gdisj _ _ => isFalse id
  | .neg φ | .empt φ | .poss φ => by unfold GDFree; exact instDecidableGDFree φ
  | .conj φ ψ | .disj φ ψ => by
    unfold GDFree; exact @instDecidableAnd _ _ (instDecidableGDFree φ) (instDecidableGDFree ψ)

instance : (φ : Formula Atom) → Decidable φ.EmptFree
  | .atom _ | .bot | .ne => isTrue trivial
  | .empt _ => isFalse id
  | .neg φ | .poss φ => by unfold EmptFree; exact instDecidableEmptFree φ
  | .conj φ ψ | .disj φ ψ | .gdisj φ ψ => by
    unfold EmptFree; exact @instDecidableAnd _ _ (instDecidableEmptFree φ) (instDecidableEmptFree ψ)

end Formula

/-- The meaning of a formula in a model (Definition 2.3) is the bilateral proposition of the
    teams that support it and the teams that anti-support it. -/
def Formula.den (M : KripkeModel W Atom) : Formula Atom → BilProp (Finset W)
  | .atom p => ⟨Team.flat (M.val p), Team.flat fun w ↦ ¬ M.val p w⟩
  | .bot => ⟨{∅}, .univ⟩
  | .ne => ⟨Team.ne, {∅}⟩
  | .neg φ => -φ.den M
  | .conj φ ψ => ⟨(φ.den M).ver ∩ (ψ.den M).ver, (φ.den M).fal ⊻ (ψ.den M).fal⟩
  | .disj φ ψ => ⟨(φ.den M).ver ⊻ (ψ.den M).ver, (φ.den M).fal ∩ (ψ.den M).fal⟩
  | .gdisj φ ψ => ⟨(φ.den M).ver ∪ (ψ.den M).ver, (φ.den M).fal ∩ (ψ.den M).fal⟩
  | .empt φ => ⟨(φ.den M).ver ∪ {∅}, (φ.den M).fal⟩
  | .poss φ => ⟨Team.poss M.access (φ.den M).ver, Team.nec M.access (φ.den M).fal⟩

abbrev support (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  t ∈ (φ.den M).ver

abbrev antiSupport (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  t ∈ (φ.den M).fal

variable (M : KripkeModel W Atom) (φ ψ χ : Formula Atom) (t : Finset W)

@[simp] theorem support_neg : support M (.neg φ) t ↔ antiSupport M φ t := Iff.rfl
@[simp] theorem antiSupport_neg : antiSupport M (.neg φ) t ↔ support M φ t := Iff.rfl
@[simp] theorem support_bot : support M (.bot : Formula Atom) t ↔ t = ∅ := Iff.rfl
@[simp] theorem antiSupport_bot : antiSupport M (.bot : Formula Atom) t := trivial
@[simp] theorem support_ne : support M (.ne : Formula Atom) t ↔ t.Nonempty := Iff.rfl
@[simp] theorem antiSupport_ne : antiSupport M (.ne : Formula Atom) t ↔ t = ∅ := Iff.rfl
@[simp] theorem support_conj : support M (.conj φ ψ) t ↔ support M φ t ∧ support M ψ t := Iff.rfl
@[simp] theorem antiSupport_disj :
    antiSupport M (.disj φ ψ) t ↔ antiSupport M φ t ∧ antiSupport M ψ t := Iff.rfl
@[simp] theorem support_gdisj : support M (.gdisj φ ψ) t ↔ support M φ t ∨ support M ψ t := Iff.rfl
@[simp] theorem antiSupport_gdisj :
    antiSupport M (.gdisj φ ψ) t ↔ antiSupport M φ t ∧ antiSupport M ψ t := Iff.rfl
@[simp] theorem support_empt : support M (.empt φ) t ↔ support M φ t ∨ t = ∅ := Iff.rfl
@[simp] theorem antiSupport_empt : antiSupport M (.empt φ) t ↔ antiSupport M φ t := Iff.rfl

/-! ### The §2 equivalences -/

/-- `⊘φ ≡ φ ⨼ ⊥`. -/
theorem support_empt_iff_gdisj_bot : support M (.empt φ) t ↔ support M (.gdisj φ .bot) t :=
  Iff.rfl

theorem support_conj_gdisj :
    support M (.conj φ (.gdisj ψ χ)) t ↔ support M (.gdisj (.conj φ ψ) (.conj φ χ)) t :=
  and_or_left

theorem support_disj_gdisj :
    support M (.disj φ (.gdisj ψ χ)) t ↔ support M (.gdisj (.disj φ ψ) (.disj φ χ)) t := by
  constructor
  · rintro ⟨t₁, h₁, t₂, h₂ | h₂, h⟩
    exacts [Or.inl ⟨t₁, h₁, t₂, h₂, h⟩, Or.inr ⟨t₁, h₁, t₂, h₂, h⟩]
  · rintro (⟨t₁, h₁, t₂, h₂, h⟩ | ⟨t₁, h₁, t₂, h₂, h⟩)
    exacts [⟨t₁, h₁, t₂, Or.inl h₂, h⟩, ⟨t₁, h₁, t₂, Or.inr h₂, h⟩]

/-- The diamond converts global to tensor disjunction, `◇(φ ⨼ ψ) ≡ ◇φ ∨ ◇ψ`, so the rule Conv◇⨼∨ of
Theorem 4.3 is sound. -/
theorem support_poss_gdisj :
    support M (.poss (.gdisj φ ψ)) t ↔ support M (.disj (.poss φ) (.poss ψ)) t :=
  .of_eq (congrArg (t ∈ ·) (Team.poss_union M.access _ _))

/-! ### Closure properties (Fact 2.7) -/

private theorem empty_mem_den_of_neFree (hNE : φ.NEFree) :
    ∅ ∈ (φ.den M).ver ∧ ∅ ∈ (φ.den M).fal := by
  induction φ with
  | atom p => exact ⟨fun w hw ↦ absurd hw (by simp), fun w hw ↦ absurd hw (by simp)⟩
  | bot => exact ⟨rfl, trivial⟩
  | ne => exact hNE.elim
  | neg ψ ih => exact (ih hNE).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨⟨(ih₁ hNE.1).1, (ih₂ hNE.2).1⟩, Set.bot_mem_sups (ih₁ hNE.1).2 (ih₂ hNE.2).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨Set.bot_mem_sups (ih₁ hNE.1).1 (ih₂ hNE.2).1, ⟨(ih₁ hNE.1).2, (ih₂ hNE.2).2⟩⟩
  | gdisj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨Or.inl (ih₁ hNE.1).1, ⟨(ih₁ hNE.1).2, (ih₂ hNE.2).2⟩⟩
  | empt ψ ih => exact ⟨Or.inr rfl, (ih hNE).2⟩
  | poss ψ _ => exact ⟨fun w hw ↦ absurd hw (by simp), fun w hw ↦ absurd hw (by simp)⟩

theorem support_empty_of_neFree (hNE : φ.NEFree) : support M φ ∅ :=
  (empty_mem_den_of_neFree M φ hNE).1

private theorem union_inter_of_union_eq {s t t₁ t₂ : Finset W} (h : t₁ ∪ t₂ = s) (hsub : t ⊆ s) :
    (t₁ ∩ t) ∪ (t₂ ∩ t) = t := by
  rw [← Finset.union_inter_distrib_right, h]
  exact Finset.inter_eq_right.mpr hsub

private theorem isLowerSet_den_of_neFree (hNE : φ.NEFree) :
    IsLowerSet (φ.den M).ver ∧ IsLowerSet (φ.den M).fal := by
  induction φ with
  | atom p => exact ⟨Team.isLowerSet_flat _, Team.isLowerSet_flat _⟩
  | bot => exact ⟨Team.isLowerSet_singleton_empty, isLowerSet_univ⟩
  | ne => exact hNE.elim
  | neg ψ ih => exact (ih hNE).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨(ih₁ hNE.1).1.inter (ih₂ hNE.2).1, (ih₁ hNE.1).2.sups (ih₂ hNE.2).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨(ih₁ hNE.1).1.sups (ih₂ hNE.2).1, (ih₁ hNE.1).2.inter (ih₂ hNE.2).2⟩
  | gdisj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨(ih₁ hNE.1).1.union (ih₂ hNE.2).1, (ih₁ hNE.1).2.inter (ih₂ hNE.2).2⟩
  | empt ψ ih => exact ⟨(ih hNE).1.union Team.isLowerSet_singleton_empty, (ih hNE).2⟩
  | poss ψ _ => exact ⟨Team.isLowerSet_flat _, Team.isLowerSet_flat _⟩

/-- NE-free formulas are downward closed. -/
theorem isLowerSet_support_of_neFree (hNE : φ.NEFree) :
    IsLowerSet { t : Finset W | support M φ t } :=
  (isLowerSet_den_of_neFree M φ hNE).1

private theorem supClosed_den_of_gdFree (hGD : φ.GDFree) :
    SupClosed (φ.den M).ver ∧ SupClosed (φ.den M).fal := by
  induction φ with
  | atom p => exact ⟨Team.supClosed_flat _, Team.supClosed_flat _⟩
  | bot => exact ⟨Team.supClosed_singleton_empty, supClosed_univ⟩
  | ne => exact ⟨Team.supClosed_ne, Team.supClosed_singleton_empty⟩
  | neg ψ ih => exact (ih hGD).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨(ih₁ hGD.1).1.inter (ih₂ hGD.2).1, (ih₁ hGD.1).2.sups (ih₂ hGD.2).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨(ih₁ hGD.1).1.sups (ih₂ hGD.2).1, (ih₁ hGD.1).2.inter (ih₂ hGD.2).2⟩
  | gdisj => exact hGD.elim
  | empt ψ ih =>
    refine ⟨fun s hs t ht ↦ ?_, (ih hGD).2⟩
    rcases hs with hs | rfl <;> rcases ht with ht | rfl
    · exact Or.inl ((ih hGD).1 hs ht)
    · simpa using Or.inl hs
    · simpa using Or.inl ht
    · simp
  | poss ψ _ => exact ⟨Team.supClosed_flat _, Team.supClosed_flat _⟩

/-- ⨼-free formulas are union closed; in particular every BSML⊘ formula is. -/
theorem supClosed_support_of_gdFree (hGD : φ.GDFree) :
    SupClosed { t : Finset W | support M φ t } :=
  (supClosed_den_of_gdFree M φ hGD).1

/-- Classical formulas — NE-free and ⨼-free — are flat. -/
theorem isFlat_support_of_neFree_gdFree (hNE : φ.NEFree) (hGD : φ.GDFree) :
    Team.IsFlat { t : Finset W | support M φ t } :=
  Team.isFlat_of_isLowerSet_supClosed_empty (isLowerSet_support_of_neFree M φ hNE)
    (supClosed_support_of_gdFree M φ hGD) (support_empty_of_neFree M φ hNE)

/-! ### BSML is not complete for union-closed properties -/

-- Lemma 3.18
theorem isLowerSet_of_support_empty (hGD : φ.GDFree) (hE : φ.EmptFree) :
    (support M φ ∅ → ∀ s t : Finset W, t ⊆ s → support M φ s → support M φ t) ∧
    (antiSupport M φ ∅ → ∀ s t : Finset W, t ⊆ s → antiSupport M φ s → antiSupport M φ t) := by
  induction φ with
  | atom p => exact ⟨fun _ _ _ h hs w hw ↦ hs w (h hw), fun _ _ _ h hs w hw ↦ hs w (h hw)⟩
  | bot => exact ⟨fun _ _ _ h hs ↦ Finset.subset_empty.mp (hs ▸ h), fun _ _ _ _ _ ↦ trivial⟩
  | ne =>
    exact ⟨fun h ↦ absurd h Finset.not_nonempty_empty,
      fun _ _ _ h hs ↦ by rw [hs] at h; exact Finset.subset_empty.mp h⟩
  | neg ψ ih => exact (ih hGD hE).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨ihs₁, iha₁⟩ := ih₁ hGD.1 hE.1
    obtain ⟨ihs₂, iha₂⟩ := ih₂ hGD.2 hE.2
    refine ⟨fun ⟨e₁, e₂⟩ s t h ⟨h₁, h₂⟩ ↦ ⟨ihs₁ e₁ s t h h₁, ihs₂ e₂ s t h h₂⟩, ?_⟩
    rintro ⟨u₁, e₁, u₂, e₂, hu⟩ s t h ⟨t₁, h₁, t₂, h₂, hsplit⟩
    have hu₁ : u₁ = ∅ := Finset.subset_empty.mp (le_sup_left.trans_eq hu)
    have hu₂ : u₂ = ∅ := Finset.subset_empty.mp (le_sup_right.trans_eq hu)
    subst hu₁ hu₂
    exact ⟨t₁ ∩ t, iha₁ e₁ t₁ _ Finset.inter_subset_left h₁, t₂ ∩ t,
      iha₂ e₂ t₂ _ Finset.inter_subset_left h₂, union_inter_of_union_eq hsplit h⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨ihs₁, iha₁⟩ := ih₁ hGD.1 hE.1
    obtain ⟨ihs₂, iha₂⟩ := ih₂ hGD.2 hE.2
    refine ⟨?_, fun ⟨e₁, e₂⟩ s t h ⟨h₁, h₂⟩ ↦ ⟨iha₁ e₁ s t h h₁, iha₂ e₂ s t h h₂⟩⟩
    rintro ⟨u₁, e₁, u₂, e₂, hu⟩ s t h ⟨t₁, h₁, t₂, h₂, hsplit⟩
    have hu₁ : u₁ = ∅ := Finset.subset_empty.mp (le_sup_left.trans_eq hu)
    have hu₂ : u₂ = ∅ := Finset.subset_empty.mp (le_sup_right.trans_eq hu)
    subst hu₁ hu₂
    exact ⟨t₁ ∩ t, ihs₁ e₁ t₁ _ Finset.inter_subset_left h₁, t₂ ∩ t,
      ihs₂ e₂ t₂ _ Finset.inter_subset_left h₂, union_inter_of_union_eq hsplit h⟩
  | gdisj => exact hGD.elim
  | empt => exact hE.elim
  | poss ψ _ => exact ⟨fun _ _ _ h hs w hw ↦ hs w (h hw), fun _ _ _ h hs w hw ↦ hs w (h hw)⟩

/-- The two-world model of Fact 3.19 makes `p` true at `true` only and has no accessible
    worlds. -/
def twoWorlds : KripkeModel Bool Unit where
  access _ := ∅
  val _ w := w = true

/-- The property `‖(p ∧ NE) ∨ (¬p ∧ NE)‖ ∪ ‖⊥‖` of Fact 3.19 is union closed and bisimulation
    invariant, yet not expressible in BSML. -/
def splitProperty (s : Finset Bool) : Prop :=
  support twoWorlds (.disj (.conj (.atom ()) .ne) (.conj (.neg (.atom ())) .ne)) s ∨ s = ∅

/-- No BSML formula expresses `splitProperty` (Fact 3.19), since it would be downward closed (Lemma
3.18). -/
theorem bsml_not_complete_for_unionClosed :
    ¬ ∃ φ : Formula Unit, φ.GDFree ∧ φ.EmptFree ∧
      ∀ s : Finset Bool, support twoWorlds φ s ↔ splitProperty s := by
  rintro ⟨φ, hGD, hE, h⟩
  have hempty : support twoWorlds φ ∅ := (h ∅).mpr (Or.inr rfl)
  have hboth : support twoWorlds φ {true, false} := (h _).mpr <| Or.inl
    ⟨{true}, ⟨fun w hw ↦ by simpa [twoWorlds] using hw, by simp⟩,
      {false}, ⟨fun w hw ↦ by simpa [twoWorlds] using hw, by simp⟩, rfl⟩
  have htrue := (h {true}).mp
    ((isLowerSet_of_support_empty twoWorlds φ hGD hE).1 hempty _ _ (by simp) hboth)
  rcases htrue with ⟨t₁, -, t₂, ⟨hp, hne⟩, hsplit⟩ | h1
  · obtain ⟨w, hw⟩ := hne
    have : w ∈ ({true} : Finset Bool) := hsplit ▸ Finset.mem_union_right _ hw
    have hw' := hp w hw
    simp_all [twoWorlds]
  · exact absurd h1 (by simp)

/-! ### The emptiness operator cancels enrichment -/

/-- For classical `α`, `⊘(α ∧ NE) ≡ α` (§5), so the emptiness operator undoes the
    non-emptiness that pragmatic enrichment adds. -/
theorem support_empt_conj_ne (hα : φ.NEFree) :
    support M (.empt (.conj φ .ne)) t ↔ support M φ t := by
  constructor
  · rintro (⟨h, _⟩ | rfl)
    exacts [h, support_empty_of_neFree M φ hα]
  · intro h
    rcases t.eq_empty_or_nonempty with rfl | hne
    exacts [Or.inr rfl, Or.inl ⟨h, hne⟩]

/-! ### The embedding of BSML -/

/-- BSML formulas as formulas of the joint language. -/
def ofBSML : BSML.Formula Atom → Formula Atom
  | .atom p => .atom p
  | .ne => .ne
  | .neg ψ => .neg (ofBSML ψ)
  | .conj ψ₁ ψ₂ => .conj (ofBSML ψ₁) (ofBSML ψ₂)
  | .disj ψ₁ ψ₂ => .disj (ofBSML ψ₁) (ofBSML ψ₂)
  | .poss ψ => .poss (ofBSML ψ)

theorem gdFree_ofBSML (φ : BSML.Formula Atom) : (ofBSML φ).GDFree := by
  induction φ <;> simp_all [ofBSML, Formula.GDFree]

theorem emptFree_ofBSML (φ : BSML.Formula Atom) : (ofBSML φ).EmptFree := by
  induction φ <;> simp_all [ofBSML, Formula.EmptFree]

-- The embedding preserves meaning: a BSML formula means the same in the joint language.
theorem den_ofBSML (φ : BSML.Formula Atom) : (ofBSML φ).den M = φ.den M := by
  induction φ with
  | atom p => rfl
  | ne => rfl
  | neg ψ ih => exact congrArg Neg.neg ih
  | conj ψ₁ ψ₂ ih₁ ih₂ => simp only [ofBSML, Formula.den, BSML.Formula.den, ih₁, ih₂]
  | disj ψ₁ ψ₂ ih₁ ih₂ => simp only [ofBSML, Formula.den, BSML.Formula.den, ih₁, ih₂]
  | poss ψ ih => simp only [ofBSML, Formula.den, BSML.Formula.den, ih]

theorem support_ofBSML (φ : BSML.Formula Atom) : support M (ofBSML φ) t ↔ BSML.support M φ t :=
  .of_eq (congrArg (t ∈ ·.ver) (den_ofBSML M φ))

/-- Narrow-scope free choice, `[◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β`, transported from
    [aloni-2022] along the embedding. -/
theorem narrowScopeFC {α β : BSML.Formula Atom} (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (ofBSML (BSML.enrich (.poss (.disj α β)))) t) :
    support M (ofBSML (.conj (.poss α) (.poss β))) t :=
  (support_ofBSML M t _).mpr (Aloni2022.narrowScopeFC hα hβ ((support_ofBSML M t _).mp h))

/-! ### Bisimulation invariance (Theorem 3.8) -/

/-- The modal depth of a formula is the greatest number of nested `◇`s in it. -/
def Formula.modalDepth : Formula Atom → ℕ
  | .atom _ | .bot | .ne => 0
  | .neg ψ | .empt ψ => ψ.modalDepth
  | .conj ψ₁ ψ₂ | .disj ψ₁ ψ₂ | .gdisj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .poss ψ => ψ.modalDepth + 1

/-- Teams that are `k`-bisimilar agree on every formula of modal depth at most `k`, in both
    polarities (Theorem 3.8). -/
theorem invariant_den {M : KripkeModel W Atom} {M' : KripkeModel W' Atom} {k : ℕ}
    (φ : Formula Atom) (hd : φ.modalDepth ≤ k) :
    Team.Invariant (WorldBisim k M · M' ·) (φ.den M).ver (φ.den M').ver ∧
      Team.Invariant (WorldBisim k M · M' ·) (φ.den M).fal (φ.den M').fal := by
  induction φ generalizing k with
  | atom p => exact ⟨Team.invariant_flat fun _ _ h ↦ h.val_iff p,
      Team.invariant_flat fun _ _ h ↦ not_congr (h.val_iff p)⟩
  | bot => exact ⟨Team.invariant_singleton_empty, Team.invariant_univ⟩
  | ne => exact ⟨Team.invariant_ne, Team.invariant_singleton_empty⟩
  | neg ψ ih => exact (ih hd).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    exact ⟨(ih₁ hd₁).1.inter (ih₂ hd₂).1, (ih₁ hd₁).2.sups (ih₂ hd₂).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    exact ⟨(ih₁ hd₁).1.sups (ih₂ hd₂).1, (ih₁ hd₁).2.inter (ih₂ hd₂).2⟩
  | gdisj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    exact ⟨(ih₁ hd₁).1.union (ih₂ hd₂).1, (ih₁ hd₁).2.inter (ih₂ hd₂).2⟩
  | empt ψ ih => exact ⟨(ih hd).1.union Team.invariant_singleton_empty, (ih hd).2⟩
  | poss ψ ih =>
    obtain _ | k := k
    · exact absurd hd (Nat.not_succ_le_zero _)
    have ih := ih (Nat.le_of_succ_le_succ hd)
    exact ⟨ih.1.poss fun _ _ h ↦ h.2, ih.2.nec fun _ _ h ↦ h.2⟩

end AloniAnttilaYang2024
