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

## Main results

* `support_empt_iff_gdisj_bot`, `support_poss_gdisj`: equivalences among the new connectives.
* `isLowerSet_support_of_neFree`, `supClosed_support_of_gdFree`,
  `isFlat_support_of_neFree_gdFree`: the closure properties of Fact 2.7.
* `invariant_eval`: bisimulation invariance (Theorem 3.8).
* `bsml_not_complete_for_unionClosed`: BSML does not express every union-closed
  bisimulation-invariant property (Fact 3.19).
* `support_empt_conj_ne`: `⊘` cancels pragmatic enrichment.
* `narrowScopeFC`: narrow-scope free choice, transferred from BSML along `ofBSML`.

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

namespace AloniAnttilaYang2024

variable {W W' : Type*} [DecidableEq W] [DecidableEq W'] {Atom : Type*}

open ModalLogic (KripkeModel WorldBisim)

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

/-- Bilateral evaluation `eval M b φ t` (Definition 2.3) is support when `b` is `true` and
    anti-support when it is `false`. -/
def eval (M : KripkeModel W Atom) : Bool → Formula Atom → Finset W → Prop
  | true, .atom p, t => ∀ w ∈ t, M.val p w
  | false, .atom p, t => ∀ w ∈ t, ¬ M.val p w
  | true, .bot, t => t = ∅
  | false, .bot, _ => True
  | true, .ne, t => t.Nonempty
  | false, .ne, t => t = ∅
  | true, .neg ψ, t => eval M false ψ t
  | false, .neg ψ, t => eval M true ψ t
  | true, .conj ψ₁ ψ₂, t => eval M true ψ₁ t ∧ eval M true ψ₂ t
  | false, .conj ψ₁ ψ₂, t => t ∈ Team.tensor {s | eval M false ψ₁ s} {s | eval M false ψ₂ s}
  | true, .disj ψ₁ ψ₂, t => t ∈ Team.tensor {s | eval M true ψ₁ s} {s | eval M true ψ₂ s}
  | false, .disj ψ₁ ψ₂, t => eval M false ψ₁ t ∧ eval M false ψ₂ t
  | true, .gdisj ψ₁ ψ₂, t => eval M true ψ₁ t ∨ eval M true ψ₂ t
  | false, .gdisj ψ₁ ψ₂, t => eval M false ψ₁ t ∧ eval M false ψ₂ t
  | true, .empt ψ, t => eval M true ψ t ∨ t = ∅
  | false, .empt ψ, t => eval M false ψ t
  | true, .poss ψ, t => ∀ w ∈ t, ∃ s ⊆ M.access w, s.Nonempty ∧ eval M true ψ s
  | false, .poss ψ, t => ∀ w ∈ t, eval M false ψ (M.access w)

abbrev support (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M true φ t

abbrev antiSupport (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M false φ t

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
    support M (.poss (.gdisj φ ψ)) t ↔ support M (.disj (.poss φ) (.poss ψ)) t := by
  classical
  constructor
  · intro h
    refine ⟨t.filter fun w ↦ ∃ s ⊆ M.access w, s.Nonempty ∧ support M φ s, ?_,
      t.filter fun w ↦ ∃ s ⊆ M.access w, s.Nonempty ∧ support M ψ s, ?_, ?_⟩
    · intro w hw; exact (Finset.mem_filter.mp hw).2
    · intro w hw; exact (Finset.mem_filter.mp hw).2
    · ext w
      simp only [Finset.mem_union, Finset.mem_filter]
      refine ⟨fun h' ↦ h'.elim And.left And.left, fun hw ↦ ?_⟩
      obtain ⟨s, hs, hne, hφ | hψ⟩ := h w hw
      exacts [Or.inl ⟨hw, s, hs, hne, hφ⟩, Or.inr ⟨hw, s, hs, hne, hψ⟩]
  · rintro ⟨t₁, h₁, t₂, h₂, h⟩ w hw
    rcases Finset.mem_union.mp (h ▸ hw) with hw | hw
    · obtain ⟨s, hs, hne, hφ⟩ := h₁ w hw; exact ⟨s, hs, hne, Or.inl hφ⟩
    · obtain ⟨s, hs, hne, hψ⟩ := h₂ w hw; exact ⟨s, hs, hne, Or.inr hψ⟩

/-! ### Closure properties (Fact 2.7) -/

private theorem eval_empty_of_neFree (hNE : φ.NEFree) : support M φ ∅ ∧ antiSupport M φ ∅ := by
  induction φ with
  | atom p => exact ⟨fun w hw ↦ absurd hw (by simp), fun w hw ↦ absurd hw (by simp)⟩
  | bot => exact ⟨rfl, trivial⟩
  | ne => exact hNE.elim
  | neg ψ ih => exact (ih hNE).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨⟨(ih₁ hNE.1).1, (ih₂ hNE.2).1⟩, Team.empty_mem_tensor (ih₁ hNE.1).2 (ih₂ hNE.2).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨Team.empty_mem_tensor (ih₁ hNE.1).1 (ih₂ hNE.2).1, ⟨(ih₁ hNE.1).2, (ih₂ hNE.2).2⟩⟩
  | gdisj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨Or.inl (ih₁ hNE.1).1, ⟨(ih₁ hNE.1).2, (ih₂ hNE.2).2⟩⟩
  | empt ψ ih => exact ⟨Or.inr rfl, (ih hNE).2⟩
  | poss ψ _ => exact ⟨fun w hw ↦ absurd hw (by simp), fun w hw ↦ absurd hw (by simp)⟩

theorem support_empty_of_neFree (hNE : φ.NEFree) : support M φ ∅ :=
  (eval_empty_of_neFree M φ hNE).1

private theorem union_inter_of_union_eq {s t t₁ t₂ : Finset W} (h : t₁ ∪ t₂ = s) (hsub : t ⊆ s) :
    (t₁ ∩ t) ∪ (t₂ ∩ t) = t := by
  rw [← Finset.union_inter_distrib_right, h]
  exact Finset.inter_eq_right.mpr hsub

private theorem eval_lower_of_neFree (hNE : φ.NEFree) :
    IsLowerSet {t : Finset W | support M φ t} ∧ IsLowerSet {t : Finset W | antiSupport M φ t} := by
  induction φ with
  | atom p => exact ⟨Team.isLowerSet_flat _, Team.isLowerSet_flat _⟩
  | bot => exact ⟨Team.isLowerSet_singleton_empty, isLowerSet_univ⟩
  | ne => exact hNE.elim
  | neg ψ ih => exact (ih hNE).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨(ih₁ hNE.1).1.inter (ih₂ hNE.2).1, (ih₁ hNE.1).2.tensor (ih₂ hNE.2).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨(ih₁ hNE.1).1.tensor (ih₂ hNE.2).1, (ih₁ hNE.1).2.inter (ih₂ hNE.2).2⟩
  | gdisj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨(ih₁ hNE.1).1.union (ih₂ hNE.2).1, (ih₁ hNE.1).2.inter (ih₂ hNE.2).2⟩
  | empt ψ ih => exact ⟨(ih hNE).1.union Team.isLowerSet_singleton_empty, (ih hNE).2⟩
  | poss ψ _ => exact ⟨Team.isLowerSet_flat _, Team.isLowerSet_flat _⟩

/-- NE-free formulas are downward closed. -/
theorem isLowerSet_support_of_neFree (hNE : φ.NEFree) :
    IsLowerSet { t : Finset W | support M φ t } :=
  (eval_lower_of_neFree M φ hNE).1

private theorem eval_supClosed_of_gdFree (hGD : φ.GDFree) :
    SupClosed {t : Finset W | support M φ t} ∧ SupClosed {t : Finset W | antiSupport M φ t} := by
  induction φ with
  | atom p => exact ⟨Team.supClosed_flat _, Team.supClosed_flat _⟩
  | bot => exact ⟨Team.supClosed_singleton_empty, supClosed_univ⟩
  | ne => exact ⟨Team.supClosed_ne, Team.supClosed_singleton_empty⟩
  | neg ψ ih => exact (ih hGD).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨(ih₁ hGD.1).1.inter (ih₂ hGD.2).1, (ih₁ hGD.1).2.tensor (ih₂ hGD.2).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact ⟨(ih₁ hGD.1).1.tensor (ih₂ hGD.2).1, (ih₁ hGD.1).2.inter (ih₂ hGD.2).2⟩
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
  (eval_supClosed_of_gdFree M φ hGD).1

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

theorem eval_ofBSML (b : Bool) (φ : BSML.Formula Atom) :
    eval M b (ofBSML φ) t ↔ BSML.eval M b φ t := by
  induction φ generalizing b t with
  | atom p => cases b <;> rfl
  | ne => cases b <;> rfl
  | neg ψ ih => cases b <;> simp only [ofBSML, eval, BSML.eval, ih]
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp only [ofBSML, eval, BSML.eval]
      constructor <;> rintro ⟨t₁, h₁, t₂, h₂, hsplit⟩
      exacts [⟨t₁, (ih₁ t₁ false).mp h₁, t₂, (ih₂ t₂ false).mp h₂, hsplit⟩,
        ⟨t₁, (ih₁ t₁ false).mpr h₁, t₂, (ih₂ t₂ false).mpr h₂, hsplit⟩]
    · simp only [ofBSML, eval, BSML.eval, ih₁, ih₂]
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp only [ofBSML, eval, BSML.eval, ih₁, ih₂]
    · simp only [ofBSML, eval, BSML.eval]
      constructor <;> rintro ⟨t₁, h₁, t₂, h₂, hsplit⟩
      exacts [⟨t₁, (ih₁ t₁ true).mp h₁, t₂, (ih₂ t₂ true).mp h₂, hsplit⟩,
        ⟨t₁, (ih₁ t₁ true).mpr h₁, t₂, (ih₂ t₂ true).mpr h₂, hsplit⟩]
  | poss ψ ih =>
    cases b
    · simp only [ofBSML, eval, BSML.eval, Team.mem_nec, Set.mem_ofPred_eq, ih]
    · simp only [ofBSML, eval, BSML.eval, Team.mem_poss, Set.mem_ofPred_eq]
      constructor <;> intro h w hw <;> obtain ⟨s, hsub, hne, hsupp⟩ := h w hw
      exacts [⟨s, hsub, hne, (ih s true).mp hsupp⟩, ⟨s, hsub, hne, (ih s true).mpr hsupp⟩]

/-- Narrow-scope free choice, `[◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β`, transported from
    [aloni-2022] along the embedding. -/
theorem narrowScopeFC {α β : BSML.Formula Atom} (hα : α.NEFree) (hβ : β.NEFree)
    (h : support M (ofBSML (BSML.enrich (.poss (.disj α β)))) t) :
    support M (ofBSML (.conj (.poss α) (.poss β))) t :=
  (eval_ofBSML M t true _).mpr (Aloni2022.narrowScopeFC hα hβ ((eval_ofBSML M t true _).mp h))

/-! ### Bisimulation invariance (Theorem 3.8) -/

/-- The modal depth of a formula is the greatest number of nested `◇`s in it. -/
def Formula.modalDepth : Formula Atom → ℕ
  | .atom _ | .bot | .ne => 0
  | .neg ψ | .empt ψ => ψ.modalDepth
  | .conj ψ₁ ψ₂ | .disj ψ₁ ψ₂ | .gdisj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .poss ψ => ψ.modalDepth + 1

/-- Teams that are `k`-bisimilar agree on every formula of modal depth at most `k`, in both
    polarities (Theorem 3.8). -/
theorem invariant_eval {M : KripkeModel W Atom} {M' : KripkeModel W' Atom} {k : ℕ}
    (φ : Formula Atom) (hd : φ.modalDepth ≤ k) (b : Bool) :
    Team.Invariant (WorldBisim k M · M' ·) {t | eval M b φ t} {t | eval M' b φ t} := by
  induction φ generalizing k b with
  | atom p =>
    cases b
    · exact Team.invariant_flat fun _ _ h ↦ not_congr (h.val_iff p)
    · exact Team.invariant_flat fun _ _ h ↦ h.val_iff p
  | bot => cases b; exacts [Team.invariant_univ, Team.invariant_singleton_empty]
  | ne => cases b; exacts [Team.invariant_singleton_empty, Team.invariant_ne]
  | neg ψ ih => cases b <;> exact ih hd _
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    cases b; exacts [(ih₁ hd₁ _).tensor (ih₂ hd₂ _), (ih₁ hd₁ _).inter (ih₂ hd₂ _)]
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    cases b; exacts [(ih₁ hd₁ _).inter (ih₂ hd₂ _), (ih₁ hd₁ _).tensor (ih₂ hd₂ _)]
  | gdisj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    cases b; exacts [(ih₁ hd₁ _).inter (ih₂ hd₂ _), (ih₁ hd₁ _).union (ih₂ hd₂ _)]
  | empt ψ ih => cases b; exacts [ih hd _, (ih hd _).union Team.invariant_singleton_empty]
  | poss ψ ih =>
    obtain _ | k := k
    · exact absurd hd (Nat.not_succ_le_zero _)
    have ih := ih (Nat.le_of_succ_le_succ hd)
    cases b; exacts [(ih _).nec fun _ _ h ↦ h.2, (ih _).poss fun _ _ h ↦ h.2]

end AloniAnttilaYang2024
