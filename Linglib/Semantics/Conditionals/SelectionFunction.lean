module

public import Linglib.Semantics.Conditionals.Basic
public import Mathlib.Order.Extension.Linear
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Selection functions

This file defines selection functions and the selection conditional. A selection function takes
a world and a possible proposition to a world at which the proposition holds, the world itself
when it holds there: intuitively the closest world at which the proposition holds. The selection
conditional *if p, q* is true when `q` holds at the world selected for `p`, and vacuously true
when `p` is impossible. A selection establishes an ordering of the worlds it selects, its
priority, and a selection function satisfying Stalnaker's condition (4) is the conditional of the
closest worlds under its priority, a well-ordering with each world first in its own. A similarity
ordering with ties corresponds to the class of selection functions its completions determine, and
for a single conditional the supervaluation over them is the conditional of the closest worlds.

## Main definitions

* `SelectionFunction`: a selection function.
* `selectionConditional`: the selection conditional.
* `SelectionFunction.IsCSO`: Stalnaker's condition (4), that antecedents each true at the world
  selected for the other select the same world.
* `Conditional.Prior`: the priority a selection establishes among the worlds it selects.
* `SelectionFunction.restrict`: a selection function restricted to a set of worlds.
* `SelectionFunction.along`, `SelectionFunction.modal`: selection along an accessibility relation
  and the selectional modal it defines.
* `Completion`: a linear extension of a family of preorders at each center.
* `SelectionFunction.Compatible`: selection by a completion of a family of preorders.

## Main results

* `SelectionFunction.exists_sel_eq`: outside a proposition any of its worlds can be selected.
* `SelectionFunction.modal_eq_core`, `SelectionFunction.modal_inter_refl`,
  `SelectionFunction.modal_eq_id`: the selectional modal along a relation is necessity along a
  function, idle where the relation is reflexive and the identity along a reflexive relation.
* `Conditional.Prior.antisymm`, `Conditional.Prior.trans`, `Conditional.Prior.total`: under
  condition (4), priority is a total ordering of the selected worlds.
* `SelectionFunction.IsCSO.selectionConditional_eq_closestImp`: under condition (4), the selection
  conditional is the conditional of the closest worlds under priority, which is centered and
  well-founded (`SelectionFunction.IsCSO.isCentered`, `SelectionFunction.IsCSO.wellFounded`).
* `SelectionFunction.Compatible.isCSO`: selection by a completion satisfies condition (4).
* `mem_closestImp_iff_forall_compatible`: the conditional of the closest worlds is the
  supervaluation over completions.

## References

* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
* [R. C. Stalnaker, *Indicative conditionals* (1975)][stalnaker-1975]
* [R. C. Stalnaker, *A Defense of Conditional Excluded Middle* (1981)][stalnaker-1981]
-/

@[expose] public section

namespace Conditional

/-- A selection function ([stalnaker-1968]) takes a world and a proposition to a selected
world, one at which the proposition holds when it is possible, and the world itself when the
proposition holds there. -/
structure SelectionFunction (W : Type*) where
  /-- The selection map. -/
  sel : W → Set W → W
  /-- The world selected for a possible proposition is one at which it holds. -/
  inclusion : ∀ (w : W) (A : Set W), A.Nonempty → sel w A ∈ A
  /-- A world at which the proposition holds selects itself. -/
  centering : ∀ (w : W) (A : Set W), w ∈ A → sel w A = w

/-- Inclusion and centering are the only constraints on a selection function, so at a world
outside a proposition any world of the proposition is selected by some selection function. -/
theorem SelectionFunction.exists_sel_eq {W : Type*} {w v : W} {A : Set W} (hv : v ∈ A)
    (hw : w ∉ A) : ∃ s : SelectionFunction W, s.sel w A = v := by
  classical
  refine ⟨⟨fun w' A' ↦ if w' ∈ A' then w' else if w' = w ∧ A' = A then v
      else if h : A'.Nonempty then h.some else w', fun w' A' hA' ↦ ?_, fun _ _ h ↦ ite_eq_left h⟩,
    by simp [hw]⟩
  split_ifs with h₁ h₂
  · exact h₁
  · exact h₂.2 ▸ hv
  · exact Set.Nonempty.some_mem _

section SelectionConditional

variable {W : Type*} (s : SelectionFunction W) {p q r : Set W} {w : W}

/-- The domain of the selection conditional, the world selected for `p` when `p` is possible and
nothing otherwise. For an impossible antecedent [stalnaker-1968] selects an absurd world, at which
every sentence is true, so that the conditional is vacuously true; the empty domain plays its
part. Condition (1) forces the absurd world when no world verifies the antecedent, and condition
(2) permits it only when no world possible relative to the base world does. With every world
possible relative to every other, as here, the two coincide. -/
def SelectionFunction.domain (w : W) (p : Set W) : Set W := {s.sel w p} ∩ p

theorem SelectionFunction.domain_eq_singleton (hp : p.Nonempty) :
    s.domain w p = {s.sel w p} :=
  Set.inter_eq_left.2 (Set.singleton_subset_iff.2 (s.inclusion w p hp))

theorem SelectionFunction.subsingleton_domain : (s.domain w p).Subsingleton :=
  Set.subsingleton_singleton.anti Set.inter_subset_left

theorem SelectionFunction.domain_of_mem (hw : w ∈ p) : s.domain w p = {w} := by
  rw [SelectionFunction.domain, s.centering w p hw,
    Set.inter_eq_left.2 (Set.singleton_subset_iff.2 hw)]

/-- The selection conditional of [stalnaker-1968], true at `w` when `q` holds at the world `s`
selects for `p` and vacuously true when `p` is impossible. The indicative reading of
[stalnaker-1975] and the counterfactual reading of [stalnaker-1981] share this clause and differ
in which selection functions are admissible. -/
def selectionConditional (p q : Set W) : Set W := ofDomain s.domain p q

theorem mem_selectionConditional :
    w ∈ selectionConditional s p q ↔ (p.Nonempty → s.sel w p ∈ q) := by
  rcases p.eq_empty_or_nonempty with rfl | hp
  · simp [selectionConditional, SelectionFunction.domain]
  · simp [selectionConditional, s.domain_eq_singleton hp, hp]

theorem mem_selectionConditional_of_nonempty (hp : p.Nonempty) :
    w ∈ selectionConditional s p q ↔ s.sel w p ∈ q := by
  simp [mem_selectionConditional, hp]

theorem mem_selectionConditional_of_mem (hw : w ∈ p) :
    w ∈ selectionConditional s p q ↔ w ∈ q := by
  rw [mem_selectionConditional_of_nonempty s ⟨w, hw⟩, s.centering w p hw]

theorem selectionConditional_inter_self : selectionConditional s p q ∩ p = q ∩ p :=
  Set.ext fun _ ↦ and_congr_left (mem_selectionConditional_of_mem s)

theorem selectionConditional_cem :
    w ∈ selectionConditional s p q ∨ w ∈ selectionConditional s p qᶜ :=
  mem_ofDomain_or_compl s.subsingleton_domain

theorem selectionConditional_or (h : w ∈ selectionConditional s p (q ∪ r)) :
    w ∈ selectionConditional s p q ∨ w ∈ selectionConditional s p r :=
  mem_ofDomain_or s.subsingleton_domain h

theorem selectionConditional_subset_materialImp : selectionConditional s p q ⊆ materialImp p q :=
  fun _ h hp ↦ (mem_selectionConditional_of_mem s hp).1 h

end SelectionConditional

/-! ### Selection along a relation

A selection function selects along an accessibility relation by selecting from the successors of
a world, and the selectional modal along the relation is necessity along the graph of this
selection: the preimage of a function, so a complete lattice homomorphism. Selection is idle at
the worlds that access themselves. -/

section Along

open scoped SetRel

variable {W : Type*} (s : SelectionFunction W) (R : SetRel W W) {A : Set W} {w : W}

namespace SelectionFunction

/-- The world selected along `R` at `w`, from the `R`-successors of `w`. -/
def along (w : W) : W := s.sel w {v | w ~[R] v}

/-- The selectional modal along `R`, sending `A` to the worlds whose selection along `R` is an
`A`-world. -/
def modal : CompleteLatticeHom (Set W) (Set W) := .setPreimage (s.along R)

variable {s R}

@[simp] theorem mem_modal : w ∈ s.modal R A ↔ s.along R w ∈ A := Iff.rfl

/-- The selectional modal is necessity along the graph of the selection. -/
theorem modal_eq_core (A : Set W) : s.modal R A = (Function.graph (s.along R)).core A :=
  Set.preimage_eq_core _ A

theorem along_eq_self (h : w ~[R] w) : s.along R w = w := s.centering w _ h

theorem rel_along (h : ∃ v, w ~[R] v) : w ~[R] s.along R w := s.inclusion w {v | w ~[R] v} h

/-- At the worlds that access themselves, the selectional modal of `A` holds where `A` does. -/
theorem modal_inter_refl (A : Set W) : s.modal R A ∩ {w | w ~[R] w} = A ∩ {w | w ~[R] w} :=
  Set.ext fun w ↦ and_congr_left fun h ↦ by
    change s.along R w ∈ A ↔ w ∈ A
    rw [along_eq_self (R := R) h]

/-- Along a reflexive relation selection is idle, so the selectional modal is the identity. -/
theorem modal_eq_id [R.IsRefl] : s.modal R = CompleteLatticeHom.id (Set W) := by
  ext A w
  change s.along R w ∈ A ↔ w ∈ A
  rw [along_eq_self R.rfl]

end SelectionFunction

variable {s}

theorem selectionConditional_eq_modal {p : Set W} (hp : p.Nonempty) (q : Set W) :
    selectionConditional s p q = s.modal (SetRel.ofSuccessors fun _ ↦ p) q :=
  Set.ext fun _ ↦ mem_selectionConditional_of_nonempty s hp

end Along

/-! ### Condition (4) and restriction -/

section CSO

variable {W : Type*} {s : SelectionFunction W} {w : W} {p q : Set W}

/-- A selection function satisfies [stalnaker-1968]'s condition (4) when two possible antecedents
each true at the world selected for the other select the same world. -/
def SelectionFunction.IsCSO (s : SelectionFunction W) : Prop :=
  ∀ w (p p' : Set W), p.Nonempty → p'.Nonempty → s.sel w p' ∈ p → s.sel w p ∈ p' →
    s.sel w p = s.sel w p'

/-- Under condition (4), the world selected for `p` lies in `q` iff it is the world selected for
`p ∩ q`. -/
theorem SelectionFunction.IsCSO.sel_mem_iff (hs : s.IsCSO) (h : (p ∩ q).Nonempty) :
    s.sel w p ∈ q ↔ s.sel w p = s.sel w (p ∩ q) :=
  ⟨fun hq ↦ hs w p (p ∩ q) (h.mono Set.inter_subset_left) h (s.inclusion w _ h).1
      ⟨s.inclusion w p (h.mono Set.inter_subset_left), hq⟩,
    fun he ↦ he ▸ (s.inclusion w _ h).2⟩

open Classical in
/-- The restriction of a selection function to a set `C`, which at a world of `C` selects among
the antecedent-worlds in `C` when there are any and otherwise selects as before. -/
noncomputable def SelectionFunction.restrict (s : SelectionFunction W) (C : Set W) :
    SelectionFunction W where
  sel w A := if w ∈ C ∧ (A ∩ C).Nonempty then s.sel w (A ∩ C) else s.sel w A
  inclusion w A hA := by
    split_ifs with h
    · exact (s.inclusion w (A ∩ C) h.2).1
    · exact s.inclusion w A hA
  centering w A hw := by
    split_ifs with h
    · exact s.centering w (A ∩ C) ⟨hw, h.1⟩
    · exact s.centering w A hw

theorem SelectionFunction.restrict_sel_of_mem (s : SelectionFunction W) (C : Set W) {A : Set W}
    (hw : w ∈ C) (hA : (A ∩ C).Nonempty) : (s.restrict C).sel w A = s.sel w (A ∩ C) := by
  simp [SelectionFunction.restrict, hw, hA]

theorem SelectionFunction.restrict_sel_of_not_nonempty (s : SelectionFunction W) (C : Set W)
    {A : Set W} (hA : ¬ (A ∩ C).Nonempty) : (s.restrict C).sel w A = s.sel w A := by
  simp [SelectionFunction.restrict, hA]

end CSO

/-! ### Priority

A selection establishes an ordering of the worlds it selects ([stalnaker-1968] fn. 8): selecting
`v` for an antecedent makes `v` prior to every world of the antecedent. When each domain of a
conditional is a set of antecedent-worlds with at most one member, condition (4) says that
priority is antisymmetric, and priority is then a total ordering of the selected worlds, each
domain holding the least selected world of its antecedent. A selection function satisfying
condition (4) is therefore the conditional of the closest worlds under its priority, the converse
of `SelectionFunction.Compatible.isCSO`. -/

section Priority

variable {I W : Type*} {D : I → Set W → Set W} {i : I} {A : Set W} {v u x : W}

/-- `v` is prior to `u` at `i` when some antecedent true at `u` has the domain `{v}`. -/
def Prior (D : I → Set W → Set W) (i : I) (v u : W) : Prop := ∃ A, D i A = {v} ∧ u ∈ A

theorem Prior.of_mem (hD : (D i A).Subsingleton) (hv : v ∈ D i A) (hu : u ∈ A) :
    Prior D i v u :=
  ⟨A, hD.eq_singleton_of_mem hv, hu⟩

theorem Prior.self (hsub : ∀ A, D i A ⊆ A) (h : Prior D i v u) : Prior D i v v :=
  let ⟨A, hA, _⟩ := h
  ⟨A, hA, hsub A (hA ▸ rfl)⟩

section CSO

variable (hcso : ∀ A B, D i B ⊆ A → D i A ⊆ B → D i A = D i B)
include hcso

theorem Prior.antisymm (h : Prior D i v u) (h' : Prior D i u v) : v = u := by
  obtain ⟨A, hA, huA⟩ := h
  obtain ⟨B, hB, hvB⟩ := h'
  have := hcso A B (by simpa [hB] using huA) (by simpa [hA] using hvB)
  rwa [hA, hB, Set.singleton_eq_singleton_iff] at this

theorem Prior.nonempty (h : Prior D i v u) (hv : v ∈ A) : (D i A).Nonempty := by
  obtain ⟨B, hB, -⟩ := h
  refine Set.nonempty_iff_ne_empty.2 fun hA ↦ ?_
  have := hcso A B (by simpa [hB] using hv) (by simp [hA])
  simp [hA, hB] at this

variable (hss : ∀ A, (D i A).Subsingleton) (hsub : ∀ A, D i A ⊆ A)
include hss hsub

theorem Prior.trans (h : Prior D i v u) (h' : Prior D i u x) : Prior D i v x := by
  obtain ⟨y, hy⟩ := h.nonempty hcso (A := {v, u, x}) (by simp)
  have hle : ∀ z ∈ ({v, u, x} : Set W), Prior D i y z := fun _ hz ↦ .of_mem (hss _) hy hz
  rcases hsub _ hy with rfl | rfl | rfl
  · exact hle x (by simp)
  · exact (Prior.antisymm hcso h (hle v (by simp))) ▸ h'
  · exact (Prior.antisymm hcso h' (hle u (by simp))) ▸ h

theorem Prior.total (hv : Prior D i v v) : Prior D i v u ∨ Prior D i u v := by
  obtain ⟨y, hy⟩ := hv.nonempty hcso (A := {v, u}) (by simp)
  rcases hsub _ hy with rfl | rfl
  exacts [.inl (.of_mem (hss _) hy (by simp)), .inr (.of_mem (hss _) hy (by simp))]

end CSO

namespace SelectionFunction

variable {s : SelectionFunction W} {w : W} {B : Set W}

theorem domain_singleton (s : SelectionFunction W) (w v : W) : s.domain w {v} = {v} := by
  rw [s.domain_eq_singleton (Set.singleton_nonempty v),
    s.inclusion w {v} (Set.singleton_nonempty v)]

theorem IsCSO.domain_eq (hs : s.IsCSO) (h₁ : s.domain w B ⊆ A) (h₂ : s.domain w A ⊆ B) :
    s.domain w A = s.domain w B := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · rw [Set.subset_empty_iff.1 h₁]; simp [domain]
  rcases B.eq_empty_or_nonempty with rfl | hB
  · rw [Set.subset_empty_iff.1 h₂]; simp [domain]
  rw [s.domain_eq_singleton hA, s.domain_eq_singleton hB] at *
  rw [hs w A B hA hB (h₁ rfl) (h₂ rfl)]

/-- Under condition (4), priority is a linear order at each world. -/
noncomputable abbrev IsCSO.linearOrder (hs : s.IsCSO) (w : W) : LinearOrder W where
  le := Prior s.domain w
  le_refl v := ⟨{v}, s.domain_singleton w v, rfl⟩
  le_trans _ _ _ := Prior.trans (fun _ _ ↦ hs.domain_eq) (fun _ ↦ s.subsingleton_domain)
    fun _ ↦ Set.inter_subset_right
  le_antisymm _ _ := Prior.antisymm fun _ _ ↦ hs.domain_eq
  le_total v _ := Prior.total (fun _ _ ↦ hs.domain_eq) (fun _ ↦ s.subsingleton_domain)
    (fun _ ↦ Set.inter_subset_right) ⟨{v}, s.domain_singleton w v, rfl⟩
  toDecidableLE := Classical.decRel _

theorem IsCSO.minimals_eq_domain (hs : s.IsCSO) (p : Set W) :
    (hs.linearOrder w).toPreorder.minimals p = s.domain w p := by
  ext v
  refine ⟨fun ⟨hv, hmin⟩ ↦ ?_,
    fun hv ↦ ⟨hv.2, fun _ hu _ ↦ Prior.of_mem s.subsingleton_domain hv hu⟩⟩
  have hD := s.domain_eq_singleton (w := w) ⟨v, hv⟩
  have hprior : Prior s.domain w (s.sel w p) v := ⟨p, hD, hv⟩
  rw [hD]
  exact Prior.antisymm (fun _ _ ↦ hs.domain_eq) (hmin (s.inclusion w p ⟨v, hv⟩) hprior) hprior

theorem IsCSO.isCentered (hs : s.IsCSO) : IsCentered fun w ↦ (hs.linearOrder w).toPreorder :=
  fun w w' hne ↦ @lt_of_le_of_ne W (hs.linearOrder w).toPartialOrder _ _
    ⟨{w, w'}, s.domain_of_mem (by simp), by simp⟩ hne

theorem IsCSO.wellFounded (hs : s.IsCSO) (w : W) :
    WellFounded (hs.linearOrder w).toPreorder.lt :=
  WellFounded.wellFounded_iff_has_min.2 fun p hp ↦
    ⟨s.sel w p, s.inclusion w p hp, fun _ hu hlt ↦ hlt.2 ⟨p, s.domain_eq_singleton hp, hu⟩⟩

/-- Under condition (4), the selection conditional is the conditional of the closest worlds
under priority. -/
theorem IsCSO.selectionConditional_eq_closestImp (hs : s.IsCSO) (p q : Set W) :
    selectionConditional s p q = closestImp (fun w ↦ (hs.linearOrder w).toPreorder) p q :=
  Set.ext fun _ ↦ by rw [mem_closestImp, hs.minimals_eq_domain]; rfl

end SelectionFunction

end Priority

/-! ### Selection functions compatible with a similarity ordering

[stalnaker-1981] reads a similarity ordering with ties and incomparabilities as the class of its
completions, the well orderings of the worlds that extend it, and a conditional as true when it
is true on every completion. -/

section Compatible

variable {W : Type*} {ord : W → Preorder W} {s : SelectionFunction W} {p q : Set W} {w v : W}

/-- A completion of a family of preorders assigns to each center a linear order of the worlds
extending its strict order. -/
structure Completion (ord : W → Preorder W) where
  /-- The completed order at each center. -/
  order : W → LinearOrder W
  le_of_lt : ∀ w x y, (ord w).lt x y → (order w).le x y

/-- A selection function is selected by a completion when it selects, for each center, the least
possible antecedent-world in the completion's order. -/
def SelectionFunction.SelectedBy (s : SelectionFunction W) (c : Completion ord) : Prop :=
  ∀ w p, p.Nonempty → ∀ u ∈ p, (c.order w).le (s.sel w p) u

/-- A selection function is compatible with a family of preorders when some completion of the
family selects it. -/
def SelectionFunction.Compatible (s : SelectionFunction W) (ord : W → Preorder W) : Prop :=
  ∃ c : Completion ord, s.SelectedBy c

/-- A selection function selected by a completion satisfies [stalnaker-1968]'s condition (4). -/
theorem SelectionFunction.Compatible.isCSO (hs : s.Compatible ord) : s.IsCSO := by
  intro w p p' hp hp' h₁ h₂
  obtain ⟨c, hc⟩ := hs
  exact (c.order w).le_antisymm _ _ (hc w p hp _ h₁) (hc w p' hp' _ h₂)

theorem SelectionFunction.Compatible.sel_mem_minimals (hs : s.Compatible ord) (hp : p.Nonempty) :
    s.sel w p ∈ (ord w).minimals p := by
  obtain ⟨c, hc⟩ := hs
  refine ⟨s.inclusion w p hp, fun u hu hus ↦ ?_⟩
  by_contra hn
  have hlt : (ord w).lt u (s.sel w p) := ((ord w).lt_iff_le_not_ge _ _).2 ⟨hus, hn⟩
  exact hn (((c.order w).le_antisymm _ _ (c.le_of_lt w u _ hlt) (hc w p hp u hu)) ▸
    (ord w).le_refl _)

theorem SelectionFunction.Compatible.domain_subset (hs : s.Compatible ord) :
    s.domain w p ⊆ (ord w).minimals p := by
  rintro v ⟨rfl, hv⟩
  exact hs.sel_mem_minimals ⟨_, hv⟩

theorem SelectionFunction.Compatible.closestImp_subset (hs : s.Compatible ord) :
    closestImp ord p q ⊆ selectionConditional s p q :=
  fun _ h ↦ hs.domain_subset.trans h

theorem exists_completion (hv : v ∈ (ord w).minimals p) :
    ∃ c : Completion ord, ∀ u ∈ p, (c.order w).le v u := by
  classical
  let key : W → W → ℕ := fun w' u ↦
    if w' = w then if (ord w).lt u v then 0 else if u = v then 1 else 2 else 0
  have hkey : ∀ w' x y, (ord w').lt x y → key w' x ≤ key w' y := by
    intro w' x y hxy
    by_cases hw : w' = w
    · subst hw
      let := ord w'
      have h₀ : y < v → x < v := hxy.trans
      have h₁ : y = v → x < v := fun h ↦ h ▸ hxy
      simp only [key, ite_true]
      split_ifs <;> first | omega | (exfalso; tauto)
    · simp [key, hw]
  let order : W → LinearOrder W := fun w' ↦
    letI := ord w'
    letI : PartialOrder W := partialOrderOfSO (· < ·)
    LinearOrder.lift' (toLinearExtension ∘ toLex ∘ fun x ↦ (key w' x, x))
      (Function.Injective.comp (fun _ _ h ↦ h)
        (Function.Injective.comp toLex.injective fun _ _ h ↦ (Prod.mk.inj h).2))
  refine ⟨⟨order, fun w' x y hxy ↦ ?_⟩, fun u hu ↦ ?_⟩
  · let P : PartialOrder W := (letI := ord w'; partialOrderOfSO (· < ·))
    refine toLinearExtension.monotone ?_
    rcases (hkey w' x y hxy).lt_or_eq with hk | hk
    · exact Prod.Lex.left _ _ hk
    · show toLex (key w' x, x) ≤ toLex (key w' y, y)
      rw [hk]
      exact Prod.Lex.right _ (Or.inr hxy)
  · let P : PartialOrder W := (letI := ord w; partialOrderOfSO (· < ·))
    refine toLinearExtension.monotone ?_
    rcases eq_or_ne u v with rfl | huv
    · exact Prod.Lex.right _ (Or.inl rfl)
    · have h0 : ¬ (ord w).lt u v := fun h ↦
        (((ord w).lt_iff_le_not_ge _ _).1 h).2 (hv.2 hu (((ord w).lt_iff_le_not_ge _ _).1 h).1)
      exact Prod.Lex.left _ _ (by simp [key, h0, huv])

theorem SelectionFunction.exists_compatible [Finite W] (hc : IsCentered ord)
    (hv : v ∈ (ord w).minimals p) :
    ∃ s : SelectionFunction W, s.Compatible ord ∧ s.sel w p = v := by
  classical
  obtain ⟨c, hcv⟩ := exists_completion hv
  have hleast : ∀ w' (p' : Set W), p'.Nonempty → ∃ m ∈ p', ∀ u ∈ p', (c.order w').le m u := by
    intro w' p' hp'
    let := c.order w'
    obtain ⟨m, hm, hmin⟩ := (wellFounded_lt (α := W)).has_min p' hp'
    exact ⟨m, hm, fun u hu ↦ not_lt.1 (hmin u hu)⟩
  choose! m hm hmle using hleast
  refine ⟨⟨fun w' p' ↦ if h : p'.Nonempty then m w' p' else w', fun w' p' hp' ↦ ?_,
    fun w' p' hw' ↦ ?_⟩, ⟨c, fun w' p' hp' u hu ↦ ?_⟩, ?_⟩
  · simpa [hp'] using hm w' p' hp'
  · have hne : p'.Nonempty := ⟨w', hw'⟩
    show (if h : p'.Nonempty then m w' p' else w') = w'
    simp only [hne, ↓reduceDIte]
    rcases eq_or_ne (m w' p') w' with h | h
    · exact h
    · exact (c.order w').le_antisymm _ _ (hmle w' p' ⟨w', hw'⟩ w' hw')
        (c.le_of_lt w' w' _ (hc w' _ h.symm))
  · simpa [hp'] using hmle w' p' hp' u hu
  · have hp : p.Nonempty := ⟨v, hv.1⟩
    show (if h : p.Nonempty then m w p else w) = v
    simp only [hp, ↓reduceDIte]
    exact (c.order w).le_antisymm _ _ (hmle w p hp v hv.1) (hcv _ (hm w p hp))

/-- On a finite, strongly centered family of preorders, the conditional of the closest worlds
holds iff the selection conditional is true on every completion, [stalnaker-1981]'s
supervaluation for a single conditional. -/
theorem mem_closestImp_iff_forall_compatible [Finite W] (hc : IsCentered ord) :
    w ∈ closestImp ord p q ↔
      ∀ s : SelectionFunction W, s.Compatible ord → w ∈ selectionConditional s p q := by
  refine ⟨fun h s hs ↦ hs.closestImp_subset h, fun h v hv ↦ ?_⟩
  obtain ⟨s, hs, rfl⟩ := SelectionFunction.exists_compatible hc hv
  exact (mem_selectionConditional_of_nonempty s ⟨_, hv.1⟩).1 (h s hs)

end Compatible

end Conditional
