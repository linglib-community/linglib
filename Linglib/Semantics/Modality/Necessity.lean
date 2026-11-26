module

public import Linglib.Semantics.Modality.Background
public import Linglib.Semantics.Modality.Basic
public import Linglib.Core.Order.Filter.AtBotOn
public import Linglib.Logic.Nonmonotonic.PremiseOrdering
public import Linglib.Semantics.Modality.ComparativePossibility
public import Linglib.Logic.Modal.Definability

/-!
# Necessity and possibility relative to conversational backgrounds

A modal base `f` and an ordering source `g` determine, at each world `w`, the propositions that are
necessities there. Following [kratzer-1991], `p` is a necessity when every accessible world `u` has
an accessible world `v` at least as good, `v ≤[g w] u`, such that `p` is true at every accessible
world at least as good as `v`. The necessities at a world form a filter, `f.necessity g w`, and a
proposition is a possibility when its negation is not a necessity.

The file then specializes. Under the Limit Assumption the necessities are the propositions true at
every best world. Over the empty ordering source they are the propositions true at every accessible
world, the simple necessities of [kratzer-1977], and simple necessity is `□` along the accessibility
relation of the modal base. When some accessible world verifies every premise of the ordering
source, the necessities are the simple necessities of the two backgrounds taken together.

## Main definitions

* `Modality.Background.necessity`: the filter of necessities at a world.
* `Modality.Background.possibility`: the dual of necessity.
* `Modality.Background.goodPossibility`: truth at every accessible world at least as good as some
  accessible world.
* `Modality.LimitAssumption`: every accessible world has a best world at least as good.
* `Modality.Background.simpleNecessity`: the necessities over the empty ordering source.
* `Modality.Background.accessible`: the accessibility relation of a modal base.

## Main results

* `Modality.Background.necessity_neBot_iff`: necessity is consistent exactly over a consistent
  modal base, whatever the ordering source.
* `Modality.Background.necessity_eq_principal`: under the Limit Assumption, necessity is truth at
  the best worlds.
* `Modality.Background.pure_le_necessity_iff`: under the Limit Assumption, what is necessary at a
  world is true there exactly when that world is one of its best worlds.
* `Modality.Background.necessity_bot`: over the empty ordering source, necessity is simple
  necessity.
* `Modality.Background.box_accessible_iff`: simple necessity is `□` along the accessibility
  relation.
* `Modality.Background.necessity_eq_simpleNecessity_sup`: over an ordering source consistent with
  the modal base, necessity is simple necessity over the two together.

## Implementation notes

The necessities at a world are a `Filter W` whose membership lemma, `Background.mem_necessity`, is
the definition of [kratzer-1991] and holds by `rfl`. Closure of necessity under consequence and
conjunction is then `Filter.mem_of_superset` and `Filter.inter_mem`, the axioms **T** and **D** are
`pure w ≤ f.necessity g w` and `(f.necessity g w).NeBot`, as for neighbourhoods in topology, and a
prejacent stated as a predicate is `∀ᶠ v in f.necessity g w, p v`. Good possibility need not be
closed under conjunction, so it is a proposition and not a filter.

[kratzer-1981] calls necessity and possibility human necessity and human possibility. The weak
necessity and slight possibility of [kratzer-1991] are not formalized here.

## References

* [kratzer-1977]
* [kratzer-1981]
* [kratzer-1991]
* [kratzer-2012]
* [portner-rubinstein-2020]
-/

@[expose] public section

open scoped PremiseOrdering

namespace Modality

open Filter ModalLogic SetRel

variable {W : Type*}

/-! ### The accessibility relation of a modal base

The worlds accessible from `w` under a modal base `f` are those of `⋂f(w)`, which makes `f` present
an accessibility relation, and every relation is presented by a modal base. -/

/-- Under a modal base, `w'` is accessible from `w` when it satisfies every premise of `f w`,
Kratzer's `w' ∈ ⋂f(w)`. -/
def Background.accessible (f : Background W) : SetRel W W :=
  .cgraph f.accessibleWorlds

@[simp] theorem Background.mem_accessible {f : Background W} {w w' : W} :
    w ~[f.accessible] w' ↔ w' ∈ f.accessibleWorlds w := .rfl

/-- The background of a relation, whose one premise at `w` is to be an `R`-successor of `w`. -/
def Background.ofRel (R : SetRel W W) : Background W := fun w ↦ {{v | w ~[R] v}}

@[simp] theorem Background.accessibleWorlds_ofRel (R : SetRel W W) (w : W) :
    (Background.ofRel R).accessibleWorlds w = {v | w ~[R] v} :=
  Set.sInter_singleton _

@[simp] theorem Background.accessible_ofRel (R : SetRel W W) :
    (Background.ofRel R).accessible = R := by
  ext ⟨w, v⟩
  exact (Set.ext_iff.1 (Background.accessibleWorlds_ofRel R w) v)

theorem accessible_bot (w w' : W) : w ~[(⊥ : Background W).accessible] w' := by simp

theorem isRealistic_iff_refl {f : Background W} : f.IsRealistic ↔ f.accessible.IsRefl :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.refl⟩

theorem isConsistent_iff_isSerial {f : Background W} : f.IsConsistent ↔ IsSerial f.accessible :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.serial⟩

variable {f g : Background W} {w : W} {s : Set W}

/-! ### Necessity

The definition of [kratzer-1991], which revises that of [kratzer-1981], does not suppose that there
are best worlds: it asks each accessible world to have an accessible world at least as good, at and
below which the proposition holds throughout. -/

/-- The necessities at `w` under a modal base `f` and an ordering source `g`: `s` is one when every
accessible world has an accessible world at least as good below which `s` holds throughout,
Definition 6 of [kratzer-1991]. -/
def Background.necessity (f g : Background W) (w : W) : Filter W :=
  @atBotOn W W (≤[g w]) id (f.accessibleWorlds w)

theorem Background.mem_necessity : s ∈ f.necessity g w ↔ ∀ u ∈ f.accessibleWorlds w,
    ∃ v ∈ f.accessibleWorlds w, (v ≤[g w] u) ∧ ∀ z ∈ f.accessibleWorlds w, (z ≤[g w] v) → z ∈ s :=
  .rfl

/-- The necessities at a world are consistent exactly when its modal base is, whatever the ordering
source: **D**. -/
theorem Background.necessity_neBot_iff :
    (f.necessity g w).NeBot ↔ (f.accessibleWorlds w).Nonempty :=
  letI := ≤[g w]; atBotOn_neBot_iff

/-- `s` is a possibility at `w` when its negation is not a necessity there,
Definition 8 of [kratzer-1991]. -/
def Background.possibility (f g : Background W) (w : W) (s : Set W) : Prop :=
  ∃ᶠ v in f.necessity g w, v ∈ s

theorem Background.possibility_iff_compl_notMem :
    f.possibility g w s ↔ sᶜ ∉ f.necessity g w :=
  .rfl

/-- `s` is a good possibility at `w` when some accessible world sees only `s`-worlds among the
accessible worlds at least as good as itself, so that `s` holds throughout a branch of the
ordering, Definition 7 of [kratzer-1991]. -/
def Background.goodPossibility (f g : Background W) (w : W) (s : Set W) : Prop :=
  ∃ u ∈ f.accessibleWorlds w, ∀ v ∈ f.accessibleWorlds w, (v ≤[g w] u) → v ∈ s

theorem Background.goodPossibility_iff : f.goodPossibility g w s ↔
    ∃ u ∈ f.accessibleWorlds w, ∀ v ∈ f.accessibleWorlds w, (v ≤[g w] u) → v ∈ s :=
  .rfl

theorem Background.goodPossibility_of_mem_necessity (hne : (f.accessibleWorlds w).Nonempty)
    (h : s ∈ f.necessity g w) : f.goodPossibility g w s :=
  letI := ≤[g w]; exists_of_mem_atBotOn h hne

/-- A good possibility is a possibility. -/
theorem Background.possibility_of_goodPossibility (h : f.goodPossibility g w s) :
    f.possibility g w s := fun hN ↦
  let ⟨u, hu, hs⟩ := h
  let ⟨v, hv, hvu, hz⟩ := Background.mem_necessity.1 hN u hu
  hz v hv (@le_refl _ (≤[g w]) v) (hs v hv hvu)

/-! ### The Limit Assumption -/

/-- A necessity holds at every best world. -/
theorem Background.principal_bestWorlds_le_necessity : 𝓟 (bestWorlds f g w) ≤ f.necessity g w :=
  fun _ h ↦ letI := ≤[g w]; setOf_minimalFor_subset_of_mem_atBotOn h

/-- The Limit Assumption holds at `w` when every accessible world sees a best world at least as
good. -/
def LimitAssumption (f g : Background W) (w : W) : Prop :=
  ∀ u ∈ f.accessibleWorlds w, ∃ v ∈ bestWorlds f g w, (v ≤[g w] u)

/-- The Limit Assumption says that the best worlds are at least as possible as the accessible
worlds, in Lewis's sense of comparative possibility. -/
theorem limitAssumption_iff_lewis :
    LimitAssumption f g w ↔ ComparativePossibility.Lewis (≤[g w]).le
      (bestWorlds f g w) (f.accessibleWorlds w) :=
  .rfl

theorem LimitAssumption.of_finite [Finite W] (f g : Background W) (w : W) :
    LimitAssumption f g w := fun _ hu ↦
  Preorder.exists_le_mem_minimals (letI := ≤[g w]; wellFounded_lt) hu

/-- An empty ordering source satisfies the Limit Assumption, every accessible world being best. -/
theorem LimitAssumption.bot (f : Background W) (w : W) : LimitAssumption f ⊥ w :=
  fun u hu ↦ ⟨u, (bestWorlds_bot f w).symm ▸ hu, fun _ _ ↦ id⟩

/-- Under the Limit Assumption the necessities are the propositions true at every best
world. -/
theorem Background.necessity_eq_principal (hlim : LimitAssumption f g w) :
    f.necessity g w = 𝓟 (bestWorlds f g w) :=
  letI := ≤[g w]; atBotOn_eq_principal hlim

theorem Background.necessity_eq_principal_of_finite [Finite W] :
    f.necessity g w = 𝓟 (bestWorlds f g w) :=
  Background.necessity_eq_principal (.of_finite f g w)

theorem Background.possibility_iff_exists_bestWorlds (hlim : LimitAssumption f g w) :
    f.possibility g w s ↔ ∃ v ∈ bestWorlds f g w, v ∈ s := by
  rw [Background.possibility, Background.necessity_eq_principal hlim, frequently_principal]

/-- Under the Limit Assumption, what is necessary at `w` is true at `w` exactly when `w` is one of
its own best worlds: **T**. -/
theorem Background.pure_le_necessity_iff (hlim : LimitAssumption f g w) :
    pure w ≤ f.necessity g w ↔ w ∈ bestWorlds f g w := by
  rw [Background.necessity_eq_principal hlim, pure_le_principal]

/-- Under a modal base and an ordering source, `w'` is best-accessible from `w` when it is among
the best worlds accessible from `w`. -/
def bestAccessible (f g : Background W) : SetRel W W :=
  .cgraph (bestWorlds f g)

@[simp] theorem mem_bestAccessible {f g : Background W} {w w' : W} :
    w ~[bestAccessible f g] w' ↔ w' ∈ bestWorlds f g w := .rfl

@[simp] theorem bestAccessible_bot (f : Background W) : bestAccessible f ⊥ = f.accessible :=
  congrArg cgraph (funext (bestWorlds_bot f))

/-- Under the Limit Assumption, necessity is `□` along the best-accessible relation. -/
theorem box_bestAccessible_iff (hlim : LimitAssumption f g w) (p : W → Prop) :
    □[bestAccessible f g] p w ↔ ∀ᶠ v in f.necessity g w, p v := by
  rw [Background.necessity_eq_principal hlim, eventually_principal]; rfl

/-! ### The empty ordering source

Over the empty ordering source every accessible world is best, and the necessities are the
propositions true at every accessible world. -/

/-- The simple necessities at `w` under a modal base `f` are the propositions that follow from its
premises there, `⋂f(w) ⊆ s`, Definition 5 of [kratzer-1977]. -/
def Background.simpleNecessity (f : Background W) (w : W) : Filter W :=
  𝓟 (f.accessibleWorlds w)

@[simp] theorem Background.mem_simpleNecessity :
    s ∈ f.simpleNecessity w ↔ f.accessibleWorlds w ⊆ s :=
  .rfl

/-- `s` is a simple possibility at `w` when its negation is not a simple necessity there. -/
def Background.simplePossibility (f : Background W) (w : W) (s : Set W) : Prop :=
  ∃ᶠ v in f.simpleNecessity w, v ∈ s

/-- Simple possibility is compatibility with the premises, `⋂f(w) ∩ s ≠ ∅`, Definition 6 of
[kratzer-1977]. -/
@[simp] theorem Background.simplePossibility_iff :
    f.simplePossibility w s ↔ ∃ v ∈ f.accessibleWorlds w, v ∈ s :=
  frequently_principal

/-- A realistic modal base makes what must be the case the case: **T**, as `pure_le_nhds` for
neighbourhoods. -/
theorem Background.isRealistic_iff_pure_le_simpleNecessity :
    f.IsRealistic ↔ ∀ w, pure w ≤ f.simpleNecessity w :=
  forall_congr' fun w ↦ (pure_le_principal w).symm

@[simp] theorem Background.necessity_bot (f : Background W) (w : W) :
    f.necessity ⊥ w = f.simpleNecessity w := by
  rw [Background.necessity_eq_principal (.bot f w), bestWorlds_bot, Background.simpleNecessity]

theorem Background.goodPossibility_bot_iff :
    f.goodPossibility ⊥ w s ↔ (f.accessibleWorlds w).Nonempty ∧ s ∈ f.simpleNecessity w :=
  ⟨fun ⟨u, hu, h⟩ ↦ ⟨⟨u, hu⟩, fun v hv ↦ h v hv fun _ h ↦ h.elim⟩,
    fun ⟨⟨u, hu⟩, h⟩ ↦ ⟨u, hu, fun _ hv _ ↦ h hv⟩⟩

/-- A necessity need not be a simple necessity, and every simple necessity is a necessity. -/
theorem Background.necessity_le_simpleNecessity (f g : Background W) (w : W) :
    f.necessity g w ≤ f.simpleNecessity w := fun _ hs ↦
  mem_of_superset (letI := ≤[g w]; self_mem_atBotOn) hs

/-- Simple necessity is `□` along the accessibility relation of the modal base. -/
theorem Background.box_accessible_iff (p : W → Prop) :
    □[f.accessible] p w ↔ ∀ᶠ v in f.simpleNecessity w, p v := by
  rw [Background.simpleNecessity, eventually_principal]; rfl

/-! ### Totally realistic modal bases -/

/-- Over a totally realistic modal base the only best world is the world of evaluation. -/
theorem Background.IsTotallyRealistic.bestWorlds_eq_singleton (hf : f.IsTotallyRealistic)
    (g : Background W) (w : W) : bestWorlds f g w = {w} := by
  refine Set.ext fun v ↦ ?_
  rw [mem_bestWorlds, hf w]
  refine ⟨And.left, fun hv ↦ ⟨hv, fun u hu _ ↦ ?_⟩⟩
  rw [Set.mem_singleton_iff] at hu hv
  subst hu hv
  exact fun _ _ ↦ id

/-! ### Unified backgrounds

When some accessible world verifies every premise of the ordering source, it is at least as good
as every accessible world, the worlds at least as good as it are those accessible under the
unified background `f ⊔ g`, and the forces that read the ordering collapse to simple necessity
over the unified background. -/

theorem Background.mem_simpleNecessity_sup_of_goodPossibility (h : f.goodPossibility g w s) :
    s ∈ (f ⊔ g).simpleNecessity w := fun v hv ↦
  let ⟨u, _, hp⟩ := h
  let hv := (Background.accessibleWorlds_sup f g w).subset hv
  hp v hv.1 (le_of_mem_accessibleWorlds hv.2 u)

private theorem mem_simpleNecessity_sup_iff {b : W} (hb : b ∈ g.accessibleWorlds w) :
    s ∈ (f ⊔ g).simpleNecessity w ↔ ∀ v ∈ f.accessibleWorlds w, (v ≤[g w] b) → v ∈ s := by
  simp only [Background.mem_simpleNecessity, Background.accessibleWorlds_sup, Set.subset_def,
    Set.mem_inter_iff, and_imp, mem_accessibleWorlds_iff_le hb]

section

variable (h : ((f ⊔ g).accessibleWorlds w).Nonempty)
include h

/-- When the ordering source is consistent with the modal base, good possibility is simple
necessity over the unified backgrounds. -/
theorem Background.goodPossibility_iff_mem_simpleNecessity_sup :
    f.goodPossibility g w s ↔ s ∈ (f ⊔ g).simpleNecessity w :=
  let ⟨b, hb⟩ := h
  let hb := (Background.accessibleWorlds_sup f g w).subset hb
  (mem_simpleNecessity_sup_iff hb.2).trans ⟨fun hs ↦ ⟨b, hb.1, hs⟩, fun ⟨u, _, hp⟩ v hv hvb ↦
    hp v hv ((≤[g w]).le_trans _ _ _ hvb (le_of_mem_accessibleWorlds hb.2 u))⟩
    |>.symm

/-- When the ordering source is consistent with the modal base, the necessities are the
simple necessities of the unified backgrounds. -/
theorem Background.necessity_eq_simpleNecessity_sup :
    f.necessity g w = (f ⊔ g).simpleNecessity w :=
  letI := ≤[g w]
  let ⟨_, hb⟩ := h
  let hb := (Background.accessibleWorlds_sup f g w).subset hb
  Filter.ext fun _ ↦ (mem_atBotOn_iff_of_least hb.1
    fun v _ ↦ le_of_mem_accessibleWorlds hb.2 v).trans (mem_simpleNecessity_sup_iff hb.2).symm

theorem Background.goodPossibility_iff_mem_necessity :
    f.goodPossibility g w s ↔ s ∈ f.necessity g w := by
  rw [Background.goodPossibility_iff_mem_simpleNecessity_sup h,
    Background.necessity_eq_simpleNecessity_sup h]

end

/-! ### Claims of a quantificational force -/

namespace QuantificationalForce

variable (N : W → Filter W) (p : Set W)

/-- The claim a modal of quantificational force `q` makes about `p` over the necessities `N`: that
`p` is a necessity, or that its negation is not. -/
def claim : QuantificationalForce → Set W
  | .universal => {w | p ∈ N w}
  | .existential => {w | ∃ᶠ v in N w, v ∈ p}

variable {N p}

@[simp] theorem mem_claim_universal : w ∈ claim N p .universal ↔ p ∈ N w := .rfl

@[simp] theorem mem_claim_existential : w ∈ claim N p .existential ↔ ∃ᶠ v in N w, v ∈ p := .rfl

/-- Over consistent necessities the universal claim entails the existential one. -/
theorem antitone_claim (hN : ∀ w, (N w).NeBot) : Antitone (claim N p) := by
  intro q r hqr w hw
  have := hN w
  cases q <;> cases r
  exacts [hw, Eventually.frequently hw, absurd hqr (by decide), hw]

variable (N p)

/-- The negation of a claim is the dual claim about the negated prejacent. -/
theorem compl_claim (q : QuantificationalForce) : (claim N p q)ᶜ = claim N pᶜ q.dual := by
  ext w
  cases q
  exacts [not_frequently, not_eventually]

end QuantificationalForce

end Modality
