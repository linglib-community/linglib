module

public import Linglib.Semantics.Modality.Background
public import Linglib.Core.Order.Filter.AtBotOn
public import Linglib.Semantics.Modality.ComparativePossibility
public import Linglib.Logic.Modal.Basic

/-!
# Necessity and possibility over conversational backgrounds

Conversational backgrounds assign each world a filter of propositions, its necessities, so that a
modal claim is membership, as a neighbourhood of a point belongs to `𝓝 x`, and possibility is the
dual `∃ᶠ`. Simple necessity is the principal filter of the accessible worlds. Kratzer's human
necessity, which needs no Limit Assumption, is what holds toward the bottom of the accessible worlds
ranked by the ordering source, `Filter.atBotOn`, and is [truth at the best
worlds](##Modality.humanNecessity_eq_principal) exactly under the Limit Assumption. Good possibility
asks for one branch of the ordering on which a proposition holds throughout. When the two
backgrounds are consistent, [human necessity is simple necessity over their
union](##Modality.humanNecessity_eq_simpleNecessity_sup).

## Main definitions

* `simpleNecessity f w`, `humanNecessity f g w`: the necessities at `w`, each a `Filter W`.
* `simplePossibility f w`, `humanPossibility f g w`: their duals.
* `goodPossibility f g w`, `LimitAssumption f g w`.

## Implementation notes

The laws of each force are filter lemmas: closure under consequence is `Filter.mem_of_superset`,
under conjunction `Filter.inter_mem`, and the axioms **T** and **D** are `pure w ≤ N w` and
`(N w).NeBot`, as for neighbourhoods in topology (`pure_le_nhds`). A prejacent stated as a
predicate is `∀ᶠ v in N w, p v`, definitionally `{v | p v} ∈ N w`. Truth at the best worlds, the
form most applications state under the Limit Assumption, is `bestWorlds f g w ⊆ s`, the principal
filter `𝓟 (bestWorlds f g w)` needing no name of its own. Weak necessity and slight possibility are
not formalized here.

## References

* [kratzer-1977]
* [kratzer-1981]
* [kratzer-1991]
* [kratzer-2012]
* [portner-rubinstein-2020]
-/

@[expose] public section

namespace Modality

open Filter ModalLogic SetRel

variable {W : Type*}

/-! ### Accessibility relations -/

/-- Under a modal base, `w'` is accessible from `w` when it satisfies every premise of `f w`,
Kratzer's `w' ∈ ⋂f(w)`. -/
def Background.accessible (f : Background W) : SetRel W W :=
  .ofSuccessors f.accessibleWorlds

/-- Under a modal base and an ordering source, `w'` is best-accessible from `w` when it is among
the best worlds accessible from `w`. -/
def bestAccessible (f g : Background W) : SetRel W W :=
  .ofSuccessors (bestWorlds f g)

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

@[simp] theorem mem_bestAccessible {f g : Background W} {w w' : W} :
    w ~[bestAccessible f g] w' ↔ w' ∈ bestWorlds f g w := .rfl

@[simp] theorem bestAccessible_bot (f : Background W) : bestAccessible f ⊥ = f.accessible :=
  congrArg ofSuccessors (funext (bestWorlds_bot f))

theorem accessible_bot (w w' : W) : w ~[(⊥ : Background W).accessible] w' := by simp

theorem isRealistic_iff_refl {f : Background W} : f.IsRealistic ↔ f.accessible.IsRefl :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.refl⟩

theorem isConsistent_iff_isSerial {f : Background W} : f.IsConsistent ↔ IsSerial f.accessible :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.serial⟩

variable {f g : Background W} {w : W} {s : Set W}

/-! ### Simple necessity -/

/-- The simple necessities at `w` under a modal base `f` are the propositions that follow from its
premises there, `⋂f(w) ⊆ s`, Definition 5 of [kratzer-1977]. -/
def simpleNecessity (f : Background W) (w : W) : Filter W :=
  𝓟 (f.accessibleWorlds w)

@[simp] theorem mem_simpleNecessity : s ∈ simpleNecessity f w ↔ f.accessibleWorlds w ⊆ s :=
  .rfl

/-- `s` is a simple possibility at `w` when its negation is not a simple necessity there. -/
def simplePossibility (f : Background W) (w : W) (s : Set W) : Prop :=
  ∃ᶠ v in simpleNecessity f w, v ∈ s

/-- Simple possibility is compatibility with the premises, `⋂f(w) ∩ s ≠ ∅`, Definition 6 of
[kratzer-1977]. -/
@[simp] theorem simplePossibility_iff :
    simplePossibility f w s ↔ ∃ v ∈ f.accessibleWorlds w, v ∈ s :=
  frequently_principal

/-- A realistic modal base makes what must be the case the case: **T**, as `pure_le_nhds` for
neighbourhoods. -/
theorem isRealistic_iff_pure_le_simpleNecessity :
    f.IsRealistic ↔ ∀ w, pure w ≤ simpleNecessity f w :=
  forall_congr' fun w ↦ (pure_le_principal w).symm

/-- A consistent modal base makes what must be the case possible: **D**. -/
theorem isConsistent_iff_simpleNecessity_neBot :
    f.IsConsistent ↔ ∀ w, (simpleNecessity f w).NeBot :=
  forall_congr' fun _ ↦ principal_neBot_iff.symm

/-- Over a totally realistic modal base the only best world is the world of evaluation. -/
theorem Background.IsTotallyRealistic.bestWorlds_eq_singleton (hf : f.IsTotallyRealistic)
    (g : Background W) (w : W) : bestWorlds f g w = {w} := by
  refine Set.ext fun v ↦ ?_
  rw [mem_bestWorlds, hf w]
  refine ⟨And.left, fun hv ↦ ⟨hv, fun u hu _ ↦ ?_⟩⟩
  rw [Set.mem_singleton_iff] at hu hv
  subst hu hv
  exact fun _ _ ↦ id

/-! ### Human necessity

Kratzer's official definition, in the version of [kratzer-1991] that revises [kratzer-1981], needs
no Limit Assumption, asking each accessible world to see, at least as good, a witness below which
the proposition holds throughout. Truth at the best worlds is its Limit Assumption collapse. -/

/-- The human necessities at `w`: `s` is one when every accessible world has an accessible world at
least as good below which `s` holds throughout, necessity in Definition 6 of [kratzer-1991] and in
[kratzer-2012], human necessity in [kratzer-1981]'s terms. -/
def humanNecessity (f g : Background W) (w : W) : Filter W :=
  @atBotOn W W (premisePreorder (g w)) id (f.accessibleWorlds w)

theorem mem_humanNecessity : s ∈ humanNecessity f g w ↔ ∀ u ∈ f.accessibleWorlds w,
    ∃ v ∈ f.accessibleWorlds w, (v ≤[g w] u) ∧ ∀ z ∈ f.accessibleWorlds w, (z ≤[g w] v) → z ∈ s :=
  .rfl

/-- `s` is a human possibility at `w` when its negation is not a human necessity there,
Definition 8 of [kratzer-1991]. -/
def humanPossibility (f g : Background W) (w : W) (s : Set W) : Prop :=
  ∃ᶠ v in humanNecessity f g w, v ∈ s

theorem humanPossibility_iff_compl_notMem :
    humanPossibility f g w s ↔ sᶜ ∉ humanNecessity f g w :=
  .rfl

/-- A human necessity holds at every best world. -/
theorem principal_bestWorlds_le_humanNecessity : 𝓟 (bestWorlds f g w) ≤ humanNecessity f g w :=
  fun _ h ↦ letI := premisePreorder (g w); setOf_minimalFor_subset_of_mem_atBotOn h

/-- The Limit Assumption holds at `w` when every accessible world sees a best world at least as
good. -/
def LimitAssumption (f g : Background W) (w : W) : Prop :=
  ∀ u ∈ f.accessibleWorlds w, ∃ v ∈ bestWorlds f g w, (v ≤[g w] u)

/-- The Limit Assumption says that the best worlds are at least as possible as the accessible
worlds, in Lewis's sense of comparative possibility. -/
theorem limitAssumption_iff_lewis :
    LimitAssumption f g w ↔ ComparativePossibility.Lewis (premisePreorder (g w)).le
      (bestWorlds f g w) (f.accessibleWorlds w) :=
  .rfl

theorem LimitAssumption.of_finite [Finite W] (f g : Background W) (w : W) :
    LimitAssumption f g w := fun _ hu ↦
  Preorder.exists_le_mem_minimals (letI := premisePreorder (g w); wellFounded_lt) hu

/-- An empty ordering source satisfies the Limit Assumption, every accessible world being best. -/
theorem LimitAssumption.bot (f : Background W) (w : W) : LimitAssumption f ⊥ w :=
  fun u hu ↦ ⟨u, (bestWorlds_bot f w).symm ▸ hu, fun _ _ ↦ id⟩

/-- Under the Limit Assumption the human necessities are the propositions true at every best
world. -/
theorem humanNecessity_eq_principal (hlim : LimitAssumption f g w) :
    humanNecessity f g w = 𝓟 (bestWorlds f g w) :=
  letI := premisePreorder (g w); atBotOn_eq_principal hlim

theorem humanNecessity_eq_principal_of_finite [Finite W] :
    humanNecessity f g w = 𝓟 (bestWorlds f g w) :=
  humanNecessity_eq_principal (.of_finite f g w)

theorem humanPossibility_iff_exists_bestWorlds (hlim : LimitAssumption f g w) :
    humanPossibility f g w s ↔ ∃ v ∈ bestWorlds f g w, v ∈ s := by
  rw [humanPossibility, humanNecessity_eq_principal hlim, frequently_principal]

@[simp] theorem humanNecessity_bot (f : Background W) (w : W) :
    humanNecessity f ⊥ w = simpleNecessity f w := by
  rw [humanNecessity_eq_principal (.bot f w), bestWorlds_bot, simpleNecessity]

/-! ### Good possibility -/

/-- `s` is a good possibility at `w` when some accessible world sees only `s`-worlds among the
accessible worlds at least as good as itself, so that `s` holds throughout a branch of the
ordering, Definition 7 of [kratzer-1991]. -/
def goodPossibility (f g : Background W) (w : W) (s : Set W) : Prop :=
  ∃ u ∈ f.accessibleWorlds w, ∀ v ∈ f.accessibleWorlds w, (v ≤[g w] u) → v ∈ s

theorem goodPossibility_iff : goodPossibility f g w s ↔
    ∃ u ∈ f.accessibleWorlds w, ∀ v ∈ f.accessibleWorlds w, (v ≤[g w] u) → v ∈ s :=
  .rfl

theorem goodPossibility_of_mem_humanNecessity (hne : (f.accessibleWorlds w).Nonempty)
    (h : s ∈ humanNecessity f g w) : goodPossibility f g w s :=
  letI := premisePreorder (g w); exists_of_mem_atBotOn h hne

theorem goodPossibility_bot_iff :
    goodPossibility f ⊥ w s ↔ (f.accessibleWorlds w).Nonempty ∧ s ∈ simpleNecessity f w :=
  ⟨fun ⟨u, hu, h⟩ ↦ ⟨⟨u, hu⟩, fun v hv ↦ h v hv fun _ h ↦ h.elim⟩,
    fun ⟨⟨u, hu⟩, h⟩ ↦ ⟨u, hu, fun _ hv _ ↦ h hv⟩⟩

/-! ### Unified backgrounds

When some accessible world verifies every premise of the ordering source, it is at least as good
as every accessible world, the worlds at least as good as it are those accessible under the
unified background `f ⊔ g`, and the forces that read the ordering collapse to simple necessity
over the unified background. -/

theorem mem_simpleNecessity_sup_of_goodPossibility (h : goodPossibility f g w s) :
    s ∈ simpleNecessity (f ⊔ g) w := fun v hv ↦
  let ⟨u, _, hp⟩ := h
  let hv := (Background.accessibleWorlds_sup f g w).subset hv
  hp v hv.1 (le_of_mem_accessibleWorlds hv.2 u)

private theorem mem_simpleNecessity_sup_iff {b : W} (hb : b ∈ g.accessibleWorlds w) :
    s ∈ simpleNecessity (f ⊔ g) w ↔ ∀ v ∈ f.accessibleWorlds w, (v ≤[g w] b) → v ∈ s := by
  simp only [mem_simpleNecessity, Background.accessibleWorlds_sup, Set.subset_def,
    Set.mem_inter_iff, and_imp, mem_accessibleWorlds_iff_le hb]

variable (h : ((f ⊔ g).accessibleWorlds w).Nonempty)
include h

/-- When the ordering source is consistent with the modal base, good possibility is simple
necessity over the unified backgrounds. -/
theorem goodPossibility_iff_mem_simpleNecessity_sup :
    goodPossibility f g w s ↔ s ∈ simpleNecessity (f ⊔ g) w :=
  let ⟨b, hb⟩ := h
  let hb := (Background.accessibleWorlds_sup f g w).subset hb
  (mem_simpleNecessity_sup_iff hb.2).trans ⟨fun hs ↦ ⟨b, hb.1, hs⟩, fun ⟨u, _, hp⟩ v hv hvb ↦
    hp v hv ((premisePreorder (g w)).le_trans _ _ _ hvb (le_of_mem_accessibleWorlds hb.2 u))⟩
    |>.symm

/-- When the ordering source is consistent with the modal base, the human necessities are the
simple necessities of the unified backgrounds. -/
theorem humanNecessity_eq_simpleNecessity_sup :
    humanNecessity f g w = simpleNecessity (f ⊔ g) w :=
  letI := premisePreorder (g w)
  let ⟨_, hb⟩ := h
  let hb := (Background.accessibleWorlds_sup f g w).subset hb
  Filter.ext fun _ ↦ (mem_atBotOn_iff_of_least hb.1
    fun v _ ↦ le_of_mem_accessibleWorlds hb.2 v).trans (mem_simpleNecessity_sup_iff hb.2).symm

theorem goodPossibility_iff_mem_humanNecessity :
    goodPossibility f g w s ↔ s ∈ humanNecessity f g w := by
  rw [goodPossibility_iff_mem_simpleNecessity_sup h, humanNecessity_eq_simpleNecessity_sup h]

end Modality
