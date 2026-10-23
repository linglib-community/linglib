module

public import Linglib.Semantics.Modality.Background
public import Linglib.Semantics.Modality.OrderingSemantics
public import Linglib.Logic.Modal.Basic

/-!
# Necessity and possibility over conversational backgrounds

Kratzer's modal operators are the box and diamond of `Logic.Modal` over the accessibility
relations two conversational backgrounds induce. Simple necessity quantifies over the worlds a
modal base makes accessible, and necessity over the best of them under an ordering source.
Kratzer's own definition, human necessity, needs no Limit Assumption: each accessible world must
see, at least as good, a witness below which only `p`-worlds occur. It is universal
quantification over the best worlds exactly under the Limit Assumption, which every finite frame
satisfies. Good possibility asks for one such witness, so `p` may hold on one branch of the
ordering and its rival on another; Portner and Rubinstein call it local necessity. Both are the
forces of ordering semantics (`OrderingSemantics`) over the accessible worlds ranked by the
ordering source. When the ordering source is consistent with the modal base, the two
backgrounds unify into one and both forces become simple necessity over their union.

## Main definitions

* `Background.ofRel R`: the background whose accessible worlds are the `R`-successors.
* `simpleNecessity f`, `simplePossibility f`: the box and diamond of `f.accessible`.
* `necessity f g`, `possibility f g`: the box and diamond of `bestAccessible f g`.
* `humanNecessity f g`, `humanPossibility f g`, `LimitAssumption f g w`.
* `goodPossibility f g`: some accessible world sees only `p`-worlds at least as good.

## Main statements

* `humanNecessity_iff_necessity`: under the Limit Assumption, human necessity is necessity.
* `goodPossibility_iff_simpleNecessity_sup`: with the ordering source consistent with the modal
  base, good possibility is simple necessity over the unified backgrounds.
* `isRealistic_iff_simpleNecessity_le_id`: a modal base is realistic exactly when simple
  necessity over it is veridical.
* `simpleNecessity_iff_sInf_le`: simple necessity is consequence from the premises at the world.

## Implementation notes

`necessity` quantifies over `bestWorlds` directly, so studies that treat `necessity` and
`possibility` as the Kratzer pair inherit the Limit Assumption; `humanNecessity` is the
limit-free form. Kratzer's comparative possibility, weak necessity and slight possibility are
not formalized here.

## References

* [kratzer-1977]
* [kratzer-1981]
* [kratzer-2012]
* [portner-rubinstein-2020]
-/

@[expose] public section

namespace Modality

open ModalLogic SetRel

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
def Background.ofRel (R : SetRel W W) : Background W := fun w ↦ {(w ~[R] ·)}

@[simp] theorem Background.accessibleWorlds_ofRel (R : SetRel W W) (w : W) :
    (Background.ofRel R).accessibleWorlds w = {v | w ~[R] v} := by
  ext
  simp [Background.ofRel]

@[simp] theorem Background.accessible_ofRel (R : SetRel W W) :
    (Background.ofRel R).accessible = R := by
  ext ⟨w, v⟩
  exact (Set.ext_iff.1 (Background.accessibleWorlds_ofRel R w) v)

@[simp] theorem mem_bestAccessible {f g : Background W} {w w' : W} :
    w ~[bestAccessible f g] w' ↔ w' ∈ bestWorlds f g w := .rfl

@[simp] theorem bestAccessible_bot (f : Background W) : bestAccessible f ⊥ = f.accessible :=
  congrArg ofSuccessors (funext (bestWorlds_bot f))

/-! ### Operators -/

/-- Simple necessity holds when `p` holds at every accessible world,
`⟦must⟧_f(p)(w) = ∀w' ∈ ⋂f(w). p(w')`, Definition 5 of [kratzer-1977]. -/
def simpleNecessity (f : Background W) (p : W → Prop) (w : W) : Prop :=
  □[f.accessible] p w

/-- Simple possibility holds when `p` holds at some accessible world,
`⟦can⟧_f(p)(w) = ∃w' ∈ ⋂f(w). p(w')`, Definition 6 of [kratzer-1977]. -/
def simplePossibility (f : Background W) (p : W → Prop) (w : W) : Prop :=
  ◇[f.accessible] p w

/-- Necessity with an ordering source holds when `p` holds at every best world,
`⟦must⟧_{f,g}(p)(w) = ∀w' ∈ Best(f,g,w). p(w')`, the Limit Assumption form of
`humanNecessity`. -/
def necessity (f g : Background W) (p : W → Prop) (w : W) : Prop :=
  □[bestAccessible f g] p w

/-- Possibility with an ordering source holds when `p` holds at some best world,
`⟦can⟧_{f,g}(p)(w) = ∃w' ∈ Best(f,g,w). p(w')`. -/
def possibility (f g : Background W) (p : W → Prop) (w : W) : Prop :=
  ◇[bestAccessible f g] p w

theorem necessity_mono {f g : Background W} {p q : W → Prop} {w : W}
    (hpq : p ≤ q) (h : necessity f g p w) : necessity f g q w :=
  box_mono (bestAccessible f g) hpq w h

theorem possibility_mono {f g : Background W} {p q : W → Prop} {w : W}
    (hpq : p ≤ q) (h : possibility f g p w) : possibility f g q w :=
  diamond_mono (bestAccessible f g) hpq w h

theorem necessity_and {f g : Background W} {p q : W → Prop} {w : W} :
    necessity f g (fun v ↦ p v ∧ q v) w ↔ necessity f g p w ∧ necessity f g q w :=
  iff_of_eq (congrFun (box_inf (bestAccessible f g)) w)

theorem necessity_and_left {f g : Background W} {p q : W → Prop} {w : W}
    (h : necessity f g (fun v ↦ p v ∧ q v) w) : necessity f g p w :=
  (necessity_and.mp h).1

/-! ### Human necessity

[kratzer-1981]'s official definition needs no Limit Assumption, asking each accessible world to
see, at least as good, a witness below which only `p`-worlds occur. It is the necessity of
ordering semantics over the accessible worlds ranked by the ordering source, and `necessity`,
universal quantification over `bestWorlds`, is its Limit Assumption collapse. -/

/-- Human necessity holds when every accessible world has an accessible world at least as good,
below which `p` holds throughout ([kratzer-1981], restated as necessity in [kratzer-2012]). -/
def humanNecessity (f g : Background W) (p : W → Prop) (w : W) : Prop :=
  OrderingSemantics.IsNecessity (premisePreorder (g w)) (f.accessibleWorlds w) {v | p v}

theorem humanNecessity_iff {f g : Background W} {p : W → Prop} {w : W} :
    humanNecessity f g p w ↔ ∀ u ∈ f.accessibleWorlds w, ∃ v ∈ f.accessibleWorlds w,
      (v ≤[g w] u) ∧ ∀ z ∈ f.accessibleWorlds w, (z ≤[g w] v) → p z :=
  Iff.rfl

theorem necessity_of_humanNecessity {f g : Background W} {p : W → Prop}
    {w : W} (h : humanNecessity f g p w) : necessity f g p w :=
  fun _ hv ↦ h.minimals_subset hv

/-- The Limit Assumption holds at `w` when every accessible world sees a best world at least as
good. -/
def LimitAssumption (f g : Background W) (w : W) : Prop :=
  ∀ u ∈ f.accessibleWorlds w, ∃ v ∈ bestWorlds f g w, (v ≤[g w] u)

theorem LimitAssumption.of_finite [Finite W] (f g : Background W) (w : W) :
    LimitAssumption f g w := fun _ hu ↦
  Preorder.exists_le_mem_minimals (letI := premisePreorder (g w); wellFounded_lt) hu

theorem humanNecessity_of_necessity {f g : Background W} {p : W → Prop}
    {w : W} (hlim : LimitAssumption f g w) (h : necessity f g p w) :
    humanNecessity f g p w :=
  OrderingSemantics.isNecessity_of_minimals_subset hlim fun _ hv ↦ h _ hv

/-- Under the Limit Assumption, [kratzer-1981]'s human necessity is exactly universal
quantification over the best worlds. -/
theorem humanNecessity_iff_necessity {f g : Background W} {p : W → Prop}
    {w : W} (hlim : LimitAssumption f g w) :
    humanNecessity f g p w ↔ necessity f g p w :=
  ⟨necessity_of_humanNecessity, humanNecessity_of_necessity hlim⟩

/-- Human possibility is the dual of `humanNecessity`, holding when the negation is not a human
necessity ([kratzer-2012]). -/
def humanPossibility (f g : Background W) (p : W → Prop) (w : W) : Prop :=
  ¬ humanNecessity f g (fun v ↦ ¬ p v) w

theorem humanPossibility_iff_possibility {f g : Background W}
    {p : W → Prop} {w : W} (hlim : LimitAssumption f g w) :
    humanPossibility f g p w ↔ possibility f g p w := by
  rw [humanPossibility, humanNecessity_iff_necessity hlim, necessity, possibility, not_box]
  simp [Diamond]

theorem humanNecessity_bot_iff (f : Background W) (p : W → Prop) (w : W) :
    humanNecessity f ⊥ p w ↔ simpleNecessity f p w := by
  constructor
  · intro h u hu
    obtain ⟨v, _, _, hall⟩ := h u hu
    exact hall u hu fun _ h ↦ h.elim
  · intro h u hu
    exact ⟨u, hu, fun _ h ↦ h.elim, fun z hz _ ↦ h z hz⟩

/-! ### Good possibility -/

section GoodPossibility

variable {f g : Background W} {p q : W → Prop} {w : W}

/-- Good possibility holds when some accessible world sees only `p`-worlds among the accessible
worlds at least as good as itself, so that `p` holds throughout a branch of the ordering. -/
def goodPossibility (f g : Background W) (p : W → Prop) (w : W) : Prop :=
  OrderingSemantics.IsGoodPossibility (premisePreorder (g w)) (f.accessibleWorlds w) {v | p v}

theorem goodPossibility_iff : goodPossibility f g p w ↔
    ∃ u ∈ f.accessibleWorlds w, ∀ v ∈ f.accessibleWorlds w, (v ≤[g w] u) → p v :=
  Iff.rfl

theorem goodPossibility_mono (h : ∀ v, p v → q v) :
    goodPossibility f g p w → goodPossibility f g q w :=
  fun hp ↦ hp.mono fun v ↦ h v

theorem goodPossibility_of_humanNecessity (hne : (f.accessibleWorlds w).Nonempty)
    (h : humanNecessity f g p w) : goodPossibility f g p w :=
  h.isGoodPossibility hne

theorem goodPossibility_bot_iff (f : Background W) (p : W → Prop) (w : W) :
    goodPossibility f ⊥ p w ↔ (f.accessibleWorlds w).Nonempty ∧ simpleNecessity f p w :=
  ⟨fun ⟨u, hu, h⟩ ↦ ⟨⟨u, hu⟩, fun v hv ↦ h v hv fun _ h ↦ h.elim⟩,
    fun ⟨⟨u, hu⟩, h⟩ ↦ ⟨u, hu, fun v hv _ ↦ h v hv⟩⟩

/-! ### Unified backgrounds

When some accessible world verifies every premise of the ordering source, it is at least as good
as every accessible world, the worlds at least as good as it are those accessible under the
unified background `f ⊔ g`, and the forces that read the ordering collapse to simple necessity
over the unified background. -/

theorem simpleNecessity_sup_of_goodPossibility (h : goodPossibility f g p w) :
    simpleNecessity (f ⊔ g) p w := by
  obtain ⟨u, -, hp⟩ := h
  show ∀ v ∈ (f ⊔ g).accessibleWorlds w, p v
  intro v hv
  rw [Background.accessibleWorlds_sup] at hv
  exact hp v hv.1 ((Preorder.ofCriteria_le_iff _ _ _ _).2 fun r hr _ ↦ hv.2 r hr)

theorem simpleNecessity_sup_of_humanNecessity (h : humanNecessity f g p w) :
    simpleNecessity (f ⊔ g) p w := by
  show ∀ v ∈ (f ⊔ g).accessibleWorlds w, p v
  intro v hv
  rw [Background.accessibleWorlds_sup] at hv
  obtain ⟨_, -, -, hall⟩ := h v hv.1
  exact hall v hv.1 ((Preorder.ofCriteria_le_iff _ _ _ _).2 fun r hr _ ↦ hv.2 r hr)

section Unified

variable {b : W} (hb : b ∈ (f ⊔ g).accessibleWorlds w)
include hb

private theorem mem_of_mem_sup : b ∈ f.accessibleWorlds w :=
  ((Background.accessibleWorlds_sup f g w).subset hb).1

private theorem le_of_mem_sup (v : W) : (b ≤[g w] v) :=
  fun r hr _ ↦ ((Background.accessibleWorlds_sup f g w).subset hb).2 r hr

private theorem simpleNecessity_sup_iff_of_mem :
    simpleNecessity (f ⊔ g) p w ↔
      ∀ v ∈ f.accessibleWorlds w, (v ≤[g w] b) → v ∈ {v | p v} := by
  have hb' := (Background.accessibleWorlds_sup f g w).subset hb
  show (∀ v ∈ (f ⊔ g).accessibleWorlds w, p v) ↔ _
  rw [Background.accessibleWorlds_sup]
  exact ⟨fun h v hv hvb ↦ h v ⟨hv, fun r hr ↦ hvb r hr (hb'.2 r hr)⟩,
    fun h v hv ↦ h v hv.1 fun r hr _ ↦ hv.2 r hr⟩

end Unified

variable (h : ((f ⊔ g).accessibleWorlds w).Nonempty)
include h

/-- When the ordering source is consistent with the modal base, good possibility is simple
necessity over the unified backgrounds. -/
theorem goodPossibility_iff_simpleNecessity_sup :
    goodPossibility f g p w ↔ simpleNecessity (f ⊔ g) p w :=
  let ⟨_, hb⟩ := h
  (OrderingSemantics.isGoodPossibility_iff_of_least (mem_of_mem_sup hb)
    fun v _ ↦ le_of_mem_sup hb v).trans (simpleNecessity_sup_iff_of_mem hb).symm

theorem humanNecessity_iff_simpleNecessity_sup :
    humanNecessity f g p w ↔ simpleNecessity (f ⊔ g) p w :=
  let ⟨_, hb⟩ := h
  (OrderingSemantics.isNecessity_iff_of_least (mem_of_mem_sup hb)
    fun v _ ↦ le_of_mem_sup hb v).trans (simpleNecessity_sup_iff_of_mem hb).symm

theorem goodPossibility_iff_humanNecessity :
    goodPossibility f g p w ↔ humanNecessity f g p w :=
  (goodPossibility_iff_simpleNecessity_sup h).trans (humanNecessity_iff_simpleNecessity_sup h).symm

end GoodPossibility

/-! ### Characterization lemmas -/

@[simp]
theorem simpleNecessity_iff (f : Background W) (p : W → Prop) (w : W) :
    simpleNecessity f p w ↔ ∀ w' ∈ f.accessibleWorlds w, p w' := Iff.rfl

@[simp]
theorem simplePossibility_iff (f : Background W) (p : W → Prop) (w : W) :
    simplePossibility f p w ↔ ∃ w' ∈ f.accessibleWorlds w, p w' := Iff.rfl

@[simp]
theorem necessity_iff (f g : Background W) (p : W → Prop) (w : W) :
    necessity f g p w ↔ ∀ w' ∈ bestWorlds f g w, p w' := Iff.rfl

@[simp]
theorem possibility_iff (f g : Background W) (p : W → Prop) (w : W) :
    possibility f g p w ↔ ∃ w' ∈ bestWorlds f g w, p w' := Iff.rfl

/-- Simple necessity is consequence from the premises at the world, `⋂f(w) ⊆ p`, Definition 5 of
[kratzer-1977]. -/
theorem simpleNecessity_iff_sInf_le (f : Background W) (p : W → Prop) (w : W) :
    simpleNecessity f p w ↔ sInf (f w) ≤ p := Iff.rfl

/-- Simple possibility is compatibility with the premises at the world, `⋂f(w) ∩ p ≠ ∅`,
Definition 6 of [kratzer-1977]. -/
theorem simplePossibility_iff_not_disjoint (f : Background W) (p : W → Prop) (w : W) :
    simplePossibility f p w ↔ ¬ Disjoint (sInf (f w)) p := by
  simp [simplePossibility_iff, Pi.disjoint_iff, Prop.disjoint_iff, not_forall]

@[simp] theorem necessity_bot_iff (f : Background W) (p : W → Prop) (w : W) :
    necessity f ⊥ p w ↔ simpleNecessity f p w := by
  simp only [necessity_iff, simpleNecessity_iff, bestWorlds_bot]

/-! ### Monotonicity in the modal base -/

theorem simpleNecessity_mono {f f' : Background W} {p : W → Prop} {w : W} (h : f w ⊆ f' w)
    (hNec : simpleNecessity f p w) : simpleNecessity f' p w :=
  fun w' hw' ↦ hNec w' (Background.accessibleWorlds_anti h hw')

theorem not_necessity_insert {f g : Background W} {p q r : W → Prop} {w u : W}
    (hq : q ∈ g w) (hpq : ∀ v, q v → ¬ p v) (hu : u ∈ bestWorlds f g w) (huq : q u)
    (hur : ¬ r u) : ¬ necessity f (fun v ↦ insert p (g v)) r w :=
  fun h ↦ hur (h u (mem_bestWorlds_insert hq hpq hu huq))

/-! ### Frame conditions on `Background.accessible` -/

/-- A realistic modal base gives reflexive accessibility. -/
theorem Background.IsRealistic.refl {f : Background W} (h : f.IsRealistic) :
    f.accessible.IsRefl :=
  ⟨fun w ↦ h w⟩

theorem Background.IsRealistic.isSerial {f : Background W} (h : f.IsRealistic) :
    IsSerial f.accessible :=
  ⟨fun w ↦ ⟨w, h.refl.refl w⟩⟩

theorem isRealistic_iff_refl {f : Background W} : f.IsRealistic ↔ f.accessible.IsRefl :=
  ⟨Background.IsRealistic.refl, fun h w ↦ h.refl w⟩

/-- A modal base is realistic exactly when simple necessity over it is veridical, what must be
the case being the case, so **T** defines realism. -/
theorem isRealistic_iff_simpleNecessity_le_id {f : Background W} :
    f.IsRealistic ↔ simpleNecessity f ≤ id :=
  isRealistic_iff_refl.trans box_T_iff.symm

theorem isRealistic_iff_id_le_simplePossibility {f : Background W} :
    f.IsRealistic ↔ id ≤ simplePossibility f :=
  isRealistic_iff_refl.trans diamond_T_iff.symm

theorem accessible_bot (w w' : W) : w ~[(⊥ : Background W).accessible] w' := by simp

/-! ### Modal axioms -/

theorem duality (f g : Background W) (p : W → Prop) (w : W) :
    necessity f g p w ↔ ¬ possibility f g (fun w' ↦ ¬ p w') w := by
  rw [necessity, possibility, not_diamond]
  simp [Box]

theorem necessity_K (f g : Background W) (p q : W → Prop) (w : W)
    (hImpl : necessity f g (fun w' ↦ p w' → q w') w) (hP : necessity f g p w) :
    necessity f g q w :=
  box_K hImpl hP

theorem Background.IsTotallyRealistic.necessity_le_id {f : Background W}
    (hTotal : f.IsTotallyRealistic) (g : Background W) : necessity f g ≤ id := by
  intro p w hNec
  have hacc : f.accessibleWorlds w = {w} := hTotal w
  refine hNec w ⟨by rw [hacc]; exact Set.mem_singleton w, fun v hv _ ↦ ?_⟩
  rw [hacc, Set.mem_singleton_iff] at hv
  subst hv
  exact (premisePreorder _).le_refl _

end Modality
