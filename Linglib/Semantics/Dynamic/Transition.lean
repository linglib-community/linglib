module

public import Linglib.Semantics.Dynamic.State

/-!
# Transitions between context fibers

A `Transition W M X Y` is a world-indexed relation from assignments of the referents in `X` to
assignments of the referents in `Y ⊇ X`. Transitions compose by world-pointwise relational
composition, with equality as identity. Applied to information states, a transition is a context
change potential in Kamp, van Genabith and Reyle's sense (Def. 24): it takes the points of the
`X`-stratum to points of the `Y`-stratum, preserving worlds. The name follows Fernando's
transition-system reading of dynamic semantics.

## Main definitions

* `Transition`, `Transition.id`, `Transition.comp`: transitions and their composition.
* `Transition.apply`, `Transition.applyState`: context change on fibers and on states.
* `Transition.ofTotal`: a relation on total assignments, typed at bases.
* `Transition.IsExtension`: outputs restrict to their inputs.
* `Transition.randomAssign`: the transition `X ⟶ insert x X` leaving `x` free.

## Main statements

* `Transition.applyState_comp`: context change is functorial.
* `Transition.applyState_eq_biUnion`, `Transition.applyState_congr_world`: context change is
  distributive and extensional.
* `Transition.IsExtension.applyState_le`: an extension only adds information (Def. 27(ii)).

## Implementation notes

`Transition.copy` repackages a transition along equalities of its bases, as `Filter.copy` does,
so that no statement carries a cast.

## References

* [kamp-vangenabith-reyle-2011]
* [fernando-1992]
* [groenendijk-stokhof-1991]
* [heim-1982]
-/

@[expose] public section

namespace DynamicSemantics

variable {W V M : Type*} {X Y Z : Set V}

/-- A transition: a world-indexed relation from `X`-assignments to
`Y`-assignments. The `grow` field makes arrows context-extending —
bases never shrink. -/
@[ext] structure Transition (W M : Type*) {V : Type*} (X Y : Set V) where
  /-- The world-indexed relation between input and output assignments. -/
  rel : W → (X → M) → (Y → M) → Prop
  /-- Bases only grow along an update. -/
  grow : X ⊆ Y

namespace Transition

/-- The identity transition at `X`: equality of assignments. -/
def id (X : Set V) : Transition W M X X where
  rel _ e e' := e = e'
  grow := subset_rfl

@[simp] theorem rel_id {w : W} {e e' : X → M} :
    (id X : Transition W M X X).rel w e e' ↔ e = e' := Iff.rfl

/-- Sequencing: world-pointwise relational composition. -/
def comp (u : Transition W M X Y) (v : Transition W M Y Z) :
    Transition W M X Z where
  rel w := Relation.Comp (u.rel w) (v.rel w)
  grow := u.grow.trans v.grow

@[simp] theorem id_comp (u : Transition W M X Y) : (id X).comp u = u := by
  ext w e e'
  exact ⟨fun ⟨k, hek, hk⟩ => hek ▸ hk, fun h => ⟨e, rfl, h⟩⟩

@[simp] theorem comp_id (u : Transition W M X Y) : u.comp (id Y) = u := by
  ext w e e'
  exact ⟨fun ⟨k, hk, hke⟩ => hke ▸ hk, fun h => ⟨e', h, rfl⟩⟩

theorem comp_assoc (u : Transition W M X Y) (v : Transition W M Y Z)
    {Z' : Set V} (t : Transition W M Z Z') :
    (u.comp v).comp t = u.comp (v.comp t) := by
  ext w e e'
  exact ⟨fun ⟨k, ⟨j, hj, hjk⟩, hk⟩ => ⟨j, hj, k, hjk, hk⟩,
    fun ⟨j, hj, k, hjk, hk⟩ => ⟨k, ⟨j, hj, hjk⟩, hk⟩⟩

/-! ### Application to fibers -/

/-- Context change ([kamp-vangenabith-reyle-2011], Def. 24), on the
presheaf fibers: relate assignments through the transition, worlds
preserved. -/
def apply (u : Transition W M X Y)
    (T : Set (W × (X → M))) :
    Set (W × (Y → M)) :=
  {e' | ∃ e, (e'.1, e) ∈ T ∧ u.rel e'.1 e e'.2}

theorem mem_apply {u : Transition W M X Y}
    {T : Set (W × (X → M))} {w : W} {g : Y → M} :
    (w, g) ∈ u.apply T ↔ ∃ e, (w, e) ∈ T ∧ u.rel w e g := Iff.rfl

@[simp] theorem apply_id (T : Set (W × (X → M))) :
    (id X).apply T = T := by
  ext ⟨w, e⟩
  exact ⟨fun ⟨k, hk, hke⟩ => (show k = e from hke) ▸ hk, fun h => ⟨e, h, rfl⟩⟩

theorem apply_comp (u : Transition W M X Y) (v : Transition W M Y Z)
    (T : Set (W × (X → M))) :
    (u.comp v).apply T = v.apply (u.apply T) := by
  ext ⟨w, h⟩
  constructor
  · rintro ⟨e, he, k, hek, hkh⟩
    exact ⟨k, ⟨e, he, hek⟩, hkh⟩
  · rintro ⟨k, ⟨e, he, hek⟩, hkh⟩
    exact ⟨e, he, k, hek, hkh⟩

/-! ### Application to root states -/

section ApplyState

/-- Context change on root states ([kamp-vangenabith-reyle-2011],
Def. 24 — the regular CCP): points of the `X`-stratum step to points of
the `Y`-stratum through the transition, worlds preserved. Index-free:
both sides are plain states. -/
def applyState (u : Transition W M X Y) (I : State W V M) :
    State W V M :=
  {q | q.domain = Y ∧ ∃ p ∈ I, p.domain = X ∧
    p.world = q.world ∧
    ∃ (e : X → M) (e' : Y → M),
      (∀ v : X, p.assignment v.1 = ↑(e v)) ∧
      (∀ v : Y, q.assignment v.1 = ↑(e' v)) ∧
      u.rel q.world e e'}

theorem uniformAt_applyState (u : Transition W M X Y) (I : State W V M) :
    State.UniformAt Y (u.applyState I) := fun _ hq => hq.1

theorem applyState_mono (u : Transition W M X Y) {I I' : State W V M} (h : I ⊆ I') :
    u.applyState I ⊆ u.applyState I' :=
  fun _ ⟨hq, p, hp, hrest⟩ => ⟨hq, p, h hp, hrest⟩

/-- Context change is distributive: the image of a state is the union of the images of its
points. -/
theorem applyState_eq_biUnion (u : Transition W M X Y) (I : State W V M) :
    u.applyState I = ⋃ p ∈ I, u.applyState ({p} : Set (Possibility W V (Flat M))) := by
  refine Set.ext fun q => ⟨fun ⟨hq, p, hp, hrest⟩ => Set.mem_iUnion₂.mpr ⟨p, hp, hq, p, rfl, hrest⟩,
    fun h => ?_⟩
  obtain ⟨p, hp, hq, p', rfl, hrest⟩ := Set.mem_iUnion₂.mp h
  exact ⟨hq, p', hp, hrest⟩

/-- Context change is extensional: its image at a world depends only on the input's points at
that world. -/
theorem applyState_congr_world (u : Transition W M X Y) {I I' : State W V M} {w : W}
    (h : ∀ p : Possibility W V (Flat M), p.world = w → (p ∈ I ↔ p ∈ I'))
    {q : Possibility W V (Flat M)} (hq : q.world = w) :
    q ∈ u.applyState I ↔ q ∈ u.applyState I' := by
  constructor
  · rintro ⟨hY, p, hp, hpX, hw, hrest⟩
    exact ⟨hY, p, (h p (hw.trans hq)).mp hp, hpX, hw, hrest⟩
  · rintro ⟨hY, p, hp, hpX, hw, hrest⟩
    exact ⟨hY, p, (h p (hw.trans hq)).mpr hp, hpX, hw, hrest⟩

/-- The point of the `Y`-stratum carrying a given world and assignment. -/
private noncomputable def ptOf (Y : Set V) (w : W) (e : Y → M) : Possibility W V (Flat M) :=
  ((Possibility.domainEquiv Y).symm (w, e)).1

private theorem domain_ptOf (Y : Set V) (w : W) (e : Y → M) : (ptOf Y w e).domain = Y :=
  ((Possibility.domainEquiv Y).symm (w, e)).2

private theorem ptOf_assignment (Y : Set V) (w : W) (e : Y → M) (v : Y) :
    (ptOf Y w e).assignment v.1 = ↑(e v) := by
  simp [ptOf, Possibility.domainEquiv, v.2]

theorem applyState_comp (u : Transition W M X Y) (v : Transition W M Y Z)
    (I : State W V M) :
    (u.comp v).applyState I = v.applyState (u.applyState I) := by
  ext q
  constructor
  · rintro ⟨hq, p, hpI, hp, hw, e, e'', he, he'', k, huk, hkv⟩
    exact ⟨hq, ptOf Y q.world k, ⟨domain_ptOf .., p, hpI, hp, hw, e, k, he,
      ptOf_assignment Y q.world k, huk⟩, domain_ptOf .., rfl, k, e'',
      ptOf_assignment Y q.world k, he'', hkv⟩
  · rintro ⟨hq, m, ⟨hm, p, hpI, hp, hw, e, k, he, hk, huk⟩, -, hmw, k', e'',
      hk', he'', hvk⟩
    have hkk' : k = k' := funext fun x => Flat.coe_injective ((hk x).symm.trans (hk' x))
    refine ⟨hq, p, hpI, hp, hw.trans hmw, e, e'', he, he'', k, ?_, ?_⟩
    · rw [← hmw]
      exact huk
    · rw [hkk']
      exact hvk

theorem uniformEquiv_applyState (u : Transition W M X Y)
    {I : State W V M} (hI : State.UniformAt X I) :
    State.uniformEquiv Y ⟨u.applyState I, uniformAt_applyState u I⟩ =
      u.apply (State.uniformEquiv X ⟨I, hI⟩) := by
  ext f
  constructor
  · intro hf
    obtain ⟨-, p, hp, hpX, hw, e, f', hpe, hqf, hrel⟩ :
        ptOf Y f.1 f.2 ∈ u.applyState I := State.mem_uniformEquiv.mp hf
    have hf' : f' = f.2 := funext fun v =>
      Flat.coe_injective ((hqf v).symm.trans (ptOf_assignment Y f.1 f.2 v))
    subst hf'
    refine ⟨e, State.mem_uniformEquiv.mpr ?_, by exact hrel⟩
    show ptOf X f.1 e ∈ I
    have hpeq : ptOf X f.1 e = p := by
      have h : Possibility.domainEquiv X ⟨p, hpX⟩ = (f.1, e) :=
        Prod.ext hw (funext fun v ↦ Flat.coe_injective (by simp [Possibility.domainEquiv, hpe v]))
      rw [ptOf, ← h, Equiv.symm_apply_apply]
    rw [hpeq]; exact hp
  · rintro ⟨e, hmem, hrel⟩
    have hpI : ptOf X f.1 e ∈ I := State.mem_uniformEquiv.mp hmem
    refine State.mem_uniformEquiv.mpr ?_
    show ptOf Y f.1 f.2 ∈ u.applyState I
    exact ⟨domain_ptOf .., ptOf X f.1 e, hpI, domain_ptOf .., rfl, e,
      f.2, ptOf_assignment X f.1 e, ptOf_assignment Y f.1 f.2, by exact hrel⟩

end ApplyState

/-! ### Random assignment -/

/-- The random-assignment transition ([groenendijk-stokhof-1991]'s random
reset `k[x]g`, [heim-1982]'s indefinite widening): preserve the input off
`x`, leave the output free at `x` — the generating arrow
`X ⟶ insert x X` of context extension. -/
def randomAssign (X : Set V) (x : V) :
    Transition W M X (insert x X) where
  rel _ e e' := ∀ (v : V) (hv : v ∈ X), v ≠ x →
    e ⟨v, hv⟩ = e' ⟨v, Set.mem_insert_of_mem x hv⟩
  grow := Set.subset_insert x X

/-! ### Typing total-assignment relations

Frameworks state their clauses on total assignments (DPL's Definition 2,
DRT's verification). `ofTotal` types such a relation at contexts by
existential extension; the predecessor's `supported_left`/
`supported_right` fields return as *hypotheses* — `ReadsAt`/`WritesAt` —
carried by the framework's own congruence lemmas, and under them the
typing is faithful (`ofTotal_rel_restrict`) and functorial
(`ofTotal_comp`). -/

section OfTotal

variable {R S : W → (V → M) → (V → M) → Prop}

/-- The relation reads its input only at `X`. -/
def ReadsAt (X : Set V) (R : W → (V → M) → (V → M) → Prop) : Prop :=
  ∀ ⦃w f f' g⦄, Set.EqOn f f' X → (R w f g ↔ R w f' g)

/-- The relation constrains its output only at `Y`. -/
def WritesAt (Y : Set V) (R : W → (V → M) → (V → M) → Prop) : Prop :=
  ∀ ⦃w f g g'⦄, Set.EqOn g g' Y → (R w f g ↔ R w f g')

/-- Type a total-assignment relation at contexts, by existential
extension of the assignments. -/
def ofTotal (h : X ⊆ Y) (R : W → (V → M) → (V → M) → Prop) :
    Transition W M X Y where
  rel w e e' := ∃ f g : V → M, X.domRestrict f = e ∧
    Y.domRestrict g = e' ∧ R w f g
  grow := h

theorem ofTotal_rel_restrict {h : X ⊆ Y} (hR : ReadsAt X R)
    (hW : WritesAt Y R) {w : W} {f g : V → M} :
    (ofTotal h R).rel w (X.domRestrict f)
      (Y.domRestrict g) ↔ R w f g := by
  constructor
  · rintro ⟨f', g', hf', hg', hR'⟩
    rw [hR (Set.domRestrict_eq_domRestrict_iff.mp hf'),
      hW (Set.domRestrict_eq_domRestrict_iff.mp hg')] at hR'
    exact hR'
  · intro hfg
    exact ⟨f, g, rfl, rfl, hfg⟩

theorem ofTotal_comp {h₁ : X ⊆ Y} {h₂ : Y ⊆ Z} (hS : ReadsAt Y S) :
    (ofTotal h₁ R).comp (ofTotal h₂ S) =
      ofTotal (h₁.trans h₂) (fun w => Relation.Comp (R w) (S w)) := by
  ext w e e''
  constructor
  · rintro ⟨e', ⟨f, g₁, hf, hg₁, hR⟩, f₂, g, hf₂, hg, hS'⟩
    refine ⟨f, g, hf, hg, g₁, hR, ?_⟩
    rw [← hf₂] at hg₁
    exact (hS (Set.domRestrict_eq_domRestrict_iff.mp hg₁)).mpr hS'
  · rintro ⟨f, g, hf, hg, k, hR, hS'⟩
    exact ⟨Y.domRestrict k, ⟨f, k, hf, rfl, hR⟩,
      ⟨k, g, rfl, hg, hS'⟩⟩

end OfTotal

/-! ### Repackaging along base equalities

The substrate-safe form of `eqToHom` conjugation (mathlib's `Filter.copy`
pattern): composites whose indices differ by base identities — e.g.
`(X ∪ U₁) ∪ U₂` against `X ∪ (U₁ ∪ U₂)` — are equated through `copy`,
keeping cast-free statements everywhere below the category layer. -/

/-- Repackage a transition along equalities of its bases. -/
def copy (u : Transition W M X Y) {X' Y' : Set V} (hX : X = X')
    (hY : Y = Y') : Transition W M X' Y' :=
  hX ▸ hY ▸ u

@[simp] theorem copy_rfl (u : Transition W M X Y) : u.copy rfl rfl = u := rfl

@[simp] theorem copy_copy (u : Transition W M X Y)
    {X' Y' X'' Y'' : Set V} (hX : X = X') (hY : Y = Y')
    (hX' : X' = X'') (hY' : Y' = Y'') :
    (u.copy hX hY).copy hX' hY' = u.copy (hX.trans hX') (hY.trans hY') := by
  subst hX hY hX' hY'
  rfl

theorem ofTotal_congr {R R' : W → (V → M) → (V → M) → Prop}
    (h h' : X ⊆ Y) (hR : R = R') : ofTotal h R = ofTotal h' R' := by
  subst hR
  rfl

theorem ofTotal_copy {R : W → (V → M) → (V → M) → Prop} {h : X ⊆ Y}
    {Y' : Set V} (hY : Y = Y') :
    (ofTotal h R).copy rfl hY = ofTotal (hY ▸ h) R := by
  subst hY
  rfl

theorem copy_comp_copy (u : Transition W M X Y) (v : Transition W M Y Z)
    {X' Y' Z' : Set V} (hX : X = X') (hY : Y = Y') (hZ : Z = Z') :
    (u.copy hX hY).comp (v.copy hY hZ) = (u.comp v).copy hX hZ := by
  subst hX hY hZ
  rfl

@[simp] theorem apply_copy (u : Transition W M X Y) {X' Y' : Set V}
    (hX : X = X') (hY : Y = Y') (T : Set (W × ((↑X' : Set V) → M))) :
    (u.copy hX hY).apply T = (by subst hX hY; exact u.apply T) := by
  subst hX hY
  rfl

@[simp] theorem applyState_copy (u : Transition W M X Y)
    {X' Y' : Set V} (hX : X = X') (hY : Y = Y') (I : State W V M) :
    (u.copy hX hY).applyState I = u.applyState I := by
  subst hX hY
  rfl

/-! ### Information growth (Def. 27) -/

/-- A transition is an *extension* when outputs restrict to their inputs:
established referents persist, only new ones are assigned. -/
def IsExtension (u : Transition W M X Y) : Prop :=
  ∀ ⦃w e e'⦄, u.rel w e e' → e = Set.domRestrict₂ (π := fun _ => M) u.grow e'

theorem isExtension_id : (id X : Transition W M X X).IsExtension :=
  fun _ _ _ h => h

/-- Extensions compose. -/
theorem IsExtension.comp {u : Transition W M X Y} {v : Transition W M Y Z}
    (hu : u.IsExtension) (hv : v.IsExtension) : (u.comp v).IsExtension := by
  rintro w e e' ⟨k, hek, hke⟩
  rw [hu hek, hv hke]
  rfl

/-- Under an extension, every point of the image comes from an input point that it extends. -/
theorem IsExtension.exists_le_of_mem_applyState {u : Transition W M X Y} (hu : u.IsExtension)
    {I : State W V M} {q : Possibility W V (Flat M)} (hq : q ∈ u.applyState I) :
    ∃ p ∈ I, p.domain = X ∧ p ≤ q ∧ q ∈ u.applyState ({p} : Set (Possibility W V (Flat M))) := by
  obtain ⟨hY, p, hp, hpX, hw, e, e', he, he', hrel⟩ := hq
  refine ⟨p, hp, hpX, ⟨hw, fun x => ?_⟩, hY, p, rfl, hpX, hw, e, e', he, he', hrel⟩
  by_cases hx : x ∈ X
  · rw [he ⟨x, hx⟩, he' ⟨x, u.grow hx⟩, hu hrel]
    rfl
  · have hbot : p.assignment x = ⊥ := not_not.mp fun h => hx (hpX ▸ h)
    exact hbot ▸ bot_le

/-- An extension only adds information: its image of a state is at least as informative as the
state (Def. 27(ii)). -/
theorem IsExtension.applyState_le {u : Transition W M X Y} (hu : u.IsExtension)
    (I : State W V M) : u.applyState I ≤ I :=
  State.le_def.mpr fun _ hq =>
    let ⟨p, hp, _, hpq, _⟩ := hu.exists_le_of_mem_applyState hq
    ⟨p, hp, hpq⟩

/-- Under an extension, a point of the image extending a point of a state uniform at the base
comes from that point alone. -/
theorem IsExtension.mem_applyState_iff_of_le {u : Transition W M X Y} (hu : u.IsExtension)
    {I : State W V M} (hI : State.UniformAt X I) {p q : Possibility W V (Flat M)} (hp : p ∈ I)
    (hpq : p ≤ q) :
    q ∈ u.applyState I ↔ q ∈ u.applyState ({p} : Set (Possibility W V (Flat M))) := by
  refine ⟨fun hq => ?_, fun hq => u.applyState_mono (Set.singleton_subset_iff.mpr hp) hq⟩
  obtain ⟨p', -, hp'X, hp'q, hq'⟩ := hu.exists_le_of_mem_applyState hq
  rwa [((Possibility.le_iff_eq_restrict hp'X).mp hp'q).trans
    ((Possibility.le_iff_eq_restrict (hI p hp)).mp hpq).symm] at hq'

end Transition

end DynamicSemantics
