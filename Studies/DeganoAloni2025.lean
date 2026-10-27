module

public import Linglib.Logic.Team.Atoms
public import Studies.Haspelmath1997
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Degano and Aloni (2025): How to be (non-)specific?

This file formalizes Degano and Aloni's typology of marked indefinites. An indefinite
has three uses, specific known, specific unknown and non-specific, and a marked indefinite is
restricted to some of them: of the seven possible restrictions, six are attested and the one
covering the specific known and the non-specific use without the specific unknown is not. In
two-sorted team semantics a team of assignments to a world variable and an individual variable
is the speaker's information state, and the uses are constancy and variation conditions on the
individual variable: constancy across the team for specific known, constancy within a world
with variation across the team for specific unknown, and variation within a world for
non-specific. The three conditions partition the teams.

Each type requires a combination of atoms, and a team meets the requirement exactly when the
type's profile lists the use the team renders. A larger team renders a use further from the
specific end, constancy passing to subteams and variation to superteams, so the use is a
monotone map from the teams to the uses ordered specific known, specific unknown, non-specific,
and a requirement is the preimage of its profile. A requirement is therefore convex, a team
between two teams meeting it meeting it too, exactly when its profile is an interval of the
uses, and only the unattested profile is not. This is the paper's account of the order of
Haspelmath's map: the profiles contiguous on the map are those with convex requirements, and of
the orderings of the three uses only the map's and its reverse make every contiguous profile
convex. Five attested types require a single atom, closed under subteams or under superteams,
and the specific unknown type the conjunction of one of each, convex and closed under neither.

German *irgend-*, Russian *koe-* and *-nibud'*, Kannada *-oo*, Italian *qualche-* and Georgian
*-γac* instantiate the six attested types: the uses are the three specificity functions of
Haspelmath's map, the non-specific use being the irrealis function, and a series covers the uses
whose functions lie in the region the book draws for it.

## TODO

The paper extends the system with negation and modality to derive the licensing of non-specific
indefinites and treats epistemic indefinites at length; neither is formalized here.

## References

* [degano-aloni-2025]
* [haspelmath-1997]
-/

@[expose] public section

namespace DeganoAloni2025

open Team Indefinite Haspelmath1997

/-! ### Uses and types -/

/-- The seven types of indefinite are the restrictions a marked indefinite can impose on its
uses, the unmarked indefinite imposing none. -/
inductive IndefiniteType where
  | unmarked
  | specific
  | nonSpecific
  | epistemic
  | specificKnown
  | skPlusNS
  | specificUnknown
  deriving DecidableEq, Fintype, Repr

namespace IndefiniteType

/-- The uses a type is built for, the check marks of the table of marked indefinites. -/
def profile : IndefiniteType → Finset SpecificityFunction
  | .unmarked => {.specificKnown, .specificUnknown, .nonSpecific}
  | .specific => {.specificKnown, .specificUnknown}
  | .nonSpecific => {.nonSpecific}
  | .epistemic => {.specificUnknown, .nonSpecific}
  | .specificKnown => {.specificKnown}
  | .skPlusNS => {.specificKnown, .nonSpecific}
  | .specificUnknown => {.specificUnknown}

theorem profile_injective : Function.Injective profile := by decide

theorem exists_profile_eq {s : Finset SpecificityFunction} (hs : s.Nonempty) :
    ∃ t, profile t = s := by
  revert s; decide

theorem profile_nonempty (t : IndefiniteType) : t.profile.Nonempty := by
  cases t <;> decide

end IndefiniteType

/-! ### Conditions on teams -/

section Teams

variable {V E : Type*} {T : Finset (V → E)} {v x : V} {u u' : SpecificityFunction}
  {t : IndefiniteType}

/-- `Renders T v x u` says that the team `T` renders the use `u`, with `v` the world variable
and `x` the individual variable. The three uses are constancy, constancy within a world with
variation across the team, and variation within a world. -/
def Renders (T : Finset (V → E)) (v x : V) : SpecificityFunction → Prop
  | .specificKnown => Dep T ∅ x
  | .specificUnknown => Dep T {v} x ∧ Var T ∅ x
  | .nonSpecific => Var T {v} x

/-- The atoms a type requires. The unattested type requires one of two atoms, a Boolean
disjunction. -/
def IndefiniteType.Requires (T : Finset (V → E)) (v x : V) : IndefiniteType → Prop
  | .unmarked => True
  | .specific => Dep T {v} x
  | .nonSpecific => Var T {v} x
  | .epistemic => Var T ∅ x
  | .specificKnown => Dep T ∅ x
  | .skPlusNS => Dep T ∅ x ∨ Var T {v} x
  | .specificUnknown => Dep T {v} x ∧ Var T ∅ x

theorem not_var_of_dep_empty (h : Dep T ∅ x) : ¬ Var T {v} x :=
  (h.mono (Finset.empty_subset _)).not_var

theorem renders_unique (h : Renders T v x u) (h' : Renders T v x u') : u = u' := by
  cases u <;> cases u' <;> first
    | rfl
    | exact absurd h'.2 h.not_var
    | exact absurd h.2 h'.not_var
    | exact absurd h' (not_var_of_dep_empty h)
    | exact absurd h (not_var_of_dep_empty h')
    | exact absurd h' h.1.not_var
    | exact absurd h h'.1.not_var

theorem IndefiniteType.requires_iff :
    t.Requires T v x ↔ ∃ u ∈ t.profile, Renders T v x u := by
  have h : Dep T ∅ x → Dep T {v} x := Dep.mono (Finset.empty_subset _)
  cases t <;>
    simp only [Requires, profile, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
      exists_eq_left, Renders, ← not_dep] <;>
    tauto

/-! ### The use a team renders

The three uses partition the teams, so each team renders one, `use`. A larger team renders a use
further from the specific end, constancy passing to subteams and variation to superteams, and a
requirement is the set of teams rendering a use of the profile. -/

section Use

variable [DecidableEq E]

/-- A team renders the specific known use under constancy across the team, the specific unknown
use under constancy within a world alone, and the non-specific use otherwise. -/
def use (T : Finset (V → E)) (v x : V) : SpecificityFunction :=
  if Dep T ∅ x then .specificKnown else if Dep T {v} x then .specificUnknown else .nonSpecific

theorem renders_use (T : Finset (V → E)) (v x : V) : Renders T v x (use T v x) := by
  unfold use
  split_ifs with hc hv
  exacts [hc, ⟨hv, not_dep.1 hc⟩, not_dep.1 hv]

/-- A team renders exactly the use `use` assigns it. -/
theorem renders_iff : Renders T v x u ↔ use T v x = u :=
  ⟨renders_unique (renders_use T v x), (· ▸ renders_use T v x)⟩

/-- A requirement is the preimage of its profile under a monotone map from the teams to the uses. -/
theorem monotone_use (v x : V) : Monotone (use (E := E) · v x) := fun T T' hT ↦ by
  have hc (h : Dep T' ∅ x) : Dep T ∅ x := h.subset hT
  have hv (h : Dep T' {v} x) : Dep T {v} x := h.subset hT
  have hcv (h : Dep T' ∅ x) : Dep T {v} x := (h.mono (Finset.empty_subset _)).subset hT
  dsimp only [use]
  split_ifs <;> first | decide | simp_all

theorem IndefiniteType.requires_iff_use_mem : t.Requires T v x ↔ use T v x ∈ t.profile := by
  simp [requires_iff, renders_iff]

theorem IndefiniteType.setOf_requires :
    {T : Finset (V → E) | t.Requires T v x} = (use · v x) ⁻¹' t.profile :=
  Set.ext fun _ ↦ requires_iff_use_mem

end Use

/-! ### Witnesses

Over a domain with two individuals `a` and `b` each use has a team: one assignment for the
specific known use, the two constant assignments for the specific unknown use, and those two
with a variant of the first at the individual variable for the non-specific use. -/

theorem exists_subset_renders [Nontrivial E] (hvx : v ≠ x) :
    ∃ T₁ T₂ T₃ : Finset (V → E), T₁ ⊆ T₂ ∧ T₂ ⊆ T₃ ∧ Renders T₁ v x .specificKnown ∧
      Renders T₂ v x .specificUnknown ∧ Renders T₃ v x .nonSpecific := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨{fun _ ↦ a}, {fun _ ↦ a, fun _ ↦ b},
    {fun _ ↦ a, fun _ ↦ b, Function.update (fun _ ↦ a) x b}, by simp,
    Finset.insert_subset_insert _ (by simp), dep_singleton _,
    ⟨dep_iff.2 ?_, var_iff.2 ⟨fun _ ↦ a, by simp, fun _ ↦ b, by simp, by simp, hab⟩⟩,
    var_iff.2 ⟨fun _ ↦ a, by simp, Function.update (fun _ ↦ a) x b, by simp, by simp [hvx],
      by simpa using hab⟩⟩
  simp [hab, hab.symm]

theorem exists_monotone_renders [Nontrivial E] (hvx : v ≠ x) :
    ∃ g : SpecificityFunction → Finset (V → E), Monotone g ∧ ∀ u, Renders (g u) v x u := by
  obtain ⟨T₁, T₂, T₃, h₁₂, h₂₃, h₁, h₂, h₃⟩ := exists_subset_renders (E := E) hvx
  refine ⟨fun | .specificKnown => T₁ | .specificUnknown => T₂ | .nonSpecific => T₃, ?_, ?_⟩
  · rintro (_ | _ | _) (_ | _ | _) h <;>
      first
        | exact le_rfl
        | exact h₁₂
        | exact h₂₃
        | exact h₁₂.trans h₂₃
        | exact absurd h (by decide)
  · rintro (_ | _ | _) <;> assumption

/-! ### Convexity

A requirement is the preimage of its profile under `use`, which is monotone and has a monotone
section. So a requirement is convex, closed under subteams or closed under superteams exactly
when its profile is, and one requirement entails another exactly when its profile is included in
the other's. -/

/-- The uses of a type form an interval exactly when the type is not the unattested one. -/
theorem IndefiniteType.ordConnected_profile_iff :
    (t.profile : Set SpecificityFunction).OrdConnected ↔ t ≠ .skPlusNS := by
  cases t <;> decide

theorem IndefiniteType.ordConnected_requires
    (h : (t.profile : Set SpecificityFunction).OrdConnected) (v x : V) :
    {T : Finset (V → E) | t.Requires T v x}.OrdConnected := by
  classical
  rw [setOf_requires]
  exact h.preimage_mono (monotone_use v x)

private theorem exists_monotone_section [DecidableEq E] [Nontrivial E] (hvx : v ≠ x) :
    ∃ g : SpecificityFunction → Finset (V → E), Monotone g ∧
      ∀ s : Set SpecificityFunction, g ⁻¹' ((use · v x) ⁻¹' s) = s := by
  obtain ⟨g, hg, hgu⟩ := exists_monotone_renders (E := E) hvx
  exact ⟨g, hg, fun s ↦ by ext u; simp [renders_iff.1 (hgu u)]⟩

/-- A type's requirement is convex exactly when its uses form an interval, so convexity over teams
is convexity over the uses. -/
theorem IndefiniteType.ordConnected_requires_iff [Nontrivial E] (hvx : v ≠ x) :
    {T : Finset (V → E) | t.Requires T v x}.OrdConnected ↔
      (t.profile : Set SpecificityFunction).OrdConnected := by
  classical
  obtain ⟨g, hg, hs⟩ := exists_monotone_section (E := E) hvx
  rw [setOf_requires]
  exact ⟨fun h ↦ by simpa only [hs] using h.preimage_mono hg, (·.preimage_mono (monotone_use v x))⟩

theorem IndefiniteType.isLowerSet_requires_iff [Nontrivial E] (hvx : v ≠ x) :
    IsLowerSet {T : Finset (V → E) | t.Requires T v x} ↔
      IsLowerSet (t.profile : Set SpecificityFunction) := by
  classical
  obtain ⟨g, hg, hs⟩ := exists_monotone_section (E := E) hvx
  rw [setOf_requires]
  exact ⟨fun h ↦ by simpa only [hs] using h.preimage hg, (·.preimage (monotone_use v x))⟩

theorem IndefiniteType.isUpperSet_requires_iff [Nontrivial E] (hvx : v ≠ x) :
    IsUpperSet {T : Finset (V → E) | t.Requires T v x} ↔
      IsUpperSet (t.profile : Set SpecificityFunction) := by
  classical
  obtain ⟨g, hg, hs⟩ := exists_monotone_section (E := E) hvx
  rw [setOf_requires]
  exact ⟨fun h ↦ by simpa only [hs] using h.preimage hg, (·.preimage (monotone_use v x))⟩

theorem IndefiniteType.setOf_requires_subset_iff [Nontrivial E] (hvx : v ≠ x)
    {t t' : IndefiniteType} :
    {T : Finset (V → E) | t.Requires T v x} ⊆ {T | t'.Requires T v x} ↔ t.profile ⊆ t'.profile := by
  classical
  obtain ⟨g, -, hs⟩ := exists_monotone_section (E := E) hvx
  rw [setOf_requires, setOf_requires, ← Finset.coe_subset]
  exact ⟨fun h ↦ by simpa only [hs] using Set.preimage_mono (f := g) h, Set.preimage_mono⟩

theorem IndefiniteType.not_ordConnected_skPlusNS [Nontrivial E] (hvx : v ≠ x) :
    ¬ {T : Finset (V → E) | skPlusNS.Requires T v x}.OrdConnected :=
  mt (ordConnected_requires_iff hvx).1 (by decide)

/-! ### Monotonicity

A constancy atom is closed under subteams and a variation atom under superteams. The specific
unknown requirement, the conjunction of one of each, is convex and closed under neither, since
its use lies strictly between the other two. -/

theorem IndefiniteType.not_isLowerSet_specificUnknown [Nontrivial E] (hvx : v ≠ x) :
    ¬ IsLowerSet {T : Finset (V → E) | specificUnknown.Requires T v x} :=
  mt (isLowerSet_requires_iff hvx).1 fun h ↦ by
    simpa [profile] using h (show SpecificityFunction.specificKnown ≤ .specificUnknown by decide)
      (by simp [profile])

theorem IndefiniteType.not_isUpperSet_specificUnknown [Nontrivial E] (hvx : v ≠ x) :
    ¬ IsUpperSet {T : Finset (V → E) | specificUnknown.Requires T v x} :=
  mt (isUpperSet_requires_iff hvx).1 fun h ↦ by
    simpa [profile] using h (show SpecificityFunction.specificUnknown ≤ .nonSpecific by decide)
      (by simp [profile])

end Teams

/-! ### The types on the map -/

/-- A series instantiates the type whose profile is exactly the uses it covers; by
`IndefiniteType.profile_injective` there is at most one. A series covering none of the three uses
instantiates no type. -/
def Instantiates (s : Series) (t : IndefiniteType) : Prop :=
  specificityFunctions s.functions = t.profile

instance (s : Series) (t : IndefiniteType) : Decidable (Instantiates s t) :=
  inferInstanceAs (Decidable (specificityFunctions s.functions = t.profile))

theorem connected_profile_iff {t : IndefiniteType} :
    (implicationalMap.induce ↑(t.profile.image SpecificityFunction.toFunction)).Connected ↔
      (t.profile : Set SpecificityFunction).OrdConnected := by
  cases t <;> decide

/-- A type's requirement is convex exactly when its uses form a connected region of the map, so
convexity over teams is contiguity on the map. -/
theorem ordConnected_requires_iff_connected {V E : Type*} [Nontrivial E] {v x : V} (hvx : v ≠ x)
    {t : IndefiniteType} :
    {T : Finset (V → E) | t.Requires T v x}.OrdConnected ↔
      (implicationalMap.induce ↑(t.profile.image SpecificityFunction.toFunction)).Connected :=
  (IndefiniteType.ordConnected_requires_iff hvx).trans connected_profile_iff.symm

/-- Whether a set of positions on a line of three is contiguous. -/
@[instance_reducible]
private def decidableOrdConnectedFin (s : Finset (Fin 3)) :
    Decidable (s : Set (Fin 3)).OrdConnected :=
  decidable_of_iff (∀ a ∈ s, ∀ b ∈ s, ∀ c, a ≤ c → c ≤ b → c ∈ s)
    ⟨fun h ↦ ⟨fun _ ha _ hb _ hc ↦ h _ ha _ hb _ hc.1 hc.2⟩,
      fun h _ ha _ hb _ h₁ h₂ ↦ h.out ha hb ⟨h₁, h₂⟩⟩

attribute [local instance] decidableOrdConnectedFin in
/-- The map orders the uses as convexity requires. On an ordering `σ` of the three uses, every
type whose uses are contiguous has a convex requirement exactly when `σ` is the map's order or its
reverse; on any other ordering the specific known and the non-specific use are contiguous, and
their disjunction is not convex. -/
theorem forall_ordConnected_requires_iff {V E : Type*} [Nontrivial E] {v x : V} (hvx : v ≠ x)
    (σ : SpecificityFunction ≃ Fin 3) :
    (∀ t : IndefiniteType, (σ '' t.profile).OrdConnected →
      {T : Finset (V → E) | t.Requires T v x}.OrdConnected) ↔ Monotone σ ∨ Antitone σ := by
  simp only [IndefiniteType.ordConnected_requires_iff hvx, ← Finset.coe_image]
  revert σ
  decide

/-- Every series of the sample covering one of the three uses instantiates a type with a convex
requirement, since it covers a connected region of the map. -/
theorem sample_instantiates_ordConnected {V E : Type*} (v x : V) :
    ∀ p ∈ Haspelmath1997.sample, ∀ s ∈ p, (specificityFunctions s.functions).Nonempty →
      ∃ t, Instantiates s t ∧ {T : Finset (V → E) | t.Requires T v x}.OrdConnected :=
  fun p hp s hs hne ↦
    let ⟨t, ht⟩ := IndefiniteType.exists_profile_eq hne
    ⟨t, ht.symm, IndefiniteType.ordConnected_requires
      (ht ▸ ordConnected_specificityFunctions (Haspelmath1997.sample_connected p hp s hs)) v x⟩

theorem examples :
    (∃ s ∈ Haspelmath1997.italian,
        s.toSeries = Italian.Indefinites.qualcheSeries ∧ Instantiates s .unmarked) ∧
      (∃ s ∈ Haspelmath1997.georgian,
        s.toSeries = Georgian.Indefinites.γacSeries ∧ Instantiates s .specific) ∧
      (∃ s ∈ Haspelmath1997.russian,
        s.toSeries = Russian.Indefinites.nibudSeries ∧ Instantiates s .nonSpecific) ∧
      (∃ s ∈ Haspelmath1997.german,
        s.toSeries = German.Indefinites.irgendSeries ∧ Instantiates s .epistemic) ∧
      (∃ s ∈ Haspelmath1997.russian,
        s.toSeries = Russian.Indefinites.koeSeries ∧ Instantiates s .specificKnown) ∧
      ∃ s ∈ Haspelmath1997.kannada,
        s.toSeries = Kannada.Indefinites.ooSeries ∧ Instantiates s .specificUnknown := by
  decide

end DeganoAloni2025
