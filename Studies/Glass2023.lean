module

public import Studies.NadathurLauer2020

/-!
# Glass (2023)

Glass explains why *cause* favours undesirable complements. Over a deterministic causal model in
the sense of Halpern and Pearl, a value is locally sufficient for a downstream value when some
setting of the other variables guarantees it, as in Mackie's sufficient sets, and globally
sufficient when every setting does; necessity is the mirror image (`GloballySufficient`,
`LocallySufficient`, `GloballyNecessary`, `LocallyNecessary`). *C causes E*, asserted on a state
of knowledge, requires the effect to develop in every settlement of what is unknown (`Cause`), so
knowing the cause alone it is assertable exactly when the cause is globally sufficient
(`cause_update_bot_iff`), the asymmetry of the paper's Table 2. The Anna Karenina Principle gives
desired outcomes conjunctive models and undesired ones disjunctive models, so *C causes E* holds
in more states of knowledge when E is bad. Glass's *cause* asserts local sufficiency where Nadathur
and Lauer's asserts necessity, and the two diverge on their bus scenario
(`glass_nl_diverge_on_bus`).

## Implementation notes

* A background, the paper's "fixed setting of other variables", is an intervention holding some
  variables at values; "no matter what happens to any other variable" quantifies over every
  context and every such intervention leaving the effect open. What a state of knowledge keeps is
  read off the situation the intervention settles.
* The lightbulb of the paper's figures, on exactly when both switches are, is the conjunctive
  model for the light being on and the disjunctive model for its being off.
* The derivation of the Anna Karenina Principle from strategic model construction, the experiment
  supporting it (wanted outcomes drew "you had to do everything right" far more often than
  unwanted ones) and the corpus skew that motivates the paper stay in prose.

## References

* [glass-2023b]
* [nadathur-lauer-2020]
* [halpern-pearl-2005]
* [mackie-1965]
-/

@[expose] public section

namespace Glass2023

open CausalModel

section General

variable {U V : Type*} [DecidableEq V] (M : CausalModel U V fun _ ↦ Bool) [M.IsAcyclic]

/-! ### Local and global necessity and sufficiency -/

/-- `C = c` is globally sufficient for `E = e` when, in every context and under every background
leaving `E` open in which `C = c`, `E = e`. -/
def GloballySufficient (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  ∀ u (X : Finset V) (ξ : X → Bool), E ∉ X → ∀ hC : C ∈ X, ξ ⟨C, hC⟩ = c →
    (M.intervene X ξ).solve u E = e

/-- `C = c` is locally sufficient for `E = e` when, in some context and under some background
leaving `E` open in which `C = c`, `E = e`. -/
def LocallySufficient (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  ∃ (u : U) (X : Finset V) (ξ : X → Bool), E ∉ X ∧ ∃ hC : C ∈ X, ξ ⟨C, hC⟩ = c ∧
    (M.intervene X ξ).solve u E = e

/-- `C = c` is globally necessary for `E = e` when, without it, `E = e` fails in every context and
under every background leaving `E` open. -/
def GloballyNecessary (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  ∀ u (X : Finset V) (ξ : X → Bool), E ∉ X → ∀ hC : C ∈ X, ξ ⟨C, hC⟩ = !c →
    (M.intervene X ξ).solve u E = !e

/-- `C = c` is locally necessary for `E = e` when, without it, `E = e` fails in some context and
under some background leaving `E` open. -/
def LocallyNecessary (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  ∃ (u : U) (X : Finset V) (ξ : X → Bool), E ∉ X ∧ ∃ hC : C ∈ X, ξ ⟨C, hC⟩ = !c ∧
    (M.intervene X ξ).solve u E = !e

/-- *C causes E* is assertable on the state of knowledge `k` when the cause is known and the effect
holds in every context under every background that keeps what is known and leaves it open. -/
def Cause (k : V → Part Bool) (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  k C = Part.some c ∧ ∀ u (X : Finset V) (ξ : X → Bool),
    k ≤ Function.updateFinset ⊥ X (fun v ↦ Part.some (ξ v)) → E ∉ X →
      (M.intervene X ξ).solve u E = e

variable {M} {C E : V} {c e : Bool} {k : V → Part Bool}

theorem globallyNecessary_iff :
    GloballyNecessary M C c E e ↔ GloballySufficient M C (!c) E (!e) := Iff.rfl

theorem locallyNecessary_iff :
    LocallyNecessary M C c E e ↔ LocallySufficient M C (!c) E (!e) := Iff.rfl

-- A background keeping what `k` settles holds each settled variable at its known value.
private theorem mem_of_le_updateFinset {X : Finset V} {ξ : X → Bool}
    (hk : k ≤ Function.updateFinset ⊥ X fun v ↦ Part.some (ξ v)) {v : V} {a : Bool}
    (hv : k v = Part.some a) :
    ∃ h : v ∈ X, ξ ⟨v, h⟩ = a := by
  have := (Part.pi_le_iff.1 hk v (hv ▸ Part.some_dom a)).symm
  rw [hv] at this
  by_cases h : v ∈ X
  · exact ⟨h, by simpa [Function.updateFinset, h] using this⟩
  · simp [Function.updateFinset, h] at this

theorem Cause.of_globallySufficient (h : GloballySufficient M C c E e) (hk : k C = Part.some c) :
    Cause M k C c E e :=
  ⟨hk, fun u X ξ hkX hE ↦
    let ⟨hC, hξ⟩ := mem_of_le_updateFinset hkX hk
    h u X ξ hE hC hξ⟩

-- (22a)
theorem LocallySufficient.of_globally [Inhabited U] (hCE : C ≠ E)
    (h : GloballySufficient M C c E e) : LocallySufficient M C c E e :=
  ⟨default, {C}, uniqueElim c, by simpa using hCE.symm, Finset.mem_singleton_self C, rfl,
    h _ _ _ (by simpa using hCE.symm) (Finset.mem_singleton_self C) rfl⟩

-- (21a)
theorem LocallyNecessary.of_globally [Inhabited U] (hCE : C ≠ E)
    (h : GloballyNecessary M C c E e) : LocallyNecessary M C c E e :=
  LocallySufficient.of_globally hCE h

/-- Knowing the cause alone, *C causes E* is assertable exactly when the cause is globally
sufficient: the asymmetry of the paper's Table 2. -/
theorem cause_update_bot_iff :
    Cause M [C ← c] C c E e ↔ GloballySufficient M C c E e := by
  refine ⟨fun h u X ξ hE hC hξ ↦ h.2 u X ξ (Part.pi_le_iff.2 fun v hv ↦ ?_) hE,
    fun h ↦ Cause.of_globallySufficient h (Function.update_self ..)⟩
  rcases eq_or_ne v C with rfl | hvC
  · simp [Function.updateFinset, hC, hξ]
  · simp [hvC] at hv

end General

/-! ### The lightbulb (Figure 2, Tables 1 and 2)

Two switches and a light that is on exactly when both are: each switch being on is necessary but
insufficient for the light to be on, and each being off suffices for it to be off. -/

namespace Light

/-- The two switches and the light. -/
inductive V
  | S1
  | S2
  | L
  deriving DecidableEq, Fintype, Repr

/-- The light reads the two switches. -/
def edges : Finset (V × V) := {(.S1, .L), (.S2, .L)}

/-- The context settles the two switches. -/
structure Context where
  S1 : Bool
  S2 : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- The light is on exactly when both switches are. -/
def light : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn | .S1 => fun u _ ↦ u.S1 | .S2 => fun u _ ↦ u.S2 | .L => fun _ x ↦ x .S1 && x .S2

instance : DecidableRel light.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : light.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

theorem solve_L {X : Finset V} {ξ : X → Bool} (h : V.L ∉ X) (u : Context) :
    (light.intervene X ξ).solve u .L =
      ((light.intervene X ξ).solve u .S1 && (light.intervene X ξ).solve u .S2) :=
  solve_intervene_of_notMem h

theorem s1_off_globallySufficient : GloballySufficient light .S1 false .L false :=
  fun u _ _ hL hS1 hξ ↦ by rw [solve_L hL, solve_intervene_of_mem hS1, hξ, Bool.false_and]

theorem s1_on_globallyNecessary : GloballyNecessary light .S1 true .L true :=
  s1_off_globallySufficient

theorem s1_on_not_globallySufficient : ¬ GloballySufficient light .S1 true .L true :=
  fun h ↦ absurd (h ⟨true, false⟩ {.S1} (uniqueElim true) (by decide) (Finset.mem_singleton_self _)
    rfl) (by decide)

-- Table 2
theorem s1_off_causes_off_uncertain :
    Cause light [.S1 ← false] .S1 false .L false :=
  cause_update_bot_iff.2 s1_off_globallySufficient

-- Table 2
theorem not_s1_on_causes_on_uncertain :
    ¬ Cause light [.S1 ← true] .S1 true .L true :=
  fun h ↦ s1_on_not_globallySufficient (cause_update_bot_iff.1 h)

/-- The background with both switches on. -/
abbrev bothOn : V → Part Bool := [.S1 ← true, .S2 ← true]

-- Table 2
theorem s1_on_causes_on_certain : Cause light bothOn .S1 true .L true := by
  refine ⟨by decide, fun u X ξ hk hL ↦ ?_⟩
  obtain ⟨h1, h1'⟩ := mem_of_le_updateFinset hk (by decide : bothOn .S1 = Part.some true)
  obtain ⟨h2, h2'⟩ := mem_of_le_updateFinset hk (by decide : bothOn .S2 = Part.some true)
  rw [solve_L hL, solve_intervene_of_mem h1, solve_intervene_of_mem h2, h1', h2']
  rfl

end Light

/-! ### Against necessity-based *cause* -/

namespace Bus

open NadathurLauer2020.Bus

theorem glass_nl_diverge_on_bus :
    Cause busModel (Function.update s_b .Tr (Part.some true)) .Tr true .Bs true ∧
      ¬ NadathurLauer2020.Cause busModel s_b actual .Tr true .Bs true := by
  refine ⟨⟨by decide, fun u X ξ hk hBs ↦ ?_⟩, not_cause⟩
  obtain ⟨hRn, hRn'⟩ :=
    mem_of_le_updateFinset hk
      (by decide : Function.update s_b .Tr (Part.some true) .Rn = Part.some true)
  rw [solve_intervene_of_notMem hBs]
  show ((busModel.intervene X ξ).solve u .Rn || (busModel.intervene X ξ).solve u .Bk) = true
  rw [solve_intervene_of_mem hRn, hRn']
  rfl

end Bus

end Glass2023
