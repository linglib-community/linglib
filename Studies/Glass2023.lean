module

public import Studies.NadathurLauer2020
public import Linglib.Semantics.Causation.CausalModel.Guarantee

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

* Global sufficiency and *cause* are `CausalModel.Guarantees`, at the state that knows the cause
  alone and at the speaker's state of knowledge.
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
  M.Guarantees [C ← c] E e

/-- `C = c` is locally sufficient for `E = e` when, in some context and under some background
leaving `E` open in which `C = c`, `E = e`. -/
def LocallySufficient (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  ∃ (u : U) (i : V → Part Bool) (_ : ∀ v, Decidable (i v).Dom), i E = ⊥ ∧ i C = Part.some c ∧
    (M.intervene i).solve u E = e

/-- `C = c` is globally necessary for `E = e` when, without it, `E = e` fails in every context and
under every background leaving `E` open. -/
def GloballyNecessary (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  M.Guarantees [C ← !c] E (!e)

/-- `C = c` is locally necessary for `E = e` when, without it, `E = e` fails in some context and
under some background leaving `E` open. -/
def LocallyNecessary (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  ∃ (u : U) (i : V → Part Bool) (_ : ∀ v, Decidable (i v).Dom), i E = ⊥ ∧ i C = Part.some (!c) ∧
    (M.intervene i).solve u E = !e

/-- *C causes E* is assertable on the state of knowledge `k` when the cause is known and the effect
holds in every context under every background that keeps what is known and leaves it open. -/
def Cause (k : V → Part Bool) (C : V) (c : Bool) (E : V) (e : Bool) : Prop :=
  k C = Part.some c ∧ M.Guarantees k E e

variable {M} {C E : V} {c e : Bool} {k : V → Part Bool}

theorem globallyNecessary_iff :
    GloballyNecessary M C c E e ↔ GloballySufficient M C (!c) E (!e) := Iff.rfl

omit [DecidableEq V] in
theorem locallyNecessary_iff :
    LocallyNecessary M C c E e ↔ LocallySufficient M C (!c) E (!e) := Iff.rfl

theorem Cause.of_globallySufficient (hCE : C ≠ E) (h : GloballySufficient M C c E e)
    (hk : k C = Part.some c) (hE : k E = ⊥) : Cause M k C c E e :=
  ⟨hk, fun i _ u hki hiE ↦
    (guarantees_single_iff hCE).1 h i u (Part.eq_some_of_pi_le hki hk) (hiE.trans hE)⟩

-- (22a)
theorem LocallySufficient.of_globally [Inhabited U] (hCE : C ≠ E)
    (h : GloballySufficient M C c E e) : LocallySufficient M C c E e :=
  ⟨default, [C ← c], inferInstance, Function.update_of_ne hCE.symm .., Function.update_self ..,
    (guarantees_single_iff hCE).1 h _ _ (Function.update_self ..)
      (Function.update_of_ne hCE.symm ..)⟩

-- (21a)
theorem LocallyNecessary.of_globally [Inhabited U] (hCE : C ≠ E)
    (h : GloballyNecessary M C c E e) : LocallyNecessary M C c E e :=
  LocallySufficient.of_globally hCE h

/-- Knowing the cause alone, *C causes E* is assertable exactly when the cause is globally
sufficient: the asymmetry of the paper's Table 2. -/
theorem cause_update_bot_iff :
    Cause M [C ← c] C c E e ↔ GloballySufficient M C c E e :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨Function.update_self .., h⟩⟩

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

theorem solve_L {i : V → Part Bool} [∀ v, Decidable (i v).Dom] (h : i .L = ⊥) (u : Context) :
    (light.intervene i).solve u .L =
      ((light.intervene i).solve u .S1 && (light.intervene i).solve u .S2) :=
  solve_intervene_of_eq_bot h

theorem s1_off_globallySufficient : GloballySufficient light .S1 false .L false :=
  (guarantees_single_iff (by decide)).2 fun i _ u hS1 hL ↦ by
    rw [solve_L hL, solve_intervene_of_eq_some hS1, Bool.false_and]

theorem s1_on_globallyNecessary : GloballyNecessary light .S1 true .L true :=
  s1_off_globallySufficient

theorem s1_on_not_globallySufficient : ¬ GloballySufficient light .S1 true .L true :=
  fun h ↦ absurd ((guarantees_single_iff (by decide)).1 h [.S1 ← true] ⟨true, false⟩
    (Function.update_self ..) (Function.update_of_ne (by decide) ..)) (by decide)

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
  refine ⟨by decide, fun i _ u hk hL ↦ ?_⟩
  have h1 := Part.eq_some_of_pi_le hk (by decide : bothOn .S1 = Part.some true)
  have h2 := Part.eq_some_of_pi_le hk (by decide : bothOn .S2 = Part.some true)
  rw [solve_L (hL.trans (by decide)), solve_intervene_of_eq_some h1,
    solve_intervene_of_eq_some h2]
  rfl

end Light

/-! ### Against necessity-based *cause* -/

namespace Bus

open NadathurLauer2020.Bus

theorem glass_nl_diverge_on_bus :
    Cause busModel (Function.update s_b .Tr (Part.some true)) .Tr true .Bs true ∧
      ¬ NadathurLauer2020.Cause busModel s_b actual .Tr true .Bs true := by
  refine ⟨⟨by decide, fun i _ u hk hBs ↦ ?_⟩, not_cause⟩
  have hRn := Part.eq_some_of_pi_le hk
    (by decide : Function.update s_b .Tr (Part.some true) .Rn = Part.some true)
  rw [solve_intervene_of_eq_bot (hBs.trans (by decide))]
  show ((busModel.intervene i).solve u .Rn || (busModel.intervene i).solve u .Bk) = true
  rw [solve_intervene_of_eq_some hRn]
  rfl

end Bus

end Glass2023
