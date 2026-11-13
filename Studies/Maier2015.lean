module

public import Linglib.Semantics.Dynamic.DRT.Accessibility
public import Linglib.Data.Examples.Maier2015
public import Mathlib.Data.Fin.VecNotation
public import Linglib.Data.Examples.Readers

/-!
# Maier (2015): Parasitic Attitudes

This file formalizes Maier's solution to Karttunen's attitude-projection puzzle, *Bill believed Fred
had been beating his wife and he hoped Fred would stop*, which does not presuppose for the speaker
that Fred was beating his wife. An agent's mental state is one discourse representation, a belief
layer with labelled non-doxastic compartments embedded in it (`MentalState`, `MentalState.flatten`),
so a referent introduced in the belief layer is accessible from every compartment while a
compartment's referents are visible nowhere else (`accessible_belief_of_compartment`,
`not_accessible_of_belief`): the non-doxastic attitudes are parasitic on belief. A sequence of
ascriptions to one agent merges into one description (`MentalState.merge`), after which a
presupposition triggered in a desire compartment binds, in the manner of van der Sandt, to the
believed event rather than projecting (`MentalState.bind`, `presup_binds_after_merge`,
`presup_resolved_after_binding`), whereas one triggered in the belief layer after a desire finds no
antecedent there and projects. That asymmetry is the paper's data: in the sequences of
`Data/Examples/Maier2015` the presupposition is filtered exactly when the doxastic ascription comes
first (`filtering_iff_doxastic_first`).

## Implementation notes

The compartment labels are structural, not intensional operators, so parasitism is the
standard accessibility of the DRS core in `Semantics/Dynamic/DRT`, a compartment being a
subordinate box; the core's negation is the subordination device, its truth conditions
playing no role. The general accessibility lemmas assume the belief layer and the
compartments hold atomic conditions, as every description in the paper does.

## References

* [maier-2015]
* [karttunen-1973]
* [van-der-sandt-1992]
-/

@[expose] public section

open FirstOrder DRT

namespace Maier2015

/-! ### The DRS language of the Karttunen example (§5.3) -/

/-- The example's relations are `sue` and `jane`, `husband(h, j)`, the event
`cheat(e, j, h)`, and `stop(j, e')`. -/
inductive MaierRel : ℕ → Type
  | sue : MaierRel 1
  | jane : MaierRel 1
  | husband : MaierRel 2
  | cheat : MaierRel 3
  | stop : MaierRel 2

/-- The first-order language of the example. -/
def maierLang : Language := ⟨fun _ ↦ Empty, MaierRel⟩

/-- Conditions over `maierLang` with `ℕ` discourse referents. -/
abbrev MCond := Condition maierLang ℕ

/-! ### Mental-state descriptions (§3.1) -/

/-- The attitude modes of the non-doxastic compartments, desire, imagination and intention. -/
inductive AttMode where
  | des
  | imgn
  | int
  deriving DecidableEq, Repr, BEq

/-- A non-doxastic compartment has its own referents and conditions under an attitude mode. -/
structure Compartment where
  mode : AttMode
  drefs : List ℕ
  conds : List MCond

/-- A mental-state description (32) is a belief layer with embedded compartments. -/
structure MentalState where
  beliefDrefs : List ℕ
  beliefConds : List MCond
  compartments : List Compartment

/-- A compartment as a subordinate box. -/
def Compartment.box (c : Compartment) : MCond := .neg (.mk c.drefs.toFinset c.conds)

/-- A description flattens to the belief box with each compartment a subordinate box, so
that accessibility runs from a compartment up to the belief layer and not back. -/
def MentalState.flatten (K : MentalState) : DRS maierLang ℕ :=
  .mk K.beliefDrefs.toFinset (K.beliefConds ++ K.compartments.map Compartment.box)

/-! ### Parasitism as accessibility -/

private theorem not_mem_subordinates_of_atomic {c : MCond} (h : c.IsAtomic)
    (s : List (DRS maierLang ℕ)) : s ∉ c.subordinates := by
  simp [Condition.subordinates_eq_nil_iff.2 h]

theorem not_accessible_of_belief (K : MentalState) (hb : ∀ c ∈ K.beliefConds, c.IsAtomic)
    (hcs : ∀ c ∈ K.compartments, ∀ cd ∈ c.conds, cd.IsAtomic) {x y : ℕ}
    (hxc : ∀ c ∈ K.compartments, x ∉ c.drefs) (hy : y ∉ K.beliefDrefs) :
    ¬ DRS.Accessible K.flatten x y := by
  rw [DRS.accessible_iff_exists_occurrence]
  rintro ⟨K', bs, hp, hx, hyp⟩
  rcases hp.cases_head with h | ⟨q, hq, hqp⟩
  · obtain ⟨rfl, rfl⟩ := List.cons.inj h
    simp [MentalState.flatten, hy] at hyp
  · obtain @⟨_, K₁, _, s, d, hd, hsub⟩ := hq
    rcases List.mem_append.1 hd with hd | hd
    · exact not_mem_subordinates_of_atomic (hb _ hd) _ hsub
    · obtain ⟨c, hcK, rfl⟩ := List.mem_map.1 hd
      obtain ⟨rfl, rfl⟩ : K₁ = .mk c.drefs.toFinset c.conds ∧ s = [] := by
        simpa [Compartment.box] using hsub
      rcases hqp.cases_head with h | ⟨r, hr, -⟩
      · obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact hxc c hcK (by simpa using hx)
      · obtain @⟨_, _, _, _, e, he, hsub'⟩ := hr
        exact not_mem_subordinates_of_atomic (hcs c hcK e he) _ hsub'

/-- A compartment sees the belief layer. Where a compartment declares a referent every belief
referent is accessible, parasitism in the paper's sense (§3.1). -/
theorem accessible_belief_of_compartment (K : MentalState) {x y : ℕ} (hx : x ∈ K.beliefDrefs)
    (hyc : ∃ c ∈ K.compartments, y ∈ c.drefs) : DRS.Accessible K.flatten y x := by
  obtain ⟨c, hc, hy⟩ := hyc
  have hsub : DirectlySubordinate (.mk c.drefs.toFinset c.conds) K.flatten :=
    ⟨c.box, List.mem_append_right _ (List.mem_map_of_mem hc), [], by simp [Compartment.box]⟩
  exact ⟨_, _, .subordinate .refl (.single hsub), by simp [MentalState.flatten, hx],
    by simpa using hy⟩

/-! ### Attitude merge (58) and presupposition binding -/

/-- Append one compartment's content to another of the same mode. -/
def Compartment.append (c c' : Compartment) : Compartment :=
  { mode := c.mode, drefs := c.drefs ++ c'.drefs, conds := c.conds ++ c'.conds }

/-- Merge two compartment lists by attitude mode. -/
def mergeCompartments (cs cs' : List Compartment) : List Compartment :=
  cs'.foldl (fun cur c' ↦
    if cur.any (·.mode == c'.mode) then
      cur.map (fun c ↦ if c.mode == c'.mode then c.append c' else c)
    else cur ++ [c']) cs

/-- Attitude merge (58) makes two partial descriptions of one agent's state one, merging the
belief layers and combining like-mode compartments. -/
def MentalState.merge (K K' : MentalState) : MentalState :=
  { beliefDrefs := K.beliefDrefs ++ K'.beliefDrefs
    beliefConds := K.beliefConds ++ K'.beliefConds
    compartments := mergeCompartments K.compartments K'.compartments }

/-- `K.bind presup antecedent` resolves a presupposition by binding its referent to an
accessible antecedent in the manner of [van-der-sandt-1992], dropping the presupposed referent
and renaming it throughout. -/
def MentalState.bind (presup antecedent : ℕ) (K : MentalState) : MentalState :=
  { beliefDrefs := K.beliefDrefs.filter (· != presup)
    beliefConds := K.beliefConds.map (Condition.map fun d ↦ if d = presup then antecedent else d)
    compartments := K.compartments.map fun c ↦
      { mode := c.mode
        drefs := c.drefs.filter (· != presup)
        conds := c.conds.map (Condition.map fun d ↦ if d = presup then antecedent else d) } }

/-! ### Karttunen's puzzle (§5.3)

*Sue thinks that Jane has been cheating on her husband. She hopes that Jane will stop
cheating on him.* Referents: Sue 10, Jane 11, the husband 12, the believed cheating event 20,
and the cheating event 21 presupposed by *stop*. -/

/-- After the first sentence Sue believes there is a cheating event (59). -/
def sueBelief : MentalState :=
  { beliefDrefs := [10, 11, 12, 20]
    beliefConds := [.atom ⟨.sue, ![10]⟩, .atom ⟨.jane, ![11]⟩, .atom ⟨.husband, ![12, 11]⟩,
                    .atom ⟨.cheat, ![20, 11, 12]⟩]
    compartments := [] }

/-- The second sentence on its own gives a desire compartment with *stop* and the presupposed
event, with no antecedent in its belief layer. -/
def sueHope : MentalState :=
  { beliefDrefs := []
    beliefConds := []
    compartments := [{ mode := .des, drefs := [21],
                       conds := [.atom ⟨.stop, ![11, 21]⟩, .atom ⟨.cheat, ![21, 11, 12]⟩] }] }

/-- The two ascriptions merged (59). -/
def sueMerged : MentalState := sueBelief.merge sueHope

/-- The merged description after binding the presupposed event to the believed one (60). -/
def sueBound : MentalState := sueMerged.bind 21 20

theorem believed_event_absent_before_merge : 20 ∉ DRS.varFinset sueHope.flatten := by
  decide

theorem presup_binds_after_merge : DRS.Accessible sueMerged.flatten 21 20 :=
  accessible_belief_of_compartment sueMerged (by decide) (by decide)

theorem parasitic_asymmetry : ¬ DRS.Accessible sueMerged.flatten 20 21 :=
  not_accessible_of_belief sueMerged (by decide) (by decide) (by decide) (by decide)

/-- After binding the presupposed referent is gone and the believed event remains, so the
presupposition is resolved by binding, neither accommodated nor projected (60). -/
theorem presup_resolved_after_binding :
    21 ∉ DRS.varFinset sueBound.flatten ∧ 20 ∈ DRS.varFinset sueBound.flatten := by
  decide

/-! ### The data -/

theorem filtering_iff_doxastic_first :
    ∀ e ∈ Examples.all, e.judgment = .acceptable ↔ e.feature? "order" = some "doxasticFirst" := by
  decide

end Maier2015
