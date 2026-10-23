module

public import Linglib.Core.Computability.Bud
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole

/-!
# Theta theory as a coloring algorithm

Marcolli and Larson implement theta theory in the mathematical model of Minimalism as a coloring
algorithm: structures freely formed by Merge are filtered by membership in the language of a bud
generating system whose colors are theta grids, tuples of giver- or receiver-marked roles, and
whose generators are the local theta-discharge configurations. A grid injected at a predicate's
leaf propagates up the tree like a conserved quantity: at each generator one receiver peels off
to the sister position, and the residue continues toward the maximal projection.

## Main definitions

* `PolarizedRole`, `Color`: giver- and receiver-marked roles, and the colors, which are bare grids
  (nonterminal; the empty grid marks a non-theta position), lexically anchored grids (terminal),
  and the empty-tree marker.
* `IsGen`, `ThetaLocal`, `system`: the generator shapes, the cherries they license, and the
  complete theta bud system.
* `comb`: the bare theta combs, a complete grid discharged one role per vertex.
* `SatisfiesCriterion`: the theta criterion on a colored operation.

## Main statements

* `IsGen.conservation`: each generator conserves theta roles.
* `ThetaLocal.eq_nontheta`: movement lands only in non-theta positions.
* `comb_derivable`: the bare combs are derivable in the complete system.
* `derives_soleReceiver`: in a movement-free derivable structure with a sole-receiver root, every
  position receives at most one role.

## Implementation notes

The trees are planar, so each generator shape licenses its children in either order, and the
theta criterion compares received roles with the head's grid as multisets.

## References

* [marcolli-larson-2025]
* [marcolli-chomsky-berwick-2025]
* [giraudo-2019]
-/

@[expose] public section

open ArgumentStructure

namespace Minimalist.Theta

/-- Whether a role occurrence gives or receives, [marcolli-larson-2025]'s marks `θ↑` and `θ↓`. -/
inductive Polarity where
  | giver
  | receiver
  deriving DecidableEq, Repr

/-- A theta role marked as given or received. -/
structure PolarizedRole where
  role : ThetaRole
  polarity : Polarity
  deriving DecidableEq, Repr

/-- The giver occurrence `θ↑`. -/
def PolarizedRole.up (ρ : ThetaRole) : PolarizedRole := ⟨ρ, .giver⟩

/-- The receiver occurrence `θ↓`. -/
def PolarizedRole.down (ρ : ThetaRole) : PolarizedRole := ⟨ρ, .receiver⟩

/-- A grid of giver occurrences, the undischarged residue a predicate carries. -/
def upGrid (g : List ThetaRole) : List PolarizedRole := g.map .up

@[simp] theorem upGrid_nil : upGrid [] = [] := rfl

@[simp] theorem down_notMem_upGrid {ρ : ThetaRole} {g : List ThetaRole} :
    PolarizedRole.down ρ ∉ upGrid g := by
  simp [upGrid, PolarizedRole.up, PolarizedRole.down]

@[simp] theorem upGrid_append (g h : List ThetaRole) :
    upGrid (g ++ h) = upGrid g ++ upGrid h := List.map_append ..

variable {L : Type*}

/-- A color is a bare grid (nonterminal, the empty grid being the non-theta marker `θ0`), a
lexically anchored grid (terminal), or the empty-tree marker `(1, θ0)`. -/
inductive Color (L : Type*) where
  | free (g : List PolarizedRole)
  | lex (item : L) (g : List PolarizedRole)
  | emptyTree
  deriving DecidableEq, Repr

/-- The non-theta marker `θ0`, the empty grid. -/
abbrev Color.nontheta : Color L := .free []

/-- The terminal colors are the lexically anchored grids and the empty-tree marker. -/
def Color.IsTerminal : Color L → Prop
  | .free _ => False
  | .lex _ _ => True
  | .emptyTree => True

@[simp] theorem Color.isTerminal_free {g : List PolarizedRole} :
    ¬ (Color.free g : Color L).IsTerminal := id

/-- The grid a color carries, if any; lexical anchoring is transparent to theta structure. -/
def Color.grid? : Color L → Option (List PolarizedRole)
  | .free g => some g
  | .lex _ g => some g
  | .emptyTree => none

/-- The color carries exactly the grid `g`. -/
def Color.Matches (c : Color L) (g : List PolarizedRole) : Prop :=
  c.grid? = some g

@[simp] theorem Color.matches_free {g h : List PolarizedRole} :
    (Color.free g : Color L).Matches h ↔ g = h := by
  simp [Color.Matches, Color.grid?]

@[simp] theorem Color.matches_lex {α : L} {g h : List PolarizedRole} :
    (Color.lex α g).Matches h ↔ g = h := by
  simp [Color.Matches, Color.grid?]

@[simp] theorem Color.not_matches_emptyTree {g : List PolarizedRole} :
    ¬ (Color.emptyTree : Color L).Matches g := by
  simp [Color.Matches, Color.grid?]

section Rules

variable (hier : ThetaRole → ThetaRole → Prop)

/-- The generator shapes of the theta bud system, as a relation between the root grid and the
two children's colors. The four cases are [marcolli-larson-2025]'s complete-system generators:

* `close`: the external role discharges and the maximal projection is recolored arbitrarily;
* `discharge`: one internal role, next in the hierarchy, peels off to the sister while the
  residue propagates;
* `adjunct`: a non-theta position attaches without disturbing the color;
* `move`: a movement landing site, the empty-tree marker attached under a non-theta root. -/
inductive IsGen : List PolarizedRole → Color L → Color L → Prop
  | close (g₀ : List PolarizedRole) (ρE : ThetaRole) {a b : Color L}
      (ha : a.Matches [.down ρE]) (hb : b.Matches [.up ρE]) :
      IsGen g₀ a b
  | discharge (g : List ThetaRole) (ρ : ThetaRole) (hg : g ≠ [])
      (hchain : ((g ++ [ρ]).tail).IsChain hier) {a b : Color L}
      (ha : a.Matches [.down ρ]) (hb : b.Matches (upGrid (g ++ [ρ]))) :
      IsGen (upGrid g) a b
  | adjunct (g₀ : List PolarizedRole) : IsGen g₀ (.free g₀) .nontheta
  | move (c' : Color L) (hc' : c' ≠ .emptyTree) : IsGen [] c' .emptyTree

/-- The cherries of the theta bud system: a bare grid at the root over children forming a
generator in either order, [marcolli-larson-2025]'s compatibility relation for colored Merge. -/
def ThetaLocal (c a b : Color L) : Prop :=
  ∃ g₀, c = .free g₀ ∧ (IsGen hier g₀ a b ∨ IsGen hier g₀ b a)

/-- The complete theta bud system: the theta cherries, with the bare grids initial and the
anchored grids and the empty-tree marker terminal. -/
abbrev system : Bud.System (Color L) :=
  .ofCherries (ThetaLocal hier) {c | ¬ c.IsTerminal} {c | c.IsTerminal}

variable {hier} {g₀ : List PolarizedRole} {c a b : Color L}

theorem IsGen.conservation (h : IsGen (L := L) hier g₀ a b) :
    (∃ ρ g, a.Matches [.down ρ] ∧ b.Matches (upGrid g ++ [.up ρ]) ∧
      (g₀ = upGrid g ∨ g = [])) ∨
    (a = .free g₀ ∧ b = .nontheta) ∨
    (g₀ = [] ∧ b = .emptyTree) := by
  cases h with
  | close g₀ ρE ha hb => exact .inl ⟨ρE, [], ha, by simpa using hb, .inr rfl⟩
  | discharge g ρ hg hchain ha hb =>
    exact .inl ⟨ρ, g, ha, by simpa [upGrid] using hb, .inl rfl⟩
  | adjunct g₀ => exact .inr (.inl ⟨rfl, rfl⟩)
  | move c' hc' => exact .inr (.inr ⟨rfl, rfl⟩)

theorem IsGen.eq_nil_of_emptyTree (h : IsGen hier g₀ a b)
    (he : a = .emptyTree ∨ b = .emptyTree) : g₀ = [] := by
  cases h with
  | close _ _ ha hb | discharge _ _ _ _ ha hb => rcases he with rfl | rfl <;> simp at ha hb
  | adjunct => simp at he
  | move => rfl

theorem ThetaLocal.eq_nontheta (h : ThetaLocal hier c a b)
    (he : a = .emptyTree ∨ b = .emptyTree) : c = .nontheta := by
  obtain ⟨g₀, rfl, hg | hg⟩ := h
  · rw [hg.eq_nil_of_emptyTree he]
  · rw [hg.eq_nil_of_emptyTree he.symm]

end Rules

section Comb

variable {hier : ThetaRole → ThetaRole → Prop}

/-- The spine of a bare theta comb: the residue grid grows by one role per node on the path to
the head leaf, which carries the complete grid. -/
def combSpine (g : List ThetaRole) : List ThetaRole → Bud.Tree (Color L)
  | [] => .leaf (.free (upGrid g))
  | ρ :: rest => .node (.free (upGrid g)) (.leaf (.free [.down ρ])) (combSpine (g ++ [ρ]) rest)

/-- A bare theta comb ([marcolli-larson-2025]'s bare-system generators): an external role,
hierarchy-ordered internal roles, one receiver per node, the full giver grid at the head leaf,
and an arbitrary root recoloring. -/
def comb (g₀ : List PolarizedRole) (ρE : ThetaRole) (ρIs : List ThetaRole) :
    Bud.Tree (Color L) :=
  .node (.free g₀) (.leaf (.free [.down ρE])) (combSpine [ρE] ρIs)

@[simp] theorem out_combSpine (g rest : List ThetaRole) :
    (combSpine (L := L) g rest).out = .free (upGrid g) := by
  cases rest <;> rfl

theorem combSpine_nodeLocal {g : List ThetaRole} (hg : g ≠ []) {rest : List ThetaRole}
    (hchain : (g ++ rest).tail.IsChain hier) :
    (combSpine (L := L) g rest).NodeLocal (ThetaLocal hier) := by
  induction rest generalizing g with
  | nil => trivial
  | cons ρ rest ih =>
    have hstep : (g ++ [ρ]).tail.IsChain hier := by
      obtain ⟨a, g', rfl⟩ := List.exists_cons_of_ne_nil hg
      exact hchain.prefix ⟨rest, by simp⟩
    exact ⟨⟨_, rfl, .inl (.discharge g ρ hg hstep (by simp) (by simp))⟩, trivial,
      ih (by simp) (by simpa using hchain)⟩

theorem comb_derivable (g₀ : List PolarizedRole) (ρE : ThetaRole) (ρIs : List ThetaRole)
    (hchain : ρIs.IsChain hier) :
    (system (L := L) hier).Derives (.leaf (.free g₀)) (comb g₀ ρE ρIs) :=
  Bud.System.ofCherries_derives_leaf_iff.2
    ⟨rfl, ⟨_, rfl, .inl (.close g₀ ρE (by simp) (by simp [upGrid]))⟩, trivial,
      combSpine_nodeLocal (by simp) (by simpa using hchain)⟩

theorem combSpine_inputs (g rest : List ThetaRole) :
    (combSpine (L := L) g rest).inputs =
      rest.map (fun ρ ↦ Color.free [.down ρ]) ++ [.free (upGrid (g ++ rest))] := by
  induction rest generalizing g with
  | nil => simp [combSpine]
  | cons ρ rest ih => simp [combSpine, ih (g ++ [ρ])]

theorem comb_inputs (g₀ : List PolarizedRole) (ρE : ThetaRole) (ρIs : List ThetaRole) :
    (comb (L := L) g₀ ρE ρIs).inputs =
      .free [.down ρE] :: ρIs.map (fun ρ ↦ Color.free [.down ρ]) ++
        [.free (upGrid (ρE :: ρIs))] := by
  simp [comb, combSpine_inputs]

end Comb

/-! ### The theta criterion -/

/-- The role a color receives, when it is a single receiver. -/
def Color.receiver? : Color L → Option ThetaRole := fun c ↦
  match c.grid? with
  | some [⟨ρ, .receiver⟩] => some ρ
  | _ => none

@[simp] theorem Color.receiver?_free_down (ρ : ThetaRole) :
    (Color.free [.down ρ] : Color L).receiver? = some ρ := rfl

/-- The theta criterion on a colored operation. Some input, the head, carries an all-giver grid,
every other input is a single receiver, and the received roles match the head's grid
bijectively, as multisets. -/
def SatisfiesCriterion (x : Bud.Tree (Color L)) : Prop :=
  ∃ i c g, x.inputs[i]? = some c ∧ c.Matches (upGrid g) ∧
    (↑((x.inputs.eraseIdx i).map Color.receiver?) : Multiset (Option ThetaRole))
      = ↑(g.map some)

theorem comb_satisfiesCriterion (g₀ : List PolarizedRole) (ρE : ThetaRole)
    (ρIs : List ThetaRole) :
    SatisfiesCriterion (comb (L := L) g₀ ρE ρIs) := by
  refine ⟨ρIs.length + 1, .free (upGrid (ρE :: ρIs)), ρE :: ρIs, ?_, by simp, ?_⟩
  · rw [comb_inputs, List.getElem?_append_right (by simp)]
    simp
  · rw [comb_inputs,
      show Color.free [PolarizedRole.down ρE] ::
          ρIs.map (fun ρ ↦ Color.free [.down ρ]) ++
          [Color.free (upGrid (ρE :: ρIs))] =
        (Color.free [PolarizedRole.down ρE] ::
          ρIs.map (fun ρ ↦ Color.free (L := L) [.down ρ])) ++
          [Color.free (upGrid (ρE :: ρIs))] by simp,
      List.eraseIdx_append_of_length_le (by simp)]
    simp [List.map_map, Function.comp_def]

/-! ### The sole-role invariant -/

/-- The number of receiver occurrences in a grid. -/
def receiverCount (g : List PolarizedRole) : ℕ :=
  g.countP (fun p ↦ p.polarity == .receiver)

@[simp] theorem receiverCount_upGrid (g : List ThetaRole) :
    receiverCount (upGrid g) = 0 := by
  simp [receiverCount, upGrid, List.countP_map, Function.comp_def,
    PolarizedRole.up]

@[simp] theorem receiverCount_down_singleton (ρ : ThetaRole) :
    receiverCount [.down ρ] = 1 := rfl

/-- The color receives at most one role, its grid having at most one receiver occurrence. -/
def Color.SoleReceiver (c : Color L) : Prop :=
  ∀ g, c.grid? = some g → receiverCount g ≤ 1

theorem Color.soleReceiver_of_receiverCount_le {c : Color L}
    {g : List PolarizedRole} (hc : c.grid? = some g)
    (hg : receiverCount g ≤ 1) : c.SoleReceiver := by
  intro g' hg'
  rw [hc] at hg'
  exact Option.some_injective _ hg' ▸ hg

section SoleRole

variable {hier : ThetaRole → ThetaRole → Prop} {g₀ : List PolarizedRole} {c a b : Color L}
  {x : Bud.Tree (Color L)}

theorem IsGen.soleReceiver (h : IsGen hier g₀ a b)
    (hc : (Color.free g₀ : Color L).SoleReceiver) (hb : b ≠ .emptyTree) :
    a.SoleReceiver ∧ b.SoleReceiver := by
  cases h with
  | close _ _ ha hb' =>
    exact ⟨Color.soleReceiver_of_receiverCount_le ha (by simp),
      Color.soleReceiver_of_receiverCount_le hb' (by simp [receiverCount, PolarizedRole.up])⟩
  | discharge _ _ _ _ ha hb' =>
    exact ⟨Color.soleReceiver_of_receiverCount_le ha (by simp),
      Color.soleReceiver_of_receiverCount_le hb' (by simp [-upGrid_append])⟩
  | adjunct =>
    exact ⟨hc, Color.soleReceiver_of_receiverCount_le (g := []) rfl (by simp [receiverCount])⟩
  | move => exact absurd rfl hb

theorem ThetaLocal.soleReceiver (h : ThetaLocal hier c a b) (hc : c.SoleReceiver)
    (ha : a ≠ .emptyTree) (hb : b ≠ .emptyTree) : a.SoleReceiver ∧ b.SoleReceiver := by
  obtain ⟨g₀, rfl, hg | hg⟩ := h
  exacts [hg.soleReceiver hc hb, (hg.soleReceiver hc ha).symm]

theorem out_ne_emptyTree (hx : x.NodeLocal (ThetaLocal hier))
    (hmove : Color.emptyTree ∉ x.inputs) : x.out ≠ .emptyTree := by
  cases x with
  | leaf c => simpa [eq_comm] using hmove
  | node c l r =>
    obtain ⟨⟨g₀, rfl, -⟩, -⟩ := hx
    simp

theorem derives_soleReceiver (h : (system (L := L) hier).Derives (.leaf c) x)
    (hroot : c.SoleReceiver) (hmove : Color.emptyTree ∉ x.inputs) :
    ∀ d ∈ x.inputs, d.SoleReceiver := by
  obtain ⟨rfl, hx⟩ := Bud.System.ofCherries_derives_leaf_iff.1 h
  clear h
  induction x with
  | leaf c => simpa using hroot
  | node c l r ihl ihr =>
    obtain ⟨hc, hl, hr⟩ := hx
    simp only [Bud.Tree.inputs_node, List.mem_append, not_or] at hmove ⊢
    obtain ⟨hl', hr'⟩ :=
      hc.soleReceiver hroot (out_ne_emptyTree hl hmove.1) (out_ne_emptyTree hr hmove.2)
    rintro d (hd | hd)
    exacts [ihl hmove.1 hl hl' d hd, ihr hmove.2 hr hr' d hd]

end SoleRole

end Minimalist.Theta
