module

public import Linglib.Core.Computability.Bud
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole

/-!
# Theta theory as a coloring algorithm

Marcolli and Larson implement theta theory in the mathematical model of Minimalism as a coloring
algorithm: structures freely formed by Merge are filtered by membership in the language of a bud
generating system whose colors are theta grids, tuples of giver- or receiver-marked roles. A grid
injected at a predicate's leaf propagates up the tree like a conserved quantity: at each vertex one
receiver peels off to the sister position, and the residue continues toward the maximal projection.
The bare system grafts whole combs, each discharging a grid completely; the complete system builds
by colored Merge, one discharge, non-theta position or movement landing site at a time, and so
derives every comb.

## Main definitions

* `Color`: bare grids, lexically anchored grids, and the empty-tree marker.
* `IsComb`, `bareSystem`: the bare theta combs and the bare theta bud system.
* `IsGen`, `ThetaLocal`, `system`: the generator shapes, the cherries they license, and the
  complete theta bud system.
* `SatisfiesCriterion`: the theta criterion on a colored operation.

## Main statements

* `IsGen.conservation`: each generator conserves theta roles.
* `ThetaLocal.eq_nontheta`: movement lands only in non-theta positions.
* `language_bareSystem_subset`: every bare theta structure is an unbalanced one.

## Implementation notes

Trees are planar, so each generator licenses its children in either order, and a comb's head is
found by its grid rather than by a head function. Grids have no maximal valency.

## References

* [marcolli-larson-2025]
* [marcolli-chomsky-berwick-2025]
* [giraudo-2019]
-/

@[expose] public section

open ArgumentStructure

namespace Minimalist.Theta

/-- A theta role marked as given or received: [marcolli-larson-2025]'s disjoint union of the giver
occurrences `θ↑` and the receiver occurrences `θ↓`. -/
abbrev PolarizedRole := ThetaRole ⊕ ThetaRole

/-- The giver occurrence `θ↑`. -/
abbrev PolarizedRole.up : ThetaRole → PolarizedRole := Sum.inl

/-- The receiver occurrence `θ↓`. -/
abbrev PolarizedRole.down : ThetaRole → PolarizedRole := Sum.inr

variable {L : Type*}

/-- A color is a bare grid (nonterminal, the empty grid being the non-theta marker `θ0`), a
lexically anchored grid (terminal), or the empty-tree marker `(1, θ0)`. -/
inductive Color (L : Type*) where
  | free (g : List PolarizedRole)
  | lex (item : L) (g : List PolarizedRole)
  | emptyTree
  deriving DecidableEq, Repr

namespace Color

/-- The non-theta marker `θ0`, the empty grid. -/
abbrev nontheta : Color L := .free []

/-- The terminal colors are the lexically anchored grids and the empty-tree marker. -/
def IsTerminal : Color L → Prop
  | .free _ => False
  | .lex _ _ => True
  | .emptyTree => True

@[simp] theorem isTerminal_free {g : List PolarizedRole} : ¬ (free g : Color L).IsTerminal := id

@[simp] theorem isTerminal_lex {α : L} {g : List PolarizedRole} : (lex α g).IsTerminal := trivial

@[simp] theorem isTerminal_emptyTree : (emptyTree : Color L).IsTerminal := trivial

/-- The grid a color carries. Lexical anchoring is transparent to theta structure, and the
empty-tree marker carries the non-theta marker. -/
def grid : Color L → List PolarizedRole
  | .free g | .lex _ g => g
  | .emptyTree => []

@[simp] theorem grid_free (g : List PolarizedRole) : (free g : Color L).grid = g := rfl

@[simp] theorem grid_lex (α : L) (g : List PolarizedRole) : (lex α g).grid = g := rfl

@[simp] theorem grid_emptyTree : (emptyTree : Color L).grid = [] := rfl

/-- The role a color receives, when its grid is a single receiver. -/
def receiver? (c : Color L) : Option ThetaRole :=
  match c.grid with
  | [.inr ρ] => some ρ
  | _ => none

theorem receiver?_eq_some {c : Color L} {ρ : ThetaRole} (h : c.grid = [.down ρ]) :
    c.receiver? = some ρ := by
  rw [receiver?, h]

theorem receiver?_eq_none {c : Color L} {g : List ThetaRole} (h : c.grid = g.map .up) :
    c.receiver? = none := by
  rw [receiver?, h]
  rcases g with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl

end Color

/-! ### The bare theta bud system -/

section Bare

variable (hier : ThetaRole → ThetaRole → Prop)

/-- `IsSpine hier g s`: `s` is the spine of a theta comb below a vertex carrying the giver residue
`g`. Either `s` is the head leaf, carrying the grid `g`, or its vertex carries `g` and discharges
the next role of the hierarchy `hier` to a receiver leaf while the spine continues with the grown
residue. Leaves may be lexically anchored. -/
inductive IsSpine : List ThetaRole → Bud.Tree (Color L) → Prop
  | head {g : List ThetaRole} {h : Color L} (hh : h.grid = g.map .up) : IsSpine g (.leaf h)
  | discharge {g : List ThetaRole} {ρ : ThetaRole} {a : Color L} {s : Bud.Tree (Color L)}
      (hchain : (g ++ [ρ]).tail.IsChain hier) (ha : a.grid = [.down ρ])
      (hs : IsSpine (g ++ [ρ]) s) : IsSpine g (.node (.free (g.map .up)) (.leaf a) s)

/-- A bare theta comb, [marcolli-larson-2025]'s generator (3.10): a vertex of arbitrary color over
a receiver leaf of the external role and the spine of the external role's residue, so that the
head's grid is discharged one role per vertex, the external role last. -/
inductive IsComb : Bud.Tree (Color L) → Prop
  | mk (g₀ : List PolarizedRole) {ρE : ThetaRole} {a : Color L} {s : Bud.Tree (Color L)}
      (ha : a.grid = [.down ρE]) (hs : IsSpine hier [ρE] s) :
      IsComb (.node (.free g₀) (.leaf a) s)

/-- The bare theta bud system, [marcolli-larson-2025]'s Definition 3.8: the combs whose root
carries at least one role, the nonempty bare grids initial and their anchorings terminal. -/
def bareSystem : Bud.System (Color L) where
  rules := {t | IsComb hier t ∧ t.out.grid ≠ []}
  initial := {c | c.grid ≠ [] ∧ ¬ c.IsTerminal}
  terminal := {c | c.grid ≠ [] ∧ c.IsTerminal}

variable {hier} {c : Color L} {t : Bud.Tree (Color L)}

@[simp] theorem mem_bareSystem_rules :
    t ∈ (bareSystem hier).rules ↔ IsComb hier t ∧ t.out.grid ≠ [] := Iff.rfl

@[simp] theorem mem_bareSystem_initial :
    c ∈ (bareSystem hier).initial ↔ c.grid ≠ [] ∧ ¬ c.IsTerminal := Iff.rfl

@[simp] theorem mem_bareSystem_terminal :
    c ∈ (bareSystem hier).terminal ↔ c.grid ≠ [] ∧ c.IsTerminal := Iff.rfl

end Bare

/-! ### The complete theta bud system -/

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
      (ha : a.grid = [.down ρE]) (hb : b.grid = [.up ρE]) :
      IsGen g₀ a b
  | discharge (g : List ThetaRole) (ρ : ThetaRole) (hg : g ≠ [])
      (hchain : ((g ++ [ρ]).tail).IsChain hier) {a b : Color L}
      (ha : a.grid = [.down ρ]) (hb : b.grid = (g ++ [ρ]).map .up) :
      IsGen (g.map .up) a b
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

@[simp] theorem mem_system_initial : c ∈ (system hier).initial ↔ ¬ c.IsTerminal := Iff.rfl

@[simp] theorem mem_system_terminal : c ∈ (system hier).terminal ↔ c.IsTerminal := Iff.rfl

/-- The local conservation law: at every generator, either one child receives the last role of
the other child's giver grid while the root keeps the residue, or the node is an adjunct
attachment, or a movement landing under a non-theta root. -/
theorem IsGen.conservation (h : IsGen (L := L) hier g₀ a b) :
    (∃ ρ g, a.grid = [.down ρ] ∧ b.grid = g.map .up ++ [.up ρ] ∧
      (g₀ = g.map .up ∨ g = [])) ∨
    (a = .free g₀ ∧ b = .nontheta) ∨
    (g₀ = [] ∧ b = .emptyTree) := by
  cases h with
  | close g₀ ρE ha hb => exact .inl ⟨ρE, [], ha, hb, .inr rfl⟩
  | discharge g ρ hg hchain ha hb => exact .inl ⟨ρ, g, ha, by simpa using hb, .inl rfl⟩
  | adjunct g₀ => exact .inr (.inl ⟨rfl, rfl⟩)
  | move c' hc' => exact .inr (.inr ⟨rfl, rfl⟩)

theorem IsGen.eq_nil_of_emptyTree (h : IsGen hier g₀ a b)
    (he : a = .emptyTree ∨ b = .emptyTree) : g₀ = [] := by
  cases h with
  | close _ _ ha hb | discharge _ _ _ _ ha hb => rcases he with rfl | rfl <;> simp at ha hb
  | adjunct => simp at he
  | move => rfl

/-- Movement lands only in non-theta positions: a generator with an empty-tree child has the
non-theta root. The External/Internal Merge dichotomy of theta theory, at generator level. -/
theorem ThetaLocal.eq_nontheta (h : ThetaLocal hier c a b)
    (he : a = .emptyTree ∨ b = .emptyTree) : c = .nontheta := by
  obtain ⟨g₀, rfl, hg | hg⟩ := h
  · rw [hg.eq_nil_of_emptyTree he]
  · rw [hg.eq_nil_of_emptyTree he.symm]

end Rules

/-! ### Combs in the complete system -/

section Comb

variable {hier : ThetaRole → ThetaRole → Prop} {g : List ThetaRole} {s t : Bud.Tree (Color L)}

theorem IsSpine.grid_out (h : IsSpine hier g s) : s.out.grid = g.map .up := by
  cases h with
  | head hh => exact hh
  | discharge => rfl

/-- A spine is built by colored Merge, one discharge at a time. -/
theorem IsSpine.derives (h : IsSpine hier g s) (hg : g ≠ []) :
    (system hier).Derives (.leaf s.out) s := by
  induction h with
  | head => rfl
  | discharge hchain ha hs ih =>
    exact .node (Bud.System.cherry_mem_ofCherries.2
      ⟨_, rfl, .inl (.discharge _ _ hg hchain ha hs.grid_out)⟩) .refl (ih (by simp))

/-- The bare theta combs are built by colored Merge in the complete system, the generator half of
[marcolli-larson-2025]'s reduction of the bare system to the complete one (Theorem 3.14). -/
theorem IsComb.derives (h : IsComb hier t) : (system hier).Derives (.leaf t.out) t := by
  obtain ⟨g₀, ha, hs⟩ := h
  exact .node (Bud.System.cherry_mem_ofCherries.2 ⟨_, rfl, .inl (.close g₀ _ ha hs.grid_out)⟩)
    .refl (hs.derives (by simp))

/-- Every bare theta structure is an unbalanced theta structure, the inclusion of
[marcolli-larson-2025]'s Theorem 3.14. -/
theorem language_bareSystem_subset :
    (bareSystem (L := L) hier).language ⊆ (system hier).language := by
  rintro x ⟨hI, hD, hT⟩
  exact ⟨hI.2, Bud.System.Derives.of_rules (B := bareSystem hier) (fun _ hr ↦ hr.1.derives) hD,
    fun c hc ↦ (hT c hc).2⟩

end Comb

/-! ### The theta criterion -/

/-- The theta criterion on a colored operation, [marcolli-larson-2025]'s Definition 3.10 as its
gloss reads it: some input, the head, carries an all-giver grid, and the other inputs are single
receivers of exactly the head's roles. -/
def SatisfiesCriterion (x : Bud.Tree (Color L)) : Prop :=
  ∃ h ∈ x.inputs, ∃ g : List ThetaRole, h.grid = g.map .up ∧
    (x.inputs.map Color.receiver? : Multiset (Option ThetaRole)) = none ::ₘ (g.map some : List _)

/-- Under the theta criterion exactly one input, the head, fails to be a single receiver. -/
theorem SatisfiesCriterion.count_none {x : Bud.Tree (Color L)} (h : SatisfiesCriterion x) :
    (x.inputs.map Color.receiver? : Multiset (Option ThetaRole)).count none = 1 := by
  obtain ⟨-, -, g, -, he⟩ := h
  rw [he, Multiset.count_cons_self, Multiset.count_eq_zero.2 (by simp)]

variable {hier : ThetaRole → ThetaRole → Prop} {t : Bud.Tree (Color L)}

theorem IsSpine.exists_inputs {g : List ThetaRole} {s : Bud.Tree (Color L)}
    (h : IsSpine hier g s) : ∃ as h ρs, s.inputs = as ++ [h] ∧
      as.map Color.receiver? = ρs.map some ∧ h.grid = (g ++ ρs).map .up := by
  induction h with
  | head hh => exact ⟨[], _, [], rfl, rfl, by simpa using hh⟩
  | @discharge g ρ a s _ ha _ ih =>
    obtain ⟨as, h, ρs, hs, has, hh⟩ := ih
    exact ⟨a :: as, h, ρ :: ρs, by simp [hs], by simp [has, Color.receiver?_eq_some ha],
      by simpa using hh⟩

/-- Each bare theta comb satisfies the theta criterion. -/
theorem IsComb.satisfiesCriterion (h : IsComb hier t) : SatisfiesCriterion t := by
  obtain @⟨g₀, ρE, a, s, ha, hs⟩ := h
  obtain ⟨as, h, ρs, hin, has, hh⟩ := hs.exists_inputs
  refine ⟨h, by simp [hin], ρE :: ρs, by simpa using hh, ?_⟩
  have hmap : (Bud.Tree.node (.free g₀) (.leaf a) s).inputs.map Color.receiver? =
      (ρE :: ρs).map some ++ [none] := by
    simp [hin, has, Color.receiver?_eq_none hh, Color.receiver?_eq_some ha]
  rw [hmap, Multiset.cons_coe, Multiset.coe_eq_coe]
  exact List.perm_append_singleton _ _

end Minimalist.Theta
