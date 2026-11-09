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
The bare system grafts whole combs, each discharging a grid completely; the complete system grafts
single discharges, non-theta positions and movement landing sites, and derives every comb.

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

@[simp] theorem upGrid_eq_nil {g : List ThetaRole} : upGrid g = [] ↔ g = [] := List.map_eq_nil_iff

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

@[simp] theorem Color.isTerminal_lex {α : L} {g : List PolarizedRole} :
    (Color.lex α g).IsTerminal := trivial

@[simp] theorem Color.isTerminal_emptyTree : (Color.emptyTree : Color L).IsTerminal := trivial

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

/-- The role a color receives, when its grid is a single receiver. -/
def Color.receiver? (c : Color L) : Option ThetaRole :=
  match c.grid? with
  | some [⟨ρ, .receiver⟩] => some ρ
  | _ => none

theorem Color.receiver?_eq_some_of_matches {c : Color L} {ρ : ThetaRole}
    (h : c.Matches [.down ρ]) : c.receiver? = some ρ := by
  rw [Color.receiver?, show c.grid? = some [.down ρ] from h]
  rfl

/-- The bare colors carry a grid of at least one role. -/
def Color.IsBare (c : Color L) : Prop :=
  ∃ g ≠ [], c.grid? = some g

@[simp] theorem Color.isBare_free {g : List PolarizedRole} :
    (Color.free g : Color L).IsBare ↔ g ≠ [] := by
  simp [Color.IsBare, Color.grid?]

@[simp] theorem Color.isBare_lex {α : L} {g : List PolarizedRole} :
    (Color.lex α g).IsBare ↔ g ≠ [] := by
  simp [Color.IsBare, Color.grid?]

@[simp] theorem Color.not_isBare_emptyTree : ¬ (Color.emptyTree : Color L).IsBare := by
  simp [Color.IsBare, Color.grid?]

/-! ### The bare theta bud system -/

section Bare

variable (hier : ThetaRole → ThetaRole → Prop)

/-- `IsSpine hier g s`: `s` is the spine of a theta comb below a vertex carrying the giver residue
`g`. Either `s` is the head leaf, carrying the grid `g`, or its vertex carries `g` and discharges
the next role of the hierarchy `hier` to a receiver leaf while the spine continues with the grown
residue. Leaves may be lexically anchored. -/
inductive IsSpine : List ThetaRole → Bud.Tree (Color L) → Prop
  | head {g : List ThetaRole} {h : Color L} (hh : h.Matches (upGrid g)) : IsSpine g (.leaf h)
  | discharge {g : List ThetaRole} {ρ : ThetaRole} {a : Color L} {s : Bud.Tree (Color L)}
      (hchain : (g ++ [ρ]).tail.IsChain hier) (ha : a.Matches [.down ρ])
      (hs : IsSpine (g ++ [ρ]) s) : IsSpine g (.node (.free (upGrid g)) (.leaf a) s)

/-- A bare theta comb, [marcolli-larson-2025]'s generator (3.10): a vertex of arbitrary color over
a receiver leaf of the external role and the spine of the external role's residue, so that the
head's grid is discharged one role per vertex, the external role last. -/
inductive IsComb : Bud.Tree (Color L) → Prop
  | mk (g₀ : List PolarizedRole) {ρE : ThetaRole} {a : Color L} {s : Bud.Tree (Color L)}
      (ha : a.Matches [.down ρE]) (hs : IsSpine hier [ρE] s) :
      IsComb (.node (.free g₀) (.leaf a) s)

/-- The bare theta bud system, [marcolli-larson-2025]'s Definition 3.8: the combs with a bare root,
the bare grids initial and their anchorings terminal. -/
def bareSystem : Bud.System (Color L) where
  rules := {t | IsComb hier t ∧ t.out.IsBare}
  initial := {c | c.IsBare ∧ ¬ c.IsTerminal}
  terminal := {c | c.IsBare ∧ c.IsTerminal}

variable {hier} {c : Color L} {t : Bud.Tree (Color L)}

@[simp] theorem mem_bareSystem_rules :
    t ∈ (bareSystem hier).rules ↔ IsComb hier t ∧ t.out.IsBare := Iff.rfl

@[simp] theorem mem_bareSystem_initial :
    c ∈ (bareSystem hier).initial ↔ c.IsBare ∧ ¬ c.IsTerminal := Iff.rfl

@[simp] theorem mem_bareSystem_terminal :
    c ∈ (bareSystem hier).terminal ↔ c.IsBare ∧ c.IsTerminal := Iff.rfl

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

@[simp] theorem mem_system_initial : c ∈ (system hier).initial ↔ ¬ c.IsTerminal := Iff.rfl

@[simp] theorem mem_system_terminal : c ∈ (system hier).terminal ↔ c.IsTerminal := Iff.rfl

/-- The local conservation law: at every generator, either one child receives the last role of
the other child's giver grid while the root keeps the residue, or the node is an adjunct
attachment, or a movement landing under a non-theta root. -/
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

theorem IsSpine.out_matches (h : IsSpine hier g s) : s.out.Matches (upGrid g) := by
  cases h with
  | head hh => exact hh
  | discharge => simp

theorem IsSpine.nodeLocal (h : IsSpine hier g s) (hg : g ≠ []) :
    s.NodeLocal (ThetaLocal hier) := by
  induction h with
  | head => trivial
  | discharge hchain ha hs ih =>
    exact ⟨⟨_, rfl, .inl (.discharge _ _ hg hchain ha hs.out_matches)⟩, trivial, ih (by simp)⟩

/-- The bare theta combs are derivable in the complete system, the generator half of
[marcolli-larson-2025]'s reduction of the bare system to the complete one (Theorem 3.14). -/
theorem IsComb.derives (h : IsComb hier t) : (system hier).Derives (.leaf t.out) t := by
  obtain ⟨g₀, ha, hs⟩ := h
  exact Bud.System.ofCherries_derives_leaf_iff.2
    ⟨rfl, ⟨_, rfl, .inl (.close g₀ _ ha hs.out_matches)⟩, trivial, hs.nodeLocal (by simp)⟩

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
gloss reads it: some input, the head, carries an all-giver grid, every other input is a single
receiver, and the received roles match the head's grid bijectively. -/
def SatisfiesCriterion (x : Bud.Tree (Color L)) : Prop :=
  ∃ l₁ h l₂ g, x.inputs = l₁ ++ h :: l₂ ∧ h.Matches (upGrid g) ∧
    ((l₁ ++ l₂).map Color.receiver?).Perm (g.map some)

/-- Under the theta criterion at most one input, the head, fails to be a single receiver. -/
theorem SatisfiesCriterion.countP_receiver?_isNone_le_one {x : Bud.Tree (Color L)}
    (h : SatisfiesCriterion x) : x.inputs.countP (fun c ↦ c.receiver?.isNone) ≤ 1 := by
  obtain ⟨l₁, h, l₂, g, hx, -, hp⟩ := h
  have h0 : (l₁ ++ l₂).countP (fun c ↦ c.receiver?.isNone) = 0 :=
    List.countP_eq_zero.2 fun c hc ↦ by
      obtain ⟨ρ, -, hρ⟩ := List.mem_map.1 (hp.subset (List.mem_map_of_mem hc))
      simp [← hρ]
  rw [List.countP_append] at h0
  rw [hx, List.countP_append, List.countP_cons]
  split <;> omega

variable {hier : ThetaRole → ThetaRole → Prop} {t : Bud.Tree (Color L)}

theorem IsSpine.exists_inputs {g : List ThetaRole} {s : Bud.Tree (Color L)}
    (h : IsSpine hier g s) : ∃ as h ρs, s.inputs = as ++ [h] ∧
      as.map Color.receiver? = ρs.map some ∧ h.Matches (upGrid (g ++ ρs)) := by
  induction h with
  | head hh => exact ⟨[], _, [], rfl, rfl, by simpa using hh⟩
  | @discharge g ρ a s _ ha _ ih =>
    obtain ⟨as, h, ρs, hs, has, hh⟩ := ih
    exact ⟨a :: as, h, ρ :: ρs, by simp [hs], by simp [has, Color.receiver?_eq_some_of_matches ha],
      by simpa using hh⟩

/-- Each bare theta comb satisfies the theta criterion. -/
theorem IsComb.satisfiesCriterion (h : IsComb hier t) : SatisfiesCriterion t := by
  obtain @⟨g₀, ρE, a, s, ha, hs⟩ := h
  obtain ⟨as, h, ρs, hin, has, hh⟩ := hs.exists_inputs
  refine ⟨a :: as, h, [], ρE :: ρs, by simp [hin], by simpa using hh, ?_⟩
  simp [has, Color.receiver?_eq_some_of_matches ha]

end Minimalist.Theta
