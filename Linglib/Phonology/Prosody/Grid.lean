module

public import Linglib.Phonology.Prosody.Word
public import Mathlib.Data.List.MinMax

/-!
# The metrical grid

The **metrical grid** is the prominence dual of the prosodic word: a column of marks over each
syllable, taller standing for greater relative prominence (primary > secondary > unstressed). This
file is organised as a small tower of objects, each adding structure to the plain grid and each
connected to the plainer one below by a forgetful map:

```
Marks        rendered rows of marks; the Continuous Column Constraint lives here
  ↑ rows                                    (Prince 1983's autonomous grid)
Grid         column heights — the pure rhythmic grid
  ↑ toGrid                                   (add the head terminal)
MarkedGrid   a grid whose columns carry the head-spine (Liberman & Prince's head terminals)
  ↑ project                                  (the RPPR)
Tree         the bracketed grid — brackets at all layers (Hayes 1995 §3.5)
```

The projection `Grid.project` is Liberman and Prince's (1977) *Relative Prominence Projection Rule*:
a homomorphism from the tree into the head-marked grid, built from a small algebra
(`cell`/`juxtapose`/`promote`/`clear`). The grid readers (`columns`, `terminals`, `headTerminals`,
`headHeights`) are the forgetful maps out of it. What the forgetful map onto the pure grid drops is
*theorem*-shaped: constituency (`Grid.ofTree_not_injective`; the grid underdetermines bracketing,
Hayes 1995 §3.8) and, under recursion, order-invariant culminativity
(`Grid.not_culminative_under_recursion`).

## Main definitions
* `Grid` / `Grid.peak` / `Grid.IsCulminative` — the pure grid (column heights) and its invariants.
* `Marks` / `Marks.IsContinuous` / `Grid.rows` — the rendered grid and the Continuous Column
  Constraint, which holds for any rendered grid by construction.
* `MarkedGrid` / `Grid.project` — the head-marked grid and the RPPR projection from a tree.
* `Tree.columns` / `Tree.headTerminals` / `Tree.headHeights` / `Tree.IsHeaded` — the grid readers.

## Main results
* `Grid.ofTree_isContinuous` — the Continuous Column Constraint, by construction (free);
  `Marks.isContinuous_iff` reads it column by column.
* `Grid.isCulminative_of_forall_lt` / `Grid.IsCulminative.eq_of_eq_peak` — a strict unique
  maximum is culminative, and a culminative grid has one peak column.
* `Grid.peak_toProsTree` — head-preservation for a foot (its grid peaks at the head σ).
* `Tree.headHeights_eq_peak` — on a non-recursive headed word the head terminal's height is the
  grid peak: metrical primary stress is the tallest column.
* `Grid.ofTree_not_injective` / `Grid.not_culminative_under_recursion` — what the projection
  forgets: constituency, and order-invariant culminativity under recursion.
* `Grid.head_below_peak_under_recursion` / `Grid.head_below_peak_unlayered` — the peak can desert
  the head terminal under recursion or without Layeredness.

## References

* [liberman-prince-1977]
* [prince-1983]
* [halle-vergnaud-1987]
* [hayes-1995]
* [ito-mester-2009]
-/

@[expose] public section

namespace Prosody

/-! ## The tower carriers

The four objects of the tower (see the module header): the rendered `Marks`, the pure `Grid`, and
the head-marked grid `MarkedGrid` built from `Column`s. Operations follow, one namespace each. -/

/-- A rendered metrical grid is a list of rows of head-marks, bottom row first. -/
abbrev Marks := List (List Bool)

/-- A metrical grid ([hayes-1995] §3.2) records the beat count (column height) over each position,
    left to right. Absolute heights carry no significance; only relative prominence does. -/
abbrev Grid := List ℕ

/-- One column of a marked grid records the σ-leaf it sits over, its mark count (`height`), and
    whether it lies on the current head-spine (the head terminal so far, [liberman-prince-1977]). -/
structure Column (α : Type*) where
  /-- The σ-leaf under this column. -/
  terminal : α
  /-- The column height = number of grid marks. -/
  height : ℕ
  /-- Whether this column is (so far) the head terminal. -/
  onSpine : Bool

/-- A grid whose columns carry the head-spine (the head terminals, [liberman-prince-1977]) — the
    pure grid *plus a head marking*. It deliberately does not record the full bracketing (that is
    `Tree`; `Grid.ofTree_not_injective` is the honest statement that heights lose it). -/
abbrev MarkedGrid (α : Type*) := List (Column α)

/-! ## Marks: the Continuous Column Constraint -/

namespace Marks

/-- Whether one row is a submask of the row below. -/
def rowSubmask (upper lower : List Bool) : Bool :=
  (upper.zip lower).all (fun p => !p.1 || p.2)

/-- The Continuous Column Constraint ([prince-1983]; [hayes-1995] §3.4.2 (9)) says that no column
    has a gap. It is a violable predicate on an arbitrary rendered grid. -/
def IsContinuous (m : Marks) : Prop :=
  m.IsChain (fun lower upper => rowSubmask upper lower = true)

instance (m : Marks) : Decidable (IsContinuous m) := by unfold IsContinuous; infer_instance

theorem isContinuous_iff {m : Marks} : IsContinuous m ↔
    ∀ r (hr : r + 1 < m.length) i (hi : i < m[r + 1].length) (hi' : i < m[r].length),
      m[r + 1][i] = true → m[r][i] = true := by
  rw [IsContinuous, List.isChain_iff_getElem]
  refine forall_congr' λ r => forall_congr' λ hr => ?_
  simp only [rowSubmask, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true]
  constructor
  · intro h i hi hi' hup
    have := h (m[r + 1][i], m[r][i]) (List.mem_iff_getElem.2 ⟨i, by simp; omega, by simp⟩)
    simpa [hup] using this
  · rintro h ⟨u, l⟩ hul
    obtain ⟨i, hi, hi'⟩ := List.mem_iff_getElem.1 hul
    simp only [List.getElem_zip, Prod.mk.injEq] at hi'
    obtain ⟨rfl, rfl⟩ := hi'
    simp only [List.length_zip, lt_min_iff] at hi
    by_cases hu : m[r + 1][i] = true
    · exact Or.inr (h i hi.1 hi.2 hu)
    · exact Or.inl (by simpa using hu)

end Marks

/-! ## The head-marked grid: the marked-grid algebra -/

namespace MarkedGrid
variable {α : Type*} (b : MarkedGrid α) (bs : List (MarkedGrid α))

/-- Forgetting the marking gives the underlying pure grid of column heights. -/
def toGrid : Grid := b.map (·.height)

/-- The terminals under the columns, left to right. -/
def terminals : List α := b.map (·.terminal)

/-- The head-spine columns' heights — the head terminals' prominences. -/
def headHeights : Grid := (b.filter (·.onSpine)).map (·.height)

/-- The head-spine terminals — the head terminals. -/
def headTerminals : List α := (b.filter (·.onSpine)).map (·.terminal)

/-- A single terminal is one column of height `1`, on its own head-spine. -/
def cell (x : α) : MarkedGrid α := [⟨x, 1, true⟩]

/-- Juxtapose sibling constituents. -/
def juxtapose : MarkedGrid α := bs.flatten

/-- In the **head-projection step** of the RPPR ([liberman-prince-1977]) a head edge raises the
    head by one grid mark, bumping every head-spine column. -/
def promote : MarkedGrid α :=
  b.map fun c => { c with height := c.height + if c.onSpine then 1 else 0 }

/-- Across a weak edge heights freeze and the head-spine marking is dropped. -/
def clear : MarkedGrid α := b.map fun c => { c with onSpine := false }

/-- On one edge of the descent a head edge projects and any other clears the spine. -/
def edge (isHead : Bool) (b : MarkedGrid α) : MarkedGrid α :=
  if isHead then b.promote else b.clear

@[simp] theorem edge_true : edge true b = b.promote := rfl
@[simp] theorem edge_false : edge false b = b.clear := rfl

/-! ### The algebra of the marked grid -/

@[simp] theorem toGrid_cell (x : α) : (cell x).toGrid = [1] := rfl
@[simp] theorem headHeights_cell (x : α) : (cell x).headHeights = [1] := rfl
@[simp] theorem headTerminals_cell (x : α) : (cell x).headTerminals = [x] := rfl

@[simp] theorem toGrid_clear : (clear b).toGrid = b.toGrid := by simp [clear, toGrid, List.map_map]

@[simp] theorem headHeights_clear : (clear b).headHeights = [] := by simp [clear, headHeights]

@[simp] theorem headTerminals_clear : (clear b).headTerminals = [] := by simp [clear, headTerminals]

@[simp] theorem headHeights_promote : (promote b).headHeights = b.headHeights.map (· + 1) := by
  induction b with
  | nil => rfl
  | cons c b ih => obtain ⟨_, _, d⟩ := c; cases d <;> simp_all [promote, headHeights]

@[simp] theorem headTerminals_promote : (promote b).headTerminals = b.headTerminals := by
  simp only [headTerminals, promote, List.filter_map, List.map_map, Function.comp_def]

@[simp] theorem toGrid_juxtapose : (juxtapose bs).toGrid = bs.flatMap (·.toGrid) := by
  simp [juxtapose, toGrid, List.flatMap_def]

@[simp] theorem headHeights_juxtapose :
    (juxtapose bs).headHeights = bs.flatMap (·.headHeights) := by
  simp [juxtapose, headHeights, List.flatMap_def, Function.comp_def]

@[simp] theorem headTerminals_juxtapose :
    (juxtapose bs).headTerminals = bs.flatMap (·.headTerminals) := by
  simp [juxtapose, headTerminals, List.flatMap_def, Function.comp_def]

@[simp] theorem headHeights_edge (h : Bool) : (edge h b).headHeights =
    if h then b.headHeights.map (· + 1) else [] := by cases h <;> simp [edge]

@[simp] theorem headTerminals_edge (h : Bool) : (edge h b).headTerminals =
    if h then b.headTerminals else [] := by cases h <;> simp [edge]

end MarkedGrid

/-! ## Grid: peak, the RPPR projection, and the readers -/

namespace Grid

/-! ### The pure grid: peak, culminativity, rendering -/

variable {g : Grid}

/-- The prominence peak is the height of the tallest column. -/
def peak (g : Grid) : ℕ := g.foldr max 0

@[simp] theorem peak_nil : peak [] = 0 := rfl

theorem le_peak {h : ℕ} (hh : h ∈ g) : h ≤ peak g := List.le_max_of_le' 0 hh le_rfl

theorem peak_le {n : ℕ} (h : ∀ x ∈ g, x ≤ n) : peak g ≤ n := List.max_le_of_forall_le _ n h

@[simp] theorem peak_reverse : peak g.reverse = peak g :=
  le_antisymm (peak_le fun _ hx ↦ le_peak (List.mem_reverse.1 hx))
    (peak_le fun _ hx ↦ le_peak (List.mem_reverse.2 hx))

theorem getD_le_peak (i : ℕ) : g.getD i 0 ≤ peak g := by
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i g.length with h | h
  · rw [List.getElem?_eq_getElem h]; exact le_peak (List.getElem_mem h)
  · simp [List.getElem?_eq_none h]

/-- A grid is culminative ([liberman-prince-1977]; [hayes-1995]) when exactly one column is
    tallest. This is strictly stronger than having a unique head terminal (`IsHeaded`), since two
    columns can tie. -/
def IsCulminative (g : Grid) : Prop := g.countP (· == peak g) = 1

instance (g : Grid) : Decidable (IsCulminative g) := by unfold IsCulminative; infer_instance

theorem isCulminative_of_forall_lt {i : ℕ} (hi : i < g.length)
    (h : ∀ j (hj : j < g.length), j ≠ i → g[j] < g[i]) : IsCulminative g := by
  have hpeak : peak g = g[i] :=
    le_antisymm (peak_le λ x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
      by_cases hji : j = i
      · subst hji; exact le_rfl
      · exact (h j hj hji).le) (le_peak (List.getElem_mem hi))
  rw [IsCulminative, hpeak]
  generalize hm : g[i] = m at h
  have h1 : (g.take i).countP (· == m) = 0 := List.countP_eq_zero.2 λ x hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_take, lt_min_iff] at hj
    simpa [List.getElem_take] using (h j hj.2 (by omega)).ne
  have h2 : (g.drop (i + 1)).countP (· == m) = 0 := List.countP_eq_zero.2 λ x hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_drop] at hj
    simpa [List.getElem_drop] using (h (i + 1 + j) (by omega) (by omega)).ne
  have h3 : g.countP (· == m) = (g.take i).countP (· == m) + (g.drop i).countP (· == m) := by
    rw [← List.countP_append, List.take_append_drop]
  rw [List.drop_eq_getElem_cons hi, List.countP_cons_of_pos (by simp [hm])] at h3
  omega

theorem IsCulminative.eq_of_eq_peak (hc : IsCulminative g) {i j : ℕ} (hi : i < g.length)
    (hj : j < g.length) (hpi : g[i] = peak g) (hpj : g[j] = peak g) : i = j := by
  by_contra hne
  wlog hlt : i < j generalizing i j
  · exact this hj hi hpj hpi (Ne.symm hne) (by omega)
  rw [IsCulminative] at hc
  generalize hp : peak g = p at hc hpi hpj
  have h1 : (g.drop i).countP (· == p) = (g.drop (i + 1)).countP (· == p) + 1 := by
    rw [List.drop_eq_getElem_cons hi, List.countP_cons_of_pos (by simp [hpi])]
  have h2 : 0 < (g.drop (i + 1)).countP (· == p) :=
    List.countP_pos_iff.2 ⟨g[j], List.mem_iff_getElem.2 ⟨j - (i + 1), by simp; omega,
      by rw [List.getElem_drop]; congr 1; omega⟩, by simp [hpj]⟩
  have h3 : g.countP (· == p) = (g.take i).countP (· == p) + (g.drop i).countP (· == p) := by
    rw [← List.countP_append, List.take_append_drop]
  omega

/-- Rendering a grid as stacked rows of marks puts a mark in row `r` over every column taller than
    `r`. -/
def rows (g : Grid) : Marks := (List.range (peak g)).map (fun r => g.map (r < ·))

@[simp] theorem length_rows : (rows g).length = peak g := by simp [rows]

@[simp] theorem length_getElem_rows {r : ℕ} (hr : r < (rows g).length) :
    (rows g)[r].length = g.length := by simp [rows]

@[simp] theorem getElem_rows {r i : ℕ} (hr : r < (rows g).length) (hi : i < (rows g)[r].length) :
    (rows g)[r][i] = decide (r < g[i]'(by simpa using hi)) := by simp [rows]

/-- **The Continuous Column Constraint is free.** Every rendered grid satisfies it, because a column
    is a solid stack of marks by construction — continuity is the shape of a histogram, not a
    theorem about trees ([hayes-1995] §3.4.2). -/
theorem rows_isContinuous (g : Grid) : Marks.IsContinuous (rows g) := by
  rw [Marks.IsContinuous, rows, List.isChain_map, List.isChain_iff_getElem]
  intro i _
  simp only [List.getElem_range, Marks.rowSubmask, List.zip_map', List.all_map, List.all_eq_true]
  intro h _
  by_cases hr : i + 1 < h <;> simp [hr]
  omega

/-! ### The RPPR projection -/

end Grid

namespace Tree

open MarkedGrid Grid

/-- One RPPR step pairs the node's label with its grid, so a parent can read the head flag off
    each child. -/
def projectStep (a : Constituent) (ps : List (Constituent × MarkedGrid Tree)) :
    Constituent × MarkedGrid Tree :=
  (a, if a.level = .syl ∧ ps = [] then cell (.node a [])
      else juxtapose (ps.map fun p => edge p.1.isHead p.2))

/-- The **Relative Prominence Projection Rule** ([liberman-prince-1977]) is a homomorphism
    `Tree → MarkedGrid`. A σ-leaf is one `cell`, and any other node juxtaposes its children,
    projecting across head edges and clearing the spine across the rest. -/
def project (t : Tree) : MarkedGrid Tree := (t.fold projectStep).2

private theorem fold_projectStep (t : Tree) :
    t.fold projectStep = (t.value, project t) := by
  cases t with | node a cs => rfl

@[simp] theorem project_node (a : Constituent) (cs : List Tree) :
    project (.node a cs) = if a.level = .syl ∧ cs = [] then cell (.node a [])
      else juxtapose (cs.map fun c => edge c.value.isHead (project c)) := by
  conv_lhs => rw [project, RoseTree.fold_node]
  simp only [fold_projectStep, projectStep, List.map_eq_nil_iff, List.map_map,
    Function.comp_def]

/-! ## Reading the grid off a tree (the forgetful maps) -/

variable (t : Tree)

/-- The σ-leaves of a tree, left to right, form the terminal tier the grid sits over. -/
def terminals : List Tree := (project t).terminals

/-- In the grid-column heights ([liberman-prince-1977]) each σ-leaf's height is `1` plus the
    contiguous run of head edges ending at it. -/
def columns : Grid := (project t).toGrid

/-- The **head terminals** ([liberman-prince-1977]) are the σ-leaves reached from the root by all
    head edges. -/
def headTerminals : List Tree := (project t).headTerminals

/-- The head terminals' prominences are the live cells' heights. -/
def headHeights : Grid := (project t).headHeights

/-- A tree is headed when it has a unique head terminal. -/
def IsHeaded : Prop := (headHeights t).length = 1

instance : Decidable (IsHeaded t) := by unfold IsHeaded; infer_instance

/-- The metrical grid of a tree, as stacked rows. -/
def _root_.Prosody.Grid.ofTree : Marks := (columns t).rows

theorem _root_.Prosody.Grid.ofTree_isContinuous : Marks.IsContinuous (Grid.ofTree t) :=
  rows_isContinuous _

/-! ### The reader recursions

Each reader is a homomorphism out of the marked-grid algebra, so on a node it is the juxtaposition
of the children's readings, projected across head edges. These fuse `project_node` with the algebra
once, so the downstream proofs never re-walk the fold. -/

variable (a : Constituent) (cs : List Tree)

theorem columns_node : columns (.node a cs) = if a.level = .syl ∧ cs = [] then [1]
    else cs.flatMap fun c => (edge c.value.isHead (project c)).toGrid := by
  simp [columns, apply_ite MarkedGrid.toGrid, List.flatMap_map]

theorem headHeights_node : headHeights (.node a cs) = if a.level = .syl ∧ cs = [] then [1]
    else cs.flatMap fun c => if c.value.isHead then (headHeights c).map (· + 1) else [] := by
  simp [headHeights, apply_ite MarkedGrid.headHeights, List.flatMap_map]

theorem headTerminals_node : headTerminals (.node a cs) = if a.level = .syl ∧ cs = [] then [.node a []]
    else cs.flatMap fun c => if c.value.isHead then headTerminals c else [] := by
  simp [headTerminals, apply_ite MarkedGrid.headTerminals, List.flatMap_map]

/-! ### The head terminals compute the head-terminal relation -/

/-- `leaf` is a head terminal of `t`, reached from the root by an all-head descent. -/
inductive IsHeadTerminal : Tree → Tree → Prop
  | leaf {a : Constituent} (ha : a.level = .syl) : IsHeadTerminal (.node a []) (.node a [])
  | head {a cs c leaf} : c ∈ cs → c.value.isHead →
      IsHeadTerminal c leaf → IsHeadTerminal (.node a cs) leaf

theorem headTerminal_sound {t leaf : Tree} (h : leaf ∈ headTerminals t) :
    IsHeadTerminal t leaf := by
  induction t using Tree.recLeafBranch with
  | leaf a ha =>
    rw [headTerminals_node, ite_eq_left ⟨ha, rfl⟩, List.mem_singleton] at h
    subst h; exact .leaf ha
  | branch a cs hne IH =>
    rw [headTerminals_node, ite_eq_right hne, List.mem_flatMap] at h
    obtain ⟨c, hc, hmem⟩ := h
    by_cases hh : c.value.isHead = true
    · rw [ite_eq_left hh] at hmem; exact .head hc hh (IH c hc hmem)
    · rw [ite_eq_right hh] at hmem; exact absurd hmem List.not_mem_nil

/-! ## Head-preservation: the foot commuting square

Reading a `Foot`'s grid recovers its head — the height-1 core of the transport story: its column
heights are `2` at the head σ and `1` elsewhere, so the grid peaks at `2`. -/

theorem columns_toProsTree {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    columns (f.toProsTree w) = Foot.toGrid f := by
  rw [Foot.toProsTree, columns_node, ite_eq_right (by simp [Constituent.level]),
      List.flatMap_map, Foot.toGrid, List.map_eq_flatMap]
  refine List.flatMap_congr fun i _ => ?_
  by_cases hi : i = f.head <;>
    simp [project_node, Constituent.level, Constituent.isHead, edge,
      promote, clear, toGrid, cell, hi]

theorem peak_toProsTree {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    peak (columns (f.toProsTree w)) = 2 := by
  rw [columns_toProsTree, Foot.toGrid]
  refine Nat.le_antisymm (peak_le fun x hx => ?_) (le_peak ?_)
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; split <;> decide
  · exact List.mem_map.mpr ⟨f.head, List.mem_finRange _, by simp⟩

/-! ## What the grid forgets

The forgetful map onto the pure grid is one-way: it drops constituency (`ofTree_not_injective`;
[hayes-1995] §3.8 argues *for* bracketing precisely because the grid underdetermines it) and, under
recursion, order-invariant culminativity (`not_culminative_under_recursion`). -/

/-- The grid render is not injective, since it **forgets constituency**. A σ parsed under a foot
    and the same σ left bare render to the same grid ([hayes-1995] §3.8). -/
theorem _root_.Prosody.Grid.ofTree_not_injective : ¬ Function.Injective Grid.ofTree :=
  Function.not_injective_iff.mpr
    ⟨.om [.ft false [.σ 1]], .om [.σ 1], by decide⟩

theorem not_culminative_under_recursion : ∃ t : Tree, IsWord t ∧ ¬ IsCulminative (columns t) :=
  ⟨.om [.ft true [.σ 1 true], .om [.ft true [.σ 1 true]]], by decide⟩

/-! ## The word peak is the head terminal

On a non-recursive headed word the grid peak *is* the head terminal ([liberman-prince-1977]):
metrical primary stress is the tallest column. Recursion is the sole obstruction, and — this being
[hayes-1995] §3.4.2(C)'s "the higher grid mark may only be assigned to a syllable that already bears
stress" — the peak sits atop a foot head. -/

private theorem height_word_child_le {ch : Tree}
    (h : IsFoot ch ∨ (ch.value.level = .syl ∧ ch.children = [])) : ch.height ≤ 2 := by
  rcases h with hfoot | ⟨_, hcs⟩
  · obtain ⟨chl, chcs⟩ := ch
    rw [RoseTree.height_node]
    have : (chcs.map RoseTree.height).foldr max 0 ≤ 1 :=
      List.max_le_of_forall_le _ _ fun x hx => by
        obtain ⟨⟨cl, ccs⟩, hc, rfl⟩ := List.mem_map.mp hx
        obtain ⟨-, hcs⟩ := hfoot.syl_leaf hc
        simp only [RoseTree.children_node] at hcs
        subst hcs
        exact le_of_eq rfl
    omega
  · obtain ⟨chl, chcs⟩ := ch
    simp only [RoseTree.children_node] at hcs; subst hcs
    exact Nat.le_succ_of_le (le_of_eq rfl)

private theorem toGrid_bounds {t : Tree} : ∀ c ∈ columns t, 1 ≤ c ∧ c ≤ t.height := by
  induction t using Tree.recLeafBranch with
  | leaf a ha =>
    rw [columns_node, ite_eq_left ⟨ha, rfl⟩, RoseTree.height_node]
    intro c hc; simp only [List.mem_singleton] at hc; omega
  | branch a cs hne IH =>
    rw [columns_node, ite_eq_right hne, RoseTree.height_node]
    intro c hc
    rw [List.mem_flatMap] at hc
    obtain ⟨ch, hch, hc⟩ := hc
    have hd : ch.height ≤ (cs.map RoseTree.height).foldr max 0 :=
      List.le_max_of_le (List.mem_map_of_mem hch) le_rfl
    cases hh : ch.value.isHead with
    | false =>
      simp only [hh, edge_false, toGrid_clear] at hc
      have := IH ch hch c hc; omega
    | true =>
      simp only [hh, edge_true, promote, toGrid, List.map_map, List.mem_map] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      have := IH ch hch x.height (List.mem_map.mpr ⟨x, hx, rfl⟩)
      by_cases hs : x.onSpine <;> simp [hs] <;> omega

theorem headHeights_sublist_columns (t : Tree) : (headHeights t).Sublist (columns t) :=
  List.filter_sublist.map _

theorem headHeight_le_peak {t : Tree} {h : ℕ} (hh : h ∈ headHeights t) : h ≤ peak (columns t) :=
  le_peak ((headHeights_sublist_columns t).subset hh)

theorem mem_toGrid_edge {h : Bool} {b : MarkedGrid Tree} {c : ℕ}
    (hc : c ∈ (edge h b).toGrid) : c ∈ b.toGrid ∨ c ∈ (edge h b).headHeights := by
  cases h with
  | false => exact .inl (by simpa using hc)
  | true =>
    simp only [edge_true, promote, toGrid, List.map_map,
      List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    by_cases hs : x.onSpine = true
    · refine .inr ?_
      simp only [edge_true, headHeights_promote, List.mem_map]
      exact ⟨x.height, List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, hs⟩, rfl⟩, by simp [hs]⟩
    · simp only [Bool.not_eq_true] at hs
      exact .inl (List.mem_map.mpr ⟨x, hx, by simp [hs]⟩)

theorem col_le_two_or_head {t : Tree} (hw : IsWord t) (hr : noRec t = 0) :
    ∀ c ∈ columns t, c ≤ 2 ∨ c ∈ headHeights t := by
  obtain ⟨a, cs⟩ := t
  obtain ⟨ha, hchild⟩ := isWord_children hw hr
  have hσ : a.level ≠ .syl := by rw [ha]; decide
  intro c hc
  rw [columns_node, ite_eq_right (by simp [hσ]), List.mem_flatMap] at hc
  obtain ⟨ch, hch, hc⟩ := hc
  rcases mem_toGrid_edge hc with hcol | hhead
  · exact .inl (le_trans (toGrid_bounds c hcol).2 (height_word_child_le (hchild ch hch)))
  · refine .inr ?_
    rw [headHeights_node, ite_eq_right (by simp [hσ]), List.mem_flatMap]
    exact ⟨ch, hch, by rwa [headHeights_edge] at hhead⟩

theorem two_le_head {t : Tree} (hw : IsWord t) (hr : noRec t = 0)
    {h : ℕ} (hh : h ∈ headHeights t) : 2 ≤ h := by
  obtain ⟨a, cs⟩ := t
  obtain ⟨ha, _⟩ := isWord_children hw hr
  have hσ : a.level ≠ .syl := by rw [ha]; decide
  rw [headHeights_node, ite_eq_right (by simp [hσ]), List.mem_flatMap] at hh
  obtain ⟨ch, hch, hh⟩ := hh
  split at hh
  · obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hh
    have : 1 ≤ h' := (toGrid_bounds h' ((headHeights_sublist_columns ch).subset hh')).1
    omega
  · exact absurd hh List.not_mem_nil

theorem headHeights_eq_peak {t : Tree} (hw : IsWord t) (hh : IsHeaded t) (hr : noRec t = 0) :
    headHeights t = [peak (columns t)] := by
  obtain ⟨v, hv⟩ := List.length_eq_one_iff.mp hh
  have hvmem : v ∈ headHeights t := by rw [hv]; exact List.mem_singleton_self v
  have hge : peak (columns t) ≤ v := by
    refine peak_le fun c hc => ?_
    rcases col_le_two_or_head hw hr c hc with h2 | hmem
    · have := two_le_head hw hr hvmem; omega
    · rw [hv, List.mem_singleton] at hmem; omega
  rw [hv, le_antisymm (headHeight_le_peak hvmem) hge]

theorem head_below_peak_under_recursion :
    ∃ t, IsWord t ∧ IsHeaded t ∧ IsCulminative (columns t) ∧ headHeights t ≠ [peak (columns t)] :=
  ⟨.om [.σ 1 true, .om [.ft true [.σ 1 true]]], by decide⟩

theorem head_below_peak_unlayered :
    ∃ t, IsHeaded t ∧ noRec t = 0 ∧ ¬ IsWord t ∧ headHeights t ≠ [peak (columns t)] :=
  ⟨.om [.ph [.ft true [.σ 1 true]], .σ 1 true], by decide⟩

end Tree

end Prosody
