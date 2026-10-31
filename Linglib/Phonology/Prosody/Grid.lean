module

public import Linglib.Phonology.Prosody.Word
public import Mathlib.Data.List.MinMax

/-!
# The metrical grid

The *metrical grid* of [hayes-1995] represents the rhythm of a word as a column of beats over
each syllable, a taller column standing for greater relative prominence. `Grid` records the
column heights, `Marks` renders them as rows of marks, and `MarkedGrid` adds to each column
whether it lies on the head spine. `Tree.project` reads a marked grid off a prosodic tree: a
syllable is a column of height one, and across each head edge the columns on the head spine gain
a mark, so that on a non-recursive headed word the terminal that head edges alone lead to, the
designated terminal element of [liberman-prince-1977], is the tallest column
(`Tree.headHeights_eq_peak`). A rendered grid satisfies the Continuous Column Constraint of
[prince-1983] and [hayes-1995], that no column has a gap (`Grid.rows_isContinuous`). The grid
forgets the constituency that Hayes's bracketed grid retains (`Grid.ofTree_not_injective`), and
under the recursive words of [ito-mester-2009] two columns can tie for the peak
(`Tree.not_culminative_under_recursion`) or the peak can be a column other than the head
terminal (`Tree.head_below_peak_under_recursion`).

## Main definitions

* `Grid`, `Grid.peak`, `Grid.IsCulminative`: column heights, the tallest height, and the
  property that exactly one column is tallest.
* `Marks`, `Marks.IsContinuous`, `Grid.rows`: rows of marks, the Continuous Column Constraint,
  and the rendering of a grid as rows.
* `MarkedGrid`, `Tree.project`: columns that carry a head-spine flag, and the marked grid of a
  prosodic tree.
* `Tree.columns`, `Tree.headTerminals`, `Tree.headHeights`, `Tree.IsHeaded`: the grid of a tree,
  its head terminals, their heights, and the property of having exactly one head terminal.

## Main statements

* `Grid.rows_isContinuous`: every rendered grid satisfies the Continuous Column Constraint.
* `Grid.isCulminative_of_forall_lt`: a column strictly taller than every other makes a grid
  culminative.
* `Tree.peak_toProsTree`: the grid of a foot peaks at height two, over its head syllable.
* `Tree.headHeights_eq_peak`: on a non-recursive headed word, the height of the head terminal is
  the peak of the grid.
* `Grid.ofTree_not_injective`: distinct trees can render the same grid.
* `Tree.not_culminative_under_recursion`: a word recursively dominating a word need not be
  culminative.
* `Tree.head_below_peak_under_recursion`, `Tree.head_below_peak_unlayered`: under recursion, or
  without Layeredness, the peak can be a column other than the head terminal.

## Implementation notes

* `Tree.project` is a fold over the tree built from `MarkedGrid.cell`, `juxtapose`, `promote`,
  and `clear`; each reader of a tree is computed from its marked grid, and `Tree.columns_node`
  and its siblings give the recursions on a node.
* Absolute heights carry no significance, as [prince-1983] notes; the statements concern the
  peak and the relative heights of columns.
* Culminativity concerns the grid alone and differs from `Tree.IsHeaded`, a unique head
  terminal: both can hold while the head terminal is not the peak
  (`Tree.head_below_peak_under_recursion`).

## References

* [M. Liberman and A. Prince, *On Stress and Linguistic Rhythm* (1977)][liberman-prince-1977]
* [A. Prince, *Relating to the Grid* (1983)][prince-1983]
* [B. Hayes, *Metrical Stress Theory: Principles and Case Studies* (1995)][hayes-1995]
* [J. Itô and A. Mester, *The Extended Prosodic Word* (2009)][ito-mester-2009]
-/

@[expose] public section

namespace Prosody

/-! ### The three carriers

The rendered `Marks`, the `Grid` of column heights, and the `MarkedGrid` built from `Column`s;
the operations on each follow in its namespace. -/

/-- A rendered metrical grid: a list of rows of marks, bottom row first. -/
abbrev Marks := List (List Bool)

/-- A metrical grid ([hayes-1995] §3.2) records the number of beats, the column height, over each
    position, left to right. -/
abbrev Grid := List ℕ

/-- One column of a marked grid records the syllable leaf it stands over, its number of marks,
    and whether it lies on the head spine, the path of head edges from the current node. -/
structure Column (α : Type*) where
  /-- The syllable leaf under this column. -/
  terminal : α
  /-- The column height, the number of grid marks. -/
  height : ℕ
  /-- Whether this column lies on the head spine of the current node. -/
  onSpine : Bool

/-- A grid whose columns carry a head-spine flag, so that the designated terminal elements of
    [liberman-prince-1977] can be read off it. It records no further bracketing. -/
abbrev MarkedGrid (α : Type*) := List (Column α)

/-! ### Marks and the Continuous Column Constraint -/

namespace Marks

/-- Whether one row is a submask of the row below. -/
def rowSubmask (upper lower : List Bool) : Bool :=
  (upper.zip lower).all (fun p => !p.1 || p.2)

/-- The Continuous Column Constraint ([prince-1983]; [hayes-1995] §3.4.2, (9)): no column has a
    gap, so that a mark on one row stands over a mark on the row below. -/
def IsContinuous (m : Marks) : Prop :=
  m.IsChain (fun lower upper => rowSubmask upper lower = true)

instance (m : Marks) : Decidable (IsContinuous m) := by unfold IsContinuous; infer_instance

/-- Read column by column, continuity says that a mark in a row sits over a mark in the row
    below. -/
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

/-! ### The marked grid and its operations -/

namespace MarkedGrid
variable {α : Type*} (b : MarkedGrid α) (bs : List (MarkedGrid α))

/-- The grid of column heights, forgetting the head-spine flags. -/
def toGrid : Grid := b.map (·.height)

/-- The terminals under the columns, left to right. -/
def terminals : List α := b.map (·.terminal)

/-- The heights of the columns on the head spine. -/
def headHeights : Grid := (b.filter (·.onSpine)).map (·.height)

/-- The terminals of the columns on the head spine. -/
def headTerminals : List α := (b.filter (·.onSpine)).map (·.terminal)

/-- A single terminal: one column of height `1`, on the head spine. -/
def cell (x : α) : MarkedGrid α := [⟨x, 1, true⟩]

/-- The grid of sibling constituents side by side. -/
def juxtapose : MarkedGrid α := bs.flatten

/-- Across a head edge every column on the head spine gains one mark. -/
def promote : MarkedGrid α :=
  b.map fun c => { c with height := c.height + if c.onSpine then 1 else 0 }

/-- Across a non-head edge heights are unchanged and no column remains on the head spine. -/
def clear : MarkedGrid α := b.map fun c => { c with onSpine := false }

/-- The grid of a child seen from its parent: promoted across a head edge, cleared across any
    other. -/
def edge (isHead : Bool) (b : MarkedGrid α) : MarkedGrid α :=
  if isHead then b.promote else b.clear

@[simp] theorem edge_true : edge true b = b.promote := rfl
@[simp] theorem edge_false : edge false b = b.clear := rfl

/-! ### The readers of the marked grid on its operations -/

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

/-! ### The grid: peak, culminativity, and rendering -/

namespace Grid

variable {g : Grid}

/-- The *peak* of a grid is the height of its tallest column. -/
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

/-- A grid is *culminative* when exactly one column is tallest, which is culminativity in the
    sense of [hayes-1995] read on the grid. -/
def IsCulminative (g : Grid) : Prop := g.countP (· == peak g) = 1

instance (g : Grid) : Decidable (IsCulminative g) := by unfold IsCulminative; infer_instance

/-- A column strictly taller than every other is the unique peak. -/
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

/-- Two columns at the peak of a culminative grid are the same column. -/
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

/-- The rendering of a grid as rows of marks: row `r` has a mark over every column taller than
    `r`. -/
def rows (g : Grid) : Marks := (List.range (peak g)).map (fun r => g.map (r < ·))

@[simp] theorem length_rows : (rows g).length = peak g := by simp [rows]

@[simp] theorem length_getElem_rows {r : ℕ} (hr : r < (rows g).length) :
    (rows g)[r].length = g.length := by simp [rows]

@[simp] theorem getElem_rows {r i : ℕ} (hr : r < (rows g).length) (hi : i < (rows g)[r].length) :
    (rows g)[r][i] = decide (r < g[i]'(by simpa using hi)) := by simp [rows]

/-- Every rendered grid satisfies the Continuous Column Constraint. -/
theorem rows_isContinuous (g : Grid) : Marks.IsContinuous (rows g) := by
  rw [Marks.IsContinuous, rows, List.isChain_map, List.isChain_iff_getElem]
  intro i _
  simp only [List.getElem_range, Marks.rowSubmask, List.zip_map', List.all_map, List.all_eq_true]
  intro h _
  by_cases hr : i + 1 < h <;> simp [hr]
  omega

end Grid

/-! ### The marked grid of a tree -/

namespace Tree

open MarkedGrid Grid

/-- One step of `project` pairs the node's label with its grid, so that a parent can read the
    head flag off each child. -/
def projectStep (a : Constituent) (ps : List (Constituent × MarkedGrid Tree)) :
    Constituent × MarkedGrid Tree :=
  (a, if a.level = .syl ∧ ps = [] then cell (.node a [])
      else juxtapose (ps.map fun p => edge p.1.isHead p.2))

/-- The marked grid of a tree: a syllable leaf is one `cell`, and any other node juxtaposes its
    children's grids, promoted across head edges and cleared across the rest, so that heights
    record the relative prominence that the Relative Prominence Projection Rule of
    [liberman-prince-1977] assigns to designated terminal elements. -/
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

/-! ### Reading the grid off a tree -/

variable (t : Tree)

/-- The syllable leaves of a tree, left to right: the terminals the grid stands over. -/
def terminals : List Tree := (project t).terminals

/-- The column heights of the grid of a tree. -/
def columns : Grid := (project t).toGrid

/-- The *head terminals* of a tree: the syllable leaves that head edges alone lead to from the
    root (`headTerminal_sound`), the designated terminal elements of [liberman-prince-1977]. -/
def headTerminals : List Tree := (project t).headTerminals

/-- The heights of the columns over the head terminals. -/
def headHeights : Grid := (project t).headHeights

/-- A tree is *headed* when it has exactly one head terminal. -/
def IsHeaded : Prop := (headHeights t).length = 1

instance : Decidable (IsHeaded t) := by unfold IsHeaded; infer_instance

/-- The metrical grid of a tree, rendered as rows of marks. -/
def _root_.Prosody.Grid.ofTree : Marks := (columns t).rows

/-- The rendered grid of a tree satisfies the Continuous Column Constraint, by
    `Grid.rows_isContinuous`. -/
theorem _root_.Prosody.Grid.ofTree_isContinuous : Marks.IsContinuous (Grid.ofTree t) :=
  rows_isContinuous _

/-! ### The readers on a node

Each reader is computed from the marked grid, so on a node it is the juxtaposition of the
children's readings across head edges. -/

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

/-! ### The head terminals are the leaves of all-head descents -/

/-- `leaf` is a head terminal of `t`: it is reached from the root by head edges alone. -/
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

/-! ### The grid of a foot

The grid of a foot has height `2` over the head syllable and `1` elsewhere
(`columns_toProsTree`), so that it peaks at `2`. -/

theorem columns_toProsTree {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    columns (f.toProsTree w) = Foot.toGrid f := by
  rw [Foot.toProsTree, columns_node, ite_eq_right (by simp [Constituent.level]),
      List.flatMap_map, Foot.toGrid, List.map_eq_flatMap]
  refine List.flatMap_congr fun i _ => ?_
  by_cases hi : i = f.head <;>
    simp [project_node, Constituent.level, Constituent.isHead, edge,
      promote, clear, toGrid, cell, hi]

/-- The grid of a foot peaks at `2`, over its head syllable. -/
theorem peak_toProsTree {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    peak (columns (f.toProsTree w)) = 2 := by
  rw [columns_toProsTree, Foot.toGrid]
  refine Nat.le_antisymm (peak_le fun x hx => ?_) (le_peak ?_)
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; split <;> decide
  · exact List.mem_map.mpr ⟨f.head, List.mem_finRange _, by simp⟩

/-! ### What the grid forgets

The grid of a tree drops its constituency (`Grid.ofTree_not_injective`), which is why
[hayes-1995] §3.8 argues for bracketing structure on indirect grounds, since bracketing has no
directly observable correlate; and under recursion the grid need not be culminative
(`not_culminative_under_recursion`). -/

/-- Rendering is not injective: a word whose syllable is footed and one whose syllable is not
    render the same grid. -/
theorem _root_.Prosody.Grid.ofTree_not_injective : ¬ Function.Injective Grid.ofTree :=
  Function.not_injective_iff.mpr
    ⟨.om [.ft false [.σ 1]], .om [.σ 1], by decide⟩

/-- Recursion can break culminativity: a word recursively dominating another word, each heading
    its own syllable, has two equally tall columns and no unique peak. -/
theorem not_culminative_under_recursion : ∃ t : Tree, IsWord t ∧ ¬ IsCulminative (columns t) :=
  ⟨.om [.ft true [.σ 1 true], .om [.ft true [.σ 1 true]]], by decide⟩

/-! ### The peak of a word is its head terminal

On a non-recursive headed word the column over the head terminal is the peak of the grid
(`headHeights_eq_peak`), so that the main stress falls on a syllable that already bears stress,
as [hayes-1995] §3.4.2 (C) observes of the Continuous Column Constraint. -/

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

/-- On a non-recursive headed word, the height of the head terminal is the peak of the grid. -/
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

/-- Under the recursive words of [ito-mester-2009], the peak can be a column other than the head
    terminal, even on a culminative grid. This consequence belongs to the model here, not to the
    source. -/
theorem head_below_peak_under_recursion :
    ∃ t, IsWord t ∧ IsHeaded t ∧ IsCulminative (columns t) ∧ headHeights t ≠ [peak (columns t)] :=
  ⟨.om [.σ 1 true, .om [.ft true [.σ 1 true]]], by decide⟩

/-- Without Layeredness, on a tree that is not a word, the peak can likewise be a column other
    than the head terminal. -/
theorem head_below_peak_unlayered :
    ∃ t, IsHeaded t ∧ noRec t = 0 ∧ ¬ IsWord t ∧ headHeights t ≠ [peak (columns t)] :=
  ⟨.om [.ph [.ft true [.σ 1 true]], .σ 1 true], by decide⟩

end Tree

end Prosody
