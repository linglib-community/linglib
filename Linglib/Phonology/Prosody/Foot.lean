module

public import Linglib.Phonology.Prosody.Syllable
public import Linglib.Core.Data.RoseTree.Licensed

/-!
# Metrical feet

The canonical metrical foot (Selkirk 1980; Nespor and Vogel 1986; Hayes 1995; Kager 1999) is a
flat, headed constituent over syllable positions: a non-empty, ordered sequence of syllables with
one distinguished `head`, the stressed daughter. Headedness (trochaic or iambic), binarity, and the
trochee, iamb and moraic inventory are derived from the structure, not stored, and the moraic
versus syllabic split is a counting parameter on `moraCount`. Re-representations into the
prosodic tree (`Prosody.Tree`) and the metrical grid are functions that recover the same head.

## Main definitions

* `IsConstituent` — well-formedness at a prosodic level on the prosodic-tree carrier: a tree
  rooted at that level and licensed by the Layeredness relation `Constituent.Licenses`;
  `IsFoot` is the `f` level, an `f`-node over a non-empty list of σ-leaves.
* `Foot` — a headed constituent over syllable positions (`head : Fin _`, so non-empty).
* `Foot.IsTrochaic` / `IsIambic` / `IsBinary` / `IsDegenerate` — derived shape predicates.
* `Foot.moraCount` — mora count under a weight reading (the quantity axis).
* `Foot.IsSyllabicTrochee` / `IsMoraicTrochee` / `IsCanonicalIamb` — the *derived* inventory.
* `Foot.toProsTree` / `Foot.toGrid` / `Foot.headFlags` — re-representations that preserve the head
  (the prosodic tree, its metrical grid, and its head-flag row).
* `footMorae` — mora count of a `Tree`-extracted weight-list foot (the flat metrical
  parse is now `Prosody.Footing`).
* `Footing.footOffsets` / `Footing.nonBimoraicFeet` — each foot's left-edge position and
  the feet failing bimoraicity: what the alignment and binarity constraints count.

## Main results

* `Foot.itl_gap` — the Iambic/Trochaic Law (Hayes 1985): a binary iamb need not be
  weight-blind-characterizable, unlike a binary (syllabic) trochee.
* `Foot.headFlags_toProsTree` — the prosodic-tree re-representation carries the same
  head profile as `headFlags` (head-preservation, the functorial spine).
* `Foot.isFoot_toProsTree` — every `Foot`'s prosodic tree is a well-formed foot tree
  (`IsFoot`): the functoriality/well-formedness bridge onto the carrier.

## References

* [selkirk-1980]
* [nespor-vogel-1986]
* [hayes-1985]
* [hayes-1995]
* [kager-1999]
* [kager-2007]
* [ito-mester-2003]
* [martinez-paricio-kager-2015]
* [lamont-2022c]
-/

@[expose] public section

namespace Prosody

/-! ### Carrier well-formedness -/

/-- A well-formed prosodic constituent at the level `ℓ` is a tree rooted in an `ℓ`-node and
licensed by `Constituent.Licenses`, so every node dominates only the levels Layeredness allows
under it. -/
def IsConstituent (ℓ : Level) (t : Tree) : Prop :=
  t.value.level = ℓ ∧ t.Licensed Constituent.Licenses

instance (ℓ : Level) (t : Tree) : Decidable (IsConstituent ℓ t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A well-formed foot is a licensed tree rooted in an `f`-node, so an `f`-node dominating a
    non-empty list of σ-leaves, the inviolable Layeredness and σ-Headedness core
    ([selkirk-1980]; [hayes-1995]). Foot binarity (FtBin) and recursive internally-layered feet
    (contested, Golston 2021 against [martinez-paricio-kager-2015]) are violable and deferred;
    these are flat feet, the sibling of `IsWord`'s Layeredness. -/
abbrev IsFoot : Tree → Prop := IsConstituent .ft

theorem IsFoot.syl_leaf {t : Tree} (h : IsFoot t) {c : Tree} (hc : c ∈ t.children) :
    c.value.level = .syl ∧ c.children = [] := by
  rcases t with ⟨a, cs⟩
  obtain ⟨hft, hl⟩ := h
  obtain ⟨b, rfl⟩ : ∃ b, a = .ft b := by cases a <;> simp_all [Constituent.level]
  have hsyl := (RoseTree.licensed_node_iff.mp hl).1.2 c.value (List.mem_map_of_mem hc)
  refine ⟨hsyl, ?_⟩
  rcases c with ⟨cl, ccs⟩
  obtain ⟨w, h', rfl⟩ : ∃ w h', cl = .syl w h' := by cases cl <;> simp_all [Constituent.level]
  simpa [Constituent.Licenses] using (RoseTree.licensed_node_iff.mp (hl.of_mem hc)).1

-- A σ-leaf is a non-`f` node, so not a foot; a flat `f`-node over a σ-leaf is one.
example : ¬ IsFoot (.node (.syl 2) []) := by decide
example : IsFoot (.node .ft [.node (.syl 2) []]) := by decide

/-! ### The canonical foot -/

/-- The canonical metrical foot ([selkirk-1980]; [hayes-1995]; [kager-1999]) is a non-empty,
    ordered sequence of syllable positions with one distinguished `head`, the stressed
    daughter. The `Fin` index forces non-emptiness by construction.
    The inventory and headedness are derived below, not stored. -/
structure Foot (S : Type*) where
  /-- The dominated syllable positions, left to right. -/
  syllables : List S
  /-- The distinguished (stressed) daughter; the `Fin` index forces non-emptiness. -/
  head      : Fin syllables.length
  deriving DecidableEq, Repr

namespace Foot
variable {S : Type*}

/-- The number of dominated syllables. -/
def length (f : Foot S) : ℕ := f.syllables.length

/-- A monosyllabic foot `(σ́)`. -/
def monosyllable (a : S) : Foot S := ⟨[a], 0⟩
/-- A head-initial disyllable `(σ́σ)` — trochaic. -/
def trochee (a b : S) : Foot S := ⟨[a, b], 0⟩
/-- A head-final disyllable `(σσ́)` — iambic. -/
def iamb (a b : S) : Foot S := ⟨[a, b], 1⟩

/-! ### Derived shape predicates -/

/-- Head-initial (trochaic). -/
def IsTrochaic (f : Foot S) : Prop := f.head.val = 0
/-- Head-final (iambic). -/
def IsIambic (f : Foot S) : Prop := f.head.val + 1 = f.syllables.length
/-- A binary (disyllabic) foot. -/
def IsBinary (f : Foot S) : Prop := f.syllables.length = 2
/-- A degenerate (monosyllabic) foot. -/
def IsDegenerate (f : Foot S) : Prop := f.syllables.length = 1

instance (f : Foot S) : Decidable f.IsTrochaic := by unfold IsTrochaic; infer_instance
instance (f : Foot S) : Decidable f.IsIambic := by unfold IsIambic; infer_instance
instance (f : Foot S) : Decidable f.IsBinary := by unfold IsBinary; infer_instance
instance (f : Foot S) : Decidable f.IsDegenerate := by unfold IsDegenerate; infer_instance

theorem not_trochaic_and_iambic (f : Foot S) (h : 1 < f.syllables.length) :
    ¬ (f.IsTrochaic ∧ f.IsIambic) := by
  rintro ⟨ht, hi⟩
  unfold IsTrochaic at ht; unfold IsIambic at hi; omega

/-! ### Quantity and the derived inventory -/

/-- Mora count under a weight reading `w` — the quantity axis the moraic/syllabic
    split parameterizes (`FtBin`-by-μ). -/
def moraCount (w : S → ℕ) (f : Foot S) : ℕ := (f.syllables.map w).sum

/-- A syllabic trochee `(σ́σ)` is head-initial and binary, weight-blind ([hayes-1995]). -/
def IsSyllabicTrochee (f : Foot S) : Prop := f.IsTrochaic ∧ f.IsBinary
/-- A moraic trochee `(H)` or `(LL)` is head-initial and bimoraic ([hayes-1995]). -/
def IsMoraicTrochee (w : S → ℕ) (f : Foot S) : Prop := f.IsTrochaic ∧ moraCount w f = 2
/-- A canonical iamb over Hayes' right-prominent inventory `{(H),(LL),(LH)}` ([hayes-1995]) is
    head-final, and either a bimoraic monosyllable or an even or right-heavy bimoraic or trimoraic
    disyllable. Unlike the trochee, the iamb references weight — the
    quantity-sensitivity the Iambic/Trochaic Law predicts. -/
def IsCanonicalIamb (w : S → ℕ) (f : Foot S) : Prop :=
  f.IsIambic ∧
    ((f.length = 1 ∧ moraCount w f = 2) ∨
     (f.length = 2 ∧ 2 ≤ moraCount w f ∧ moraCount w f ≤ 3 ∧
       (f.syllables.map w).headD 0 ≤ (f.syllables.map w).getLast?.getD 0))

instance (f : Foot S) : Decidable f.IsSyllabicTrochee := by
  unfold IsSyllabicTrochee; infer_instance
instance (w : S → ℕ) (f : Foot S) : Decidable (IsMoraicTrochee w f) := by
  unfold IsMoraicTrochee; infer_instance
instance (w : S → ℕ) (f : Foot S) : Decidable (IsCanonicalIamb w f) := by
  unfold IsCanonicalIamb; infer_instance

/-- By **the Iambic/Trochaic Law** ([hayes-1985], after Bolton 1894) a binary iamb is not
    characterizable weight-blind, since the head-final binary cell admits the left-heavy `(H L̗)`
    that Hayes' canonical inventory excludes, whereas a binary trochee is exactly
    `IsSyllabicTrochee` (weight-blind). The witness is `(H L̗)`. -/
theorem itl_gap : ∃ f : Foot ℕ, (f.IsIambic ∧ f.IsBinary) ∧ ¬ IsCanonicalIamb id f :=
  ⟨Foot.iamb 2 1, by decide⟩

/-! ### Re-representations (preserving the head) -/

/-- As a prosodic tree ([selkirk-1980]; [ito-mester-2003]) a foot is a depth-1 `.f` node over
    `.σ` leaves, the head σ marked via `Constituent.isHead`. The `.f` node
    itself is marked `isHead` when the foot heads its ω (the `isHead` argument, set by the
    caller building the word tree). -/
def toProsTree (w : S → Syllable.Weight) (f : Foot S) (isHead : Bool := false) : Tree :=
  .node (.ft isHead) ((List.finRange f.syllables.length).map (fun i =>
    .node (.syl (w (f.syllables.get i)) (decide (i = f.head))) []))

/-- In the **metrical grid** of a foot in isolation ([hayes-1995]) the head σ carries `2` grid
    marks and every other σ `1`. -/
def toGrid (f : Foot S) : List ℕ :=
  (List.finRange f.syllables.length).map (fun i => if i = f.head then 2 else 1)

/-- The σ-leaves' **head flags** are `true` at the head σ and `false` elsewhere ([hayes-1995]). -/
def headFlags (f : Foot S) : List Bool :=
  (List.finRange f.syllables.length).map (fun i => decide (i = f.head))

/-- The σ-leaves' head flags read off a tree. -/
def childHeadFlags : Tree → List Bool
  | .node _ cs => cs.map (fun | .node a _ => a.isHead)

@[simp] theorem toGrid_length (f : Foot S) :
    (toGrid f).length = f.syllables.length := by simp [toGrid]

/-- The two re-representations carry the **same head profile**, since the prosodic tree's σ-leaf
    head flags are exactly `headFlags f`, so both recover the foot's head. -/
theorem headFlags_toProsTree (w : S → Syllable.Weight) (f : Foot S) :
    childHeadFlags (toProsTree w f) = headFlags f := by
  simp [childHeadFlags, toProsTree, headFlags, List.map_map, Function.comp, Constituent.isHead]

/-- A `Foot` record's prosodic-tree re-representation is always a well-formed foot tree, since
    `toProsTree` lands in the depth-1 f/σ band that `IsFoot` carves out. With `headFlags_toProsTree`
    (head-preservation) this is the load-bearing half of the `Foot S ≃ {t // IsFoot t}`
    embedding that bridges footing-on-`Foot` to OT-on-`Tree`. -/
theorem isFoot_toProsTree (w : S → Syllable.Weight) (f : Foot S) :
    IsFoot (f.toProsTree w) := by
  have hpos : 0 < f.syllables.length := f.head.pos
  refine ⟨rfl, RoseTree.licensed_node_iff.mpr ⟨⟨?_, ?_⟩, ?_⟩⟩
  · simpa [List.finRange_eq_nil_iff] using hpos.ne'
  · simp [Constituent.level]
  · simp [Constituent.Licenses]

end Foot

/-! ### Foot mora count -/

/-- Mora count of a foot given as a weight-list (each weight *is* a mora count). The
    moraic measure for `Tree`-extracted feet (`Prosody.feet`, in `Word.lean`); for a
    headed `Foot S`, use `Foot.moraCount`. -/
def footMorae (ws : List Syllable.Weight) : Nat :=
  ws.foldl (· + ·) 0

/-! ### Footings
[lamont-2022c] [kager-2007]

A **footing**: a flat parse into feet and stray (unfooted) syllables, no designated head
([lamont-2022c]); the σ-type `S` carries quantity (`Unit` insensitive, `Syllable.Weight` not).
A prosodic word ω (an `IsWord` tree, `Prosody/Word.lean`) is the headed refinement of a
footing. -/

/-- A footing is a flat sequence of feet and stray (unfooted) syllables, with no designated head
    ([lamont-2022c]). -/
abbrev Footing (S : Type*) := List (Foot S ⊕ S)

namespace Footing
variable {S : Type*} (fc : Footing S)

/-- The feet, left to right. -/
def feet : List (Foot S) := fc.filterMap Sum.getLeft?

/-- The stray (unfooted) syllables, left to right. -/
def strays : List S := fc.filterMap Sum.getRight?

/-- The total number of syllables, footed and stray. -/
def size : Nat := (fc.map (Sum.elim Foot.length (fun _ => 1))).sum

/-- The `Parse(σ)` violation profile ([lamont-2022c]) is `1` at each stray σ and `0` at each
    footed one. -/
def strayMarks : List Nat := fc.flatMap (Sum.elim (List.replicate ·.length 0) (fun _ => [1]))

/-! ### Foot positions and quantity

The structural readings the metrical alignment and binarity constraints count
([kager-2007]): ALL-FT-LEFT is `footOffsets.sum`, ALL-FT-RIGHT the same on the reversed
footing, FT-BIN(μ) the length of `nonBimoraicFeet`, and PARSE-SYL the length of `strays`. -/

/-- The left-edge position of each foot, in syllables from the left edge of the footing. -/
def footOffsets : List ℕ :=
  (fc.foldl (fun (acc : List ℕ × ℕ) x =>
    Sum.elim (fun f => (acc.1 ++ [acc.2], acc.2 + f.length)) (fun _ => (acc.1, acc.2 + 1)) x)
    ([], 0)).1

/-- The feet that are not bimoraic under the weight reading `w` (for the syllabic reading,
read every syllable as one mora). -/
def nonBimoraicFeet (w : S → ℕ) (fc : Footing S) : List (Foot S) :=
  fc.feet.filter fun f => f.moraCount w ≠ 2

end Footing

/-! ### Worked examples -/

-- Inventory falls out of the derived predicates (no `FootType` enum).
example : (Foot.trochee 1 1).IsSyllabicTrochee := by decide
example : (Foot.trochee 2 0 : Foot ℕ).IsMoraicTrochee id := by decide
example : (Foot.iamb 1 2 : Foot ℕ).IsCanonicalIamb id := by decide
example : ¬ (Foot.iamb 2 1 : Foot ℕ).IsCanonicalIamb id := by decide
example : (Foot.monosyllable 0).IsDegenerate := by decide

-- The re-representations recover the head: a trochee marks position 0, an iamb 1.
example : Foot.headFlags (Foot.trochee 1 1) = [true, false] := by decide
example : Foot.headFlags (Foot.iamb 1 1) = [false, true] := by decide
-- ...and the grid peaks at the head: `2` there, `1` elsewhere.
example : Foot.toGrid (Foot.trochee 1 1) = [2, 1] := by decide
example : Foot.toGrid (Foot.iamb 1 1) = [1, 2] := by decide

end Prosody
