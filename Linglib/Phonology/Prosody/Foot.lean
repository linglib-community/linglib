module

public import Linglib.Phonology.Prosody.Syllable
public import Linglib.Core.Data.RoseTree.Licensed

/-!
# Metrical feet

The canonical metrical foot (Selkirk 1980; Nespor and Vogel 1986; Hayes 1995; Kager 1999) is a
flat, headed constituent over syllable positions: a non-empty, ordered sequence of syllables with
one distinguished `head`, the stressed daughter. Headedness (trochaic or iambic) and binarity are
derived from the structure, not stored, and the moraic versus syllabic split is a reading of
syllable duration, a weight function. The Iambic/Trochaic Law is a condition on that reading:
a trochee's syllables are even in duration and an iamb's head is longer than its dependent. It
follows that a weight-blind reading supports trochees and no iambs, and the light–light iamb,
which Hayes admits as a smaller version of the canonical light–heavy one, violates the law.
Re-representations into the prosodic tree (`Prosody.Tree`) and the metrical grid are functions
that recover the same head.

## Main definitions

* `IsConstituent` — well-formedness at a prosodic level on the prosodic-tree carrier: a tree
  rooted at that level and licensed by the Layeredness relation `Constituent.Licenses`;
  `IsFoot` is the `f` level, an `f`-node over a non-empty list of σ-leaves.
* `Foot` — a headed constituent over syllable positions (`head : Fin _`, so non-empty).
* `Foot.IsTrochaic` / `IsIambic` / `IsBinary` / `IsDegenerate` — derived shape predicates.
* `Foot.moraCount` — mora count under a weight reading (the quantity axis).
* `Foot.IsSyllabicTrochee` / `IsMoraicTrochee` — the trochees of the inventory.
* `Foot.IsEven` / `Foot.ConformsToITL` — even duration, and the Iambic/Trochaic Law.
* `Foot.toProsTree` / `Foot.toGrid` / `Foot.headFlags` — re-representations that preserve the head
  (the prosodic tree, its metrical grid, and its head-flag row).
* `footMorae` — mora count of a `Tree`-extracted weight-list foot (the flat metrical
  parse is now `Prosody.Footing`).
* `Footing.footOffsets` / `Footing.nonBimoraicFeet` — each foot's left-edge position and
  the feet failing bimoraicity: what the alignment and binarity constraints count.

## Main results

* `Foot.conformsToITL_trochee_iff` / `Foot.conformsToITL_iamb_iff` — a binary trochee conforms
  to the Iambic/Trochaic Law iff it is even, a binary iamb iff its head is the longer syllable.
* `Foot.IsBinary.conformsToITL_const_iff` — under a weight-blind reading the binary feet that
  conform are exactly the trochees: there is no syllabic iamb.
* `Foot.not_conformsToITL_iamb_of_eq` — the even iamb, light–light among them, violates the law.
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
instance (f : Foot S) : Decidable f.IsSyllabicTrochee := by
  unfold IsSyllabicTrochee; infer_instance
instance (w : S → ℕ) (f : Foot S) : Decidable (IsMoraicTrochee w f) := by
  unfold IsMoraicTrochee; infer_instance

/-! ### The Iambic/Trochaic Law

By the Iambic/Trochaic Law ([hayes-1985], after Bolton 1894) elements contrasting in intensity
group with initial prominence and elements contrasting in duration with final prominence. On
feet ([hayes-1995] §4.5.2) a trochee consists of units equal in duration, syllables for the
syllabic trochee and morae for the moraic one, and the canonical iamb concatenates a light
syllable with a heavy one. The law is a condition on a reading `w` of syllable duration, a
constant one for syllabic counting and the mora count for moraic counting, and not part of the
definition of a foot. -/

/-- A foot is **even** under the duration reading `w` when its syllables have equal duration. -/
def IsEven (w : S → ℕ) (f : Foot S) : Prop := ∀ a ∈ f.syllables, ∀ b ∈ f.syllables, w a = w b

instance (w : S → ℕ) (f : Foot S) : Decidable (f.IsEven w) := by
  unfold IsEven; infer_instance

/-- A foot **conforms to the Iambic/Trochaic Law** under the duration reading `w` when a trochee
is even and an iamb's head is longer than each of its other syllables ([hayes-1995] (33),
§4.5.2). -/
def ConformsToITL (w : S → ℕ) (f : Foot S) : Prop :=
  (f.IsTrochaic → f.IsEven w) ∧
    (f.IsIambic → ∀ i, i ≠ f.head → w (f.syllables.get i) < w (f.syllables.get f.head))

instance (w : S → ℕ) (f : Foot S) : Decidable (f.ConformsToITL w) := by
  unfold ConformsToITL IsTrochaic IsIambic; infer_instance

section ITL

variable {w : S → ℕ} {a b : S}

@[simp] theorem isTrochaic_trochee : (trochee a b).IsTrochaic := rfl
@[simp] theorem not_isIambic_trochee : ¬ (trochee a b).IsIambic :=
  fun h ↦ absurd (show (0 : ℕ) + 1 = 2 from h) (by decide)
@[simp] theorem isIambic_iamb : (iamb a b).IsIambic := rfl
@[simp] theorem not_isTrochaic_iamb : ¬ (iamb a b).IsTrochaic :=
  fun h ↦ absurd (show (1 : ℕ) = 0 from h) (by decide)

theorem conformsToITL_trochee_iff : (trochee a b).ConformsToITL w ↔ w a = w b := by
  refine ⟨fun h ↦ h.1 rfl a (by simp [trochee]) b (by simp [trochee]),
    fun h ↦ ⟨fun _ ↦ ?_, fun h' ↦ absurd h' not_isIambic_trochee⟩⟩
  simp [IsEven, trochee, h]

theorem conformsToITL_iamb_iff : (iamb a b).ConformsToITL w ↔ w a < w b := by
  refine ⟨fun h ↦ h.2 rfl ⟨0, by simp [iamb]⟩ (by simp [iamb, Fin.ext_iff]),
    fun h ↦ ⟨fun h' ↦ absurd h' not_isTrochaic_iamb, fun _ i hi ↦ ?_⟩⟩
  obtain ⟨_ | _ | i, hi'⟩ := i
  · exact h
  · exact absurd rfl hi
  · simp [iamb] at hi'; omega

/-- An even iamb violates the Iambic/Trochaic Law: it has final prominence without a contrast in
duration. The light–light iamb, a smaller version of the canonical light–heavy one in Hayes'
inventory, is one ([hayes-1995] p. 82). -/
theorem not_conformsToITL_iamb_of_eq (h : w a = w b) : ¬ (iamb a b).ConformsToITL w := by
  rw [conformsToITL_iamb_iff, h]
  exact lt_irrefl _

/-- A binary foot is a trochee or an iamb. -/
theorem IsBinary.eq_trochee_or_eq_iamb {f : Foot S} (hf : f.IsBinary) :
    ∃ a b, f = trochee a b ∨ f = iamb a b := by
  obtain ⟨syls, head⟩ := f
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hf
  obtain ⟨_ | _ | i, hi⟩ := head
  · exact ⟨a, b, .inl rfl⟩
  · exact ⟨a, b, .inr rfl⟩
  · simp at hi; omega

/-- Under a weight-blind reading, a binary foot conforms to the Iambic/Trochaic Law exactly when
it is a trochee: the law supports the syllabic trochee and no syllabic iamb. -/
theorem IsBinary.conformsToITL_const_iff {f : Foot S} (hf : f.IsBinary) (c : ℕ) :
    f.ConformsToITL (fun _ ↦ c) ↔ f.IsTrochaic := by
  obtain ⟨a, b, rfl | rfl⟩ := hf.eq_trochee_or_eq_iamb
  · simp [conformsToITL_trochee_iff]
  · simp [conformsToITL_iamb_iff]

/-- A binary moraic trochee over syllables of positive duration is light–light, so it conforms to
the Iambic/Trochaic Law. -/
theorem IsMoraicTrochee.conformsToITL_trochee (h : (trochee a b).IsMoraicTrochee w)
    (ha : 0 < w a) (hb : 0 < w b) : (trochee a b).ConformsToITL w := by
  have h2 : w a + w b = 2 := by simpa [moraCount, trochee] using h.2
  exact conformsToITL_trochee_iff.2 (by omega)

end ITL

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
example : (Foot.monosyllable 2 : Foot ℕ).IsMoraicTrochee id := by decide
-- Under moraic counting the light–heavy iamb conforms to the Iambic/Trochaic Law, and the
-- heavy–light trochee and the light–light iamb do not.
example : (Foot.iamb 1 2 : Foot ℕ).ConformsToITL id := by decide
example : ¬ (Foot.trochee 2 1 : Foot ℕ).ConformsToITL id := by decide
example : ¬ (Foot.iamb 1 1 : Foot ℕ).ConformsToITL id := by decide
example : (Foot.monosyllable 0).IsDegenerate := by decide

-- The re-representations recover the head: a trochee marks position 0, an iamb 1.
example : Foot.headFlags (Foot.trochee 1 1) = [true, false] := by decide
example : Foot.headFlags (Foot.iamb 1 1) = [false, true] := by decide
-- ...and the grid peaks at the head: `2` there, `1` elsewhere.
example : Foot.toGrid (Foot.trochee 1 1) = [2, 1] := by decide
example : Foot.toGrid (Foot.iamb 1 1) = [1, 2] := by decide

end Prosody
