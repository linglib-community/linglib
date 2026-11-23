module

public import Linglib.Semantics.Dynamic.Possibility
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Piecewise
public import Mathlib.Order.Closure
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Files

A *file* records what a discourse has established. It has a set of cards `dom`, one for each
individual mentioned so far, and a satisfaction set `sat`, the pairs of a world and a sequence of
individuals that fit every entry. The two are separate data, tied by one condition: the
satisfaction set does not distinguish two points that agree on the cards. So a file says nothing
about an individual it has no card for, and a file that nothing satisfies still has its cards.

Files are ordered by information, `F ≤ G` when `G.dom ⊆ F.dom` and `F.sat ⊆ G.sat`, and they
form a complete lattice. The meet `F ⊓ G` has the cards of both and the points that satisfy both.
The join `F ⊔ G` has the cards they share and the points that agree on those cards with a point
of either. The top is the file with no cards that every point satisfies, and the bottom the file
with every card that no point satisfies. The world set `File.worlds F` is the set of worlds at
which some sequence satisfies `F`, the worlds in which the file is true; a join is true where
either file is (`File.worldsHom`).

The existential closure `F.restrict X` forgets the cards outside `X`, keeping every point that
agrees on `X` with a point of `F`. It is the join of `F` with the file that has the cards in `X`
and no points (`File.restrict_eq_sup`), so it is a closure operator (`File.restrictClosure`); it
is true in the same worlds as `F` (`File.worlds_restrict`), and below a file whose cards lie in
`X` it changes nothing (`File.restrict_le_iff`). The difference `F \ G` keeps the cards of `F`
and the points of `F` that no point of `G` agrees with on those cards. When `G` has no card that
`F` lacks, it is the difference of the satisfaction sets (`File.sat_sdiff_of_dom_subset`).

## Implementation notes

The condition tying `sat` to `dom` is stated for all cards outside `dom` at once, where
[heim-1982]'s principle (B) changes one card at a time. This is the form under which
`F.restrict F.dom = F` (`File.restrict_dom`).

The difference of files is not a co-Heyting difference: `F \ F` keeps the cards of `F`.

The points are those of `Dynamic/Possibility.lean` with total assignments, [heim-1982]'s
world–sequence pairs. The information states of `Dynamic/State.lean` are sets of partial points
with no domain apart from the points, where a state that nothing satisfies makes every referent
both familiar and novel.

## References

* [heim-1982]
-/

@[expose] public section

namespace DynamicSemantics

variable {W V M : Type*}

/-! ### Files -/

/-- A file: a set of cards and the set of points that satisfy it, which does not distinguish
points that agree on the cards. -/
@[ext]
structure File (W V M : Type*) where
  /-- The cards of the file. -/
  dom : Set V
  /-- The satisfaction set: the points that fit every entry of the file. -/
  sat : Set (Possibility W V M)
  /-- A point that agrees on the cards with a point of the satisfaction set belongs to it. -/
  mem_sat_of_eqOn ⦃p q : Possibility W V M⦄ : p.EqOn q dom → p ∈ sat → q ∈ sat

namespace File

variable {ι : Type*} {F G H : File W V M} {X Y : Set V} {p q : Possibility W V M} {x : V}

theorem mem_sat_congr (h : p.EqOn q F.dom) : p ∈ F.sat ↔ q ∈ F.sat :=
  ⟨F.mem_sat_of_eqOn h, F.mem_sat_of_eqOn h.symm⟩

/-- `F ≤ G` when `F` has every card of `G` and every point of `F` satisfies `G`. -/
instance : PartialOrder (File W V M) :=
  .lift (fun F ↦ (OrderDual.toDual F.dom, F.sat)) fun _ _ h ↦
    let ⟨hdom, hsat⟩ := Prod.mk.inj h
    File.ext (OrderDual.toDual_inj.mp hdom) hsat

theorem le_iff : F ≤ G ↔ G.dom ⊆ F.dom ∧ F.sat ⊆ G.sat := Iff.rfl

theorem dom_anti : Antitone (dom : File W V M → Set V) := fun _ _ ⟨h, _⟩ ↦ h

theorem sat_mono : Monotone (sat : File W V M → Set (Possibility W V M)) :=
  fun _ _ ⟨_, h⟩ ↦ h

@[gcongr] theorem dom_subset_dom (h : F ≤ G) : G.dom ⊆ F.dom := dom_anti h

@[gcongr] theorem sat_subset_sat (h : F ≤ G) : F.sat ⊆ G.sat := sat_mono h

/-- The meet of two files has the cards of both and the points that satisfy both. -/
instance : SemilatticeInf (File W V M) where
  inf F G :=
    { dom := F.dom ∪ G.dom
      sat := F.sat ∩ G.sat
      mem_sat_of_eqOn := fun _ _ h ⟨hF, hG⟩ ↦
        ⟨F.mem_sat_of_eqOn (h.mono Set.subset_union_left) hF,
          G.mem_sat_of_eqOn (h.mono Set.subset_union_right) hG⟩ }
  inf_le_left _ _ := ⟨Set.subset_union_left, Set.inter_subset_left⟩
  inf_le_right _ _ := ⟨Set.subset_union_right, Set.inter_subset_right⟩
  le_inf _ _ _ h₁ h₂ :=
    ⟨Set.union_subset (dom_anti h₁) (dom_anti h₂), Set.subset_inter (sat_mono h₁) (sat_mono h₂)⟩

@[simp] theorem dom_inf (F G : File W V M) : (F ⊓ G).dom = F.dom ∪ G.dom := rfl

@[simp] theorem sat_inf (F G : File W V M) : (F ⊓ G).sat = F.sat ∩ G.sat := rfl

/-- The initial file has no cards, and every point satisfies it. The absurd file has every card,
and no point satisfies it. -/
instance : BoundedOrder (File W V M) where
  top := ⟨∅, Set.univ, fun _ _ _ _ ↦ trivial⟩
  le_top _ := ⟨Set.empty_subset _, Set.subset_univ _⟩
  bot := ⟨Set.univ, ∅, fun _ _ _ h ↦ h.elim⟩
  bot_le _ := ⟨Set.subset_univ _, Set.empty_subset _⟩

@[simp] theorem dom_top : (⊤ : File W V M).dom = ∅ := rfl

@[simp] theorem sat_top : (⊤ : File W V M).sat = Set.univ := rfl

@[simp] theorem dom_bot : (⊥ : File W V M).dom = Set.univ := rfl

@[simp] theorem sat_bot : (⊥ : File W V M).sat = ∅ := rfl

/-! ### Atomic files -/

/-- The file of an atomic formula: its cards are the formula's variables, and a point satisfies
it when the values of the variables stand in the predicate at the point's world. -/
def atom (ζ : W → (ι → M) → Prop) (args : ι → V) : File W V M where
  dom := Set.range args
  sat := {p | ζ p.world (p.assignment ∘ args)}
  mem_sat_of_eqOn p q h hp := by
    have hq : q.assignment ∘ args = p.assignment ∘ args :=
      funext fun k ↦ (h.assignment_eqOn ⟨k, rfl⟩).symm
    change ζ q.world (q.assignment ∘ args)
    rw [hq, ← h.world_eq]
    exact hp

@[simp] theorem dom_atom (ζ : W → (ι → M) → Prop) (args : ι → V) :
    (atom ζ args).dom = Set.range args := rfl

@[simp] theorem mem_sat_atom {ζ : W → (ι → M) → Prop} {args : ι → V} :
    p ∈ (atom ζ args).sat ↔ ζ p.world (p.assignment ∘ args) := Iff.rfl

/-- The file of a one-place predicate at the card `x`. -/
def atomAt (x : V) (N : W → M → Prop) : File W V M :=
  atom (fun w m ↦ N w (m ())) fun _ : Unit ↦ x

@[simp] theorem dom_atomAt (x : V) (N : W → M → Prop) : (atomAt x N).dom = {x} :=
  Set.range_const

@[simp] theorem mem_sat_atomAt {N : W → M → Prop} :
    p ∈ (atomAt x N).sat ↔ N p.world (p.assignment x) := Iff.rfl

theorem le_atomAt_iff {N : W → M → Prop} :
    F ≤ atomAt x N ↔ x ∈ F.dom ∧ F.sat ⊆ (atomAt x N).sat := by
  rw [le_iff, dom_atomAt, Set.singleton_subset_iff]

/-- A file that entails a predicate of the card `x`, and is satisfied by a point at whose world
some individual lacks the predicate, has the card `x`. -/
theorem mem_dom_of_forall_mem_sat {N : W → M → Prop}
    (h : ∀ p ∈ F.sat, N p.world (p.assignment x)) (hN : ∃ p ∈ F.sat, ∃ m, ¬ N p.world m) :
    x ∈ F.dom := by
  classical
  by_contra hx
  obtain ⟨p, hp, m, hm⟩ := hN
  exact hm (by simpa using h _ (F.mem_sat_of_eqOn (Possibility.eqOn_update hx m) hp))

/-! ### Existential closure -/

/-- The existential closure of a file off the cards in `X`: it keeps the cards in `X`, and a
point satisfies it when it agrees on `X` with a point that satisfies the file. -/
def restrict (F : File W V M) (X : Set V) : File W V M where
  dom := F.dom ∩ X
  sat := {p | ∃ q ∈ F.sat, q.EqOn p X}
  mem_sat_of_eqOn := by
    classical
    rintro p p' h ⟨q, hq, hqp⟩
    refine ⟨⟨q.world, X.piecewise p'.assignment q.assignment⟩,
      F.mem_sat_of_eqOn (p := q) ⟨rfl, fun v hv ↦ ?_⟩ hq,
      hqp.world_eq.trans h.world_eq, fun v hv ↦ Set.piecewise_eq_of_mem _ _ _ hv⟩
    by_cases hX : v ∈ X
    · exact ((hqp.assignment_eqOn hX).trans (h.assignment_eqOn ⟨hv, hX⟩)).trans
        (Set.piecewise_eq_of_mem _ _ _ hX).symm
    · exact (Set.piecewise_eq_of_notMem _ _ _ hX).symm

@[simp] theorem dom_restrict (F : File W V M) (X : Set V) : (F.restrict X).dom = F.dom ∩ X := rfl

@[simp] theorem mem_sat_restrict : p ∈ (F.restrict X).sat ↔ ∃ q ∈ F.sat, q.EqOn p X := Iff.rfl

theorem le_restrict (F : File W V M) (X : Set V) : F ≤ F.restrict X :=
  ⟨Set.inter_subset_left, fun p hp ↦ ⟨p, hp, .refl _ _⟩⟩

/-- Below a file whose cards lie in `X`, a file and its existential closure off `X` are the
same. -/
theorem restrict_le_iff (h : G.dom ⊆ X) : F.restrict X ≤ G ↔ F ≤ G :=
  ⟨(le_restrict F X).trans, fun hFG ↦ ⟨Set.subset_inter (dom_anti hFG) h,
    fun _ ⟨_, hq, hqp⟩ ↦ G.mem_sat_of_eqOn (hqp.mono h) (sat_mono hFG hq)⟩⟩

@[simp] theorem restrict_eq_self_iff : F.restrict X = F ↔ F.dom ⊆ X :=
  ⟨fun h ↦ h ▸ Set.inter_subset_right,
    fun h ↦ ((restrict_le_iff h).mpr le_rfl).antisymm (le_restrict F X)⟩

theorem restrict_dom (F : File W V M) : F.restrict F.dom = F :=
  restrict_eq_self_iff.mpr subset_rfl

/-- Existential closure off the cards in `X`, as a closure operator on files. Its closed
elements are the files whose cards lie in `X`. -/
def restrictClosure (X : Set V) : ClosureOperator (File W V M) :=
  .mk₂ (·.restrict X) (le_restrict · X) fun _ _ h ↦ (restrict_le_iff Set.inter_subset_right).mpr h

@[simp] theorem restrictClosure_apply (X : Set V) (F : File W V M) :
    restrictClosure X F = F.restrict X := rfl

theorem isClosed_restrictClosure_iff : (restrictClosure X).IsClosed F ↔ F.dom ⊆ X :=
  (restrictClosure X).isClosed_iff.trans restrict_eq_self_iff

theorem restrict_mono (X : Set V) : Monotone (restrict · X : File W V M → File W V M) :=
  (restrictClosure X).monotone

@[gcongr] theorem restrict_le_restrict (h : F ≤ G) : F.restrict X ≤ G.restrict X :=
  restrict_mono X h

@[gcongr] theorem restrict_le_restrict_of_subset (h : X ⊆ Y) : F.restrict Y ≤ F.restrict X :=
  le_iff.mpr ⟨Set.inter_subset_inter_right _ h, fun _ ⟨q, hq, hqp⟩ ↦ ⟨q, hq, hqp.mono h⟩⟩

/-! ### Joins -/

/-- The join of two files has the cards they share and the points that agree on those cards with
a point of either. -/
instance : Lattice (File W V M) where
  __ := (inferInstance : SemilatticeInf (File W V M))
  sup F G :=
    { dom := F.dom ∩ G.dom
      sat := (F.restrict G.dom).sat ∪ (G.restrict F.dom).sat
      mem_sat_of_eqOn := fun _ _ h hp ↦ hp.imp
        ((F.restrict G.dom).mem_sat_of_eqOn h)
        ((G.restrict F.dom).mem_sat_of_eqOn (h.mono (Set.inter_comm G.dom F.dom).subset)) }
  le_sup_left F _ :=
    le_iff.mpr ⟨Set.inter_subset_left, fun _ hp ↦ .inl (sat_mono (le_restrict F _) hp)⟩
  le_sup_right _ G :=
    le_iff.mpr ⟨Set.inter_subset_right, fun _ hp ↦ .inr (sat_mono (le_restrict G _) hp)⟩
  sup_le _ _ _ hF hG := le_iff.mpr ⟨Set.subset_inter (dom_anti hF) (dom_anti hG), Set.union_subset
    (sat_mono ((restrict_le_iff (dom_anti hG)).mpr hF))
    (sat_mono ((restrict_le_iff (dom_anti hF)).mpr hG))⟩

@[simp] theorem dom_sup (F G : File W V M) : (F ⊔ G).dom = F.dom ∩ G.dom := rfl

theorem sat_sup (F G : File W V M) :
    (F ⊔ G).sat = (F.restrict G.dom).sat ∪ (G.restrict F.dom).sat := rfl

/-- Existential closure off the cards in `X` is the join with the file that has the cards in `X`
and no points. -/
theorem restrict_eq_sup (F : File W V M) (X : Set V) :
    F.restrict X = F ⊔ (⊥ : File W V M).restrict X :=
  File.ext (by simp) (by rw [sat_sup]; ext p; simp)

theorem bot_restrict_sup_bot_restrict (X Y : Set V) :
    (⊥ : File W V M).restrict X ⊔ (⊥ : File W V M).restrict Y =
      (⊥ : File W V M).restrict (X ∩ Y) :=
  File.ext (by simp) (by rw [sat_sup]; ext p; simp)

theorem restrict_restrict (F : File W V M) (X Y : Set V) :
    (F.restrict X).restrict Y = F.restrict (X ∩ Y) := by
  rw [restrict_eq_sup (F.restrict X), restrict_eq_sup F X, restrict_eq_sup F (X ∩ Y), sup_assoc,
    bot_restrict_sup_bot_restrict]

/-! ### Arbitrary meets -/

/-- The meet of a set of files has the cards of all of them and the points that satisfy all of
them. -/
instance : InfSet (File W V M) where
  sInf S :=
    { dom := ⋃ F ∈ S, F.dom
      sat := ⋂ F ∈ S, F.sat
      mem_sat_of_eqOn := fun _ _ h hp ↦ Set.mem_iInter₂.mpr fun F hF ↦
        F.mem_sat_of_eqOn (h.mono (Set.subset_biUnion_of_mem (u := dom) hF))
          (Set.mem_iInter₂.mp hp F hF) }

@[simp] theorem dom_sInf (S : Set (File W V M)) : (sInf S).dom = ⋃ F ∈ S, F.dom := rfl

@[simp] theorem sat_sInf (S : Set (File W V M)) : (sInf S).sat = ⋂ F ∈ S, F.sat := rfl

protected theorem isGLB_sInf (S : Set (File W V M)) : IsGLB S (sInf S) :=
  ⟨fun _ hF ↦ le_iff.mpr
      ⟨Set.subset_biUnion_of_mem (u := dom) hF, Set.biInter_subset_of_mem (t := sat) hF⟩,
    fun _ hG ↦ le_iff.mpr ⟨Set.iUnion₂_subset fun _ hF ↦ dom_anti (hG hF),
      Set.subset_iInter₂ fun _ hF ↦ sat_mono (hG hF)⟩⟩

/-- Files form a complete lattice. -/
instance : CompleteLattice (File W V M) where
  __ := (inferInstance : Lattice (File W V M))
  __ := (inferInstance : BoundedOrder (File W V M))
  __ := completeLatticeOfInf (File W V M) File.isGLB_sInf

/-! ### Cards and satisfaction sets as maps -/

/-- The cards of a file: the meet unites them and the join intersects them. -/
def domHom : BoundedLatticeHom (File W V M) (Set V)ᵒᵈ where
  toFun F := OrderDual.toDual F.dom
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl

@[simp] theorem domHom_apply (F : File W V M) : domHom F = OrderDual.toDual F.dom := rfl

/-- The satisfaction set of a file, which the meet intersects. -/
def satHom : InfTopHom (File W V M) (Set (Possibility W V M)) where
  toFun := sat
  map_inf' _ _ := rfl
  map_top' := rfl

@[simp] theorem satHom_apply (F : File W V M) : satHom F = F.sat := rfl

/-! ### The world set -/

/-- The world set of a file: the worlds in which it is true, those at which some sequence
satisfies it. -/
def worlds (F : File W V M) : Set W := Possibility.world '' F.sat

@[simp] theorem mem_worlds {w : W} : w ∈ F.worlds ↔ ∃ p ∈ F.sat, p.world = w := Iff.rfl

theorem worlds_mono : Monotone (worlds : File W V M → Set W) :=
  fun _ _ h ↦ Set.image_mono (sat_mono h)

@[gcongr] theorem worlds_subset_worlds (h : F ≤ G) : F.worlds ⊆ G.worlds := worlds_mono h

@[simp] theorem worlds_bot : (⊥ : File W V M).worlds = ∅ := Set.image_empty _

/-- A file and its existential closure are true in the same worlds. -/
@[simp] theorem worlds_restrict (F : File W V M) (X : Set V) : (F.restrict X).worlds = F.worlds :=
  Set.Subset.antisymm (by rintro _ ⟨_, ⟨q, hq, hqp⟩, rfl⟩; exact ⟨q, hq, hqp.world_eq⟩)
    (worlds_mono (le_restrict F X))

theorem worlds_sup (F G : File W V M) : (F ⊔ G).worlds = F.worlds ∪ G.worlds := by
  rw [worlds, sat_sup, Set.image_union]
  exact congrArg₂ _ (worlds_restrict F _) (worlds_restrict G _)

/-- The world set of a file: a join of files is true in the worlds where either is. -/
def worldsHom : SupBotHom (File W V M) (Set W) where
  toFun := worlds
  map_sup' := worlds_sup
  map_bot' := worlds_bot

@[simp] theorem worldsHom_apply (F : File W V M) : worldsHom F = F.worlds := rfl

/-! ### Difference -/

/-- The difference of two files keeps the cards of the first and its points that no point of the
second agrees with on those cards. -/
instance : SDiff (File W V M) where
  sdiff F G :=
    { dom := F.dom
      sat := F.sat \ (G.restrict F.dom).sat
      mem_sat_of_eqOn := fun _ _ h ⟨hp, hnp⟩ ↦ ⟨F.mem_sat_of_eqOn h hp, fun hq ↦ hnp <|
        (G.restrict F.dom).mem_sat_of_eqOn (h.symm.mono Set.inter_subset_right) hq⟩ }

@[simp] theorem dom_sdiff (F G : File W V M) : (F \ G).dom = F.dom := rfl

theorem sat_sdiff (F G : File W V M) : (F \ G).sat = F.sat \ (G.restrict F.dom).sat := rfl

@[simp] theorem mem_sat_sdiff :
    p ∈ (F \ G).sat ↔ p ∈ F.sat ∧ ∀ q ∈ G.sat, ¬ q.EqOn p F.dom := by
  simp [sat_sdiff]

theorem sdiff_le (F G : File W V M) : F \ G ≤ F := le_iff.mpr ⟨subset_rfl, Set.sdiff_subset⟩

@[gcongr] theorem sdiff_le_sdiff_left (h : G ≤ H) : F \ H ≤ F \ G :=
  le_iff.mpr ⟨subset_rfl, _root_.sdiff_le_sdiff_left (sat_mono (restrict_mono F.dom h))⟩

/-- When the second file has no card the first lacks, the difference of files is the difference
of their satisfaction sets. -/
theorem sat_sdiff_of_dom_subset (h : G.dom ⊆ F.dom) : (F \ G).sat = F.sat \ G.sat := by
  rw [sat_sdiff, restrict_eq_self_iff.mpr h]

/-- The points of `F \ (G \ H)` are the points of `F` each of whose variants in `G` on the cards
of `F` has a variant in `H` on the cards of `G`. -/
theorem mem_sat_sdiff_sdiff :
    p ∈ (F \ (G \ H)).sat ↔
      p ∈ F.sat ∧ ∀ q ∈ G.sat, q.EqOn p F.dom → ∃ r ∈ H.sat, r.EqOn q G.dom := by
  simp only [mem_sat_sdiff, and_imp]
  exact and_congr_right fun _ ↦ forall₂_congr fun q hq ↦
    ⟨fun h hqp ↦ by_contra fun hne ↦ h (fun r hr hrq ↦ hne ⟨r, hr, hrq⟩) hqp,
      fun h hno hqp ↦ let ⟨r, hr, hrq⟩ := h hqp; hno r hr hrq⟩

end File

end DynamicSemantics
