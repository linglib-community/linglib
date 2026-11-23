module

public import Linglib.Semantics.Dynamic.Partial
public import Linglib.Semantics.Dynamic.Possibility
public import Mathlib.Data.Set.Piecewise
public import Mathlib.Order.Closure
public import Mathlib.Order.Hom.BoundedLattice

/-!
# File change semantics

A *file* records what a discourse has established. It has a set of cards `dom`, one for each
individual mentioned so far, and a satisfaction set `sat`, the pairs of a world and a sequence of
individuals that fit every entry. The two are separate data, tied by one condition: the
satisfaction set does not distinguish two points that agree on the cards. So a file says nothing
about an individual it has no card for, and a file that nothing satisfies still has its cards.

Files are ordered by information, `F ≤ G` when `G.dom ⊆ F.dom` and `F.sat ⊆ G.sat`, and they
form a bounded lattice. The meet `F ⊓ G` has the cards of both and the points that satisfy both.
The join `F ⊔ G` has the cards they share and the points that agree on those cards with a point
of either. The top is the file with no cards that every point satisfies. The world set
`File.worlds F` is the set of worlds at which some sequence satisfies `F`, the worlds in which
the file is true; a join is true where either file is (`File.worldsHom`).

The existential closure `F.restrict X` forgets the cards outside `X`, keeping every point that
agrees on `X` with a point of `F`. It is a closure operator (`File.restrictClosure`), it is
true in the same worlds as `F` (`File.worlds_restrict`), and below a file whose cards lie in `X`
it changes nothing (`File.restrict_le_iff`). The difference `F \ G` keeps the cards of `F` and
the points of `F` that no point of `G` agrees with on those cards. When `G` has no card that `F`
lacks, it is the difference of the satisfaction sets (`File.sat_sdiff_of_dom_subset`), the
negation of [heim-1983].

A *file change potential* is a partial function on files, the meaning of a sentence: the change
its utterance makes to the file, defined where the sentence is felicitous. The update by an
atomic formula is the meet with the formula's file `File.atom`, which adds the cards of its
variables and removes the points that falsify it. An indefinite is felicitous where its card is
new, and a definite where its card is present and the file entails its descriptive content,
where `F` entails an update that removes no point of `F` (`File.Entails`). For a one-place
content at the definite's own card, the condition is that the file lies below the content's file
(`FCP.admits_definite_ofFile_atomAt`). Negation is `PartialUpdate.neg` at the difference of
files, so the cards introduced under it are forgotten (`FCP.dom_eq_of_mem_neg`).

The update by a file, negation and the conditional descend in the information order, and an
indefinite or a definite does when its content does (`PartialUpdate.IsEliminative`). Under such
an update no card is removed, no point is added, and a file false in a world stays false in it,
since `File.dom` is antitone and `File.sat` and `File.worlds` are monotone.

## Implementation notes

The condition tying `sat` to `dom` is stated for all cards outside `dom` at once, where
[heim-1982]'s principle (B) changes one card at a time. This is the form under which
`F.restrict F.dom = F` (`File.restrict_dom`).

The difference of files is not a co-Heyting difference: `F \ F` keeps the cards of `F`.

The points are those of `Dynamic/Possibility.lean` with total assignments, [heim-1982]'s
world–sequence pairs. The information states of `Dynamic/State.lean` are sets of partial points
with no domain apart from the points, where a state that nothing satisfies makes every referent
both familiar and novel.

## TODO

Files have arbitrary meets, the union of the cards with the intersection of the satisfaction
sets, so they form a complete lattice, and `F.restrict X` is the join of `F` with the file that
has the cards `X` and no points. Neither is stated.

## References

* [heim-1982]
* [heim-1983]
-/

@[expose] public section

namespace DynamicSemantics

variable {W V M : Type*}

/-! ### Agreement of points -/

namespace Possibility

variable {X Y : Set V} {p q r : Possibility W V M}

/-- Two points agree on the cards in `X` when they share their world and their sequences take
the same values on `X`. -/
structure AgreeOn (X : Set V) (p q : Possibility W V M) : Prop where
  /-- The points share their world. -/
  world_eq : p.world = q.world
  /-- The sequences take the same values on `X`. -/
  eqOn : Set.EqOn p.assignment q.assignment X

@[refl] theorem AgreeOn.refl (X : Set V) (p : Possibility W V M) : p.AgreeOn X p :=
  ⟨rfl, Set.eqOn_refl _ _⟩

@[symm] theorem AgreeOn.symm (h : p.AgreeOn X q) : q.AgreeOn X p := ⟨h.world_eq.symm, h.eqOn.symm⟩

@[trans] theorem AgreeOn.trans (h : p.AgreeOn X q) (h' : q.AgreeOn X r) : p.AgreeOn X r :=
  ⟨h.world_eq.trans h'.world_eq, h.eqOn.trans h'.eqOn⟩

theorem AgreeOn.mono (hXY : X ⊆ Y) (h : p.AgreeOn Y q) : p.AgreeOn X q :=
  ⟨h.world_eq, h.eqOn.mono hXY⟩

theorem agreeOn_comm : p.AgreeOn X q ↔ q.AgreeOn X p := ⟨.symm, .symm⟩

@[simp] theorem agreeOn_empty : p.AgreeOn ∅ q ↔ p.world = q.world :=
  ⟨AgreeOn.world_eq, fun h ↦ ⟨h, Set.eqOn_empty _ _⟩⟩

@[simp] theorem agreeOn_univ : p.AgreeOn Set.univ q ↔ p = q :=
  ⟨fun h ↦ Possibility.ext h.world_eq (funext fun v ↦ h.eqOn (Set.mem_univ v)),
    fun h ↦ h ▸ .refl _ _⟩

theorem agreeOn_update [DecidableEq V] {x : V} (hx : x ∉ X) (m : M) : p.AgreeOn X (p.update x m) :=
  ⟨rfl, fun _ hv ↦ (Function.update_of_ne (ne_of_mem_of_not_mem hv hx) _ _).symm⟩

end Possibility

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
  mem_sat_of_agreeOn ⦃p q : Possibility W V M⦄ : p.AgreeOn dom q → p ∈ sat → q ∈ sat

namespace File

variable {ι : Type*} {F G H : File W V M} {X Y : Set V} {p q : Possibility W V M} {x : V}

theorem mem_sat_congr (h : p.AgreeOn F.dom q) : p ∈ F.sat ↔ q ∈ F.sat :=
  ⟨F.mem_sat_of_agreeOn h, F.mem_sat_of_agreeOn h.symm⟩

/-- `F ≤ G` when `F` has every card of `G` and every point of `F` satisfies `G`. -/
instance : PartialOrder (File W V M) :=
  .lift (fun F ↦ (OrderDual.toDual F.dom, F.sat)) fun _ _ h ↦
    let ⟨hdom, hsat⟩ := Prod.mk.inj h
    File.ext (OrderDual.toDual_inj.mp hdom) hsat

theorem le_iff : F ≤ G ↔ G.dom ⊆ F.dom ∧ F.sat ⊆ G.sat := Iff.rfl

theorem dom_anti : Antitone (dom : File W V M → Set V) := fun _ _ ⟨h, _⟩ ↦ h

theorem sat_mono : Monotone (sat : File W V M → Set (Possibility W V M)) :=
  fun _ _ ⟨_, h⟩ ↦ h

/-- The meet of two files has the cards of both and the points that satisfy both. -/
instance : SemilatticeInf (File W V M) where
  inf F G :=
    { dom := F.dom ∪ G.dom
      sat := F.sat ∩ G.sat
      mem_sat_of_agreeOn := fun _ _ h ⟨hF, hG⟩ ↦
        ⟨F.mem_sat_of_agreeOn (h.mono Set.subset_union_left) hF,
          G.mem_sat_of_agreeOn (h.mono Set.subset_union_right) hG⟩ }
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
  mem_sat_of_agreeOn p q h hp := by
    have hq : q.assignment ∘ args = p.assignment ∘ args :=
      funext fun k ↦ (h.eqOn ⟨k, rfl⟩).symm
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
  exact hm (by simpa using h _ (F.mem_sat_of_agreeOn (Possibility.agreeOn_update hx m) hp))

/-! ### Existential closure -/

/-- The existential closure of a file off the cards in `X`: it keeps the cards in `X`, and a
point satisfies it when it agrees on `X` with a point that satisfies the file. -/
def restrict (F : File W V M) (X : Set V) : File W V M where
  dom := F.dom ∩ X
  sat := {p | ∃ q ∈ F.sat, q.AgreeOn X p}
  mem_sat_of_agreeOn := by
    classical
    rintro p p' h ⟨q, hq, hqp⟩
    refine ⟨⟨q.world, X.piecewise p'.assignment q.assignment⟩,
      F.mem_sat_of_agreeOn (p := q) ⟨rfl, fun v hv ↦ ?_⟩ hq,
      hqp.world_eq.trans h.world_eq, fun v hv ↦ Set.piecewise_eq_of_mem _ _ _ hv⟩
    by_cases hX : v ∈ X
    · exact ((hqp.eqOn hX).trans (h.eqOn ⟨hv, hX⟩)).trans (Set.piecewise_eq_of_mem _ _ _ hX).symm
    · exact (Set.piecewise_eq_of_notMem _ _ _ hX).symm

@[simp] theorem dom_restrict (F : File W V M) (X : Set V) : (F.restrict X).dom = F.dom ∩ X := rfl

@[simp] theorem mem_sat_restrict : p ∈ (F.restrict X).sat ↔ ∃ q ∈ F.sat, q.AgreeOn X p := Iff.rfl

theorem le_restrict (F : File W V M) (X : Set V) : F ≤ F.restrict X :=
  ⟨Set.inter_subset_left, fun p hp ↦ ⟨p, hp, .refl _ _⟩⟩

/-- Below a file whose cards lie in `X`, a file and its existential closure off `X` are the
same. -/
theorem restrict_le_iff (h : G.dom ⊆ X) : F.restrict X ≤ G ↔ F ≤ G :=
  ⟨(le_restrict F X).trans, fun hFG ↦ ⟨Set.subset_inter (dom_anti hFG) h,
    fun _ ⟨_, hq, hqp⟩ ↦ G.mem_sat_of_agreeOn (hqp.mono h) (sat_mono hFG hq)⟩⟩

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

/-! ### Joins -/

/-- The join of two files has the cards they share and the points that agree on those cards with
a point of either. -/
instance : Lattice (File W V M) where
  __ := (inferInstance : SemilatticeInf (File W V M))
  sup F G :=
    { dom := F.dom ∩ G.dom
      sat := (F.restrict G.dom).sat ∪ (G.restrict F.dom).sat
      mem_sat_of_agreeOn := fun _ _ h hp ↦ hp.imp
        ((F.restrict G.dom).mem_sat_of_agreeOn h)
        ((G.restrict F.dom).mem_sat_of_agreeOn (h.mono (Set.inter_comm G.dom F.dom).subset)) }
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
      mem_sat_of_agreeOn := fun _ _ h ⟨hp, hnp⟩ ↦ ⟨F.mem_sat_of_agreeOn h hp, fun hq ↦ hnp <|
        (G.restrict F.dom).mem_sat_of_agreeOn (h.symm.mono Set.inter_subset_right) hq⟩ }

@[simp] theorem dom_sdiff (F G : File W V M) : (F \ G).dom = F.dom := rfl

theorem sat_sdiff (F G : File W V M) : (F \ G).sat = F.sat \ (G.restrict F.dom).sat := rfl

@[simp] theorem mem_sat_sdiff :
    p ∈ (F \ G).sat ↔ p ∈ F.sat ∧ ∀ q ∈ G.sat, ¬ q.AgreeOn F.dom p := by
  simp [sat_sdiff]

theorem sdiff_le (F G : File W V M) : F \ G ≤ F := le_iff.mpr ⟨subset_rfl, Set.sdiff_subset⟩

/-- When the second file has no card the first lacks, the difference of files is the difference
of their satisfaction sets. -/
theorem sat_sdiff_of_dom_subset (h : G.dom ⊆ F.dom) : (F \ G).sat = F.sat \ G.sat := by
  rw [sat_sdiff, restrict_eq_self_iff.mpr h]

/-- The points of `F \ (G \ H)` are the points of `F` each of whose variants in `G` on the cards
of `F` has a variant in `H` on the cards of `G`. -/
theorem mem_sat_sdiff_sdiff :
    p ∈ (F \ (G \ H)).sat ↔
      p ∈ F.sat ∧ ∀ q ∈ G.sat, q.AgreeOn F.dom p → ∃ r ∈ H.sat, r.AgreeOn G.dom q := by
  simp only [mem_sat_sdiff, and_imp]
  exact and_congr_right fun _ ↦ forall₂_congr fun q hq ↦
    ⟨fun h hqp ↦ by_contra fun hne ↦ h (fun r hr hrq ↦ hne ⟨r, hr, hrq⟩) hqp,
      fun h hno hqp ↦ let ⟨r, hr, hrq⟩ := h hqp; hno r hr hrq⟩

end File

/-! ### File change potentials -/

/-- A file change potential: a partial update of files, defined where the sentence is
felicitous. -/
abbrev FCP (W V M : Type*) := PartialUpdate (File W V M)

/-- A file entails an update that is defined on it and removes none of its points. -/
def File.Entails (F : File W V M) (φ : FCP W V M) : Prop := ∃ F' ∈ φ F, F.sat ⊆ F'.sat

namespace FCP

variable {A B F F' : File W V M} {φ ψ : FCP W V M} {x : V}

/-- The assertive update by a file takes the meet with it. -/
def ofFile (A : File W V M) : FCP W V M := PFun.lift (· ⊓ A)

@[simp] theorem ofFile_apply : ofFile A F = Part.some (F ⊓ A) := rfl

theorem mem_ofFile : F' ∈ ofFile A F ↔ F' = F ⊓ A := Part.mem_some_iff

@[simp] theorem admits_ofFile (A F : File W V M) : (ofFile A).Admits F := trivial

@[simp] theorem ofFile_top : ofFile (⊤ : File W V M) = PFun.id _ := funext fun _ ↦ by simp

/-- Updating by two files in sequence is updating by their meet. -/
theorem ofFile_inf : ofFile (A ⊓ B) = (ofFile A).seq (ofFile B) :=
  funext fun _ ↦ by simp [PartialUpdate.seq, PFun.comp_apply, inf_assoc]

/-- A file supports the update by a file it lies below. -/
@[simp] theorem supports_ofFile : (ofFile A).supports F ↔ F ≤ A := by
  rw [PartialUpdate.supports_iff_mem, mem_ofFile, eq_comm, inf_eq_left]

theorem isEliminative_ofFile (A : File W V M) : (ofFile A).IsEliminative :=
  fun _ _ h ↦ mem_ofFile.mp h ▸ inf_le_left

/-! ### Entailment -/

theorem _root_.DynamicSemantics.File.Entails.admits (h : F.Entails φ) : φ.Admits F :=
  let ⟨F', hF', _⟩ := h
  Part.dom_iff_mem.mpr ⟨F', hF'⟩

theorem _root_.DynamicSemantics.PartialUpdate.supports.entails (h : φ.supports F) : F.Entails φ :=
  ⟨F, h, subset_rfl⟩

@[simp] theorem _root_.DynamicSemantics.File.entails_ofFile :
    F.Entails (ofFile A) ↔ F.sat ⊆ A.sat := by
  simp [File.Entails]

/-- Under an eliminative update, a file entails the update iff the update keeps its satisfaction
set. -/
theorem _root_.DynamicSemantics.File.entails_iff_of_isEliminative (h : φ.IsEliminative) :
    F.Entails φ ↔ ∃ F' ∈ φ F, F'.sat = F.sat :=
  exists_congr fun F' ↦ and_congr_right fun hF' ↦
    ⟨fun hsub ↦ (File.sat_mono (h F F' hF')).antisymm hsub, fun heq ↦ heq.ge⟩

/-! ### Felicity conditions -/

/-- An indefinite at the card `x`, felicitous on the files that lack the card. -/
def indefinite (x : V) (φ : FCP W V M) : FCP W V M :=
  fun F ↦ Part.assert (x ∉ F.dom) fun _ ↦ φ F

/-- A definite at the card `x`, felicitous on the files that have the card and entail its
content. -/
def definite (x : V) (φ : FCP W V M) : FCP W V M :=
  fun F ↦ Part.assert (x ∈ F.dom ∧ F.Entails φ) fun _ ↦ φ F

theorem mem_indefinite : F' ∈ indefinite x φ F ↔ x ∉ F.dom ∧ F' ∈ φ F :=
  Part.mem_assert_iff.trans exists_prop

theorem mem_definite : F' ∈ definite x φ F ↔ x ∈ F.dom ∧ F.Entails φ ∧ F' ∈ φ F :=
  Part.mem_assert_iff.trans (exists_prop.trans and_assoc)

theorem indefinite_apply (h : x ∉ F.dom) : indefinite x φ F = φ F := Part.assert_pos h

theorem definite_apply (hx : x ∈ F.dom) (h : F.Entails φ) : definite x φ F = φ F :=
  Part.assert_pos ⟨hx, h⟩

theorem admits_indefinite : (indefinite x φ).Admits F ↔ x ∉ F.dom ∧ φ.Admits F := exists_prop

theorem admits_definite : (definite x φ).Admits F ↔ x ∈ F.dom ∧ F.Entails φ :=
  ⟨fun ⟨h, _⟩ ↦ h, fun ⟨hx, h⟩ ↦ ⟨⟨hx, h⟩, h.admits⟩⟩

/-- A definite whose content is a file is felicitous on the files that have its card and whose
points all satisfy the content. -/
theorem admits_definite_ofFile :
    (definite x (ofFile A)).Admits F ↔ x ∈ F.dom ∧ F.sat ⊆ A.sat := by
  rw [admits_definite, File.entails_ofFile]

/-- A definite with a one-place content at its own card is felicitous on the files below the
content's file. -/
theorem admits_definite_ofFile_atomAt {N : W → M → Prop} :
    (definite x (ofFile (File.atomAt x N))).Admits F ↔ F ≤ File.atomAt x N := by
  rw [admits_definite_ofFile, File.le_atomAt_iff]

theorem definite_ofFile_apply (h : F ≤ A) (hx : x ∈ F.dom) :
    definite x (ofFile A) F = Part.some F := by
  rw [definite_apply hx (File.entails_ofFile.mpr (File.sat_mono h)), ofFile_apply,
    inf_eq_left.mpr h]

theorem _root_.DynamicSemantics.PartialUpdate.IsEliminative.indefinite (h : φ.IsEliminative)
    (x : V) : (indefinite x φ).IsEliminative :=
  fun F F' hF' ↦ let ⟨_, h'⟩ := mem_indefinite.mp hF'; h F F' h'

theorem _root_.DynamicSemantics.PartialUpdate.IsEliminative.definite (h : φ.IsEliminative)
    (x : V) : (definite x φ).IsEliminative :=
  fun F F' hF' ↦ let ⟨_, _, h'⟩ := mem_definite.mp hF'; h F F' h'

/-! ### Negation and the conditional -/

/-- Negation adds no card. -/
theorem dom_eq_of_mem_neg (h : F' ∈ PartialUpdate.neg φ F) : F'.dom = F.dom := by
  obtain ⟨_, -, rfl⟩ := PartialUpdate.mem_neg.mp h
  rfl

theorem isEliminative_neg (φ : FCP W V M) : (PartialUpdate.neg φ).IsEliminative := fun F _ h ↦ by
  obtain ⟨G, -, rfl⟩ := PartialUpdate.mem_neg.mp h
  exact File.sdiff_le F G

theorem isEliminative_cond (φ ψ : FCP W V M) : (PartialUpdate.cond φ ψ).IsEliminative :=
  fun F _ h ↦ by
    obtain ⟨_, -, _, -, rfl⟩ := PartialUpdate.mem_cond.mp h
    exact File.sdiff_le F _

end FCP

end DynamicSemantics
