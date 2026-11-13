module

public import Linglib.Phonology.Subregular.Local
public import Linglib.Phonology.Subregular.TierStrictlyLocal
public import Linglib.Phonology.Subregular.StrictlyPiecewise
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Tactic.FinCases
public import Linglib.Core.Computability.Edge
public import Linglib.Core.Order.Flat

/-!
# Word models

A word model is a word as a relational structure: its positions, each carrying the labels of its
symbol, under an ordering of the positions. A homomorphism of word models under precedence [picks
out a subsequence](##Subregular.WordModel.nonempty_hom_lt_iff) carrying the labels position by
position, and under successor, the covering relation,
[an infix](##Subregular.WordModel.nonempty_hom_covBy_iff). A word's diagram occurs in a structure
[exactly when the word maps into it](##Subregular.WordModel.diagram_occurs_iff_nonempty_hom), so
the subfactor order on words is the
[subsequence](##Subregular.WordModel.diagram_le_diagram_iff), respectively
[infix](##Subregular.WordModel.succDiagram_le_succDiagram_iff), order. The strictly local and
locally testable sets of word models under precedence are the
[strictly piecewise](##Language.isStrictlyPiecewise_iff_wordModel) and
[piecewise testable](##Language.isPiecewiseTestable_iff_wordModel) stringsets; those of words
between their edges under successor are the
[strictly local](##Language.isStrictlyLocal_iff_wordModel) and
[locally testable](##Language.isLocallyTestable_iff_wordModel) ones, and on the projection to a
tier the [tier-based strictly local](##Language.isTierStrictlyLocal_iff_wordModel) ones. In a
feature-labelled model a symbol carries the values of its features, so that a position of a
factor stands for a natural class.

## Implementation notes

* An ordering is a relation on the positions passed to `WordModel`, so precedence is
  `WordModel w (· < ·)` and successor `WordModel (anchor w) (· ⋖ ·)`. Rogers and Lambert's word
  models carry both orderings in one signature; here a model has one.
* As in Rogers and Lambert's word models, the edges carry their own labels and are not related to
  themselves. The strictly local stringsets pad a word with `k - 1` boundary symbols instead, and
  the two classes differ only at `k = 1`, where the word models also forbid every word; the
  locally testable classes agree at every `k`.
* Strict locality under successor rests on
  [locality of concatenation](##Subregular.WordModel.factors_append_append_subset): a `k`-factor
  of a word around `k - 1` or more symbols occurs on one side of them, which is suffix
  substitution closure read on models.

## TODO

* Successor relativized to a tier is modelled by the successor model of the word's projection.
  The relation on the word's own positions, relating a tier position to the next one, and the
  isomorphism of the substructure it induces on the tier positions with that model, are not
  stated.

## References

* [rogers-lambert-2019]
* [rogers-pullum-2011]
* [rogers-heinz-et-al-2010]
* [lambert-2023]
* [chandlee-eyraud-heinz-jardine-rawski-2019]
-/

@[expose] public section

universe u

open FirstOrder FirstOrder.Language List

namespace Subregular

variable {α : Type u}

/-- The relation symbols of word models, a unary label for each symbol and a binary
ordering. -/
inductive WordRel (α : Type u) : ℕ → Type u
  | label (a : α) : WordRel α 1
  | ord : WordRel α 2

/-- The signature of word models over `α`. -/
def wordLanguage (α : Type u) : FirstOrder.Language := ⟨fun _ ↦ Empty, WordRel α⟩

instance : (wordLanguage α).IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

instance [Finite α] : Finite (Σ n, (wordLanguage α).Relations n) :=
  .of_injective (β := Option α) (fun | ⟨_, .label a⟩ => some a | ⟨_, .ord⟩ => none) <| by
    rintro ⟨_, _ | _⟩ ⟨_, _ | _⟩ h <;> simp_all

/-- The labels a symbol carries in word models whose unary relations are `P`. -/
class Labelling (β P : Type*) where
  /-- The labels of a symbol. -/
  labels : β → Set P

/-- In the conventional model a symbol is its own one label. -/
instance (β : Type*) : Labelling β β := ⟨fun b ↦ {b}⟩

@[simp] theorem Labelling.labels_self {β : Type*} (b : β) : labels (P := β) b = {b} := rfl

/-- The word model of `u` under an ordering `R` of its positions, each position labelled by its
symbol. -/
def WordModel {β : Type*} (u : List β) (_ : Fin u.length → Fin u.length → Prop) : Type :=
  Fin u.length

namespace WordModel

variable {β : Type*} {u u' : List β} {R : Fin u.length → Fin u.length → Prop}
  {R' : Fin u'.length → Fin u'.length → Prop}

instance : LinearOrder (WordModel u R) := inferInstanceAs (LinearOrder (Fin u.length))

/-- A position, as an index into the word. -/
def toFin (i : WordModel u R) : Fin u.length := i

/-- The symbol at a position. -/
def label (i : WordModel u R) : β := u.get i

variable {P : Type*} [Labelling β P]

/-- A position satisfies the unary relations of the labels its symbol carries. -/
instance : (wordLanguage P).Structure (WordModel u R) where
  RelMap
    | .label p, x => p ∈ Labelling.labels (x 0).label
    | .ord, x => R (x 0) (x 1)

@[simp] theorem relMap_label (p : P) (x : Fin 1 → WordModel u R) :
    Structure.RelMap (L := wordLanguage P) (WordRel.label p) x ↔
      p ∈ Labelling.labels (x 0).label := .rfl

@[simp] theorem relMap_ord (x : Fin 2 → WordModel u R) :
    Structure.RelMap (L := wordLanguage P) WordRel.ord x ↔ R (x 0) (x 1) := .rfl

/-- A map of positions under which symbols keep their labels and positions their order is a
homomorphism of word models. -/
@[simps]
def hom (e : Fin u.length → Fin u'.length)
    (hlabel : ∀ i, Labelling.labels (P := P) (u.get i) ⊆ Labelling.labels (u'.get (e i)))
    (hord : ∀ i j, R i j → R' (e i) (e j)) :
    WordModel u R →[wordLanguage P] WordModel u' R' where
  toFun := e
  map_fun' f := isEmptyElim f
  map_rel' r x h := by
    cases r with
    | label p => exact hlabel _ h
    | ord => exact hord _ _ h

theorem labels_subset_labels_hom (φ : WordModel u R →[wordLanguage P] WordModel u' R')
    (i : WordModel u R) : Labelling.labels (P := P) i.label ⊆ Labelling.labels (φ i).label :=
  fun p hp ↦ φ.map_rel (WordRel.label p) ![i] hp

theorem rel_hom (φ : WordModel u R →[wordLanguage P] WordModel u' R') {i j : WordModel u R}
    (h : R i j) : R' (φ i) (φ j) :=
  φ.map_rel WordRel.ord ![i, j] h

/-- An assignment moved along a map of the positions it uses, keeping their symbols and their
order, realizes what it realized. -/
theorem mem_realizers_of {n : ℕ} {T : Set ((wordLanguage P).Atom (Fin n))}
    {v : Fin n → WordModel u R} {v' : Fin n → WordModel u' R'}
    (hlabel : ∀ x, (v' x).label = (v x).label) (hord : ∀ x y, R (v x) (v y) → R' (v' x) (v' y))
    (hv : v ∈ Atom.realizers (WordModel u R) T) : v' ∈ Atom.realizers (WordModel u' R') T := by
  refine Atom.mem_realizers.2 fun ⟨r, args⟩ ha ↦ ?_
  have h := Atom.mem_realizers.1 hv _ ha
  cases r with
  | label p =>
    change p ∈ Labelling.labels (v' (args 0)).label
    rw [hlabel]
    exact h
  | ord => exact hord _ _ h

/-! ### Precedence -/

section Precedence

variable {w w' : List α}

/-- A homomorphism of word models under precedence picks out a subsequence whose positions carry
the labels, position by position. -/
theorem nonempty_hom_lt_iff [Labelling α P] :
    Nonempty (WordModel w (· < ·) →[wordLanguage P] WordModel w' (· < ·)) ↔
      ∃ t, t <+ w' ∧
        List.Forall₂ (fun a b ↦ Labelling.labels (P := P) a ⊆ Labelling.labels b) w t := by
  constructor
  · rintro ⟨φ⟩
    have hmono : StrictMono fun i ↦ show Fin w'.length from φ i := fun i j hij ↦ rel_hom φ hij
    refine ⟨List.ofFn fun i ↦ w'.get (φ i), List.sublist_iff_exists_fin_orderEmbedding_get_eq.2
      ⟨(Fin.castOrderIso List.length_ofFn).toOrderEmbedding.trans
        (OrderEmbedding.ofStrictMono _ hmono), fun i ↦ by simp only [List.get_ofFn]; rfl⟩, ?_⟩
    rw [List.forall₂_iff_get]
    refine ⟨List.length_ofFn.symm, fun i h₁ _ ↦ ?_⟩
    simp only [List.get_ofFn]
    exact labels_subset_labels_hom φ ⟨i, h₁⟩
  · rintro ⟨t, htw, hwt⟩
    obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.1 htw
    obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.1 hwt
    exact ⟨hom (fun i ↦ e (Fin.cast hlen i))
      (fun i ↦ he (Fin.cast hlen i) ▸ hget i i.2 (hlen ▸ i.2)) fun i j h ↦ e.lt_iff_lt.2 h⟩

theorem factors_subset_of_sublist [Labelling α P] {k : ℕ} (h : w <+ w') :
    (wordLanguage P).factors k (WordModel w (· < ·)) ⊆
      (wordLanguage P).factors k (WordModel w' (· < ·)) :=
  let ⟨φ⟩ := nonempty_hom_lt_iff.2 ⟨w, h, List.forall₂_same.2 fun _ _ ↦ subset_rfl⟩
  factors_mono φ

theorem exists_sublist_of_occurs [Labelling α P] {k : ℕ} {f : (wordLanguage P).Factor k}
    (hf : f.Occurs (WordModel w (· < ·))) :
    ∃ s, s <+ w ∧ s.length ≤ k ∧ f.Occurs (WordModel s (· < ·)) := by
  obtain ⟨v, hv⟩ := hf
  let u (x : Fin f.n) : Fin w.length := v x
  let I : Finset (Fin w.length) := Finset.univ.image u
  have hmem (x) : u x ∈ I := Finset.mem_image_of_mem _ (Finset.mem_univ x)
  have key (y : I) : I.orderEmbOfFin rfl ((I.orderIsoOfFin rfl).symm y) = y := by
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  have hlen : (List.ofFn fun i ↦ w.get (I.orderEmbOfFin rfl i)).length = I.card :=
    List.length_ofFn
  refine ⟨List.ofFn fun i ↦ w.get (I.orderEmbOfFin rfl i), ?_, ?_, ?_⟩
  · refine List.sublist_iff_exists_fin_orderEmbedding_get_eq.2
      ⟨OrderEmbedding.ofStrictMono (fun i ↦ I.orderEmbOfFin rfl (Fin.cast hlen i))
        fun i j h ↦ (I.orderEmbOfFin rfl).lt_iff_lt.2 h, fun i ↦ by simp; rfl⟩
  · exact hlen.le.trans ((Finset.card_image_le.trans (by simp)).trans f.n_le)
  · refine ⟨fun x ↦ Fin.cast hlen.symm ((I.orderIsoOfFin rfl).symm ⟨u x, hmem x⟩),
      mem_realizers_of (fun x ↦ ?_) (fun x y h ↦ ?_) hv⟩
    · change List.get _ _ = w.get (u x)
      simp only [List.get_ofFn, Fin.cast_cast, Fin.cast_eq_self]
      rw [key]
    · exact (I.orderIsoOfFin rfl).symm.lt_iff_lt.2 (Subtype.mk_lt_mk.2 h)

/-- The positive diagram of a word of at most `k` symbols under precedence, as a `k`-factor of
the labels `P`: every atom its positions satisfy. -/
def diagram (P : Type*) [Labelling α P] (s : List α) {k : ℕ} (hs : s.length ≤ k) :
    (wordLanguage P).Factor k where
  n := s.length
  n_le := hs
  atoms := Atom.diagram (WordModel s (· < ·))
  preconnected x y := by
    rcases lt_trichotomy x y with h | rfl | h
    · exact SimpleGraph.Adj.reachable
        ⟨h.ne, .inl ⟨⟨.ord, ![x, y]⟩, by exact h, ⟨0, rfl⟩, ⟨1, rfl⟩⟩⟩
    · rfl
    · exact SimpleGraph.Adj.reachable
        ⟨h.ne', .inr ⟨⟨.ord, ![y, x]⟩, by exact h, ⟨0, rfl⟩, ⟨1, rfl⟩⟩⟩

/-- A word's diagram occurs in a structure exactly when the word maps homomorphically into
it. -/
theorem diagram_occurs_iff_nonempty_hom [Labelling α P] {s : List α} {k : ℕ} (hs : s.length ≤ k)
    {N : Type*} [(wordLanguage P).Structure N] :
    (diagram P s hs).Occurs N ↔ Nonempty (WordModel s (· < ·) →[wordLanguage P] N) :=
  ⟨fun ⟨v, hv⟩ ↦ ⟨Atom.diagramHomEquiv.symm ⟨v, hv⟩⟩, fun ⟨φ⟩ ↦ ⟨_, (Atom.diagramHomEquiv φ).2⟩⟩

/-- The diagram of a word occurs exactly in the words with a subsequence whose positions carry
its labels, position by position. -/
theorem diagram_occurs_iff_forall₂ [Labelling α P] {s : List α} {k : ℕ} (hs : s.length ≤ k) :
    (diagram P s hs).Occurs (WordModel w (· < ·)) ↔
      ∃ t, t <+ w ∧
        List.Forall₂ (fun a b ↦ Labelling.labels (P := P) a ⊆ Labelling.labels b) s t :=
  (diagram_occurs_iff_nonempty_hom hs).trans nonempty_hom_lt_iff

theorem diagram_occurs_iff {s : List α} {k : ℕ} (hs : s.length ≤ k) :
    (diagram α s hs).Occurs (WordModel w (· < ·)) ↔ s <+ w := by
  simp only [diagram_occurs_iff_forall₂, Labelling.labels_self, Set.singleton_subset_singleton,
    List.forall₂_eq_eq_eq, exists_eq_right']

/-- The subfactors of a word's diagram are the factors occurring in the word. -/
theorem le_diagram_iff [Labelling α P] {s : List α} {k : ℕ} (hs : s.length ≤ k)
    {f : (wordLanguage P).Factor k} : f ≤ diagram P s hs ↔ f.Occurs (WordModel s (· < ·)) :=
  Factor.le_iff_occurs

/-- Under precedence one word's diagram is a subfactor of another's exactly when the word is a
subsequence of the other, [chandlee-eyraud-heinz-jardine-rawski-2019]'s Proposition 2. -/
theorem diagram_le_diagram_iff {s : List α} {k : ℕ} (hs : s.length ≤ k) (hw : w.length ≤ k) :
    diagram α s hs ≤ diagram α w hw ↔ s <+ w :=
  (le_diagram_iff hw).trans (diagram_occurs_iff hs)

theorem diagram_singleton_occurs_iff [Labelling α P] {d : α} {k : ℕ} (hk : [d].length ≤ k) :
    (diagram P [d] hk).Occurs (WordModel w (· < ·)) ↔
      ∃ x ∈ w, Labelling.labels (P := P) d ⊆ Labelling.labels x := by
  rw [diagram_occurs_iff_forall₂]
  constructor
  · rintro ⟨t, htw, hdt⟩
    cases hdt with
    | cons h hnil =>
      cases hnil
      exact ⟨_, htw.subset (List.mem_singleton_self _), h⟩
  · rintro ⟨x, hx, hdx⟩
    exact ⟨[x], List.singleton_sublist.2 hx, .cons hdx .nil⟩

theorem factors_subset_of_subseqSet_subset {k : ℕ} (h : subseqSet k w ⊆ subseqSet k w') :
    (wordLanguage α).factors k (WordModel w (· < ·)) ⊆
      (wordLanguage α).factors k (WordModel w' (· < ·)) := fun _ hf ↦
  let ⟨_, hsw, hs, hfs⟩ := exists_sublist_of_occurs hf
  factors_subset_of_sublist (h ⟨hsw, hs⟩).1 hfs

theorem factors_eq_iff_subseqSet {k : ℕ} :
    (wordLanguage α).factors k (WordModel w (· < ·)) =
        (wordLanguage α).factors k (WordModel w' (· < ·)) ↔
      subseqSet k w = subseqSet k w' := by
  refine ⟨fun h ↦ Set.ext fun s ↦ ⟨fun ⟨hsw, hs⟩ ↦ ⟨?_, hs⟩, fun ⟨hsw, hs⟩ ↦ ⟨?_, hs⟩⟩,
    fun h ↦ (factors_subset_of_subseqSet_subset h.subset).antisymm
      (factors_subset_of_subseqSet_subset h.symm.subset)⟩
  · exact (diagram_occurs_iff hs).1 (h.subset ((diagram_occurs_iff hs).2 hsw))
  · exact (diagram_occurs_iff hs).1 (h.symm.subset ((diagram_occurs_iff hs).2 hsw))

end Precedence

/-! ### Feature-labelled models

A position may carry several properties, the values of features, as in Chandlee, Eyraud,
Heinz, Jardine and Rawski's unconventional models. A word of partial valuations `ι → Flat V`,
such as a word of segments, has a unary relation for each feature value, holding at the
positions with that value, so a position never has two values of one feature and may have none.
Under precedence the diagram of such a word occurs exactly in the words with a subsequence lying
above it position by position, and a natural class is a one-position factor. -/

section Features

variable {ι V : Type*}

/-- A partial valuation, such as a segment, carries the values it gives its features. -/
instance : Labelling (ι → Flat V) (ι × V) := ⟨fun s ↦ {p | s p.1 = p.2}⟩

theorem labels_subset_labels_iff {s t : ι → Flat V} :
    Labelling.labels (P := ι × V) s ⊆ Labelling.labels t ↔ s ≤ t := by
  refine ⟨fun h i ↦ ?_, fun h p hp ↦ Flat.coe_le_iff.1 ((show s p.1 = p.2 from hp) ▸ h p.1)⟩
  cases hs : s i with
  | bot => exact bot_le
  | coe a => exact Flat.coe_le_iff.2 (h (show s (i, a).1 = (i, a).2 from hs))

theorem diagram_occurs_iff_forall₂_le {s w : List (ι → Flat V)} {k : ℕ} (hs : s.length ≤ k) :
    (diagram (ι × V) s hs).Occurs (WordModel w (· < ·)) ↔
      ∃ t, t <+ w ∧ List.Forall₂ (· ≤ ·) s t := by
  simp only [diagram_occurs_iff_forall₂, labels_subset_labels_iff]

end Features

/-! ### Successor -/

section Successor

variable {c : List β}

private theorem covBy_unit {m : ℕ} {a b : Fin m} (h : a ⋖ b) :
    (a : ℕ) ≤ b + 1 ∧ (b : ℕ) ≤ a + 1 := by
  rw [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h
  omega

theorem le_add_one_of_adj {n : ℕ} {T : Set ((wordLanguage P).Atom (Fin n))}
    {r : Fin n → WordModel u (· ⋖ ·)} (hr : r ∈ Atom.realizers (WordModel u (· ⋖ ·)) T)
    {x y : Fin n} (h : (Atom.gaifman T).Adj x y) : ((r x).toFin : ℕ) ≤ (r y).toFin + 1 := by
  obtain ⟨hne, hxy⟩ := h
  have key : ∀ a ∈ T, x ∈ Set.range a.args → y ∈ Set.range a.args →
      ((r x).toFin : ℕ) ≤ (r y).toFin + 1 := by
    rintro ⟨_ | _, args⟩ ha ⟨i, rfl⟩ ⟨j, rfl⟩
    · exact absurd (congrArg args (Subsingleton.elim i j)) hne
    · have hR' := covBy_unit (Atom.mem_realizers.1 hr _ ha)
      fin_cases i <;> fin_cases j
      · exact absurd rfl hne
      · exact hR'.1
      · exact hR'.2
      · exact absurd rfl hne
  rcases hxy with ⟨a, ha, hx, hy⟩ | ⟨a, ha, hy, hx⟩ <;> exact key a ha hx hy

/-- Under successor an occurrence of a `k`-factor spans fewer than `k` steps. -/
theorem le_add_of_occurs {k : ℕ} {f : (wordLanguage P).Factor k}
    {r : Fin f.n → WordModel u (· ⋖ ·)} (hr : r ∈ Atom.realizers (WordModel u (· ⋖ ·)) f.atoms)
    (x y : Fin f.n) : ((r x).toFin : ℕ) ≤ (r y).toFin + (k - 1) := by
  have walk : ∀ {a b : Fin f.n} (p : (Atom.gaifman f.atoms).Walk a b),
      ((r a).toFin : ℕ) ≤ (r b).toFin + p.length := by
    intro a b p
    induction p with
    | nil => simp
    | cons h p ih =>
      have := le_add_one_of_adj hr h
      simp only [SimpleGraph.Walk.length_cons]
      omega
  obtain ⟨p⟩ := f.preconnected x y
  have hlen := p.toPath.2.length_lt
  simp only [Fintype.card_fin] at hlen
  have := walk p.toPath.1
  have := f.n_le
  omega

/-- A homomorphism of word models under successor picks out an infix whose positions carry the
labels, position by position. -/
theorem nonempty_hom_covBy_iff :
    Nonempty (WordModel c (· ⋖ ·) →[wordLanguage P] WordModel u (· ⋖ ·)) ↔
      ∃ t, t <:+: u ∧
        List.Forall₂ (fun a b ↦ Labelling.labels (P := P) a ⊆ Labelling.labels b) c t := by
  constructor
  · rintro ⟨φ⟩
    let r : Fin c.length → WordModel u (· ⋖ ·) := φ
    rcases Nat.eq_zero_or_pos c.length with h0 | hpos
    · rw [List.eq_nil_of_length_eq_zero h0]
      exact ⟨[], List.nil_infix, .nil⟩
    have hsucc (i : ℕ) (hi : i + 1 < c.length) :
        ((r ⟨i + 1, hi⟩).toFin : ℕ) = (r ⟨i, by omega⟩).toFin + 1 := by
      have h : (r ⟨i, by omega⟩).toFin ⋖ (r ⟨i + 1, hi⟩).toFin :=
        rel_hom φ (i := ⟨i, by omega⟩) (j := ⟨i + 1, hi⟩) (by simp [Fin.covBy_iff])
      rw [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h
      exact h.symm
    have hoff (i : ℕ) (hi : i < c.length) :
        ((r ⟨i, hi⟩).toFin : ℕ) = (r ⟨0, hpos⟩).toFin + i := by
      induction i with
      | zero => rfl
      | succ i ih => rw [hsucc i hi, ih (by omega)]; rfl
    set m : ℕ := ((r ⟨0, hpos⟩).toFin : ℕ)
    have hm : m + c.length ≤ u.length := by
      have := hoff (c.length - 1) (by omega)
      have := (r ⟨c.length - 1, by omega⟩).toFin.2
      omega
    refine ⟨(u.drop m).take c.length,
      (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix, ?_⟩
    rw [List.forall₂_iff_get]
    refine ⟨by simp only [List.length_take, List.length_drop]; omega, fun i h₁ h₂ ↦ ?_⟩
    have hget : ((u.drop m).take c.length).get ⟨i, h₂⟩ = (r ⟨i, h₁⟩).label := by
      simp only [List.get_eq_getElem, List.getElem_take, List.getElem_drop]
      change u[m + i] = u[((r ⟨i, h₁⟩).toFin : ℕ)]
      simp only [hoff i h₁, m]
    rw [hget]
    exact labels_subset_labels_hom φ ⟨i, h₁⟩
  · rintro ⟨t, htu, hct⟩
    obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.1 hct
    obtain ⟨m, hm, ht⟩ := List.infix_iff_getElem?.1 htu
    have hlt (i : Fin c.length) : (i : ℕ) + m < u.length := by omega
    have hu (i : Fin c.length) : u[(i : ℕ) + m]'(hlt i) = t[(i : ℕ)]'(i.2.trans_eq hlen) := by
      have := ht i (i.2.trans_eq hlen)
      rw [List.getElem?_eq_getElem (hlt i)] at this
      exact Option.some.inj this
    refine ⟨hom (fun i ↦ ⟨i + m, hlt i⟩) (fun i ↦ ?_) fun i j h ↦ ?_⟩
    · change Labelling.labels (c.get i) ⊆ Labelling.labels (u[(i : ℕ) + m]'(hlt i))
      rw [hu i]
      exact hget i i.2 (i.2.trans_eq hlen)
    · simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h ⊢
      omega

theorem factors_subset_of_infix {k : ℕ} (h : c <:+: u) :
    (wordLanguage P).factors k (WordModel c (· ⋖ ·)) ⊆
      (wordLanguage P).factors k (WordModel u (· ⋖ ·)) :=
  let ⟨φ⟩ := nonempty_hom_covBy_iff.2 ⟨c, h, List.forall₂_same.2 fun _ _ ↦ subset_rfl⟩
  factors_mono φ

/-- A factor realized under successor within a window of a word occurs in the window. -/
theorem occurs_take_drop {k : ℕ} {f : (wordLanguage P).Factor k}
    {r : Fin f.n → WordModel u (· ⋖ ·)} (hr : r ∈ Atom.realizers (WordModel u (· ⋖ ·)) f.atoms)
    {m l : ℕ} (hm : ∀ a, m ≤ ((r a).toFin : ℕ)) (hl : ∀ a, ((r a).toFin : ℕ) < m + l) :
    f.Occurs (WordModel ((u.drop m).take l) (· ⋖ ·)) := by
  have hlt (a) : ((r a).toFin : ℕ) - m < ((u.drop m).take l).length := by
    have := hm a
    have := hl a
    have := (r a).toFin.2
    simp only [List.length_take, List.length_drop]
    omega
  refine ⟨fun a ↦ show WordModel ((u.drop m).take l) (· ⋖ ·) from ⟨(r a).toFin - m, hlt a⟩,
    mem_realizers_of (fun a ↦ ?_) (fun a b hab ↦ ?_) hr⟩
  · change ((u.drop m).take l)[((r a).toFin : ℕ) - m]'(hlt a) =
      u[((r a).toFin : ℕ)]'(r a).toFin.2
    simp only [List.getElem_take, List.getElem_drop]
    congr 1
    have := hm a
    omega
  · change (r a).toFin ⋖ (r b).toFin at hab
    change (⟨_, hlt a⟩ : Fin _) ⋖ ⟨_, hlt b⟩
    have := hm a
    have := hm b
    simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at hab ⊢
    omega

theorem exists_infix_of_occurs {k : ℕ} {f : (wordLanguage P).Factor k}
    (hf : f.Occurs (WordModel u (· ⋖ ·))) :
    ∃ c, c <:+: u ∧ c.length ≤ k ∧ f.Occurs (WordModel c (· ⋖ ·)) := by
  obtain ⟨r, hr⟩ := hf
  have window (m : ℕ) (hm : ∀ a, m ≤ ((r a).toFin : ℕ)) (hl : ∀ a, ((r a).toFin : ℕ) < m + k) :
      ∃ c, c <:+: u ∧ c.length ≤ k ∧ f.Occurs (WordModel c (· ⋖ ·)) :=
    ⟨_, (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix,
      List.length_take_le _ _, occurs_take_drop hr hm hl⟩
  rcases Nat.eq_zero_or_pos f.n with h0 | hpos
  · exact window 0 (fun _ ↦ Nat.zero_le _) fun a ↦ absurd a.2 (by omega)
  have hne : (Finset.univ : Finset (Fin f.n)).Nonempty := ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_mem_eq_inf' hne fun a ↦ ((r a).toFin : ℕ)
  have hk : 1 ≤ k := hpos.trans_le f.n_le
  refine window (r a₀).toFin (fun a ↦ ha₀ ▸ Finset.inf'_le _ (Finset.mem_univ a)) fun a ↦ ?_
  have := le_add_of_occurs hr a a₀
  omega

/-- Under successor a `k`-factor of a word around `k - 1` or more symbols occurs on one side of
them. -/
theorem factors_append_append_subset {k : ℕ} {a x b : List β} (hx : k ≤ x.length + 1) :
    (wordLanguage P).factors k (WordModel (a ++ x ++ b) (· ⋖ ·)) ⊆
      (wordLanguage P).factors k (WordModel (a ++ x) (· ⋖ ·)) ∪
        (wordLanguage P).factors k (WordModel (x ++ b) (· ⋖ ·)) := by
  rintro f ⟨r, hr⟩
  have hspan := le_add_of_occurs hr
  by_cases hA : ∀ c, ((r c).toFin : ℕ) < a.length + x.length
  · have := occurs_take_drop hr (m := 0) (fun _ ↦ Nat.zero_le _) (by simpa using hA)
    rw [List.drop_zero, List.take_left' (by simp)] at this
    exact .inl this
  · obtain ⟨c₀, hc₀⟩ := by simpa only [not_forall, not_lt] using hA
    have := occurs_take_drop hr (m := a.length) (l := x.length + b.length)
      (fun c ↦ by have := hspan c₀ c; omega)
      (fun c ↦ by have := (r c).toFin.2; simp only [List.length_append] at this; omega)
    rw [List.append_assoc, List.drop_left' rfl, List.take_of_length_le (by simp)] at this
    exact .inr this

/-- The diagram of a word under successor, as a `k`-factor of the labels `P`: the path of its
positions, each carrying the labels of its symbol. -/
def succDiagram (P : Type*) [Labelling β P] (c : List β) {k : ℕ} (hc : c.length ≤ k) :
    (wordLanguage P).Factor k where
  n := c.length
  n_le := hc
  atoms := Atom.diagram (WordModel c (· ⋖ ·))
  preconnected x y := by
    have hpos : 0 < c.length := x.pos
    have reach (i : ℕ) (hi : i < c.length) :
        (Atom.gaifman (L := wordLanguage P) (Atom.diagram (WordModel c (· ⋖ ·)))).Reachable
          ⟨0, hpos⟩ ⟨i, hi⟩ := by
      induction i with
      | zero => rfl
      | succ i ih =>
        refine (ih (by omega)).trans <| SimpleGraph.Adj.reachable
          ⟨Fin.ne_of_val_ne i.lt_succ_self.ne,
            .inl ⟨⟨.ord, ![⟨i, by omega⟩, ⟨i + 1, hi⟩]⟩, ?_, ⟨0, rfl⟩, ⟨1, rfl⟩⟩⟩
        change (⟨i, _⟩ : Fin c.length) ⋖ ⟨i + 1, hi⟩
        simp [Fin.covBy_iff]
    exact (reach x x.2).symm.trans (reach y y.2)

/-- A word's successor diagram occurs in a structure exactly when the word maps homomorphically
into it. -/
theorem succDiagram_occurs_iff_nonempty_hom {k : ℕ} (hc : c.length ≤ k)
    {N : Type*} [(wordLanguage P).Structure N] :
    (succDiagram P c hc).Occurs N ↔ Nonempty (WordModel c (· ⋖ ·) →[wordLanguage P] N) :=
  ⟨fun ⟨v, hv⟩ ↦ ⟨Atom.diagramHomEquiv.symm ⟨v, hv⟩⟩, fun ⟨φ⟩ ↦ ⟨_, (Atom.diagramHomEquiv φ).2⟩⟩

/-- The successor diagram of a word occurs exactly in the words with an infix whose positions
carry its labels, position by position. -/
theorem succDiagram_occurs_iff_forall₂ {k : ℕ} (hc : c.length ≤ k) :
    (succDiagram P c hc).Occurs (WordModel u (· ⋖ ·)) ↔
      ∃ t, t <:+: u ∧
        List.Forall₂ (fun a b ↦ Labelling.labels (P := P) a ⊆ Labelling.labels b) c t :=
  (succDiagram_occurs_iff_nonempty_hom hc).trans nonempty_hom_covBy_iff

theorem succDiagram_occurs_iff {k : ℕ} (hc : c.length ≤ k) :
    (succDiagram β c hc).Occurs (WordModel u (· ⋖ ·)) ↔ c <:+: u := by
  simp only [succDiagram_occurs_iff_forall₂, Labelling.labels_self, Set.singleton_subset_singleton,
    List.forall₂_eq_eq_eq, exists_eq_right']

/-- The subfactors of a word's successor diagram are the factors occurring in the word. -/
theorem le_succDiagram_iff {k : ℕ} (hc : c.length ≤ k)
    {f : (wordLanguage P).Factor k} : f ≤ succDiagram P c hc ↔ f.Occurs (WordModel c (· ⋖ ·)) :=
  Factor.le_iff_occurs

/-- Under successor one word's diagram is a subfactor of another's exactly when the word is an
infix of the other, [chandlee-eyraud-heinz-jardine-rawski-2019]'s Proposition 1. -/
theorem succDiagram_le_succDiagram_iff {k : ℕ} (hc : c.length ≤ k)
    (hu : u.length ≤ k) : succDiagram β c hc ≤ succDiagram β u hu ↔ c <:+: u :=
  (le_succDiagram_iff hu).trans (succDiagram_occurs_iff hc)

theorem factors_eq_iff_infix {k : ℕ} {u u' : List β} :
    (wordLanguage β).factors k (WordModel u (· ⋖ ·)) =
        (wordLanguage β).factors k (WordModel u' (· ⋖ ·)) ↔
      {c | c <:+: u ∧ c.length ≤ k} = {c | c <:+: u' ∧ c.length ≤ k} := by
  have sub (u u' : List β)
      (h : {c | c <:+: u ∧ c.length ≤ k} ⊆ {c | c <:+: u' ∧ c.length ≤ k}) :
      (wordLanguage β).factors k (WordModel u (· ⋖ ·)) ⊆
        (wordLanguage β).factors k (WordModel u' (· ⋖ ·)) := fun _ hf ↦
    let ⟨_, hc, hlen, hfc⟩ := exists_infix_of_occurs hf
    factors_subset_of_infix (h ⟨hc, hlen⟩).1 hfc
  refine ⟨fun h ↦ Set.ext fun c ↦ ⟨fun ⟨hc, hlen⟩ ↦ ⟨?_, hlen⟩, fun ⟨hc, hlen⟩ ↦ ⟨?_, hlen⟩⟩,
    fun h ↦ (sub _ _ h.subset).antisymm (sub _ _ h.symm.subset)⟩
  · exact (succDiagram_occurs_iff hlen).1 (h.subset ((succDiagram_occurs_iff hlen).2 hc))
  · exact (succDiagram_occurs_iff hlen).1 (h.symm.subset ((succDiagram_occurs_iff hlen).2 hc))

end Successor

end WordModel

/-! ### Anchored words -/

/-- The word `w` between its edges, `⋊ w ⋉`. -/
def anchor (w : List α) : List (α ⊕ Edge) := .inr .left :: (w.map .inl ++ [.inr .right])

section Anchor

variable {s v : List α}

@[simp] theorem length_anchor (w : List α) : (anchor w).length = w.length + 2 := by
  simp [anchor]

private theorem prefix_of_infix_cons {β : Type*} {e : β} {c l : List β} (h : e :: c <:+: e :: l)
    (he : e ∉ l) : c <+: l := by
  rcases List.infix_cons_iff.1 h with h | h
  · exact (List.cons_prefix_cons.1 h).2
  · exact absurd (h.subset List.mem_cons_self) he

theorem infix_of_map_inl_infix_anchor (h : s.map .inl <:+: anchor v) : s <:+: v := by
  simpa [anchor, List.filterMap_map] using h.filterMap Sum.getLeft?

theorem prefix_of_infix_anchor (h : .inr .left :: s.map .inl <:+: anchor v) : s <+: v := by
  have := (prefix_of_infix_cons h (by simp)).filterMap Sum.getLeft?
  simpa [List.filterMap_map] using this

theorem suffix_of_infix_anchor (h : s.map .inl ++ [.inr .right] <:+: anchor v) : s <:+ v := by
  have h' : .inr .right :: (s.reverse.map .inl) <:+:
      .inr .right :: ((v.reverse.map .inl) ++ [(.inr .left : α ⊕ Edge)]) := by
    simpa [anchor, List.map_reverse] using h.reverse
  have := (prefix_of_infix_cons h' (by simp)).filterMap Sum.getLeft?
  simpa [List.filterMap_map, List.reverse_prefix] using this

theorem eq_of_anchor_infix_anchor {w : List α} (h : anchor w <:+: anchor v) : w = v := by
  have hp := prefix_of_infix_cons h (by simp)
  have hle : w.length ≤ v.length := by simpa using hp.length_le
  have hlen : w.length = v.length := by
    refine le_antisymm hle (not_lt.1 fun hlt ↦ ?_)
    have hmem : (Sum.inr Edge.right : α ⊕ Edge) ∈ w.map .inl ++ [.inr .right] := by simp
    rw [List.prefix_iff_eq_take.1 hp, List.take_append_of_le_length (by simpa using hlt)] at hmem
    simpa using List.mem_of_mem_take hmem
  have := List.append_cancel_right (hp.eq_of_length (by simpa using hlen))
  exact List.map_injective_iff.2 Sum.inl_injective this

theorem anchor_append_append (u x v : List α) :
    anchor (u ++ x ++ v) =
      (.inr .left :: u.map .inl) ++ x.map .inl ++ (v.map .inl ++ [.inr .right]) := by
  simp [anchor]

theorem map_inl_infix_anchor_iff : s.map .inl <:+: anchor v ↔ s <:+: v :=
  ⟨infix_of_map_inl_infix_anchor,
    fun h ↦ (h.map _).trans ⟨[.inr .left], [.inr .right], by simp [anchor]⟩⟩

theorem cons_infix_anchor_iff : .inr .left :: s.map .inl <:+: anchor v ↔ s <+: v :=
  ⟨prefix_of_infix_anchor, fun h ↦
    (List.cons_prefix_cons.2 ⟨rfl, (h.map _).trans (List.prefix_append _ _)⟩).isInfix⟩

theorem append_infix_anchor_iff : s.map .inl ++ [.inr .right] <:+: anchor v ↔ s <:+ v := by
  refine ⟨suffix_of_infix_anchor, fun h ↦ ?_⟩
  obtain ⟨t, ht⟩ := h.map (Sum.inl : α → α ⊕ Edge)
  exact List.IsSuffix.isInfix ⟨.inr .left :: t, by rw [anchor, ← ht]; simp⟩

private theorem eq_map_inl_filterMap {c : List (α ⊕ Edge)} (h : ∀ x ∈ c, x.isLeft) :
    c = (c.filterMap Sum.getLeft?).map .inl := by
  induction c with
  | nil => rfl
  | cons x c ih =>
    obtain ⟨a, rfl⟩ : ∃ a, x = .inl a := Sum.isLeft_iff.1 (h x (by simp))
    simp [← ih fun y hy ↦ h y (by simp [hy])]

theorem infix_anchor_cases {c : List (α ⊕ Edge)} (h : c <:+: anchor v) :
    ∃ s : List α, c = s.map .inl ∨ c = .inr .left :: s.map .inl ∨
      c = s.map .inl ++ [.inr .right] ∨ c = anchor s := by
  have hmap (d : List (α ⊕ Edge)) (hd : d <:+: v.map .inl) :
      d = (d.filterMap Sum.getLeft?).map .inl :=
    eq_map_inl_filterMap fun x hx ↦ by obtain ⟨a, -, rfl⟩ := List.mem_map.1 (hd.subset hx); rfl
  rw [anchor, List.infix_cons_iff] at h
  rcases h with h | h
  · rcases List.prefix_cons_iff.1 h with rfl | ⟨t, rfl, ht⟩
    · exact ⟨[], .inl rfl⟩
    · rcases List.prefix_concat_iff.1 ht with rfl | ht
      · exact ⟨v, .inr (.inr (.inr rfl))⟩
      · exact ⟨_, .inr (.inl (congrArg _ (hmap t ht.isInfix)))⟩
  · rcases List.infix_concat_iff.1 h with h | h
    · rcases List.suffix_concat_iff.1 h with rfl | ⟨t, rfl, ht⟩
      · exact ⟨[], .inl rfl⟩
      · exact ⟨_, .inr (.inr (.inl (congrArg (· ++ _) (hmap t ht.isInfix))))⟩
    · exact ⟨_, .inl (hmap c h)⟩

end Anchor

/-! ### Locally testable stringsets -/

section LocallyTestable

variable {w v : List α} {k : ℕ}

private theorem eq_of_kTestVector_eq (h : w.kTestVector k = v.kTestVector k) (hw : w.length < k) :
    w = v := by
  simp only [List.kTestVector, Prod.mk.injEq, Edge.takeAt_left, Edge.takeAt_right] at h
  obtain ⟨hP, hK, -⟩ := h
  have hv : v.length < k := by
    by_contra hv
    have := ((Set.ext_iff.1 hK (v.take k)).2
      ⟨(List.take_prefix _ _).isInfix, by simp; omega⟩).1.length_le
    simp at this
    omega
  rwa [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hP

theorem kTestVector_eq_iff :
    w.kTestVector k = v.kTestVector k ↔
      {c | c <:+: anchor w ∧ c.length ≤ k} = {c | c <:+: anchor v ∧ c.length ≤ k} := by
  constructor
  · have sub (w v : List α) (h : w.kTestVector k = v.kTestVector k) :
        {c | c <:+: anchor w ∧ c.length ≤ k} ⊆ {c | c <:+: anchor v ∧ c.length ≤ k} := by
      rintro c ⟨hc, hck⟩
      refine ⟨?_, hck⟩
      by_cases hw : w.length < k
      · rwa [← eq_of_kTestVector_eq h hw]
      have h' := h
      simp only [List.kTestVector, Prod.mk.injEq, Edge.takeAt_left, Edge.takeAt_right] at h'
      obtain ⟨hP, hK, hQ⟩ := h'
      obtain ⟨s, rfl | rfl | rfl | rfl⟩ := infix_anchor_cases hc
      · rw [map_inl_infix_anchor_iff] at hc ⊢
        obtain ⟨f, hfw, hfk, hsf⟩ := exists_infix_length_eq hc (by simpa using hck) (by omega)
        exact hsf.trans ((Set.ext_iff.1 hK f).1 ⟨hfw, hfk⟩).1
      · rw [cons_infix_anchor_iff] at hc ⊢
        have : s <+: w.take (k - 1) := List.prefix_take_iff.2 ⟨hc, by simp at hck; omega⟩
        rw [hP] at this
        exact this.trans (List.take_prefix _ _)
      · rw [append_infix_anchor_iff] at hc ⊢
        have : s <:+ w.rtake (k - 1) := List.suffix_rtake_iff.2 ⟨hc, by simp at hck; omega⟩
        rw [hQ] at this
        exact this.trans (List.rtake_suffix _ _)
      · obtain rfl := eq_of_anchor_infix_anchor hc
        simp at hck
        omega
    exact fun h ↦ (sub w v h).antisymm (sub v w h.symm)
  · intro hA
    have mem (c : List (α ⊕ Edge)) (hc : c.length ≤ k) : c <:+: anchor w ↔ c <:+: anchor v := by
      simpa [hc] using Set.ext_iff.1 hA c
    simp only [List.kTestVector, Prod.mk.injEq, Edge.takeAt_left, Edge.takeAt_right]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨by simp, Set.ext fun f ↦ ?_, by simp⟩
      simp only [Set.mem_ofPred_eq, List.length_eq_zero_iff]
      constructor <;> rintro ⟨-, rfl⟩ <;> exact ⟨List.nil_infix, rfl⟩
    have pre (w v : List α) (mem : ∀ c : List (α ⊕ Edge), c.length ≤ k →
        c <:+: anchor w → c <:+: anchor v) : w.take (k - 1) <+: v.take (k - 1) :=
      List.prefix_take_iff.2 ⟨cons_infix_anchor_iff.1 (mem _ (by simp; omega)
        (cons_infix_anchor_iff.2 (List.take_prefix _ _))), by simp⟩
    have suf (w v : List α) (mem : ∀ c : List (α ⊕ Edge), c.length ≤ k →
        c <:+: anchor w → c <:+: anchor v) : w.rtake (k - 1) <:+ v.rtake (k - 1) :=
      List.suffix_rtake_iff.2 ⟨append_infix_anchor_iff.1 (mem _ (by simp; omega)
        (append_infix_anchor_iff.2 (List.rtake_suffix _ _))), by simp⟩
    refine ⟨(pre w v fun c hc ↦ (mem c hc).1).eq_of_length
        (le_antisymm (pre w v fun c hc ↦ (mem c hc).1).length_le
          (pre v w fun c hc ↦ (mem c hc).2).length_le), Set.ext fun f ↦ ?_,
      (suf w v fun c hc ↦ (mem c hc).1).eq_of_length
        (le_antisymm (suf w v fun c hc ↦ (mem c hc).1).length_le
          (suf v w fun c hc ↦ (mem c hc).2).length_le)⟩
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hf, rfl⟩
      exact ⟨map_inl_infix_anchor_iff.1 ((mem _ (by simp)).1 (map_inl_infix_anchor_iff.2 hf)), rfl⟩
    · rintro ⟨hf, rfl⟩
      exact ⟨map_inl_infix_anchor_iff.1 ((mem _ (by simp)).2 (map_inl_infix_anchor_iff.2 hf)), rfl⟩

end LocallyTestable

/-! ### Strictly local stringsets -/

section StrictlyLocal

variable {u₁ v₁ u₂ v₂ x : List α} {k : ℕ}

theorem factors_crossover_subset (hx : x.length = k - 1) :
    (wordLanguage (α ⊕ Edge)).factors k (WordModel (anchor (u₁ ++ x ++ v₂)) (· ⋖ ·)) ⊆
      (wordLanguage (α ⊕ Edge)).factors k (WordModel (anchor (u₁ ++ x ++ v₁)) (· ⋖ ·)) ∪
        (wordLanguage (α ⊕ Edge)).factors k (WordModel (anchor (u₂ ++ x ++ v₂)) (· ⋖ ·)) := by
  rw [anchor_append_append, anchor_append_append, anchor_append_append]
  refine (WordModel.factors_append_append_subset (by simp; omega)).trans
    (Set.union_subset_union (WordModel.factors_subset_of_infix ?_)
      (WordModel.factors_subset_of_infix ?_))
  · exact (List.prefix_append _ _).isInfix
  · rw [List.append_assoc]
    exact (List.suffix_append _ _).isInfix

variable {L : _root_.Language α}

theorem mem_of_factors_subset_biUnion (hL : L.SuffixSubstitutionClosed k) (hk : 2 ≤ k)
    {w : List α} (hw : (wordLanguage (α ⊕ Edge)).factors k (WordModel (anchor w) (· ⋖ ·)) ⊆
      ⋃ v ∈ L, (wordLanguage (α ⊕ Edge)).factors k (WordModel (anchor v) (· ⋖ ·))) :
    w ∈ L := by
  have hinfix (c : List (α ⊕ Edge)) (hc : c <:+: anchor w) (hlen : c.length ≤ k) :
      ∃ v ∈ L, c <:+: anchor v := by
    obtain ⟨v, hv, hcv⟩ := Set.mem_iUnion₂.1
      (hw ((WordModel.succDiagram_occurs_iff hlen).2 hc))
    exact ⟨v, hv, (WordModel.succDiagram_occurs_iff hlen).1 hcv⟩
  by_cases hshort : w.length + 2 ≤ k
  · obtain ⟨v, hv, hwv⟩ := hinfix (anchor w) (List.infix_refl _) (by simpa using hshort)
    rwa [eq_of_anchor_infix_anchor hwv]
  refine hL.mem_of_exists_infix hk (by omega) ?_ (fun s hs hlen ↦ ?_) ?_
  · obtain ⟨v, hv, hcv⟩ := hinfix (.inr .left :: (w.take (k - 1)).map .inl)
      (cons_infix_anchor_iff.2 (List.take_prefix _ _)) (by simp; omega)
    exact ⟨v, hv, prefix_of_infix_anchor hcv⟩
  · obtain ⟨v, hv, hcv⟩ := hinfix (s.map .inl) (map_inl_infix_anchor_iff.2 hs) (by simp [hlen])
    exact ⟨v, hv, infix_of_map_inl_infix_anchor hcv⟩
  · obtain ⟨v, hv, hcv⟩ := hinfix ((w.rtake (k - 1)).map .inl ++ [.inr .right])
      (append_infix_anchor_iff.2 (List.rtake_suffix _ _)) (by simp; omega)
    exact ⟨v, hv, suffix_of_infix_anchor hcv⟩

end StrictlyLocal


end Subregular

open Subregular

namespace Language

variable {α : Type u} {L : Language α} {k : ℕ}

/-- A stringset is strictly `k`-piecewise exactly when it is a strictly `k`-local set of
precedence models. -/
theorem isStrictlyPiecewise_iff_wordModel :
    L.IsStrictlyPiecewise k ↔ (wordLanguage α).IsStrictlyLocal (WordModel · (· < ·)) k L := by
  rw [isStrictlyLocal_iff]
  constructor
  · intro hL w hw
    rw [← hL.language_self]
    intro s hs hsw
    obtain ⟨v, hv, hsv⟩ := Set.mem_iUnion₂.1 (hw ((WordModel.diagram_occurs_iff hs).2 hsw))
    exact hL.isSublistClosed ((WordModel.diagram_occurs_iff hs).1 hsv) hv
  · intro hS
    refine ⟨L, le_antisymm (fun w hw ↦ hS w fun f hf ↦ ?_) fun w hw s _ hs ↦ ?_⟩
    · obtain ⟨s, hsw, hs, hfs⟩ := WordModel.exists_sublist_of_occurs hf
      exact Set.mem_iUnion₂.2 ⟨s, hw s hs hsw, hfs⟩
    · exact hS s fun f hf ↦ Set.mem_iUnion₂.2 ⟨w, hw, WordModel.factors_subset_of_sublist hs hf⟩

/-- A stringset is strictly `k`-local, for `2 ≤ k`, exactly when it is a strictly `k`-local set of
anchored words ordered by successor. -/
theorem isStrictlyLocal_iff_wordModel (hk : 2 ≤ k) :
    L.IsStrictlyLocal k ↔
      (wordLanguage (α ⊕ Edge)).IsStrictlyLocal (fun w ↦ WordModel (anchor w) (· ⋖ ·)) k L := by
  rw [isStrictlyLocal_iff_suffixSubstitutionClosed hk, FirstOrder.Language.isStrictlyLocal_iff]
  refine ⟨fun hL w hw ↦ mem_of_factors_subset_biUnion hL hk hw, fun hS u₁ v₁ u₂ v₂ x hx h₁ h₂ ↦ ?_⟩
  exact (FirstOrder.Language.isStrictlyLocal_iff.2 hS).mem_of_factors_subset_union h₁ h₂
    (factors_crossover_subset hx)

/-- A stringset is tier-based strictly `k`-local, for `2 ≤ k`, exactly when for some tier it is a
strictly `k`-local set of words under successor relativized to the tier. Restricting a word to
its tier positions and taking successor there gives the successor model of its projection, so
the relativized models are those of the projections. -/
theorem isTierStrictlyLocal_iff_wordModel (hk : 2 ≤ k) :
    L.IsTierStrictlyLocal k ↔ ∃ (T : α → Prop) (_ : DecidablePred T),
      (wordLanguage (α ⊕ Edge)).IsStrictlyLocal
        (fun w ↦ WordModel (anchor (w.filter (T ·))) (· ⋖ ·)) k L := by
  constructor
  · rintro ⟨G, rfl⟩
    exact ⟨G.tier, inferInstance,
      ((isStrictlyLocal_iff_wordModel hk).1 ⟨G.permitted, rfl⟩).comap
        fun w : List α ↦ w.filter (G.tier ·)⟩
  · rintro ⟨T, _, G', rfl⟩
    obtain ⟨G₀, hG₀⟩ := (isStrictlyLocal_iff_wordModel hk).2 ⟨G', rfl⟩
    exact ⟨⟨T, G₀⟩, Set.ext fun w ↦ Set.ext_iff.1 hG₀ (w.filter (T ·))⟩

/-- A stringset is piecewise `k`-testable exactly when it is a locally `k`-testable set of words
under precedence. -/
theorem isPiecewiseTestable_iff_wordModel :
    L.IsPiecewiseTestable k ↔ (wordLanguage α).IsLocallyTestable (WordModel · (· < ·)) k L :=
  ⟨fun h _ _ e ↦ h (WordModel.factors_eq_iff_subseqSet.1 e),
    fun h _ _ e ↦ h (WordModel.factors_eq_iff_subseqSet.2 e)⟩

/-- A stringset is locally `k`-testable exactly when it is a locally `k`-testable set of words
between their edges under successor. -/
theorem isLocallyTestable_iff_wordModel :
    L.IsLocallyTestable k ↔
      (wordLanguage (α ⊕ Edge)).IsLocallyTestable (fun w ↦ WordModel (anchor w) (· ⋖ ·)) k L := by
  have key (w v : List α) : w.kTestVector k = v.kTestVector k ↔
      (wordLanguage (α ⊕ Edge)).factors k (WordModel (anchor w) (· ⋖ ·)) =
        (wordLanguage (α ⊕ Edge)).factors k (WordModel (anchor v) (· ⋖ ·)) :=
    kTestVector_eq_iff.trans WordModel.factors_eq_iff_infix.symm
  exact ⟨fun h _ _ e ↦ h ((key _ _).2 e), fun h _ _ e ↦ h ((key _ _).1 e)⟩

end Language
