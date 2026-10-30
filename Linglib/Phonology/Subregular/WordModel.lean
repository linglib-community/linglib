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
symbol, related by an ordering of the positions. In the conventional model a symbol is its own one
label; in a feature-labelled model, Chandlee, Eyraud, Heinz, Jardine and Rawski's for segments, it
carries the values of its features, so that a position of a factor stands for a natural class. Two orderings recover the two strict classes of
stringsets as strictly local sets of word models. Under precedence, a factor occurring in a word
occurs in the subsequence its occurrence picks out, and a subsequence is itself a factor, its
positive diagram, so the strictly local sets are the strictly piecewise stringsets. Under
successor, the covering relation of the positions, an occurrence of a `k`-factor spans fewer than
`k` steps, so it misses one side of any `k - 1` symbols, and the strictly local sets of words
between their edges are the strictly local stringsets. Relativizing successor to a tier, by
restricting a word to its tier positions and taking successor there, gives the successor model of
the word's projection, so the strictly local sets of relativized models are the tier-based
strictly local stringsets. A set is locally testable when membership depends only on the set of
factors; under successor the factors of a word are fixed by the infixes of at most `k` symbols of
the word between its edges, and these by its `k`-test vector, and under precedence by its
subsequences of at most `k` symbols.

## Main definitions

* `Subregular.wordLanguage`: the signature of word models, a unary relation for each label and
  an ordering.
* `Subregular.Labelling`: the labels a symbol carries, itself alone in the conventional model
  and the values of its features in a feature-labelled one.
* `Subregular.WordModel`: a word under an ordering of its positions.
* `Subregular.anchor`: a word between its edges.

## Main statements

* `Language.isStrictlyLocal_iff_wordModel`, `Language.isLocallyTestable_iff_wordModel`: the
  strictly local and locally testable stringsets are the strictly local and locally testable sets
  of words between their edges under successor.
* `Language.isStrictlyPiecewise_iff_wordModel`, `Language.isPiecewiseTestable_iff_wordModel`: the
  strictly piecewise and piecewise testable stringsets are those of words under precedence.
* `Language.isTierStrictlyLocal_iff_wordModel`: the tier-based strictly local stringsets are the
  strictly local sets of words under successor relativized to a tier.
* `Subregular.WordModel.diagram_occurs_iff_forall₂`,
  `Subregular.WordModel.succDiagram_occurs_iff_forall₂`: a word's diagram occurs under precedence,
  respectively successor, exactly in the words with a subsequence, respectively infix, whose
  positions carry its labels; for words of segments this is subsumption, position by position.

## Implementation notes

* An ordering is a relation on the positions passed to `WordModel`, so precedence is
  `WordModel w (· < ·)` and successor `WordModel (anchor w) (· ⋖ ·)`.
* As in Rogers and Lambert's word models, the edges carry their own labels and are not related to
  themselves. The strictly local stringsets pad a word with `k - 1` boundary symbols instead, and
  the two classes differ only at `k = 1`, where the word models also forbid every word; the
  locally testable classes agree at every `k`.

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

theorem mem_realizers_of_subset {n : ℕ} {T : Set ((wordLanguage P).Atom (Fin n))}
    {v : Fin n → WordModel u R} {v' : Fin n → WordModel u' R'}
    (hlabel : ∀ x, Labelling.labels (P := P) (v x).label ⊆ Labelling.labels (v' x).label)
    (hord : ∀ x y, R (v x) (v y) → R' (v' x) (v' y))
    (hv : v ∈ Atom.realizers (WordModel u R) T) : v' ∈ Atom.realizers (WordModel u' R') T := by
  refine Atom.mem_realizers.2 fun ⟨r, args⟩ ha ↦ ?_
  have h := Atom.mem_realizers.1 hv _ ha
  cases r with
  | label p => exact hlabel (args 0) h
  | ord => exact hord _ _ h

theorem mem_realizers_of {n : ℕ} {T : Set ((wordLanguage P).Atom (Fin n))}
    {v : Fin n → WordModel u R} {v' : Fin n → WordModel u' R'}
    (hlabel : ∀ x, (v' x).label = (v x).label) (hord : ∀ x y, R (v x) (v y) → R' (v' x) (v' y))
    (hv : v ∈ Atom.realizers (WordModel u R) T) : v' ∈ Atom.realizers (WordModel u' R') T :=
  mem_realizers_of_subset (fun x ↦ by rw [hlabel x]) hord hv

/-! ### Precedence -/

section Precedence

variable {w w' : List α}

theorem factors_subset_of_sublist [Labelling α P] {k : ℕ} (h : w <+ w') :
    (wordLanguage P).factors k (WordModel w (· < ·)) ⊆
      (wordLanguage P).factors k (WordModel w' (· < ·)) := by
  obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.1 h
  rintro f ⟨v, hv⟩
  exact ⟨fun x ↦ show WordModel w' (· < ·) from e (v x),
    mem_realizers_of (fun x ↦ (he (v x)).symm) (fun x y h ↦ e.lt_iff_lt.2 h) hv⟩

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
  · exact hlen.le.trans ((Finset.card_image_le.trans (by simp)).trans f.le)
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
  le := hs
  atoms := {a | a.Realize (M := WordModel s (· < ·)) id}
  preconnected x y := by
    rcases lt_trichotomy x y with h | rfl | h
    · exact SimpleGraph.Adj.reachable
        ⟨h.ne, .inl ⟨⟨.ord, ![x, y]⟩, by exact h, ⟨0, rfl⟩, ⟨1, rfl⟩⟩⟩
    · rfl
    · exact SimpleGraph.Adj.reachable
        ⟨h.ne', .inr ⟨⟨.ord, ![y, x]⟩, by exact h, ⟨0, rfl⟩, ⟨1, rfl⟩⟩⟩

/-- The diagram of a word occurs exactly in the words with a subsequence whose positions carry
its labels, position by position. -/
theorem diagram_occurs_iff_forall₂ [Labelling α P] {s : List α} {k : ℕ} (hs : s.length ≤ k) :
    (diagram P s hs).Occurs (WordModel w (· < ·)) ↔
      ∃ t, t <+ w ∧
        List.Forall₂ (fun a b ↦ Labelling.labels (P := P) a ⊆ Labelling.labels b) s t := by
  constructor
  · rintro ⟨v, hv⟩
    have hle (i : Fin s.length) :
        Labelling.labels (P := P) (s.get i) ⊆ Labelling.labels (WordModel.label (v i)) :=
      fun p hp ↦ Atom.mem_realizers.1 hv ⟨.label p, ![i]⟩ hp
    have hmono : StrictMono fun i ↦ show Fin w.length from v i := fun i j hij ↦
      Atom.mem_realizers.1 hv ⟨.ord, ![i, j]⟩ hij
    refine ⟨List.ofFn fun i ↦ w.get (v i), List.sublist_iff_exists_fin_orderEmbedding_get_eq.2
      ⟨(Fin.castOrderIso List.length_ofFn).toOrderEmbedding.trans
        (OrderEmbedding.ofStrictMono _ hmono), fun i ↦ by simp only [List.get_ofFn]; rfl⟩, ?_⟩
    rw [List.forall₂_iff_get]
    refine ⟨List.length_ofFn.symm, fun i h₁ _ ↦ ?_⟩
    simp only [List.get_ofFn]
    exact hle ⟨i, h₁⟩
  · rintro ⟨t, htw, hst⟩
    obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.1 hst
    refine factors_subset_of_sublist htw ⟨fun i ↦ show WordModel t (· < ·) from Fin.cast hlen i,
      mem_realizers_of_subset (fun i ↦ hget i i.2 (hlen ▸ i.2)) (fun i j h ↦ by exact h)
        (v := id) (fun _ ha ↦ ha)⟩

theorem diagram_occurs_iff {s : List α} {k : ℕ} (hs : s.length ≤ k) :
    (diagram α s hs).Occurs (WordModel w (· < ·)) ↔ s <+ w := by
  simp only [diagram_occurs_iff_forall₂, Labelling.labels_self, Set.singleton_subset_singleton,
    List.forall₂_eq_eq_eq, exists_eq_right']

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

/-! ### Orderings with unit steps -/

section UnitSteps

variable {n : ℕ} {T : Set ((wordLanguage P).Atom (Fin n))} {r : Fin n → WordModel u R}

theorem le_add_one_of_adj (hR : ∀ a b, R a b → (a : ℕ) ≤ b + 1 ∧ (b : ℕ) ≤ a + 1)
    (hr : r ∈ Atom.realizers (WordModel u R) T) {x y : Fin n} (h : (Atom.gaifman T).Adj x y) :
    ((r x).toFin : ℕ) ≤ (r y).toFin + 1 := by
  obtain ⟨hne, hxy⟩ := h
  have key : ∀ a ∈ T, x ∈ Set.range a.args → y ∈ Set.range a.args →
      ((r x).toFin : ℕ) ≤ (r y).toFin + 1 := by
    rintro ⟨_ | _, args⟩ ha ⟨i, rfl⟩ ⟨j, rfl⟩
    · exact absurd (congrArg args (Subsingleton.elim i j)) hne
    · have hR' := hR _ _ (Atom.mem_realizers.1 hr _ ha)
      fin_cases i <;> fin_cases j
      · exact absurd rfl hne
      · exact hR'.1
      · exact hR'.2
      · exact absurd rfl hne
  rcases hxy with ⟨a, ha, hx, hy⟩ | ⟨a, ha, hy, hx⟩ <;> exact key a ha hx hy

theorem le_add_of_occurs {k : ℕ} {f : (wordLanguage P).Factor k}
    (hR : ∀ a b, R a b → (a : ℕ) ≤ b + 1 ∧ (b : ℕ) ≤ a + 1)
    {r : Fin f.n → WordModel u R} (hr : r ∈ Atom.realizers (WordModel u R) f.atoms)
    (x y : Fin f.n) : ((r x).toFin : ℕ) ≤ (r y).toFin + (k - 1) := by
  have walk : ∀ {a b : Fin f.n} (p : (Atom.gaifman f.atoms).Walk a b),
      ((r a).toFin : ℕ) ≤ (r b).toFin + p.length := by
    intro a b p
    induction p with
    | nil => simp
    | cons h p ih =>
      have := le_add_one_of_adj hR hr h
      simp only [SimpleGraph.Walk.length_cons]
      omega
  obtain ⟨p⟩ := f.preconnected x y
  have hlen := p.toPath.2.length_lt
  simp only [Fintype.card_fin] at hlen
  have := walk p.toPath.1
  have := f.le
  omega

end UnitSteps

/-! ### Successor -/

theorem covBy_unit {m : ℕ} (a b : Fin m) (h : a ⋖ b) : (a : ℕ) ≤ b + 1 ∧ (b : ℕ) ≤ a + 1 := by
  rw [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h
  omega

theorem factors_subset_of_infix {k : ℕ} {c u : List β} (h : c <:+: u) :
    (wordLanguage P).factors k (WordModel c (· ⋖ ·)) ⊆
      (wordLanguage P).factors k (WordModel u (· ⋖ ·)) := by
  obtain ⟨t, hlen, ht⟩ := List.infix_iff_getElem?.1 h
  have hlt (i : Fin c.length) : (i : ℕ) + t < u.length := by omega
  rintro f ⟨r, hr⟩
  refine ⟨fun a ↦ show WordModel u (· ⋖ ·) from ⟨(r a).toFin + t, hlt _⟩,
    mem_realizers_of (fun a ↦ ?_) (fun a b hab ↦ ?_) hr⟩
  · have := ht _ (r a).toFin.2
    rw [List.getElem?_eq_getElem (hlt _)] at this
    exact Option.some_injective _ this
  · change (r a).toFin ⋖ (r b).toFin at hab
    change (⟨_, hlt _⟩ : Fin u.length) ⋖ ⟨_, hlt _⟩
    simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at hab ⊢
    omega

theorem exists_infix_of_occurs {k : ℕ} {u : List β} {f : (wordLanguage P).Factor k}
    (hf : f.Occurs (WordModel u (· ⋖ ·))) :
    ∃ c, c <:+: u ∧ c.length ≤ k ∧ f.Occurs (WordModel c (· ⋖ ·)) := by
  obtain ⟨r, hr⟩ := hf
  rcases Nat.eq_zero_or_pos f.n with h0 | hpos
  · refine ⟨[], List.nil_infix, by simp, fun x ↦ absurd x.2 (by omega),
      Atom.mem_realizers.2 fun ⟨rel, args⟩ _ ↦ ?_⟩
    cases rel <;> exact absurd (args 0).2 (by omega)
  have hne : (Finset.univ : Finset (Fin f.n)).Nonempty := ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_mem_eq_inf' hne fun a ↦ ((r a).toFin : ℕ)
  have hm (a) : ((r a₀).toFin : ℕ) ≤ (r a).toFin := ha₀ ▸ Finset.inf'_le _ (Finset.mem_univ a)
  have hspan := le_add_of_occurs covBy_unit hr
  set m := ((r a₀).toFin : ℕ)
  have hk : 1 ≤ k := hpos.trans_le f.le
  have hlt (a) : ((r a).toFin : ℕ) - m < ((u.drop m).take k).length := by
    have := hspan a a₀
    have := (r a).toFin.2
    simp only [List.length_take, List.length_drop]
    omega
  refine ⟨(u.drop m).take k, (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix,
    List.length_take_le _ _, fun a ↦ show WordModel ((u.drop m).take k) (· ⋖ ·) from
      ⟨(r a).toFin - m, hlt a⟩, mem_realizers_of (fun a ↦ ?_) (fun a b hab ↦ ?_) hr⟩
  · change ((u.drop m).take k)[((r a).toFin : ℕ) - m]'(hlt a) =
      u[((r a).toFin : ℕ)]'(r a).toFin.2
    simp only [List.getElem_take, List.getElem_drop]
    congr 1
    have := hm a
    omega
  · change (r a).toFin ⋖ (r b).toFin at hab
    change (⟨_, hlt a⟩ : Fin _) ⋖ ⟨_, hlt b⟩
    have := hm a
    simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at hab ⊢
    omega

/-- The diagram of a word under successor, as a `k`-factor of the labels `P`: the path of its
positions, each carrying the labels of its symbol. -/
def succDiagram (P : Type*) [Labelling β P] (c : List β) {k : ℕ} (hc : c.length ≤ k) :
    (wordLanguage P).Factor k where
  n := c.length
  le := hc
  atoms := {a | a.Realize (M := WordModel c (· ⋖ ·)) id}
  preconnected x y := by
    have hpos : 0 < c.length := x.pos
    have reach (i : ℕ) (hi : i < c.length) :
        (Atom.gaifman {a : (wordLanguage P).Atom (Fin c.length) |
          a.Realize (M := WordModel c (· ⋖ ·)) id}).Reachable ⟨0, hpos⟩ ⟨i, hi⟩ := by
      induction i with
      | zero => rfl
      | succ i ih =>
        refine (ih (by omega)).trans <| SimpleGraph.Adj.reachable
          ⟨by simp, .inl ⟨⟨.ord, ![⟨i, by omega⟩, ⟨i + 1, hi⟩]⟩, ?_, ⟨0, rfl⟩, ⟨1, rfl⟩⟩⟩
        change (⟨i, _⟩ : Fin c.length) ⋖ ⟨i + 1, hi⟩
        simp [Fin.covBy_iff]
    exact (reach x x.2).symm.trans (reach y y.2)

/-- The successor diagram of a word occurs exactly in the words with an infix whose positions
carry its labels, position by position. -/
theorem succDiagram_occurs_iff_forall₂ {c u : List β} {k : ℕ} (hc : c.length ≤ k) :
    (succDiagram P c hc).Occurs (WordModel u (· ⋖ ·)) ↔
      ∃ t, t <:+: u ∧
        List.Forall₂ (fun a b ↦ Labelling.labels (P := P) a ⊆ Labelling.labels b) c t := by
  constructor
  · rintro ⟨r₀, hr⟩
    let r : Fin c.length → WordModel u (· ⋖ ·) := r₀
    rcases Nat.eq_zero_or_pos c.length with h0 | hpos
    · rw [List.eq_nil_of_length_eq_zero h0]
      exact ⟨[], List.nil_infix, .nil⟩
    have hle (i : Fin c.length) :
        Labelling.labels (P := P) (c.get i) ⊆ Labelling.labels (r i).label :=
      fun p hp ↦ Atom.mem_realizers.1 hr ⟨.label p, ![i]⟩ hp
    have hsucc (i : ℕ) (hi : i + 1 < c.length) :
        ((r ⟨i + 1, hi⟩).toFin : ℕ) = (r ⟨i, by omega⟩).toFin + 1 := by
      have h := Atom.mem_realizers.1 hr ⟨.ord, ![⟨i, show i < c.length by omega⟩, ⟨i + 1, hi⟩]⟩ (by
        change (⟨i, _⟩ : Fin c.length) ⋖ ⟨i + 1, hi⟩
        simp [Fin.covBy_iff])
      change (r ⟨i, _⟩).toFin ⋖ (r ⟨i + 1, hi⟩).toFin at h
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
    exact hle ⟨i, h₁⟩
  · rintro ⟨t, htu, hct⟩
    obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.1 hct
    refine factors_subset_of_infix htu ⟨fun i ↦ show WordModel t (· ⋖ ·) from Fin.cast hlen i,
      mem_realizers_of_subset (fun i ↦ hget i i.2 (hlen ▸ i.2)) (fun i j h ↦ ?_)
        (v := id) (fun _ ha ↦ ha)⟩
    change (i : Fin c.length) ⋖ j at h
    change Fin.cast hlen i ⋖ Fin.cast hlen j
    simpa [Fin.covBy_iff] using h

theorem succDiagram_occurs_iff {c u : List β} {k : ℕ} (hc : c.length ≤ k) :
    (succDiagram β c hc).Occurs (WordModel u (· ⋖ ·)) ↔ c <:+: u := by
  simp only [succDiagram_occurs_iff_forall₂, Labelling.labels_self, Set.singleton_subset_singleton,
    List.forall₂_eq_eq_eq, exists_eq_right']

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

theorem getElem_anchor_append_of_le {p q q' : List α} {i : ℕ} (hi : i ≤ p.length)
    (h₁ : i < (anchor (p ++ q)).length) (h₂ : i < (anchor (p ++ q')).length) :
    (anchor (p ++ q))[i] = (anchor (p ++ q'))[i] := by
  cases i with
  | zero => rfl
  | succ j =>
    simp only [anchor, List.getElem_cons_succ, List.map_append, List.append_assoc]
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]

theorem getElem_anchor_append_of_ge {l l' p p' q : List α} (hl : l = p ++ q)
    (hl' : l' = p' ++ q) {i i' : ℕ} (hi : p.length + 1 ≤ i) (hi' : i' = i - p.length + p'.length)
    (h₁ : i < (anchor l).length) (h₂ : i' < (anchor l').length) :
    (anchor l)[i] = (anchor l')[i'] := by
  subst hl hl' hi'
  obtain ⟨j, rfl⟩ : ∃ j, i = p.length + 1 + j := ⟨i - p.length - 1, by omega⟩
  have e : p.length + 1 + j - p.length + p'.length = p'.length + 1 + j := by omega
  simp only [e]
  simp only [anchor, List.map_append, List.append_assoc, show ∀ m, m + 1 + j = (m + j) + 1 by
    intro m; omega, List.getElem_cons_succ]
  have key (r : List α)
      (h : r.length + j < (r.map Sum.inl ++ (q.map Sum.inl ++ [Sum.inr Edge.right])).length) :
      (r.map Sum.inl ++ (q.map Sum.inl ++ [(Sum.inr Edge.right : α ⊕ Edge)]))[r.length + j] =
        (q.map Sum.inl ++ [Sum.inr Edge.right])[j]'(by simp at h ⊢; omega) := by
    rw [List.getElem_append_right (by simp)]
    simp only [List.length_map, Nat.add_sub_cancel_left]
  rw [key, key]

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

private theorem suffix_rtake_iff {s : List α} {n : ℕ} :
    s <:+ w.rtake n ↔ s <:+ w ∧ s.length ≤ n := by
  rw [List.rtake_eq_reverse_take_reverse, ← List.reverse_prefix, List.reverse_reverse,
    List.prefix_take_iff, List.reverse_prefix, List.length_reverse]

private theorem exists_infix_length_eq {s : List α} (h : s <:+: w) (hs : s.length ≤ k)
    (hk : k ≤ w.length) : ∃ f, f <:+: w ∧ f.length = k ∧ s <:+: f := by
  obtain ⟨t, ht, hget⟩ := List.infix_iff_getElem?.1 h
  refine ⟨(w.drop (min t (w.length - k))).take k,
    (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix, by simp; omega,
    List.infix_iff_getElem?.2 ⟨t - min t (w.length - k), by simp; omega, fun i hi ↦ ?_⟩⟩
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, ← hget i hi]
  congr 1
  omega

private theorem eq_of_kTestVector_eq (h : w.kTestVector k = v.kTestVector k) (hw : w.length < k) :
    w = v := by
  simp only [List.kTestVector, Prod.mk.injEq, Edge.takeAt_left, Edge.takeAt_right] at h
  obtain ⟨hP, hK, -⟩ := h
  have hv : v.length < k := by
    by_contra hv
    have hmem : v.take k ∈ v.kFactors k :=
      List.mem_kFactors.2 ⟨(List.take_prefix _ _).isInfix, by simp; omega⟩
    have := ((List.mem_kFactors.1 ((Set.ext_iff.1 hK _).2 hmem)).1).length_le
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
        exact hsf.trans (List.mem_kFactors.1
          ((Set.ext_iff.1 hK f).1 (List.mem_kFactors.2 ⟨hfw, hfk⟩))).1
      · rw [cons_infix_anchor_iff] at hc ⊢
        have : s <+: w.take (k - 1) := List.prefix_take_iff.2 ⟨hc, by simp at hck; omega⟩
        rw [hP] at this
        exact this.trans (List.take_prefix _ _)
      · rw [append_infix_anchor_iff] at hc ⊢
        have : s <:+ w.rtake (k - 1) := suffix_rtake_iff.2 ⟨hc, by simp at hck; omega⟩
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
    · refine ⟨by simp, Set.ext fun f ↦ ?_, by simp [List.rtake]⟩
      simp only [Set.mem_ofPred_eq, List.mem_kFactors, List.length_eq_zero_iff]
      constructor <;> rintro ⟨-, rfl⟩ <;> exact ⟨List.nil_infix, rfl⟩
    have pre (w v : List α) (mem : ∀ c : List (α ⊕ Edge), c.length ≤ k →
        c <:+: anchor w → c <:+: anchor v) : w.take (k - 1) <+: v.take (k - 1) :=
      List.prefix_take_iff.2 ⟨cons_infix_anchor_iff.1 (mem _ (by simp; omega)
        (cons_infix_anchor_iff.2 (List.take_prefix _ _))), by simp⟩
    have suf (w v : List α) (mem : ∀ c : List (α ⊕ Edge), c.length ≤ k →
        c <:+: anchor w → c <:+: anchor v) : w.rtake (k - 1) <:+ v.rtake (k - 1) :=
      suffix_rtake_iff.2 ⟨append_infix_anchor_iff.1 (mem _ (by simp [List.rtake]; omega)
        (append_infix_anchor_iff.2 (List.rtake_suffix _ _))), by simp [List.rtake]; omega⟩
    refine ⟨(pre w v fun c hc ↦ (mem c hc).1).eq_of_length
        (le_antisymm (pre w v fun c hc ↦ (mem c hc).1).length_le
          (pre v w fun c hc ↦ (mem c hc).2).length_le), Set.ext fun f ↦ ?_,
      (suf w v fun c hc ↦ (mem c hc).1).eq_of_length
        (le_antisymm (suf w v fun c hc ↦ (mem c hc).1).length_le
          (suf v w fun c hc ↦ (mem c hc).2).length_le)⟩
    simp only [Set.mem_ofPred_eq, List.mem_kFactors]
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
  rintro f ⟨r, hr⟩
  have hspan := WordModel.le_add_of_occurs WordModel.covBy_unit hr
  by_cases hA : ∀ a, ((r a).toFin : ℕ) ≤ u₁.length + x.length
  · refine .inl ⟨fun a ↦ show WordModel (anchor (u₁ ++ x ++ v₁)) (· ⋖ ·) from
      ⟨(r a).toFin, by have := hA a; simp; omega⟩,
      WordModel.mem_realizers_of (fun a ↦ ?_) (fun a b h ↦ ?_) hr⟩
    · exact getElem_anchor_append_of_le (by simpa using hA a) _ _
    · change (r a).toFin ⋖ (r b).toFin at h
      change (⟨_, _⟩ : Fin _) ⋖ ⟨_, _⟩
      simpa only [Fin.covBy_iff] using h
  · obtain ⟨a₀, ha₀⟩ := by simpa only [not_forall, not_le] using hA
    have hge (a) : u₁.length + 1 ≤ ((r a).toFin : ℕ) := by have := hspan a₀ a; omega
    have hlt (a) : ((r a).toFin : ℕ) < u₁.length + x.length + v₂.length + 2 := by
      have := (r a).toFin.2
      simp only [length_anchor, List.length_append] at this
      omega
    refine .inr ⟨fun a ↦ show WordModel (anchor (u₂ ++ x ++ v₂)) (· ⋖ ·) from
      ⟨(r a).toFin - u₁.length + u₂.length, by have := hge a; have := hlt a; simp; omega⟩,
      WordModel.mem_realizers_of (fun a ↦ ?_) (fun a b h ↦ ?_) hr⟩
    · exact (getElem_anchor_append_of_ge (List.append_assoc ..) (List.append_assoc ..) (hge a)
        rfl _ _).symm
    · change (r a).toFin ⋖ (r b).toFin at h
      change (⟨_, _⟩ : Fin _) ⋖ ⟨_, _⟩
      have := hge a
      have := hge b
      simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h ⊢
      omega

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
  have hmid : (w.map Sum.inl : List (α ⊕ Edge)) <:+: anchor w :=
    ⟨[.inr .left], [.inr .right], by simp [anchor]⟩
  by_cases hshort : w.length + 2 ≤ k
  · obtain ⟨v, hv, hwv⟩ := hinfix (anchor w) (List.infix_refl _) (by simpa using hshort)
    rwa [eq_of_anchor_infix_anchor hwv]
  have hmw : k - 1 ≤ w.length := by omega
  -- A member extends each prefix of `w` of at least `k - 1` symbols.
  have hpre (j : ℕ) (hj : k - 1 ≤ j) (hjw : j ≤ w.length) : ∃ y, w.take j ++ y ∈ L := by
    induction j, hj using Nat.le_induction with
    | base =>
      obtain ⟨v, hv, hcv⟩ := hinfix (.inr .left :: (w.take (k - 1)).map .inl)
        ((List.cons_prefix_cons.2 ⟨rfl, ((List.take_prefix _ w).map _).trans
          (List.prefix_append _ _)⟩).isInfix) (by simp; omega)
      obtain ⟨y, rfl⟩ := prefix_of_infix_anchor hcv
      exact ⟨y, hv⟩
    | succ j hj ih =>
      obtain ⟨y, hy⟩ := ih (by omega)
      have hjlt : j < w.length := by omega
      have hx : ((w.take j).drop (j - (k - 1))).length = k - 1 := by simp; omega
      have hinf : (w.take j).drop (j - (k - 1)) ++ [(w[j])] <:+: w := by
        rw [← List.drop_append_of_le_length (by simp; omega),
          ← List.take_succ_eq_append_getElem hjlt]
        exact (List.drop_suffix _ _).isInfix.trans (List.take_prefix _ _).isInfix
      obtain ⟨v, hv, hcv⟩ := hinfix (((w.take j).drop (j - (k - 1)) ++ [(w[j])]).map .inl)
        ((hinf.map _).trans hmid) (by simp; omega)
      obtain ⟨u₂, v₂, rfl⟩ := infix_of_map_inl_infix_anchor hcv
      refine ⟨v₂, ?_⟩
      have := hL ((w.take j).take (j - (k - 1))) y u₂ ([(w[j])] ++ v₂) _ hx
        (by rwa [List.take_append_drop]) (by simpa only [List.append_assoc] using hv)
      rw [List.take_append_drop] at this
      rwa [List.take_succ_eq_append_getElem hjlt, List.append_assoc]
  obtain ⟨y, hy⟩ := hpre w.length hmw le_rfl
  rw [List.take_length] at hy
  have hx : (w.drop (w.length - (k - 1))).length = k - 1 := by simp; omega
  have hsuf : (w.drop (w.length - (k - 1))).map Sum.inl ++ [(.inr .right : α ⊕ Edge)] <:+
      anchor w := by
    obtain ⟨t, ht⟩ := (List.drop_suffix (w.length - (k - 1)) w).map (Sum.inl : α → α ⊕ Edge)
    exact ⟨.inr .left :: t, by rw [anchor, ← ht]; simp⟩
  obtain ⟨v, hv, hcv⟩ := hinfix _ hsuf.isInfix (by simp; omega)
  obtain ⟨u₂, rfl⟩ := suffix_of_infix_anchor hcv
  have := hL (w.take (w.length - (k - 1))) y u₂ [] _ hx (by rwa [List.take_append_drop])
    (by simpa using hv)
  simpa using this

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
    IsTierStrictlyLocal k L ↔ ∃ (T : α → Prop) (_ : DecidablePred T),
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
