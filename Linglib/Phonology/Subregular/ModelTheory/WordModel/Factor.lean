module

public import Linglib.Core.ModelTheory.Factor
public import Linglib.Phonology.Subregular.ModelTheory.WordModel.Basic
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Tactic.FinCases

/-!
# Homomorphisms and factors of word models

A homomorphism of word models carries the labels of each position and the orderings the signature
names. Under precedence it picks out a subsequence carrying the labels position by position, and
under successor an infix. A word's diagram occurs in a structure exactly when the word maps into
it, so the subfactor order on words is the subsequence order under precedence and the infix order
under successor, and under successor two words have the same factors exactly when they have the
same infixes of bounded length. In a feature-labelled model a symbol carries the values of
its features, so that a position of a factor stands for a natural class.

## Main definitions

* `Subregular.WordModel.hom`: a map of positions that keeps labels and orderings, as a
  homomorphism.
* `Subregular.WordModel.diagram`, `Subregular.WordModel.succDiagram`: the diagram of a word under
  precedence and under successor, as a factor.

## Main results

* `Subregular.WordModel.nonempty_hom_lt_iff`, `Subregular.WordModel.nonempty_hom_covBy_iff`: the
  homomorphisms of word models pick out subsequences under precedence and infixes under
  successor.
* `Subregular.WordModel.diagram_occurs_iff_nonempty_hom`,
  `Subregular.WordModel.succDiagram_occurs_iff_nonempty_hom`: a word's diagram occurs in a structure
  exactly when the word maps into it.
* `Subregular.WordModel.diagram_le_diagram_iff`,
  `Subregular.WordModel.succDiagram_le_succDiagram_iff`: the subfactor order on words is the
  subsequence order, respectively the infix order.
* `Subregular.WordModel.factors_eq_iff_infix`: under successor the factors of a word are determined
  by its infixes of bounded length.
* `Subregular.WordModel.factors_append_append_subset`: under successor a factor of a word around
  enough symbols occurs on one side of them.

## Implementation notes

* A homomorphism may add labels, so its condition on symbols is `ℓ a ⊆ ℓ b`.
* The results are about one ordering at a time, in the signatures `wordLanguage P {.prec}` and
  `wordLanguage P {.succ}`.

## References

* [rogers-lambert-2019]
* [chandlee-eyraud-heinz-jardine-rawski-2019]
-/

@[expose] public section

universe u

open FirstOrder FirstOrder.Language List

namespace Subregular

variable {α : Type u}

instance [Finite α] {S : Set WordOrd} : Finite (Σ n, (wordLanguage α S).Relations n) :=
  .of_injective (β := α ⊕ S) (fun | ⟨_, .label a⟩ => .inl a | ⟨_, .ord o⟩ => .inr o) <| by
    rintro ⟨_, _ | _⟩ ⟨_, _ | _⟩ h <;> simp_all

namespace WordModel

variable {β P : Type*} {ℓ : β → Set P} {u u' : List β} {S : Set WordOrd}

/-- A map of positions under which symbols keep their labels and positions their order is a
homomorphism of word models. -/
@[simps]
def hom (e : Fin u.length → Fin u'.length)
    (hlabel : ∀ i, ℓ (u.get i) ⊆ ℓ (u'.get (e i)))
    (hord : ∀ o ∈ S, ∀ i j : WordModel ℓ u, Rel o i j → Rel (ℓ := ℓ) (u := u') o (e i) (e j)) :
    WordModel ℓ u →[wordLanguage P S] WordModel ℓ u' where
  toFun := e
  map_fun' f := isEmptyElim f
  map_rel' r x h := by
    cases r with
    | label p => exact hlabel _ h
    | ord o => exact hord o o.2 _ _ h

theorem labels_subset_labels_hom (φ : WordModel ℓ u →[wordLanguage P S] WordModel ℓ u')
    (i : WordModel ℓ u) : ℓ i.label ⊆ ℓ (φ i).label :=
  fun p hp ↦ φ.map_rel (WordRel.label p) ![i] hp

theorem rel_hom (φ : WordModel ℓ u →[wordLanguage P S] WordModel ℓ u') (o : S)
    {i j : WordModel ℓ u} (h : Rel o i j) : Rel o (φ i) (φ j) :=
  φ.map_rel (WordRel.ord o) ![i, j] h

/-- An assignment moved along a map of the positions it uses, keeping their symbols and their
order, realizes what it realized. -/
theorem mem_realizers_of {n : ℕ} {T : Set ((wordLanguage P S).Atom (Fin n))}
    {v : Fin n → WordModel ℓ u} {v' : Fin n → WordModel ℓ u'}
    (hlabel : ∀ x, (v' x).label = (v x).label)
    (hord : ∀ o ∈ S, ∀ x y, Rel o (v x) (v y) → Rel o (v' x) (v' y))
    (hv : v ∈ Atom.realizers (WordModel ℓ u) T) : v' ∈ Atom.realizers (WordModel ℓ u') T := by
  refine Atom.mem_realizers.2 fun ⟨r, args⟩ ha ↦ ?_
  have h := Atom.mem_realizers.1 hv _ ha
  cases r with
  | label p =>
    change p ∈ ℓ (v' (args 0)).label
    rw [hlabel]
    exact h
  | ord o => exact hord o o.2 _ _ h

/-! ### Precedence -/

section Precedence

variable {w w' : List β}

/-- A homomorphism of word models under precedence picks out a subsequence whose positions carry
the labels, position by position. -/
theorem nonempty_hom_lt_iff :
    Nonempty (WordModel ℓ w →[wordLanguage P {.prec}] WordModel ℓ w') ↔
      ∃ t, t <+ w' ∧ List.Forall₂ (fun a b ↦ ℓ a ⊆ ℓ b) w t := by
  constructor
  · rintro ⟨φ⟩
    have hmono : StrictMono fun i ↦ show Fin w'.length from φ i := fun i j hij ↦
      rel_hom φ ⟨.prec, Set.mem_singleton _⟩ hij
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
      (fun i ↦ he (Fin.cast hlen i) ▸ hget i i.2 (hlen ▸ i.2)) fun o ho i j h ↦ by
        obtain rfl := Set.eq_of_mem_singleton ho
        exact e.lt_iff_lt.2 h⟩

theorem factors_subset_of_sublist {k : ℕ} (h : w <+ w') :
    (wordLanguage P {.prec}).factors k (WordModel ℓ w) ⊆
      (wordLanguage P {.prec}).factors k (WordModel ℓ w') :=
  let ⟨φ⟩ := nonempty_hom_lt_iff.2 ⟨w, h, List.forall₂_same.2 fun _ _ ↦ subset_rfl⟩
  factors_mono φ

theorem exists_sublist_of_occurs {k : ℕ} {f : (wordLanguage P {.prec}).Factor k}
    (hf : f.Occurs (WordModel ℓ w)) :
    ∃ s, s <+ w ∧ s.length ≤ k ∧ f.Occurs (WordModel ℓ s) := by
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
      mem_realizers_of (fun x ↦ ?_) (fun o ho x y h ↦ ?_) hv⟩
    · change List.get _ _ = w.get (u x)
      simp only [List.get_ofFn, Fin.cast_cast, Fin.cast_eq_self]
      rw [key]
    · obtain rfl := Set.eq_of_mem_singleton ho
      exact (I.orderIsoOfFin rfl).symm.lt_iff_lt.2 (Subtype.mk_lt_mk.2 h)

/-- The positive diagram of a word of at most `k` symbols under precedence, as a `k`-factor of
the labels `P`: every atom its positions satisfy. -/
def diagram (ℓ : β → Set P) (s : List β) {k : ℕ} (hs : s.length ≤ k) :
    (wordLanguage P {.prec}).Factor k where
  n := s.length
  n_le := hs
  atoms := Atom.diagram (WordModel ℓ s)
  preconnected x y := by
    rcases lt_trichotomy x y with h | rfl | h
    · exact SimpleGraph.Adj.reachable
        ⟨h.ne, .inl ⟨⟨.ord ⟨.prec, Set.mem_singleton _⟩, ![x, y]⟩, by exact h, ⟨0, rfl⟩, ⟨1, rfl⟩⟩⟩
    · rfl
    · exact SimpleGraph.Adj.reachable
        ⟨h.ne', .inr ⟨⟨.ord ⟨.prec, Set.mem_singleton _⟩, ![y, x]⟩, by exact h, ⟨0, rfl⟩, ⟨1, rfl⟩⟩⟩

/-- A word's diagram occurs in a structure exactly when the word maps homomorphically into
it. -/
theorem diagram_occurs_iff_nonempty_hom {s : List β} {k : ℕ} (hs : s.length ≤ k)
    {N : Type*} [(wordLanguage P {.prec}).Structure N] :
    (diagram ℓ s hs).Occurs N ↔ Nonempty (WordModel ℓ s →[wordLanguage P {.prec}] N) :=
  ⟨fun ⟨v, hv⟩ ↦ ⟨Atom.diagramHomEquiv.symm ⟨v, hv⟩⟩, fun ⟨φ⟩ ↦ ⟨_, (Atom.diagramHomEquiv φ).2⟩⟩

/-- The diagram of a word occurs exactly in the words with a subsequence whose positions carry
its labels, position by position. -/
theorem diagram_occurs_iff_forall₂ {s : List β} {k : ℕ} (hs : s.length ≤ k) :
    (diagram ℓ s hs).Occurs (WordModel ℓ w) ↔
      ∃ t, t <+ w ∧ List.Forall₂ (fun a b ↦ ℓ a ⊆ ℓ b) s t :=
  (diagram_occurs_iff_nonempty_hom hs).trans nonempty_hom_lt_iff

theorem diagram_occurs_iff {s : List β} {k : ℕ} (hs : s.length ≤ k) :
    (diagram ({·}) s hs).Occurs (WordModel ({·}) w) ↔ s <+ w := by
  simp only [diagram_occurs_iff_forall₂, Set.singleton_subset_singleton,
    List.forall₂_eq_eq_eq, exists_eq_right']

/-- The subfactors of a word's diagram are the factors occurring in the word. -/
theorem le_diagram_iff {s : List β} {k : ℕ} (hs : s.length ≤ k)
    {f : (wordLanguage P {.prec}).Factor k} : f ≤ diagram ℓ s hs ↔ f.Occurs (WordModel ℓ s) :=
  Factor.le_iff_occurs

/-- Under precedence one word's diagram is a subfactor of another's exactly when the word is a
subsequence of the other, [chandlee-eyraud-heinz-jardine-rawski-2019]'s Proposition 2. -/
theorem diagram_le_diagram_iff {s : List β} {k : ℕ} (hs : s.length ≤ k) (hw : w.length ≤ k) :
    diagram ({·}) s hs ≤ diagram ({·}) w hw ↔ s <+ w :=
  (le_diagram_iff hw).trans (diagram_occurs_iff hs)

theorem diagram_singleton_occurs_iff {d : β} {k : ℕ} (hk : [d].length ≤ k) :
    (diagram ℓ [d] hk).Occurs (WordModel ℓ w) ↔
      ∃ x ∈ w, ℓ d ⊆ ℓ x := by
  rw [diagram_occurs_iff_forall₂]
  constructor
  · rintro ⟨t, htw, hdt⟩
    cases hdt with
    | cons h hnil =>
      cases hnil
      exact ⟨_, htw.subset (List.mem_singleton_self _), h⟩
  · rintro ⟨x, hx, hdx⟩
    exact ⟨[x], List.singleton_sublist.2 hx, .cons hdx .nil⟩

end Precedence

/-! ### Successor -/

section Successor

variable {c : List β}

private theorem covBy_unit {m : ℕ} {a b : Fin m} (h : a ⋖ b) :
    (a : ℕ) ≤ b + 1 ∧ (b : ℕ) ≤ a + 1 := by
  rw [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h
  omega

theorem le_add_one_of_adj {n : ℕ} {T : Set ((wordLanguage P {.succ}).Atom (Fin n))}
    {r : Fin n → WordModel ℓ u} (hr : r ∈ Atom.realizers (WordModel ℓ u) T)
    {x y : Fin n} (h : (Atom.gaifman T).Adj x y) : ((r x).toFin : ℕ) ≤ (r y).toFin + 1 := by
  obtain ⟨hne, hxy⟩ := h
  have key : ∀ a ∈ T, x ∈ Set.range a.args → y ∈ Set.range a.args →
      ((r x).toFin : ℕ) ≤ (r y).toFin + 1 := by
    rintro ⟨_ | ⟨o, ho⟩, args⟩ ha ⟨i, rfl⟩ ⟨j, rfl⟩
    · exact absurd (congrArg args (Subsingleton.elim i j)) hne
    · obtain rfl := Set.eq_of_mem_singleton ho
      have hR' := covBy_unit (Atom.mem_realizers.1 hr _ ha)
      fin_cases i <;> fin_cases j
      · exact absurd rfl hne
      · exact hR'.1
      · exact hR'.2
      · exact absurd rfl hne
  rcases hxy with ⟨a, ha, hx, hy⟩ | ⟨a, ha, hy, hx⟩ <;> exact key a ha hx hy

/-- Under successor an occurrence of a `k`-factor spans fewer than `k` steps. -/
theorem le_add_of_occurs {k : ℕ} {f : (wordLanguage P {.succ}).Factor k}
    {r : Fin f.n → WordModel ℓ u} (hr : r ∈ Atom.realizers (WordModel ℓ u) f.atoms)
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
    Nonempty (WordModel ℓ c →[wordLanguage P {.succ}] WordModel ℓ u) ↔
      ∃ t, t <:+: u ∧ List.Forall₂ (fun a b ↦ ℓ a ⊆ ℓ b) c t := by
  constructor
  · rintro ⟨φ⟩
    let r : Fin c.length → WordModel ℓ u := φ
    rcases Nat.eq_zero_or_pos c.length with h0 | hpos
    · rw [List.eq_nil_of_length_eq_zero h0]
      exact ⟨[], List.nil_infix, .nil⟩
    have hsucc (i : ℕ) (hi : i + 1 < c.length) :
        ((r ⟨i + 1, hi⟩).toFin : ℕ) = (r ⟨i, by omega⟩).toFin + 1 := by
      have h : (r ⟨i, by omega⟩).toFin ⋖ (r ⟨i + 1, hi⟩).toFin :=
        rel_hom φ ⟨.succ, Set.mem_singleton _⟩ (i := ⟨i, by omega⟩) (j := ⟨i + 1, hi⟩)
          (Fin.covBy_iff.2 (Nat.covBy_iff_add_one_eq.2 rfl))
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
    refine ⟨hom (fun i ↦ ⟨i + m, hlt i⟩) (fun i ↦ ?_) fun o ho i j h ↦ ?_⟩
    · change ℓ (c.get i) ⊆ ℓ (u[(i : ℕ) + m]'(hlt i))
      rw [hu i]
      exact hget i i.2 (i.2.trans_eq hlen)
    · obtain rfl := Set.eq_of_mem_singleton ho
      change i.toFin ⋖ j.toFin at h
      change (⟨(i.toFin : ℕ) + m, hlt i⟩ : Fin u.length) ⋖ ⟨(j.toFin : ℕ) + m, hlt j⟩
      simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h ⊢
      omega

theorem factors_subset_of_infix {k : ℕ} (h : c <:+: u) :
    (wordLanguage P {.succ}).factors k (WordModel ℓ c) ⊆
      (wordLanguage P {.succ}).factors k (WordModel ℓ u) :=
  let ⟨φ⟩ := nonempty_hom_covBy_iff.2 ⟨c, h, List.forall₂_same.2 fun _ _ ↦ subset_rfl⟩
  factors_mono φ

/-- A factor realized under successor within a window of a word occurs in the window. -/
theorem occurs_take_drop {k : ℕ} {f : (wordLanguage P {.succ}).Factor k}
    {r : Fin f.n → WordModel ℓ u} (hr : r ∈ Atom.realizers (WordModel ℓ u) f.atoms)
    {m l : ℕ} (hm : ∀ a, m ≤ ((r a).toFin : ℕ)) (hl : ∀ a, ((r a).toFin : ℕ) < m + l) :
    f.Occurs (WordModel ℓ ((u.drop m).take l)) := by
  have hlt (a) : ((r a).toFin : ℕ) - m < ((u.drop m).take l).length := by
    have := hm a
    have := hl a
    have := (r a).toFin.2
    simp only [List.length_take, List.length_drop]
    omega
  refine ⟨fun a ↦ show WordModel ℓ ((u.drop m).take l) from ⟨(r a).toFin - m, hlt a⟩,
    mem_realizers_of (fun a ↦ ?_) (fun o ho a b hab ↦ ?_) hr⟩
  · change ((u.drop m).take l)[((r a).toFin : ℕ) - m]'(hlt a) =
      u[((r a).toFin : ℕ)]'(r a).toFin.2
    simp only [List.getElem_take, List.getElem_drop]
    congr 1
    have := hm a
    omega
  · obtain rfl := Set.eq_of_mem_singleton ho
    change (r a).toFin ⋖ (r b).toFin at hab
    change (⟨_, hlt a⟩ : Fin _) ⋖ ⟨_, hlt b⟩
    have := hm a
    have := hm b
    simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at hab ⊢
    omega

theorem exists_infix_of_occurs {k : ℕ} {f : (wordLanguage P {.succ}).Factor k}
    (hf : f.Occurs (WordModel ℓ u)) :
    ∃ c, c <:+: u ∧ c.length ≤ k ∧ f.Occurs (WordModel ℓ c) := by
  obtain ⟨r, hr⟩ := hf
  have window (m : ℕ) (hm : ∀ a, m ≤ ((r a).toFin : ℕ)) (hl : ∀ a, ((r a).toFin : ℕ) < m + k) :
      ∃ c, c <:+: u ∧ c.length ≤ k ∧ f.Occurs (WordModel ℓ c) :=
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
    (wordLanguage P {.succ}).factors k (WordModel ℓ (a ++ x ++ b)) ⊆
      (wordLanguage P {.succ}).factors k (WordModel ℓ (a ++ x)) ∪
        (wordLanguage P {.succ}).factors k (WordModel ℓ (x ++ b)) := by
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
def succDiagram (ℓ : β → Set P) (c : List β) {k : ℕ} (hc : c.length ≤ k) :
    (wordLanguage P {.succ}).Factor k where
  n := c.length
  n_le := hc
  atoms := Atom.diagram (WordModel ℓ c)
  preconnected x y := by
    have hpos : 0 < c.length := x.pos
    have reach (i : ℕ) (hi : i < c.length) :
        (Atom.gaifman (L := wordLanguage P {.succ}) (Atom.diagram (WordModel ℓ c))).Reachable
          ⟨0, hpos⟩ ⟨i, hi⟩ := by
      induction i with
      | zero => rfl
      | succ i ih =>
        refine (ih (by omega)).trans <| SimpleGraph.Adj.reachable
          ⟨Fin.ne_of_val_ne i.lt_succ_self.ne,
            .inl ⟨⟨.ord ⟨.succ, Set.mem_singleton _⟩, ![⟨i, by omega⟩, ⟨i + 1, hi⟩]⟩, ?_, ⟨0, rfl⟩,
              ⟨1, rfl⟩⟩⟩
        change (⟨i, _⟩ : Fin c.length) ⋖ ⟨i + 1, hi⟩
        simp [Fin.covBy_iff]
    exact (reach x x.2).symm.trans (reach y y.2)

/-- A word's successor diagram occurs in a structure exactly when the word maps homomorphically
into it. -/
theorem succDiagram_occurs_iff_nonempty_hom {k : ℕ} (hc : c.length ≤ k)
    {N : Type*} [(wordLanguage P {.succ}).Structure N] :
    (succDiagram ℓ c hc).Occurs N ↔ Nonempty (WordModel ℓ c →[wordLanguage P {.succ}] N) :=
  ⟨fun ⟨v, hv⟩ ↦ ⟨Atom.diagramHomEquiv.symm ⟨v, hv⟩⟩, fun ⟨φ⟩ ↦ ⟨_, (Atom.diagramHomEquiv φ).2⟩⟩

/-- The successor diagram of a word occurs exactly in the words with an infix whose positions
carry its labels, position by position. -/
theorem succDiagram_occurs_iff_forall₂ {k : ℕ} (hc : c.length ≤ k) :
    (succDiagram ℓ c hc).Occurs (WordModel ℓ u) ↔
      ∃ t, t <:+: u ∧ List.Forall₂ (fun a b ↦ ℓ a ⊆ ℓ b) c t :=
  (succDiagram_occurs_iff_nonempty_hom hc).trans nonempty_hom_covBy_iff

theorem succDiagram_occurs_iff {k : ℕ} (hc : c.length ≤ k) :
    (succDiagram ({·}) c hc).Occurs (WordModel ({·}) u) ↔ c <:+: u := by
  simp only [succDiagram_occurs_iff_forall₂, Set.singleton_subset_singleton,
    List.forall₂_eq_eq_eq, exists_eq_right']

/-- The subfactors of a word's successor diagram are the factors occurring in the word. -/
theorem le_succDiagram_iff {k : ℕ} (hc : c.length ≤ k)
    {f : (wordLanguage P {.succ}).Factor k} : f ≤ succDiagram ℓ c hc ↔ f.Occurs (WordModel ℓ c) :=
  Factor.le_iff_occurs

/-- Under successor one word's diagram is a subfactor of another's exactly when the word is an
infix of the other, [chandlee-eyraud-heinz-jardine-rawski-2019]'s Proposition 1. -/
theorem succDiagram_le_succDiagram_iff {k : ℕ} (hc : c.length ≤ k)
    (hu : u.length ≤ k) : succDiagram ({·}) c hc ≤ succDiagram ({·}) u hu ↔ c <:+: u :=
  (le_succDiagram_iff hu).trans (succDiagram_occurs_iff hc)

theorem factors_eq_iff_infix {k : ℕ} {u u' : List β} :
    (wordLanguage β {.succ}).factors k (WordModel ({·}) u) =
        (wordLanguage β {.succ}).factors k (WordModel ({·}) u') ↔
      {c | c <:+: u ∧ c.length ≤ k} = {c | c <:+: u' ∧ c.length ≤ k} := by
  have sub (u u' : List β)
      (h : {c | c <:+: u ∧ c.length ≤ k} ⊆ {c | c <:+: u' ∧ c.length ≤ k}) :
      (wordLanguage β {.succ}).factors k (WordModel ({·}) u) ⊆
        (wordLanguage β {.succ}).factors k (WordModel ({·}) u') := fun _ hf ↦
    let ⟨_, hc, hlen, hfc⟩ := exists_infix_of_occurs hf
    factors_subset_of_infix (h ⟨hc, hlen⟩).1 hfc
  refine ⟨fun h ↦ Set.ext fun c ↦ ⟨fun ⟨hc, hlen⟩ ↦ ⟨?_, hlen⟩, fun ⟨hc, hlen⟩ ↦ ⟨?_, hlen⟩⟩,
    fun h ↦ (sub _ _ h.subset).antisymm (sub _ _ h.symm.subset)⟩
  · exact (succDiagram_occurs_iff hlen).1 (h.subset ((succDiagram_occurs_iff hlen).2 hc))
  · exact (succDiagram_occurs_iff hlen).1 (h.symm.subset ((succDiagram_occurs_iff hlen).2 hc))

end Successor

end WordModel

end Subregular
