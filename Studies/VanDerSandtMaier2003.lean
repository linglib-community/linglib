module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.VanDerSandtMaier2003
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Order.Disjoint

/-!
# van der Sandt and Maier (2003): Denials in Discourse

This file formalizes [van-der-sandt-maier-2003]'s account of denial as a non-monotonic
correction operation on the discourse record, independent of the semantic operator of
negation, against [horn-1985]'s metalinguistic negation. A denial leaves a negated star
condition in the discourse representation, and reverse anaphora moves the material objected
to under that negation, (2); removing the whole contribution of the previous utterance fails on
[strawson-1952]'s pushed man, (3), on multiple presuppositions, (4), and on an acknowledged
part of the utterance, (5). Layered DRT distributes the information an utterance conveys over
layers, each condition labelled with the Frege, presupposition or implicature layer of the
sentence it comes from, `Label`, `Condition`, `LDRS`, and the content of a set of layers ignores
every other, `content`, (13). Directed reverse anaphora then targets the offensive layers alone,
a smallest set of layers whose content is inconsistent with the Frege content of the correction,
`IsOff`, (18), and moves their conditions under the negation of the denial, `directedRA`, (19):
the resulting record keeps the conditions of every other layer and entails the negation of the
offensive content, `content_directedRA`, so the offensive content is retracted,
`disjoint_content_directedRA`, while assertion, the merge of representations, only strengthens
the record, `content_append_subset`. The worked examples are the implicature denials of the
possibly right Pope, (20), `popeOff`, `pope_content_directedRA`, and of the lady who is a wife,
(21), `ladyOff`, `lady_nice_survives`.

## Implementation notes

The paper interprets layered representations by partial embeddings and closes open layers
into singular propositions through the utterance context, (15) and (16); here a condition
carries the proposition it expresses once anchored, so an LDRS is a list of labelled
propositions and the L-content is the intersection of the conditions bearing a label in L.
Offensiveness is minimal disjointness, which need not be unique. The finer targeting of
footnote 10, moving only the smallest inconsistent sub-DRS, is not formalized: at the
granularity of layers the denial of one of two presuppositions of the same sentence, (4),
retracts both, `kingQuit_quit_lost`, the limitation the paper records there. The examples are
the rows of `Data.Examples.VanDerSandtMaier2003`.

## References

* [van-der-sandt-maier-2003]
* [van-der-sandt-1991]
* [van-der-sandt-1992]
* [geurts-1998]
* [horn-1985]
* [horn-1989]
* [levinson-2000]
* [strawson-1952]
* [kamp-reyle-1993]
-/

@[expose] public section

namespace VanDerSandtMaier2003

/-! ### Layered DRT -/

/-- The layer of a semantic contribution carrying a condition: a backgrounded
precondition, the proffered content, or an enrichment beyond the truth conditions —
the paper's `pr`, `fr` and `imp` layers. -/
inductive ContentLayer where
  | presupposition
  | atIssue
  | implicature
  deriving DecidableEq, Repr

/-- A layer label, (6), names the background or a content layer of the `i`-th sentence. -/
inductive Label where
  | background
  | of (layer : ContentLayer) (i : ℕ)
  deriving DecidableEq, Repr

/-- The Frege layer of sentence `i`. -/
abbrev fr (i : ℕ) : Label := .of .atIssue i

/-- The presupposition layer of sentence `i`. -/
abbrev pr (i : ℕ) : Label := .of .presupposition i

/-- The implicature layer of sentence `i`. -/
abbrev imp (i : ℕ) : Label := .of .implicature i

variable {W : Type*}

/-- A labelled condition, (8), pairs its labels with the proposition it expresses once its
reference
markers are anchored in the context. -/
structure Condition (W : Type*) where
  labels : Finset Label
  content : Set W

/-- A layered DRS lists its labelled conditions. -/
abbrev LDRS (W : Type*) := List (Condition W)

/-- By (11b) and (13), the `L`-content of a representation, the conditions bearing a label in
`L`,
every other condition being ignored. -/
def content (ϕ : LDRS W) (L : Finset Label) : Set W :=
  ⋂ c ∈ ϕ.filter (λ c => (c.labels ∩ L).Nonempty), c.content

theorem mem_content_iff {ϕ : LDRS W} {L : Finset Label} {w : W} :
    w ∈ content ϕ L ↔ ∀ c ∈ ϕ, (c.labels ∩ L).Nonempty → w ∈ c.content := by
  simp only [content, Set.mem_iInter, List.mem_filter, decide_eq_true_eq, and_imp]

theorem content_append (ϕ ψ : LDRS W) (L : Finset Label) :
    content (ϕ ++ ψ) L = content ϕ L ∩ content ψ L := by
  ext w
  simp only [mem_content_iff, List.mem_append, Set.mem_inter_iff]
  exact ⟨λ h => ⟨λ c hc => h c (Or.inl hc), λ c hc => h c (Or.inr hc)⟩,
    λ h c hc => hc.elim (h.1 c) (h.2 c)⟩

theorem content_append_subset (ϕ ψ : LDRS W) (L : Finset Label) :
    content (ϕ ++ ψ) L ⊆ content ϕ L := by
  rw [content_append]
  exact Set.inter_subset_left

/-! ### Directed reverse anaphora -/

/-- In (18), `L` is offensive against the correction layers `K`, a smallest set of layers
whose
content is inconsistent with the content of `K`. -/
def IsOff (ϕ : LDRS W) (K L : Finset Label) : Prop :=
  Disjoint (content ϕ L) (content ϕ K) ∧ ∀ L' ⊂ L, ¬ Disjoint (content ϕ L') (content ϕ K)

/-- The conditions bearing no offensive label. -/
def surviving (ϕ : LDRS W) (off : Finset Label) : LDRS W :=
  ϕ.filter (λ c => c.labels ∩ off = ∅)

/-- Directed reverse anaphora for the denial `σ i`, (19), moves the conditions bearing an
offensive
label move under a negation in the denial's Frege layer, the others stay. -/
def directedRA (ϕ : LDRS W) (off : Finset Label) (i : ℕ) : LDRS W :=
  surviving ϕ off ++ [⟨{fr i}, (content ϕ off)ᶜ⟩]

theorem content_directedRA (ϕ : LDRS W) (off : Finset Label) {i : ℕ} {L : Finset Label}
    (hi : fr i ∈ L) :
    content (directedRA ϕ off i) L = content (surviving ϕ off) L ∩ (content ϕ off)ᶜ := by
  rw [directedRA, content_append]
  congr 1
  ext w
  simp only [mem_content_iff, List.mem_singleton, forall_eq, Set.mem_compl_iff]
  exact ⟨λ h => h ⟨fr i, Finset.mem_inter.2 ⟨Finset.mem_singleton_self _, hi⟩⟩, λ h _ => h⟩

theorem disjoint_content_directedRA (ϕ : LDRS W) (off : Finset Label) {i : ℕ} {L : Finset Label}
    (hi : fr i ∈ L) : Disjoint (content (directedRA ϕ off i) L) (content ϕ off) := by
  rw [content_directedRA ϕ off hi]
  exact Set.disjoint_left.2 λ w hw => hw.2

theorem content_directedRA_subset {ϕ : LDRS W} {off : Finset Label} {i : ℕ} {L : Finset Label}
    (hi : fr i ∈ L) {c : Condition W} (hc : c ∈ ϕ) (hoff : c.labels ∩ off = ∅)
    (hL : (c.labels ∩ L).Nonempty) : content (directedRA ϕ off i) L ⊆ c.content := by
  rw [content_directedRA ϕ off hi]
  intro w hw
  exact mem_content_iff.1 hw.1 c (List.mem_filter.2 ⟨hc, by simp [hoff]⟩) hL

/-! ### The possibly right Pope, (20) -/

/-- The worlds of (20) make the Pope possibly but not necessarily right, or necessarily
right. -/
inductive PopeW where
  | possNotNec
  | nec
  deriving DecidableEq, Repr, Fintype

/-- `ψ` of (20) before reverse anaphora holds the background Pope, σ₁'s Frege content that he
is
possibly right and implicature that he is not necessarily right, and σ₃'s correction that he is
necessarily right. -/
def popeRecord : LDRS PopeW :=
  [⟨{.background}, Set.univ⟩, ⟨{fr 1}, Set.univ⟩, ⟨{imp 1}, {.possNotNec}⟩, ⟨{fr 3}, {.nec}⟩]

private theorem content_popeRecord_imp : content popeRecord {imp 1} = {.possNotNec} := by
  ext w
  simp [mem_content_iff, popeRecord]

private theorem content_popeRecord_fr3 : content popeRecord {fr 3} = {.nec} := by
  ext w
  simp [mem_content_iff, popeRecord]

theorem popeOff : IsOff popeRecord {fr 3} {imp 1} := by
  refine ⟨?_, λ L' hL' => ?_⟩
  · rw [content_popeRecord_imp, content_popeRecord_fr3]
    exact Set.disjoint_singleton.2 (by decide)
  · rw [Finset.ssubset_singleton_iff.1 hL', content_popeRecord_fr3]
    intro h
    have : content popeRecord ∅ = Set.univ := by
      ext w
      simp [mem_content_iff]
    rw [this] at h
    exact Set.singleton_ne_empty _ (Set.univ_disjoint.1 h)

theorem pope_content_directedRA :
    content (directedRA popeRecord {imp 1} 2) {.background, fr 1, fr 2, fr 3} = {.nec} := by
  ext w
  have h2 : fr 2 ∈ ({.background, fr 1, fr 2, fr 3} : Finset Label) := by decide
  simp [content_directedRA _ _ h2, mem_content_iff, surviving, popeRecord]
  cases w <;> simp

/-! ### The lady who is a wife, (21) -/

/-- In the worlds of (21), the woman pointed at is a nice stranger, a nice wife, or a wife
who is
not nice. -/
inductive LadyW where
  | niceStranger
  | niceWife
  | plainWife
  deriving DecidableEq, Repr, Fintype

/-- `ψ` of (21) holds the background pointing, σ₁'s Frege content that she is a lady and
nice, the
latter acknowledged by σ₂, its implicature that she is a stranger, and σ₄'s correction that she
is my wife. -/
def ladyRecord : LDRS LadyW :=
  [⟨{.background}, Set.univ⟩, ⟨{fr 1}, Set.univ⟩, ⟨{fr 1, fr 2}, {.niceStranger, .niceWife}⟩,
    ⟨{imp 1}, {.niceStranger}⟩, ⟨{fr 4}, {.niceWife, .plainWife}⟩]

private theorem content_ladyRecord_imp : content ladyRecord {imp 1} = {.niceStranger} := by
  ext w
  simp [mem_content_iff, ladyRecord]

private theorem content_ladyRecord_fr4 : content ladyRecord {fr 4} = {.niceWife, .plainWife} := by
  ext w
  simp [mem_content_iff, ladyRecord]

theorem ladyOff : IsOff ladyRecord {fr 4} {imp 1} := by
  refine ⟨?_, λ L' hL' => ?_⟩
  · rw [content_ladyRecord_imp, content_ladyRecord_fr4]
    exact Set.disjoint_singleton_left.2 (by decide)
  · rw [Finset.ssubset_singleton_iff.1 hL', content_ladyRecord_fr4]
    intro h
    have : content ladyRecord ∅ = Set.univ := by
      ext w
      simp [mem_content_iff]
    rw [this] at h
    exact (Set.insert_nonempty _ _).ne_empty (Set.univ_disjoint.1 h)

theorem lady_nice_survives :
    content (directedRA ladyRecord {imp 1} 3) {.background, fr 1, fr 2, fr 3, fr 4} ⊆
      {.niceStranger, .niceWife} := by
  refine content_directedRA_subset (c := ⟨{fr 1, fr 2}, {LadyW.niceStranger, .niceWife}⟩)
    ?_ ?_ ?_ ?_
  · decide
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · decide
  · decide

/-! ### Two presuppositions, (4) -/

/-- The worlds of (4) record whether France has a king and whether I quit smoking. -/
abbrev KingQuitW := Bool × Bool

/-- `ψ` of (4) holds σ₁'s two presuppositions, that France has a king and that I quit
smoking, its
Frege content that the king knows it, and σ₂'s correction that France has no king. -/
def kingQuitRecord : LDRS KingQuitW :=
  [⟨{pr 1}, {w | w.1 = true}⟩, ⟨{pr 1}, {w | w.2 = true}⟩, ⟨{fr 1}, {w | w.1 = true ∧ w.2 = true}⟩,
    ⟨{fr 2}, {w | w.1 = false}⟩]

/-- At the granularity of layers, denying the king moves the presupposition that I quit
smoking under the negation as well: only the Frege conditions survive, the limitation of
footnote 10. -/
theorem kingQuit_quit_lost :
    surviving kingQuitRecord {pr 1} =
      [⟨{fr 1}, {w | w.1 = true ∧ w.2 = true}⟩, ⟨{fr 2}, {w | w.1 = false}⟩] := by
  simp [surviving, kingQuitRecord]

end VanDerSandtMaier2003
