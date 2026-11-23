module

public import Studies.Heim1982
public import Studies.Karttunen1973
public import Linglib.Data.Examples.Heim1983

/-!
# Heim (1983): On the Projection Problem for Presuppositions

This file formalizes Heim's paper. A context admits a sentence when the sentence's context
change potential is defined on it, a sentence presupposes what every admitting context
entails (12), and the heritage properties that Karttunen and Peters stipulate for *if*
and *not* are read off the potentials (14) and (15): a context admits "If A, B" iff it admits
A and its update by A admits B, and negation is a hole. The King example (1)–(3) is worked as
the paper does (`king_admits_iff`), and the two ways of accommodating a presupposition under
negation are (16)'s global and local readings (`globalNeg_entails`, `localNeg_entails`); a
preference for the global one recaptures Gazdar's cancellation under the threat of
inconsistency (`cancellation_only_under_inconsistency`). Contexts as sets of sequence–world
pairs (§3) carry the potentials for open sentences and for *every* (21): under the novelty
stipulation (22), "Every nation cherishes its king" presupposes that every nation has a king
(`every_nation_presupposes`), a presupposition in the restrictor projects universally (23),
and an indefinite's presupposition projects universally unless it is accommodated in the
course of the update (§3.3).

## Implementation notes

The propositional part (§2) uses the substrate's partial context change potentials over a
type of worlds: `ofTrivalent` for a sentence with a trivalent meaning, `cond` for (14), `neg`
for (15), and `Admits` for definedness, so that the heritage properties are the substrate's
`admits_cond` and `admits_neg`. Presupposing a proposition `p` (12) is the substrate's
`Presupposes` of the update `ofTrivalent fun w ↦ ofProp (p w)` (`presupposes_ofProp_iff`). The
file part (§3) uses the same potentials over the substrate's world–sequence points, with
`atom`, `atomP`, and `every` stated here as (19)–(21) and entailment by a context read as
inclusion. The paper gives no potential for *no* (24), so that sentence is a row only.

A file of the dissertation has a domain of cards beside its satisfaction set; the files of §3
are the satisfaction sets, and on them the paper's clauses are the rules of the dissertation:
the atom is the meet with the atom's file (`atom_sat`), negation by set difference is rule (IV)
where no card is added (`neg_sat`), and (21) is rule (III) (`everyClause_sat`). The novelty
stipulation (22) holds of exactly the satisfaction sets of the files that lack the card
(`File.novelIn_iff_exists_file`).

`TrueWrt` makes the truth definition (13) total. Heim defines the truth of `S` with respect to
`c` only at a world where `c` is true and only when `c` admits `S`, and leaves it undefined
elsewhere; `TrueWrt` is false there instead, so its negation is not falsity in Heim's sense, and
`trueWrt_ofTrivalent` assumes both conditions.

Admittance of a conjunction is compared with the projection rule of Karttunen's 1974 paper, which
filters a presupposition of the second clause entailed by the context incremented with the first
(`admits_seq_iff_conj`). Karttunen's rule also keeps a presupposition the context alone entails;
the filter here drops it, which changes no context's admittance.

## References

* [heim-1983]
* [heim-1982]
* [karttunen-1973]
* [karttunen-1974-presupposition]
* [karttunen-peters-1979]
* [gazdar-1979]
* [lewis-1979]
-/

@[expose] public section

namespace Heim1983

open DynamicSemantics PartialUpdate CCP.Partial Presupposition

/-! ### Admittance and presupposition (§2.1–§2.2) -/

section Propositional

variable {W : Type*}

/-- (13), made total: `S` is true in `w` with respect to `c` when `c` admits `S` and the context
    `c` updated by `S` is true in `w`, and is not true otherwise. -/
def TrueWrt (φ : CCP.Partial W) (c : Set W) (w : W) : Prop := ∃ h : φ.Admits c, w ∈ (φ c).get h

theorem trueWrt_ofTrivalent {p : W → Trivalent} {c : Set W} {w : W} (hw : w ∈ c)
    (h : (ofTrivalent p).Admits c) : TrueWrt (ofTrivalent p) c w ↔ p w = .true :=
  ⟨fun ⟨_, _, hq⟩ => hq, fun hq => ⟨h, hw, hq⟩⟩

variable (king son bald : W → Prop)

open Classical in
/-- *The king has a son* (1) presupposes a king and asserts that he has a son. -/
noncomputable def kingHasSon : W → Trivalent :=
  Trivalent.condEvent king son

open Classical in
/-- *The king's son is bald* (2) presupposes a king with a son. -/
noncomputable def kingsSonBald : W → Trivalent :=
  Trivalent.condEvent (fun w ↦ king w ∧ son w) bald

/-- (3) "If the king has a son, the king's son is bald", by (14). -/
noncomputable def ifKingHasSon : CCP.Partial W :=
  cond (ofTrivalent (kingHasSon king son)) (ofTrivalent (kingsSonBald king son bald))

variable {king son bald}

/-- A context admits (3) iff it entails there is a king, since it must admit (1) and its update by
(1) admits (2) (§2.1). -/
theorem king_admits_iff (c : Set W) :
    (ifKingHasSon king son bald).Admits c ↔ ∀ w ∈ c, king w := by
  simp [ifKingHasSon, admits_cond_ofTrivalent_iff, admits_ofTrivalent, Set.subset_def,
    kingHasSon, kingsSonBald, Connective.localContext]

open Classical in
-- (3), (1)
theorem king_presupposes :
    Presupposes (ifKingHasSon king son bald) (ofTrivalent fun w ↦ Trivalent.ofProp (king w)) :=
  (presupposes_ofProp_iff _ _).mpr fun c h ↦ (king_admits_iff c).mp h

open Classical in
-- (3)
theorem not_presupposes_son (h : ∃ w, king w ∧ ¬ son w) :
    ¬ Presupposes (ifKingHasSon king son bald) (ofTrivalent fun w ↦ Trivalent.ofProp (son w)) := by
  rw [presupposes_ofProp_iff]
  obtain ⟨w, hk, hs⟩ := h
  intro hp
  exact hs (hp {w} ((king_admits_iff _).mpr fun _ hv => hv ▸ hk) w rfl)

/-! ### Accommodation (§2.3) -/

variable (φ : CCP.Partial W) (p : Set W)

/-- The global option (A) evaluates *Not S* in a context that does not admit `S` by amending
    the context to `c ∩ p` and computing `(c ∩ p) + Not S`. -/
def globalNeg : CCP.Partial W := fun c => neg φ (c ∩ p)

/-- The local option (B) amends the context to `c ∩ p` only to compute `(c ∩ p) + S`, and
    subtracts that from `c` itself. -/
def localNeg : CCP.Partial W := fun c => (φ (c ∩ p)).map (c \ ·)

variable {φ p}

theorem globalNeg_admits {c : Set W} (h : φ.Admits (c ∩ p)) : (globalNeg φ p).Admits c := h

theorem localNeg_admits {c : Set W} (h : φ.Admits (c ∩ p)) : (localNeg φ p).Admits c := h

/-- The global option's result entails the accommodated presupposition, so (16) read in
    isolation has France with a king. -/
theorem globalNeg_entails {c c' : Set W} (h : c' ∈ globalNeg φ p c) : c' ⊆ p :=
  fun _ hw ↦ let ⟨_, hp⟩ := isEliminative_neg φ _ _ h hw; hp

open Classical in
/-- Under the local option, (16) entails only that France has no king or he did not come. -/
theorem localNeg_entails {came : W → Prop} [DecidablePred came] {c c' : Set W}
    (h : c' ∈ localNeg (ofTrivalent (Trivalent.condEvent (· ∈ p) came)) p c) :
    c' = {w ∈ c | w ∉ p ∨ ¬ came w} := by
  obtain ⟨t, ht, rfl⟩ := (Part.mem_map_iff _).mp h
  obtain ⟨-, rfl⟩ := (mem_ofTrivalent _ _ _).mp ht
  ext w
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_inter_iff, Trivalent.condEvent_eq_true_iff]
  tauto

theorem globalNeg_disjoint {c c' : Set W} (h : c' ∈ globalNeg φ p c) : c' ∩ pᶜ = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨hw, hn⟩ => hn (globalNeg_entails h hw)

open scoped Classical in
/-- The paper's ceteris paribus preference for global over local accommodation takes the
    global result `g` continued by `k`, unless `k` is inconsistent with it, and otherwise the
    local result `l` continued by `k`. -/
noncomputable def preferGlobal (k g l : Set W) : Set W :=
  if (g ∩ k).Nonempty then g ∩ k else l ∩ k

-- (16)
theorem preferGlobal_univ_subset {c g : Set W} (l : Set W) (hg : g ∈ globalNeg φ p c)
    (hne : g.Nonempty) : preferGlobal Set.univ g l ⊆ p := by
  rw [preferGlobal, Set.inter_univ, ite_eq_left hne]
  exact globalNeg_entails hg

-- (16)
theorem preferGlobal_compl {c g : Set W} (l : Set W) (hg : g ∈ globalNeg φ p c) :
    preferGlobal pᶜ g l = l ∩ pᶜ := by
  rw [preferGlobal, globalNeg_disjoint hg, ite_eq_right Set.not_nonempty_empty]

/-- The preference recaptures [gazdar-1979]'s assumption that presupposition cancellation
    occurs only under the threat of inconsistency. A preferred reading that does not entail
    the presupposition comes from a global result inconsistent with the continuation. -/
theorem cancellation_only_under_inconsistency {c g l k : Set W} (hg : g ∈ globalNeg φ p c)
    (h : ¬ preferGlobal k g l ⊆ p) : g ∩ k = ∅ := by
  rw [preferGlobal] at h
  split_ifs at h with hk
  · exact absurd (Set.inter_subset_left.trans (globalNeg_entails hg)) h
  · exact Set.not_nonempty_iff_eq_empty.mp hk

end Propositional

/-! ### Files: contexts as sets of sequence–world pairs (§3) -/

section Files

variable {M W : Type*}

/-- A file is a set of pairs of a sequence of individuals and a world (§3.1). -/
abbrev File (M W : Type*) := Set (Possibility W ℕ M)

/-- The proposition a file determines (17). -/
def File.prop (c : File M W) : Set W := Possibility.world '' c

/-- A file is true in a world when some sequence fits it there (18). -/
def File.TrueIn (c : File M W) (w : W) : Prop := ∃ p ∈ c, p.world = w

/-- The update by an open sentence `P xᵢ` without presupposition (19). -/
def atom (P : M → W → Prop) (i : ℕ) : CCP.Partial (Possibility W ℕ M) :=
  PFun.lift fun c ↦ {p ∈ c | P (p.assignment i) p.world}

/-- An open sentence `P xᵢ` presupposing `pre xᵢ` is admitted by a file iff every pair in it
    satisfies the presupposition at the `i`-th member (20). -/
def atomP (pre P : M → W → Prop) (i : ℕ) : CCP.Partial (Possibility W ℕ M) :=
  fun c ↦ ⟨∀ p ∈ c, pre (p.assignment i) p.world, fun _ ↦ {p ∈ c | P (p.assignment i) p.world}⟩

/-- The clause of (21) keeps the pairs of `c` each of whose `i`-variants in `cA` survives in
    `cAB`. -/
def File.everyClause (i : ℕ) (c cA cAB : File M W) : File M W :=
  {p ∈ c | ∀ a, p.update i a ∈ cA → p.update i a ∈ cAB}

/-- `c + Every xᵢ, A, B` (21) keeps the pairs of `c` each of whose `i`-variants in `c + A`
    survives in `c + A + B`, and is defined iff `c + A` and `c + A + B` are. -/
def every (i : ℕ) (A B : CCP.Partial (Possibility W ℕ M)) : CCP.Partial (Possibility W ℕ M) :=
  fun c ↦ (A c).bind fun cA ↦ (B cA).map fun cAB ↦ File.everyClause i c cA cAB

/-- The file does not yet distinguish the `i`-th member of a sequence (22), the lexical
    novelty requirement of *every* and of an indefinite indexed `i`. -/
def File.NovelIn (c : File M W) (i : ℕ) : Prop := ∀ p a, p ∈ c ↔ p.update i a ∈ c

variable {i : ℕ} {c : File M W}

theorem atom_admits (P : M → W → Prop) (i : ℕ) (c : File M W) : (atom P i).Admits c := trivial

theorem atomP_admits_iff (pre P : M → W → Prop) (i : ℕ) (c : File M W) :
    (atomP pre P i).Admits c ↔ ∀ p ∈ c, pre (p.assignment i) p.world := Iff.rfl

theorem every_admits_iff (i : ℕ) (A B : CCP.Partial (Possibility W ℕ M)) (c : File M W) :
    (every i A B).Admits c ↔ ∃ h : A.Admits c, B.Admits ((A c).get h) :=
  Iff.rfl

-- (ii), §3.2
theorem every_atom_admits_iff (i : ℕ) (A pre B : M → W → Prop) (c : File M W) :
    (every i (atom A i) (atomP pre B i)).Admits c ↔
      ∀ p ∈ c, A (p.assignment i) p.world → pre (p.assignment i) p.world :=
  ⟨fun ⟨_, h⟩ p hp hA ↦ h p ⟨hp, hA⟩, fun h ↦ ⟨trivial, fun p ⟨hp, hA⟩ ↦ h p hp hA⟩⟩

/-- For a novel index, (7) presupposes under (22) that every nation has a king. -/
theorem every_nation_presupposes (i : ℕ) (nation hasKing cherishes : M → W → Prop)
    (hc : c.NovelIn i) :
    (every i (atom nation i) (atomP hasKing cherishes i)).Admits c ↔
      ∀ w ∈ c.prop, ∀ a, nation a w → hasKing a w := by
  rw [every_atom_admits_iff]
  constructor
  · rintro h _ ⟨p, hp, rfl⟩ a hn
    have := h (p.update i a) ((hc p a).mp hp)
    simp only [Possibility.update_assignment, Function.update_self, Possibility.update_world]
      at this
    exact this hn
  · exact fun h p hp hn ↦ h p.world ⟨p, hp, rfl⟩ _ hn

-- (23) [karttunen-peters-1979]
theorem every_restrictor_presupposes (i : ℕ) (hasKing serves rewarded : M → W → Prop)
    (hc : c.NovelIn i) :
    (every i (atomP hasKing serves i) (atom rewarded i)).Admits c ↔
      ∀ w ∈ c.prop, ∀ a, hasKing a w := by
  constructor
  · rintro ⟨h, -⟩ _ ⟨p, hp, rfl⟩ a
    simpa using h (p.update i a) ((hc p a).mp hp)
  · exact fun h ↦ ⟨fun p hp ↦ h p.world ⟨p, hp, rfl⟩ _, trivial⟩

/-! ### Files of the dissertation

A file of [heim-1982] has a domain of cards beside its satisfaction set, which does not
distinguish sequences that agree on the cards. The files of this paper are the satisfaction
sets, and on them the clauses (19), (15) and (21) are rules (I), (IV) and (III) of the
dissertation, with (22) in place of the absence of a card. -/

variable {F G H : DynamicSemantics.File W ℕ M}

-- (22) holds of the satisfaction sets of the files that lack the card `i`, and of no other set.
theorem File.novelIn_iff_exists_file :
    c.NovelIn i ↔ ∃ F : DynamicSemantics.File W ℕ M, F.sat = c ∧ i ∉ F.dom := by
  constructor
  · intro h
    refine ⟨⟨{i}ᶜ, c, fun p q hpq hp ↦ ?_⟩, rfl, fun hi ↦ hi rfl⟩
    have hq : q = p.update i (q.assignment i) :=
      Possibility.ext hpq.world_eq.symm <| funext fun j ↦ by
        by_cases hj : j = i
        · subst hj; simp
        · rw [Possibility.update_assignment, Function.update_of_ne hj]; exact (hpq.eqOn hj).symm
    exact hq ▸ (h p _).mp hp
  · rintro ⟨F, rfl, hi⟩ p a
    exact File.mem_sat_congr (Possibility.agreeOn_update hi a)

-- (19) is rule (I): the update by an open sentence takes the meet with its file.
theorem atom_sat (P : M → W → Prop) (i : ℕ) (F : DynamicSemantics.File W ℕ M) :
    atom P i F.sat = Part.some (F ⊓ File.atomAt i fun w m ↦ P m w).sat :=
  rfl

-- (15) is rule (IV) where the update adds no card.
theorem neg_sat {φ : CCP.Partial (Possibility W ℕ M)} (hφ : φ F.sat = Part.some G.sat)
    (hG : G.dom ⊆ F.dom) : neg φ F.sat = Part.some (F \ G).sat := by
  rw [neg, hφ, Part.map_some, File.sat_sdiff_of_dom_subset hG]

-- (21) is rule (III) where the restrictor adds the card `i` alone and the nuclear scope none.
theorem everyClause_sat (hi : i ∉ F.dom) (hG : G.dom = insert i F.dom) (hH : H.dom ⊆ G.dom) :
    File.everyClause i F.sat G.sat H.sat = (Heim1982.universal F G H).sat := by
  ext p
  refine and_congr_right fun _ ↦ ⟨fun h q hq hqp ↦ ?_, fun h a ha ↦ ?_⟩
  · have hpq : (p.update i (q.assignment i)).AgreeOn G.dom q := by
      refine ⟨hqp.world_eq.symm, fun j hj ↦ ?_⟩
      rcases hG ▸ hj with rfl | hj
      · simp
      · rw [Possibility.update_assignment, Function.update_of_ne fun h : j = i ↦ hi (h ▸ hj)]
        exact (hqp.eqOn hj).symm
    exact ⟨_, h _ (G.mem_sat_of_agreeOn hpq.symm hq), hpq⟩
  · obtain ⟨r, hr, hrq⟩ := h _ ha (Possibility.agreeOn_update hi a).symm
    exact H.mem_sat_of_agreeOn (hrq.mono hH) hr

/-! ### Indefinites (§3.3) -/

/-- *A fat man was pushing his bicycle* (26)–(27) is the sequence of two open sentences, the
    second presupposing that `xᵢ` has a bicycle. -/
def fatManBicycle (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop) :
    CCP.Partial (Possibility W ℕ M) :=
  seq (atom fatMan i) (atomP hasBicycle pushing i)

-- (25), (22)
theorem fatManBicycle_admits_iff (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop)
    (hc : c.NovelIn i) :
    (fatManBicycle i fatMan hasBicycle pushing).Admits c ↔
      ∀ w ∈ c.prop, ∀ a, fatMan a w → hasBicycle a w := by
  constructor
  · rintro ⟨_, h⟩ _ ⟨p, hp, rfl⟩ a hf
    simpa using h (p.update i a) ⟨(hc p a).mp hp, by simpa using hf⟩
  · exact fun h ↦ ⟨trivial, fun p ⟨hp, hf⟩ ↦ h p.world ⟨p, hp, rfl⟩ _ hf⟩

/-- Accommodation in the course of the update amends `c + "xᵢ is a fat man"` with
    *xᵢ has a bicycle* before the second sentence is evaluated. -/
def fatManBicycleAcc (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop) :
    CCP.Partial (Possibility W ℕ M) :=
  fun c ↦ atomP hasBicycle pushing i
    {p ∈ c | fatMan (p.assignment i) p.world ∧ hasBicycle (p.assignment i) p.world}

theorem fatManBicycleAcc_admits (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop)
    (c : File M W) : (fatManBicycleAcc i fatMan hasBicycle pushing).Admits c :=
  fun _ ⟨_, _, hb⟩ ↦ hb

theorem fatManBicycleAcc_entails (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop)
    {c c' : File M W} (h : c' ∈ fatManBicycleAcc i fatMan hasBicycle pushing c) :
    ∀ p ∈ c', fatMan (p.assignment i) p.world ∧ hasBicycle (p.assignment i) p.world ∧
      pushing (p.assignment i) p.world := by
  rw [fatManBicycleAcc, atomP, Part.mem_mk_iff] at h
  obtain ⟨-, rfl⟩ := h
  exact fun p ⟨⟨_, hf, hb⟩, hpush⟩ ↦ ⟨hf, hb, hpush⟩

theorem fatManBicycleAcc_not_universal :
    ∃ (c' : File Bool Unit), c' ∈ fatManBicycleAcc 0 (fun _ _ ↦ True) (fun a _ ↦ a = true)
        (fun _ _ ↦ True) Set.univ ∧ c'.TrueIn () ∧
      ¬ ∀ w ∈ c'.prop, ∀ a : Bool, a = true := by
  have hp : (⟨(), fun _ ↦ true⟩ : Possibility Unit ℕ Bool) ∈
      (fatManBicycleAcc 0 (fun _ _ ↦ True) (fun a _ ↦ a = true) (fun _ _ ↦ True) Set.univ).get
        (fatManBicycleAcc_admits _ _ _ _ _) := ⟨⟨Set.mem_univ _, trivial, rfl⟩, trivial⟩
  exact ⟨_, Part.get_mem (fatManBicycleAcc_admits _ _ _ _ _), ⟨_, hp, rfl⟩,
    fun h ↦ Bool.false_ne_true (h () ⟨_, hp, rfl⟩ false)⟩

end Files

/-! ### Admittance and Karttunen's context-relative filter

[karttunen-1974-presupposition] shows that a context satisfies the presuppositions of a
compound sentence iff it entails the presuppositions that a context-relative projection rule
assigns the sentence. Here the rule is the conjunction filter of `Karttunen1973.conj` with
entailment from the context incremented with the first conjunct. -/

-- [karttunen-1974-presupposition], (4a), (7) and the proof that (8) iff (9), pp. 183–186
theorem admits_seq_iff_conj {W : Type*} (c : Set W) (p q : W → Trivalent) :
    (seq (ofTrivalent p) (ofTrivalent q)).Admits c ↔
      ∀ C ∈ (Karttunen1973.conj (fun P C ↦ c ∩ P ⊆ C) (.ofTrivalent p)
        (.ofTrivalent q)).logSet, c ⊆ C := by
  rw [admits_seq_ofTrivalent_iff, admits_ofTrivalent]
  simp only [Karttunen1973.mem_logSet_conj, Karttunen1973.Presupposing.ofTrivalent,
    Writer.logSet_ofSet, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, hq⟩ C (rfl | ⟨rfl, hf⟩)
    · exact hp
    · exact absurd (fun w ⟨hw, ha, _⟩ ↦ hq ⟨hw, ha⟩) hf
  · intro h
    have hp : c ⊆ (Trivalent.gapExt p)ᶜ := h _ (.inl rfl)
    refine ⟨hp, fun w ⟨hw, ha⟩ ↦ ?_⟩
    by_cases hf : c ∩ (Karttunen1973.Presupposing.ofTrivalent p).truth ⊆ (Trivalent.gapExt q)ᶜ
    · exact hf ⟨hw, ha, fun t ht ↦ Set.mem_singleton_iff.mp ht ▸ hp hw⟩
    · exact h _ (.inr ⟨rfl, hf⟩) hw

end Heim1983
