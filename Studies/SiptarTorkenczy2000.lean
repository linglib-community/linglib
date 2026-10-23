module

public import Linglib.Phonology.Autosegmental.Melody
public import Linglib.Fragments.Hungarian.Phonology
public import Linglib.Data.Wordlist.SiptarTorkenczy2000

/-!
# Siptár and Törkenczy (2000): The Phonology of Hungarian

This file formalizes the analysis of vowel harmony in chapter 6 of [siptar-torkenczy-2000] and
runs it on the derivations the chapter gives. A stem is a sequence of vocalic nodes with the
unary place features COR, LAB and DOR of [clements-hume-1995] either prelinked to nodes or
floating on the morpheme, and a suffix vowel is a node carrying a linked LAB or placeless, with
its aperture. Four rules apply in order: Link DOR and Link Place associate a floating feature,
unboundedly, to every node it may reach; Spread DOR and Spread Place extend an anchored feature
to the adjacent node, iterating left to right; and a node still placeless is coronal by
default. Throughout, DOR may join any node without COR, COR only a placeless node, and LAB any
node without DOR that is not low (`MayLink`, `linkDor`, `linkPlace`, `spreadDor`,
`spreadPlace`, `derive`). The rules only add association lines and never put COR and DOR on
one node (`links_subset_derive`, `derive_sound`). The eleven stem representations of
the chapter's Table 18 with the four suffixes of its (2) yield the forty-four suffixed forms of
its (13) to (23) (`derivations`), transparency, antiharmony and opacity following from the
prelinking alone, and the vacillating stem of section 3.2.3.1 has two representations deriving
its two forms (`dzsungel_vacillates`). The surface generalization of section 3.2, that the
last harmonic vowel governs suffix backness through the transparent neutral vowels, is the
Fragment's `palatalHarmony`; it agrees with the derivations on the regular stems and
is silent or wrong exactly on the neutral, antiharmonic and opaque stems the analysis handles
by prelinking (`sourceValue_agrees`, `sourceValue_viz`, `sourceValue_hid`,
`sourceValue_kodex`).

## Implementation notes

* Words are the substrate's `Form` with vocalic nodes for the backbone, place features for the tier
  and the stem and suffix as sponsors, and the rules act on its `Candidate`s; a rule inserts
  association lines, and the derivation composes the rules in the chapter's order. Default COR is
  read at the surface, a placeless node counting as coronal. Where the chapter has COR and LAB
  spread together onto one node, COR spreads first and LAB joins it.
* A word is a stem and one suffix; the chapter's stems have at most two vowels and its
  suffixes one, and a prelinked feature is one tier element per node it is linked to.
  Apertures are read from the vowel letters and matter only through the constraint against a
  low labial node; long vowels are not distinguished.
* The forms are rows of `Data/Wordlist/SiptarTorkenczy2000.json`; a derivation is compared with
  the suffixed form's segments after the stem's, since three of the chapter's forms shorten
  the stem vowel.

## References

* [siptar-torkenczy-2000]
* [clements-hume-1995]
* [rose-walker-2011]
-/

@[expose] public section

namespace SiptarTorkenczy2000

open Autosegmental Hungarian Phonology.Harmony

/-- The unary place features of the vowels, (1) of the chapter. -/
inductive Place
  | cor | lab | dor
  deriving DecidableEq, Fintype

/-- A vocalic node with its aperture features. -/
structure VNode where
  open1 : Bool
  open2 : Bool
  deriving DecidableEq

/-- The aperture of the vowel a letter writes. The high vowels are closed on both features, the
mid vowels and *é* open on the second, and the low vowels and *e* open on both. -/
def VNode.ofLetter (l : String) : VNode :=
  if l ∈ ["i", "í", "ü", "ű", "u", "ú"] then ⟨false, false⟩
  else if l ∈ ["ö", "ő", "o", "ó", "é"] then ⟨false, true⟩
  else ⟨true, true⟩

/-- The sponsors of a word's material. -/
inductive Morph
  | stem | suffix
  deriving DecidableEq

/-- A phonological word is an autosegmental form over vocalic nodes and place features. -/
abbrev Word := Form VNode Place Morph

/-! ### The rules -/

variable {w : Word} (c : Candidate w)

/-- The place features linked to the `i`-th node. -/
def places (i : Fin w.lower.length) : List Place := c.tierValues i

/-- Whether the `i`-th node is low. -/
def isLow (i : Fin w.lower.length) : Bool := w.lower[i].value.open1

/-- The value of the `k`-th tier element. -/
def valueAt (k : Fin w.upper.length) : Place := w.upper[k].value

/-- Where a place feature may associate, principles (7c) and (7d) under constraints (6a) and
(6b): DOR to any node without COR, COR to a placeless node, LAB to a node without DOR that is
not low. -/
def MayLink (p : Place) (i : Fin w.lower.length) : Prop :=
  (p = .dor → .cor ∉ places c i) ∧ (p = .cor → places c i = []) ∧
    (p = .lab → .dor ∉ places c i ∧ isLow i = false)

instance (p : Place) (i : Fin w.lower.length) : Decidable (MayLink c p i) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Associate tier element `k`, bearing `p`, to every node it may link to. -/
def linkAll (k : Fin w.upper.length) (p : Place) : Candidate w :=
  (List.finRange w.lower.length).foldl (fun g i ↦ if MayLink g p i then g.insertLink k i else g) c

/-- The floating tier elements bearing `p`. -/
def floating (p : Place) : List (Fin w.upper.length) :=
  (List.finRange w.upper.length).filter fun k ↦ decide (c.IsFloating k ∧ valueAt k = p)

/-- By Link DOR (3b), every floating DOR associates to every node without COR. -/
def linkDor : Candidate w := (floating c .dor).foldl (fun g k ↦ linkAll g k .dor) c

/-- By Link Place (3a), every floating place feature associates to every node it may link to. -/
def linkPlace : Candidate w :=
  (List.finRange w.upper.length).foldl
    (fun g k ↦ if g.IsFloating k then linkAll g k (valueAt k) else g) c

/-- The tier element bearing `p` anchored on node `i`. -/
def anchored (p : Place) (i : Fin w.lower.length) : Option (Fin w.upper.length) :=
  (c.linksTo i).find? fun k ↦ valueAt k = p

/-- Spread `p` from node `i` to the next node when it is anchored on `i` and may link there. -/
def spreadAt (p : Place) (i : Fin w.lower.length) : Candidate w :=
  match anchored c p i with
  | some k =>
    if h : i.val + 1 < w.lower.length then
      if MayLink c p ⟨i.val + 1, h⟩ then c.insertLink k ⟨i.val + 1, h⟩ else c
    else c
  | none => c

/-- By Spread DOR (4b), iterating left to right, an anchored DOR extends to the next node. -/
def spreadDor : Candidate w := (List.finRange w.lower.length).foldl (fun g i ↦ spreadAt g .dor i) c

/-- By Spread Place (4a), iterating left to right, an anchored COR extends to the next node when
it is placeless, and an anchored LAB when it bears no DOR and is not low. -/
def spreadPlace : Candidate w :=
  (List.finRange w.lower.length).foldl (fun g i ↦ spreadAt (spreadAt g .cor i) .lab i) c

/-- The derivation applies the linking rules, the DOR rule first, and then the spreading
rules. -/
def derive : Candidate w := spreadPlace (spreadDor (linkPlace (linkDor c)))

/-- A node surfaces back with DOR, front rounded with LAB alone, and front unrounded with COR
or, by Default COR (5), when placeless. -/
inductive Quality
  | back | frontRounded | frontUnrounded
  deriving DecidableEq

/-- The quality of a place specification. -/
def quality (ps : List Place) : Quality :=
  if .dor ∈ ps then .back else if .lab ∈ ps then .frontRounded else .frontUnrounded

/-! ### Structural properties -/

variable {c}

/-- By constraint (6a), no node bears both COR and DOR. -/
def Sound (g : Candidate w) : Prop := ∀ i, ¬ (.cor ∈ places g i ∧ .dor ∈ places g i)

theorem mem_places_insertLink {p : Place} {k : Fin w.upper.length} {i j : Fin w.lower.length} :
    p ∈ places (c.insertLink k i) j ↔ p ∈ places c j ∨ (j = i ∧ valueAt k = p) := by
  simp only [places, valueAt, Candidate.mem_tierValues, Candidate.insertLink_links,
    Finset.mem_insert, Prod.mk.injEq]
  aesop

/-- Inserting a line admitted by `MayLink` keeps the form sound. -/
theorem Sound.insertLink {p : Place} {k : Fin w.upper.length} {i : Fin w.lower.length}
    (hs : Sound c) (hv : valueAt k = p) (hm : MayLink c p i) : Sound (c.insertLink k i) := by
  intro j ⟨hc, hd⟩
  rw [mem_places_insertLink] at hc hd
  rcases hc with hc | ⟨hji, hc⟩ <;> rcases hd with hd | ⟨hji', hd⟩
  · exact hs j ⟨hc, hd⟩
  · exact hm.1 (hv.symm.trans hd) (hji' ▸ hc)
  · exact List.ne_nil_of_mem (hji ▸ hd) (hm.2.1 (hv.symm.trans hc))
  · exact Place.noConfusion (hc.symm.trans hd)

/-- Every rule preserves the association lines and soundness. -/
structure Preserves (f g : Candidate w) : Prop where
  subset : f.links ⊆ g.links
  sound : Sound f → Sound g

theorem Preserves.refl : Preserves c c := ⟨subset_rfl, id⟩

theorem Preserves.trans {g h : Candidate w} (h₁ : Preserves c g) (h₂ : Preserves g h) :
    Preserves c h :=
  ⟨h₁.subset.trans h₂.subset, h₂.sound ∘ h₁.sound⟩

theorem Preserves.insertLink {p : Place} {k : Fin w.upper.length} {i : Fin w.lower.length}
    (hv : valueAt k = p) (hm : MayLink c p i) : Preserves c (c.insertLink k i) :=
  ⟨Finset.subset_insert _ _, fun hs ↦ hs.insertLink hv hm⟩

private theorem foldl_preserves {α : Type*} {step : Candidate w → α → Candidate w} (l : List α)
    (h : ∀ a ∈ l, ∀ g, Preserves c g → Preserves g (step g a)) :
    ∀ g, Preserves c g → Preserves c (l.foldl step g) := by
  induction l with
  | nil => exact fun _ hg ↦ hg
  | cons a l ih =>
    exact fun g hg ↦ ih (fun b hb ↦ h b (List.mem_cons_of_mem a hb)) _
      (hg.trans (h a (List.mem_cons_self ..) g hg))

theorem preserves_linkAll {k : Fin w.upper.length} {p : Place} (hv : valueAt k = p) :
    Preserves c (linkAll c k p) :=
  foldl_preserves _ (fun i _ g _ ↦ by
    split_ifs with hm
    · exact Preserves.insertLink hv hm
    · exact .refl) c .refl

theorem preserves_linkDor : Preserves c (linkDor c) :=
  foldl_preserves _ (fun k hk g _ ↦ by
    have hv : valueAt k = .dor := (of_decide_eq_true (List.mem_filter.1 hk).2).2
    exact preserves_linkAll hv) c .refl

theorem preserves_linkPlace : Preserves c (linkPlace c) :=
  foldl_preserves _ (fun k _ g _ ↦ by
    split_ifs
    · exact preserves_linkAll rfl
    · exact .refl) c .refl

theorem preserves_spreadAt (p : Place) (i : Fin w.lower.length) : Preserves c (spreadAt c p i) := by
  unfold spreadAt
  split
  · next k hk =>
    split_ifs with _ hm
    · simp only [anchored] at hk
      exact Preserves.insertLink (by simpa using List.find?_some hk) hm
    · exact .refl
    · exact .refl
  · exact .refl

theorem preserves_spreadDor : Preserves c (spreadDor c) :=
  foldl_preserves _ (fun i _ _ _ ↦ preserves_spreadAt .dor i) c .refl

theorem preserves_spreadPlace : Preserves c (spreadPlace c) :=
  foldl_preserves _ (fun i _ _ _ ↦ (preserves_spreadAt .cor i).trans (preserves_spreadAt .lab i))
    c .refl

theorem preserves_derive : Preserves c (derive c) :=
  preserves_linkDor.trans (preserves_linkPlace.trans
    (preserves_spreadDor.trans preserves_spreadPlace))

/-- The rules only add association lines. -/
theorem links_subset_derive : c.links ⊆ (derive c).links := preserves_derive.subset

/-- The rules never put COR and DOR on one node. -/
theorem derive_sound (hs : Sound c) : Sound (derive c) := preserves_derive.sound hs

/-! ### Stems and suffixes -/

/-- A stem's underlying representation in Table 18 gives for each vowel its aperture and the
place features prelinked to it, and the floating place features of the morpheme. -/
structure Stem where
  nodes : List (VNode × List Place)
  floating : List Place

/-- The representation of a stem row whose vowels bear the given prelinked features. -/
def Stem.ofRow (row : CLDF.Wordlist.Form Wordlist.Cell) (linked : List (List Place))
    (floating : List Place) : Stem :=
  ⟨((row.segments.filter fun l ↦ (ofLetter l).isSome).map VNode.ofLetter).zip linked, floating⟩

/-- Of the suffixes of the derivations, (2), the possessive ü/u and the ablative ö/o carry a
linked LAB, and the dative e/a, the allative ö/o/e and the inessive e/a are placeless. -/
inductive Suffix
  | poss | abl | dat | all | iness
  deriving DecidableEq

/-- The suffix vowel's aperture. -/
def Suffix.node : Suffix → VNode
  | .poss => ⟨false, false⟩
  | .abl | .all => ⟨false, true⟩
  | .dat | .iness => ⟨true, true⟩

/-- Whether the suffix vowel carries a linked LAB. -/
def Suffix.hasLab : Suffix → Bool
  | .poss | .abl => true
  | .dat | .all | .iness => false

/-- The segments of a suffix at a harmonic quality, none where that quality cannot arise. -/
def Suffix.segments : Suffix → Quality → Option (List String)
  | .poss, .back => some ["u", "n", "k"]
  | .poss, .frontRounded => some ["ü", "n", "k"]
  | .abl, .back => some ["t", "ó", "l"]
  | .abl, .frontRounded => some ["t", "ő", "l"]
  | .dat, .back => some ["n", "a", "k"]
  | .dat, .frontUnrounded => some ["n", "e", "k"]
  | .all, .back => some ["h", "o", "z"]
  | .all, .frontRounded => some ["h", "ö", "z"]
  | .all, .frontUnrounded => some ["h", "e", "z"]
  | .iness, .back => some ["b", "a", "n"]
  | .iness, .frontUnrounded => some ["b", "e", "n"]
  | _, _ => none

/-- The word of a stem and a suffix concatenates the stem's melody, its floating features and
then its prelinked features over its nodes, with the suffix's melody, a LAB over the suffix
node when the suffix has one. -/
def word (s : Stem) (x : Suffix) : Word :=
  let prelinked : List (Place × ℕ) := s.nodes.zipIdx.flatMap fun (v, i) ↦ v.2.map (·, i)
  let n := s.floating.length
  Form.melody .stem (s.floating ++ prelinked.map (·.1)) (s.nodes.map (·.1))
      (prelinked.zipIdx.map fun ((q, j) : (Place × ℕ) × ℕ) ↦ (n + j, q.2)).toFinset *
    Form.melody .suffix (if x.hasLab then [.lab] else []) [x.node]
      (if x.hasLab then {(0, 0)} else ∅)

/-- The slot of the suffix node, the last node of the word. -/
def suffixSlot (s : Stem) (x : Suffix) : Fin (word s x).lower.length :=
  ⟨s.nodes.length, by simp [word]⟩

/-- The suffix segments the derivation yields. -/
def derived (s : Stem) (x : Suffix) : Option (List String) :=
  x.segments (quality (places (derive (.input (word s x))) (suffixSlot s x)))

/-- Whether the derivation gives a stem back suffixes. -/
def Stem.isBack (s : Stem) : Bool :=
  decide (quality (places (derive (.input (word s .dat))) (suffixSlot s .dat)) = .back)

/-! ### The representations of Table 18 -/

namespace Stem

/-- The pure DOR stem *ház* 'house' has a floating DOR (8a). -/
def haz : Stem := ofRow Wordlist.haz [[]] [.dor]

/-- The pure LAB stem *tűz* 'fire' has a floating LAB (8b). -/
def tuz : Stem := ofRow Wordlist.tuz [[]] [.lab]

/-- The pure COR stem *víz* 'water' has a floating COR (8c). -/
def viz : Stem := ofRow Wordlist.viz [[]] [.cor]

/-- The COR + DOR stem *piros* 'red' has a linked COR and a floating DOR (9a). -/
def piros : Stem := ofRow Wordlist.piros [[.cor], []] [.dor]

/-- The LAB + DOR stem *nüansz* 'nuance' has both features linked (10a). -/
def nuansz : Stem := ofRow Wordlist.nuansz [[.lab], [.dor]] []

/-- The LAB + COR stem *öreg* 'old' has both features linked (10b). -/
def oreg : Stem := ofRow Wordlist.oreg [[.lab], [.cor]] []

/-- The COR + LAB stem *szemölcs* 'wart' has a floating COR and a linked LAB (11a). -/
def szemolcs : Stem := ofRow Wordlist.szemolcs [[], [.lab]] [.cor]

/-- The DOR + LAB stem *sofőr* 'driver' has a linked DOR and a labial vowel exceptionally also
coronal, which keeps DOR from spreading onto it (11b). -/
def sofor : Stem := ofRow Wordlist.sofor [[.dor], [.cor, .lab]] []

/-- The transparent DOR + COR stem *papír* 'paper' has a floating DOR and a linked COR (12a). -/
def papir : Stem := ofRow Wordlist.papir [[], [.cor]] [.dor]

/-- The antiharmonic DOR + COR stem *híd* 'bridge' has a linked COR and a floating DOR with no
node in the stem to link to (12b). -/
def hid : Stem := ofRow Wordlist.hid [[.cor]] [.dor]

/-- The opaque DOR + COR stem *kódex* 'codex' has both features linked (12c). -/
def kodex : Stem := ofRow Wordlist.kodex [[.dor], [.cor]] []

/-- The vacillating stem *dzsungel* 'jungle' represented like *papír*. -/
def dzsungelTransparent : Stem := ofRow Wordlist.dzsungel [[], [.cor]] [.dor]

/-- The vacillating stem *dzsungel* 'jungle' represented like *kódex*. -/
def dzsungelOpaque : Stem := ofRow Wordlist.dzsungel [[.dor], [.cor]] []

end Stem

/-- The stems of Table 18, each with the row of its base form. -/
def stems : List (CLDF.Wordlist.Form Wordlist.Cell × Stem) :=
  [(Wordlist.haz, .haz), (Wordlist.tuz, .tuz), (Wordlist.viz, .viz), (Wordlist.piros, .piros),
    (Wordlist.nuansz, .nuansz), (Wordlist.oreg, .oreg), (Wordlist.szemolcs, .szemolcs),
    (Wordlist.sofor, .sofor), (Wordlist.papir, .papir), (Wordlist.hid, .hid),
    (Wordlist.kodex, .kodex)]

/-- The suffixes of the derivations, by the names of the relations in the data. -/
def suffixes : List (String × Suffix) :=
  [("1pl", .poss), ("ablative", .abl), ("dative", .dat), ("allative", .all),
    ("inessive", .iness)]

/-- Every derivation of (13) to (23) from a stem of Table 18 except *dzsungel* yields the attested
suffix. -/
theorem derivations : ∀ rel ∈ Wordlist.relations, rel.form ≠ Wordlist.dzsungel →
    ∃ s ∈ stems.lookup rel.form, ∃ x ∈ suffixes.lookup rel.relation,
      derived s x = some (rel.target.segments.drop rel.form.segments.length) := by
  decide +kernel

/-- The vacillating stem of section 3.2.3.1 derives its back form from the transparent
representation and its front form from the opaque one. -/
theorem dzsungel_vacillates :
    derived .dzsungelTransparent .iness =
        some (Wordlist.dzsungelban.segments.drop Wordlist.dzsungel.segments.length) ∧
      derived .dzsungelOpaque .iness =
        some (Wordlist.dzsungelben.segments.drop Wordlist.dzsungel.segments.length) := by
  decide

/-! ### The surface generalization of section 3.2

The Fragment's palatal harmony system reads the backness of the last harmonic vowel through
the transparent neutral vowels. -/

/-- The stems whose harmonic vowels govern their suffixes as section 3.2 describes, all but the
pure COR *víz*, the antiharmonic *híd* and the opaque *kódex*. -/
def regular : List (CLDF.Wordlist.Form Wordlist.Cell × Stem) :=
  stems.filter (·.1 ∉ [Wordlist.viz, Wordlist.hid, Wordlist.kodex])

/-- On the regular stems the surface generalization and the derivations agree. -/
theorem sourceValue_agrees : ∀ t ∈ regular,
    palatalHarmony.searchCopy.sourceValue (vowelsOf t.1.segments) = some t.2.isBack := by
  decide +kernel

/-- A pure COR stem has no harmonic vowel to read, and its floating COR derives front
suffixes. -/
theorem sourceValue_viz :
    palatalHarmony.searchCopy.sourceValue (vowelsOf Wordlist.viz.segments) = none ∧
      Stem.viz.isBack = false := by
  decide

/-- An antiharmonic stem has no harmonic vowel to read either; its floating DOR derives back
suffixes. -/
theorem sourceValue_hid :
    palatalHarmony.searchCopy.sourceValue (vowelsOf Wordlist.hid.segments) = none ∧
      Stem.hid.isBack = true := by
  decide

/-- An opaque stem's last harmonic vowel is back, yet its linked DOR cannot reach the suffix
and its linked COR derives front suffixes. -/
theorem sourceValue_kodex :
    palatalHarmony.searchCopy.sourceValue (vowelsOf Wordlist.kodex.segments) = some true ∧
      Stem.kodex.isBack = false := by
  decide

end SiptarTorkenczy2000
