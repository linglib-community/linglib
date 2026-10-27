module

public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Finset.Union
public import Linglib.Phonology.Autosegmental.NonCrossing

/-!
# Hayes (1989): Compensatory Lengthening in Moraic Phonology

This file formalizes Hayes's moraic theory of compensatory lengthening (CL): a
syllabification that gives vowels their moras underlyingly and coda consonants theirs by the
language-particular rule of Weight by Position, deletion on the segmental tier only, Parasitic
Delinking, and CL as the filling of a stranded mora by a language-particular convention, all
under the ban on crossing association lines. The typological argument of the paper's §5 is
derived from the representations: `cl_delete_of_isOnset` is the onset-deletion asymmetry (an
onset projects no mora, so its loss strands nothing, and Moraic Conservation holds by
construction), `NoCrossing.cl` says that filling from the nearest linked segment never crosses a
line, and `not_noCrossing_link_of_onset` is the vowel-loss asymmetry (the vowel to the right of
a stranded mora lies outside the mora's `Autosegmental.window`, past that syllable's onset
line). The seven CL types of the typology, the weight prerequisite of §6, and the two-mora
limit and trimoraic syllables of §7 are run as derivations on the paper's forms.

## Implementation notes

A `Form` places every prosodic node at the timeline slot of the segment that projected it, so
the syllable, mora, and segmental tiers share one order and the lines a syllable node draws
directly to its onset consonants can cross the lines of a mora; `Autosegmental.IsNonCrossing`
on the node-to-segment lines is then the ban on crossing association lines as (66) and (68)
use it. The melody alphabet `Seg` is schematic, as the paper's forms are: segment features play
no role in the argument. Intervocalic clusters divide after their first consonant; every form
below has a one-consonant onset, so the language-particular division principles of §2.1 are
not needed. A CL convention takes the nearest linked segment on its side; the vowel-only
restriction of (17b) and the sonority-graded Degemination (41) of Ilokano are not modelled.

## TODO

* The cluster cases of (27d), where Stray Erasure removes the unsyllabifiable half of the
  geminate, and Degemination (41).
* The X-theory derivations of §3.1, §4, and §5.3 that the moraic account is compared against.

## References

* [hayes-1989]
* [hyman-1985]
* [ito-1986]
* [steriade-1982]
-/

@[expose] public section

namespace Hayes1989

open Autosegmental

/-! ### Prosodic nodes -/

/-- The prosodic tiers above the melody. -/
inductive Tier
  | syl
  | mora
  deriving DecidableEq, Repr

/-- A prosodic node records its tier and the timeline slot of the segment that projected it,
    the nucleus for a syllable node and the mora-bearing segment for a mora; `idx` tells apart
    the two morae of one long vowel ((3a)). -/
structure Node where
  tier : Tier
  slot : ℕ
  idx : ℕ := 0
  deriving DecidableEq, Repr

namespace Node

/-- The syllable node over the nucleus at slot `v`. -/
abbrev σ (v : ℕ) : Node := ⟨.syl, v, 0⟩

/-- The `k`-th mora projected from slot `i`. -/
abbrev μ (i : ℕ) (k : ℕ := 0) : Node := ⟨.mora, i, k⟩

/-- Nodes are ordered by slot, the order in which association lines are drawn. -/
instance : Preorder Node := Preorder.lift Node.slot

instance : DecidableLT Node := fun a b ↦ inferInstanceAs (Decidable (a.slot < b.slot))
instance : DecidableLE Node := fun a b ↦ inferInstanceAs (Decidable (a.slot ≤ b.slot))

end Node

open Node

/-! ### Forms -/

/-- A moraic representation over a melody, in which segment `i` occupies timeline slot `i`. -/
structure Form (α : Type*) where
  /-- The segmental tier. -/
  melody : List α
  /-- The prosodic nodes present. A syllable deleted by Parasitic Delinking is gone, while a
      stranded mora survives. -/
  nodes : Finset Node
  /-- Domination of morae by syllable nodes. -/
  dom : Finset (Node × Node)
  /-- Association lines run to the melody, from a syllable node to its onset consonants and
      from a mora to the segments it dominates. -/
  links : Finset (Node × ℕ)

namespace Form

variable {α : Type*} (f : Form α)

/-- The ban on crossing association lines, on both layers. -/
def NoCrossing : Prop :=
  IsNonCrossing (f.links : SetRel Node ℕ) ∧ IsNonCrossing (f.dom : SetRel Node Node)

instance : Decidable f.NoCrossing := by unfold Form.NoCrossing; infer_instance

/-- The slots node `n` is associated to. -/
def span (n : Node) : Finset ℕ := (f.links.filter (·.1 = n)).image (·.2)

/-- The morae of syllable node `s`. -/
def morae (s : Node) : Finset Node := (f.dom.filter (·.1 = s)).image (·.2)

/-- Syllable weight is the number of morae. -/
def weight (s : Node) : ℕ := (f.morae s).card

/-- The nuclear segments of syllable node `s` are the slots its morae dominate. -/
def nuclear (s : Node) : Finset ℕ := (f.morae s).biUnion f.span

/-- The number of association lines at slot `i`, which is one for a short segment and two for a
    long vowel ((3a)) or a geminate ((9a)). -/
def length (i : ℕ) : ℕ := (f.links.filter (·.2 = i)).card

/-- The morae stranded by a deletion on the segmental tier are those dominating nothing. -/
def stranded : Finset Node := f.nodes.filter fun n ↦ n.tier = .mora ∧ f.span n = ∅

/-- Morae no syllable node dominates. -/
def free : Finset Node := f.nodes.filter fun n ↦ n.tier = .mora ∧ n ∉ f.dom.image (·.2)

/-- The mora count of the form. -/
def moraCount : ℕ := (f.nodes.filter (·.tier = .mora)).card

/-- The surface string after Stray Erasure pairs each linked segment with its number of lines. -/
def surface : List (α × ℕ) :=
  f.melody.zipIdx.filterMap fun p ↦ if 0 < f.length p.2 then some (p.1, f.length p.2) else none

/-! #### Operations -/

/-- Deletion on the segmental tier only ((17a)) removes every association line of slot `i`, and
    a mora that dominated it alone is stranded. -/
def delete (i : ℕ) : Form α := { f with links := f.links.filter (·.2 ≠ i) }

/-- `delink` erases one association line, as Glide Formation (37) disassociates a vowel from its
    mora. -/
def delink (n : Node) (i : ℕ) : Form α := { f with links := f.links.erase (n, i) }

/-- `link` draws one association line, for spreading onto a stranded mora or adjunction of a
    stray segment. -/
def link (n : Node) (i : ℕ) : Form α := { f with links := insert (n, i) f.links }

/-- Parasitic Delinking (23) deletes a syllable node with no nuclear segment, together with its
    lines; its morae survive, now free. -/
def parasitic : Form α :=
  let dead := f.nodes.filter fun n ↦ n.tier = .syl ∧ f.nuclear n = ∅
  { f with nodes := f.nodes \ dead, dom := f.dom.filter (·.1 ∉ dead),
           links := f.links.filter (·.1 ∉ dead) }

/-- Prosodic Licensing ([ito-1986]) adjoins a free mora to the nearest syllable node on its
    left. -/
def adjoin : Form α :=
  { f with dom := f.dom ∪ f.free.biUnion fun m ↦
      let syls := (f.nodes.filter fun n ↦ n.tier = .syl ∧ n.slot ≤ m.slot).image (·.slot)
      syls.max.recBotCoe ∅ fun v ↦ {(σ v, m)} }

/-- A language's CL convention ((17b), (25a), (40a)) fills a stranded mora from the nearest
    segment linked to a node on its left, or from the nearest on its right. -/
inductive Convention
  | fromLeft
  | fromRight
  deriving DecidableEq, Repr

/-- `fills` is the set of lines CL draws, from each stranded mora to the nearest segment linked
    on the convention's side, the endpoint of the mora's window. -/
def fills : Convention → Finset (Node × ℕ)
  | .fromLeft => f.stranded.biUnion fun m ↦ (leftBound f.links m).recBotCoe ∅ fun j ↦ {(m, j)}
  | .fromRight =>
    f.stranded.biUnion fun m ↦ (rightBound f.links m).recTopCoe ∅ fun j ↦ {(m, j)}

/-- Compensatory lengthening fills every stranded mora with the convention's segment; a mora
    with none stays stranded, for Stray Erasure. -/
def cl (c : Convention) : Form α := { f with links := f.links ∪ f.fills c }

/-! #### Moraic Conservation (64)

No operation but Stray Erasure touches the mora tier, so CL conserves mora count by
construction. -/

@[simp] theorem moraCount_delete (i : ℕ) : (f.delete i).moraCount = f.moraCount := rfl

@[simp] theorem moraCount_delink (n : Node) (i : ℕ) :
    (f.delink n i).moraCount = f.moraCount := rfl

@[simp] theorem moraCount_link (n : Node) (i : ℕ) : (f.link n i).moraCount = f.moraCount := rfl

@[simp] theorem moraCount_adjoin : f.adjoin.moraCount = f.moraCount := rfl

@[simp] theorem moraCount_cl (c : Convention) : (f.cl c).moraCount = f.moraCount := rfl

@[simp] theorem moraCount_parasitic : f.parasitic.moraCount = f.moraCount := by
  unfold moraCount parasitic
  congr 1
  ext n
  simp +contextual [Finset.mem_filter, Finset.mem_sdiff]

@[simp] theorem nodes_delete (i : ℕ) : (f.delete i).nodes = f.nodes := rfl

/-! #### Stranding -/

/-- Slot `i` is an onset when only syllable nodes link to it, so that it projects no mora. -/
def IsOnset (i : ℕ) : Prop := ∀ p ∈ f.links, p.2 = i → p.1.tier = .syl

instance (i : ℕ) : Decidable (f.IsOnset i) := inferInstanceAs (Decidable (∀ p ∈ f.links, _))

theorem span_delete (n : Node) (i : ℕ) : (f.delete i).span n = (f.span n).erase i := by
  ext j
  simp only [span, delete, Finset.mem_image, Finset.mem_filter, Finset.mem_erase]
  grind

theorem stranded_delete (i : ℕ) :
    (f.delete i).stranded =
      f.stranded ∪ f.nodes.filter (fun n ↦ n.tier = .mora ∧ f.span n = {i}) := by
  ext n
  simp only [stranded, span_delete, nodes_delete, Finset.mem_union, Finset.mem_filter,
    Finset.erase_eq_empty_iff]
  tauto

-- §5.3.1
theorem stranded_delete_of_isOnset {i : ℕ} (h : f.IsOnset i) :
    (f.delete i).stranded = f.stranded := by
  rw [stranded_delete, Finset.union_eq_left, Finset.subset_iff]
  rintro n hn
  obtain ⟨-, hm, hi⟩ := Finset.mem_filter.1 hn
  have hi : i ∈ f.span n := hi ▸ Finset.mem_singleton_self i
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
  obtain ⟨hp, hpn⟩ := Finset.mem_filter.1 hp
  exact absurd (h p hp rfl) (by rw [hpn, hm]; decide)

theorem cl_eq_self (h : f.stranded = ∅) (c : Convention) : f.cl c = f := by
  cases c <;> simp [cl, fills, h]

/-- Compensatory lengthening from onset deletion is impossible ((57), (63)). -/
theorem cl_delete_of_isOnset {i : ℕ} (h : f.IsOnset i) (h₀ : f.stranded = ∅)
    (c : Convention) : (f.delete i).cl c = f.delete i :=
  (f.delete i).cl_eq_self (by rw [stranded_delete_of_isOnset f h, h₀]) c

/-! #### Crossing

Removing lines keeps a form free of crossing lines, and so does CL, which links each stranded
mora to the endpoint of its window, the nearest segment linked on the convention's side. Only
`link` can cross, and `noCrossing_link_iff` says exactly when. -/

variable {f}

theorem NoCrossing.delete (h : f.NoCrossing) (i : ℕ) : (f.delete i).NoCrossing :=
  ⟨h.1.subset (Finset.filter_subset _ _), h.2⟩

theorem NoCrossing.delink (h : f.NoCrossing) (n : Node) (i : ℕ) : (f.delink n i).NoCrossing :=
  ⟨h.1.subset (Finset.erase_subset _ _), h.2⟩

theorem NoCrossing.parasitic (h : f.NoCrossing) : f.parasitic.NoCrossing :=
  ⟨h.1.subset (Finset.filter_subset _ _), h.2.subset (Finset.filter_subset _ _)⟩

variable {m : Node} {i : ℕ}

theorem mem_fills_fromLeft {p : Node × ℕ} :
    p ∈ f.fills .fromLeft ↔ p.1 ∈ f.stranded ∧ leftBound f.links p.1 = p.2 := by
  simp only [fills, Finset.mem_biUnion]
  refine ⟨?_, fun ⟨hm, hb⟩ ↦ ⟨p.1, hm, by simp [hb]⟩⟩
  rintro ⟨m, hm, hp⟩
  cases hb : leftBound f.links m <;> simp_all

theorem mem_fills_fromRight {p : Node × ℕ} :
    p ∈ f.fills .fromRight ↔ p.1 ∈ f.stranded ∧ rightBound f.links p.1 = p.2 := by
  simp only [fills, Finset.mem_biUnion]
  refine ⟨?_, fun ⟨hm, hb⟩ ↦ ⟨p.1, hm, by simp [hb]⟩⟩
  rintro ⟨m, hm, hp⟩
  cases hb : rightBound f.links m <;> simp_all

theorem NoCrossing.cl (h : f.NoCrossing) (c : Convention) : (f.cl c).NoCrossing := by
  refine ⟨?_, h.2⟩
  cases c
  · exact h.1.union_of_leftBound fun p hp ↦ (mem_fills_fromLeft.1 hp).2
  · exact h.1.union_of_rightBound fun p hp ↦ (mem_fills_fromRight.1 hp).2

theorem noCrossing_link_iff :
    (f.link m i).NoCrossing ↔ f.NoCrossing ∧ i ∈ window (f.links : SetRel Node ℕ) m := by
  simp only [Form.NoCrossing, link, Finset.coe_insert, isNonCrossing_insert_iff_mem_window,
    and_right_comm]

/-- A stranded mora left of a syllable cannot lengthen its nucleus across the onset, so rightward
vowel-loss CL is unattested (§5.3.2, (61) and (66)). -/
theorem not_noCrossing_link_of_onset {v c : ℕ} (hc : (σ v, c) ∈ f.links) (hm : m.slot < v)
    (hcv : c < v) : ¬ (f.link m v).NoCrossing := fun hp ↦
  notMem_window_of_mem_image_Ioi ⟨σ v, hm, hc⟩ hcv
    (noCrossing_link_iff.1 hp).2

-- (68)
theorem not_noCrossing_link_of_coda {v c : ℕ} (hc : (μ c, c) ∈ f.links) (hv : v < c)
    (hm : c < m.slot) : ¬ (f.link m v).NoCrossing := fun hp ↦
  notMem_window_of_mem_image_Iio ⟨μ c, hm, hc⟩ hv
    (noCrossing_link_iff.1 hp).2

end Form

/-! ### Syllabification (§2.1)

An underlying form lists each segment with its mora count ((3)–(7)): none for a consonant or
glide, one for a short vowel, two for a long vowel. Moraic segments are nuclei; a consonant
adjoins as onset to the following nucleus when prevocalic and otherwise as coda to the
preceding one; Weight by Position (10) gives a coda its own mora while the syllable is below
the language's mora limit, and a later coda rides the syllable's last mora (§7, (73)). -/

/-- An underlying form lists segments with their mora counts. -/
abbrev Underlying (α : Type*) := List (α × ℕ)

namespace Underlying

variable {α : Type*} (u : Underlying α)

/-- The underlying mora count at slot `i`. -/
def morae (i : ℕ) : ℕ := (u[i]?.map Prod.snd).getD 0

/-- The nucleus slots. -/
def nuclei : List ℕ := (List.range u.length).filter fun i ↦ 0 < u.morae i

/-- `host i` is the nucleus of the syllable that slot `i` belongs to. That is `i` itself if it
    is moraic, the following nucleus if `i` is the consonant right before it, and the preceding
    nucleus otherwise. -/
def host (i : ℕ) : Option ℕ :=
  if 0 < u.morae i then some i else
  match (u.nuclei.filter (· < i)).max?, (u.nuclei.filter (i < ·)).min? with
  | none, none => none
  | none, some v => some v
  | some v, none => some v
  | some v₁, some v₂ => if i + 1 = v₂ then some v₂ else some v₁

/-- The nucleus slot `c` is an onset consonant of, if any. -/
def onsetHost (c : ℕ) : Option ℕ := (u.host c).bind fun v ↦ if c < v then some v else none

/-- The nucleus slot `c` is a coda consonant of, if any. -/
def codaHost (c : ℕ) : Option ℕ := (u.host c).bind fun v ↦ if v < c then some v else none

/-- The number of coda consonants of the same syllable before `c`. -/
def codaRank (c : ℕ) : ℕ :=
  ((List.range c).filter fun c' ↦ u.codaHost c' = u.codaHost c).length

/-- Weight by Position (10) gives coda `c` of the syllable at `v` its own mora when the language
    has the rule and the syllable is still below its mora limit. -/
def Projects (wbp : Bool) (limit v c : ℕ) : Prop := wbp ∧ u.morae v + u.codaRank c < limit

instance (wbp : Bool) (limit v c : ℕ) : Decidable (u.Projects wbp limit v c) := by
  unfold Projects; infer_instance

/-- The mora dominating coda `c` of the syllable at `v`, which is its own under Weight by
    Position and otherwise the syllable's last mora so far. -/
def codaMora (wbp : Bool) (limit v c : ℕ) : Node :=
  if u.Projects wbp limit v c then μ c else
  let earlier := (List.range c).filter fun c' ↦
    u.codaHost c' = some v ∧ u.Projects wbp limit v c'
  earlier.max?.elim (μ v (u.morae v - 1)) (μ ·)

/-- The onset lines. -/
def onsets : List (Node × ℕ) :=
  (List.range u.length).filterMap fun c ↦ (u.onsetHost c).map fun v ↦ (σ v, c)

/-- The coda consonants with their syllables. -/
def codas : List (ℕ × ℕ) :=
  (List.range u.length).filterMap fun c ↦ (u.codaHost c).map fun v ↦ (v, c)

/-- Syllabification projects syllable nodes from nuclei over their morae, adjoins onsets to the
    syllable node and codas to a mora, with Weight by Position for a language that has it
    (`wbp`) up to its mora limit (two by default, §7). -/
def syllabify (wbp : Bool) (limit : ℕ := 2) : Form α :=
  let vMorae := u.nuclei.flatMap fun v ↦ (List.range (u.morae v)).map fun k ↦ (σ v, μ v k)
  let cMorae := u.codas.filterMap fun p ↦
    if u.Projects wbp limit p.1 p.2 then some (σ p.1, μ p.2) else none
  { melody := u.map Prod.fst
    nodes := (u.nuclei.map σ ++ (vMorae ++ cMorae).map Prod.snd).toFinset
    dom := (vMorae ++ cMorae).toFinset
    links := (u.onsets ++ vMorae.map (fun p ↦ (p.2, p.2.slot)) ++
      u.codas.map (fun p ↦ (u.codaMora wbp limit p.1 p.2, p.2))).toFinset }

end Underlying

/-! ### The forms of the paper -/

/-- The schematic melody alphabet of the paper's forms. -/
inductive Seg
  | a | e | i | o | u | schwa
  | b | d | g | k | l | m | n | p | r | s | t | v | w | x | θ | ng
  deriving DecidableEq, Repr

open Seg Form.Convention

/-- A short vowel. -/
abbrev V (seg : Seg) : Seg × ℕ := (seg, 1)

/-- A long vowel ((3a)). -/
abbrev VV (seg : Seg) : Seg × ℕ := (seg, 2)

/-- A consonant or glide ((4), (5)). -/
abbrev C (seg : Seg) : Seg × ℕ := (seg, 0)

/-! #### Classical CL: Latin (12), (17) -/

/-- Latin *kasnus* 'gray' ((12b)), CVC heavy. -/
def kasnus : Form Seg := Underlying.syllabify [C k, V a, C s, C n, V u, C s] true

-- (17a)
theorem kasnus_stranded : (kasnus.delete 2).stranded = {μ 2} := by decide

/-- In (17c) the stranded mora is filled by spreading from the left. -/
def kaanus : Form Seg := (kasnus.delete 2).cl fromLeft

theorem kaanus_noCrossing : kaanus.NoCrossing := ((by decide : kasnus.NoCrossing).delete 2).cl _

theorem kaanus_surface : kaanus.surface = [(k, 1), (a, 2), (n, 1), (u, 1), (s, 1)] := by decide

-- (64)
theorem kaanus_moraCount : kaanus.moraCount = kasnus.moraCount := by simp [kaanus]

/-! #### Onset deletion: Latin (14), (18) and Turkish -/

/-- In Latin *smereō* 'deserve' ((14)), word-initial *s* is an onset. -/
def smereo : Form Seg := Underlying.syllabify [C s, C m, V e, C r, V e, VV o] true

-- (18)
theorem mereo_no_cl : (smereo.delete 0).cl fromLeft = smereo.delete 0 :=
  smereo.cl_delete_of_isOnset (by decide) (by decide) _

/-- In Turkish *savmak* 'to get rid of' (§5.2.1), coda *v* deletes with CL. -/
def savmak : Form Seg := Underlying.syllabify [C s, V a, C v, C m, V a, C k] true

theorem saamak_surface :
    ((savmak.delete 2).cl fromLeft).surface = [(s, 1), (a, 2), (m, 1), (a, 1), (k, 1)] := by
  decide

/-- In Turkish *davul* 'drum', onset *v* deletes without CL, giving [daul] and not *[daːul]. -/
def davul : Form Seg := Underlying.syllabify [C d, V a, C v, V u, C l] true

theorem daul_no_cl : (davul.delete 2).cl fromLeft = davul.delete 2 :=
  davul.cl_delete_of_isOnset (by decide) (by decide) _

/-! #### Double flop: Ancient Greek (19), (21) -/

/-- In East Ionic *odwos* 'threshold' ((19)), *d* is a moraic coda and *w* the next onset. -/
def odwos : Form Seg := Underlying.syllabify [V o, C d, C w, V o, C s] true

/-- Deleting the onset *w* strands nothing; the *d* then resyllabifies as the onset of the
    following syllable, and only that strands its mora ((21)). -/
def odwos_flop : Form Seg := ((odwos.delete 2).delink (μ 1) 1).link (σ 3) 1

theorem odwos_delete_stranded : (odwos.delete 2).stranded = ∅ :=
  odwos.stranded_delete_of_isOnset (by decide)

theorem odwos_flop_stranded : odwos_flop.stranded = {μ 1} := by decide

theorem oodos_surface :
    (odwos_flop.cl fromLeft).surface = [(o, 2), (d, 1), (o, 1), (s, 1)] := by decide

theorem oodos_noCrossing : (odwos_flop.cl fromLeft).NoCrossing :=
  (by decide : odwos_flop.NoCrossing).cl _

/-! #### Vowel loss: Middle English (24)–(26) and the asymmetry (61), (66), (68) -/

/-- Middle English *tale* 'tale' (Minkova 1982). -/
def tale : Form Seg := Underlying.syllabify [C t, V a, C l, V schwa] true

/-- Schwa Drop and Parasitic Delinking (24) remove the second syllable and free its mora. -/
def tal_free : Form Seg := (tale.delete 3).parasitic

theorem tal_free_nodes : tal_free.nodes = {σ 1, μ 1, μ 3} := by decide

/-- In (25)–(26) CL fills from the left, then the stray *l* adjoins to the migrated mora, which
    the first syllable adopts. -/
def taal : Form Seg := ((tal_free.cl fromLeft).link (μ 3) 2).adjoin

theorem taal_noCrossing : taal.NoCrossing := by decide

theorem taal_surface : taal.surface = [(t, 1), (a, 2), (l, 1)] := by decide

theorem taal_weight : taal.weight (σ 1) = 2 := by decide

theorem taal_moraCount : taal.moraCount = tale.moraCount := by simp [taal, tal_free]

/-- The mirror image (61), (66) is *#ala* with the first vowel deleted. -/
def ala : Form Seg := Underlying.syllabify [V a, C l, V a] true

/-- After Parasitic Delinking the first mora is free, but the *l* remains the second
    syllable's onset. -/
def la_free : Form Seg := (ala.delete 0).parasitic

theorem la_free_stranded : la_free.stranded = {μ 0} := by decide

theorem no_rightward_vowel_loss : ¬ (la_free.link (μ 0) 2).NoCrossing :=
  Form.not_noCrossing_link_of_onset (c := 1) (by decide) (by decide) (by decide)

-- (56)
theorem lla_surface : ((la_free.cl fromRight).surface) = [(l, 2), (a, 1)] := by decide

theorem lla_noCrossing : (la_free.cl fromRight).NoCrossing :=
  ((by decide : ala.NoCrossing).delete 0).parasitic.cl _

/-- The form (68), *talpa* with the final vowel deleted, whose first syllable is closed by a
    moraic *l*. -/
def talpa : Form Seg := Underlying.syllabify [C t, V a, C l, C p, V a] true

def talp_free : Form Seg := (talpa.delete 4).parasitic

theorem talp_no_vowel_lengthening : ¬ (talp_free.link (μ 4) 1).NoCrossing :=
  Form.not_noCrossing_link_of_coda (c := 2) (by decide) (by decide) (by decide)

-- (7)
theorem talp_consonant_lengthening : (talp_free.link (μ 4) 2).NoCrossing := by decide

theorem talp_consonant_length : (talp_free.link (μ 4) 2).length 2 = 2 := by decide

/-! #### Glide Formation: Ilokano (38)–(40) and Managerial Lengthening (44), (46) -/

/-- Ilokano *bagi + en* 'to have as one's own' ((27a)), CVC heavy. -/
def bagien : Form Seg := Underlying.syllabify [C b, V a, C g, V i, V e, C n] true

/-- Glide Formation (37) delinks the stem vowel from its mora, Parasitic Delinking removes its
    syllable, and the stray *g* and glide adjoin to the following syllable (39). -/
def bagien_gf : Form Seg := ((bagien.delink (μ 3) 3).parasitic.link (σ 4) 2).link (σ 4) 3

theorem bagien_gf_stranded : bagien_gf.stranded = {μ 3} := by decide

theorem bagien_gf_noCrossing : bagien_gf.NoCrossing := by decide

/-- Ilokano fills from the right ((40a)). The *g*, now an onset of the following syllable,
    spreads onto the mora, which the first syllable adopts, giving *bag.gyen*. -/
def baggyen : Form Seg := (bagien_gf.cl fromRight).adjoin

theorem baggyen_rightBound : rightBound bagien_gf.links (μ 3) = ((2 : ℕ) : WithTop ℕ) := by
  decide

theorem baggyen_surface :
    baggyen.surface = [(b, 1), (a, 1), (g, 2), (i, 1), (e, 1), (n, 1)] := by decide

theorem baggyen_noCrossing : baggyen.NoCrossing := by decide

theorem baggyen_weight : baggyen.weight (σ 1) = 2 := by decide

/-- Only the convention keeps the preceding vowel from filling the mora instead ((44)), which
    would give *baagyen*, the Managerial Lengthening of English *patience* ((46)). -/
def baagyen : Form Seg := (bagien_gf.cl fromLeft).adjoin

theorem baagyen_leftBound : leftBound bagien_gf.links (μ 3) = ((1 : ℕ) : WithBot ℕ) := by
  decide

theorem baagyen_surface :
    baagyen.surface = [(b, 1), (a, 2), (g, 1), (i, 1), (e, 1), (n, 1)] := by decide

theorem baagyen_noCrossing : baagyen.NoCrossing := by decide

/-! #### Total assimilation (49b) and prenasalization (52) -/

/-- In regressive total assimilation, *asta* → *atta*, the coda deletes and the following
    consonant fills its mora, the convention of Lesbian and Thessalian Greek (§3.3). -/
def asta : Form Seg := Underlying.syllabify [V a, C s, C t, V a] true

theorem atta_surface : ((asta.delete 1).cl fromRight).surface = [(a, 1), (t, 2), (a, 1)] := by
  decide

theorem atta_noCrossing : ((asta.delete 1).cl fromRight).NoCrossing :=
  ((by decide : asta.NoCrossing).delete 1).cl _

/-- Bantu prenasalization, *amba* → *aːmba*, which the paper lists without a derivation. Here
    the nasal leaves its mora for the onset of the following syllable, and the vowel fills it. -/
def amba : Form Seg := Underlying.syllabify [V a, C m, C b, V a] true

def aamba : Form Seg := ((amba.delink (μ 1) 1).link (σ 3) 1).cl fromLeft

theorem aamba_surface : aamba.surface = [(a, 2), (m, 1), (b, 1), (a, 1)] := by decide

theorem aamba_noCrossing : aamba.NoCrossing := Form.NoCrossing.cl (by decide) _

/-! #### Inverse CL: Luganda (55a) -/

/-- In Luganda *aika* → *akka*, the vowel deletes and the following consonant geminates. -/
def aika : Form Seg := Underlying.syllabify [V a, V i, C k, V a] true

def akka : Form Seg := ((aika.delete 1).parasitic.cl fromRight).adjoin

theorem akka_surface : akka.surface = [(a, 1), (k, 2), (a, 1)] := by decide

theorem akka_noCrossing : akka.NoCrossing := by decide

/-! #### The weight prerequisite (§6, (71)) -/

/-- In *pas*, in a language without Weight by Position, the coda rides the nucleus mora. -/
def pas_light : Form Seg := Underlying.syllabify [C p, V a, C s] false

/-- *pas* in a language with Weight by Position. -/
def pas_heavy : Form Seg := Underlying.syllabify [C p, V a, C s] true

theorem pas_light_no_cl : (pas_light.delete 2).stranded = ∅ := by decide

theorem pas_heavy_cl : (pas_heavy.delete 2).stranded = {μ 2} := by decide

theorem pas_light_weight : pas_light.weight (σ 1) = 1 := by decide

theorem pas_heavy_weight : pas_heavy.weight (σ 1) = 2 := by decide

/-! #### The two-mora limit and trimoraic syllables (§7) -/

/-- In Komi *sult.ni* 'to stand up' ((73)), the two-mora limit makes the *t* of a doubly closed
    syllable share the *l*'s mora. -/
def sultni : Form Seg := Underlying.syllabify [C s, V u, C l, C t, C n, V i] true

theorem sutni_no_cl : (sultni.delete 2).stranded = ∅ := by decide

/-- In Komi *sul.ta.li* 'I stood up', the *l* alone closes its syllable and bears a mora. -/
def sultali : Form Seg := Underlying.syllabify [C s, V u, C l, C t, V a, C l, V i] true

theorem suutali_surface :
    ((sultali.delete 2).cl fromLeft).surface =
      [(s, 1), (u, 2), (t, 1), (a, 1), (l, 1), (i, 1)] := by decide

/-- In Proto-Germanic *θangxta* 'thought' ((74)), CL in a nonfinal doubly closed syllable needs
    a trimoraic syllable, a mora limit of three. -/
def θangxta : Form Seg := Underlying.syllabify [C θ, V a, C ng, C x, C t, V a] true 3

theorem θangxta_weight : θangxta.weight (σ 1) = 3 := by decide

theorem θaaxta_surface :
    ((θangxta.delete 2).cl fromLeft).surface =
      [(θ, 1), (a, 2), (x, 1), (t, 1), (a, 1)] := by decide

theorem θangxta_limit_two_no_cl :
    ((Underlying.syllabify [C θ, V a, C ng, C x, C t, V a] true).delete 2).stranded = ∅ := by
  decide

/-- In Dithmarschen German *spreeke* 'speak, 1sg' ((76c)), vowel loss with CL lengthens a long
    vowel to overlong, a trimoraic syllable ((77)). -/
def spreeke : Form Seg := Underlying.syllabify [C s, C p, C r, VV e, C k, V schwa] true

def spreeek : Form Seg := (((spreeke.delete 5).parasitic.cl fromLeft).link (μ 5) 4).adjoin

theorem spreeek_surface : spreeek.surface = [(s, 1), (p, 1), (r, 1), (e, 3), (k, 1)] := by
  decide

theorem spreeek_weight : spreeek.weight (σ 3) = 3 := by decide

theorem spreeek_noCrossing : spreeek.NoCrossing := by decide

end Hayes1989
