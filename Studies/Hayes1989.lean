module

public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.SDiff
public import Linglib.Phonology.Prosody.Mora
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Hayes (1989): Compensatory Lengthening in Moraic Phonology

This file formalizes Hayes's moraic theory of compensatory lengthening (CL): a
syllabification that gives vowels their moras underlyingly and coda consonants theirs by the
language-particular rule of Weight by Position, deletion on the segmental tier only, Parasitic
Delinking, and CL as the filling of a stranded mora by a language-particular convention, all
under the ban on crossing association lines. The typological argument of the paper's §5 is
derived from the representations: `cl_delete_of_isOnset` is the onset-deletion asymmetry (an
onset projects no mora, so its loss strands nothing, and Moraic Conservation holds by
construction), `noCrossing_cl` says that filling from the nearest linked segment never crosses a
line, and `not_noCrossing_link_of_onset` is the vowel-loss asymmetry (the vowel to the right of
a stranded mora lies outside the mora's `Autosegmental.window`, past that syllable's onset
line). The seven CL types of the typology, the weight prerequisite of §6, and the two-mora
limit and trimoraic syllables of §7 are run as derivations on the paper's forms.

## Implementation notes

The representations are `Prosody.MoraicForm`s, whose nodes stand on the timeline of the melody,
so that the lines a syllable draws directly to its onset consonants can cross the lines of a
mora, as (66) and (68) use the ban. The nuclear segments of a syllable are those its morae
dominate, and Parasitic Delinking removes a syllable with none, so a nucleus is moraic here, as
in the paper. The segments are those of the PHOIBLE chart; their features play no role in the
argument. Intervocalic clusters divide after their first consonant; every form below has a
one-consonant onset, so the language-particular division principles of §2.1 are not needed. A
CL convention takes the nearest linked segment on its side; the vowel-only restriction of (17b)
and the sonority-graded Degemination (41) of Ilokano are not modelled.

## TODO

* The cluster cases of (27d), where Stray Erasure removes the unsyllabifiable half of the
  geminate, and Degemination (41).
* The X-theory derivations of §3.1, §4, and §5.3 that the moraic account is compared against.

## References

* [hayes-1989]
* [hyman-1985]
* [ito-1986]
* [steriade-1982]
* [moran-mccloy-2019]
-/

@[expose] public section

namespace Hayes1989

open Autosegmental Prosody

/-! ### The operations of the theory -/

section Operations

variable {α : Type*} (X : MoraicForm α)

/-- The nuclear segments of syllable `s` are the slots its morae dominate. -/
def nuclear (s : ℕ) : Finset ℕ := (X.moraeOf s).biUnion X.moraSpan

/-- Parasitic Delinking (23) deletes a syllable with no nuclear segment, together with its
lines; its morae survive, now free. -/
def parasitic : MoraicForm α :=
  let dead := X.syllables.filter (nuclear X · = ∅)
  { X with syllables := X.syllables \ dead, syllableMora := X.syllableMora.filter (·.1 ∉ dead),
           syllableSegment := X.syllableSegment.filter (·.1 ∉ dead) }

/-- Prosodic Licensing ([ito-1986]) adjoins a free mora to the nearest syllable on its left. -/
def adjoin : MoraicForm α :=
  { X with syllableMora := X.syllableMora ∪ X.free.biUnion fun m ↦
      (X.syllables.filter (· ≤ m.slot)).max.recBotCoe ∅ fun v ↦ {(v, m)} }

/-- A language's CL convention ((17b), (25a), (40a)) fills a stranded mora from the nearest
segment linked to a node on its left, or from the nearest on its right. -/
inductive Convention
  | fromLeft
  | fromRight
  deriving DecidableEq, Repr

/-- `fills` is the set of lines CL draws, from each stranded mora to the nearest segment linked
on the convention's side, the endpoint of the mora's window. -/
def fills : Convention → Finset (Mora × ℕ)
  | .fromLeft => X.stranded.biUnion fun m ↦ (leftBound X.lines m.slot).recBotCoe ∅ fun j ↦ {(m, j)}
  | .fromRight =>
    X.stranded.biUnion fun m ↦ (rightBound X.lines m.slot).recTopCoe ∅ fun j ↦ {(m, j)}

/-- Compensatory lengthening fills every stranded mora with the convention's segment; a mora
with none stays stranded, for Stray Erasure. -/
def cl (c : Convention) : MoraicForm α := { X with moraSegment := X.moraSegment ∪ fills X c }

/-- The surface string after Stray Erasure pairs each linked segment with its length. -/
def surface : List (α × ℕ) :=
  X.melody.zipIdx.filterMap fun p ↦
    if 0 < X.lineCount p.2 then some (p.1, X.lineCount p.2) else none

/-- Slot `i` is an onset when no mora is linked to it. -/
def IsOnset (i : ℕ) : Prop := ∀ p ∈ X.moraSegment, p.2 ≠ i

instance (i : ℕ) : Decidable (IsOnset X i) := inferInstanceAs (Decidable (∀ p ∈ X.moraSegment, _))

/-! #### Moraic Conservation (64)

No operation but Stray Erasure touches the mora tier, so CL conserves the morae by
construction. -/

@[simp] theorem morae_adjoin : (adjoin X).morae = X.morae := rfl

@[simp] theorem morae_cl (c : Convention) : (cl X c).morae = X.morae := rfl

@[simp] theorem morae_parasitic : (parasitic X).morae = X.morae := rfl

/-! #### Stranding -/

variable {X}

-- §5.3.1
theorem stranded_delete_of_isOnset {i : ℕ} (h : IsOnset X i) :
    (X.delete i).stranded = X.stranded := by
  rw [MoraicForm.stranded_delete, Finset.union_eq_left]
  intro m hm
  obtain ⟨-, hm⟩ := Finset.mem_filter.1 hm
  exact absurd rfl (h _ (MoraicForm.mem_moraSpan.1 (hm ▸ Finset.mem_singleton_self i)).2)

theorem cl_eq_self (h : X.stranded = ∅) (c : Convention) : cl X c = X := by
  cases c <;> simp [cl, fills, h]

/-- Compensatory lengthening from onset deletion is impossible ((57), (63)). -/
theorem cl_delete_of_isOnset {i : ℕ} (h : IsOnset X i) (h₀ : X.stranded = ∅)
    (c : Convention) : cl (X.delete i) c = X.delete i :=
  cl_eq_self (by rw [stranded_delete_of_isOnset h, h₀]) c

/-! #### Crossing

Removing lines keeps a form free of crossing lines, and so does CL, which links each stranded
mora to the endpoint of its window, the nearest segment linked on the convention's side. Only
drawing a line can cross, and `MoraicForm.noCrossing_linkMora_iff` says exactly when. -/

theorem noCrossing_parasitic (h : X.NoCrossing) : (parasitic X).NoCrossing :=
  ⟨h.1.subset (Finset.coe_subset.2 (Finset.union_subset_union
      (Finset.union_subset_union subset_rfl (Finset.filter_subset _ _)) subset_rfl)), h.2,
    h.3.subset (Finset.coe_subset.2 (Finset.image_subset_image (Finset.filter_subset _ _)))⟩

variable {m : Mora} {i : ℕ}

theorem mem_fills_fromLeft {p : Mora × ℕ} :
    p ∈ fills X .fromLeft ↔ p.1 ∈ X.stranded ∧ leftBound X.lines p.1.slot = WithBot.some p.2 := by
  simp only [fills, Finset.mem_biUnion]
  refine ⟨?_, fun ⟨hm, hb⟩ ↦ ⟨p.1, hm, by simp [hb]⟩⟩
  rintro ⟨m, hm, hp⟩
  cases hb : leftBound X.lines m.slot <;> simp_all

theorem mem_fills_fromRight {p : Mora × ℕ} :
    p ∈ fills X .fromRight ↔ p.1 ∈ X.stranded ∧ rightBound X.lines p.1.slot = WithTop.some p.2 := by
  simp only [fills, Finset.mem_biUnion]
  refine ⟨?_, fun ⟨hm, hb⟩ ↦ ⟨p.1, hm, by simp [hb]⟩⟩
  rintro ⟨m, hm, hp⟩
  cases hb : rightBound X.lines m.slot <;> simp_all

theorem lines_cl (c : Convention) :
    (cl X c).lines = X.lines ∪ (fills X c).image (Prod.map Mora.slot id) := by
  simp only [MoraicForm.lines, cl, Finset.image_union, Finset.union_assoc]

theorem noCrossing_cl (h : X.NoCrossing) (c : Convention) : (cl X c).NoCrossing := by
  refine ⟨?_, h.2, h.3⟩
  rw [lines_cl]
  cases c
  · refine h.1.union_of_leftBound fun p hp ↦ ?_
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    exact (mem_fills_fromLeft.1 hq).2
  · refine h.1.union_of_rightBound fun p hp ↦ ?_
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    exact (mem_fills_fromRight.1 hq).2

/-- A stranded mora left of a syllable cannot lengthen its nucleus across the onset, so rightward
vowel-loss CL is unattested (§5.3.2, (61) and (66)). -/
theorem not_noCrossing_link_of_onset {v c : ℕ} (hc : (v, c) ∈ X.syllableSegment)
    (hm : m.slot < v) (hcv : c < v) : ¬ (X.linkMora m v).NoCrossing := fun hp ↦
  notMem_window_of_mem_image_Ioi ⟨v, hm, MoraicForm.mem_lines.2 (.inr (.inl hc))⟩ hcv
    (MoraicForm.noCrossing_linkMora_iff.1 hp).2

-- (68)
theorem not_noCrossing_link_of_coda {v c : ℕ} (hc : (Mora.of c, c) ∈ X.moraSegment)
    (hv : v < c) (hm : c < m.slot) : ¬ (X.linkMora m v).NoCrossing := fun hp ↦
  notMem_window_of_mem_image_Iio ⟨c, hm, MoraicForm.mem_lines.2 (.inr (.inr ⟨_, rfl, hc⟩))⟩ hv
    (MoraicForm.noCrossing_linkMora_iff.1 hp).2

end Operations

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
def codaMora (wbp : Bool) (limit v c : ℕ) : Mora :=
  if u.Projects wbp limit v c then .of c else
  let earlier := (List.range c).filter fun c' ↦
    u.codaHost c' = some v ∧ u.Projects wbp limit v c'
  earlier.max?.elim (.of v (u.morae v - 1)) (.of ·)

/-- The onset lines. -/
def onsets : List (ℕ × ℕ) :=
  (List.range u.length).filterMap fun c ↦ (u.onsetHost c).map fun v ↦ (v, c)

/-- The coda consonants with their syllables. -/
def codas : List (ℕ × ℕ) :=
  (List.range u.length).filterMap fun c ↦ (u.codaHost c).map fun v ↦ (v, c)

/-- Syllabification projects syllables from nuclei over their morae, adjoins onsets to the
syllable and codas to a mora, with Weight by Position for a language that has it (`wbp`) up to
its mora limit (two by default, §7). -/
def syllabify (wbp : Bool) (limit : ℕ := 2) : MoraicForm α :=
  let vMorae := u.nuclei.flatMap fun v ↦ (List.range (u.morae v)).map fun k ↦ (v, Mora.of v k)
  let cMorae := u.codas.filterMap fun p ↦
    if u.Projects wbp limit p.1 p.2 then some (p.1, Mora.of p.2) else none
  .ofLines (u.map Prod.fst) (syllableMora := (vMorae ++ cMorae).toFinset)
    (syllableSegment := u.onsets.toFinset)
    (moraSegment := (vMorae.map (fun p ↦ (p.2, p.2.slot)) ++
      u.codas.map fun p ↦ (u.codaMora wbp limit p.1 p.2, p.2)).toFinset)

end Underlying

/-! ### The forms of the paper -/

open Phonology Data.PHOIBLE Convention

/-! #### Segments -/

def a : Segment := .ofChart .«a»
def e : Segment := .ofChart .«e»
def i : Segment := .ofChart .«i»
def o : Segment := .ofChart .«o»
def u : Segment := .ofChart .«u»
def schwa : Segment := .ofChart .«ə»
def b : Segment := .ofChart .«b»
def d : Segment := .ofChart .«d»
def g : Segment := .ofChart .«ɡ»
def k : Segment := .ofChart .«k»
def l : Segment := .ofChart .«l»
def m : Segment := .ofChart .«m»
def n : Segment := .ofChart .«n»
def p : Segment := .ofChart .«p»
def r : Segment := .ofChart .«r»
def s : Segment := .ofChart .«s»
def t : Segment := .ofChart .«t»
def v : Segment := .ofChart .«v»
def w : Segment := .ofChart .«w»
def x : Segment := .ofChart .«x»
def θ : Segment := .ofChart .«θ»
def ng : Segment := .ofChart .«ŋ»

/-- A short vowel. -/
abbrev V (seg : Segment) : Segment × ℕ := (seg, 1)

/-- A long vowel ((3a)). -/
abbrev VV (seg : Segment) : Segment × ℕ := (seg, 2)

/-- A consonant or glide ((4), (5)). -/
abbrev C (seg : Segment) : Segment × ℕ := (seg, 0)

/-! #### Classical CL: Latin (12), (17) -/

/-- Latin *kasnus* 'gray' ((12b)), CVC heavy. -/
def kasnus : MoraicForm Segment := Underlying.syllabify [C k, V a, C s, C n, V u, C s] true

-- The paper's syllabification of a form is well formed and free of crossing lines.
theorem kasnus_wellFormed : kasnus.WellFormed ∧ kasnus.NoCrossing := by decide

-- (17a)
theorem kasnus_stranded : (kasnus.delete 2).stranded = {.of 2} := by decide

/-- In (17c) the stranded mora is filled by spreading from the left. -/
def kaanus : MoraicForm Segment := cl (kasnus.delete 2) fromLeft

theorem kaanus_noCrossing : kaanus.NoCrossing :=
  noCrossing_cl ((by decide : kasnus.NoCrossing).delete 2) _

theorem kaanus_surface : surface kaanus = [(k, 1), (a, 2), (n, 1), (u, 1), (s, 1)] := by decide

-- (64)
theorem kaanus_morae : kaanus.morae = kasnus.morae := rfl

/-! #### Onset deletion: Latin (14), (18) and Turkish -/

/-- In Latin *smereō* 'deserve' ((14)), word-initial *s* is an onset. -/
def smereo : MoraicForm Segment := Underlying.syllabify [C s, C m, V e, C r, V e, VV o] true

-- (18)
theorem mereo_no_cl : cl (smereo.delete 0) fromLeft = smereo.delete 0 :=
  cl_delete_of_isOnset (by decide) (by decide) _

/-- In Turkish *savmak* 'to get rid of' (§5.2.1), coda *v* deletes with CL. -/
def savmak : MoraicForm Segment := Underlying.syllabify [C s, V a, C v, C m, V a, C k] true

theorem saamak_surface :
    surface (cl (savmak.delete 2) fromLeft) = [(s, 1), (a, 2), (m, 1), (a, 1), (k, 1)] := by
  decide

/-- In Turkish *davul* 'drum', onset *v* deletes without CL, giving [daul] and not *[daːul]. -/
def davul : MoraicForm Segment := Underlying.syllabify [C d, V a, C v, V u, C l] true

theorem daul_no_cl : cl (davul.delete 2) fromLeft = davul.delete 2 :=
  cl_delete_of_isOnset (by decide) (by decide) _

/-! #### Double flop: Ancient Greek (19), (21) -/

/-- In East Ionic *odwos* 'threshold' ((19)), *d* is a moraic coda and *w* the next onset. -/
def odwos : MoraicForm Segment := Underlying.syllabify [V o, C d, C w, V o, C s] true

/-- Deleting the onset *w* strands nothing; the *d* then resyllabifies as the onset of the
following syllable, and only that strands its mora ((21)). -/
def odwos_flop : MoraicForm Segment := ((odwos.delete 2).delinkMora (.of 1) 1).linkSyllable 3 1

theorem odwos_delete_stranded : (odwos.delete 2).stranded = ∅ :=
  (stranded_delete_of_isOnset (by decide)).trans (by decide)

theorem odwos_flop_stranded : odwos_flop.stranded = {.of 1} := by decide

theorem oodos_surface :
    surface (cl odwos_flop fromLeft) = [(o, 2), (d, 1), (o, 1), (s, 1)] := by decide

theorem oodos_noCrossing : (cl odwos_flop fromLeft).NoCrossing :=
  noCrossing_cl (by decide) _

/-! #### Vowel loss: Middle English (24)–(26) and the asymmetry (61), (66), (68) -/

/-- Middle English *tale* 'tale' (Minkova 1982). -/
def tale : MoraicForm Segment := Underlying.syllabify [C t, V a, C l, V schwa] true

/-- Schwa Drop and Parasitic Delinking (24) remove the second syllable and free its mora. -/
def tal_free : MoraicForm Segment := parasitic (tale.delete 3)

theorem tal_free_nodes : tal_free.syllables = {1} ∧ tal_free.morae = {.of 1, .of 3} := by decide

/-- In (25)–(26) CL fills from the left, then the stray *l* adjoins to the migrated mora, which
the first syllable adopts. -/
def taal : MoraicForm Segment := adjoin ((cl tal_free fromLeft).linkMora (.of 3) 2)

theorem taal_noCrossing : taal.NoCrossing := by decide

theorem taal_surface : surface taal = [(t, 1), (a, 2), (l, 1)] := by decide

theorem taal_weight : taal.weight 1 = 2 := by decide

theorem taal_morae : taal.morae = tale.morae := rfl

/-- The mirror image (61), (66) is *#ala* with the first vowel deleted. -/
def ala : MoraicForm Segment := Underlying.syllabify [V a, C l, V a] true

/-- After Parasitic Delinking the first mora is free, but the *l* remains the second
syllable's onset. -/
def la_free : MoraicForm Segment := parasitic (ala.delete 0)

theorem la_free_stranded : la_free.stranded = {.of 0} := by decide

theorem no_rightward_vowel_loss : ¬ (la_free.linkMora (.of 0) 2).NoCrossing :=
  not_noCrossing_link_of_onset (c := 1) (by decide) (by decide) (by decide)

-- (56)
theorem lla_surface : surface (cl la_free fromRight) = [(l, 2), (a, 1)] := by decide

theorem lla_noCrossing : (cl la_free fromRight).NoCrossing :=
  noCrossing_cl (noCrossing_parasitic ((by decide : ala.NoCrossing).delete 0)) _

/-- The form (68), *talpa* with the final vowel deleted, whose first syllable is closed by a
moraic *l*. -/
def talpa : MoraicForm Segment := Underlying.syllabify [C t, V a, C l, C p, V a] true

def talp_free : MoraicForm Segment := parasitic (talpa.delete 4)

theorem talp_no_vowel_lengthening : ¬ (talp_free.linkMora (.of 4) 1).NoCrossing :=
  not_noCrossing_link_of_coda (c := 2) (by decide) (by decide) (by decide)

-- (7)
theorem talp_consonant_lengthening : (talp_free.linkMora (.of 4) 2).NoCrossing := by decide

theorem talp_consonant_length : (talp_free.linkMora (.of 4) 2).lineCount 2 = 2 := by decide

/-! #### Glide Formation: Ilokano (38)–(40) and Managerial Lengthening (44), (46) -/

/-- Ilokano *bagi + en* 'to have as one's own' ((27a)), CVC heavy. -/
def bagien : MoraicForm Segment := Underlying.syllabify [C b, V a, C g, V i, V e, C n] true

/-- Glide Formation (37) delinks the stem vowel from its mora, Parasitic Delinking removes its
syllable, and the stray *g* and glide adjoin to the following syllable (39). -/
def bagien_gf : MoraicForm Segment :=
  ((parasitic (bagien.delinkMora (.of 3) 3)).linkSyllable 4 2).linkSyllable 4 3

theorem bagien_gf_stranded : bagien_gf.stranded = {.of 3} := by decide

theorem bagien_gf_noCrossing : bagien_gf.NoCrossing := by decide

/-- Ilokano fills from the right ((40a)). The *g*, now an onset of the following syllable,
spreads onto the mora, which the first syllable adopts, giving *bag.gyen*. -/
def baggyen : MoraicForm Segment := adjoin (cl bagien_gf fromRight)

theorem baggyen_rightBound : rightBound bagien_gf.lines 3 = ((2 : ℕ) : WithTop ℕ) := by
  decide

theorem baggyen_surface :
    surface baggyen = [(b, 1), (a, 1), (g, 2), (i, 1), (e, 1), (n, 1)] := by decide

theorem baggyen_noCrossing : baggyen.NoCrossing := by decide

theorem baggyen_weight : baggyen.weight 1 = 2 := by decide

/-- Only the convention keeps the preceding vowel from filling the mora instead ((44)), which
would give *baagyen*, the Managerial Lengthening of English *patience* ((46)). -/
def baagyen : MoraicForm Segment := adjoin (cl bagien_gf fromLeft)

theorem baagyen_leftBound : leftBound bagien_gf.lines 3 = ((1 : ℕ) : WithBot ℕ) := by
  decide

theorem baagyen_surface :
    surface baagyen = [(b, 1), (a, 2), (g, 1), (i, 1), (e, 1), (n, 1)] := by decide

theorem baagyen_noCrossing : baagyen.NoCrossing := by decide

/-! #### Total assimilation (49b) and prenasalization (52) -/

/-- In regressive total assimilation, *asta* → *atta*, the coda deletes and the following
consonant fills its mora, the convention of Lesbian and Thessalian Greek (§3.3). -/
def asta : MoraicForm Segment := Underlying.syllabify [V a, C s, C t, V a] true

theorem atta_surface : surface (cl (asta.delete 1) fromRight) = [(a, 1), (t, 2), (a, 1)] := by
  decide

theorem atta_noCrossing : (cl (asta.delete 1) fromRight).NoCrossing :=
  noCrossing_cl ((by decide : asta.NoCrossing).delete 1) _

/-- Bantu prenasalization, *amba* → *aːmba*, which the paper lists without a derivation. Here
the nasal leaves its mora for the onset of the following syllable, and the vowel fills it. -/
def amba : MoraicForm Segment := Underlying.syllabify [V a, C m, C b, V a] true

def aamba : MoraicForm Segment := cl ((amba.delinkMora (.of 1) 1).linkSyllable 3 1) fromLeft

theorem aamba_surface : surface aamba = [(a, 2), (m, 1), (b, 1), (a, 1)] := by decide

theorem aamba_noCrossing : aamba.NoCrossing := noCrossing_cl (by decide) _

/-! #### Inverse CL: Luganda (55a) -/

/-- In Luganda *aika* → *akka*, the vowel deletes and the following consonant geminates. -/
def aika : MoraicForm Segment := Underlying.syllabify [V a, V i, C k, V a] true

def akka : MoraicForm Segment := adjoin (cl (parasitic (aika.delete 1)) fromRight)

theorem akka_surface : surface akka = [(a, 1), (k, 2), (a, 1)] := by decide

theorem akka_noCrossing : akka.NoCrossing := by decide

/-! #### The weight prerequisite (§6, (71)) -/

/-- In *pas*, in a language without Weight by Position, the coda rides the nucleus mora. -/
def pas_light : MoraicForm Segment := Underlying.syllabify [C p, V a, C s] false

/-- *pas* in a language with Weight by Position. -/
def pas_heavy : MoraicForm Segment := Underlying.syllabify [C p, V a, C s] true

theorem pas_light_no_cl : (pas_light.delete 2).stranded = ∅ := by decide

theorem pas_heavy_cl : (pas_heavy.delete 2).stranded = {.of 2} := by decide

theorem pas_light_weight : pas_light.weight 1 = 1 := by decide

theorem pas_heavy_weight : pas_heavy.weight 1 = 2 := by decide

/-! #### The two-mora limit and trimoraic syllables (§7) -/

/-- In Komi *sult.ni* 'to stand up' ((73)), the two-mora limit makes the *t* of a doubly closed
syllable share the *l*'s mora. -/
def sultni : MoraicForm Segment := Underlying.syllabify [C s, V u, C l, C t, C n, V i] true

theorem sutni_no_cl : (sultni.delete 2).stranded = ∅ := by decide

/-- In Komi *sul.ta.li* 'I stood up', the *l* alone closes its syllable and bears a mora. -/
def sultali : MoraicForm Segment :=
  Underlying.syllabify [C s, V u, C l, C t, V a, C l, V i] true

theorem suutali_surface :
    surface (cl (sultali.delete 2) fromLeft) =
      [(s, 1), (u, 2), (t, 1), (a, 1), (l, 1), (i, 1)] := by decide

/-- In Proto-Germanic *θangxta* 'thought' ((74)), CL in a nonfinal doubly closed syllable needs
a trimoraic syllable, a mora limit of three. -/
def θangxta : MoraicForm Segment := Underlying.syllabify [C θ, V a, C ng, C x, C t, V a] true 3

theorem θangxta_weight : θangxta.weight 1 = 3 := by decide

theorem θaaxta_surface :
    surface (cl (θangxta.delete 2) fromLeft) =
      [(θ, 1), (a, 2), (x, 1), (t, 1), (a, 1)] := by decide

theorem θangxta_limit_two_no_cl :
    ((Underlying.syllabify [C θ, V a, C ng, C x, C t, V a] true).delete 2).stranded = ∅ := by
  decide

/-- In Dithmarschen German *spreeke* 'speak, 1sg' ((76c)), vowel loss with CL lengthens a long
vowel to overlong, a trimoraic syllable ((77)). -/
def spreeke : MoraicForm Segment := Underlying.syllabify [C s, C p, C r, VV e, C k, V schwa] true

def spreeek : MoraicForm Segment :=
  adjoin ((cl (parasitic (spreeke.delete 5)) fromLeft).linkMora (.of 5) 4)

theorem spreeek_surface : surface spreeek = [(s, 1), (p, 1), (r, 1), (e, 3), (k, 1)] := by
  decide

theorem spreeek_weight : spreeek.weight 3 = 3 := by decide

theorem spreeek_noCrossing : spreeek.NoCrossing := by decide

end Hayes1989
