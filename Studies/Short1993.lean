module

public import Linglib.Fragments.Slavic.Czech.Phonology
public import Linglib.Data.Wordlist.Short1993
public import Mathlib.Data.Finset.Card

/-!
# Short (1993): Czech

Short's chapter on Czech in Comrie and Corbett's *The Slavonic Languages* describes the phonemes
that the Czech phonology fragment gives as segments. This file checks the fragment against the
chapter: the twenty-five consonantal phonemes, the obstruents paired in [voice], the reflexes of
the second palatalization of velars, and the reading of the spelling on the words the chapter
prints, against its phonemic transcription where it gives one.

## Main results

* `card_consonants`: the twenty-five consonantal phonemes.
* `voiced_mem_iff`, `devoiced_mem_iff`: the obstruents paired in [voice], all but *c*, *č*,
  *ch* and *h*.
* `secondPalatalization_mem`, `secondPalatalization_g`: the reflexes of the second
  palatalization are coronal stridents with the voicing of their sources, and that of *g* is
  that of *k* voiced and de-affricated.
* `ofString?_eq_segments`: the spelling reads as the chapter's transcriptions, save that of
  *oběd*, which has the final devoicing the reading leaves out (`ofString?_obed`).

## References

* [short-1993-czech]
-/

@[expose] public section

namespace Short1993

open Phonology Czech.Phonology Short1993.Wordlist

/-! ### Phonemes -/

theorem vowels_eq : vowels = {a, e, i, o, u} := by decide +kernel

/-- "There are twenty-five consonantal phonemes" (p. 457). -/
theorem card_consonants : consonants.card = 25 := by decide +kernel

/-! ### Voicing pairs -/

/-- The voiceless obstruents whose counterpart in [voice] is a phoneme are all but *c*, *č* and
*ch*, whose counterparts [dz], [dž] and [ɣ] occur only as positional variants
(pp. 457–458). -/
theorem voiced_mem_iff : ∀ x ∈ inventory, x.HasValue .sonorant false → x.HasValue .voice false →
    (x.setFeature .voice true ∈ inventory ↔ x ≠ c ∧ x ≠ č ∧ x ≠ ch) := by
  decide +kernel

/-- The counterparts in [voice] of *c*, *č* and *ch* are [dz], [dž] and [ɣ]. Where /x/ might
assimilate, "it voices not to /h/, but to [ɣ]" (p. 458). -/
theorem setFeature_voice_c_č_ch :
    c.setFeature .voice true = .ofChart .«dz» ∧ č.setFeature .voice true = .ofChart .«d̠ʒ» ∧
      ch.setFeature .voice true = .ofChart .«ɣ» := by
  decide +kernel

/-- The voiced obstruents whose counterpart in [voice] is a phoneme are all but *h*, whose
counterpart is the voiceless glottal [h]. Where voice is neutralized Short gives /x/ as the
voiceless counterpart of /h/ (p. 458), which differs from it in more than [voice]. -/
theorem devoiced_mem_iff : ∀ x ∈ inventory, x.HasValue .sonorant false →
    x.HasValue .voice true → (x.setFeature .voice false ∈ inventory ↔ x ≠ h) := by
  decide +kernel

/-- *h* and *ch*, "a nearly matching pair of fricatives" (p. 462), differ in [voice],
[spread glottis] and [consonantal], and in [dorsal] and the tongue-body features that go with
it. -/
theorem h_ch : Finset.univ.filter (fun ft ↦ h ft ≠ ch ft) =
    {.consonantal, .voice, .spreadGlottis, .dorsal, .high, .low, .front, .back} := by
  decide +kernel

/-! ### The second palatalization -/

/-- The reflexes are *c*, *z* and *š* (p. 462). -/
theorem image_secondPalatalization : palatalizing.image secondPalatalization = {c, z, š} := by
  decide +kernel

theorem secondPalatalization_mem : ∀ x ∈ palatalizing,
    secondPalatalization x ∈ inventory ∧ (secondPalatalization x).HasValue .coronal true ∧
      (secondPalatalization x).HasValue .strident true ∧
      (secondPalatalization x).HasValue .dorsal false ∧
      secondPalatalization x .voice = x .voice := by
  decide +kernel

/-- "Here too the reflex of *g* has de-affricated from *dz* to *z*" (p. 462): the reflex of *g*
is that of *k* voiced, [dz], de-affricated, and *h*, the Czech reflex of Proto-Slavic *g*
(p. 461), shares it. *k* and *g* differ in [voice] alone, and their reflexes in [continuant] as
well. -/
theorem secondPalatalization_g :
    (secondPalatalization k).setFeature .voice true = .ofChart .«dz» ∧
      (Segment.ofChart .«dz»).setFeature .continuant true = secondPalatalization g ∧
      secondPalatalization h = secondPalatalization g ∧
      Finset.univ.filter (fun ft ↦ k ft ≠ g ft) = {.voice} ∧
      Finset.univ.filter (fun ft ↦ secondPalatalization k ft ≠ secondPalatalization g ft) =
        {.continuant, .voice} := by
  decide +kernel

/-! ### Spelling -/

/-- *b*, *p*, *v* and *f* before *ě* are followed by /j/, and *m* by /ň/, so that *pěna* 'foam',
*věno* 'dowry', *harfě* 'harp' and *město* 'town' read as Short's transcriptions /pjena/,
/vjeno/, /harfje/ and /mňesto/, each transcribed phoneme read as its letter (p. 459). -/
theorem ofString?_eq_segments : ∀ w ∈ [pena, veno, harfe, mesto],
    ofString? w.form = (w.segments.mapM ofString?).map List.flatten := by
  decide +kernel

/-- *oběd* 'lunch' reads as /objed/, where Short's /objet/ has the final devoicing that
`ofString?` leaves out (p. 459). -/
theorem ofString?_obed :
    ofString? obed.form = some [o, b, j, e, d] ∧
      (obed.segments.mapM ofString?).map List.flatten = some [o, b, j, e, t] := by
  decide +kernel

/-- Length is phonemic, as in *dal* 'he gave' and *dál* 'further', *dul* 'blew' and *důl*
'mine', and *ryby* 'fish' and *rybí* 'fish-', where *y* and *i* write one vowel (p. 456). -/
theorem ofString?_length :
    ofString? dal.form = some [d, a, l] ∧ ofString? dal_long.form = some [d, a, a, l] ∧
      ofString? dul.form = some [d, u, l] ∧ ofString? dul_long.form = some [d, u, u, l] ∧
      ofString? ryby.form = some [r, i, b, i] ∧
      ofString? ryby_long.form = some [r, i, b, i, i] := by
  decide +kernel

/-- The diphthong of *soud* 'court' against the vowel of *sud* 'barrel' (p. 456). -/
theorem ofString?_diphthong :
    ofString? sud.form = some [s, u, d] ∧ ofString? soud.form = some [s, o, u, d] := by
  decide +kernel

/-- The alternation of *d* with *ď* before a front vowel, in *mladý*, *mladí*, *mladě* 'young'
(p. 462), and *ď* written with the háček before a back vowel, as in *ďábel* 'devil' (p. 459). -/
theorem ofString?_d_ď :
    ofString? mlady.form = some [m, l, a, d, i, i] ∧
      ofString? mladi.form = some [m, l, a, ď, i, i] ∧
      ofString? mlade.form = some [m, l, a, ď, e] ∧
      ofString? dabel.form = some [ď, a, a, b, e, l] := by
  decide +kernel

/-- The alternation of *t* with *ť*, in *krutý*, *krutí*, *krutě* 'cruel' (p. 462), and *ť*
before a back vowel, as in *ťuhýk* 'shrike' (p. 459). -/
theorem ofString?_t_ť :
    ofString? kruty.form = some [k, r, u, t, i, i] ∧
      ofString? kruti.form = some [k, r, u, ť, i, i] ∧
      ofString? krute.form = some [k, r, u, ť, e] ∧
      ofString? tuhyk.form = some [ť, u, h, i, i, k] := by
  decide +kernel

/-- The alternation of *n* with *ň*, in *plný*, *plně* 'full' (p. 462). -/
theorem ofString?_n_ň :
    ofString? plny.form = some [p, l, n, i, i] ∧ ofString? plne.form = some [p, l, ň, e] := by
  decide +kernel

end Short1993
