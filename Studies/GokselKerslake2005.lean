module

public import Linglib.Fragments.Turkish.Possession
public import Linglib.Fragments.Turkish.Verbs

/-!
# Göksel and Kerslake (2005): Turkish suffixation

This file checks the account of the form and order of Turkish suffixes in the reference
grammar of Göksel and Kerslake against the Turkish Fragment.

The vowel harmony of Chapter 3 is derived by the surface forms of `Turkish.Phonology` from the
exponent forms of `Turkish.Morphotactics`. The permissible vowel sequences of §3.1 are the
surface forms of the two suffix vowels. The last vowel of a disharmonic loan decides
(*otobüs-ler*), an invariant suffix vowel is skipped and triggers what follows (*görüyorum*,
§3.4), and the palatal l of *gol* fronts its suffix (§3.4). The bracketed segments of Chapter 6
appear where they keep vowels and consonants apart (§6.1.3), and a stem-final `a` or `e`,
the vowel of the negative included, is raised before -(I)yor (§8.2.3.3).

The suffix order of Chapter 8 is licensing by the templates of the finite verb and the nominal.
The grammar's example words are licensed with their stacked voice suffixes, reversed orders are
not, and the rule that markers of one position cannot co-occur (§8.2.3) holds because the
template does not repeat the position.

The possessive and locative existential sentences of §12.1.1.2 are those of
`Turkish.Possession`, with the possessive suffix on the possessee obligatory (§14.4).

## Main results

* `followers_table`: the §3.1 table of permissible vowel sequences.
* `retriggering`, `palatal_l`: the §3.4 exceptions to harmony, derived rather than listed.
* `deletable_vowels`, `deletable_consonants`, `predicate_buffers`: the bracketed segments of
  §6.1.3 after consonant-final and vowel-final stems.
* `hiatus_repairs`: the two kinds of bracketed segment as elision and insertion at a juncture.
* `pronominal_n`: the final `n` of a third-person possessive before a case suffix.
* `imperfective_of_vowel_stems`, `negative_raised`: the vowel-final stems of §8.2.3.3 and the
  negative of §8.2.2 before -(I)yor.
* `causative_stems`, `spelled_stems`: the -DIr causatives of §8.2.1.1 and the Fragment's verbs.
* `finite_verb`: §8.2 (7), every slot of the finite verb.
* `same_position_excluded`: §8.2.3 (i), since the template does not repeat position 3.
* `possessive_existential`, `locative_existential`: §12.1.1.2 (21), (22), (26) and (17).
* `possessive_obligatory`: §14.4 (117), the possessive suffix on the possessee.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
-/

@[expose] public section

namespace GokselKerslake2005

open Turkish Phonology Verb.Exponent Nominal.Exponent

/-! ### Vowel harmony (Chapter 3) -/

/-- `followers v` lists the vowels that may follow `v` in a suffix, the surface forms of `A`
and of `I` after it. -/
def followers (v : Segment) : List Segment :=
  [A, I].map fun x ↦ (surface [v, x]).getLastD x

/-- The permissible vowel sequences are those the grammar tabulates (§3.1). -/
theorem followers_table :
    followers a = [a, ı] ∧ followers ı = [a, ı] ∧ followers o = [a, u] ∧ followers u = [a, u] ∧
    followers e = [e, i] ∧ followers i = [e, i] ∧ followers ö = [e, ü] ∧ followers ü = [e, ü] := by
  decide

/-- The second-person possessive -(I)n on *kız*, *el*, *kol* and *göz* surfaces with each of the
four high vowels (§3.2.1). -/
theorem iType :
    realize [k, ı, z] [(possessive (.personNumber .second .singular)).form] =
        [k, ı, z, ı, n] ∧
    realize [e, l] [(possessive (.personNumber .second .singular)).form] =
        [e, l, i, n] ∧
    realize [k, o, l] [(possessive (.personNumber .second .singular)).form] =
        [k, o, l, u, n] ∧
    realize [g, ö, z] [(possessive (.personNumber .second .singular)).form] =
        [g, ö, z, ü, n] := by
  decide

/-- The last vowel of a stem decides, so the disharmonic loan *otobüs* takes *-ler*
(Chapter 3). -/
theorem last_vowel_decides :
    realize [o, t, o, b, ü, s] [plural.form] =
      [o, t, o, b, ü, s, l, e, r] := by
  decide

/-- In *üz-ül-dü-nüz* 'you became sad' rounding is copied through three suffixes, and the `D`
of -DI is voiced after `l` (§3.2). -/
theorem iterated :
    realize [ü, z] [passive.form, di.form, (person .one (.personNumber .second .plural)).form] =
      [ü, z, ü, l, d, ü, n, ü, z] := by
  decide

/-- The `o` of -(I)yor does not harmonize and triggers the person marker in *gör-üyor-um*, and
the converb -(y)ken is invariable in *bak-mış-ken* (§3.4 (vi)). -/
theorem retriggering :
    realize [g, ö, r] [iyor.form, (person .two (.personNumber .first .singular)).form] =
      [g, ö, r, ü, y, o, r, u, m] ∧
    realize [b, a, k] [miş.form, ⟨some y, [k, e, n]⟩] = [b, a, k, m, ı, ş, k, e, n] := by
  decide

/-- The palatal l of *gol* and *hal* fronts the suffix in *gol-ü* and *hal-im*, while rounding
still comes from the vowel (§3.4 (iv)). -/
theorem palatal_l :
    realize [g, o, l'] [(possessive (.personNumber .third .singular)).form] =
      [g, o, l', ü] ∧
    realize [h, a, l'] [(possessive (.personNumber .first .singular)).form] =
      [h, a, l', i, m] := by
  decide

/-- The `D` of -DI is `d` after a voiced segment and `t` after a voiceless one, as in *kal-dı*
and *düş-tü* (§6.1.2). -/
theorem voicing_of_D :
    realize [k, a, l] [di.form] = [k, a, l, d, ı] ∧
    realize [d, ü, ş] [di.form] = [d, ü, ş, t, ü] := by
  decide

/-- A bracketed vowel appears after a consonant and is lost after a vowel, as in *pul-um*,
*ev-im* against *araba-m*, *ev-iniz* against *araba-nız*, *ev-imiz* against *araba-mız*, and
the aorist *gör-ür* against *ara-r* (§6.1.3, §8.1.2). -/
theorem deletable_vowels :
    realize [p, u, l] [(possessive (.personNumber .first .singular)).form] = [p, u, l, u, m] ∧
    realize [e, v] [(possessive (.personNumber .first .singular)).form] = [e, v, i, m] ∧
    realize [a, r, a, b, a] [(possessive (.personNumber .first .singular)).form] = [a, r, a, b, a,
                                                                                    m] ∧
    realize [e, v] [(possessive (.personNumber .second .plural)).form] = [e, v, i, n, i, z] ∧
    realize [a, r, a, b, a] [(possessive (.personNumber .second .plural)).form] =
      [a, r, a, b, a, n, ı, z] ∧
    realize [e, v] [(possessive (.personNumber .first .plural)).form] = [e, v, i, m, i, z] ∧
    realize [a, r, a, b, a] [(possessive (.personNumber .first .plural)).form] =
      [a, r, a, b, a, m, ı, z] ∧
    realize [g, ö, r] [aorist.form] = [g, ö, r, ü, r] ∧
    realize [a, r, a] [aorist.form] = [a, r, a, r] := by
  decide

/-- A bracketed consonant appears after a vowel and is lost after a consonant. The buffer `y`
does so in *Emine-ye*, *masa-ya* and *atla-yacak* against *sor-acak*, the `n` of the genitive
in *Suna-nın* and *Emine-nin* against *Betül-ün*, and the `s` of the possessive in *araba-sı*
and *elbise-si* against *ev-i* (§6.1.3, §8.1.2, §8.1.3). -/
theorem deletable_consonants :
    realize [e, m, i, n, e] [dative.form] = [e, m, i, n, e, y, e] ∧
    realize [m, a, s, a] [dative.form] = [m, a, s, a, y, a] ∧
    realize [a, t, l, a] [acak.form] = [a, t, l, a, y, a, c, a, K] ∧
    realize [s, o, r] [acak.form] = [s, o, r, a, c, a, K] ∧
    realize [s, u, n, a] [genitive.form] = [s, u, n, a, n, ı, n] ∧
    realize [e, m, i, n, e] [genitive.form] = [e, m, i, n, e, n, i, n] ∧
    realize [b, e, t, ü, l] [genitive.form] = [b, e, t, ü, l, ü, n] ∧
    realize [a, r, a, b, a] [(possessive (.personNumber .third .singular)).form] = [a, r, a, b, a,
                                                                                    s, ı] ∧
    realize [e, l, b, i, s, e] [(possessive (.personNumber .third .singular)).form] =
      [e, l, b, i, s, e, s, i] ∧
    realize [e, v] [(possessive (.personNumber .third .singular)).form] = [e, v, i] := by
  decide

/-- A third-person possessive takes a final `n` before a case suffix, as in *tepe-si-n-de*,
*yüz-ü-n-e* and *elbise-leri-n-e*, where the `n` also keeps the buffer `y` of the dative away.
It takes none word-finally, as in *tepe-si*, and the other possessives take none, as in
*oda-m-da* (§6.2 (iib), §8.1.2). -/
theorem pronominal_n :
    realize [t, e, p, e]
        (Nominal.forms [⟨_, possessive (.personNumber .third .singular)⟩, ⟨_, locative⟩]) =
      [t, e, p, e, s, i, n, d, e] ∧
    realize [y, ü,
             z] (Nominal.forms [⟨_, possessive (.personNumber .third .singular)⟩, ⟨_, dative⟩]) =
      [y, ü, z, ü, n, e] ∧
    realize [e, l, b, i, s, e]
        (Nominal.forms [⟨_, possessive (.personNumber .third .plural)⟩, ⟨_, dative⟩]) =
      [e, l, b, i, s, e, l, e, r, i, n, e] ∧
    realize [t, e, p, e] (Nominal.forms [⟨_, possessive (.personNumber .third .singular)⟩]) =
      [t, e, p, e, s, i] ∧
    realize [o, d,
             a] (Nominal.forms [⟨_, possessive (.personNumber .first .singular)⟩, ⟨_, locative⟩]) =
      [o, d, a, m, d, a] := by
  decide

/-- The juncture of *araba* 'car' and the vowel of -(I)m. -/
def arabaIm : Hiatus.Juncture := ⟨[a, r, a, b], a, I, [m], by decide, by decide⟩

/-- The juncture of *masa* 'table' and the vowel of -(y)A. -/
def masaA : Hiatus.Juncture := ⟨[m, a, s], a, A, [], by decide, by decide⟩

/-- The two kinds of bracketed segment are the two repairs of hiatus at a juncture. In
*araba-m* the vowel of -(I)m is elided, and in *masa-ya* the `y` of -(y)A is inserted
(§6.1.3). -/
theorem hiatus_repairs :
    (possessive (.personNumber .first .singular)).form.attach arabaIm.stem = arabaIm.elideV2 ∧
    dative.form.attach masaA.stem = masaA.epenthesize y :=
  ⟨Suffix.attach_eq_elideV2 arabaIm rfl rfl,
    Suffix.attach_eq_epenthesize masaA rfl (by decide) rfl⟩

/-- The copular markers and the first-person markers of group 2 take the buffer `y` after a
vowel, as in *okul-da-yım*, *ev-de-ydi-k*, *hasta-ysa-lar* and *kat-sa-ydı-lar* (§8.4). -/
theorem predicate_buffers :
    realize [o, k, u, l] [locative.form, (person .two (.personNumber .first .singular)).form] =
      [o, k, u, l, d, a, y, ı, m] ∧
    realize [e, v] [locative.form, pastCopula.form,
                    (person .one (.personNumber .first .plural)).form] =
      [e, v, d, e, y, d, i, k] ∧
    realize [h, a, s, t, a] [conditionalCopula.form,
                             (person .one (.personNumber .third .plural)).form] =
      [h, a, s, t, a, y, s, a, l, a, r] ∧
    realize [k, a, t] [sa.form, pastCopula.form,
                       (person .one (.personNumber .third .plural)).form] =
      [k, a, t, s, a, y, d, ı, l, a, r] := by
  decide

/-- Before -(I)yor a stem-final `a` or `e` becomes high and harmonizes, as in *anlıyor*,
*okşuyor*, *bekliyor* and *özlüyor*, and a stem-final high vowel stands, as in *eriyor* and
*kuruyor* (§8.2.3.3). -/
theorem imperfective_of_vowel_stems :
    realize [a, n, l, a] [iyor.form] = [a, n, l, ı, y, o, r] ∧
    realize [o, k, ş, a] [iyor.form] = [o, k, ş, u, y, o, r] ∧
    realize [b, e, k, l, e] [iyor.form] = [b, e, k, l, i, y, o, r] ∧
    realize [ö, z, l, e] [iyor.form] = [ö, z, l, ü, y, o, r] ∧
    realize [e, r, i] [iyor.form] = [e, r, i, y, o, r] ∧
    realize [k, u, r, u] [iyor.form] = [k, u, r, u, y, o, r] := by
  decide

/-- The vowel of the negative is a stem-final vowel before -(I)yor like any other, as in
*anla-mı-yor*, *gör-mü-yor*, *sakla-mı-yor* and *söyle-mi-yor* (§8.2.2, §8.2.3.3). -/
theorem negative_raised :
    realize [a, n, l, a] [negative.form, iyor.form] =
      [a, n, l, a, m, ı, y, o, r] ∧
    realize [g, ö, r] [negative.form, iyor.form] =
      [g, ö, r, m, ü, y, o, r] ∧
    realize [s, a, k, l, a] [negative.form, iyor.form] =
      [s, a, k, l, a, m, ı, y, o, r] ∧
    realize [s, ö, y, l, e] [negative.form, iyor.form] =
      [s, ö, y, l, e, m, i, y, o, r] := by
  decide

/-- *Ev-ler-imiz-de-ymiş-ler* 'apparently they are at our homes' is the nominal string, the
evidential copula, whose buffer `y` appears after the locative's vowel, and a group-2 person
marker (§8.1 (2)). -/
theorem nominal_predicate :
    realize [e, v] [plural.form, (possessive (.personNumber .first .plural)).form, locative.form,
        evidentialCopula.form, (person .two (.personNumber .third .plural)).form] =
      [e, v, l, e, r, i, m, i, z, d, e, y, m, i, ş, l, e, r] := by
  decide

/-- The causative -DIr on *yap-*, *koy-*, *öl-* and *dol-* gives the stems *yaptır-*,
*koydur-*, *öldür-* and *doldur-* (§8.2.1.1). -/
theorem causative_stems :
    realize [y, a, p] [causative.form] = [y, a, p, t, ı, r] ∧
    realize [k, o, y] [causative.form] = [k, o, y, d, u, r] ∧
    realize [ö, l] [causative.form] = [ö, l, d, ü, r] ∧
    realize [d, o, l] [causative.form] = [d, o, l, d, u, r] := by
  decide

/-- The spelled stem of every verb of the Fragment writes the surface form of its root and
voice suffixes, the causatives *öldür-* and *yaptır-* among them. -/
theorem spelled_stems : ∀ v ∈ verbs, ofString? v.form = some (v.inflect []) := by
  decide

/-! ### The order of suffixes (Chapter 8) -/

/-- *çocuk-lar-ın-a* 'to your children' has the order number, possession, case (§8.1 (1)). -/
theorem nominal :
    Nominal.template.Licensed (E := Nominal.Exponent)
      [⟨_, .plural⟩, ⟨_, .possessive (.personNumber .second .singular)⟩, ⟨_, .dative⟩] := by
  decide

/-- *Döğ-üş-tür-t-ül-me-yebil-iyor-muş-sunuz-dur* fills every slot of the finite verb, the
voice slot with four stacked suffixes (§8.2 (7)). -/
theorem finite_verb :
    Verb.template.Licensed (E := Verb.Exponent)
      [⟨_, .reciprocal⟩, ⟨_, .causative⟩, ⟨_, .causative⟩, ⟨_, .passive⟩, ⟨_, .negative⟩,
        ⟨_, .abil⟩, ⟨_, .iyor⟩, ⟨_, .evidentialCopula⟩,
        ⟨_, .person .two (.personNumber .second .plural)⟩,
        ⟨_, .dir⟩] := by
  decide

/-- *Bitir-e-me-miş-tir*, *Oku-yabil-ecek-miş* and *git-ti-ydi-n* fill positions 1-3-5, 2-3-4,
and 3-4 with a group-1 person marker (§8.2.3 (11), (12), §8.2.3.3). -/
theorem tam_positions :
    Verb.template.Licensed (E := Verb.Exponent)
      [⟨_, .possibility⟩, ⟨_, .negative⟩, ⟨_, .miş⟩, ⟨_, .dir⟩] ∧
    Verb.template.Licensed (E := Verb.Exponent)
      [⟨_, .abil⟩, ⟨_, .acak⟩, ⟨_, .evidentialCopula⟩] ∧
    Verb.template.Licensed (E := Verb.Exponent)
      [⟨_, .di⟩, ⟨_, .pastCopula⟩, ⟨_, .person .one (.personNumber .second .singular)⟩] := by
  decide

/-- The negative follows voice and precedes the tense/aspect/modality marker (§8.2.2), and
the copular markers follow that marker (§8.2.3), so the reversed orders are unlicensed. -/
theorem reversed_orders :
    ¬ Verb.template.Licensed (E := Verb.Exponent) [⟨_, .negative⟩, ⟨_, .causative⟩] ∧
    ¬ Verb.template.Licensed (E := Verb.Exponent) [⟨_, .di⟩, ⟨_, .negative⟩] ∧
    ¬ Verb.template.Licensed (E := Verb.Exponent) [⟨_, .pastCopula⟩, ⟨_, .di⟩] := by
  decide

/-- Markers of position 3 cannot co-occur, since the template does not repeat the position
(§8.2.3 (i)). -/
theorem same_position_excluded (m₁ m₂ : Verb.Exponent .tam) :
    ¬ Verb.template.Licensed [⟨_, m₁⟩, ⟨_, m₂⟩] :=
  show [Verb.Slot.tam, .tam] ∉ Verb.template.language by decide

/-! ### Existential sentences (§12.1.1.2) -/

/-- The possessive existential sentences (21), with the adverbial after or before the
possessor, (22), with a past copula and no possessor, and (26): *Ayten-in İstanbul'da iki
arkadaş-ı var* and *İstanbul'da Ayten-in iki arkadaş-ı var* 'Ayten has two friends in
Istanbul', *O gün paramız yoktu* 'We had no money that day' and *Murat'ın yatı var* 'Murat
has a yacht'. -/
theorem possessive_existential :
    Possession.IsPossessive [[a, y, t, e, n]] [realize [i, s, t, a, n, b, u, l] [locative.form]]
        [[i, k, i], [a, r, k, a, d, a, ş]] (.personNumber .third .singular) Possession.var
        [[a, y, t, e, n, i, n], [i, s, t, a, n, b, u, l, d, a], [i, k, i],
          [a, r, k, a, d, a, ş, ı], [v, a, r]] ∧
    Possession.IsPossessive [[a, y, t, e, n]] [realize [i, s, t, a, n, b, u, l] [locative.form]]
        [[i, k, i], [a, r, k, a, d, a, ş]] (.personNumber .third .singular) Possession.var
        [[i, s, t, a, n, b, u, l, d, a], [a, y, t, e, n, i, n], [i, k, i],
          [a, r, k, a, d, a, ş, ı], [v, a, r]] ∧
    Possession.IsPossessive [] [[o], [g, ü, n]] [[p, a, r, a]] (.personNumber .first .plural)
        (Possession.predicate Possession.yok (some pastCopula))
        [[o], [g, ü, n], [p, a, r, a, m, ı, z], [y, o, k, t, u]] ∧
    Possession.IsPossessive [[m, u, r, a, t]] [] [[y, a, t]] (.personNumber .third .singular)
        Possession.var [[m, u, r, a, t, ı, n], [y, a, t, ı], [v, a, r]] := by
  decide

/-- The locative existential sentence (17), *Ben-de bir kitap var* 'I have a book'. -/
theorem locative_existential :
    Possession.locative [[b, e, n]] [[b, i, r], [k, i, t, a, p]] Possession.var =
      [[b, e, n, d, e], [b, i, r], [k, i, t, a, p], [v, a, r]] := by
  decide

/-- The possessive suffix on *araba* in (117) is obligatory (§14.4): *Siz-in araba-nız var*
'You have a car', without the question particle, and no person-number cell gives *Sizin
araba var*. -/
theorem possessive_obligatory :
    Possession.IsPossessive [[s, i, z]] [] [[a, r, a, b, a]] (.personNumber .second .plural)
        Possession.var [[s, i, z, i, n], [a, r, a, b, a, n, ı, z], [v, a, r]] ∧
      ∀ c ∈ Agreement.Bundle.personNumberCells, ¬ Possession.IsPossessive [[s, i, z]] []
        [[a, r, a, b, a]] c Possession.var [[s, i, z, i, n], [a, r, a, b, a], [v, a, r]] :=
  ⟨by decide, fun _ hc h ↦ h.ne_bare (np := []) hc [[s, i, z, i, n]] rfl⟩

end GokselKerslake2005
