module

public import Linglib.Fragments.Turkish.Clause
public import Linglib.Fragments.Turkish.Possession
public import Linglib.Fragments.Turkish.QuestionParticles
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

The suffix order of Chapter 8 is licensing by the templates of the finite verb and the nominal,
the person marker of the verb moving where §8.4 allows and nowhere else.
The grammar's example words are licensed with their stacked voice suffixes, reversed orders are
not, and the rule that markers of one position cannot co-occur (§8.2.3) holds because the
template does not repeat the position.

The question clitic *mI* stands before the first clitic among the markers of a predicate and
after the other markers (§11.1.1.5), as `Turkish.QuestionParticles.mi.insert` places it, so the
grammar's examples are its surface forms, the markers after it attached to it (§6.3 (5)).

The converbs of §8.5.2.2 are those of `Turkish.Converb` on the grammar's verbs, and
*-(y)Ip* and *-(y)ArAk* follow every slot before the position-3 marker and none after it
(§28.2).

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
* `person_mobility`, `person_fixed`: §8.4, the places of a person marker outside the template.
* `mi_precedes_clitics`, `mi_follows`: §11.1.1.5, the position of *mI* among the markers of a
  predicate.
* `converbs`, `doubled_converbs`: the converbs of §8.5.2.2 and -DIkçA.
* `conjunctive_converbs`: §28.2, -(y)Ip and -(y)ArAk in place of the position-3 marker.
* `possessive_existential`, `locative_existential`: §12.1.1.2 (21), (22), (26) and (17).
* `possessive_obligatory`: §14.4 (117), the possessive suffix on the possessee.

## Errata

Among the examples of §11.1.1.5, *Gittiler mı?* should be *Gittiler mi?*, since fronting
harmony gives a front vowel after *gittiler* (§3.2.1), and *Baslasın mı?* should be
*Başlasın mı?*.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
-/

@[expose] public section

namespace GokselKerslake2005

open Turkish Phonology Verb.Exponent Nominal.Exponent QuestionParticles

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

-- §3.2.1
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

-- Chapter 3
theorem last_vowel_decides :
    realize [o, t, o, b, ü, s] [plural.form] =
      [o, t, o, b, ü, s, l, e, r] := by
  decide

-- §3.2
theorem iterated :
    realize [ü, z] [passive.form, di.form, (person .one (.personNumber .second .plural)).form] =
      [ü, z, ü, l, d, ü, n, ü, z] := by
  decide

/-- The `o` of -(I)yor does not harmonize and triggers the person marker in *gör-üyor-um*, and
the converb -(y)ken is invariable in *bak-mış-ken* (§3.4 (vi)). -/
theorem retriggering :
    realize [g, ö, r] [iyor.form, (person .two (.personNumber .first .singular)).form] =
      [g, ö, r, ü, y, o, r, u, m] ∧
    realize [b, a, k] (miş.form :: Converb.ken.form) = [b, a, k, m, ı, ş, k, e, n] := by
  decide

/-- The palatal l of *gol* and *hal* fronts the suffix in *gol-ü* and *hal-im*, while rounding
still comes from the vowel (§3.4 (iv)). -/
theorem palatal_l :
    realize [g, o, l'] [(possessive (.personNumber .third .singular)).form] =
      [g, o, l', ü] ∧
    realize [h, a, l'] [(possessive (.personNumber .first .singular)).form] =
      [h, a, l', i, m] := by
  decide

-- §6.1.2
theorem voicing_of_D :
    realize [k, a, l] [di.form] = [k, a, l, d, ı] ∧
    realize [d, ü, ş] [di.form] = [d, ü, ş, t, ü] := by
  decide

/-- A bracketed vowel appears after a consonant and is lost after a vowel, as in *ev-im* against
*araba-m* (§6.1.3, §8.1.2). -/
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

/-- A bracketed consonant appears after a vowel and is lost after a consonant, as in *masa-ya*
against *sor-acak* (§6.1.3, §8.1.2, §8.1.3). -/
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

/-- A third-person possessive takes a final `n` before a case suffix but not word-finally, as in
*tepe-si-n-de* against *tepe-si* (§6.2 (iib), §8.1.2). -/
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

/-- Bracketed vowels and consonants are the two repairs of hiatus, elision in *araba-m* and
epenthesis in *masa-ya* (§6.1.3). -/
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

/-- Before -(I)yor a stem-final `a` or `e` becomes high and harmonizes, as in *anlıyor*, while a
final high vowel stands (§8.2.3.3). -/
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

-- §8.1, (2)
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

-- §8.1, (1)
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

-- §8.2.3, (11), (12), §8.2.3.3
theorem tam_positions :
    Verb.template.Licensed (E := Verb.Exponent)
      [⟨_, .possibility⟩, ⟨_, .negative⟩, ⟨_, .miş⟩, ⟨_, .dir⟩] ∧
    Verb.template.Licensed (E := Verb.Exponent)
      [⟨_, .abil⟩, ⟨_, .acak⟩, ⟨_, .evidentialCopula⟩] ∧
    Verb.template.Licensed (E := Verb.Exponent)
      [⟨_, .di⟩, ⟨_, .pastCopula⟩, ⟨_, .person .one (.personNumber .second .singular)⟩] := by
  decide

-- §8.2.2, §8.2.3
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

/-- A person marker precedes the copular marker when it is a group-1 marker after -DI, as in
*git-ti-m-di*, *gel-di-niz-se* and *bak-tı-k-tı*, or the third-person plural, as in
*kat-sa-lar-dı*, and the third-person plural may also follow -DIr, as in *gid-iyor-dur-lar*,
beside the orders of the template (§8.3.2, §8.3.3, §8.4). -/
theorem person_mobility : ∀ w ∈ ([
      ([g, i, t], [⟨_, di⟩, ⟨_, person .one (.personNumber .first .singular)⟩, ⟨_, pastCopula⟩],
        "git-ti-m-di"),
      ([g, i, t], [⟨_, di⟩, ⟨_, pastCopula⟩, ⟨_, person .one (.personNumber .first .singular)⟩],
        "git-ti-ydi-m"),
      ([g, e, l], [⟨_, di⟩, ⟨_, person .one (.personNumber .second .plural)⟩,
        ⟨_, conditionalCopula⟩], "gel-di-niz-se"),
      ([g, e, l], [⟨_, di⟩, ⟨_, conditionalCopula⟩,
        ⟨_, person .one (.personNumber .second .plural)⟩], "gel-di-yse-niz"),
      ([b, a, k], [⟨_, di⟩, ⟨_, person .one (.personNumber .first .plural)⟩, ⟨_, pastCopula⟩],
        "bak-tı-k-tı"),
      ([k, a, t], [⟨_, sa⟩, ⟨_, person .one (.personNumber .third .plural)⟩, ⟨_, pastCopula⟩],
        "kat-sa-lar-dı"),
      ([g, i, d], [⟨_, iyor⟩, ⟨_, person .two (.personNumber .third .plural)⟩, ⟨_, dir⟩],
        "gid-iyor-lar-dır"),
      ([g, i, d], [⟨_, iyor⟩, ⟨_, dir⟩, ⟨_, person .two (.personNumber .third .plural)⟩],
        "gid-iyor-dur-lar")] :
      List (List Segment × List (Σ σ, Verb.Exponent σ) × String)),
    Verb.Licensed w.2.1 ∧
      ofSegmented? w.2.2 = some (realize w.1 (Verb.forms w.2.1)) := by
  decide

/-- No other person marker leaves its place, so *gid-iyor-um-du*, *gid-iyor-dur-um* and
*git-se-m-di* are unlicensed (§8.4). -/
theorem person_fixed :
    ¬ Verb.Licensed [⟨_, iyor⟩, ⟨_, person .two (.personNumber .first .singular)⟩,
      ⟨_, pastCopula⟩] ∧
    ¬ Verb.Licensed [⟨_, iyor⟩, ⟨_, dir⟩, ⟨_, person .two (.personNumber .first .singular)⟩] ∧
    ¬ Verb.Licensed [⟨_, sa⟩, ⟨_, person .one (.personNumber .first .singular)⟩,
      ⟨_, pastCopula⟩] := by
  decide

/-! ### The question clitic (§11.1.1.5) -/

/-- *mI* precedes the copular markers, as in *Gitse miydik?*, *Başlamış mıydınız?* and *Burada
mıymış?*, the group-2 person markers but the third-person plural, as in *Gidiyor musun?*,
*İster miyiz?* and *Hazır mısınız?*, and -DIr, as in *Unutmuş mudurlar?*, *Evde midir?* and
*geçmiş miyimdir?*, and the markers after it attach to it, as in *bil-iyor mu-ydu-nuz*
(§6.3 (5)). -/
theorem mi_precedes_clitics : ∀ w ∈ ([
      ([g, i, t], [⟨_, sa⟩, ⟨_, pastCopula⟩, ⟨_, person .one (.personNumber .first .plural)⟩],
        ["gitse", "miydik"]),
      ([b, a, ş, l, a],
        [⟨_, miş⟩, ⟨_, pastCopula⟩, ⟨_, person .one (.personNumber .second .plural)⟩],
        ["başlamış", "mıydınız"]),
      ([b, u, r, a, d, a], [⟨_, evidentialCopula⟩], ["burada", "mıymış"]),
      ([g, i, d], [⟨_, iyor⟩, ⟨_, person .two (.personNumber .second .singular)⟩],
        ["gidiyor", "musun"]),
      ([i, s, t, e], [⟨_, aorist⟩, ⟨_, person .two (.personNumber .first .plural)⟩],
        ["ister", "miyiz"]),
      ([h, a, z, ı, r], [⟨_, person .two (.personNumber .second .plural)⟩], ["hazır", "mısınız"]),
      ([u, n, u, t], [⟨_, miş⟩, ⟨_, dir⟩, ⟨_, person .two (.personNumber .third .plural)⟩],
        ["unutmuş", "mudurlar"]),
      ([e, v, d, e], [⟨_, dir⟩], ["evde", "midir"]),
      ([g, e, ç], [⟨_, miş⟩, ⟨_, person .two (.personNumber .first .singular)⟩, ⟨_, dir⟩],
        ["geçmiş", "miyimdir"]),
      ([b, i, l], [⟨_, iyor⟩, ⟨_, pastCopula⟩, ⟨_, person .one (.personNumber .second .plural)⟩],
        ["biliyor", "muydunuz"])] :
      List (List Segment × List (Σ σ, Verb.Exponent σ) × List String)),
    Verb.Licensed w.2.1 ∧
      (w.2.2.mapM ofString?).map List.flatten = some (realize w.1 (mi.insert w.2.1)) := by
  decide

/-- *mI* follows the group-1 person markers, as in *Gördün mü?*, *Gitsek mi?* and *Yürüdünüz
mü?*, those of group 3, as in *Kalayım mı?* and *Başlasın mı?*, the third-person plural, as in
*Gittiler mi?*, *Uyanırlar mı?* and *Okuldalar mı?*, and a subject complement without markers,
as in *Akıllı mı?* and *Benimki mi?*. -/
theorem mi_follows : ∀ w ∈ ([
      ([g, ö, r], [⟨_, di⟩, ⟨_, person .one (.personNumber .second .singular)⟩], ["gördün", "mü"]),
      ([g, i, t], [⟨_, sa⟩, ⟨_, person .one (.personNumber .first .plural)⟩], ["gitsek", "mi"]),
      ([y, ü, r, ü], [⟨_, di⟩, ⟨_, person .one (.personNumber .second .plural)⟩],
        ["yürüdünüz", "mü"]),
      ([k, a, l], [⟨_, optative⟩, ⟨_, person .three (.personNumber .first .singular)⟩],
        ["kalayım", "mı"]),
      ([b, a, ş, l, a], [⟨_, person .three (.personNumber .third .singular)⟩], ["başlasın", "mı"]),
      ([g, i, t], [⟨_, di⟩, ⟨_, person .one (.personNumber .third .plural)⟩], ["gittiler", "mi"]),
      ([u, y, a, n], [⟨_, aorist⟩, ⟨_, person .two (.personNumber .third .plural)⟩],
        ["uyanırlar", "mı"]),
      ([o, k, u, l, d, a], [⟨_, person .two (.personNumber .third .plural)⟩], ["okuldalar", "mı"]),
      ([a, k, ı, l, l, ı], [], ["akıllı", "mı"]),
      ([b, e, n, i, m, k, i], [], ["benimki", "mi"])] :
      List (List Segment × List (Σ σ, Verb.Exponent σ) × List String)),
    Verb.Licensed w.2.1 ∧
      (w.2.2.mapM ofString?).map List.flatten = some (realize w.1 (mi.insert w.2.1)) := by
  decide

/-! ### Converbs (§8.5.2.2) -/

/-- The converbs on the grammar's verbs: on the stem, as in *koş-up*, *kalk-ma-yınca*,
*yık-ıl-ma-dan* and *koş-tukça*, -(y)ken on a position-3 marker or a nominal, as in
*çalış-ır-ken* and *sokak-ta-y-ken*, and -cAsInA on -mIş and a person marker, as in
*duy-ma-mış-çasına* and *konuş-uyor-muş-um-casına* (§8.5.1.1, §8.5.2.2, §26.2.3 (40),
§26.3.8 (69), (73)). -/
theorem converbs : ∀ w ∈ [("koş-up", [k, o, ş], Converb.ip.form),
      ("gir-ip", [g, i, r], Converb.ip.form),
      ("yüz-ünce", [y, ü, z], Converb.inca.form),
      ("kalk-ma-yınca", [k, a, l, k], negative.form :: Converb.inca.form),
      ("koş-arak", [k, o, ş], Converb.arak.form),
      ("büyü-yerek", [b, ü, y, ü], Converb.arak.form),
      ("çalış-arak", [ç, a, l, ı, ş], Converb.arak.form),
      ("düşün-eli", [d, ü, ş, ü, n], Converb.ali.form),
      ("gel-eli", [g, e, l], Converb.ali.form),
      ("yık-ıl-ma-dan", [y, ı, k], passive.form :: Converb.madan.form),
      ("seyret-me-den", [s, e, y, r, e, t], Converb.madan.form),
      ("koş-tukça", [k, o, ş], Converb.dikca.form),
      ("çalış-ır-ken", [ç, a, l, ı, ş], aorist.form :: Converb.ken.form),
      ("çocuk-ken", [ç, o, c, u, k], Converb.ken.form),
      ("sokak-ta-y-ken", [s, o, k, a, k], locative.form :: Converb.ken.form),
      ("duy-ma-mış-çasına", [d, u, y], negative.form :: miş.form :: Converb.casina.form),
      ("konuş-uyor-muş-um-casına", [k, o, n, u, ş], iyor.form :: evidentialCopula.form ::
        (person .two (.personNumber .first .singular)).form :: Converb.casina.form)],
    ofSegmented? w.1 = some (realize w.2.1 w.2.2) := by
  decide

/-- The converbs on two verbs, as in *baka baka*, *duy-du-m duy-alı* and *ye-r ye-mez*
(§8.5.2.2). -/
theorem doubled_converbs :
    ofString? "baka" = some (realize [b, a, k] DoubledConverb.aA.forms.1) ∧
    ofString? "baka" = some (realize [b, a, k] DoubledConverb.aA.forms.2) ∧
    ofString? "duydum" = some (realize [d, u, y]
      (DoubledConverb.diAli.forms.1 ++ [(person .one (.personNumber .first .singular)).form])) ∧
    ofString? "duyalı" = some (realize [d, u, y] DoubledConverb.diAli.forms.2) ∧
    ofString? "yer" = some (realize [y, e] DoubledConverb.arMaz.forms.1) ∧
    ofString? "yemez" = some (realize [y, e] DoubledConverb.arMaz.forms.2) := by
  decide

/-- -(y)Ip and -(y)ArAk stand in place of the position-3 marker and all the suffixes after it,
so they follow exactly the slots before it (§28.2). -/
theorem conjunctive_converbs :
    ∀ c ∈ [Converb.ip, .arak], ∀ s : Verb.Slot, s ≤ c.follows ↔ s < .tam := by
  decide

/-! ### Existential sentences (§12.1.1.2) -/

/-- The existentials (21), (22) and (26), such as *Murat'ın yatı var* 'Murat has a yacht', are
possessive. -/
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

/-- The possessive suffix on *araba* in (117) is obligatory, so no person-number cell gives *Sizin
araba var* (§14.4). -/
theorem possessive_obligatory :
    Possession.IsPossessive [[s, i, z]] [] [[a, r, a, b, a]] (.personNumber .second .plural)
        Possession.var [[s, i, z, i, n], [a, r, a, b, a, n, ı, z], [v, a, r]] ∧
      ∀ c ∈ Agreement.Bundle.personNumberCells, ¬ Possession.IsPossessive [[s, i, z]] []
        [[a, r, a, b, a]] c Possession.var [[s, i, z, i, n], [a, r, a, b, a], [v, a, r]] :=
  ⟨by decide, fun _ hc h ↦ h.ne_bare (np := []) hc [[s, i, z, i, n]] rfl⟩

end GokselKerslake2005
