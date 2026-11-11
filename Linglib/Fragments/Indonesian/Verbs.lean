module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Fragments.Indonesian.Phonology

/-!
# Indonesian verbs

This file defines the Indonesian verbs of Beavers and Udayana's study of the middle voice and
five verbs that show the readings of the prefix *ter-* in Sneddon's grammar: the stative,
which has no actor, the accidental and the abilitative, of which a verb may have more than one.

An entry records the segments of the root, whether the root has a middle in *ber-*, and the
readings of its *ter-* form. The prefixed forms are derived by `Indonesian.Phonology`, the
active by the nasal alternation of *meN-* and the forms in *ber-* and *ter-* by the loss of
their *r*.

## References

* [sneddon-1996]
* [beavers-udayana-2022]
-/

@[expose] public section

open Phonology

namespace Indonesian

open ArgumentStructure Indonesian.Phonology

/-! ### Readings of *ter-* -/

/-- The three readings of a verb in *ter-* ([sneddon-1996] pp. 112–119). Some verbs have more
than one, as *terbuka* 'open', which is usually stative and can be accidental or abilitative. -/
inductive TerClass where
  /-- The state that follows an action, as in *tertulis* 'written'. -/
  | stative
  /-- An action that was not intended, as in *terbawa* 'taken by mistake'. -/
  | accidental
  /-- The ability to carry out the action, as in *tidak terbeli* 'cannot be afforded'. -/
  | abilitative
  deriving DecidableEq, Repr

namespace TerClass

/-- A stative *ter-* verb involves no action and so has no actor, and an accidental or
abilitative one can take an agent phrase with *oleh*. -/
def HasAgent (c : TerClass) : Prop := c ≠ .stative

instance : DecidablePred HasAgent := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- An accidental *ter-* verb marks the action as not intended; the other two readings leave
volition open. -/
def IsNonvolitional (c : TerClass) : Prop := c = .accidental

instance : DecidablePred IsNonvolitional := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- An abilitative *ter-* verb keeps the suffix *-kan* or *-i* of its base, as in
*terpecahkan* 'can be solved', which the other two readings drop. -/
def RetainsSuffix (c : TerClass) : Prop := c = .abilitative

instance : DecidablePred RetainsSuffix := fun _ ↦ inferInstanceAs (Decidable (_ = _))

end TerClass

/-! ### Entries -/

/-- An Indonesian verb is the root entry, whose `form` is the spelled root, together with the
segments of the root and its prefixation. -/
structure Verb extends _root_.Verb where
  /-- The segments of the root. -/
  rootSegments : List Segment
  /-- Whether the root has a middle in *ber-*. -/
  ber : Bool := false
  /-- The readings of the *ter-* form, none for a root without one. -/
  terClasses : List TerClass := []
  /-- The nouns that the *ber-* form incorporates. -/
  incorporatedNPs : List String := []
  deriving BEq

namespace Verb

/-- The active form in *meN-*. -/
def meN (v : Verb) : List Segment := Phonology.meN v.rootSegments

/-- The passive form in *di-*. -/
def di (v : Verb) : List Segment := [d, i] ++ v.rootSegments

/-- The middle in *ber-*, for a root that has one. -/
def ber? (v : Verb) : Option (List Segment) :=
  if v.ber then some (Phonology.ber v.rootSegments) else none

/-- The form in *ter-*, for a root that has one. -/
def ter? (v : Verb) : Option (List Segment) :=
  if v.terClasses = [] then none else some (Phonology.ter v.rootSegments)

end Verb

/-! ### Roots with a middle in *ber-* -/

/-- *jual* 'sell', as in *Mobil itu berjual dengan mudah* 'The car sells easily'. Its middle
incorporates a noun, as in *berjual baju* and *berjual diri*. -/
def jual : Verb where
  morphs := [.root "jual"]
  rootSegments := [j, u, a, l]
  valency := .ofFrame ArgumentFrame.np
  ber := true
  incorporatedNPs := ["baju", "diri"]

/-- *masak* 'cook'. -/
def masak : Verb where
  morphs := [.root "masak"]
  rootSegments := [m, a, s, a, k]
  valency := .ofFrame ArgumentFrame.np
  ber := true

/-- *cuci* 'wash', whose middle incorporates body-part nouns and others, as in *bercuci mata*
'wash one's eyes'. -/
def cuci : Verb where
  morphs := [.root "cuci"]
  rootSegments := [c, u, c, i]
  valency := .ofFrame ArgumentFrame.np
  ber := true
  incorporatedNPs := ["mata", "kaki", "muka", "mulut", "rambut", "baju", "ikan", "pisang", "diri"]

/-- *tambat* 'tie, moor', as in *Kapal itu bertambat dengan mudah* 'The boat moors easily'. -/
def tambat : Verb where
  morphs := [.root "tambat"]
  rootSegments := [t, a, m, b, a, t]
  valency := .ofFrame ArgumentFrame.np
  ber := true

/-- *dandan* 'dress', as in *Ali berdandan* 'Ali dressed'. -/
def dandan : Verb where
  morphs := [.root "dandan"]
  rootSegments := [d, a, n, d, a, n]
  valency := .ofFrame ArgumentFrame.np
  ber := true

/-- *cukur* 'shave'. -/
def cukur : Verb where
  morphs := [.root "cukur"]
  rootSegments := [c, u, k, u, r]
  valency := .ofFrame ArgumentFrame.np
  ber := true

/-- *jemur* 'dry in the sun', whose middle *berjemur (diri)* is 'sunbathe'. -/
def jemur : Verb where
  morphs := [.root "jemur"]
  rootSegments := [j, e, m, u, r]
  valency := .ofFrame ArgumentFrame.np
  ber := true
  incorporatedNPs := ["diri"]

/-- *sisir* 'comb'. -/
def sisir : Verb where
  morphs := [.root "sisir"]
  rootSegments := [s, i, s, i, r]
  valency := .ofFrame ArgumentFrame.np
  ber := true

/-! ### Roots with a form in *ter-* -/

/-- *buka* 'open', whose *terbuka* is usually stative, *Pintu terbuka* 'The door is open', and
can be accidental or abilitative ([sneddon-1996] p. 119). -/
def buka : Verb where
  morphs := [.root "buka"]
  rootSegments := [b, u, k, a]
  valency := .ofFrame ArgumentFrame.np
  terClasses := [.stative, .accidental, .abilitative]

/-- *pecah* 'break', as in *Jendela itu terpecah* 'The window broke'. Its middle *berpecah* has
the dispositional or passive reading alone. -/
def pecah : Verb where
  morphs := [.root "pecah"]
  rootSegments := [p, e, c, a, h]
  valency := .ofFrame ArgumentFrame.np
  ber := true
  terClasses := [.stative]

/-- *tulis* 'write', whose stative is *Surat itu tertulis dalam bahasa Inggris* 'That letter is
written in English', beside the passive *ditulis* 'was written'. -/
def tulis : Verb where
  morphs := [.root "tulis"]
  rootSegments := [t, u, l, i, s]
  valency := .ofFrame ArgumentFrame.np
  terClasses := [.stative]

/-- *bawa* 'carry, take', whose *terbawa* is accidental in *Maaf, koran saudara terbawa oleh
saya* 'Sorry, I took your newspaper by mistake' and abilitative in *Apa terbawa oleh kau
paket-paket itu sendiri?* 'Were you able to carry those parcels by yourself?' ([sneddon-1996]
p. 118). -/
def bawa : Verb where
  morphs := [.root "bawa"]
  rootSegments := [b, a, w, a]
  valency := .ofFrame ArgumentFrame.np
  terClasses := [.accidental, .abilitative]

/-- *dengar* 'hear', whose abilitative is *tidak terdengar dari sini* 'cannot be heard from
here'. -/
def dengar : Verb where
  morphs := [.root "dengar"]
  rootSegments := [d, e, ng, a, r]
  valency := .ofFrame ArgumentFrame.np
  terClasses := [.abilitative]

/-- The entries of this file. -/
def verbs : List Verb :=
  [jual, masak, cuci, tambat, dandan, cukur, jemur, sisir, buka, pecah, tulis, bawa, dengar]

/-! ### Derived forms -/

theorem pecah_forms :
    pecah.meN = [m, e, m, e, c, a, h] ∧ pecah.ter? = some [t, e, r, p, e, c, a, h] := by
  decide

theorem tambat_forms :
    tambat.meN = [m, e, n, a, m, b, a, t] ∧
      tambat.ber? = some [b, e, r, t, a, m, b, a, t] := by
  decide

theorem sisir_meN : sisir.meN = [m, e, ny, i, s, i, r] := by decide

theorem masak_meN : masak.meN = [m, e, m, a, s, a, k] := by decide

theorem dengar_forms :
    dengar.meN = [m, e, n, d, e, ng, a, r] ∧ dengar.di = [d, i, d, e, ng, a, r] := by
  decide

theorem meN_suffix :
    ∀ v ∈ verbs, ∀ x ∈ v.rootSegments.head?,
      if x ∈ substituting then v.rootSegments.tail <:+ v.meN ∧ ¬ v.rootSegments <:+ v.meN
      else v.rootSegments <:+ v.meN := by
  decide

end Indonesian
