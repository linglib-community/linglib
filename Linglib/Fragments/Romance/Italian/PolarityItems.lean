module

public import Linglib.Fragments.Romance.Italian.Indefinites
public import Linglib.Semantics.PolarityItem.Licensing

/-!
# Italian polarity items

Italian gives the negative polarity and free choice uses that English *any* combines to separate
items (Chierchia). The n-words *nessuno* 'no one', *niente* 'nothing' and *neanche* 'not even' take
part in negative concord: after the verb they need *non* or another n-word before it, *Non ho detto
niente a nessuno* 'I haven't said anything to anybody', while before the verb they are negative on
their own, *Nessuno ha telefonato* 'Nobody called' (Chierchia; Maiden and Robustelli). Chierchia
likens them to strong NPIs, restricted to roughly the anti-additive environments, and *nessuno* is
not licensed in the restriction of *ogni* 'every'; but *nessuno* and *niente* also follow *senza*
'without' and colloquially mean 'anybody', 'anything' in questions (Maiden and Robustelli). *Mai*
'never' takes the same two positions, and after the verb it is the weak NPI 'ever' of questions,
superlatives and comparatives; the high-register *alcuno* 'any' is a weak NPI without free choice
uses. *Qualsiasi* and its variant *qualunque* head two free choice constructions, [*qualsiasi* N],
read universally, and [*un* N *qualsiasi*], read existentially, neither of them an NPI (Chierchia).
*Pur con* 'even with' needs its clause negated, and *affatto* 'at all' is an NPI as well (Napoli and
Nespor), nowadays used only in negative sentences (Maiden and Robustelli).

## Implementation notes

*Nessuno*, *niente* and *mai* carry the weak licensor, as the negative words of Spanish and French
do: Maiden and Robustelli attest them in questions, which license only weak items. *Neanche*,
attested only with a negation, carries the anti-additive licensor that Chierchia gives n-words.

## References

* [chierchia-2006]
* [chierchia-2013]
* [maiden-robustelli-2007]
* [napoli-nespor-1976]

## TODO

The licensing theory gives the restriction of a universal anti-additive strength, so it admits
*nessuno* there, against [chierchia-2006]; the judgment belongs with a Chierchia 2006 example
row.
-/

@[expose] public section

namespace Italian.PolarityItems

open PolarityItem

/-! ### N-words -/

/-- *nessuno* 'no one' is the n-word built on *uno* 'one', as in *Gianni non ha telefonato a
nessuno* 'Gianni didn't call anybody', *Nessuno ha telefonato* 'Nobody called', and with a second
negation the double negation reading *Nessuno non ha protestato* 'everybody protested'. It
follows *senza*, *senza incontrare nessuno* 'without meeting anyone', and colloquially means
'anybody' in a question, *C'è nessuno lì dentro?* 'Is there anybody in there?'. -/
def nessuno : PolarityItem :=
  { form := Indefinites.nessuno.form
  , licensor := some .weak
  , licensingContexts := [.negation, .nobody, .withoutClause, .question] }

/-- *niente*, or *nulla*, 'nothing', as in *Non ho detto niente a nessuno* 'I haven't said
anything to anybody', *senza niente che mi aiutasse* 'without anything to help me', and colloquially
*Hai dimenticato niente?* 'Have you forgotten anything?'. -/
def niente : PolarityItem :=
  { form := "niente/nulla"
  , licensor := some .weak
  , licensingContexts := [.negation, .nobody, .withoutClause, .question] }

/-- *neanche* 'not even' has the variants *nemmeno* and *neppure*, as in *Non si comporta bene
neanche a scuola* 'He doesn't behave well even at school', *Neanche a scuola si comporta bene*
'Not even at school does he behave well'. -/
def neanche : PolarityItem :=
  { form := "neanche/nemmeno/neppure"
  , licensor := some .antiAdditive
  , licensingContexts := [.negation, .nobody] }

/-! ### Weak NPIs -/

/-- *mai* 'never, ever' is a weak NPI without free choice uses, as in *Non l'ho mai visto senza
cappello* 'I've never seen him hatless', *Nessuno è mai arrivato puntuale* 'Nobody has ever
arrived on time', *Hai mai letto I promessi sposi?* 'Have you ever read The Betrothed?', *l'uomo
più dolce e più grande che abbia mai incontrato* 'the sweetest and greatest man I have ever
encountered', *Piove più che mai* 'It rains more than ever'. -/
def mai : PolarityItem :=
  { form := "mai"
  , licensor := some .weak
  , licensingContexts :=
      [.negation, .nobody, .question, .superlative, .clausalComparative] }

/-- *alcuno* 'any' is a weak NPI of formal and bureaucratic styles without free choice uses, as in
*Non ho comprato alcun libro* 'I didn't buy any book', *senza aver visto alcuno* 'without having
seen anyone', *Dubito che Gianni abbia comprato alcun libro* 'I doubt that Gianni bought any
book', *Se Gianni avesse comprato alcun libro, ce lo avrebbe detto* 'If Gianni had bought any
book, he would have told us', against *\*Ho comprato alcun libro*. The plural *alcuni* 'some' is
a plain indefinite. -/
def alcuno : PolarityItem :=
  { form := "alcuno"
  , licensor := some .weak
  , licensingContexts := [.negation, .withoutClause, .doubtVerb, .conditionalAntecedent] }

/-- *pur con* 'even with', as in *pur con tutta la fantasia del mondo* 'even with all the fantasy
in the world', which needs the verb of its clause negated, giving *Non puoi immaginarlo, pur con
tutta la fantasia del mondo* against *\*Puoi immaginarlo, …*. Elsewhere *pure* 'also, even' is not
polarity sensitive, *Si è pure offerta di allevare lei il bastardo* 'She even offered to bring the
bastard up herself'. -/
def pur : PolarityItem :=
  { form := "pur con"
  , licensor := some .weak
  , licensingContexts := [.negation] }

/-- *affatto* 'at all', now used only in negative sentences, *Non sono affatto sparito* 'I
haven't disappeared at all'; its non-negative use 'quite', *Affatto bello gli sembrò lo
spettacolo* 'The show seemed quite beautiful to him', is very formal and literary. -/
def affatto : PolarityItem :=
  { form := "affatto"
  , licensor := some .weak
  , licensingContexts := [.negation] }

/-! ### Free choice items -/

/-- *qualsiasi*, or *qualunque*, before the noun is the universal free choice item, as in *Prendi
qualunque dolce* 'take any sweet', *Mangia qualsiasi schifezza* 'He eats any old junk'.
Episodically it needs a modifier, *Ieri ho parlato con qualsiasi filosofo che fosse interessato
a parlarmi* against *??Ieri ho parlato con qualsiasi filosofo*, and under negation an unmodified
one has only the rhetorical 'not just any' reading, *Non leggerò qualunque libro*. -/
def qualsiasi : PolarityItem :=
  { form := "qualsiasi/qualunque"
  , freeChoice := true
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic] }

/-- *un* N *qualsiasi*, or *qualunque*, is the existential free choice item, as in *Prendi un dolce
qualunque* 'take a sweet whatever', *Pensa a un numero qualsiasi* 'Think of any number'. It is
marginal in a plain episodic sentence, *??Ieri ho parlato con un qualsiasi filosofo*, and under
negation it has only the rhetorical reading, *Io non sono un agricoltore qualunque* 'I'm not
just any old farmer'. -/
def unoQualsiasi : PolarityItem :=
  { form := "un N qualsiasi"
  , freeChoice := true
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative] }

/-- The polarity items. -/
def items : List PolarityItem :=
  [nessuno, niente, neanche, mai, alcuno, pur, affatto, qualsiasi, unoQualsiasi]

theorem italian_licensing_sound :
    ∀ e ∈ items, ∀ c ∈ e.licensingContexts, c.licenser.Admits e := by
  decide

end Italian.PolarityItems
