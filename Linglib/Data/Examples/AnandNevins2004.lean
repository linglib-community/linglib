module

public import Linglib.Data.Examples.Schema

/-!
# `AnandNevins2004` — typed example data

Auto-generated from `Linglib/Data/Examples/AnandNevins2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AnandNevins2004.Examples`.
-/

@[expose] public section

namespace AnandNevins2004.Examples

def ex_4 : Datum :=
  { id := "anandnevins2004_4"
    source := ⟨"anand-nevins-2004", "(4)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "Hɛseni (mɨ-ra) va kɛ ɛz dɛwletia."
    glossedTokens := [("Hɛseni", "Hesen.OBL"), ("(mɨ-ra)", "(I.OBL-to)"), ("va", "said"), ("kɛ", "that"), ("ɛz", "I"), ("dɛwletia", "rich.be-PRES")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("utterance context", .acceptable), ("reported context", .acceptable)]
    paperFeatures := [("entry", "vano"), ("indexical", "I")] }

def ex_5 : Datum :=
  { id := "anandnevins2004_5"
    source := ⟨"anand-nevins-2004", "(5)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "Hɛseni (Ali-ra) va kɛ tɨ dɛwletia."
    glossedTokens := [("Hɛseni", "Hesen.OBL"), ("(Ali-ra)", "(Ali.OBL-to)"), ("va", "said"), ("kɛ", "that"), ("tɨ", "you"), ("dɛwletia", "rich.be-PRES")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("utterance context", .acceptable), ("reported context", .acceptable)]
    paperFeatures := [("entry", "vano"), ("indexical", "you")] }

def ex_6 : Datum :=
  { id := "anandnevins2004_6"
    source := ⟨"anand-nevins-2004", "(6)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "Waxto kɛ ma D.-de bime, H. mɨ-ra va kɛ o ita ame dina."
    glossedTokens := [("Waxto", "when"), ("kɛ", "that"), ("ma", "we"), ("D.-de", "D.-at"), ("bime", "were"), ("H.", "H.obl"), ("mɨ-ra", "me-at"), ("va", "said"), ("kɛ", "that"), ("o", "he"), ("ita", "here"), ("ame", "came"), ("dina", "world")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("utterance context", .acceptable), ("reported context", .acceptable)]
    paperFeatures := [("entry", "vano"), ("indexical", "here")] }

def ex_7 : Datum :=
  { id := "anandnevins2004_7"
    source := ⟨"anand-nevins-2004", "(7)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "Hefte nayeraraver, H. mɨ-ra va kɛ o vɨzeri Rojda paci kɛrd."
    glossedTokens := [("Hefte", "week"), ("nayeraraver", "ago"), ("H.", "H.obl"), ("mɨ-ra", "me-at"), ("va", "said"), ("kɛ", "that"), ("o", "he"), ("vɨzeri", "yesterday"), ("Rojda", "Rojda"), ("paci", "kiss"), ("kɛrd", "did")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("reported context", .acceptable), ("utterance context", .unacceptable)]
    paperFeatures := [("entry", "vano"), ("indexical", "yesterday"), ("pragmatic_clash", "a report made a week ago cannot concern the utterance's yesterday")] }

def fn3_i : Datum :=
  { id := "anandnevins2004_fn3_i"
    source := ⟨"anand-nevins-2004", "fn. 3 (i)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "Hɛsen teɾmine kɛno kɛ ɛz newɛsha."
    glossedTokens := [("Hɛsen", "Hesen"), ("teɾmine", "believe"), ("kɛno", "does"), ("kɛ", "that"), ("ɛz", "I"), ("newɛsha", "sick.be-PRES")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("utterance context", .acceptable), ("reported context", .unacceptable)]
    paperFeatures := [("entry", "zazaki_attitude"), ("indexical", "I")] }

def ex_8 : Datum :=
  { id := "anandnevins2004_8"
    source := ⟨"anand-nevins-2004", "(8)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "Mɨ kes paci ne kɛrd."
    glossedTokens := [("Mɨ", "I.ERG"), ("kes", "anyone"), ("paci", "kiss"), ("ne", "not"), ("kɛrd", "did")]
    context := ""
    judgment := .acceptable
    alternatives := [("Mɨ kes paci kɛrd.", .ungrammatical)]
    readings := []
    paperFeatures := [("test", "npi"), ("npi", "kes")] }

def ex_9 : Datum :=
  { id := "anandnevins2004_9"
    source := ⟨"anand-nevins-2004", "(9)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "Rojda ne va kɛ mɨ kes paci kɛrd."
    glossedTokens := [("Rojda", "Rojda"), ("ne", "not"), ("va", "said"), ("kɛ", "that"), ("mɨ", "I"), ("kes", "anyone"), ("paci", "kiss"), ("kɛrd", "did")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("reported context", .acceptable)]
    paperFeatures := [("entry", "vano"), ("indexical", "I"), ("test", "npi_licensing")] }

def ex_10 : Datum :=
  { id := "anandnevins2004_10"
    source := ⟨"anand-nevins-2004", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The girl that Hesen said, \"I kissed t.\" is pretty."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "extraction"), ("construction", "direct quotation")] }

def ex_11 : Datum :=
  { id := "anandnevins2004_11"
    source := ⟨"anand-nevins-2004", "(11)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "čɛnɛkɛ kɛ Hɛseni va mɨ paci kɛrda rindɛka."
    glossedTokens := [("čɛnɛkɛ", "girl"), ("kɛ", "that"), ("Hɛseni", "Hesen"), ("va", "said"), ("mɨ", "I"), ("paci", "kiss"), ("kɛrda", "did"), ("rindɛka", "pretty.be-PRES")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("reported context", .acceptable), ("utterance context", .acceptable)]
    paperFeatures := [("entry", "vano"), ("indexical", "I"), ("test", "extraction")] }

def ex_12 : Datum :=
  { id := "anandnevins2004_12"
    source := ⟨"anand-nevins-2004", "(12)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "Piyaa-o kɛ Rojda va kɛ mɨ paci kɛrd Ali biyo."
    glossedTokens := [("Piyaa-o", "Person"), ("kɛ", "that"), ("Rojda", "Rojda"), ("va", "said"), ("kɛ", "that"), ("mɨ", "I"), ("paci", "kiss"), ("kɛrd", "did"), ("Ali", "Ali"), ("biyo", "was")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("reported context", .acceptable), ("utterance context", .acceptable)]
    paperFeatures := [("entry", "vano"), ("indexical", "I"), ("test", "extraction")] }

def ex_13 : Datum :=
  { id := "anandnevins2004_13"
    source := ⟨"anand-nevins-2004", "(13)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "Vɨzeri Rojda Bill-ra va kɛ ɛz to-ra miradiša."
    glossedTokens := [("Vɨzeri", "Yesterday"), ("Rojda", "Rojda"), ("Bill-ra", "Bill-to"), ("va", "said"), ("kɛ", "that"), ("ɛz", "I"), ("to-ra", "you-to"), ("miradiša", "angry.be-PRES")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("both reported", .acceptable), ("both utterance", .acceptable), ("mixed I-utterance you-reported", .unacceptable), ("mixed I-reported you-utterance", .unacceptable)]
    paperFeatures := [("entry", "vano"), ("indexical", "I"), ("indexical", "you"), ("test", "shift_together")] }

def ex_14 : Datum :=
  { id := "anandnevins2004_14"
    source := ⟨"anand-nevins-2004", "(14)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "Hɛsen mɨ-ra va kɛ ɛz nɨka uža ena."
    glossedTokens := [("Hɛsen", "Hesen"), ("mɨ-ra", "me.OBL-to"), ("va", "said"), ("kɛ", "that"), ("ɛz", "I"), ("nɨka", "now"), ("uža", "there"), ("ena", "coming")]
    context := ""
    judgment := .acceptable
    alternatives := [("Hɛsen mɨ-ra va kɛ ɛz nɨka ita ena.", .ungrammatical)]
    readings := []
    paperFeatures := [("entry", "vano"), ("indexical", "now"), ("indexical", "here"), ("test", "shift_together")] }

def ex_15 : Datum :=
  { id := "anandnevins2004_15"
    source := ⟨"anand-nevins-2004", "(15)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "Hɛsen hefti nayeraver ɾeyal kɛno va kɛ ɛz to de hefti naeratepia paci kena."
    glossedTokens := [("Hɛsen", "Hesen"), ("hefti", "week"), ("nayeraver", "ago"), ("ɾeyal", "plan"), ("kɛno", "did"), ("va", "said"), ("kɛ", "that"), ("ɛz", "I"), ("to", "you"), ("de", "two"), ("hefti", "weeks"), ("naeratepia", "after"), ("paci", "kiss"), ("kena", "will-do")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("both reported", .acceptable), ("mixed persons-reported time-utterance", .unacceptable)]
    paperFeatures := [("entry", "vano"), ("indexical", "I"), ("indexical", "you"), ("indexical", "in two weeks"), ("test", "shift_together")] }

def ex_17 : Datum :=
  { id := "anandnevins2004_17"
    source := ⟨"anand-nevins-2004", "(17)"⟩
    reportedIn := none
    language := "slav1253"
    primaryText := "Simon rásereyineht'u hadi."
    glossedTokens := [("Simon", "Simon"), ("rásereyineht'u", "2.sg-hit-1.sg"), ("hadi", "3.sg-say")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("utterance context", .acceptable)]
    paperFeatures := [("entry", "slave_say"), ("indexical", "you")] }

def ex_18 : Datum :=
  { id := "anandnevins2004_18"
    source := ⟨"anand-nevins-2004", "(18)"⟩
    reportedIn := none
    language := "slav1253"
    primaryText := "sehlégé segha gon´ɨhkie rárulu yudeli"
    glossedTokens := [("sehlégé", "1.sg-friend"), ("segha", "1.sg-for"), ("gon´ɨhkie", "slippers"), ("rárulu", "3.sg-will-sew"), ("yudeli", "3.sg-want-4.sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("both reported", .acceptable), ("mixed friend-reported slippers-utterance", .unacceptable), ("mixed friend-utterance slippers-reported", .unacceptable)]
    paperFeatures := [("entry", "slave_want"), ("indexical", "I"), ("indexical", "I"), ("test", "shift_together")] }

def ex_21 : Datum :=
  { id := "anandnevins2004_21"
    source := ⟨"anand-nevins-2004", "(21)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "Hɛsen va kɛ pyaay kɛ mɨ-ra hes kene pyaay kɛ mɨ-ra hes ne kene ame zuja."
    glossedTokens := [("Hɛsen", "Hesen"), ("va", "said"), ("kɛ", "that"), ("pyaay", "people"), ("kɛ", "that"), ("mɨ-ra", "me.OBL"), ("hes", "like"), ("kene", "do"), ("pyaay", "people"), ("kɛ", "that"), ("mɨ-ra", "me.OBL"), ("hes", "like"), ("ne", "NEG"), ("kene", "do"), ("ame", "came"), ("zuja", "together")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("both reported", .acceptable), ("both utterance", .acceptable), ("mixed first-reported second-utterance", .unacceptable), ("mixed first-utterance second-reported", .unacceptable)]
    paperFeatures := [("entry", "vano"), ("indexical", "me"), ("indexical", "me"), ("test", "shift_together"), ("c_command", "no")] }

def ex_32 : Datum :=
  { id := "anandnevins2004_32"
    source := ⟨"anand-nevins-2004", "(32)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "Ali mɨ-ra va kɛ Hɛseni to-ra va ɛz braye Rojda-o."
    glossedTokens := [("Ali", "Ali"), ("mɨ-ra", "me-to"), ("va", "said"), ("kɛ", "that"), ("Hɛseni", "Hesen"), ("to-ra", "you-to"), ("va", "said"), ("ɛz", "I"), ("braye", "brother"), ("Rojda-o", "Rojda-GEN")]
    context := "Andrew, secretly the brother of the traitor Rojda, is confronted by Hesen; Ali overhears, then tells Andrew what Hesen said; Andrew reports Ali's words to his neighbor (31)."
    judgment := .acceptable
    alternatives := []
    readings := [("lowest reported context", .acceptable), ("intermediate reported context", .acceptable), ("utterance context", .unacceptable)]
    paperFeatures := [("entry", "vano"), ("indexical", "I"), ("test", "multiple_embedding"), ("intermediate_shift", "yes")] }

def ex_33 : Datum :=
  { id := "anandnevins2004_33"
    source := ⟨"anand-nevins-2004", "(33)"⟩
    reportedIn := none
    language := "diml1238"
    primaryText := "Ali mɨ-ra va kɛ Hɛseni Fatima-ra va ɛz braye Rojda-o."
    glossedTokens := [("Ali", "Ali"), ("mɨ-ra", "me-to"), ("va", "said"), ("kɛ", "that"), ("Hɛseni", "Hesen"), ("Fatima-ra", "Fatima-to"), ("va", "said"), ("ɛz", "I"), ("braye", "brother"), ("Rojda-o", "Rojda-GEN")]
    context := "As for (32), but Ali overheard Hesen telling Fatima."
    judgment := .acceptable
    alternatives := []
    readings := [("lowest reported context", .acceptable), ("intermediate reported context", .acceptable), ("utterance context", .acceptable)]
    paperFeatures := [("entry", "vano"), ("indexical", "I"), ("test", "multiple_embedding"), ("intermediate_shift", "no")] }

def ex_34a : Datum :=
  { id := "anandnevins2004_34a"
    source := ⟨"anand-nevins-2004", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John told Bill, you should buy it for me, not him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language_type", "non-shifting")] }

def ex_34b : Datum :=
  { id := "anandnevins2004_34b"
    source := ⟨"anand-nevins-2004", "(34b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wanted, you should buy it for me, not him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language_type", "non-shifting")] }

def ex_36 : Datum :=
  { id := "anandnevins2004_36"
    source := ⟨"anand-nevins-2004", "(36)"⟩
    reportedIn := none
    language := "slav1253"
    primaryText := "segha ráwǫd´ɨ sédįdi yįlé"
    glossedTokens := [("segha", "1.sg-for"), ("ráwǫd´ɨ", "2.sg-will-buy"), ("sédįdi", "2.sg-tell-1.sg"), ("yįlé", "PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("both reported", .acceptable)]
    paperFeatures := [("entry", "slave_tell"), ("indexical", "I"), ("indexical", "you")] }

def ex_37a : Datum :=
  { id := "anandnevins2004_37a"
    source := ⟨"anand-nevins-2004", "(37a)"⟩
    reportedIn := none
    language := "slav1253"
    primaryText := "sú leshuyie k'eguhw'e yerinewe"
    glossedTokens := [("sú", "Q"), ("leshuyie", "spoon"), ("k'eguhw'e", "1.sg-will-lick"), ("yerinewe", "2.sg-want")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("utterance context", .acceptable), ("reported context", .unacceptable)]
    paperFeatures := [("entry", "slave_want"), ("indexical", "you")] }

def ex_37b : Datum :=
  { id := "anandnevins2004_37b"
    source := ⟨"anand-nevins-2004", "(37b)"⟩
    reportedIn := none
    language := "slav1253"
    primaryText := "denexare wǫję yenįwe"
    glossedTokens := [("denexare", "sister"), ("wǫję", "2.sg-will-sing"), ("yenįwe", "3.sg-want")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("utterance context", .acceptable), ("reported context", .unacceptable)]
    paperFeatures := [("entry", "slave_want"), ("indexical", "you")] }

def ex_38a : Datum :=
  { id := "anandnevins2004_38a"
    source := ⟨"anand-nevins-2004", "(38a)"⟩
    reportedIn := none
    language := "slav1253"
    primaryText := "John beya ráwoz´ɨe yudeli"
    glossedTokens := [("John", "John"), ("beya", "1.sg-son"), ("ráwoz´ɨe", "3.sg-will-hunt"), ("yudeli", "3.sg-want-4.sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("reported context", .acceptable), ("utterance context", .acceptable)]
    paperFeatures := [("entry", "slave_want"), ("indexical", "I")] }

def ex_38b : Datum :=
  { id := "anandnevins2004_38b"
    source := ⟨"anand-nevins-2004", "(38b)"⟩
    reportedIn := none
    language := "slav1253"
    primaryText := "Simon rásereyineht'u hadi"
    glossedTokens := [("Simon", "Simon"), ("rásereyineht'u", "2.sg-hit-1.sg"), ("hadi", "3.sg-say")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("reported context", .acceptable), ("utterance context", .unacceptable)]
    paperFeatures := [("entry", "slave_say"), ("indexical", "I")] }

def ex_42a : Datum :=
  { id := "anandnevins2004_42a"
    source := ⟨"anand-nevins-2004", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Thinking that she was Mary's mother, John begged of Mary, \"Mary should sing.\""
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "de_te")] }

def ex_42b : Datum :=
  { id := "anandnevins2004_42b"
    source := ⟨"anand-nevins-2004", "(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John begged Mary to sing."
    glossedTokens := []
    context := "John, thinking she was Mary's mother, begged of Mary that Mary should sing."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "de_te")] }

def ex_45 : Datum :=
  { id := "anandnevins2004_45"
    source := ⟨"anand-nevins-2004", "(45)"⟩
    reportedIn := none
    language := "mupu1234"
    primaryText := "wu sat n-an nə gwar ta dar n-jos"
    glossedTokens := [("wu", "3m"), ("sat", "say"), ("n-an", "prep-1sg"), ("nə", "Comp"), ("gwar", "ADDR-LOG"), ("ta", "stop"), ("dar", "stay"), ("n-jos", "Jos")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "context_blocking"), ("logophor", "ADDR-LOG")] }

def ex_46 : Datum :=
  { id := "anandnevins2004_46"
    source := ⟨"anand-nevins-2004", "(46)"⟩
    reportedIn := none
    language := "amha1245"
    primaryText := "alǝttazzǝzǝññ alǝ."
    glossedTokens := [("alǝttazzǝzǝññ", "1st.sg.-FUT-NEG-obey-1st.sg."), ("alǝ", "3rd.sg.m-PAST-say")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("mixed I-reported me-utterance", .unacceptable)]
    paperFeatures := [("test", "shift_together"), ("indexical", "I"), ("indexical", "me")] }

def ex_47 : Datum :=
  { id := "anandnevins2004_47"
    source := ⟨"anand-nevins-2004", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Over the past few years, John has repeatedly told me he would return my money in precisely two days."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("two days after each telling", .acceptable)]
    paperFeatures := [("expression", "in precisely two days")] }

def ex_48 : Datum :=
  { id := "anandnevins2004_48"
    source := ⟨"anand-nevins-2004", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Last Saturday [May 8th], John said that he'd return in precisely eight days."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("May 16th", .acceptable), ("May 23rd", .unacceptable)]
    paperFeatures := [("expression", "in precisely eight days"), ("embedded_tense", "would")] }

def ex_49 : Datum :=
  { id := "anandnevins2004_49"
    source := ⟨"anand-nevins-2004", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Last Saturday [May 8th], John said that he will return in precisely eight days."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("May 16th", .unacceptable), ("May 23rd", .acceptable)]
    paperFeatures := [("expression", "in precisely eight days"), ("embedded_tense", "will")] }

def ex_50 : Datum :=
  { id := "anandnevins2004_50"
    source := ⟨"anand-nevins-2004", "(50)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I met John a week ago. In precisely two days he was sick."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("I met John a week ago. Two days later he was sick.", .acceptable)]
    readings := []
    paperFeatures := [("expression", "in precisely two days"), ("test", "discourse_anaphora")] }

def all : List Datum := [ex_4, ex_5, ex_6, ex_7, fn3_i, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_17, ex_18, ex_21, ex_32, ex_33, ex_34a, ex_34b, ex_36, ex_37a, ex_37b, ex_38a, ex_38b, ex_42a, ex_42b, ex_45, ex_46, ex_47, ex_48, ex_49, ex_50]

end AnandNevins2004.Examples
