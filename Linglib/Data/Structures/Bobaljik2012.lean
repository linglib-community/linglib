module

public import Linglib.Data.Structures.Schema

/-!
# `Bobaljik2012`: language samples

Auto-generated from `Linglib/Data/Structures/Bobaljik2012.json` by `scripts/gen_structures.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in
`namespace Bobaljik2012.Structures`.
-/

@[expose] public section

namespace Bobaljik2012.Structures

open Data.Structures

/-- region: The broad geographic region under which the table groups the language (p. 229). -/
inductive Region where
  /-- `Africa`: Africa -/
  | africa
  /-- `Eurasia`: Eurasia -/
  | eurasia
  /-- `E Asia`: East Asia -/
  | eAsia
  /-- `Pacific`: the Pacific -/
  | pacific
  /-- `Americas`: the Americas -/
  | americas
  deriving DecidableEq, Repr

/-- family: The family heading under which Table B.1 groups the language, the book's classification without commitment to it (p. 16). -/
inductive Family where
  /-- `Indo-European`: Indo-European -/
  | indoEuropean
  /-- `Uralic`: Uralic -/
  | uralic
  /-- `Altaic`: Altaic -/
  | altaic
  /-- `Yeniseian`: Yeniseian -/
  | yeniseian
  /-- `Chukotko-Kamchatkan`: Chukotko-Kamchatkan -/
  | chukotkoKamchatkan
  /-- `Kartvelian`: Kartvelian -/
  | kartvelian
  /-- `NW Caucasian`: NW Caucasian -/
  | nwCaucasian
  /-- `Nakh-Dagestanian`: Nakh-Dagestanian -/
  | nakhDagestanian
  /-- `Semitic`: Semitic -/
  | semitic
  deriving DecidableEq, Repr

/-- CMPR TYP: The type of comparative construction the descriptions consulted indicate (pp. 229-230). -/
inductive CmprTyp where
  /-- `EX`: an 'exceed' comparative, with a verb meaning 'exceed' or 'surpass' -/
  | exceed
  /-- `CN`: a conjoined comparative, two conjoined clauses -/
  | conjoined
  /-- `ST`: a standard comparative, monoclausal with a marked standard of comparison -/
  | standard
  /-- `OTH`: none of the three main types -/
  | other
  deriving DecidableEq, Repr

/-- CMPR: The morphological expression of comparison on the adjective (pp. 230-231); a code in parentheses is described as optional. -/
inductive Cmpr where
  /-- `M`: a synthetic comparative, an affix or process on the adjective, for at least some adjectives -/
  | morphological
  /-- `PER`: no regular synthetic comparative; an adverb or other free element marks comparison -/
  | periphrastic
  /-- `ZERO`: no marking of comparison on the adjective -/
  | zero
  deriving DecidableEq, Repr

/-- SPRL: The morphosyntactic expression of the relative superlative (pp. 232-233). -/
inductive Sprl where
  /-- `M`: a synthetic superlative -/
  | morphological
  /-- `PER`: a periphrastic superlative -/
  | periphrastic
  /-- `ABS`: the source indicates only absolute superlatives -/
  | absolute
  /-- `ALL`: the comparative construction with a universal quantifier as the standard -/
  | universal
  /-- `CPR`: no clear morphosyntactic distinction between comparative and superlative -/
  | comparative
  /-- `DEF`: the comparative (or positive) with a marker of definiteness -/
  | definite
  /-- `VERY`: the comparative with an intensifier -/
  | intensified
  /-- `POS`: the positive, the superlative sense from context -/
  | positive
  /-- `NONE`: no fixed superlative construction -/
  | none
  /-- `n/i`: no information available -/
  | noInformation
  /-- `OTH`: see the note at the entry -/
  | other
  /-- `ZERO`: printed only for Zazaki in Table B.1; the legend defines ZERO for CMPR alone, as no marking on the adjective -/
  | zero
  deriving DecidableEq, Repr

/-- SUPPL: Whether there is evidence of suppletion in comparative or superlative formation (p. 233). -/
inductive Suppl where
  /-- `Y`: there is suppletion; YES in the legend and in the Uralic rows of Table B.1 -/
  | yes
  /-- `NO`: there is no suppletion -/
  | no
  /-- `MORE`: suppletion only in 'many/much - more' -/
  | more
  /-- `V`: suppletive verbs may replace an 'exceed' comparative -/
  | verb
  /-- `n/i`: no suppletion is indicated in the available description -/
  | notIndicated
  /-- `?`: printed '?', a mark the legend does not define -/
  | unclear
  deriving DecidableEq, Repr

/-- A row of a sample: a language with its codes for each parameter. -/
structure Row where
  /-- The language. -/
  language : Language
  /-- The codes for region. -/
  region : List (Coded Region)
  /-- The codes for family. -/
  family : List (Coded Family)
  /-- The codes for CMPR TYP. -/
  cmprTyp : List (Coded CmprTyp)
  /-- The codes for CMPR. -/
  cmpr : List (Coded Cmpr)
  /-- The codes for SPRL. -/
  sprl : List (Coded Sprl)
  /-- The codes for SUPPL. -/
  suppl : List (Coded Suppl)
  deriving DecidableEq, Repr

def tamashek : Language :=
  { id := "tamashek", name := "Tamashek", glottocode := some "tama1365" }

def hausa : Language :=
  { id := "hausa", name := "Hausa", glottocode := some "haus1257" }

def lele : Language :=
  { id := "lele", name := "Lele", glottocode := some "lele1276" }

def mina : Language :=
  { id := "mina", name := "Mina", glottocode := some "mina1276" }

def qimant : Language :=
  { id := "qimant", name := "Qimant", glottocode := some "qima1242" }

def somali : Language :=
  { id := "somali", name := "Somali", glottocode := some "soma1255" }

def arabic_std : Language :=
  { id := "arabic_std", name := "Arabic (Standard)", glottocode := some "stan1318" }

def neo_aramaic : Language :=
  { id := "neo_aramaic", name := "Neo-Aramaic", glottocode := none }

def hebrew : Language :=
  { id := "hebrew", name := "Hebrew (Modern)", glottocode := some "hebr1245" }

def khoekhoe_nama : Language :=
  { id := "khoekhoe_nama", name := "Khoekhoe (Nama)", glottocode := some "nama1264" }

def khwe : Language :=
  { id := "khwe", name := "Khwe", glottocode := some "kxoe1243" }

def koromfe : Language :=
  { id := "koromfe", name := "Koromfe", glottocode := some "koro1298" }

def ijo : Language :=
  { id := "ijo", name := "Ịjọ", glottocode := none }

def kana : Language :=
  { id := "kana", name := "Kana", glottocode := some "khan1278" }

def ogbronuagum : Language :=
  { id := "ogbronuagum", name := "Ogbronuagum", glottocode := some "ogbr1243" }

def banda : Language :=
  { id := "banda", name := "Banda", glottocode := none }

def lingala : Language :=
  { id := "lingala", name := "Lingala", glottocode := some "ling1263" }

def nandi : Language :=
  { id := "nandi", name := "Nandi", glottocode := some "nand1266" }

def sotho_northern : Language :=
  { id := "sotho_northern", name := "Sotho (Northern)", glottocode := some "pedi1238" }

def zulu : Language :=
  { id := "zulu", name := "Zulu", glottocode := some "zulu1248" }

def lango : Language :=
  { id := "lango", name := "Lango", glottocode := some "lang1324" }

def mbay : Language :=
  { id := "mbay", name := "Mbay", glottocode := some "mbay1241" }

def koroboro_seno : Language :=
  { id := "koroboro_seno", name := "Koroboro Seno", glottocode := some "koyr1242" }

def kanuri : Language :=
  { id := "kanuri", name := "Kanuri", glottocode := some "cent2050" }

def irish : Language :=
  { id := "irish", name := "Irish", glottocode := some "iris1253" }

def modern_greek : Language :=
  { id := "modern_greek", name := "Modern Greek", glottocode := some "mode1248" }

def kashmiri : Language :=
  { id := "kashmiri", name := "Kashmiri", glottocode := some "kash1277" }

def persian_farsi : Language :=
  { id := "persian_farsi", name := "Persian (Farsi)", glottocode := some "west2369" }

def czech : Language :=
  { id := "czech", name := "Czech", glottocode := some "czec1258" }

def finnish : Language :=
  { id := "finnish", name := "Finnish", glottocode := some "finn1318" }

def udmurt : Language :=
  { id := "udmurt", name := "Udmurt", glottocode := some "udmu1245" }

def nenets : Language :=
  { id := "nenets", name := "Nenets (Yurak)", glottocode := none }

def ket : Language :=
  { id := "ket", name := "Ket", glottocode := some "kett1243" }

def even : Language :=
  { id := "even", name := "Even", glottocode := some "even1260" }

def evenki : Language :=
  { id := "evenki", name := "Evenki", glottocode := some "even1259" }

def khalkha : Language :=
  { id := "khalkha", name := "Khalkha", glottocode := some "halh1238" }

def lezgian : Language :=
  { id := "lezgian", name := "Lezgian", glottocode := some "lezg1247" }

def hunzib : Language :=
  { id := "hunzib", name := "Hunzib", glottocode := some "hunz1247" }

def abkhaz : Language :=
  { id := "abkhaz", name := "Abkhaz", glottocode := some "abkh1244" }

def bashkir : Language :=
  { id := "bashkir", name := "Bashkir", glottocode := some "bash1264" }

def khakas : Language :=
  { id := "khakas", name := "Khakas", glottocode := some "khak1248" }

def tyvan : Language :=
  { id := "tyvan", name := "Tyvan", glottocode := some "tuvi1240" }

def itelmen : Language :=
  { id := "itelmen", name := "Itelmen", glottocode := some "itel1242" }

def chukchi : Language :=
  { id := "chukchi", name := "Chukchi", glottocode := some "chuk1273" }

def malayalam : Language :=
  { id := "malayalam", name := "Malayalam", glottocode := some "mala1464" }

def ainu : Language :=
  { id := "ainu", name := "Ainu", glottocode := some "ainu1240" }

def nivkh : Language :=
  { id := "nivkh", name := "Nivkh", glottocode := some "gily1242" }

def burushaski : Language :=
  { id := "burushaski", name := "Burushaski", glottocode := some "buru1296" }

def yukagir : Language :=
  { id := "yukagir", name := "Yukagir", glottocode := some "sout2750" }

def basque : Language :=
  { id := "basque", name := "Basque", glottocode := some "basq1248" }

def asl : Language :=
  { id := "asl", name := "ASL", glottocode := some "amer1248" }

def cantonese : Language :=
  { id := "cantonese", name := "Cantonese", glottocode := some "cant1236" }

def kunming : Language :=
  { id := "kunming", name := "Kunming", glottocode := some "kunm1234" }

def mandarin : Language :=
  { id := "mandarin", name := "Mandarin", glottocode := some "mand1415" }

def dzongkha : Language :=
  { id := "dzongkha", name := "Dzongkha", glottocode := some "dzon1239" }

def kham : Language :=
  { id := "kham", name := "Kham", glottocode := none }

def limbu : Language :=
  { id := "limbu", name := "Limbu", glottocode := some "limb1266" }

def newar_dolokha : Language :=
  { id := "newar_dolokha", name := "Newar (Dolokha)", glottocode := some "dola1240" }

def bisu : Language :=
  { id := "bisu", name := "Bisu", glottocode := some "bisu1244" }

def mongsen_ao : Language :=
  { id := "mongsen_ao", name := "Mongsen Ao", glottocode := some "mong1332" }

def mizo : Language :=
  { id := "mizo", name := "Mizo", glottocode := some "lush1249" }

def dumi : Language :=
  { id := "dumi", name := "Dumi", glottocode := some "dumi1241" }

def lao : Language :=
  { id := "lao", name := "Lao", glottocode := some "laoo1244" }

def thai : Language :=
  { id := "thai", name := "Thai", glottocode := some "thai1261" }

def japanese : Language :=
  { id := "japanese", name := "Japanese", glottocode := some "nucl1643" }

def korean : Language :=
  { id := "korean", name := "Korean", glottocode := some "kore1280" }

def mayali : Language :=
  { id := "mayali", name := "Mayali", glottocode := some "gunw1252" }

def nunggubuyu : Language :=
  { id := "nunggubuyu", name := "Nunggubuyu", glottocode := some "nung1290" }

def arrernte : Language :=
  { id := "arrernte", name := "Arrernte", glottocode := none }

def dyirbal : Language :=
  { id := "dyirbal", name := "Dyirbal", glottocode := some "dyir1250" }

def gumbaynggir : Language :=
  { id := "gumbaynggir", name := "Gumbaynggir", glottocode := some "kumb1268" }

def warlpiri : Language :=
  { id := "warlpiri", name := "Warlpiri", glottocode := some "warl1254" }

def yindjibarndi : Language :=
  { id := "yindjibarndi", name := "Yindjibarndi", glottocode := some "yind1247" }

def kayardild : Language :=
  { id := "kayardild", name := "Kayardild", glottocode := some "kaya1319" }

def jingulu : Language :=
  { id := "jingulu", name := "Jingulu", glottocode := some "djin1251" }

def amis : Language :=
  { id := "amis", name := "Amis", glottocode := some "amis1246" }

def paiwan : Language :=
  { id := "paiwan", name := "Paiwan", glottocode := some "paiw1248" }

def puyuma : Language :=
  { id := "puyuma", name := "Puyuma", glottocode := some "puyu1239" }

def rukai : Language :=
  { id := "rukai", name := "Rukai", glottocode := some "ruka1240" }

def seediq : Language :=
  { id := "seediq", name := "Seediq", glottocode := some "taro1264" }

def rapanui : Language :=
  { id := "rapanui", name := "Rapanui", glottocode := some "rapa1244" }

def maori : Language :=
  { id := "maori", name := "Maori", glottocode := some "maor1246" }

def muna : Language :=
  { id := "muna", name := "Muna", glottocode := some "muna1247" }

def pendau : Language :=
  { id := "pendau", name := "Pendau", glottocode := some "pend1242" }

def yapese : Language :=
  { id := "yapese", name := "Yapese", glottocode := some "yape1248" }

def palauan : Language :=
  { id := "palauan", name := "Palauan", glottocode := some "pala1344" }

def fijian_boumaa : Language :=
  { id := "fijian_boumaa", name := "Fijian (Boumaa)", glottocode := some "fiji1243" }

def tuvaluan : Language :=
  { id := "tuvaluan", name := "Tuvaluan", glottocode := some "tuva1244" }

def manam : Language :=
  { id := "manam", name := "Manam", glottocode := some "mana1295" }

def sinaugoro : Language :=
  { id := "sinaugoro", name := "Sinaugoro", glottocode := some "sina1266" }

def amele : Language :=
  { id := "amele", name := "Amele", glottocode := some "amel1241" }

def klon : Language :=
  { id := "klon", name := "Klon", glottocode := some "kelo1247" }

def teiwa : Language :=
  { id := "teiwa", name := "Teiwa", glottocode := some "teiw1235" }

def mian : Language :=
  { id := "mian", name := "Mian", glottocode := some "mian1256" }

def ekagi : Language :=
  { id := "ekagi", name := "Ekagi", glottocode := some "ekar1243" }

def koiari : Language :=
  { id := "koiari", name := "Koiari", glottocode := some "gras1249" }

def mauwake : Language :=
  { id := "mauwake", name := "Mauwake", glottocode := some "mauw1238" }

def arapesh : Language :=
  { id := "arapesh", name := "Arapesh", glottocode := none }

def skou : Language :=
  { id := "skou", name := "Skou", glottocode := some "nucl1634" }

def mundari : Language :=
  { id := "mundari", name := "Mundari", glottocode := some "mund1320" }

def santali : Language :=
  { id := "santali", name := "Santali", glottocode := some "sant1410" }

def remo : Language :=
  { id := "remo", name := "Remo", glottocode := some "bond1245" }

def semalai : Language :=
  { id := "semalai", name := "Semalai", glottocode := some "seme1247" }

def palaung : Language :=
  { id := "palaung", name := "Palaung", glottocode := none }

def vietnamese : Language :=
  { id := "vietnamese", name := "Vietnamese", glottocode := some "viet1252" }

def khmer : Language :=
  { id := "khmer", name := "Khmer", glottocode := some "cent1989" }

def sapuan : Language :=
  { id := "sapuan", name := "Sapuan", glottocode := some "sapu1248" }

def aleut : Language :=
  { id := "aleut", name := "Aleut", glottocode := some "aleu1260" }

def west_greenlandic : Language :=
  { id := "west_greenlandic", name := "West Greenlandic", glottocode := some "kala1399" }

def straits_salish : Language :=
  { id := "straits_salish", name := "Straits Salish", glottocode := some "stra1244" }

def navajo : Language :=
  { id := "navajo", name := "Navajo", glottocode := some "nava1243" }

def nishnaabemwin : Language :=
  { id := "nishnaabemwin", name := "Nishnaabemwin", glottocode := none }

def cherokee : Language :=
  { id := "cherokee", name := "Cherokee", glottocode := some "cher1273" }

def kiowa : Language :=
  { id := "kiowa", name := "Kiowa", glottocode := some "kiow1266" }

def chimariko : Language :=
  { id := "chimariko", name := "Chimariko", glottocode := some "chim1301" }

def kiliwa : Language :=
  { id := "kiliwa", name := "Kiliwa", glottocode := some "kili1268" }

def choctaw : Language :=
  { id := "choctaw", name := "Choctaw", glottocode := some "choc1276" }

def crow : Language :=
  { id := "crow", name := "Crow", glottocode := some "crow1244" }

def wappo : Language :=
  { id := "wappo", name := "Wappo", glottocode := some "wapp1239" }

def nahuatl : Language :=
  { id := "nahuatl", name := "Nahuatl", glottocode := some "clas1250" }

def comanche : Language :=
  { id := "comanche", name := "Comanche", glottocode := some "coma1245" }

def tumpisa_shoshone : Language :=
  { id := "tumpisa_shoshone", name := "Tümpisa Shoshone", glottocode := some "pana1305" }

def cupeno : Language :=
  { id := "cupeno", name := "Cupeño", glottocode := some "cupe1243" }

def sonora_yaqui : Language :=
  { id := "sonora_yaqui", name := "Sonora Yaqui", glottocode := some "yaqu1251" }

def tohono_oodham : Language :=
  { id := "tohono_oodham", name := "Tohono O’odham", glottocode := some "toho1245" }

def tarascan : Language :=
  { id := "tarascan", name := "Tarascan", glottocode := some "pure1242" }

def totonac : Language :=
  { id := "totonac", name := "Totonac", glottocode := some "yecu1235" }

def miskitu : Language :=
  { id := "miskitu", name := "Miskitu", glottocode := some "misk1235" }

def mixtec : Language :=
  { id := "mixtec", name := "Mixtec", glottocode := some "sanm1296" }

def wari : Language :=
  { id := "wari", name := "Wari’", glottocode := some "wari1268" }

def yagua : Language :=
  { id := "yagua", name := "Yagua", glottocode := some "yagu1244" }

def bare : Language :=
  { id := "bare", name := "Bare", glottocode := some "bare1276" }

def tariana : Language :=
  { id := "tariana", name := "Tariana", glottocode := some "tari1256" }

def warekena : Language :=
  { id := "warekena", name := "Warekena", glottocode := none }

def paumari : Language :=
  { id := "paumari", name := "Paumarí", glottocode := some "paum1247" }

def apalai : Language :=
  { id := "apalai", name := "Apalai", glottocode := some "apal1257" }

def hixkaryana : Language :=
  { id := "hixkaryana", name := "Hixkaryana", glottocode := some "hixk1239" }

def bororo : Language :=
  { id := "bororo", name := "Bororo", glottocode := some "boro1282" }

def kayapo : Language :=
  { id := "kayapo", name := "Kayapó", glottocode := some "kaya1330" }

def piraha : Language :=
  { id := "piraha", name := "Pirahã", glottocode := some "pira1253" }

def mbya_guarani : Language :=
  { id := "mbya_guarani", name := "Mbyá (Guaraní)", glottocode := some "mbya1239" }

def urubu_kaapor : Language :=
  { id := "urubu_kaapor", name := "Urubu-Kaapor", glottocode := some "urub1250" }

def andoke : Language :=
  { id := "andoke", name := "Andoke", glottocode := some "ando1256" }

def aymara : Language :=
  { id := "aymara", name := "Aymara", glottocode := none }

def mapuche : Language :=
  { id := "mapuche", name := "Mapuche", glottocode := some "mapu1245" }

def moseten : Language :=
  { id := "moseten", name := "Mosetén", glottocode := some "mose1249" }

def urarina : Language :=
  { id := "urarina", name := "Urarina", glottocode := some "urar1246" }

def kwaza : Language :=
  { id := "kwaza", name := "Kwaza", glottocode := some "kwaz1243" }

def albanian : Language :=
  { id := "albanian", name := "Albanian", glottocode := none }

def hittite : Language :=
  { id := "hittite", name := "Hittite", glottocode := some "hitt1242" }

def tocharian : Language :=
  { id := "tocharian", name := "Tocharian", glottocode := none }

def armenian_classical : Language :=
  { id := "armenian_classical", name := "Armenian (Classical)", glottocode := some "clas1256" }

def armenian_middle : Language :=
  { id := "armenian_middle", name := "Armenian (Middle)", glottocode := some "midd1364" }

def armenian_western : Language :=
  { id := "armenian_western", name := "Armenian (Western)", glottocode := some "homs1234" }

def armenian_eastern : Language :=
  { id := "armenian_eastern", name := "Armenian (Eastern)", glottocode := some "nucl1235" }

def latvian : Language :=
  { id := "latvian", name := "Latvian", glottocode := some "latv1249" }

def lithuanian : Language :=
  { id := "lithuanian", name := "Lithuanian", glottocode := some "lith1251" }

def old_church_slavonic : Language :=
  { id := "old_church_slavonic", name := "Old Church Slavonic", glottocode := some "chur1257" }

def belorussian : Language :=
  { id := "belorussian", name := "Belorussian", glottocode := some "bela1254" }

def bulgarian : Language :=
  { id := "bulgarian", name := "Bulgarian", glottocode := some "bulg1262" }

def macedonian : Language :=
  { id := "macedonian", name := "Macedonian", glottocode := some "mace1250" }

def polish : Language :=
  { id := "polish", name := "Polish", glottocode := some "poli1260" }

def russian : Language :=
  { id := "russian", name := "Russian", glottocode := some "russ1263" }

def serbian_croatian : Language :=
  { id := "serbian_croatian", name := "Serbian/Croatian", glottocode := some "sout1528" }

def slovak : Language :=
  { id := "slovak", name := "Slovak", glottocode := some "slov1269" }

def slovenian : Language :=
  { id := "slovenian", name := "Slovenian", glottocode := some "slov1268" }

def sorbian : Language :=
  { id := "sorbian", name := "Sorbian", glottocode := none }

def ukrainian : Language :=
  { id := "ukrainian", name := "Ukrainian", glottocode := some "ukra1253" }

def old_irish : Language :=
  { id := "old_irish", name := "Old Irish", glottocode := some "oldi1246" }

def breton : Language :=
  { id := "breton", name := "Breton", glottocode := some "bret1244" }

def manx : Language :=
  { id := "manx", name := "Manx", glottocode := some "manx1243" }

def scottish_gaelic : Language :=
  { id := "scottish_gaelic", name := "Scottish Gaelic", glottocode := some "scot1245" }

def welsh : Language :=
  { id := "welsh", name := "Welsh", glottocode := some "wels1247" }

def latin : Language :=
  { id := "latin", name := "Latin", glottocode := some "lati1261" }

def catalan : Language :=
  { id := "catalan", name := "Catalan", glottocode := some "stan1289" }

def french_old : Language :=
  { id := "french_old", name := "French (Old)", glottocode := some "oldf1239" }

def french_modern : Language :=
  { id := "french_modern", name := "French (Modern)", glottocode := some "stan1290" }

def italian : Language :=
  { id := "italian", name := "Italian", glottocode := some "ital1282" }

def portuguese : Language :=
  { id := "portuguese", name := "Portuguese", glottocode := some "port1283" }

def romanian : Language :=
  { id := "romanian", name := "Romanian", glottocode := some "roma1327" }

def spanish : Language :=
  { id := "spanish", name := "Spanish", glottocode := some "stan1288" }

def gothic : Language :=
  { id := "gothic", name := "Gothic", glottocode := some "goth1244" }

def english_old : Language :=
  { id := "english_old", name := "English (Old)", glottocode := some "olde1238" }

def icelandic_old : Language :=
  { id := "icelandic_old", name := "Icelandic (Old)", glottocode := some "oldn1244" }

def afrikaans : Language :=
  { id := "afrikaans", name := "Afrikaans", glottocode := some "afri1274" }

def danish : Language :=
  { id := "danish", name := "Danish", glottocode := some "dani1285" }

def dutch : Language :=
  { id := "dutch", name := "Dutch", glottocode := some "dutc1256" }

def english_modern : Language :=
  { id := "english_modern", name := "English (Modern)", glottocode := some "stan1293" }

def faroese : Language :=
  { id := "faroese", name := "Faroese", glottocode := some "faro1244" }

def frisian : Language :=
  { id := "frisian", name := "Frisian", glottocode := some "west2354" }

def german : Language :=
  { id := "german", name := "German", glottocode := some "stan1295" }

def german_cimbrian : Language :=
  { id := "german_cimbrian", name := "German (Cimbrian)", glottocode := some "tred1238" }

def icelandic_modern : Language :=
  { id := "icelandic_modern", name := "Icelandic (Modern)", glottocode := some "icel1247" }

def norwegian : Language :=
  { id := "norwegian", name := "Norwegian", glottocode := some "norw1258" }

def swedish : Language :=
  { id := "swedish", name := "Swedish", glottocode := some "swed1254" }

def yiddish : Language :=
  { id := "yiddish", name := "Yiddish", glottocode := some "east2295" }

def greek_ancient : Language :=
  { id := "greek_ancient", name := "Greek (Ancient)", glottocode := some "anci1242" }

def greek_modern : Language :=
  { id := "greek_modern", name := "Greek (Modern)", glottocode := some "mode1248" }

def sanskrit : Language :=
  { id := "sanskrit", name := "Sanskrit", glottocode := some "sans1269" }

def bagri : Language :=
  { id := "bagri", name := "Bagri", glottocode := some "bagr1243" }

def hindi : Language :=
  { id := "hindi", name := "Hindi", glottocode := some "hind1269" }

def marathi : Language :=
  { id := "marathi", name := "Marathi", glottocode := some "mara1378" }

def nepali : Language :=
  { id := "nepali", name := "Nepali", glottocode := some "nepa1254" }

def sinhalese : Language :=
  { id := "sinhalese", name := "Sinhalese", glottocode := some "sinh1246" }

def romani : Language :=
  { id := "romani", name := "Romani", glottocode := none }

def romani_vlax : Language :=
  { id := "romani_vlax", name := "Romani (Vlax)", glottocode := some "vlax1238" }

def persian_old : Language :=
  { id := "persian_old", name := "Persian (Old)", glottocode := some "oldp1254" }

def persian_middle : Language :=
  { id := "persian_middle", name := "Persian (Middle)", glottocode := some "pahl1241" }

def sogdian : Language :=
  { id := "sogdian", name := "Sogdian", glottocode := some "sogd1245" }

def khotanese_gyazdian : Language :=
  { id := "khotanese_gyazdian", name := "Khotanese (Gyāźdian)", glottocode := some "khot1251" }

def balochi : Language :=
  { id := "balochi", name := "Balochi", glottocode := none }

def gilyan : Language :=
  { id := "gilyan", name := "Gilyan", glottocode := some "gila1241" }

def kurdish_kurmanji : Language :=
  { id := "kurdish_kurmanji", name := "Kurdish (Kurmanji)", glottocode := some "nort2641" }

def kurdish_sorani : Language :=
  { id := "kurdish_sorani", name := "Kurdish (Sorani)", glottocode := some "cent1972" }

def ossetian : Language :=
  { id := "ossetian", name := "Ossetian", glottocode := none }

def pashto : Language :=
  { id := "pashto", name := "Pashto", glottocode := none }

def shughni_rushan : Language :=
  { id := "shughni_rushan", name := "Shughni-Rushan", glottocode := some "shug1248" }

def tajik : Language :=
  { id := "tajik", name := "Tajik", glottocode := some "taji1245" }

def talysh : Language :=
  { id := "talysh", name := "Talysh", glottocode := some "taly1247" }

def tat : Language :=
  { id := "tat", name := "Tat", glottocode := none }

def wakhi : Language :=
  { id := "wakhi", name := "Wakhi", glottocode := some "wakh1245" }

def yagnobi : Language :=
  { id := "yagnobi", name := "Yagnobi", glottocode := some "yagn1238" }

def zazaki : Language :=
  { id := "zazaki", name := "Zazaki", glottocode := none }

def estonian : Language :=
  { id := "estonian", name := "Estonian", glottocode := some "esto1258" }

def ingrian : Language :=
  { id := "ingrian", name := "Ingrian", glottocode := some "ingr1248" }

def karelian : Language :=
  { id := "karelian", name := "Karelian", glottocode := some "kare1335" }

def livonian : Language :=
  { id := "livonian", name := "Livonian", glottocode := some "livv1244" }

def lude : Language :=
  { id := "lude", name := "Lude", glottocode := some "ludi1246" }

def veps : Language :=
  { id := "veps", name := "Veps", glottocode := some "veps1250" }

def votic : Language :=
  { id := "votic", name := "Votic", glottocode := some "voti1245" }

def saami_north : Language :=
  { id := "saami_north", name := "Saami (North)", glottocode := some "nort2671" }

def saami_south : Language :=
  { id := "saami_south", name := "Saami (South)", glottocode := some "sout2674" }

def saami_kildin : Language :=
  { id := "saami_kildin", name := "Saami (Kildin)", glottocode := some "kild1236" }

def hungarian : Language :=
  { id := "hungarian", name := "Hungarian", glottocode := some "hung1274" }

def khanty_ostyak : Language :=
  { id := "khanty_ostyak", name := "Khanty (Ostyak)", glottocode := none }

def mansi_vogul : Language :=
  { id := "mansi_vogul", name := "Mansi (Vogul)", glottocode := none }

def mari_cheremis : Language :=
  { id := "mari_cheremis", name := "Mari (Cheremis)", glottocode := none }

def mordva : Language :=
  { id := "mordva", name := "Mordva", glottocode := none }

def komi : Language :=
  { id := "komi", name := "Komi", glottocode := none }

def nganasan_tavgy : Language :=
  { id := "nganasan_tavgy", name := "Nganasan (Tavgy)", glottocode := some "ngan1291" }

def selkup : Language :=
  { id := "selkup", name := "Selkup", glottocode := some "selk1253" }

def manchu : Language :=
  { id := "manchu", name := "Manchu", glottocode := some "manc1252" }

def nanai : Language :=
  { id := "nanai", name := "Nanai", glottocode := some "nana1257" }

def negidal : Language :=
  { id := "negidal", name := "Negidal", glottocode := some "negi1245" }

def orochi : Language :=
  { id := "orochi", name := "Orochi", glottocode := some "oroc1248" }

def orok : Language :=
  { id := "orok", name := "Orok", glottocode := some "orok1265" }

def ulch : Language :=
  { id := "ulch", name := "Ulch", glottocode := some "ulch1241" }

def azeri : Language :=
  { id := "azeri", name := "Azeri", glottocode := some "nort2697" }

def chuvash : Language :=
  { id := "chuvash", name := "Chuvash", glottocode := some "chuv1255" }

def gagauz : Language :=
  { id := "gagauz", name := "Gagauz", glottocode := some "gaga1249" }

def karachay_balkar : Language :=
  { id := "karachay_balkar", name := "Karachay-Balkar", glottocode := some "kara1465" }

def karaim : Language :=
  { id := "karaim", name := "Karaim", glottocode := some "kara1464" }

def kazakh : Language :=
  { id := "kazakh", name := "Kazakh", glottocode := some "kaza1248" }

def kirghiz : Language :=
  { id := "kirghiz", name := "Kirghiz", glottocode := some "kirg1245" }

def kumyk : Language :=
  { id := "kumyk", name := "Kumyk", glottocode := some "kumy1244" }

def nogai : Language :=
  { id := "nogai", name := "Nogai", glottocode := some "noga1249" }

def shor : Language :=
  { id := "shor", name := "Shor", glottocode := some "shor1247" }

def tatar : Language :=
  { id := "tatar", name := "Tatar", glottocode := some "tata1255" }

def turkish : Language :=
  { id := "turkish", name := "Turkish", glottocode := some "nucl1301" }

def turkic_old : Language :=
  { id := "turkic_old", name := "Turkic (Old)", glottocode := some "oldu1238" }

def turkmen : Language :=
  { id := "turkmen", name := "Turkmen", glottocode := some "turk1304" }

def uyghur : Language :=
  { id := "uyghur", name := "Uyghur", glottocode := some "uigh1240" }

def uzbek : Language :=
  { id := "uzbek", name := "Uzbek", glottocode := some "nort2690" }

def bonan : Language :=
  { id := "bonan", name := "Bonan", glottocode := some "bona1250" }

def buryat : Language :=
  { id := "buryat", name := "Buryat", glottocode := some "russ1264" }

def dagur : Language :=
  { id := "dagur", name := "Dagur", glottocode := some "daur1238" }

def kalmyk : Language :=
  { id := "kalmyk", name := "Kalmyk", glottocode := some "kalm1244" }

def moghol : Language :=
  { id := "moghol", name := "Moghol", glottocode := some "mogh1245" }

def mongghul : Language :=
  { id := "mongghul", name := "Mongghul", glottocode := some "huzh1238" }

def oirat : Language :=
  { id := "oirat", name := "Oirat", glottocode := some "kalm1243" }

def ordos : Language :=
  { id := "ordos", name := "Ordos", glottocode := some "ordo1245" }

def santa : Language :=
  { id := "santa", name := "Santa", glottocode := some "dong1285" }

def shira_yughur : Language :=
  { id := "shira_yughur", name := "Shira Yughur", glottocode := some "east2337" }

def kott : Language :=
  { id := "kott", name := "Kott", glottocode := some "kott1240" }

def yugh : Language :=
  { id := "yugh", name := "Yugh", glottocode := some "yugh1239" }

def alutor : Language :=
  { id := "alutor", name := "Alutor", glottocode := some "alut1245" }

def kerek : Language :=
  { id := "kerek", name := "Kerek", glottocode := some "kere1280" }

def koryak : Language :=
  { id := "koryak", name := "Koryak", glottocode := some "kory1246" }

def georgian : Language :=
  { id := "georgian", name := "Georgian", glottocode := some "nucl1302" }

def mingrelian : Language :=
  { id := "mingrelian", name := "Mingrelian", glottocode := some "ming1252" }

def laz_chan : Language :=
  { id := "laz_chan", name := "Laz (Chan)", glottocode := some "lazz1240" }

def svan : Language :=
  { id := "svan", name := "Svan", glottocode := some "svan1243" }

def abaza : Language :=
  { id := "abaza", name := "Abaza", glottocode := some "abaz1241" }

def adyghe : Language :=
  { id := "adyghe", name := "Adyghe", glottocode := some "adyg1241" }

def kabardian : Language :=
  { id := "kabardian", name := "Kabardian", glottocode := some "kaba1278" }

def ubykh : Language :=
  { id := "ubykh", name := "Ubykh", glottocode := some "ubyk1235" }

def chechen : Language :=
  { id := "chechen", name := "Chechen", glottocode := some "chec1245" }

def ingush : Language :=
  { id := "ingush", name := "Ingush", glottocode := some "ingu1240" }

def batsbi : Language :=
  { id := "batsbi", name := "Batsbi", glottocode := some "bats1242" }

def avar : Language :=
  { id := "avar", name := "Avar", glottocode := some "avar1256" }

def andi : Language :=
  { id := "andi", name := "Andi", glottocode := some "andi1255" }

def botlikh : Language :=
  { id := "botlikh", name := "Botlikh", glottocode := some "botl1242" }

def bagvalal : Language :=
  { id := "bagvalal", name := "Bagvalal", glottocode := some "bagv1239" }

def tsez : Language :=
  { id := "tsez", name := "Tsez", glottocode := some "dido1241" }

def tabasaran : Language :=
  { id := "tabasaran", name := "Tabasaran", glottocode := some "taba1259" }

def amharic : Language :=
  { id := "amharic", name := "Amharic", glottocode := some "amha1245" }

def arabic_gulf : Language :=
  { id := "arabic_gulf", name := "Arabic (Gulf)", glottocode := some "gulf1241" }

def arabic_moroccan : Language :=
  { id := "arabic_moroccan", name := "Arabic (Moroccan)", glottocode := some "moro1292" }

def assyrian_neo_aramaic : Language :=
  { id := "assyrian_neo_aramaic", name := "Assyrian Neo-Aramaic", glottocode := some "assy1241" }

def hebrew_biblical : Language :=
  { id := "hebrew_biblical", name := "Hebrew (Biblical)", glottocode := some "bibl1238" }

def maltese : Language :=
  { id := "maltese", name := "Maltese", glottocode := some "malt1254" }

/-- The broad sample of Appendix A: 148 languages chosen on a quasi-random basis, each with the type of its comparative construction, the expression of comparison on the adjective and of the relative superlative, and whether there is suppletion (section 1.3). The rows of Table A.1, in the order of the source (bobaljik-2012, Table A.1). -/
def broadSample : List Row := [
  { language := tamashek,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.definite, false, false, false⟩],
    suppl := [⟨.verb, false, false, false⟩] },
  { language := hausa,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := lele,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := mina,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := qimant,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := somali,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := arabic_std,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.definite, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := neo_aramaic,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.definite, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := hebrew,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.more, false, false, false⟩] },
  { language := khoekhoe_nama,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := khwe,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.positive, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := koromfe,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.none, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := ijo,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kana,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := ogbronuagum,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := banda,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := lingala,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := nandi,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := sotho_northern,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := zulu,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩, ⟨.morphological, true, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := lango,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := mbay,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := koroboro_seno,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kanuri,
    region := [⟨.africa, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := irish,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.comparative, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := modern_greek,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.definite, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := kashmiri,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := persian_farsi,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := czech,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := finnish,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := udmurt,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := nenets,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.unclear, false, false, false⟩] },
  { language := ket,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := even,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := evenki,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, true, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := khalkha,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := lezgian,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.more, true, false, false⟩] },
  { language := hunzib,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := abkhaz,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := bashkir,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := khakas,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := tyvan,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := itelmen,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.none, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := chukchi,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := malayalam,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.intensified, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := ainu,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.periphrastic, false, true, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := nivkh,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.intensified, true, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := burushaski,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := yukagir,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := basque,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := asl,
    region := [⟨.eurasia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := cantonese,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := kunming,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.morphological, false, true, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := mandarin,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := dzongkha,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, true, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kham,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := limbu,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := newar_dolokha,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := bisu,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := mongsen_ao,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.intensified, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := mizo,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := dumi,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := lao,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := thai,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := japanese,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, true, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := korean,
    region := [⟨.eAsia, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.periphrastic, false, true, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := mayali,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.comparative, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := nunggubuyu,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.none, false, false, false⟩],
    suppl := [⟨.no, true, false, false⟩] },
  { language := arrernte,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := dyirbal,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := gumbaynggir,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := warlpiri,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := yindjibarndi,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.none, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kayardild,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := jingulu,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.none, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := amis,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := paiwan,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := puyuma,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, true, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, true, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := rukai,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, true, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := seediq,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.comparative, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := rapanui,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := maori,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.intensified, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := muna,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := pendau,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := yapese,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := palauan,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := fijian_boumaa,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := tuvaluan,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.standard, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.positive, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := manam,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := sinaugoro,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := amele,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩, ⟨.standard, true, false, false⟩],
    cmpr := [⟨.periphrastic, true, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := klon,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.comparative, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := teiwa,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.positive, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := mian,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, true, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := ekagi,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := koiari,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.none, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := mauwake,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := arapesh,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, true, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.none, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := skou,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.none, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := mundari,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := santali,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := remo,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := semalai,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := palaung,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, true, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := vietnamese,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.other, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := khmer,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := sapuan,
    region := [⟨.pacific, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := aleut,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := west_greenlandic,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.comparative, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := straits_salish,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.none, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := navajo,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := nishnaabemwin,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.none, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := cherokee,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kiowa,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.comparative, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := chimariko,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, true, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kiliwa,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, true, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := choctaw,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := crow,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.other, false, false, false⟩],
    cmpr := [⟨.morphological, true, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := wappo,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := nahuatl,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.none, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := comanche,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, true, false, false⟩],
    sprl := [⟨.none, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := tumpisa_shoshone,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := cupeno,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩, ⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.universal, false, true, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := sonora_yaqui,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := tohono_oodham,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.intensified, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := tarascan,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.other, false, false, false⟩],
    cmpr := [⟨.morphological, true, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := totonac,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.comparative, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := miskitu,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.absolute, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := mixtec,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.definite, false, false, false⟩],
    suppl := [⟨.no, true, false, false⟩] },
  { language := wari,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := yagua,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := bare,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := tariana,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := warekena,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := paumari,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := apalai,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := hixkaryana,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.other, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := bororo,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kayapo,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.absolute, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := piraha,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := mbya_guarani,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := urubu_kaapor,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := andoke,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.absolute, false, false, false⟩, ⟨.periphrastic, false, true, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := aymara,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩, ⟨.exceed, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := mapuche,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.standard, false, false, false⟩],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.universal, true, false, false⟩],
    suppl := [] },
  { language := moseten,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.absolute, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := urarina,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.exceed, false, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kwaza,
    region := [⟨.americas, false, false, false⟩],
    family := [],
    cmprTyp := [⟨.conjoined, true, false, false⟩],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.none, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] }]

/-- The focused survey of Appendix B: 174 languages with morphological comparison or comparative suppletion and their relatives, each with the expression of comparison on the adjective and of the relative superlative, and whether there is suppletion (section 1.3). The rows of Table B.1, in the order of the source (bobaljik-2012, Table B.1). -/
def focusedSurvey : List Row := [
  { language := albanian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := hittite,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := tocharian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, true, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := armenian_classical,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.universal, false, false, false⟩, ⟨.comparative, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := armenian_middle,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.definite, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := armenian_western,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩, ⟨.morphological, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := armenian_eastern,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩, ⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := latvian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := lithuanian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := old_church_slavonic,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := belorussian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := bulgarian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := czech,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := macedonian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := polish,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := russian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := serbian_croatian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := slovak,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := slovenian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := sorbian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := ukrainian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := old_irish,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := breton,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := irish,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.comparative, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := manx,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.comparative, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := scottish_gaelic,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.comparative, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := welsh,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := latin,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := catalan,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := french_old,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := french_modern,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := italian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := portuguese,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := romanian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := spanish,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := gothic,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := english_old,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := icelandic_old,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := afrikaans,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := danish,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := dutch,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := english_modern,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := faroese,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := frisian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := german,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := german_cimbrian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := icelandic_modern,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := norwegian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := swedish,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := yiddish,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := greek_ancient,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := greek_modern,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := sanskrit,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := bagri,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := hindi,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := kashmiri,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.unclear, false, false, false⟩] },
  { language := marathi,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := nepali,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := sinhalese,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := romani,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := romani_vlax,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.definite, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := persian_old,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := persian_middle,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := sogdian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := khotanese_gyazdian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := balochi,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := gilyan,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := kurdish_kurmanji,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.comparative, false, false, false⟩, ⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := kurdish_sorani,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := ossetian,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩, ⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := pashto,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩, ⟨.intensified, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := persian_farsi,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := shughni_rushan,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := tajik,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.morphological, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := talysh,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := tat,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := wakhi,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := yagnobi,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := zazaki,
    region := [],
    family := [⟨.indoEuropean, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.zero, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := estonian,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := finnish,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := ingrian,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := karelian,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := livonian,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩, ⟨.universal, false, false, false⟩, ⟨.definite, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := lude,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := veps,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := votic,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := saami_north,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := saami_south,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := saami_kildin,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := hungarian,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := khanty_ostyak,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := mansi_vogul,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := mari_cheremis,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := mordva,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := komi,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := udmurt,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := nenets,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := nganasan_tavgy,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, true, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.unclear, false, false, false⟩] },
  { language := selkup,
    region := [],
    family := [⟨.uralic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := even,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := evenki,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, true, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := manchu,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := nanai,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, true, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := negidal,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.morphological, false, true, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := orochi,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := orok,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.universal, false, false, false⟩, ⟨.intensified, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := ulch,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := azeri,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := bashkir,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := chuvash,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := gagauz,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := karachay_balkar,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := karaim,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kazakh,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := khakas,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kirghiz,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kumyk,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := nogai,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := shor,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := tatar,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := turkish,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := turkic_old,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.yes, true, false, false⟩] },
  { language := turkmen,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, true, false, false⟩],
    sprl := [⟨.absolute, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := tyvan,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := uyghur,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := uzbek,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := bonan,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := buryat,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.intensified, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := dagur,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kalmyk,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := khalkha,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := moghol,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := mongghul,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := oirat,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := ordos,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := santa,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := shira_yughur,
    region := [],
    family := [⟨.altaic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := ket,
    region := [],
    family := [⟨.yeniseian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kott,
    region := [],
    family := [⟨.yeniseian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.comparative, false, false, false⟩, ⟨.universal, false, false, false⟩],
    suppl := [⟨.yes, true, false, false⟩] },
  { language := yugh,
    region := [],
    family := [⟨.yeniseian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := itelmen,
    region := [],
    family := [⟨.chukotkoKamchatkan, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.none, false, false, false⟩],
    suppl := [⟨.no, false, false, false⟩] },
  { language := alutor,
    region := [],
    family := [⟨.chukotkoKamchatkan, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := chukchi,
    region := [],
    family := [⟨.chukotkoKamchatkan, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kerek,
    region := [],
    family := [⟨.chukotkoKamchatkan, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := koryak,
    region := [],
    family := [⟨.chukotkoKamchatkan, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := georgian,
    region := [],
    family := [⟨.kartvelian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := mingrelian,
    region := [],
    family := [⟨.kartvelian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := laz_chan,
    region := [],
    family := [⟨.kartvelian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := svan,
    region := [],
    family := [⟨.kartvelian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := abaza,
    region := [],
    family := [⟨.nwCaucasian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := abkhaz,
    region := [],
    family := [⟨.nwCaucasian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := adyghe,
    region := [],
    family := [⟨.nwCaucasian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, true, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := kabardian,
    region := [],
    family := [⟨.nwCaucasian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, true, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.yes, true, false, false⟩] },
  { language := ubykh,
    region := [],
    family := [⟨.nwCaucasian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := chechen,
    region := [],
    family := [⟨.nakhDagestanian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := ingush,
    region := [],
    family := [⟨.nakhDagestanian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := batsbi,
    region := [],
    family := [⟨.nakhDagestanian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.morphological, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := avar,
    region := [],
    family := [⟨.nakhDagestanian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := andi,
    region := [],
    family := [⟨.nakhDagestanian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := botlikh,
    region := [],
    family := [⟨.nakhDagestanian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := bagvalal,
    region := [],
    family := [⟨.nakhDagestanian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := tsez,
    region := [],
    family := [⟨.nakhDagestanian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.noInformation, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := hunzib,
    region := [],
    family := [⟨.nakhDagestanian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := lezgian,
    region := [],
    family := [⟨.nakhDagestanian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.yes, true, false, false⟩] },
  { language := tabasaran,
    region := [],
    family := [⟨.nakhDagestanian, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := amharic,
    region := [],
    family := [⟨.semitic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := arabic_std,
    region := [],
    family := [⟨.semitic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.definite, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := arabic_gulf,
    region := [],
    family := [⟨.semitic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.definite, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := arabic_moroccan,
    region := [],
    family := [⟨.semitic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.definite, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := assyrian_neo_aramaic,
    region := [],
    family := [⟨.semitic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.definite, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := hebrew_biblical,
    region := [],
    family := [⟨.semitic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.zero, false, false, false⟩],
    sprl := [⟨.universal, false, false, false⟩, ⟨.definite, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] },
  { language := hebrew,
    region := [],
    family := [⟨.semitic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.periphrastic, false, true, false⟩],
    sprl := [⟨.periphrastic, false, false, false⟩],
    suppl := [⟨.yes, false, false, false⟩] },
  { language := maltese,
    region := [],
    family := [⟨.semitic, false, false, false⟩],
    cmprTyp := [],
    cmpr := [⟨.morphological, false, false, false⟩],
    sprl := [⟨.definite, false, false, false⟩],
    suppl := [⟨.notIndicated, false, false, false⟩] }]

end Bobaljik2012.Structures
