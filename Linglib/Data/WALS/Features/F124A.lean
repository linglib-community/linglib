module

/-!
# WALS Feature 124A: 'Want' Complement Subjects
[cristofaro-2013]

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 124A`.

Chapter 124, 283 languages.
-/

@[expose] public section

namespace Data.WALS.F124A

/-- WALS 124A values. -/
inductive WantComplementSubject where
  /-- Subject is left implicit (144 languages). -/
  | subjectIsLeftImplicit
  /-- Subject is expressed overtly (72 languages). -/
  | subjectIsExpressedOvertly
  /-- Both construction types exist (14 languages). -/
  | bothConstructionTypesExist
  /-- Desiderative verbal affix (45 languages). -/
  | desiderativeVerbalAffix
  /-- Desiderative particle (8 languages). -/
  | desiderativeParticle
  deriving DecidableEq, Repr

/-- The WALS 124A coding: each language's value, keyed by its WALS code (283 languages). -/
def allData : List (String × WantComplementSubject) :=
  [ ("abk", .subjectIsExpressedOvertly) -- Abkhaz
  , ("abu", .subjectIsExpressedOvertly) -- Abun
  , ("ace", .subjectIsLeftImplicit) -- Acehnese
  , ("aeg", .subjectIsExpressedOvertly) -- Arabic (Egyptian)
  , ("aga", .desiderativeVerbalAffix) -- Agarabi
  , ("ain", .subjectIsLeftImplicit) -- Ainu
  , ("akh", .subjectIsLeftImplicit) -- Akha
  , ("alb", .subjectIsExpressedOvertly) -- Albanian
  , ("ale", .desiderativeVerbalAffix) -- Aleut
  , ("all", .subjectIsExpressedOvertly) -- Ala'ala
  , ("aly", .subjectIsLeftImplicit) -- Alyawarra
  , ("ame", .subjectIsExpressedOvertly) -- Amele
  , ("aml", .bothConstructionTypesExist) -- Ambae (Lolovoli Northeast)
  , ("amp", .subjectIsLeftImplicit) -- Arrernte (Mparntwe)
  , ("ana", .desiderativeVerbalAffix) -- Araona
  , ("ano", .subjectIsLeftImplicit) -- Anong
  , ("apj", .subjectIsExpressedOvertly) -- Apache (Jicarilla)
  , ("apu", .desiderativeVerbalAffix) -- Apurinã
  , ("ara", .desiderativeVerbalAffix) -- Lokono
  , ("ass", .subjectIsLeftImplicit) -- Assamese
  , ("awp", .desiderativeVerbalAffix) -- Awa Pit
  , ("bab", .subjectIsLeftImplicit) -- Babungo
  , ("bae", .subjectIsExpressedOvertly) -- Baré
  , ("bag", .subjectIsExpressedOvertly) -- Bagirmi
  , ("bak", .subjectIsLeftImplicit) -- Baka (in Cameroon)
  , ("baw", .subjectIsLeftImplicit) -- Bawm
  , ("bbw", .subjectIsExpressedOvertly) -- Bininj Gun-Wok
  , ("ben", .subjectIsLeftImplicit) -- Bengali
  , ("biu", .subjectIsLeftImplicit) -- Bisu
  , ("bla", .subjectIsExpressedOvertly) -- Blackfoot
  , ("bma", .subjectIsExpressedOvertly) -- Berber (Middle Atlas)
  , ("boz", .subjectIsLeftImplicit) -- Bozo (Tigemaxo)
  , ("brm", .subjectIsLeftImplicit) -- Burmese
  , ("bud", .subjectIsExpressedOvertly) -- Buduma
  , ("bul", .subjectIsExpressedOvertly) -- Bulgarian
  , ("bvi", .subjectIsLeftImplicit) -- Bali-Vitu
  , ("cch", .subjectIsExpressedOvertly) -- Chocho
  , ("cha", .subjectIsLeftImplicit) -- Chamorro
  , ("chk", .desiderativeVerbalAffix) -- Chukchi
  , ("chn", .subjectIsLeftImplicit) -- Chantyal
  , ("cic", .subjectIsLeftImplicit) -- Chichewa
  , ("cmn", .subjectIsLeftImplicit) -- Comanche
  , ("cnl", .subjectIsLeftImplicit) -- Canela
  , ("cnt", .subjectIsLeftImplicit) -- Cantonese
  , ("cop", .subjectIsLeftImplicit) -- Coptic
  , ("dgb", .subjectIsExpressedOvertly) -- Dagbani
  , ("dgr", .subjectIsLeftImplicit) -- Dagur
  , ("dha", .subjectIsLeftImplicit) -- Dhaasanac
  , ("dhb", .subjectIsLeftImplicit) -- Dharumbal
  , ("dhi", .subjectIsLeftImplicit) -- Dhivehi
  , ("die", .subjectIsExpressedOvertly) -- Diegueño (Mesa Grande)
  , ("dre", .subjectIsLeftImplicit) -- Drehu
  , ("drg", .subjectIsLeftImplicit) -- Dargwa
  , ("eng", .subjectIsLeftImplicit) -- English
  , ("epe", .subjectIsLeftImplicit) -- Epena Pedee
  , ("err", .subjectIsLeftImplicit) -- Erromangan
  , ("eve", .desiderativeVerbalAffix) -- Evenki
  , ("ewe", .subjectIsExpressedOvertly) -- Ewe
  , ("fij", .desiderativeParticle) -- Fijian
  , ("fin", .subjectIsLeftImplicit) -- Finnish
  , ("fon", .bothConstructionTypesExist) -- Fongbe
  , ("fre", .subjectIsLeftImplicit) -- French
  , ("gar", .subjectIsLeftImplicit) -- Garo
  , ("gel", .subjectIsLeftImplicit) -- Gela
  , ("geo", .bothConstructionTypesExist) -- Georgian
  , ("ger", .subjectIsLeftImplicit) -- German
  , ("gol", .subjectIsExpressedOvertly) -- Gola
  , ("grk", .subjectIsExpressedOvertly) -- Greek (Modern)
  , ("gua", .desiderativeVerbalAffix) -- Guaraní
  , ("guu", .subjectIsLeftImplicit) -- Guugu Yimidhirr
  , ("hat", .subjectIsExpressedOvertly) -- Hatam
  , ("hau", .subjectIsExpressedOvertly) -- Hausa
  , ("heb", .subjectIsLeftImplicit) -- Hebrew (Modern)
  , ("hin", .subjectIsLeftImplicit) -- Hindi
  , ("hix", .subjectIsLeftImplicit) -- Hixkaryana
  , ("hma", .subjectIsLeftImplicit) -- Hmar
  , ("hmo", .subjectIsLeftImplicit) -- Hmong Njua
  , ("hoa", .subjectIsLeftImplicit) -- Hoava
  , ("hum", .desiderativeVerbalAffix) -- Huitoto (Murui)
  , ("hun", .subjectIsLeftImplicit) -- Hungarian
  , ("hzb", .subjectIsLeftImplicit) -- Hunzib
  , ("ik", .subjectIsLeftImplicit) -- Ik
  , ("ika", .subjectIsLeftImplicit) -- Ika
  , ("imo", .subjectIsLeftImplicit) -- Imonda
  , ("ind", .subjectIsLeftImplicit) -- Indonesian
  , ("irq", .subjectIsLeftImplicit) -- Iraqw
  , ("itz", .desiderativeParticle) -- Itzaj
  , ("jab", .subjectIsExpressedOvertly) -- Jabêm
  , ("jak", .subjectIsExpressedOvertly) -- Jakaltek
  , ("jam", .desiderativeVerbalAffix) -- Jaminjung
  , ("jel", .subjectIsExpressedOvertly) -- Jeli
  , ("jpn", .desiderativeVerbalAffix) -- Japanese
  , ("juh", .bothConstructionTypesExist) -- Ju|'hoan
  , ("kam", .subjectIsLeftImplicit) -- Kambera
  , ("kan", .subjectIsLeftImplicit) -- Kana
  , ("kao", .subjectIsLeftImplicit) -- Karao
  , ("kas", .subjectIsLeftImplicit) -- Kashmiri
  , ("kay", .desiderativeVerbalAffix) -- Kayardild
  , ("kem", .subjectIsLeftImplicit) -- Kemant
  , ("ker", .subjectIsLeftImplicit) -- Kera
  , ("ket", .subjectIsLeftImplicit) -- Ket
  , ("kfe", .bothConstructionTypesExist) -- Koromfe
  , ("kgu", .subjectIsExpressedOvertly) -- Kalkatungu
  , ("khm", .subjectIsLeftImplicit) -- Khmer
  , ("kho", .subjectIsLeftImplicit) -- Nama
  , ("klq", .subjectIsExpressedOvertly) -- Kalam
  , ("klv", .subjectIsExpressedOvertly) -- Kilivila
  , ("kma", .desiderativeVerbalAffix) -- Kamaiurá
  , ("kmu", .subjectIsLeftImplicit) -- Khmu'
  , ("knd", .subjectIsLeftImplicit) -- Kannada
  , ("kob", .desiderativeVerbalAffix) -- Kobon
  , ("kod", .subjectIsLeftImplicit) -- Kodava
  , ("kon", .subjectIsLeftImplicit) -- Kongo
  , ("kor", .subjectIsLeftImplicit) -- Korean
  , ("krb", .subjectIsLeftImplicit) -- Kiribati
  , ("kro", .subjectIsLeftImplicit) -- Krongo
  , ("krw", .desiderativeParticle) -- Korowai
  , ("kse", .subjectIsExpressedOvertly) -- Koyraboro Senni
  , ("kty", .subjectIsLeftImplicit) -- Khanty
  , ("kug", .subjectIsLeftImplicit) -- Kunming
  , ("kuk", .subjectIsLeftImplicit) -- Kukú
  , ("kut", .subjectIsExpressedOvertly) -- Kutenai
  , ("kwa", .subjectIsExpressedOvertly) -- Kwaio
  , ("kwk", .desiderativeVerbalAffix) -- Kwakw'ala
  , ("kya", .subjectIsLeftImplicit) -- Kuku-Yalanji
  , ("kyk", .desiderativeVerbalAffix) -- Kyaka
  , ("kyl", .subjectIsLeftImplicit) -- Kayah Li (Eastern)
  , ("lad", .desiderativeVerbalAffix) -- Ladakhi
  , ("lak", .subjectIsLeftImplicit) -- Lak
  , ("lan", .subjectIsLeftImplicit) -- Lango
  , ("lat", .subjectIsLeftImplicit) -- Latvian
  , ("lel", .subjectIsLeftImplicit) -- Lele
  , ("lep", .subjectIsLeftImplicit) -- Lepcha
  , ("lez", .subjectIsLeftImplicit) -- Lezgian
  , ("lgu", .subjectIsLeftImplicit) -- Longgu
  , ("lil", .subjectIsLeftImplicit) -- Lillooet
  , ("lin", .bothConstructionTypesExist) -- Lingala
  , ("lml", .subjectIsExpressedOvertly) -- Limilngan
  , ("luv", .subjectIsLeftImplicit) -- Luvale
  , ("mac", .desiderativeVerbalAffix) -- Macushi
  , ("mad", .subjectIsLeftImplicit) -- Ma'di
  , ("mak", .desiderativeVerbalAffix) -- Makah
  , ("mam", .subjectIsExpressedOvertly) -- Mam
  , ("mao", .subjectIsLeftImplicit) -- Maori
  , ("map", .desiderativeParticle) -- Mapudungun
  , ("mar", .subjectIsExpressedOvertly) -- Maricopa
  , ("may", .subjectIsExpressedOvertly) -- Maybrat
  , ("mbi", .subjectIsLeftImplicit) -- Mbili
  , ("mby", .bothConstructionTypesExist) -- Mbay
  , ("mcv", .desiderativeVerbalAffix) -- Mocoví
  , ("mde", .subjectIsExpressedOvertly) -- Mende
  , ("mdr", .subjectIsLeftImplicit) -- Madurese
  , ("meh", .subjectIsExpressedOvertly) -- Mehri
  , ("mei", .subjectIsLeftImplicit) -- Meithei
  , ("mhi", .subjectIsLeftImplicit) -- Marathi
  , ("mid", .subjectIsLeftImplicit) -- Midob
  , ("mis", .subjectIsLeftImplicit) -- Miskito
  , ("miy", .bothConstructionTypesExist) -- Miya
  , ("mku", .desiderativeVerbalAffix) -- Maranungku
  , ("mle", .subjectIsLeftImplicit) -- Maale
  , ("mnd", .subjectIsLeftImplicit) -- Mandarin
  , ("mno", .subjectIsLeftImplicit) -- Mono (in United States)
  , ("moh", .subjectIsExpressedOvertly) -- Mohawk
  , ("mos", .subjectIsLeftImplicit) -- Mosetén
  , ("mrl", .subjectIsExpressedOvertly) -- Murle
  , ("mrt", .subjectIsLeftImplicit) -- Martuthunira
  , ("mts", .desiderativeVerbalAffix) -- Matis
  , ("mup", .subjectIsLeftImplicit) -- Mupun
  , ("mxc", .subjectIsExpressedOvertly) -- Mixtec (Chalcatongo)
  , ("nab", .desiderativeVerbalAffix) -- Nabak
  , ("nav", .subjectIsExpressedOvertly) -- Navajo
  , ("nbr", .desiderativeParticle) -- Ngäbere
  , ("ndb", .subjectIsLeftImplicit) -- Ndebele
  , ("ngi", .subjectIsLeftImplicit) -- Ngiyambaa
  , ("ngl", .desiderativeVerbalAffix) -- Ngalakan
  , ("nha", .subjectIsLeftImplicit) -- Nhanda
  , ("nht", .subjectIsExpressedOvertly) -- Nahuatl (Tetelcingo)
  , ("nia", .subjectIsExpressedOvertly) -- Nias
  , ("niu", .subjectIsLeftImplicit) -- Niuean
  , ("nko", .subjectIsLeftImplicit) -- Nkore-Kiga
  , ("nmb", .desiderativeVerbalAffix) -- Nambikuára (Southern)
  , ("nmi", .desiderativeVerbalAffix) -- Nahuatl (Mecayapan Isthmus)
  , ("nph", .subjectIsLeftImplicit) -- Nar-Phu
  , ("nse", .subjectIsLeftImplicit) -- Nsenga
  , ("nti", .subjectIsExpressedOvertly) -- Ngiti
  , ("nua", .subjectIsExpressedOvertly) -- Nuaulu
  , ("obo", .bothConstructionTypesExist) -- Obolo
  , ("oji", .desiderativeVerbalAffix) -- Ojibwa (Eastern)
  , ("olu", .desiderativeVerbalAffix) -- Olutec
  , ("ood", .desiderativeVerbalAffix) -- O'odham
  , ("orh", .bothConstructionTypesExist) -- Oromo (Harar)
  , ("otm", .subjectIsExpressedOvertly) -- Otomí (Mezquital)
  , ("pae", .subjectIsLeftImplicit) -- Páez
  , ("pal", .subjectIsLeftImplicit) -- Palauan
  , ("pec", .subjectIsLeftImplicit) -- Pech
  , ("per", .bothConstructionTypesExist) -- Pero
  , ("pga", .subjectIsExpressedOvertly) -- Pilagá
  , ("pit", .subjectIsLeftImplicit) -- Pitjantjatjara
  , ("pms", .subjectIsExpressedOvertly) -- Paamese
  , ("pno", .desiderativeVerbalAffix) -- Paiute (Northern)
  , ("pny", .subjectIsLeftImplicit) -- Panyjima
  , ("pop", .subjectIsExpressedOvertly) -- Popoloca (Metzontla)
  , ("prh", .desiderativeVerbalAffix) -- Pirahã
  , ("prs", .subjectIsExpressedOvertly) -- Persian
  , ("ptt", .subjectIsLeftImplicit) -- Pattani
  , ("pul", .subjectIsLeftImplicit) -- Puluwat
  , ("pur", .subjectIsLeftImplicit) -- Purépecha
  , ("qaf", .subjectIsExpressedOvertly) -- Qafar
  , ("qhu", .subjectIsLeftImplicit) -- Quechua (Huallaga)
  , ("qia", .desiderativeVerbalAffix) -- Qiang
  , ("qim", .subjectIsLeftImplicit) -- Quechua (Imbabura)
  , ("rag", .subjectIsExpressedOvertly) -- Raga
  , ("ram", .subjectIsLeftImplicit) -- Rama
  , ("rap", .subjectIsLeftImplicit) -- Rapanui
  , ("raw", .subjectIsLeftImplicit) -- Rawang
  , ("ret", .subjectIsLeftImplicit) -- Retuarã
  , ("rom", .subjectIsExpressedOvertly) -- Romanian
  , ("rus", .subjectIsLeftImplicit) -- Russian
  , ("sam", .desiderativeParticle) -- Samoan
  , ("san", .subjectIsLeftImplicit) -- Sango
  , ("sap", .subjectIsLeftImplicit) -- Sapuan
  , ("sed", .subjectIsLeftImplicit) -- Sedang
  , ("see", .desiderativeVerbalAffix) -- Seediq
  , ("ser", .subjectIsLeftImplicit) -- Seri
  , ("shk", .desiderativeVerbalAffix) -- Shipibo-Konibo
  , ("sho", .desiderativeVerbalAffix) -- Shoshone
  , ("sir", .subjectIsExpressedOvertly) -- Siar
  , ("sla", .subjectIsExpressedOvertly) -- Slave
  , ("slb", .subjectIsExpressedOvertly) -- Saliba (in Papua New Guinea)
  , ("sno", .subjectIsLeftImplicit) -- Saami (Northern)
  , ("som", .subjectIsExpressedOvertly) -- Somali
  , ("soq", .subjectIsExpressedOvertly) -- Soqotri
  , ("spa", .subjectIsLeftImplicit) -- Spanish
  , ("squ", .subjectIsExpressedOvertly) -- Squamish
  , ("sue", .subjectIsLeftImplicit) -- Suena
  , ("sun", .subjectIsLeftImplicit) -- Sundanese
  , ("sup", .subjectIsLeftImplicit) -- Supyire
  , ("syu", .subjectIsExpressedOvertly) -- Salt-Yui
  , ("tab", .subjectIsExpressedOvertly) -- Taba
  , ("tag", .subjectIsLeftImplicit) -- Tagalog
  , ("tau", .subjectIsLeftImplicit) -- Tauya
  , ("ten", .subjectIsExpressedOvertly) -- Tennet
  , ("tgn", .desiderativeVerbalAffix) -- Tugun
  , ("tha", .subjectIsLeftImplicit) -- Thai
  , ("tib", .subjectIsLeftImplicit) -- Tibetan (Standard Spoken)
  , ("tid", .subjectIsLeftImplicit) -- Tidore
  , ("tja", .subjectIsExpressedOvertly) -- Tiipay (Jamul)
  , ("tmm", .subjectIsExpressedOvertly) -- Tamabo
  , ("tob", .desiderativeVerbalAffix) -- Toba
  , ("tps", .desiderativeVerbalAffix) -- Tepehuan (Southeastern)
  , ("trb", .bothConstructionTypesExist) -- Teribe
  , ("trt", .bothConstructionTypesExist) -- Ternate
  , ("tru", .subjectIsLeftImplicit) -- Trumai
  , ("tsi", .subjectIsExpressedOvertly) -- Tsimshian (Coast)
  , ("ttn", .subjectIsExpressedOvertly) -- Tetun
  , ("tuk", .bothConstructionTypesExist) -- Tukang Besi
  , ("tur", .subjectIsLeftImplicit) -- Turkish
  , ("tzu", .subjectIsExpressedOvertly) -- Tzutujil
  , ("udh", .desiderativeVerbalAffix) -- Udihe
  , ("udm", .subjectIsLeftImplicit) -- Udmurt
  , ("uku", .desiderativeParticle) -- Upper Kuskokwim
  , ("urk", .desiderativeParticle) -- Urubú-Kaapor
  , ("vie", .subjectIsLeftImplicit) -- Vietnamese
  , ("wal", .subjectIsExpressedOvertly) -- Walman
  , ("wam", .subjectIsLeftImplicit) -- Wambaya
  , ("wch", .subjectIsExpressedOvertly) -- Wichí
  , ("wlf", .subjectIsLeftImplicit) -- Wolof
  , ("wra", .subjectIsLeftImplicit) -- Warao
  , ("wrm", .subjectIsExpressedOvertly) -- Warembori
  , ("yag", .subjectIsLeftImplicit) -- Yagua
  , ("yaq", .desiderativeVerbalAffix) -- Yaqui
  , ("yey", .subjectIsLeftImplicit) -- Yeyi
  , ("yim", .subjectIsLeftImplicit) -- Yimas
  , ("yir", .desiderativeVerbalAffix) -- Yir Yoront
  , ("yko", .subjectIsLeftImplicit) -- Yukaghir (Kolyma)
  , ("ynk", .subjectIsLeftImplicit) -- Yankuntjatjara
  , ("yor", .subjectIsLeftImplicit) -- Yoruba
  , ("ypk", .desiderativeVerbalAffix) -- Yup'ik (Central)
  , ("ytu", .desiderativeVerbalAffix) -- Yukaghir (Tundra)
  , ("ywr", .subjectIsExpressedOvertly) -- Yawuru
  , ("zaq", .subjectIsExpressedOvertly) -- Zapotec (Quiegolani)
  , ("zch", .desiderativeVerbalAffix) -- Zoque (Chimalapa)
  , ("zul", .subjectIsLeftImplicit) -- Zulu
  ]

end Data.WALS.F124A
