module

/-!
# WALS Feature 128A: Utterance Complement Clauses
[cristofaro-2013]

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 128A`.

Chapter 128, 143 languages.
-/

@[expose] public section

namespace Data.WALS.F128A

/-- WALS 128A values. -/
inductive UtteranceComplementType where
  /-- Balanced (114 languages). -/
  | balanced
  /-- Balanced/deranked (18 languages). -/
  | balancedDeranked
  /-- Deranked (11 languages). -/
  | deranked
  deriving DecidableEq, Repr

/-- The WALS 128A coding: each language's value, keyed by its WALS code (143 languages). -/
def allData : List (String × UtteranceComplementType) :=
  [ ("abk", .balancedDeranked) -- Abkhaz
  , ("abu", .balanced) -- Abun
  , ("ace", .balanced) -- Acehnese
  , ("aco", .balanced) -- Acoma
  , ("ain", .balanced) -- Ainu
  , ("akn", .balanced) -- Akan
  , ("ame", .balanced) -- Amele
  , ("any", .balanced) -- Anywa
  , ("apu", .balanced) -- Apurinã
  , ("arg", .balancedDeranked) -- Arabic (Gulf)
  , ("arp", .balanced) -- Arapesh (Mountain)
  , ("awp", .deranked) -- Awa Pit
  , ("bdc", .balanced) -- Berbice Dutch Creole
  , ("bkr", .balanced) -- Batak (Karo)
  , ("bma", .balancedDeranked) -- Berber (Middle Atlas)
  , ("brh", .balanced) -- Brahui
  , ("brs", .balanced) -- Barasano
  , ("bsq", .balanced) -- Basque
  , ("bur", .balanced) -- Burushaski
  , ("cah", .deranked) -- Cahuilla
  , ("cnl", .balanced) -- Canela
  , ("djp", .balanced) -- Djapu
  , ("dre", .balanced) -- Drehu
  , ("emb", .deranked) -- Emberá (Northern)
  , ("eng", .balanced) -- English
  , ("epe", .balanced) -- Epena Pedee
  , ("err", .balanced) -- Erromangan
  , ("eve", .deranked) -- Evenki
  , ("fij", .balanced) -- Fijian
  , ("fin", .balancedDeranked) -- Finnish
  , ("fre", .balancedDeranked) -- French
  , ("geo", .balanced) -- Georgian
  , ("gim", .balanced) -- Gimira
  , ("goo", .balanced) -- Gooniyandi
  , ("grk", .balanced) -- Greek (Modern)
  , ("grw", .balancedDeranked) -- Greenlandic (West)
  , ("gum", .balanced) -- Gumbaynggir
  , ("heb", .balanced) -- Hebrew (Modern)
  , ("hin", .balanced) -- Hindi
  , ("hix", .balanced) -- Hixkaryana
  , ("hmo", .balanced) -- Hmong Njua
  , ("ho", .balanced) -- Ho
  , ("hun", .balanced) -- Hungarian
  , ("igb", .balanced) -- Igbo
  , ("ika", .balanced) -- Ika
  , ("ind", .balanced) -- Indonesian
  , ("ing", .balancedDeranked) -- Ingush
  , ("iri", .balanced) -- Irish
  , ("ita", .balancedDeranked) -- Italian
  , ("itz", .balanced) -- Itzaj
  , ("jak", .balanced) -- Jakaltek
  , ("jpn", .balanced) -- Japanese
  , ("juh", .balanced) -- Ju|'hoan
  , ("kan", .balanced) -- Kana
  , ("kas", .balanced) -- Kashmiri
  , ("kay", .balanced) -- Kayardild
  , ("kch", .balanced) -- Koyra Chiini
  , ("kew", .balanced) -- Kewa
  , ("kfe", .balancedDeranked) -- Koromfe
  , ("kho", .balanced) -- Nama
  , ("khs", .balanced) -- Khasi
  , ("kio", .balanced) -- Kiowa
  , ("kmj", .balanced) -- Karimojong
  , ("kmu", .balanced) -- Khmu'
  , ("knd", .balancedDeranked) -- Kannada
  , ("knr", .balanced) -- Kanuri
  , ("kor", .balanced) -- Korean
  , ("kro", .balancedDeranked) -- Krongo
  , ("lan", .balanced) -- Lango
  , ("lez", .balancedDeranked) -- Lezgian
  , ("lim", .balanced) -- Limbu
  , ("lkt", .balanced) -- Lakhota
  , ("lnd", .balanced) -- Linda
  , ("mar", .balancedDeranked) -- Maricopa
  , ("may", .balanced) -- Maybrat
  , ("mei", .balanced) -- Meithei
  , ("mhi", .balanced) -- Marathi
  , ("miy", .balanced) -- Miya
  , ("mna", .balanced) -- Muna
  , ("mnd", .balanced) -- Mandarin
  , ("mrt", .deranked) -- Martuthunira
  , ("mup", .balancedDeranked) -- Mupun
  , ("mxc", .balanced) -- Mixtec (Chalcatongo)
  , ("myi", .balanced) -- Mangarrayi
  , ("mym", .balanced) -- Malayalam
  , ("nan", .balanced) -- Nandi
  , ("nbd", .balanced) -- Nubian (Dongolese)
  , ("nbm", .balanced) -- Ngbaka (Ma'bo)
  , ("ndy", .balanced) -- Ndyuka
  , ("ngi", .balanced) -- Ngiyambaa
  , ("ngt", .balanced) -- Naga (Tangkhul)
  , ("nht", .balanced) -- Nahuatl (Tetelcingo)
  , ("niv", .deranked) -- Nivkh
  , ("nko", .balanced) -- Nkore-Kiga
  , ("noo", .balanced) -- Noon
  , ("npi", .balanced) -- Nigerian Pidgin
  , ("nug", .balanced) -- Nunggubuyu
  , ("nun", .balanced) -- Nung (in Vietnam)
  , ("orb", .balanced) -- Oromo (Boraana)
  , ("otm", .balanced) -- Otomí (Mezquital)
  , ("pan", .balanced) -- Panjabi
  , ("per", .balanced) -- Pero
  , ("pit", .balanced) -- Pitjantjatjara
  , ("pms", .balanced) -- Paamese
  , ("prh", .balanced) -- Pirahã
  , ("prs", .balanced) -- Persian
  , ("qhu", .balanced) -- Quechua (Huallaga)
  , ("ram", .balanced) -- Rama
  , ("res", .deranked) -- Resígaro
  , ("ret", .balanced) -- Retuarã
  , ("rus", .balanced) -- Russian
  , ("saw", .balanced) -- Sawu
  , ("sla", .balanced) -- Slave
  , ("sml", .balanced) -- Semelai
  , ("spa", .balancedDeranked) -- Spanish
  , ("squ", .deranked) -- Squamish
  , ("sup", .balanced) -- Supyire
  , ("swa", .balanced) -- Swahili
  , ("tab", .balanced) -- Taba
  , ("tag", .balanced) -- Tagalog
  , ("thk", .deranked) -- Thakali
  , ("tml", .deranked) -- Tamil
  , ("tpi", .balanced) -- Tok Pisin
  , ("tru", .deranked) -- Trumai
  , ("tsh", .balanced) -- Tümpisa Shoshone
  , ("tuk", .balanced) -- Tukang Besi
  , ("tur", .balancedDeranked) -- Turkish
  , ("tvl", .balanced) -- Tuvaluan
  , ("tzu", .balanced) -- Tzutujil
  , ("udh", .balancedDeranked) -- Udihe
  , ("ung", .balanced) -- Ungarinjin
  , ("urk", .balanced) -- Urubú-Kaapor
  , ("ute", .balanced) -- Ute
  , ("vai", .balanced) -- Vai
  , ("vie", .balanced) -- Vietnamese
  , ("war", .balanced) -- Wari'
  , ("way", .balanced) -- Wayampi
  , ("wma", .balanced) -- West Makian
  , ("wra", .balanced) -- Warao
  , ("yag", .balanced) -- Yagua
  , ("yaq", .balanced) -- Yaqui
  , ("yko", .balancedDeranked) -- Yukaghir (Kolyma)
  , ("yor", .balanced) -- Yoruba
  ]

end Data.WALS.F128A
