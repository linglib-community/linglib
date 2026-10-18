module

/-!
# WALS Feature 77A: Semantic Distinctions of Evidentiality
[de-haan-2013]

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 77A`.

Chapter 77, 418 languages.
-/

@[expose] public section

namespace Data.WALS.F77A

/-- WALS 77A values. -/
inductive EvidentialityDistinctions where
  /-- No grammatical evidentials (181 languages). -/
  | noGrammaticalEvidentials
  /-- Indirect only (166 languages). -/
  | indirectOnly
  /-- Direct and indirect (71 languages). -/
  | directAndIndirect
  deriving DecidableEq, Repr

/-- The WALS 77A coding: each language's value, keyed by its WALS code (418 languages). -/
def allData : List (String × EvidentialityDistinctions) :=
  [ ("abi", .noGrammaticalEvidentials) -- Abipón
  , ("abk", .indirectOnly) -- Abkhaz
  , ("abm", .indirectOnly) -- Alabama
  , ("acm", .indirectOnly) -- Achumawi
  , ("aco", .directAndIndirect) -- Acoma
  , ("adk", .directAndIndirect) -- Andoke
  , ("aeg", .noGrammaticalEvidentials) -- Arabic (Egyptian)
  , ("afr", .indirectOnly) -- Afrikaans
  , ("agr", .noGrammaticalEvidentials) -- Aguaruna
  , ("agt", .noGrammaticalEvidentials) -- Anguthimri
  , ("aho", .indirectOnly) -- Arapaho
  , ("ain", .directAndIndirect) -- Ainu
  , ("akh", .directAndIndirect) -- Akha
  , ("akr", .indirectOnly) -- Arikara
  , ("ala", .noGrammaticalEvidentials) -- Alamblak
  , ("alb", .indirectOnly) -- Albanian
  , ("alw", .noGrammaticalEvidentials) -- Alawa
  , ("amc", .indirectOnly) -- Amahuaca
  , ("amd", .directAndIndirect) -- Amdo
  , ("ame", .noGrammaticalEvidentials) -- Amele
  , ("amu", .indirectOnly) -- Amuesha
  , ("ana", .indirectOnly) -- Araona
  , ("apc", .indirectOnly) -- Apache (Chiricahua)
  , ("apl", .directAndIndirect) -- Apalaí
  , ("apu", .indirectOnly) -- Apurinã
  , ("arc", .indirectOnly) -- Archi
  , ("arg", .indirectOnly) -- Arabic (Gulf)
  , ("arp", .noGrammaticalEvidentials) -- Arapesh (Mountain)
  , ("arw", .indirectOnly) -- Armenian (Western)
  , ("asm", .indirectOnly) -- Asmat
  , ("awp", .noGrammaticalEvidentials) -- Awa Pit
  , ("aym", .directAndIndirect) -- Aymara (Central)
  , ("baa", .noGrammaticalEvidentials) -- Barai
  , ("baq", .indirectOnly) -- Baure
  , ("baw", .noGrammaticalEvidentials) -- Bawm
  , ("bco", .indirectOnly) -- Bella Coola
  , ("bdk", .noGrammaticalEvidentials) -- Budukh
  , ("beb", .noGrammaticalEvidentials) -- Benabena
  , ("bej", .indirectOnly) -- Beja
  , ("bkr", .noGrammaticalEvidentials) -- Batak (Karo)
  , ("bla", .noGrammaticalEvidentials) -- Blackfoot
  , ("blx", .indirectOnly) -- Biloxi
  , ("bor", .indirectOnly) -- Bora
  , ("bre", .noGrammaticalEvidentials) -- Breton
  , ("brh", .noGrammaticalEvidentials) -- Brahui
  , ("brm", .noGrammaticalEvidentials) -- Burmese
  , ("brs", .directAndIndirect) -- Barasano
  , ("bse", .noGrammaticalEvidentials) -- Berber (Ayt Seghrouchen Middle Atlas)
  , ("bsq", .indirectOnly) -- Basque
  , ("bul", .directAndIndirect) -- Bulgarian
  , ("bur", .noGrammaticalEvidentials) -- Burushaski
  , ("cah", .indirectOnly) -- Cahuilla
  , ("can", .noGrammaticalEvidentials) -- Candoshi
  , ("car", .directAndIndirect) -- Carib
  , ("cax", .noGrammaticalEvidentials) -- Campa (Axininca)
  , ("cbo", .indirectOnly) -- Chácobo
  , ("ccm", .indirectOnly) -- Chinantec (Comaltepec)
  , ("cco", .indirectOnly) -- Chasta Costa
  , ("cct", .indirectOnly) -- Choctaw
  , ("cha", .indirectOnly) -- Chamorro
  , ("chc", .directAndIndirect) -- Chechen
  , ("che", .indirectOnly) -- Cherokee
  , ("chk", .noGrammaticalEvidentials) -- Chukchi
  , ("chl", .indirectOnly) -- Chehalis (Upper)
  , ("chp", .indirectOnly) -- Chipewyan
  , ("chr", .noGrammaticalEvidentials) -- Chrau
  , ("cjo", .noGrammaticalEvidentials) -- Chichimeca-Jonaz
  , ("ckl", .noGrammaticalEvidentials) -- Chinook (Lower)
  , ("cku", .indirectOnly) -- Chinook (Upper)
  , ("cle", .noGrammaticalEvidentials) -- Chinantec (Lealao)
  , ("cmh", .noGrammaticalEvidentials) -- Chemehuevi
  , ("cmn", .indirectOnly) -- Comanche
  , ("cnl", .noGrammaticalEvidentials) -- Canela
  , ("cnt", .indirectOnly) -- Cantonese
  , ("coc", .indirectOnly) -- Cocama
  , ("coe", .indirectOnly) -- Coeur d'Alene
  , ("coo", .indirectOnly) -- Coos (Hanis)
  , ("cor", .indirectOnly) -- Cora
  , ("crp", .directAndIndirect) -- Carapana
  , ("crt", .noGrammaticalEvidentials) -- Chorote
  , ("cso", .noGrammaticalEvidentials) -- Chatino (Sierra Occidental)
  , ("ctm", .indirectOnly) -- Chitimacha
  , ("cyv", .noGrammaticalEvidentials) -- Cayuvava
  , ("dag", .noGrammaticalEvidentials) -- Daga
  , ("den", .indirectOnly) -- Dení
  , ("die", .noGrammaticalEvidentials) -- Diegueño (Mesa Grande)
  , ("dio", .noGrammaticalEvidentials) -- Diola-Fogny
  , ("diy", .directAndIndirect) -- Diyari
  , ("djp", .noGrammaticalEvidentials) -- Djapu
  , ("dmi", .indirectOnly) -- Dumi
  , ("dni", .indirectOnly) -- Dani (Lower Grand Valley)
  , ("dre", .noGrammaticalEvidentials) -- Drehu
  , ("dut", .indirectOnly) -- Dutch
  , ("dyi", .noGrammaticalEvidentials) -- Dyirbal
  , ("eka", .indirectOnly) -- Ekari
  , ("eng", .noGrammaticalEvidentials) -- English
  , ("epe", .indirectOnly) -- Epena Pedee
  , ("ese", .indirectOnly) -- Ese Ejja
  , ("est", .indirectOnly) -- Estonian
  , ("eve", .directAndIndirect) -- Evenki
  , ("ewe", .noGrammaticalEvidentials) -- Ewe
  , ("fas", .directAndIndirect) -- Fasu
  , ("fij", .noGrammaticalEvidentials) -- Fijian
  , ("fin", .indirectOnly) -- Finnish
  , ("for", .noGrammaticalEvidentials) -- Fore
  , ("fox", .indirectOnly) -- Fox
  , ("fre", .indirectOnly) -- French
  , ("fur", .noGrammaticalEvidentials) -- Fur
  , ("gag", .directAndIndirect) -- Gagauz
  , ("gar", .indirectOnly) -- Garo
  , ("geo", .directAndIndirect) -- Georgian
  , ("ger", .indirectOnly) -- German
  , ("gjj", .indirectOnly) -- Guajajara
  , ("gny", .indirectOnly) -- Gunya
  , ("god", .directAndIndirect) -- Godoberi
  , ("goo", .indirectOnly) -- Gooniyandi
  , ("grb", .noGrammaticalEvidentials) -- Grebo
  , ("grf", .indirectOnly) -- Garífuna
  , ("grk", .noGrammaticalEvidentials) -- Greek (Modern)
  , ("grw", .indirectOnly) -- Greenlandic (West)
  , ("gso", .indirectOnly) -- Greenlandic (South)
  , ("gua", .indirectOnly) -- Guaraní
  , ("gum", .noGrammaticalEvidentials) -- Gumbaynggir
  , ("guu", .noGrammaticalEvidentials) -- Guugu Yimidhirr
  , ("hai", .directAndIndirect) -- Haida
  , ("ham", .indirectOnly) -- Hamtai
  , ("hau", .noGrammaticalEvidentials) -- Hausa
  , ("heb", .noGrammaticalEvidentials) -- Hebrew (Modern)
  , ("hid", .indirectOnly) -- Hidatsa
  , ("hin", .noGrammaticalEvidentials) -- Hindi
  , ("hix", .directAndIndirect) -- Hixkaryana
  , ("hlp", .directAndIndirect) -- Hualapai
  , ("hlu", .indirectOnly) -- Halkomelem (Upriver)
  , ("hmi", .noGrammaticalEvidentials) -- Huitoto (Minica)
  , ("hmo", .noGrammaticalEvidentials) -- Hmong Njua
  , ("hop", .indirectOnly) -- Hopi
  , ("hun", .noGrammaticalEvidentials) -- Hungarian
  , ("hup", .directAndIndirect) -- Hupa
  , ("hzb", .indirectOnly) -- Hunzib
  , ("igb", .noGrammaticalEvidentials) -- Igbo
  , ("ign", .noGrammaticalEvidentials) -- Ignaciano
  , ("ika", .directAndIndirect) -- Ika
  , ("imo", .noGrammaticalEvidentials) -- Imonda
  , ("ind", .noGrammaticalEvidentials) -- Indonesian
  , ("ing", .directAndIndirect) -- Ingush
  , ("iqu", .indirectOnly) -- Iquito
  , ("iri", .noGrammaticalEvidentials) -- Irish
  , ("irq", .noGrammaticalEvidentials) -- Iraqw
  , ("ite", .noGrammaticalEvidentials) -- Itelmen
  , ("ito", .indirectOnly) -- Itonama
  , ("itz", .indirectOnly) -- Itzaj
  , ("jak", .indirectOnly) -- Jakaltek
  , ("jaq", .directAndIndirect) -- Jaqaru
  , ("jem", .indirectOnly) -- Jemez
  , ("jmm", .directAndIndirect) -- Jamamadi
  , ("jpn", .indirectOnly) -- Japanese
  , ("juh", .noGrammaticalEvidentials) -- Ju|'hoan
  , ("kay", .directAndIndirect) -- Kayardild
  , ("ker", .noGrammaticalEvidentials) -- Kera
  , ("ket", .noGrammaticalEvidentials) -- Ket
  , ("kew", .directAndIndirect) -- Kewa
  , ("kfe", .noGrammaticalEvidentials) -- Koromfe
  , ("kha", .directAndIndirect) -- Khalkha
  , ("khl", .noGrammaticalEvidentials) -- Khalaj
  , ("khm", .noGrammaticalEvidentials) -- Khmer
  , ("kho", .noGrammaticalEvidentials) -- Nama
  , ("khs", .noGrammaticalEvidentials) -- Khasi
  , ("khw", .directAndIndirect) -- Khowar
  , ("kic", .indirectOnly) -- Kickapoo
  , ("kio", .indirectOnly) -- Kiowa
  , ("kje", .directAndIndirect) -- Koreguaje
  , ("kji", .directAndIndirect) -- Kurmanji
  , ("kkv", .noGrammaticalEvidentials) -- Lusi
  , ("klh", .directAndIndirect) -- Kalasha
  , ("kls", .noGrammaticalEvidentials) -- Kalispel
  , ("klv", .noGrammaticalEvidentials) -- Kilivila
  , ("kma", .indirectOnly) -- Kamaiurá
  , ("kmk", .indirectOnly) -- Kalmyk
  , ("kmu", .noGrammaticalEvidentials) -- Khmu'
  , ("knd", .indirectOnly) -- Kannada
  , ("kng", .indirectOnly) -- Kaingang
  , ("knm", .noGrammaticalEvidentials) -- Kunama
  , ("knr", .noGrammaticalEvidentials) -- Kanuri
  , ("koa", .directAndIndirect) -- Koasati
  , ("kob", .noGrammaticalEvidentials) -- Kobon
  , ("kod", .directAndIndirect) -- Kodava
  , ("kol", .noGrammaticalEvidentials) -- Kolami
  , ("kon", .noGrammaticalEvidentials) -- Kongo
  , ("kor", .indirectOnly) -- Korean
  , ("kpm", .noGrammaticalEvidentials) -- Kapampangan
  , ("krb", .noGrammaticalEvidentials) -- Kiribati
  , ("krk", .indirectOnly) -- Karok
  , ("kro", .noGrammaticalEvidentials) -- Krongo
  , ("kse", .noGrammaticalEvidentials) -- Koyraboro Senni
  , ("ksh", .directAndIndirect) -- Kashaya
  , ("kto", .directAndIndirect) -- Kato
  , ("kut", .noGrammaticalEvidentials) -- Kutenai
  , ("kwk", .indirectOnly) -- Kwakw'ala
  , ("kws", .indirectOnly) -- Kawaiisu
  , ("kyl", .directAndIndirect) -- Kayah Li (Eastern)
  , ("kzy", .directAndIndirect) -- Komi-Zyrian
  , ("lad", .directAndIndirect) -- Ladakhi
  , ("lah", .indirectOnly) -- Lahu
  , ("lak", .noGrammaticalEvidentials) -- Lak
  , ("lan", .noGrammaticalEvidentials) -- Lango
  , ("lat", .indirectOnly) -- Latvian
  , ("lav", .noGrammaticalEvidentials) -- Lavukaleve
  , ("laz", .directAndIndirect) -- Laz
  , ("leg", .directAndIndirect) -- Lega
  , ("lep", .noGrammaticalEvidentials) -- Lepcha
  , ("lez", .indirectOnly) -- Lezgian
  , ("lim", .indirectOnly) -- Limbu
  , ("lit", .indirectOnly) -- Lithuanian
  , ("lkt", .indirectOnly) -- Lakhota
  , ("luv", .noGrammaticalEvidentials) -- Luvale
  , ("mab", .noGrammaticalEvidentials) -- Maba
  , ("mac", .noGrammaticalEvidentials) -- Macushi
  , ("mak", .directAndIndirect) -- Makah
  , ("mal", .noGrammaticalEvidentials) -- Malagasy
  , ("mam", .indirectOnly) -- Mam
  , ("mao", .noGrammaticalEvidentials) -- Maori
  , ("map", .noGrammaticalEvidentials) -- Mapudungun
  , ("mar", .directAndIndirect) -- Maricopa
  , ("mau", .noGrammaticalEvidentials) -- Maung
  , ("may", .noGrammaticalEvidentials) -- Maybrat
  , ("mch", .noGrammaticalEvidentials) -- Machiguenga
  , ("mdn", .indirectOnly) -- Mandan
  , ("mei", .directAndIndirect) -- Meithei
  , ("mgl", .directAndIndirect) -- Mingrelian
  , ("mja", .indirectOnly) -- Mixtec (Jamiltepec)
  , ("mku", .noGrammaticalEvidentials) -- Maranungku
  , ("mnd", .noGrammaticalEvidentials) -- Mandarin
  , ("mne", .indirectOnly) -- Maidu (Northeast)
  , ("mny", .noGrammaticalEvidentials) -- Margany
  , ("moh", .indirectOnly) -- Mohawk
  , ("mov", .noGrammaticalEvidentials) -- Movima
  , ("mrd", .indirectOnly) -- Marind
  , ("mrl", .noGrammaticalEvidentials) -- Murle
  , ("mrt", .indirectOnly) -- Martuthunira
  , ("mse", .noGrammaticalEvidentials) -- Munsee
  , ("mss", .indirectOnly) -- Miwok (Southern Sierra)
  , ("mtg", .indirectOnly) -- Montagnais
  , ("mth", .indirectOnly) -- Mixe (Tlahuitoltepec)
  , ("mtl", .indirectOnly) -- Mattole
  , ("mun", .noGrammaticalEvidentials) -- Mundari
  , ("mxc", .noGrammaticalEvidentials) -- Mixtec (Chalcatongo)
  , ("mxo", .indirectOnly) -- Mixtec (Ocotepec)
  , ("mxs", .indirectOnly) -- Mixtec (Silacayoapan)
  , ("mxt", .noGrammaticalEvidentials) -- Mixtec (Ayutla)
  , ("mxz", .noGrammaticalEvidentials) -- Mixtec (Coatzospan)
  , ("myi", .indirectOnly) -- Mangarrayi
  , ("nav", .indirectOnly) -- Navajo
  , ("nbd", .noGrammaticalEvidentials) -- Nubian (Dongolese)
  , ("ndy", .noGrammaticalEvidentials) -- Ndyuka
  , ("nep", .indirectOnly) -- Nepali
  , ("nev", .indirectOnly) -- Nevome
  , ("nez", .noGrammaticalEvidentials) -- Nez Perce
  , ("ngi", .directAndIndirect) -- Ngiyambaa
  , ("nhh", .noGrammaticalEvidentials) -- Nahuatl (Huasteca)
  , ("nhm", .indirectOnly) -- Nahuatl (Michoacán)
  , ("nhn", .indirectOnly) -- Nahuatl (North Puebla)
  , ("nht", .indirectOnly) -- Nahuatl (Tetelcingo)
  , ("nit", .indirectOnly) -- Nitinaht
  , ("niv", .indirectOnly) -- Nivkh
  , ("nko", .noGrammaticalEvidentials) -- Nkore-Kiga
  , ("nmi", .indirectOnly) -- Nahuatl (Mecayapan Isthmus)
  , ("nmp", .noGrammaticalEvidentials) -- Nahuatl (Milpa Alta)
  , ("nsn", .indirectOnly) -- Nisenan
  , ("nti", .noGrammaticalEvidentials) -- Ngiti
  , ("ntu", .directAndIndirect) -- Nenets
  , ("nug", .noGrammaticalEvidentials) -- Nunggubuyu
  , ("nuu", .indirectOnly) -- Nuuchahnulth
  , ("nwd", .indirectOnly) -- Newar (Dolakha)
  , ("nya", .noGrammaticalEvidentials) -- Nyawaygi
  , ("oji", .noGrammaticalEvidentials) -- Ojibwa (Eastern)
  , ("omh", .indirectOnly) -- Omaha
  , ("ond", .indirectOnly) -- Oneida
  , ("ood", .indirectOnly) -- O'odham
  , ("orh", .noGrammaticalEvidentials) -- Oromo (Harar)
  , ("otm", .indirectOnly) -- Otomí (Mezquital)
  , ("pae", .indirectOnly) -- Páez
  , ("pai", .indirectOnly) -- Paiwan
  , ("pau", .indirectOnly) -- Paumarí
  , ("pem", .noGrammaticalEvidentials) -- Pemon
  , ("pip", .noGrammaticalEvidentials) -- Pipil
  , ("pir", .indirectOnly) -- Piro
  , ("pit", .indirectOnly) -- Pitjantjatjara
  , ("plk", .noGrammaticalEvidentials) -- Palikur
  , ("pme", .directAndIndirect) -- Pomo (Eastern)
  , ("pmn", .directAndIndirect) -- Pomo (Northern)
  , ("pms", .noGrammaticalEvidentials) -- Paamese
  , ("pno", .indirectOnly) -- Paiute (Northern)
  , ("poh", .noGrammaticalEvidentials) -- Pohnpeian
  , ("pot", .indirectOnly) -- Potawatomi
  , ("ppi", .noGrammaticalEvidentials) -- Pitta Pitta
  , ("prc", .indirectOnly) -- Paresi
  , ("prh", .directAndIndirect) -- Pirahã
  , ("prs", .directAndIndirect) -- Persian
  , ("psm", .indirectOnly) -- Passamaquoddy-Maliseet
  , ("pso", .directAndIndirect) -- Pomo (Southeastern)
  , ("ptw", .indirectOnly) -- Patwin
  , ("pum", .directAndIndirect) -- Pumi
  , ("pur", .indirectOnly) -- Purépecha
  , ("put", .indirectOnly) -- Paiute (Southern)
  , ("pwn", .indirectOnly) -- Pawnee
  , ("qaw", .noGrammaticalEvidentials) -- Qawasqar
  , ("qhu", .directAndIndirect) -- Quechua (Huallaga)
  , ("qim", .directAndIndirect) -- Quechua (Imbabura)
  , ("que", .directAndIndirect) -- Quechan
  , ("qui", .indirectOnly) -- Quileute
  , ("ram", .noGrammaticalEvidentials) -- Rama
  , ("rap", .noGrammaticalEvidentials) -- Rapanui
  , ("ret", .directAndIndirect) -- Retuarã
  , ("rom", .noGrammaticalEvidentials) -- Romanian
  , ("rus", .noGrammaticalEvidentials) -- Russian
  , ("rut", .indirectOnly) -- Rutul
  , ("san", .noGrammaticalEvidentials) -- Sango
  , ("say", .noGrammaticalEvidentials) -- Sayula Popoluca
  , ("sba", .noGrammaticalEvidentials) -- Sáliba (in Colombia)
  , ("sel", .noGrammaticalEvidentials) -- Selknam
  , ("she", .directAndIndirect) -- Sherpa
  , ("shk", .indirectOnly) -- Shipibo-Konibo
  , ("shu", .indirectOnly) -- Shuswap
  , ("sin", .directAndIndirect) -- Siona
  , ("siu", .noGrammaticalEvidentials) -- Siuslaw
  , ("sla", .indirectOnly) -- Slave
  , ("slp", .noGrammaticalEvidentials) -- Selepet
  , ("slr", .directAndIndirect) -- Salar
  , ("snm", .directAndIndirect) -- Sanuma
  , ("snt", .noGrammaticalEvidentials) -- Sentani
  , ("spa", .noGrammaticalEvidentials) -- Spanish
  , ("squ", .directAndIndirect) -- Squamish
  , ("src", .indirectOnly) -- Sarcee
  , ("sre", .noGrammaticalEvidentials) -- Sre
  , ("srn", .indirectOnly) -- Sirionó
  , ("srr", .indirectOnly) -- Serrano
  , ("sue", .indirectOnly) -- Suena
  , ("sup", .noGrammaticalEvidentials) -- Supyire
  , ("swa", .noGrammaticalEvidentials) -- Swahili
  , ("swe", .indirectOnly) -- Swedish
  , ("tab", .noGrammaticalEvidentials) -- Taba
  , ("tac", .indirectOnly) -- Tacana
  , ("tag", .indirectOnly) -- Tagalog
  , ("tar", .directAndIndirect) -- Tariana
  , ("tau", .noGrammaticalEvidentials) -- Tauya
  , ("tew", .indirectOnly) -- Tewa (Arizona)
  , ("tha", .noGrammaticalEvidentials) -- Thai
  , ("thk", .noGrammaticalEvidentials) -- Thakali
  , ("til", .noGrammaticalEvidentials) -- Tillamook
  , ("tiw", .noGrammaticalEvidentials) -- Tiwi
  , ("tkl", .indirectOnly) -- Takelma
  , ("tli", .noGrammaticalEvidentials) -- Tlingit
  , ("tlp", .noGrammaticalEvidentials) -- Tlapanec
  , ("tmc", .noGrammaticalEvidentials) -- Timucua
  , ("tml", .indirectOnly) -- Tamil
  , ("tnb", .noGrammaticalEvidentials) -- Tunebo
  , ("ton", .indirectOnly) -- Tonkawa
  , ("toq", .noGrammaticalEvidentials) -- Toqabaqita
  , ("tpn", .indirectOnly) -- Tepehuan (Northern)
  , ("trg", .noGrammaticalEvidentials) -- Tewa (Rio Grande)
  , ("trn", .indirectOnly) -- Terêna
  , ("tru", .indirectOnly) -- Trumai
  , ("tsh", .indirectOnly) -- Tümpisa Shoshone
  , ("tsi", .indirectOnly) -- Tsimshian (Coast)
  , ("tsm", .noGrammaticalEvidentials) -- Tasmanian
  , ("ttu", .directAndIndirect) -- Tsova-Tush
  , ("tuc", .directAndIndirect) -- Tucano
  , ("tuk", .noGrammaticalEvidentials) -- Tukang Besi
  , ("tun", .indirectOnly) -- Tunica
  , ("tur", .directAndIndirect) -- Turkish
  , ("tus", .noGrammaticalEvidentials) -- Tuscarora
  , ("tuy", .directAndIndirect) -- Tuyuca
  , ("twe", .directAndIndirect) -- Tarahumara (Western)
  , ("twn", .indirectOnly) -- Tiwa (Northern)
  , ("tws", .noGrammaticalEvidentials) -- Tiwa (Southern)
  , ("txj", .noGrammaticalEvidentials) -- Totonac (Xicotepec de Juárez)
  , ("tzo", .indirectOnly) -- Tzotzil
  , ("tzu", .indirectOnly) -- Tzutujil
  , ("uhi", .noGrammaticalEvidentials) -- Uradhi
  , ("una", .noGrammaticalEvidentials) -- Una
  , ("ung", .noGrammaticalEvidentials) -- Ungarinjin
  , ("urk", .indirectOnly) -- Urubú-Kaapor
  , ("usa", .noGrammaticalEvidentials) -- Usan
  , ("vie", .noGrammaticalEvidentials) -- Vietnamese
  , ("wai", .indirectOnly) -- Wai Wai
  , ("wam", .noGrammaticalEvidentials) -- Wambaya
  , ("wao", .indirectOnly) -- Waorani
  , ("war", .noGrammaticalEvidentials) -- Wari'
  , ("wat", .noGrammaticalEvidentials) -- Watjarri
  , ("way", .indirectOnly) -- Wayampi
  , ("wch", .noGrammaticalEvidentials) -- Wichí
  , ("wic", .indirectOnly) -- Wichita
  , ("win", .directAndIndirect) -- Wintu
  , ("wiy", .noGrammaticalEvidentials) -- Wiyot
  , ("wol", .noGrammaticalEvidentials) -- Woleaian
  , ("wra", .indirectOnly) -- Warao
  , ("wrd", .noGrammaticalEvidentials) -- Wardaman
  , ("wrg", .noGrammaticalEvidentials) -- Warrgamay
  , ("wrk", .noGrammaticalEvidentials) -- Warekena
  , ("wur", .indirectOnly) -- Waurá
  , ("wyn", .noGrammaticalEvidentials) -- Wayana
  , ("yag", .noGrammaticalEvidentials) -- Yagua
  , ("yam", .indirectOnly) -- Yaminahua
  , ("yaq", .indirectOnly) -- Yaqui
  , ("yid", .noGrammaticalEvidentials) -- Yidiny
  , ("yim", .noGrammaticalEvidentials) -- Yimas
  , ("yko", .indirectOnly) -- Yukaghir (Kolyma)
  , ("ykt", .directAndIndirect) -- Yakut
  , ("yor", .noGrammaticalEvidentials) -- Yoruba
  , ("ypk", .indirectOnly) -- Yup'ik (Central)
  , ("yuc", .noGrammaticalEvidentials) -- Yuchi
  , ("yuk", .noGrammaticalEvidentials) -- Yukulta
  , ("yur", .noGrammaticalEvidentials) -- Yurok
  , ("ywl", .noGrammaticalEvidentials) -- Yawelmani
  , ("yyg", .noGrammaticalEvidentials) -- Yaygir
  , ("zqc", .indirectOnly) -- Zoque (Copainalá)
  , ("zul", .noGrammaticalEvidentials) -- Zulu
  , ("zun", .noGrammaticalEvidentials) -- Zuni
  ]

end Data.WALS.F77A
