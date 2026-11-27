module

/-!
# WALS Feature 116A: Polar Questions
[dryer-2013-wals]

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 116A`.

Chapter 116, 955 languages.
-/

@[expose] public section

namespace Data.WALS.F116A

/-- WALS 116A values. -/
inductive PolarQuestionType where
  /-- Question particle (585 languages). -/
  | questionParticle
  /-- Interrogative verb morphology (164 languages). -/
  | interrogativeVerbMorphology
  /-- Mixture of previous two types (15 languages). -/
  | mixtureOfPreviousTwoTypes
  /-- Interrogative word order (13 languages). -/
  | interrogativeWordOrder
  /-- Absence of declarative morphemes (4 languages). -/
  | absenceOfDeclarativeMorphemes
  /-- Interrogative intonation only (173 languages). -/
  | interrogativeIntonationOnly
  /-- No interrogative-declarative distinction (1 languages). -/
  | noInterrogativeDeclarativeDistinction
  deriving DecidableEq, Repr

/-- Rows 1 to 500 of `allData`. -/
def allData_0 : List (String × PolarQuestionType) :=
  [ ("aab", .questionParticle) -- Arapesh (Abu)
  , ("aar", .interrogativeVerbMorphology) -- Aari
  , ("abk", .interrogativeVerbMorphology) -- Abkhaz
  , ("abu", .questionParticle) -- Abun
  , ("ace", .questionParticle) -- Acehnese
  , ("acn", .questionParticle) -- Achang
  , ("acu", .interrogativeVerbMorphology) -- Achuar
  , ("adi", .questionParticle) -- Adioukrou
  , ("adz", .interrogativeIntonationOnly) -- Adzera
  , ("aeg", .questionParticle) -- Arabic (Egyptian)
  , ("aga", .interrogativeVerbMorphology) -- Agarabi
  , ("agc", .questionParticle) -- Agta (Central)
  , ("agd", .questionParticle) -- Agta (Dupaningan)
  , ("agm", .questionParticle) -- Angami
  , ("ain", .questionParticle) -- Ainu
  , ("ajg", .questionParticle) -- Ajagbe
  , ("akh", .questionParticle) -- Akha
  , ("akn", .questionParticle) -- Akan
  , ("ala", .interrogativeIntonationOnly) -- Alamblak
  , ("alb", .questionParticle) -- Albanian
  , ("alk", .interrogativeIntonationOnly) -- Arop-Lokep
  , ("all", .questionParticle) -- Ala'ala
  , ("aln", .questionParticle) -- Alune
  , ("amb", .questionParticle) -- Ambulas
  , ("amc", .questionParticle) -- Amahuaca
  , ("ame", .questionParticle) -- Amele
  , ("amh", .mixtureOfPreviousTwoTypes) -- Amharic
  , ("aml", .interrogativeIntonationOnly) -- Ambae (Lolovoli Northeast)
  , ("amn", .questionParticle) -- Amanab
  , ("amo", .questionParticle) -- Amo
  , ("amp", .questionParticle) -- Arrernte (Mparntwe)
  , ("amq", .questionParticle) -- Ambai
  , ("amr", .questionParticle) -- Arabic (Moroccan)
  , ("ams", .questionParticle) -- Arabic (Modern Standard)
  , ("amx", .questionParticle) -- Anamuxra
  , ("ana", .interrogativeVerbMorphology) -- Araona
  , ("anc", .questionParticle) -- Angas
  , ("ang", .interrogativeVerbMorphology) -- Anggor
  , ("ani", .questionParticle) -- //Ani
  , ("anj", .questionParticle) -- Anejom
  , ("ann", .questionParticle) -- Anindilyakwa
  , ("ano", .interrogativeIntonationOnly) -- Anong
  , ("anu", .questionParticle) -- Anufo
  , ("ao", .questionParticle) -- Ao
  , ("aoj", .questionParticle) -- Mufian
  , ("api", .questionParticle) -- Apinayé
  , ("apl", .interrogativeIntonationOnly) -- Apalaí
  , ("apt", .questionParticle) -- Apatani
  , ("apu", .interrogativeIntonationOnly) -- Apurinã
  , ("apw", .interrogativeVerbMorphology) -- Apache (Western)
  , ("ara", .interrogativeIntonationOnly) -- Lokono
  , ("arc", .interrogativeVerbMorphology) -- Archi
  , ("arg", .interrogativeIntonationOnly) -- Arabic (Gulf)
  , ("arm", .interrogativeIntonationOnly) -- Armenian (Eastern)
  , ("aro", .questionParticle) -- Arosi
  , ("arp", .questionParticle) -- Arapesh (Mountain)
  , ("arw", .interrogativeIntonationOnly) -- Armenian (Western)
  , ("asm", .questionParticle) -- Asmat
  , ("ass", .interrogativeVerbMorphology) -- Assamese
  , ("asy", .questionParticle) -- Arabic (Syrian)
  , ("ata", .questionParticle) -- Atayal
  , ("ath", .interrogativeVerbMorphology) -- Athpare
  , ("ava", .questionParticle) -- Avar
  , ("avk", .questionParticle) -- Avikam
  , ("awp", .questionParticle) -- Awa Pit
  , ("awt", .questionParticle) -- Awtuw
  , ("aym", .questionParticle) -- Aymara (Central)
  , ("aze", .questionParticle) -- Azerbaijani
  , ("azi", .interrogativeIntonationOnly) -- Azari (Iranian)
  , ("baa", .questionParticle) -- Barai
  , ("bab", .questionParticle) -- Babungo
  , ("bae", .interrogativeIntonationOnly) -- Baré
  , ("baf", .interrogativeIntonationOnly) -- Bafut
  , ("bag", .questionParticle) -- Bagirmi
  , ("bai", .questionParticle) -- Bai
  , ("bam", .questionParticle) -- Bambara
  , ("bao", .interrogativeVerbMorphology) -- Bao'an
  , ("bar", .questionParticle) -- Bari
  , ("baw", .questionParticle) -- Bawm
  , ("bbf", .questionParticle) -- Bobo Madaré (Northern)
  , ("bbw", .questionParticle) -- Bininj Gun-Wok
  , ("bco", .interrogativeVerbMorphology) -- Bella Coola
  , ("bdm", .interrogativeIntonationOnly) -- Badimaya
  , ("bej", .interrogativeVerbMorphology) -- Beja
  , ("bel", .questionParticle) -- Belhare
  , ("bem", .questionParticle) -- Bemba
  , ("ber", .questionParticle) -- Berta
  , ("bfg", .questionParticle) -- Berber (Figuig)
  , ("bgn", .questionParticle) -- Bugun
  , ("bgo", .questionParticle) -- Bongo
  , ("bgz", .interrogativeIntonationOnly) -- Banggi
  , ("bho", .questionParticle) -- Bhojpuri
  , ("bii", .interrogativeIntonationOnly) -- Biri
  , ("bik", .interrogativeIntonationOnly) -- Biak
  , ("bil", .interrogativeIntonationOnly) -- Bilua
  , ("bir", .questionParticle) -- Birom
  , ("biu", .interrogativeVerbMorphology) -- Bisu
  , ("bkn", .questionParticle) -- Bakundu
  , ("bkr", .questionParticle) -- Batak (Karo)
  , ("bla", .interrogativeVerbMorphology) -- Blackfoot
  , ("ble", .interrogativeIntonationOnly) -- Baoulé
  , ("bln", .interrogativeVerbMorphology) -- Bilin
  , ("blr", .questionParticle) -- Belorussian
  , ("blt", .interrogativeVerbMorphology) -- Balti
  , ("blx", .questionParticle) -- Biloxi
  , ("bma", .questionParticle) -- Berber (Middle Atlas)
  , ("bmb", .interrogativeVerbMorphology) -- Bimoba
  , ("bnj", .questionParticle) -- Bandjalang
  , ("bnu", .questionParticle) -- Bularnu
  , ("bod", .interrogativeVerbMorphology) -- Bodo
  , ("bon", .questionParticle) -- Bongu
  , ("bra", .questionParticle) -- Brao
  , ("bre", .questionParticle) -- Breton
  , ("brf", .questionParticle) -- Berber (Rif)
  , ("brm", .interrogativeVerbMorphology) -- Burmese
  , ("brn", .interrogativeVerbMorphology) -- Burunge
  , ("brp", .questionParticle) -- Barupu
  , ("brs", .interrogativeVerbMorphology) -- Barasano
  , ("bsh", .interrogativeIntonationOnly) -- Bushoong
  , ("bsk", .questionParticle) -- Bashkir
  , ("bsq", .questionParticle) -- Basque
  , ("bti", .interrogativeVerbMorphology) -- Betoi
  , ("btk", .questionParticle) -- Bontok
  , ("bud", .questionParticle) -- Buduma
  , ("bug", .questionParticle) -- Bugis
  , ("bul", .questionParticle) -- Bulgarian
  , ("bum", .interrogativeIntonationOnly) -- Buma
  , ("bur", .interrogativeVerbMorphology) -- Burushaski
  , ("bus", .questionParticle) -- Busa
  , ("bwc", .questionParticle) -- Bajau (West Coast)
  , ("bya", .questionParticle) -- Byansi
  , ("cah", .interrogativeIntonationOnly) -- Cahuilla
  , ("cai", .interrogativeIntonationOnly) -- Chai
  , ("can", .interrogativeVerbMorphology) -- Candoshi
  , ("car", .interrogativeVerbMorphology) -- Carib
  , ("cax", .questionParticle) -- Campa (Axininca)
  , ("cba", .interrogativeVerbMorphology) -- Chumash (Barbareño)
  , ("cbo", .questionParticle) -- Chácobo
  , ("ccm", .questionParticle) -- Chinantec (Comaltepec)
  , ("cct", .questionParticle) -- Choctaw
  , ("cea", .questionParticle) -- Cree (Swampy)
  , ("cem", .questionParticle) -- Cèmuhî
  , ("cga", .questionParticle) -- Chaga
  , ("cha", .questionParticle) -- Chamorro
  , ("chc", .interrogativeVerbMorphology) -- Chechen
  , ("che", .questionParticle) -- Cherokee
  , ("chg", .mixtureOfPreviousTwoTypes) -- Chang
  , ("chh", .questionParticle) -- Chaha
  , ("chi", .interrogativeVerbMorphology) -- Chimariko
  , ("chk", .interrogativeIntonationOnly) -- Chukchi
  , ("chn", .mixtureOfPreviousTwoTypes) -- Chantyal
  , ("chp", .questionParticle) -- Chipewyan
  , ("chq", .questionParticle) -- Chinantec (Quiotepec)
  , ("chr", .questionParticle) -- Chrau
  , ("chs", .questionParticle) -- Chin (Siyin)
  , ("chv", .interrogativeVerbMorphology) -- Chuvash
  , ("chw", .questionParticle) -- Cham (Western)
  , ("chx", .questionParticle) -- Chontal (Huamelultec Oaxaca)
  , ("cic", .questionParticle) -- Chichewa
  , ("cle", .questionParticle) -- Chinantec (Lealao)
  , ("cmh", .questionParticle) -- Chemehuevi
  , ("cml", .interrogativeIntonationOnly) -- Camling
  , ("cmn", .questionParticle) -- Comanche
  , ("cmr", .questionParticle) -- Chin (Mara)
  , ("cmy", .interrogativeIntonationOnly) -- Chontal Maya
  , ("cnl", .questionParticle) -- Canela
  , ("cnm", .questionParticle) -- Canamarí
  , ("cnt", .questionParticle) -- Cantonese
  , ("coa", .interrogativeVerbMorphology) -- Coahuilteco
  , ("coc", .questionParticle) -- Cocama
  , ("coo", .questionParticle) -- Coos (Hanis)
  , ("cop", .questionParticle) -- Coptic
  , ("cpl", .interrogativeIntonationOnly) -- Chinantec (Palantla)
  , ("cpy", .interrogativeVerbMorphology) -- Chipaya
  , ("cre", .questionParticle) -- Cree (Plains)
  , ("crn", .questionParticle) -- Cornish
  , ("crp", .interrogativeVerbMorphology) -- Carapana
  , ("cso", .questionParticle) -- Chatino (Sierra Occidental)
  , ("cti", .questionParticle) -- Chin (Tiddim)
  , ("ctl", .interrogativeIntonationOnly) -- Catalan
  , ("ctm", .questionParticle) -- Chitimacha
  , ("cub", .interrogativeVerbMorphology) -- Cubeo
  , ("cup", .interrogativeIntonationOnly) -- Cupeño
  , ("cze", .interrogativeWordOrder) -- Czech
  , ("dan", .questionParticle) -- Dan
  , ("dds", .questionParticle) -- Donno So
  , ("des", .interrogativeVerbMorphology) -- Desano
  , ("deu", .interrogativeVerbMorphology) -- Deuri
  , ("dgr", .questionParticle) -- Dagur
  , ("dha", .interrogativeIntonationOnly) -- Dhaasanac
  , ("dhi", .questionParticle) -- Dhivehi
  , ("die", .interrogativeVerbMorphology) -- Diegueño (Mesa Grande)
  , ("dim", .interrogativeVerbMorphology) -- Dime
  , ("din", .absenceOfDeclarativeMorphemes) -- Dinka
  , ("dio", .interrogativeIntonationOnly) -- Diola-Fogny
  , ("diy", .interrogativeIntonationOnly) -- Diyari
  , ("dji", .questionParticle) -- Djingili
  , ("djm", .interrogativeIntonationOnly) -- Djambarrpuyngu
  , ("djp", .mixtureOfPreviousTwoTypes) -- Djapu
  , ("dlm", .interrogativeIntonationOnly) -- Dla (Menggwa)
  , ("dmk", .questionParticle) -- Domaaki
  , ("dng", .questionParticle) -- Ding
  , ("dni", .interrogativeVerbMorphology) -- Dani (Lower Grand Valley)
  , ("don", .questionParticle) -- Dong (Southern)
  , ("doy", .questionParticle) -- Doyayo
  , ("dre", .questionParticle) -- Drehu
  , ("drm", .questionParticle) -- Darma
  , ("dsh", .interrogativeWordOrder) -- Danish
  , ("duk", .questionParticle) -- Duka
  , ("dul", .questionParticle) -- Dulong
  , ("dum", .questionParticle) -- Dumo
  , ("dun", .questionParticle) -- Duna
  , ("dut", .interrogativeWordOrder) -- Dutch
  , ("dyi", .questionParticle) -- Dyirbal
  , ("ebi", .questionParticle) -- Ebira
  , ("efi", .questionParticle) -- Efik
  , ("ega", .questionParticle) -- Ega
  , ("egn", .questionParticle) -- Engenni
  , ("eip", .interrogativeVerbMorphology) -- Eipo
  , ("emb", .interrogativeVerbMorphology) -- Emberá (Northern)
  , ("eme", .questionParticle) -- Émérillon
  , ("ene", .interrogativeVerbMorphology) -- Enets
  , ("eng", .interrogativeWordOrder) -- English
  , ("eno", .interrogativeIntonationOnly) -- Enggano
  , ("epe", .interrogativeVerbMorphology) -- Epena Pedee
  , ("erk", .interrogativeIntonationOnly) -- Efate (South)
  , ("err", .questionParticle) -- Erromangan
  , ("ese", .questionParticle) -- Ese Ejja
  , ("est", .questionParticle) -- Estonian
  , ("eud", .questionParticle) -- Eudeve
  , ("eve", .questionParticle) -- Evenki
  , ("evn", .questionParticle) -- Even
  , ("ewe", .questionParticle) -- Ewe
  , ("ewo", .questionParticle) -- Ewondo
  , ("fas", .interrogativeVerbMorphology) -- Fasu
  , ("fij", .interrogativeIntonationOnly) -- Fijian
  , ("fin", .questionParticle) -- Finnish
  , ("foe", .interrogativeVerbMorphology) -- Foe
  , ("fre", .questionParticle) -- French
  , ("fri", .interrogativeWordOrder) -- Frisian
  , ("fua", .questionParticle) -- Fulfulde (Adamawa)
  , ("ful", .interrogativeVerbMorphology) -- Fulniô
  , ("fut", .questionParticle) -- Futuna-Aniwa
  , ("fye", .questionParticle) -- Fyem
  , ("gae", .interrogativeVerbMorphology) -- Gaelic (Scots)
  , ("gah", .interrogativeVerbMorphology) -- Gahuku
  , ("gal", .interrogativeVerbMorphology) -- Galo
  , ("gap", .questionParticle) -- Gapapaiwa
  , ("gar", .interrogativeVerbMorphology) -- Garo
  , ("gav", .questionParticle) -- Gavião
  , ("gbb", .questionParticle) -- Gbeya Bossangoa
  , ("gdb", .interrogativeVerbMorphology) -- Gutob
  , ("gds", .interrogativeVerbMorphology) -- Gadsup
  , ("gel", .questionParticle) -- Gela
  , ("geo", .interrogativeIntonationOnly) -- Georgian
  , ("ger", .interrogativeWordOrder) -- German
  , ("ggu", .questionParticle) -- Gureng Gureng
  , ("ghb", .interrogativeIntonationOnly) -- Guahibo
  , ("ghr", .questionParticle) -- Bunan
  , ("gim", .interrogativeVerbMorphology) -- Gimira
  , ("git", .questionParticle) -- Gitksan
  , ("gln", .interrogativeVerbMorphology) -- Golin
  , ("gmw", .interrogativeIntonationOnly) -- Gumawana
  , ("gmz", .interrogativeVerbMorphology) -- Gumuz
  , ("gnb", .interrogativeIntonationOnly) -- Gunbalang
  , ("goa", .questionParticle) -- Goajiro
  , ("goe", .questionParticle) -- Goemai
  , ("gok", .questionParticle) -- Gokana
  , ("gon", .questionParticle) -- Gondi
  , ("grb", .questionParticle) -- Grebo
  , ("grj", .interrogativeIntonationOnly) -- Guarijío
  , ("grk", .questionParticle) -- Greek (Modern)
  , ("grr", .questionParticle) -- Garrwa
  , ("grw", .interrogativeVerbMorphology) -- Greenlandic (West)
  , ("gua", .questionParticle) -- Guaraní
  , ("gud", .questionParticle) -- Gude
  , ("gug", .questionParticle) -- Gugada
  , ("guh", .questionParticle) -- Guhu-Samane
  , ("guj", .interrogativeIntonationOnly) -- Gujarati
  , ("gul", .questionParticle) -- Gula (in Central African Republic)
  , ("gum", .interrogativeIntonationOnly) -- Gumbaynggir
  , ("gur", .questionParticle) -- Gurung
  , ("guw", .questionParticle) -- Gungbe
  , ("gwa", .questionParticle) -- Gwari
  , ("gyc", .interrogativeVerbMorphology) -- Gyarong (Cogtse)
  , ("hai", .questionParticle) -- Haida
  , ("ham", .questionParticle) -- Hamtai
  , ("hat", .questionParticle) -- Hatam
  , ("hau", .questionParticle) -- Hausa
  , ("hay", .interrogativeIntonationOnly) -- Hayu
  , ("hdi", .questionParticle) -- Hdi
  , ("heb", .questionParticle) -- Hebrew (Modern)
  , ("hil", .questionParticle) -- Hiligaynon
  , ("hin", .questionParticle) -- Hindi
  , ("hix", .interrogativeIntonationOnly) -- Hixkaryana
  , ("hma", .questionParticle) -- Hmar
  , ("hmi", .interrogativeIntonationOnly) -- Huitoto (Minica)
  , ("hmo", .questionParticle) -- Hmong Njua
  , ("hna", .questionParticle) -- Mina
  , ("hnd", .questionParticle) -- Hunde
  , ("ho", .questionParticle) -- Ho
  , ("hoa", .interrogativeIntonationOnly) -- Hoava
  , ("hop", .questionParticle) -- Hopi
  , ("hpd", .interrogativeWordOrder) -- Hup
  , ("htc", .interrogativeIntonationOnly) -- Huastec
  , ("hua", .interrogativeVerbMorphology) -- Hua
  , ("huc", .questionParticle) -- =|Hoan
  , ("hun", .questionParticle) -- Hungarian
  , ("hve", .questionParticle) -- Huave (San Mateo del Mar)
  , ("hya", .interrogativeIntonationOnly) -- Haya
  , ("hzb", .interrogativeVerbMorphology) -- Hunzib
  , ("iaa", .questionParticle) -- Iaai
  , ("iba", .questionParticle) -- Iban
  , ("idu", .interrogativeVerbMorphology) -- Idu
  , ("ifm", .questionParticle) -- Ifumu
  , ("ifu", .questionParticle) -- Ifugao (Batad)
  , ("igb", .interrogativeIntonationOnly) -- Igbo
  , ("ige", .questionParticle) -- Igede
  , ("ijo", .interrogativeVerbMorphology) -- Ijo (Kolokuma)
  , ("ik", .questionParticle) -- Ik
  , ("ika", .mixtureOfPreviousTwoTypes) -- Ika
  , ("imo", .questionParticle) -- Imonda
  , ("ina", .questionParticle) -- Inanwatan
  , ("ind", .questionParticle) -- Indonesian
  , ("ing", .interrogativeVerbMorphology) -- Ingush
  , ("iri", .questionParticle) -- Irish
  , ("irq", .interrogativeVerbMorphology) -- Iraqw
  , ("irr", .interrogativeIntonationOnly) -- Irarutu
  , ("ita", .interrogativeIntonationOnly) -- Italian
  , ("ite", .questionParticle) -- Itelmen
  , ("ito", .interrogativeVerbMorphology) -- Itonama
  , ("iwa", .questionParticle) -- Iwaidja
  , ("iwm", .questionParticle) -- Iwam
  , ("izi", .questionParticle) -- Izi
  , ("jab", .questionParticle) -- Jabêm
  , ("jak", .interrogativeIntonationOnly) -- Jakaltek
  , ("jar", .questionParticle) -- Izere
  , ("jeb", .questionParticle) -- Jebero
  , ("jmo", .interrogativeIntonationOnly) -- Jur Mödö
  , ("jms", .questionParticle) -- Jamsay
  , ("jng", .questionParticle) -- Jingpho
  , ("jpn", .questionParticle) -- Japanese
  , ("jug", .interrogativeVerbMorphology) -- Jugli
  , ("juh", .questionParticle) -- Ju|'hoan
  , ("juk", .questionParticle) -- Jukun
  , ("kaa", .questionParticle) -- Karó (Arára)
  , ("kab", .absenceOfDeclarativeMorphemes) -- Kabardian
  , ("kae", .interrogativeVerbMorphology) -- Kaki Ae
  , ("kan", .interrogativeVerbMorphology) -- Kana
  , ("kar", .questionParticle) -- Kara (in Central African Republic)
  , ("kas", .mixtureOfPreviousTwoTypes) -- Kashmiri
  , ("kau", .questionParticle) -- Kaulong
  , ("kay", .interrogativeIntonationOnly) -- Kayardild
  , ("kba", .interrogativeIntonationOnly) -- Kamba
  , ("kbl", .interrogativeIntonationOnly) -- Kabyle
  , ("kbw", .questionParticle) -- Karen (Bwe)
  , ("kby", .questionParticle) -- Kabiyé
  , ("kch", .interrogativeIntonationOnly) -- Koyra Chiini
  , ("kdz", .questionParticle) -- Kadazan
  , ("kel", .questionParticle) -- Kele
  , ("kem", .interrogativeVerbMorphology) -- Kemant
  , ("ken", .questionParticle) -- Kenga
  , ("ker", .questionParticle) -- Kera
  , ("ket", .questionParticle) -- Ket
  , ("kew", .questionParticle) -- Kewa
  , ("kfe", .questionParticle) -- Koromfe
  , ("kgy", .mixtureOfPreviousTwoTypes) -- Kyirong
  , ("kgz", .questionParticle) -- Kirghiz
  , ("kha", .questionParticle) -- Khalkha
  , ("khg", .questionParticle) -- Khaling
  , ("khi", .interrogativeVerbMorphology) -- Khinalug
  , ("khm", .questionParticle) -- Khmer
  , ("khn", .questionParticle) -- Khün
  , ("kho", .questionParticle) -- Nama
  , ("khr", .questionParticle) -- Kharia
  , ("khs", .questionParticle) -- Khasi
  , ("kik", .interrogativeIntonationOnly) -- Kikuyu
  , ("kil", .questionParticle) -- Kiluba
  , ("kim", .questionParticle) -- Kimaghama
  , ("kio", .questionParticle) -- Kiowa
  , ("kis", .interrogativeIntonationOnly) -- Kisi
  , ("kiw", .questionParticle) -- Kiwai (Southern)
  , ("kje", .interrogativeVerbMorphology) -- Koreguaje
  , ("kkp", .interrogativeVerbMorphology) -- Karakalpak
  , ("klm", .questionParticle) -- Klamath
  , ("klv", .interrogativeIntonationOnly) -- Kilivila
  , ("klw", .interrogativeVerbMorphology) -- Kiliwa
  , ("kma", .interrogativeIntonationOnly) -- Kamaiurá
  , ("kmb", .questionParticle) -- Kombai
  , ("kmh", .interrogativeVerbMorphology) -- Kham
  , ("kmj", .questionParticle) -- Karimojong
  , ("kmk", .interrogativeVerbMorphology) -- Kalmyk
  , ("kmn", .interrogativeVerbMorphology) -- Kuman
  , ("kmo", .questionParticle) -- Koiali (Mountain)
  , ("kmr", .interrogativeVerbMorphology) -- Kamoro
  , ("kmu", .questionParticle) -- Khmu'
  , ("kmz", .interrogativeIntonationOnly) -- Kamasau
  , ("knc", .interrogativeIntonationOnly) -- Kugu Nganhcara
  , ("knd", .questionParticle) -- Kannada
  , ("kni", .interrogativeIntonationOnly) -- Konni
  , ("knk", .questionParticle) -- Kanakuru
  , ("knm", .interrogativeVerbMorphology) -- Kunama
  , ("knn", .interrogativeVerbMorphology) -- Kinnauri
  , ("kno", .questionParticle) -- Kanoê
  , ("knr", .interrogativeVerbMorphology) -- Kanuri
  , ("knw", .interrogativeVerbMorphology) -- Konkow
  , ("kob", .questionParticle) -- Kobon
  , ("koe", .interrogativeVerbMorphology) -- Koegu
  , ("kok", .interrogativeVerbMorphology) -- Kokborok
  , ("kol", .interrogativeVerbMorphology) -- Kolami
  , ("kor", .interrogativeVerbMorphology) -- Korean
  , ("kos", .questionParticle) -- Kosraean
  , ("kpw", .questionParticle) -- Karen (Pwo)
  , ("kqq", .interrogativeIntonationOnly) -- Krenak
  , ("krc", .interrogativeVerbMorphology) -- Karachay-Balkar
  , ("kre", .questionParticle) -- Kresh
  , ("krj", .questionParticle) -- Karadjeri
  , ("krn", .questionParticle) -- Korana
  , ("kro", .interrogativeVerbMorphology) -- Krongo
  , ("krw", .questionParticle) -- Korowai
  , ("ksa", .questionParticle) -- Keresan (Santa Ana)
  , ("kse", .questionParticle) -- Koyraboro Senni
  , ("ksg", .questionParticle) -- Karen (Sgaw)
  , ("ksm", .questionParticle) -- Kasem
  , ("ksn", .questionParticle) -- Kasong
  , ("kta", .questionParticle) -- Koita
  , ("kum", .questionParticle) -- Kumauni
  , ("kun", .interrogativeIntonationOnly) -- Kuna
  , ("kuo", .interrogativeIntonationOnly) -- Kuot
  , ("kut", .questionParticle) -- Kutenai
  , ("kuu", .interrogativeIntonationOnly) -- Kuuku Ya'u
  , ("kuv", .questionParticle) -- Kuvi
  , ("kwn", .questionParticle) -- Kwangali
  , ("kwo", .questionParticle) -- Kwoma
  , ("kws", .interrogativeIntonationOnly) -- Kawaiisu
  , ("kwz", .interrogativeVerbMorphology) -- Kwaza
  , ("kxo", .questionParticle) -- Kxoe
  , ("kya", .questionParticle) -- Kuku-Yalanji
  , ("kyk", .interrogativeVerbMorphology) -- Kyaka
  , ("kyl", .questionParticle) -- Kayah Li (Eastern)
  , ("kyp", .questionParticle) -- Kayapó
  , ("kyz", .questionParticle) -- Kayabí
  , ("laa", .questionParticle) -- Laal
  , ("lab", .interrogativeIntonationOnly) -- Labu
  , ("lac", .questionParticle) -- Lacandón
  , ("lad", .interrogativeVerbMorphology) -- Ladakhi
  , ("lag", .questionParticle) -- Lagwan
  , ("lah", .questionParticle) -- Lahu
  , ("lai", .questionParticle) -- Lai
  , ("lal", .questionParticle) -- Lalo
  , ("lan", .interrogativeIntonationOnly) -- Lango
  , ("lao", .questionParticle) -- Lao
  , ("lat", .questionParticle) -- Latvian
  , ("lav", .questionParticle) -- Lavukaleve
  , ("lbu", .interrogativeIntonationOnly) -- Lunda
  , ("ldo", .questionParticle) -- Londo
  , ("ldu", .questionParticle) -- Lendu
  , ("lel", .questionParticle) -- Lele
  , ("len", .questionParticle) -- Lenakel
  , ("lep", .questionParticle) -- Lepcha
  , ("lew", .questionParticle) -- Lewo
  , ("lez", .interrogativeVerbMorphology) -- Lezgian
  , ("lgt", .questionParticle) -- Logoti
  , ("lho", .interrogativeVerbMorphology) -- Lhomi
  , ("lin", .interrogativeIntonationOnly) -- Lingala
  , ("lis", .interrogativeVerbMorphology) -- Lisu
  , ("lit", .questionParticle) -- Lithuanian
  , ("lkt", .questionParticle) -- Lakhota
  , ("lmb", .questionParticle) -- Lamba
  , ("lmg", .questionParticle) -- Lamang
  , ("lmh", .interrogativeIntonationOnly) -- Lamaholot
  , ("lmn", .questionParticle) -- Lamani
  , ("lmp", .questionParticle) -- Lampung
  , ("lnd", .questionParticle) -- Linda
  , ("lon", .interrogativeIntonationOnly) -- Loniu
  , ("lot", .interrogativeVerbMorphology) -- Lotha
  , ("loz", .questionParticle) -- Lozi
  , ("lug", .questionParticle) -- Lugbara
  , ("lui", .questionParticle) -- Luiseño
  , ("lun", .questionParticle) -- Lungchang
  , ("luo", .interrogativeIntonationOnly) -- Luo
  , ("luv", .questionParticle) -- Luvale
  , ("maa", .questionParticle) -- Maasai
  , ("mab", .interrogativeVerbMorphology) -- Maba
  , ("mac", .interrogativeIntonationOnly) -- Macushi
  , ("mad", .questionParticle) -- Ma'di
  , ("mae", .questionParticle) -- Mae
  , ("maj", .questionParticle) -- Majang
  , ("mak", .questionParticle) -- Makah
  , ("mal", .questionParticle) -- Malagasy
  , ("mam", .questionParticle) -- Mam
  , ("man", .interrogativeIntonationOnly) -- Mano
  , ("mao", .interrogativeIntonationOnly) -- Maori
  , ("map", .questionParticle) -- Mapudungun
  , ("mar", .interrogativeVerbMorphology) -- Maricopa
  , ("mas", .questionParticle) -- Masa
  , ("mau", .questionParticle) -- Maung
  , ("maw", .questionParticle) -- Maninka (Western)
  , ("max", .questionParticle) -- Maxakalí
  , ("may", .questionParticle) -- Maybrat
  ]

/-- Rows 501 to 955 of `allData`. -/
def allData_1 : List (String × PolarQuestionType) :=
  [ ("mbi", .questionParticle) -- Mbili
  , ("mbm", .questionParticle) -- Mbum
  , ("mbr", .questionParticle) -- Mbara
  , ("mby", .questionParticle) -- Mbay
  , ("mcc", .questionParticle) -- Mochica
  , ("mcd", .questionParticle) -- Macedonian
  , ("mco", .questionParticle) -- Mixe (Coatlán)
  , ("mde", .interrogativeIntonationOnly) -- Mende
  , ("mdn", .interrogativeVerbMorphology) -- Mandan
  , ("mdo", .questionParticle) -- Mbodomo
  , ("mds", .questionParticle) -- Manadonese
  , ("mea", .questionParticle) -- Meyah
  , ("mee", .questionParticle) -- Me'en
  , ("meh", .interrogativeIntonationOnly) -- Mehri
  , ("mei", .questionParticle) -- Meithei
  , ("mek", .questionParticle) -- Mekens
  , ("men", .interrogativeVerbMorphology) -- Menomini
  , ("mer", .interrogativeIntonationOnly) -- Meryam Mir
  , ("mey", .questionParticle) -- Menya
  , ("mgg", .interrogativeVerbMorphology) -- Mangghuer
  , ("mgk", .questionParticle) -- Mungaka
  , ("mgu", .questionParticle) -- Musgu
  , ("mhi", .questionParticle) -- Marathi
  , ("mie", .questionParticle) -- Mien
  , ("mik", .interrogativeVerbMorphology) -- Mikir
  , ("mir", .questionParticle) -- Miriwung
  , ("mis", .mixtureOfPreviousTwoTypes) -- Miskito
  , ("miy", .questionParticle) -- Miya
  , ("miz", .questionParticle) -- Mizo
  , ("mka", .questionParticle) -- Mauka
  , ("mke", .questionParticle) -- Mekeo
  , ("mkh", .questionParticle) -- Mongol (Khamnigan)
  , ("mkj", .questionParticle) -- Makasae
  , ("mku", .interrogativeIntonationOnly) -- Maranungku
  , ("mlg", .interrogativeIntonationOnly) -- Malgwa
  , ("mmb", .questionParticle) -- Mangap-Mbula
  , ("mmi", .questionParticle) -- Mambai
  , ("mmn", .questionParticle) -- Mamanwa
  , ("mmv", .questionParticle) -- Mamvu
  , ("mna", .interrogativeIntonationOnly) -- Muna
  , ("mnc", .interrogativeVerbMorphology) -- Manchu
  , ("mnd", .questionParticle) -- Mandarin
  , ("mne", .interrogativeVerbMorphology) -- Maidu (Northeast)
  , ("mng", .interrogativeWordOrder) -- Manggarai
  , ("mni", .interrogativeVerbMorphology) -- Moni
  , ("mnm", .interrogativeIntonationOnly) -- Manam
  , ("mno", .questionParticle) -- Mono (in United States)
  , ("mns", .mixtureOfPreviousTwoTypes) -- Mansi
  , ("mny", .questionParticle) -- Margany
  , ("mok", .questionParticle) -- Mokilese
  , ("mon", .questionParticle) -- Mon
  , ("moo", .questionParticle) -- Mooré
  , ("mor", .questionParticle) -- Mor
  , ("mos", .questionParticle) -- Mosetén
  , ("mou", .questionParticle) -- Moru
  , ("mov", .interrogativeIntonationOnly) -- Movima
  , ("mpa", .questionParticle) -- Murrinh-Patha
  , ("mpr", .questionParticle) -- Maipure
  , ("mpt", .questionParticle) -- Mian
  , ("mpu", .questionParticle) -- Mpur
  , ("mra", .interrogativeIntonationOnly) -- Mara
  , ("mrd", .mixtureOfPreviousTwoTypes) -- Marind
  , ("mrg", .questionParticle) -- Margi
  , ("mri", .questionParticle) -- Moraori
  , ("mrl", .interrogativeIntonationOnly) -- Murle
  , ("mro", .mixtureOfPreviousTwoTypes) -- Moro
  , ("mrq", .questionParticle) -- Marquesan
  , ("mrt", .interrogativeIntonationOnly) -- Martuthunira
  , ("mru", .questionParticle) -- Maru
  , ("mrw", .questionParticle) -- Muruwari
  , ("msc", .interrogativeVerbMorphology) -- Muisca
  , ("msg", .interrogativeVerbMorphology) -- Mising
  , ("msl", .interrogativeVerbMorphology) -- Masalit
  , ("msn", .questionParticle) -- Maisin
  , ("mts", .interrogativeVerbMorphology) -- Matis
  , ("mtt", .interrogativeVerbMorphology) -- Massachusett
  , ("mtu", .questionParticle) -- Motu
  , ("mum", .questionParticle) -- Mumuye
  , ("mun", .questionParticle) -- Mundari
  , ("mup", .questionParticle) -- Mupun
  , ("mus", .questionParticle) -- Mussau
  , ("mut", .questionParticle) -- Mutsun
  , ("mwb", .questionParticle) -- Manobo (Western Bukidnon)
  , ("mwo", .interrogativeIntonationOnly) -- Mwotlap
  , ("mxc", .noInterrogativeDeclarativeDistinction) -- Mixtec (Chalcatongo)
  , ("mxj", .questionParticle) -- Mixtec (Jicaltepec)
  , ("mxo", .questionParticle) -- Mixtec (Ocotepec)
  , ("mxp", .questionParticle) -- Mixtec (Peñoles)
  , ("mxx", .questionParticle) -- Mixe (Ayutla)
  , ("mxy", .questionParticle) -- Mixtec (Yosondúa)
  , ("myi", .questionParticle) -- Mangarrayi
  , ("mym", .questionParticle) -- Malayalam
  , ("mzh", .questionParticle) -- Mazatec (Huautla)
  , ("nab", .interrogativeIntonationOnly) -- Nabak
  , ("nad", .interrogativeIntonationOnly) -- Nadëb
  , ("nag", .questionParticle) -- Nagatman
  , ("naj", .interrogativeIntonationOnly) -- Neo-Aramaic (Arbel Jewish)
  , ("nam", .questionParticle) -- Namia
  , ("nan", .questionParticle) -- Nandi
  , ("nar", .questionParticle) -- Nara (in Ethiopia)
  , ("nas", .questionParticle) -- Nasioi
  , ("nav", .questionParticle) -- Navajo
  , ("nax", .questionParticle) -- Naxi
  , ("nbd", .interrogativeVerbMorphology) -- Nubian (Dongolese)
  , ("nbm", .questionParticle) -- Ngbaka (Ma'bo)
  , ("ncm", .questionParticle) -- Ncàm
  , ("ndb", .questionParticle) -- Ndebele
  , ("ndi", .interrogativeIntonationOnly) -- Ngbandi
  , ("ndj", .interrogativeIntonationOnly) -- Ndjébbana
  , ("ndr", .interrogativeIntonationOnly) -- Nadroga
  , ("ndy", .interrogativeIntonationOnly) -- Ndyuka
  , ("nep", .questionParticle) -- Nepali
  , ("nev", .questionParticle) -- Nevome
  , ("new", .questionParticle) -- Newari (Kathmandu)
  , ("ney", .questionParticle) -- Neyo
  , ("nez", .questionParticle) -- Nez Perce
  , ("nga", .interrogativeVerbMorphology) -- Nganasan
  , ("ngb", .questionParticle) -- Ngbaka (Minagende)
  , ("ngd", .interrogativeIntonationOnly) -- Ngad'a
  , ("ngi", .questionParticle) -- Ngiyambaa
  , ("ngk", .interrogativeIntonationOnly) -- Ngankikurungkurr
  , ("ngm", .questionParticle) -- Ngambay
  , ("ngn", .questionParticle) -- Ngandi
  , ("ngo", .interrogativeIntonationOnly) -- Ngoni
  , ("ngt", .interrogativeVerbMorphology) -- Naga (Tangkhul)
  , ("ngz", .interrogativeIntonationOnly) -- Ngizim
  , ("nha", .interrogativeIntonationOnly) -- Nhanda
  , ("nht", .interrogativeIntonationOnly) -- Nahuatl (Tetelcingo)
  , ("nia", .questionParticle) -- Nias
  , ("nif", .interrogativeIntonationOnly) -- Niuafo'ou
  , ("niu", .questionParticle) -- Niuean
  , ("niv", .questionParticle) -- Nivkh
  , ("nkb", .questionParticle) -- Ngalkbun
  , ("nke", .questionParticle) -- Nkem
  , ("nkn", .questionParticle) -- Nkonya
  , ("nko", .questionParticle) -- Nkore-Kiga
  , ("nma", .questionParticle) -- Naga (Mao)
  , ("nmb", .interrogativeVerbMorphology) -- Nambikuára (Southern)
  , ("nnc", .questionParticle) -- Nancowry
  , ("nnd", .interrogativeVerbMorphology) -- Nend
  , ("nnk", .interrogativeIntonationOnly) -- Nankina
  , ("noc", .interrogativeVerbMorphology) -- Nocte
  , ("non", .questionParticle) -- Noni
  , ("noo", .questionParticle) -- Noon
  , ("nor", .interrogativeWordOrder) -- Norwegian
  , ("nph", .interrogativeVerbMorphology) -- Nar-Phu
  , ("nsg", .questionParticle) -- Nisgha
  , ("nsn", .questionParticle) -- Nisenan
  , ("nti", .questionParticle) -- Ngiti
  , ("nua", .interrogativeIntonationOnly) -- Nuaulu
  , ("nug", .questionParticle) -- Nunggubuyu
  , ("nun", .questionParticle) -- Nung (in Vietnam)
  , ("nup", .questionParticle) -- Nupe
  , ("nwd", .questionParticle) -- Newar (Dolakha)
  , ("nyk", .interrogativeVerbMorphology) -- Nyamkad
  , ("nyn", .questionParticle) -- Nyigina
  , ("nyu", .questionParticle) -- Nyulnyul
  , ("nze", .questionParticle) -- Naga (Zeme)
  , ("obg", .questionParticle) -- Ogbronuagum
  , ("obo", .questionParticle) -- Obolo
  , ("ocu", .questionParticle) -- Ocuilteco
  , ("oji", .questionParticle) -- Ojibwa (Eastern)
  , ("olo", .questionParticle) -- Olo
  , ("omh", .questionParticle) -- Omaha
  , ("omi", .questionParticle) -- Ömie
  , ("ond", .questionParticle) -- Oneida
  , ("ong", .mixtureOfPreviousTwoTypes) -- Onge
  , ("ood", .questionParticle) -- O'odham
  , ("ora", .interrogativeIntonationOnly) -- Emai
  , ("orh", .interrogativeIntonationOnly) -- Oromo (Harar)
  , ("oro", .mixtureOfPreviousTwoTypes) -- Orokaiva
  , ("osa", .interrogativeIntonationOnly) -- Osage
  , ("otm", .questionParticle) -- Otomí (Mezquital)
  , ("oya", .questionParticle) -- Oriya
  , ("paa", .interrogativeIntonationOnly) -- Pa'a
  , ("pae", .interrogativeVerbMorphology) -- Páez
  , ("pai", .interrogativeIntonationOnly) -- Paiwan
  , ("pal", .interrogativeWordOrder) -- Palauan
  , ("pan", .questionParticle) -- Panjabi
  , ("par", .interrogativeIntonationOnly) -- Päri
  , ("pau", .interrogativeVerbMorphology) -- Paumarí
  , ("paw", .interrogativeVerbMorphology) -- Pawaian
  , ("pdp", .interrogativeVerbMorphology) -- Folopa
  , ("per", .questionParticle) -- Pero
  , ("pga", .questionParticle) -- Pilagá
  , ("pip", .interrogativeIntonationOnly) -- Pipil
  , ("pir", .questionParticle) -- Piro
  , ("pis", .questionParticle) -- Pisa
  , ("plk", .questionParticle) -- Palikur
  , ("pme", .interrogativeVerbMorphology) -- Pomo (Eastern)
  , ("pms", .interrogativeIntonationOnly) -- Paamese
  , ("pno", .questionParticle) -- Paiute (Northern)
  , ("pnx", .questionParticle) -- Panará
  , ("pod", .questionParticle) -- Podoko
  , ("poh", .interrogativeIntonationOnly) -- Pohnpeian
  , ("pok", .questionParticle) -- Poko-Rawo
  , ("pol", .questionParticle) -- Polish
  , ("por", .questionParticle) -- Portuguese
  , ("ppi", .interrogativeIntonationOnly) -- Pitta Pitta
  , ("prh", .mixtureOfPreviousTwoTypes) -- Pirahã
  , ("prk", .interrogativeVerbMorphology) -- Purki
  , ("prs", .questionParticle) -- Persian
  , ("psh", .interrogativeIntonationOnly) -- Pashto
  , ("pso", .interrogativeVerbMorphology) -- Pomo (Southeastern)
  , ("psw", .interrogativeIntonationOnly) -- Port Sandwich
  , ("ptt", .interrogativeVerbMorphology) -- Pattani
  , ("pum", .questionParticle) -- Pumi
  , ("puq", .absenceOfDeclarativeMorphemes) -- Puquina
  , ("qaw", .interrogativeVerbMorphology) -- Qawasqar
  , ("qhu", .interrogativeVerbMorphology) -- Quechua (Huallaga)
  , ("qia", .interrogativeVerbMorphology) -- Qiang
  , ("qim", .questionParticle) -- Quechua (Imbabura)
  , ("qui", .interrogativeVerbMorphology) -- Quileute
  , ("qum", .questionParticle) -- Sipakapense
  , ("rap", .questionParticle) -- Rapanui
  , ("raw", .questionParticle) -- Rawang
  , ("rem", .interrogativeVerbMorphology) -- Remo
  , ("res", .questionParticle) -- Resígaro
  , ("ret", .questionParticle) -- Retuarã
  , ("rit", .questionParticle) -- Ritharngu
  , ("rny", .interrogativeIntonationOnly) -- Runyankore
  , ("rom", .interrogativeIntonationOnly) -- Romanian
  , ("ron", .questionParticle) -- Ron
  , ("rot", .questionParticle) -- Rotuman
  , ("rov", .interrogativeIntonationOnly) -- Roviana
  , ("ruk", .interrogativeIntonationOnly) -- Rukai (Tanan)
  , ("rum", .questionParticle) -- Rumu
  , ("run", .interrogativeVerbMorphology) -- Runga
  , ("rus", .questionParticle) -- Russian
  , ("rwe", .questionParticle) -- Romani (Welsh)
  , ("ryu", .interrogativeVerbMorphology) -- Shuri
  , ("sah", .interrogativeIntonationOnly) -- Sahu
  , ("sal", .interrogativeVerbMorphology) -- Salinan
  , ("sam", .questionParticle) -- Samoan
  , ("san", .questionParticle) -- Sango
  , ("sap", .questionParticle) -- Sapuan
  , ("sar", .interrogativeIntonationOnly) -- Sare
  , ("scr", .questionParticle) -- Serbian-Croatian
  , ("sea", .interrogativeIntonationOnly) -- Southeast Ambrym
  , ("sed", .questionParticle) -- Sedang
  , ("sem", .questionParticle) -- Sema
  , ("ser", .questionParticle) -- Seri
  , ("ses", .interrogativeIntonationOnly) -- Sesotho
  , ("sgb", .questionParticle) -- Sougb
  , ("she", .questionParticle) -- Sherpa
  , ("shh", .questionParticle) -- Sharanahua
  , ("shi", .questionParticle) -- Shiriana
  , ("shk", .questionParticle) -- Shipibo-Konibo
  , ("shl", .interrogativeIntonationOnly) -- Shilluk
  , ("shu", .questionParticle) -- Shuswap
  , ("sia", .interrogativeVerbMorphology) -- Siane
  , ("sid", .interrogativeIntonationOnly) -- Sidaama
  , ("sio", .questionParticle) -- Sio
  , ("sis", .questionParticle) -- Sisiqa
  , ("siu", .questionParticle) -- Siuslaw
  , ("skk", .questionParticle) -- Sikkimese
  , ("sko", .questionParticle) -- Skou
  , ("skw", .interrogativeIntonationOnly) -- Shekhawati
  , ("sla", .questionParticle) -- Slave
  , ("slb", .questionParticle) -- Saliba (in Papua New Guinea)
  , ("sle", .questionParticle) -- Samba Leko
  , ("slg", .questionParticle) -- Sulung
  , ("slo", .questionParticle) -- Slovene
  , ("sml", .interrogativeIntonationOnly) -- Semelai
  , ("smn", .interrogativeVerbMorphology) -- Seminole
  , ("sna", .interrogativeVerbMorphology) -- Shina
  , ("sng", .questionParticle) -- Sinaugoro
  , ("snm", .interrogativeIntonationOnly) -- Sanuma
  , ("snn", .questionParticle) -- Soninke
  , ("sno", .questionParticle) -- Saami (Northern)
  , ("so", .questionParticle) -- So
  , ("sob", .questionParticle) -- Sobei
  , ("som", .questionParticle) -- Somali
  , ("son", .questionParticle) -- Sonsorol-Tobi
  , ("spa", .interrogativeWordOrder) -- Spanish
  , ("squ", .questionParticle) -- Squamish
  , ("src", .interrogativeVerbMorphology) -- Sarcee
  , ("srd", .questionParticle) -- Sardinian
  , ("sre", .questionParticle) -- Sre
  , ("srn", .questionParticle) -- Sirionó
  , ("sro", .questionParticle) -- Siroi
  , ("sta", .interrogativeVerbMorphology) -- Santa
  , ("sti", .questionParticle) -- Stieng
  , ("stl", .interrogativeVerbMorphology) -- Santali
  , ("sud", .interrogativeIntonationOnly) -- Sudest
  , ("sue", .interrogativeVerbMorphology) -- Suena
  , ("sul", .interrogativeIntonationOnly) -- Sulka
  , ("sun", .questionParticle) -- Sundanese
  , ("sup", .questionParticle) -- Supyire
  , ("svs", .interrogativeIntonationOnly) -- Savosavo
  , ("swa", .questionParticle) -- Swahili
  , ("swe", .interrogativeWordOrder) -- Swedish
  , ("swt", .questionParticle) -- Swati
  , ("syu", .interrogativeVerbMorphology) -- Salt-Yui
  , ("tab", .interrogativeIntonationOnly) -- Taba
  , ("tac", .questionParticle) -- Tacana
  , ("taf", .interrogativeIntonationOnly) -- Taiof
  , ("tag", .questionParticle) -- Tagalog
  , ("tah", .questionParticle) -- Tahitian
  , ("tai", .interrogativeIntonationOnly) -- Tuareg (Air)
  , ("taj", .questionParticle) -- Tajik
  , ("tak", .questionParticle) -- Takia
  , ("tam", .questionParticle) -- Tamang (Eastern)
  , ("tao", .questionParticle) -- Tarao
  , ("tar", .interrogativeIntonationOnly) -- Tariana
  , ("tas", .mixtureOfPreviousTwoTypes) -- Tashlhiyt
  , ("tat", .questionParticle) -- Tatana'
  , ("tau", .questionParticle) -- Tauya
  , ("tbo", .questionParticle) -- Tboli
  , ("tbt", .interrogativeIntonationOnly) -- Tobati
  , ("tbu", .questionParticle) -- Tubu
  , ("tbw", .interrogativeIntonationOnly) -- Tabwa
  , ("tbx", .interrogativeVerbMorphology) -- Tangbe
  , ("tee", .questionParticle) -- Tepehua (Huehuetla)
  , ("tel", .interrogativeVerbMorphology) -- Telugu
  , ("ten", .interrogativeIntonationOnly) -- Tennet
  , ("teo", .interrogativeIntonationOnly) -- Teop
  , ("ter", .questionParticle) -- Tera
  , ("tet", .questionParticle) -- Tetela
  , ("tgh", .questionParticle) -- Tuareg (Ghat)
  , ("tgk", .questionParticle) -- Tigak
  , ("tgl", .questionParticle) -- Tshangla
  , ("tha", .questionParticle) -- Thai
  , ("tho", .questionParticle) -- Thompson
  , ("thy", .interrogativeIntonationOnly) -- Kuuk Thaayorre
  , ("tib", .questionParticle) -- Tibetan (Standard Spoken)
  , ("tid", .interrogativeIntonationOnly) -- Tidore
  , ("tim", .questionParticle) -- Timugon
  , ("tin", .questionParticle) -- Tinrin
  , ("tir", .interrogativeIntonationOnly) -- Tiriyo
  , ("tiw", .questionParticle) -- Tiwi
  , ("tja", .questionParticle) -- Tiipay (Jamul)
  , ("tke", .interrogativeIntonationOnly) -- Tokelauan
  , ("tkl", .questionParticle) -- Takelma
  , ("tla", .questionParticle) -- Tolai
  , ("tlp", .questionParticle) -- Tlapanec
  , ("tml", .interrogativeVerbMorphology) -- Tamil
  , ("tmo", .interrogativeVerbMorphology) -- Tibetan (Modern Literary)
  , ("tna", .questionParticle) -- Turkana
  , ("tne", .questionParticle) -- Temne
  , ("tni", .interrogativeVerbMorphology) -- Tinani
  , ("tnn", .questionParticle) -- Tunen
  , ("tny", .questionParticle) -- Tenyer
  , ("tob", .interrogativeIntonationOnly) -- Toba
  , ("ton", .interrogativeVerbMorphology) -- Tonkawa
  , ("toz", .questionParticle) -- Tonga (in Zambia)
  , ("tpn", .questionParticle) -- Tepehuan (Northern)
  , ("tps", .interrogativeIntonationOnly) -- Tepehuan (Southeastern)
  , ("trb", .questionParticle) -- Teribe
  , ("tri", .questionParticle) -- Trique (Copala)
  , ("tsf", .interrogativeVerbMorphology) -- Tsafiki
  , ("tsh", .questionParticle) -- Tümpisa Shoshone
  , ("tsi", .interrogativeIntonationOnly) -- Tsimshian (Coast)
  , ("tsk", .questionParticle) -- Tamashek
  , ("tsn", .questionParticle) -- Tsonga
  , ("tsz", .interrogativeVerbMorphology) -- Tsez
  , ("tte", .interrogativeVerbMorphology) -- Tutelo
  , ("ttn", .questionParticle) -- Tetun
  , ("ttu", .questionParticle) -- Tsova-Tush
  , ("tuc", .interrogativeVerbMorphology) -- Tucano
  , ("tuk", .questionParticle) -- Tukang Besi
  , ("tun", .interrogativeVerbMorphology) -- Tunica
  , ("tur", .questionParticle) -- Turkish
  , ("tus", .questionParticle) -- Tuscarora
  , ("tuv", .questionParticle) -- Tuvan
  , ("tuy", .interrogativeVerbMorphology) -- Tuyuca
  , ("tvl", .interrogativeIntonationOnly) -- Tuvaluan
  , ("tvo", .questionParticle) -- Tatar
  , ("tvt", .questionParticle) -- Tutsa
  , ("twe", .questionParticle) -- Tarahumara (Western)
  , ("txj", .questionParticle) -- Totonac (Xicotepec de Juárez)
  , ("tzo", .questionParticle) -- Tzotzil
  , ("tzu", .questionParticle) -- Tzutujil
  , ("uby", .interrogativeVerbMorphology) -- Ubykh
  , ("udh", .interrogativeIntonationOnly) -- Udihe
  , ("ukr", .questionParticle) -- Ukrainian
  , ("uld", .questionParticle) -- Uldeme
  , ("uli", .interrogativeIntonationOnly) -- Ulithian
  , ("una", .interrogativeVerbMorphology) -- Una
  , ("urd", .questionParticle) -- Urdu
  , ("urk", .questionParticle) -- Urubú-Kaapor
  , ("url", .questionParticle) -- Urak Lawoi'
  , ("urt", .questionParticle) -- Urat
  , ("usa", .interrogativeIntonationOnly) -- Usan
  , ("usr", .interrogativeVerbMorphology) -- Usarufa
  , ("ute", .questionParticle) -- Ute
  , ("uzb", .interrogativeVerbMorphology) -- Uzbek
  , ("vie", .questionParticle) -- Vietnamese
  , ("vnm", .interrogativeIntonationOnly) -- Vinmavis
  , ("wah", .questionParticle) -- Wahgi
  , ("wak", .interrogativeVerbMorphology) -- Wakhi
  , ("wal", .questionParticle) -- Walman
  , ("wao", .interrogativeVerbMorphology) -- Waorani
  , ("wap", .interrogativeVerbMorphology) -- Wappo
  , ("war", .interrogativeIntonationOnly) -- Wari'
  , ("was", .questionParticle) -- Washo
  , ("way", .questionParticle) -- Wayampi
  , ("wbn", .questionParticle) -- Wambon
  , ("wch", .questionParticle) -- Wichí
  , ("wel", .questionParticle) -- Welsh
  , ("wem", .interrogativeIntonationOnly) -- Wembawemba
  , ("wic", .questionParticle) -- Wichita
  , ("wik", .questionParticle) -- Wikchamni
  , ("wiy", .questionParticle) -- Wiyot
  , ("wlf", .questionParticle) -- Wolof
  , ("wly", .interrogativeVerbMorphology) -- Wolaytta
  , ("wma", .interrogativeIntonationOnly) -- West Makian
  , ("wn", .questionParticle) -- Wik Ngathana
  , ("wol", .interrogativeIntonationOnly) -- Woleaian
  , ("wra", .interrogativeVerbMorphology) -- Warao
  , ("wrg", .interrogativeIntonationOnly) -- Warrgamay
  , ("wrk", .interrogativeWordOrder) -- Warekena
  , ("wrl", .questionParticle) -- Warlpiri
  , ("wrn", .interrogativeIntonationOnly) -- Warndarang
  , ("wsk", .questionParticle) -- Waskia
  , ("wth", .questionParticle) -- Wathawurrung
  , ("wtm", .interrogativeVerbMorphology) -- Watam
  , ("wwa", .questionParticle) -- Waama
  , ("xas", .questionParticle) -- Xasonga
  , ("xav", .questionParticle) -- Xavánte
  , ("xbi", .interrogativeIntonationOnly) -- Kombio
  , ("xho", .questionParticle) -- Xhosa
  , ("xoo", .questionParticle) -- !Xóõ
  , ("yag", .questionParticle) -- Yagua
  , ("yal", .interrogativeVerbMorphology) -- Yale (Kosarek)
  , ("yap", .interrogativeIntonationOnly) -- Yapese
  , ("yaq", .questionParticle) -- Yaqui
  , ("yar", .questionParticle) -- Yareba
  , ("ygr", .questionParticle) -- Yagaria
  , ("yid", .interrogativeIntonationOnly) -- Yidiny
  , ("yin", .questionParticle) -- Yindjibarndi
  , ("yiw", .questionParticle) -- Yi (Wuding-Luquan)
  , ("yko", .interrogativeIntonationOnly) -- Yukaghir (Kolyma)
  , ("yng", .interrogativeIntonationOnly) -- Yingkarta
  , ("yok", .questionParticle) -- Yokuts (Yaudanchi)
  , ("yor", .interrogativeIntonationOnly) -- Yoruba
  , ("ypk", .questionParticle) -- Yup'ik (Central)
  , ("yqy", .questionParticle) -- Yaqay
  , ("yuc", .questionParticle) -- Yuchi
  , ("yuk", .questionParticle) -- Yukulta
  , ("yul", .questionParticle) -- Yulu
  , ("yur", .questionParticle) -- Yurok
  , ("yuw", .questionParticle) -- Yuwaalaraay
  , ("ywl", .questionParticle) -- Yawelmani
  , ("zag", .interrogativeVerbMorphology) -- Beria
  , ("zai", .questionParticle) -- Zapotec (Isthmus)
  , ("zap", .questionParticle) -- Zapotec (Mitla)
  , ("zay", .absenceOfDeclarativeMorphemes) -- Zayse
  , ("zaz", .interrogativeIntonationOnly) -- Zazaki
  , ("zch", .interrogativeIntonationOnly) -- Zoque (Chimalapa)
  , ("zhn", .questionParticle) -- Zhuang (Northern)
  , ("zqc", .interrogativeVerbMorphology) -- Zoque (Copainalá)
  , ("zul", .questionParticle) -- Zulu
  , ("zya", .questionParticle) -- Zapotec (Yatzachi)
  , ("zzo", .interrogativeIntonationOnly) -- Zapotec (Zoogocho)
  ]

/-- The WALS 116A coding: each language's value, keyed by its WALS code (955 languages). -/
def allData : List (String × PolarQuestionType) := allData_0 ++ allData_1

end Data.WALS.F116A
