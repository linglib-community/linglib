module

/-!
# WALS Feature 92A: Position of Polar Question Particles
[dryer-2013-wals]

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 92A`.

Chapter 92, 884 languages.
-/

@[expose] public section

namespace Data.WALS.F92A

/-- WALS 92A values. -/
inductive QuestionParticlePosition where
  /-- Initial (129 languages). -/
  | initial
  /-- Final (314 languages). -/
  | final
  /-- Second position (52 languages). -/
  | secondPosition
  /-- Other position (8 languages). -/
  | otherPosition
  /-- In either of two positions (26 languages). -/
  | inEitherOfTwoPositions
  /-- No question particle (355 languages). -/
  | noQuestionParticle
  deriving DecidableEq, Repr

/-- Rows 1 to 500 of `allData`. -/
def allData_0 : List (String × QuestionParticlePosition) :=
  [ ("aab", .final) -- Arapesh (Abu)
  , ("aar", .noQuestionParticle) -- Aari
  , ("abk", .noQuestionParticle) -- Abkhaz
  , ("abu", .final) -- Abun
  , ("ace", .inEitherOfTwoPositions) -- Acehnese
  , ("acn", .final) -- Achang
  , ("acu", .noQuestionParticle) -- Achuar
  , ("adi", .final) -- Adioukrou
  , ("adz", .noQuestionParticle) -- Adzera
  , ("aeg", .initial) -- Arabic (Egyptian)
  , ("aga", .noQuestionParticle) -- Agarabi
  , ("agc", .initial) -- Agta (Central)
  , ("agd", .secondPosition) -- Agta (Dupaningan)
  , ("agm", .final) -- Angami
  , ("ain", .final) -- Ainu
  , ("ajg", .final) -- Ajagbe
  , ("akh", .final) -- Akha
  , ("akn", .inEitherOfTwoPositions) -- Akan
  , ("ala", .noQuestionParticle) -- Alamblak
  , ("alb", .initial) -- Albanian
  , ("alk", .noQuestionParticle) -- Arop-Lokep
  , ("all", .initial) -- Ala'ala
  , ("amc", .secondPosition) -- Amahuaca
  , ("ame", .final) -- Amele
  , ("aml", .noQuestionParticle) -- Ambae (Lolovoli Northeast)
  , ("amn", .inEitherOfTwoPositions) -- Amanab
  , ("amo", .final) -- Amo
  , ("amp", .secondPosition) -- Arrernte (Mparntwe)
  , ("amq", .final) -- Ambai
  , ("amr", .initial) -- Arabic (Moroccan)
  , ("ams", .initial) -- Arabic (Modern Standard)
  , ("ana", .noQuestionParticle) -- Araona
  , ("anc", .final) -- Angas
  , ("ang", .noQuestionParticle) -- Anggor
  , ("ani", .final) -- //Ani
  , ("anj", .final) -- Anejom
  , ("ano", .noQuestionParticle) -- Anong
  , ("anu", .final) -- Anufo
  , ("ao", .final) -- Ao
  , ("aoj", .final) -- Mufian
  , ("api", .initial) -- Apinayé
  , ("apl", .noQuestionParticle) -- Apalaí
  , ("apt", .final) -- Apatani
  , ("apu", .noQuestionParticle) -- Apurinã
  , ("apw", .noQuestionParticle) -- Apache (Western)
  , ("ara", .noQuestionParticle) -- Lokono
  , ("arc", .noQuestionParticle) -- Archi
  , ("arg", .noQuestionParticle) -- Arabic (Gulf)
  , ("arm", .noQuestionParticle) -- Armenian (Eastern)
  , ("aro", .final) -- Arosi
  , ("arp", .final) -- Arapesh (Mountain)
  , ("arw", .noQuestionParticle) -- Armenian (Western)
  , ("asm", .final) -- Asmat
  , ("ass", .noQuestionParticle) -- Assamese
  , ("asy", .final) -- Arabic (Syrian)
  , ("ata", .final) -- Atayal
  , ("ath", .noQuestionParticle) -- Athpare
  , ("ava", .secondPosition) -- Avar
  , ("avk", .final) -- Avikam
  , ("awp", .final) -- Awa Pit
  , ("awt", .final) -- Awtuw
  , ("aym", .final) -- Aymara (Central)
  , ("aze", .final) -- Azerbaijani
  , ("azi", .noQuestionParticle) -- Azari (Iranian)
  , ("bab", .final) -- Babungo
  , ("bae", .noQuestionParticle) -- Baré
  , ("baf", .noQuestionParticle) -- Bafut
  , ("bag", .final) -- Bagirmi
  , ("bai", .final) -- Bai
  , ("bam", .final) -- Bambara
  , ("bao", .noQuestionParticle) -- Bao'an
  , ("baw", .final) -- Bawm
  , ("bbf", .final) -- Bobo Madaré (Northern)
  , ("bbw", .initial) -- Bininj Gun-Wok
  , ("bco", .noQuestionParticle) -- Bella Coola
  , ("bdm", .noQuestionParticle) -- Badimaya
  , ("bej", .noQuestionParticle) -- Beja
  , ("bel", .final) -- Belhare
  , ("bem", .inEitherOfTwoPositions) -- Bemba
  , ("ber", .final) -- Berta
  , ("bfg", .initial) -- Berber (Figuig)
  , ("bgn", .final) -- Bugun
  , ("bgo", .final) -- Bongo
  , ("bgz", .noQuestionParticle) -- Banggi
  , ("bho", .initial) -- Bhojpuri
  , ("bii", .noQuestionParticle) -- Biri
  , ("bik", .noQuestionParticle) -- Biak
  , ("bil", .noQuestionParticle) -- Bilua
  , ("bir", .final) -- Birom
  , ("biu", .noQuestionParticle) -- Bisu
  , ("bkn", .final) -- Bakundu
  , ("bkr", .secondPosition) -- Batak (Karo)
  , ("bla", .noQuestionParticle) -- Blackfoot
  , ("ble", .noQuestionParticle) -- Baoulé
  , ("bln", .noQuestionParticle) -- Bilin
  , ("blr", .initial) -- Belorussian
  , ("blt", .noQuestionParticle) -- Balti
  , ("blx", .final) -- Biloxi
  , ("bma", .initial) -- Berber (Middle Atlas)
  , ("bmb", .noQuestionParticle) -- Bimoba
  , ("bnj", .initial) -- Bandjalang
  , ("bnu", .initial) -- Bularnu
  , ("bod", .noQuestionParticle) -- Bodo
  , ("bon", .final) -- Bongu
  , ("bra", .final) -- Brao
  , ("bre", .initial) -- Breton
  , ("brf", .initial) -- Berber (Rif)
  , ("brm", .noQuestionParticle) -- Burmese
  , ("brn", .noQuestionParticle) -- Burunge
  , ("brp", .initial) -- Barupu
  , ("brs", .noQuestionParticle) -- Barasano
  , ("bsh", .noQuestionParticle) -- Bushoong
  , ("bsq", .otherPosition) -- Basque
  , ("bti", .noQuestionParticle) -- Betoi
  , ("btk", .initial) -- Bontok
  , ("bud", .final) -- Buduma
  , ("bul", .secondPosition) -- Bulgarian
  , ("bum", .noQuestionParticle) -- Buma
  , ("bur", .noQuestionParticle) -- Burushaski
  , ("bus", .final) -- Busa
  , ("bwc", .secondPosition) -- Bajau (West Coast)
  , ("bya", .initial) -- Byansi
  , ("cah", .noQuestionParticle) -- Cahuilla
  , ("cai", .noQuestionParticle) -- Chai
  , ("can", .noQuestionParticle) -- Candoshi
  , ("car", .noQuestionParticle) -- Carib
  , ("cba", .noQuestionParticle) -- Chumash (Barbareño)
  , ("ccm", .initial) -- Chinantec (Comaltepec)
  , ("cct", .final) -- Choctaw
  , ("cea", .secondPosition) -- Cree (Swampy)
  , ("cem", .initial) -- Cèmuhî
  , ("cga", .final) -- Chaga
  , ("cha", .initial) -- Chamorro
  , ("chc", .noQuestionParticle) -- Chechen
  , ("che", .secondPosition) -- Cherokee
  , ("chg", .final) -- Chang
  , ("chh", .final) -- Chaha
  , ("chi", .noQuestionParticle) -- Chimariko
  , ("chk", .noQuestionParticle) -- Chukchi
  , ("chp", .final) -- Chipewyan
  , ("chq", .initial) -- Chinantec (Quiotepec)
  , ("chr", .final) -- Chrau
  , ("chs", .final) -- Chin (Siyin)
  , ("chv", .noQuestionParticle) -- Chuvash
  , ("chw", .final) -- Cham (Western)
  , ("chx", .initial) -- Chontal (Huamelultec Oaxaca)
  , ("cic", .initial) -- Chichewa
  , ("cle", .initial) -- Chinantec (Lealao)
  , ("cmh", .secondPosition) -- Chemehuevi
  , ("cml", .noQuestionParticle) -- Camling
  , ("cmn", .secondPosition) -- Comanche
  , ("cmr", .final) -- Chin (Mara)
  , ("cmy", .noQuestionParticle) -- Chontal Maya
  , ("cnl", .initial) -- Canela
  , ("coa", .noQuestionParticle) -- Coahuilteco
  , ("coc", .secondPosition) -- Cocama
  , ("coo", .final) -- Coos (Hanis)
  , ("cop", .initial) -- Coptic
  , ("cpl", .noQuestionParticle) -- Chinantec (Palantla)
  , ("cpy", .noQuestionParticle) -- Chipaya
  , ("cre", .secondPosition) -- Cree (Plains)
  , ("crn", .initial) -- Cornish
  , ("crp", .noQuestionParticle) -- Carapana
  , ("cso", .final) -- Chatino (Sierra Occidental)
  , ("ctl", .noQuestionParticle) -- Catalan
  , ("ctm", .final) -- Chitimacha
  , ("cub", .noQuestionParticle) -- Cubeo
  , ("cup", .noQuestionParticle) -- Cupeño
  , ("cze", .noQuestionParticle) -- Czech
  , ("dan", .final) -- Dan
  , ("dds", .final) -- Donno So
  , ("des", .noQuestionParticle) -- Desano
  , ("deu", .noQuestionParticle) -- Deuri
  , ("dgr", .final) -- Dagur
  , ("dha", .noQuestionParticle) -- Dhaasanac
  , ("dhi", .final) -- Dhivehi
  , ("die", .noQuestionParticle) -- Diegueño (Mesa Grande)
  , ("dim", .noQuestionParticle) -- Dime
  , ("din", .noQuestionParticle) -- Dinka
  , ("dio", .noQuestionParticle) -- Diola-Fogny
  , ("diy", .noQuestionParticle) -- Diyari
  , ("dji", .initial) -- Djingili
  , ("djm", .noQuestionParticle) -- Djambarrpuyngu
  , ("djp", .initial) -- Djapu
  , ("dlm", .noQuestionParticle) -- Dla (Menggwa)
  , ("dmk", .final) -- Domaaki
  , ("dni", .noQuestionParticle) -- Dani (Lower Grand Valley)
  , ("don", .final) -- Dong (Southern)
  , ("doy", .final) -- Doyayo
  , ("dre", .initial) -- Drehu
  , ("drm", .initial) -- Darma
  , ("dsh", .noQuestionParticle) -- Danish
  , ("duk", .final) -- Duka
  , ("dul", .final) -- Dulong
  , ("dum", .final) -- Dumo
  , ("dun", .final) -- Duna
  , ("dut", .noQuestionParticle) -- Dutch
  , ("dyi", .secondPosition) -- Dyirbal
  , ("ebi", .inEitherOfTwoPositions) -- Ebira
  , ("efi", .initial) -- Efik
  , ("ega", .final) -- Ega
  , ("egn", .final) -- Engenni
  , ("eip", .noQuestionParticle) -- Eipo
  , ("emb", .noQuestionParticle) -- Emberá (Northern)
  , ("eme", .secondPosition) -- Émérillon
  , ("ene", .noQuestionParticle) -- Enets
  , ("eng", .noQuestionParticle) -- English
  , ("eno", .noQuestionParticle) -- Enggano
  , ("epe", .noQuestionParticle) -- Epena Pedee
  , ("erk", .noQuestionParticle) -- Efate (South)
  , ("err", .initial) -- Erromangan
  , ("ese", .initial) -- Ese Ejja
  , ("est", .inEitherOfTwoPositions) -- Estonian
  , ("eud", .initial) -- Eudeve
  , ("eve", .final) -- Evenki
  , ("ewe", .final) -- Ewe
  , ("ewo", .initial) -- Ewondo
  , ("fas", .noQuestionParticle) -- Fasu
  , ("fij", .noQuestionParticle) -- Fijian
  , ("fin", .secondPosition) -- Finnish
  , ("foe", .noQuestionParticle) -- Foe
  , ("fre", .initial) -- French
  , ("fri", .noQuestionParticle) -- Frisian
  , ("fua", .final) -- Fulfulde (Adamawa)
  , ("ful", .noQuestionParticle) -- Fulniô
  , ("fut", .final) -- Futuna-Aniwa
  , ("fye", .final) -- Fyem
  , ("gae", .noQuestionParticle) -- Gaelic (Scots)
  , ("gah", .noQuestionParticle) -- Gahuku
  , ("gal", .noQuestionParticle) -- Galo
  , ("gap", .final) -- Gapapaiwa
  , ("gar", .noQuestionParticle) -- Garo
  , ("gav", .initial) -- Gavião
  , ("gbb", .final) -- Gbeya Bossangoa
  , ("gdb", .noQuestionParticle) -- Gutob
  , ("gds", .noQuestionParticle) -- Gadsup
  , ("gel", .final) -- Gela
  , ("geo", .noQuestionParticle) -- Georgian
  , ("ger", .noQuestionParticle) -- German
  , ("ghb", .noQuestionParticle) -- Guahibo
  , ("ghr", .final) -- Bunan
  , ("gim", .noQuestionParticle) -- Gimira
  , ("git", .final) -- Gitksan
  , ("gln", .noQuestionParticle) -- Golin
  , ("gmw", .noQuestionParticle) -- Gumawana
  , ("gmz", .noQuestionParticle) -- Gumuz
  , ("gnb", .noQuestionParticle) -- Gunbalang
  , ("goa", .initial) -- Goajiro
  , ("goe", .final) -- Goemai
  , ("gok", .initial) -- Gokana
  , ("gon", .final) -- Gondi
  , ("grb", .initial) -- Grebo
  , ("grj", .noQuestionParticle) -- Guarijío
  , ("grk", .initial) -- Greek (Modern)
  , ("grr", .inEitherOfTwoPositions) -- Garrwa
  , ("grw", .noQuestionParticle) -- Greenlandic (West)
  , ("gud", .final) -- Gude
  , ("guh", .final) -- Guhu-Samane
  , ("guj", .noQuestionParticle) -- Gujarati
  , ("gul", .final) -- Gula (in Central African Republic)
  , ("gum", .noQuestionParticle) -- Gumbaynggir
  , ("gur", .final) -- Gurung
  , ("guw", .final) -- Gungbe
  , ("gwa", .final) -- Gwari
  , ("gyc", .noQuestionParticle) -- Gyarong (Cogtse)
  , ("hai", .secondPosition) -- Haida
  , ("ham", .final) -- Hamtai
  , ("hat", .final) -- Hatam
  , ("hau", .final) -- Hausa
  , ("hay", .noQuestionParticle) -- Hayu
  , ("hdi", .final) -- Hdi
  , ("heb", .initial) -- Hebrew (Modern)
  , ("hin", .initial) -- Hindi
  , ("hix", .noQuestionParticle) -- Hixkaryana
  , ("hma", .final) -- Hmar
  , ("hmi", .noQuestionParticle) -- Huitoto (Minica)
  , ("hmo", .otherPosition) -- Hmong Njua
  , ("hna", .final) -- Mina
  , ("hnd", .inEitherOfTwoPositions) -- Hunde
  , ("ho", .final) -- Ho
  , ("hoa", .noQuestionParticle) -- Hoava
  , ("hop", .initial) -- Hopi
  , ("hpd", .noQuestionParticle) -- Hup
  , ("htc", .noQuestionParticle) -- Huastec
  , ("hua", .noQuestionParticle) -- Hua
  , ("hve", .initial) -- Huave (San Mateo del Mar)
  , ("hya", .noQuestionParticle) -- Haya
  , ("hzb", .noQuestionParticle) -- Hunzib
  , ("iaa", .initial) -- Iaai
  , ("iba", .initial) -- Iban
  , ("idu", .noQuestionParticle) -- Idu
  , ("ifm", .final) -- Ifumu
  , ("ifu", .initial) -- Ifugao (Batad)
  , ("igb", .noQuestionParticle) -- Igbo
  , ("ige", .final) -- Igede
  , ("ijo", .noQuestionParticle) -- Ijo (Kolokuma)
  , ("ik", .final) -- Ik
  , ("ika", .final) -- Ika
  , ("ina", .final) -- Inanwatan
  , ("ind", .inEitherOfTwoPositions) -- Indonesian
  , ("ing", .noQuestionParticle) -- Ingush
  , ("iri", .initial) -- Irish
  , ("irq", .noQuestionParticle) -- Iraqw
  , ("irr", .noQuestionParticle) -- Irarutu
  , ("ita", .noQuestionParticle) -- Italian
  , ("ito", .noQuestionParticle) -- Itonama
  , ("iwa", .inEitherOfTwoPositions) -- Iwaidja
  , ("iwm", .final) -- Iwam
  , ("izi", .final) -- Izi
  , ("jab", .final) -- Jabêm
  , ("jak", .noQuestionParticle) -- Jakaltek
  , ("jar", .final) -- Izere
  , ("jmo", .noQuestionParticle) -- Jur Mödö
  , ("jms", .final) -- Jamsay
  , ("jng", .final) -- Jingpho
  , ("jpn", .final) -- Japanese
  , ("jug", .noQuestionParticle) -- Jugli
  , ("juh", .secondPosition) -- Ju|'hoan
  , ("juk", .final) -- Jukun
  , ("kaa", .final) -- Karó (Arára)
  , ("kab", .noQuestionParticle) -- Kabardian
  , ("kae", .noQuestionParticle) -- Kaki Ae
  , ("kan", .noQuestionParticle) -- Kana
  , ("kar", .final) -- Kara (in Central African Republic)
  , ("kau", .final) -- Kaulong
  , ("kay", .noQuestionParticle) -- Kayardild
  , ("kba", .noQuestionParticle) -- Kamba
  , ("kbl", .noQuestionParticle) -- Kabyle
  , ("kbw", .final) -- Karen (Bwe)
  , ("kby", .final) -- Kabiyé
  , ("kch", .noQuestionParticle) -- Koyra Chiini
  , ("kdz", .secondPosition) -- Kadazan
  , ("kel", .final) -- Kele
  , ("kem", .noQuestionParticle) -- Kemant
  , ("ken", .final) -- Kenga
  , ("ker", .final) -- Kera
  , ("kew", .final) -- Kewa
  , ("kfe", .final) -- Koromfe
  , ("kgz", .final) -- Kirghiz
  , ("kha", .final) -- Khalkha
  , ("khg", .final) -- Khaling
  , ("khi", .noQuestionParticle) -- Khinalug
  , ("khm", .final) -- Khmer
  , ("khn", .final) -- Khün
  , ("kho", .secondPosition) -- Nama
  , ("khr", .final) -- Kharia
  , ("kik", .noQuestionParticle) -- Kikuyu
  , ("kil", .final) -- Kiluba
  , ("kim", .final) -- Kimaghama
  , ("kio", .initial) -- Kiowa
  , ("kis", .noQuestionParticle) -- Kisi
  , ("kje", .noQuestionParticle) -- Koreguaje
  , ("kkp", .noQuestionParticle) -- Karakalpak
  , ("klm", .inEitherOfTwoPositions) -- Klamath
  , ("klv", .noQuestionParticle) -- Kilivila
  , ("klw", .noQuestionParticle) -- Kiliwa
  , ("kma", .noQuestionParticle) -- Kamaiurá
  , ("kmb", .final) -- Kombai
  , ("kmh", .noQuestionParticle) -- Kham
  , ("kmj", .final) -- Karimojong
  , ("kmk", .noQuestionParticle) -- Kalmyk
  , ("kmn", .noQuestionParticle) -- Kuman
  , ("kmo", .secondPosition) -- Koiali (Mountain)
  , ("kmr", .noQuestionParticle) -- Kamoro
  , ("kmu", .final) -- Khmu'
  , ("kmz", .noQuestionParticle) -- Kamasau
  , ("knc", .noQuestionParticle) -- Kugu Nganhcara
  , ("knd", .final) -- Kannada
  , ("kni", .noQuestionParticle) -- Konni
  , ("knk", .final) -- Kanakuru
  , ("knm", .noQuestionParticle) -- Kunama
  , ("knn", .noQuestionParticle) -- Kinnauri
  , ("kno", .final) -- Kanoê
  , ("knr", .noQuestionParticle) -- Kanuri
  , ("knw", .noQuestionParticle) -- Konkow
  , ("kob", .final) -- Kobon
  , ("koe", .noQuestionParticle) -- Koegu
  , ("kok", .noQuestionParticle) -- Kokborok
  , ("kol", .noQuestionParticle) -- Kolami
  , ("kor", .noQuestionParticle) -- Korean
  , ("kos", .initial) -- Kosraean
  , ("kpw", .final) -- Karen (Pwo)
  , ("kqq", .noQuestionParticle) -- Krenak
  , ("krc", .noQuestionParticle) -- Karachay-Balkar
  , ("kre", .final) -- Kresh
  , ("krj", .initial) -- Karadjeri
  , ("krn", .final) -- Korana
  , ("kro", .noQuestionParticle) -- Krongo
  , ("krw", .final) -- Korowai
  , ("ksa", .initial) -- Keresan (Santa Ana)
  , ("kse", .inEitherOfTwoPositions) -- Koyraboro Senni
  , ("ksg", .final) -- Karen (Sgaw)
  , ("ksm", .final) -- Kasem
  , ("kta", .final) -- Koita
  , ("kum", .inEitherOfTwoPositions) -- Kumauni
  , ("kun", .noQuestionParticle) -- Kuna
  , ("kuo", .noQuestionParticle) -- Kuot
  , ("kut", .initial) -- Kutenai
  , ("kuu", .noQuestionParticle) -- Kuuku Ya'u
  , ("kuv", .final) -- Kuvi
  , ("kwn", .final) -- Kwangali
  , ("kwo", .secondPosition) -- Kwoma
  , ("kws", .noQuestionParticle) -- Kawaiisu
  , ("kwz", .noQuestionParticle) -- Kwaza
  , ("kxo", .final) -- Kxoe
  , ("kya", .initial) -- Kuku-Yalanji
  , ("kyk", .noQuestionParticle) -- Kyaka
  , ("kyl", .final) -- Kayah Li (Eastern)
  , ("kyp", .initial) -- Kayapó
  , ("kyz", .secondPosition) -- Kayabí
  , ("laa", .inEitherOfTwoPositions) -- Laal
  , ("lab", .noQuestionParticle) -- Labu
  , ("lac", .final) -- Lacandón
  , ("lad", .noQuestionParticle) -- Ladakhi
  , ("lag", .final) -- Lagwan
  , ("lah", .final) -- Lahu
  , ("lai", .final) -- Lai
  , ("lal", .final) -- Lalo
  , ("lan", .noQuestionParticle) -- Lango
  , ("lao", .final) -- Lao
  , ("lat", .initial) -- Latvian
  , ("lav", .final) -- Lavukaleve
  , ("lbu", .noQuestionParticle) -- Lunda
  , ("ldo", .final) -- Londo
  , ("ldu", .secondPosition) -- Lendu
  , ("lel", .final) -- Lele
  , ("len", .final) -- Lenakel
  , ("lep", .final) -- Lepcha
  , ("lew", .final) -- Lewo
  , ("lez", .noQuestionParticle) -- Lezgian
  , ("lgt", .final) -- Logoti
  , ("lho", .noQuestionParticle) -- Lhomi
  , ("lin", .noQuestionParticle) -- Lingala
  , ("lis", .noQuestionParticle) -- Lisu
  , ("lit", .initial) -- Lithuanian
  , ("lkt", .final) -- Lakhota
  , ("lmg", .final) -- Lamang
  , ("lmh", .noQuestionParticle) -- Lamaholot
  , ("lmn", .final) -- Lamani
  , ("lmp", .initial) -- Lampung
  , ("lnd", .final) -- Linda
  , ("lon", .noQuestionParticle) -- Loniu
  , ("lot", .noQuestionParticle) -- Lotha
  , ("loz", .inEitherOfTwoPositions) -- Lozi
  , ("lug", .final) -- Lugbara
  , ("lui", .secondPosition) -- Luiseño
  , ("lun", .final) -- Lungchang
  , ("luo", .noQuestionParticle) -- Luo
  , ("maa", .initial) -- Maasai
  , ("mab", .noQuestionParticle) -- Maba
  , ("mac", .noQuestionParticle) -- Macushi
  , ("mad", .final) -- Ma'di
  , ("mae", .final) -- Mae
  , ("maj", .final) -- Majang
  , ("mak", .secondPosition) -- Makah
  , ("mal", .inEitherOfTwoPositions) -- Malagasy
  , ("mam", .secondPosition) -- Mam
  , ("man", .noQuestionParticle) -- Mano
  , ("mao", .noQuestionParticle) -- Maori
  , ("mar", .noQuestionParticle) -- Maricopa
  , ("mas", .final) -- Masa
  , ("mau", .initial) -- Maung
  , ("maw", .final) -- Maninka (Western)
  , ("max", .initial) -- Maxakalí
  , ("may", .final) -- Maybrat
  , ("mbi", .otherPosition) -- Mbili
  , ("mbm", .final) -- Mbum
  , ("mbr", .final) -- Mbara
  , ("mby", .final) -- Mbay
  , ("mco", .inEitherOfTwoPositions) -- Mixe (Coatlán)
  , ("mde", .noQuestionParticle) -- Mende
  , ("mdn", .noQuestionParticle) -- Mandan
  , ("mdo", .final) -- Mbodomo
  , ("mea", .final) -- Meyah
  , ("mee", .final) -- Me'en
  , ("meh", .noQuestionParticle) -- Mehri
  , ("mei", .final) -- Meithei
  , ("mek", .final) -- Mekens
  , ("men", .noQuestionParticle) -- Menomini
  , ("mer", .noQuestionParticle) -- Meryam Mir
  , ("mey", .final) -- Menya
  , ("mgg", .noQuestionParticle) -- Mangghuer
  , ("mgk", .final) -- Mungaka
  , ("mgu", .final) -- Musgu
  , ("mhi", .final) -- Marathi
  , ("mie", .final) -- Mien
  , ("mik", .noQuestionParticle) -- Mikir
  , ("mis", .final) -- Miskito
  , ("miy", .final) -- Miya
  , ("miz", .final) -- Mizo
  , ("mka", .final) -- Mauka
  , ("mke", .final) -- Mekeo
  , ("mkh", .final) -- Mongol (Khamnigan)
  , ("mku", .noQuestionParticle) -- Maranungku
  , ("mlg", .noQuestionParticle) -- Malgwa
  , ("mmb", .final) -- Mangap-Mbula
  , ("mmi", .final) -- Mambai
  , ("mna", .noQuestionParticle) -- Muna
  , ("mnc", .noQuestionParticle) -- Manchu
  , ("mnd", .final) -- Mandarin
  ]

/-- Rows 501 to 884 of `allData`. -/
def allData_1 : List (String × QuestionParticlePosition) :=
  [ ("mne", .noQuestionParticle) -- Maidu (Northeast)
  , ("mng", .noQuestionParticle) -- Manggarai
  , ("mni", .noQuestionParticle) -- Moni
  , ("mnm", .noQuestionParticle) -- Manam
  , ("mno", .secondPosition) -- Mono (in United States)
  , ("mns", .initial) -- Mansi
  , ("mny", .initial) -- Margany
  , ("mok", .initial) -- Mokilese
  , ("mon", .final) -- Mon
  , ("moo", .final) -- Mooré
  , ("mos", .secondPosition) -- Mosetén
  , ("mou", .final) -- Moru
  , ("mov", .noQuestionParticle) -- Movima
  , ("mpa", .final) -- Murrinh-Patha
  , ("mpt", .final) -- Mian
  , ("mpu", .final) -- Mpur
  , ("mra", .noQuestionParticle) -- Mara
  , ("mrd", .final) -- Marind
  , ("mrg", .final) -- Margi
  , ("mri", .final) -- Moraori
  , ("mrl", .noQuestionParticle) -- Murle
  , ("mro", .initial) -- Moro
  , ("mrq", .initial) -- Marquesan
  , ("mrt", .noQuestionParticle) -- Martuthunira
  , ("mru", .final) -- Maru
  , ("mrw", .initial) -- Muruwari
  , ("msc", .noQuestionParticle) -- Muisca
  , ("msg", .noQuestionParticle) -- Mising
  , ("msl", .noQuestionParticle) -- Masalit
  , ("msn", .final) -- Maisin
  , ("mts", .noQuestionParticle) -- Matis
  , ("mtt", .noQuestionParticle) -- Massachusett
  , ("mtu", .final) -- Motu
  , ("mum", .final) -- Mumuye
  , ("mun", .final) -- Mundari
  , ("mup", .final) -- Mupun
  , ("mus", .final) -- Mussau
  , ("mut", .initial) -- Mutsun
  , ("mwo", .noQuestionParticle) -- Mwotlap
  , ("mxc", .noQuestionParticle) -- Mixtec (Chalcatongo)
  , ("mxj", .final) -- Mixtec (Jicaltepec)
  , ("mxo", .initial) -- Mixtec (Ocotepec)
  , ("mxp", .final) -- Mixtec (Peñoles)
  , ("mxx", .final) -- Mixe (Ayutla)
  , ("mxy", .final) -- Mixtec (Yosondúa)
  , ("myi", .final) -- Mangarrayi
  , ("mym", .final) -- Malayalam
  , ("mzh", .initial) -- Mazatec (Huautla)
  , ("nab", .noQuestionParticle) -- Nabak
  , ("nad", .noQuestionParticle) -- Nadëb
  , ("nag", .final) -- Nagatman
  , ("naj", .noQuestionParticle) -- Neo-Aramaic (Arbel Jewish)
  , ("nam", .final) -- Namia
  , ("nan", .final) -- Nandi
  , ("nas", .secondPosition) -- Nasioi
  , ("nav", .inEitherOfTwoPositions) -- Navajo
  , ("nbd", .noQuestionParticle) -- Nubian (Dongolese)
  , ("nbm", .final) -- Ngbaka (Ma'bo)
  , ("ncm", .final) -- Ncàm
  , ("ndb", .final) -- Ndebele
  , ("ndi", .noQuestionParticle) -- Ngbandi
  , ("ndj", .noQuestionParticle) -- Ndjébbana
  , ("ndr", .noQuestionParticle) -- Nadroga
  , ("ndy", .noQuestionParticle) -- Ndyuka
  , ("nev", .initial) -- Nevome
  , ("new", .final) -- Newari (Kathmandu)
  , ("ney", .final) -- Neyo
  , ("nez", .initial) -- Nez Perce
  , ("nga", .noQuestionParticle) -- Nganasan
  , ("ngb", .final) -- Ngbaka (Minagende)
  , ("ngd", .noQuestionParticle) -- Ngad'a
  , ("ngi", .secondPosition) -- Ngiyambaa
  , ("ngk", .noQuestionParticle) -- Ngankikurungkurr
  , ("ngm", .final) -- Ngambay
  , ("ngn", .initial) -- Ngandi
  , ("ngo", .noQuestionParticle) -- Ngoni
  , ("ngt", .noQuestionParticle) -- Naga (Tangkhul)
  , ("ngz", .noQuestionParticle) -- Ngizim
  , ("nha", .noQuestionParticle) -- Nhanda
  , ("nht", .noQuestionParticle) -- Nahuatl (Tetelcingo)
  , ("nia", .initial) -- Nias
  , ("nif", .noQuestionParticle) -- Niuafo'ou
  , ("niu", .otherPosition) -- Niuean
  , ("niv", .final) -- Nivkh
  , ("nkb", .initial) -- Ngalkbun
  , ("nke", .final) -- Nkem
  , ("nkn", .final) -- Nkonya
  , ("nko", .final) -- Nkore-Kiga
  , ("nma", .final) -- Naga (Mao)
  , ("nmb", .noQuestionParticle) -- Nambikuára (Southern)
  , ("nnc", .initial) -- Nancowry
  , ("nnd", .noQuestionParticle) -- Nend
  , ("nnk", .noQuestionParticle) -- Nankina
  , ("noc", .noQuestionParticle) -- Nocte
  , ("non", .final) -- Noni
  , ("noo", .final) -- Noon
  , ("nor", .noQuestionParticle) -- Norwegian
  , ("nph", .noQuestionParticle) -- Nar-Phu
  , ("nsg", .final) -- Nisgha
  , ("nti", .inEitherOfTwoPositions) -- Ngiti
  , ("nua", .noQuestionParticle) -- Nuaulu
  , ("nug", .inEitherOfTwoPositions) -- Nunggubuyu
  , ("nun", .final) -- Nung (in Vietnam)
  , ("nup", .inEitherOfTwoPositions) -- Nupe
  , ("nwd", .final) -- Newar (Dolakha)
  , ("nyk", .noQuestionParticle) -- Nyamkad
  , ("nyu", .initial) -- Nyulnyul
  , ("nze", .final) -- Naga (Zeme)
  , ("obg", .final) -- Ogbronuagum
  , ("obo", .initial) -- Obolo
  , ("ocu", .initial) -- Ocuilteco
  , ("oji", .secondPosition) -- Ojibwa (Eastern)
  , ("olo", .final) -- Olo
  , ("omh", .final) -- Omaha
  , ("ond", .secondPosition) -- Oneida
  , ("ong", .initial) -- Onge
  , ("ood", .initial) -- O'odham
  , ("ora", .noQuestionParticle) -- Emai
  , ("orh", .noQuestionParticle) -- Oromo (Harar)
  , ("oro", .final) -- Orokaiva
  , ("osa", .noQuestionParticle) -- Osage
  , ("otm", .initial) -- Otomí (Mezquital)
  , ("oya", .final) -- Oriya
  , ("paa", .noQuestionParticle) -- Pa'a
  , ("pae", .noQuestionParticle) -- Páez
  , ("pai", .noQuestionParticle) -- Paiwan
  , ("pal", .noQuestionParticle) -- Palauan
  , ("pan", .initial) -- Panjabi
  , ("par", .noQuestionParticle) -- Päri
  , ("pau", .noQuestionParticle) -- Paumarí
  , ("paw", .noQuestionParticle) -- Pawaian
  , ("pdp", .noQuestionParticle) -- Folopa
  , ("per", .final) -- Pero
  , ("pga", .initial) -- Pilagá
  , ("pip", .noQuestionParticle) -- Pipil
  , ("pis", .final) -- Pisa
  , ("plk", .initial) -- Palikur
  , ("pme", .noQuestionParticle) -- Pomo (Eastern)
  , ("pms", .noQuestionParticle) -- Paamese
  , ("pno", .secondPosition) -- Paiute (Northern)
  , ("pnx", .initial) -- Panará
  , ("pod", .final) -- Podoko
  , ("poh", .noQuestionParticle) -- Pohnpeian
  , ("pok", .final) -- Poko-Rawo
  , ("pol", .initial) -- Polish
  , ("por", .initial) -- Portuguese
  , ("ppi", .noQuestionParticle) -- Pitta Pitta
  , ("prh", .final) -- Pirahã
  , ("prk", .noQuestionParticle) -- Purki
  , ("prs", .initial) -- Persian
  , ("psh", .noQuestionParticle) -- Pashto
  , ("pso", .noQuestionParticle) -- Pomo (Southeastern)
  , ("psw", .noQuestionParticle) -- Port Sandwich
  , ("ptt", .noQuestionParticle) -- Pattani
  , ("puq", .noQuestionParticle) -- Puquina
  , ("qaw", .noQuestionParticle) -- Qawasqar
  , ("qhu", .noQuestionParticle) -- Quechua (Huallaga)
  , ("qia", .noQuestionParticle) -- Qiang
  , ("qim", .final) -- Quechua (Imbabura)
  , ("qui", .noQuestionParticle) -- Quileute
  , ("qum", .initial) -- Sipakapense
  , ("rap", .initial) -- Rapanui
  , ("raw", .final) -- Rawang
  , ("rem", .noQuestionParticle) -- Remo
  , ("res", .initial) -- Resígaro
  , ("ret", .initial) -- Retuarã
  , ("rit", .final) -- Ritharngu
  , ("rny", .noQuestionParticle) -- Runyankore
  , ("rom", .noQuestionParticle) -- Romanian
  , ("ron", .final) -- Ron
  , ("rot", .initial) -- Rotuman
  , ("rov", .noQuestionParticle) -- Roviana
  , ("ruk", .noQuestionParticle) -- Rukai (Tanan)
  , ("rum", .final) -- Rumu
  , ("run", .noQuestionParticle) -- Runga
  , ("rus", .secondPosition) -- Russian
  , ("rwe", .initial) -- Romani (Welsh)
  , ("ryu", .noQuestionParticle) -- Shuri
  , ("sah", .noQuestionParticle) -- Sahu
  , ("sal", .noQuestionParticle) -- Salinan
  , ("sam", .initial) -- Samoan
  , ("san", .final) -- Sango
  , ("sap", .final) -- Sapuan
  , ("sar", .noQuestionParticle) -- Sare
  , ("scr", .inEitherOfTwoPositions) -- Serbian-Croatian
  , ("sea", .noQuestionParticle) -- Southeast Ambrym
  , ("sed", .otherPosition) -- Sedang
  , ("sem", .final) -- Sema
  , ("ser", .final) -- Seri
  , ("ses", .noQuestionParticle) -- Sesotho
  , ("she", .final) -- Sherpa
  , ("shh", .final) -- Sharanahua
  , ("shi", .final) -- Shiriana
  , ("shk", .secondPosition) -- Shipibo-Konibo
  , ("shl", .noQuestionParticle) -- Shilluk
  , ("shu", .inEitherOfTwoPositions) -- Shuswap
  , ("sia", .noQuestionParticle) -- Siane
  , ("sid", .noQuestionParticle) -- Sidaama
  , ("sio", .final) -- Sio
  , ("skk", .final) -- Sikkimese
  , ("sko", .final) -- Skou
  , ("skw", .noQuestionParticle) -- Shekhawati
  , ("sla", .initial) -- Slave
  , ("slb", .final) -- Saliba (in Papua New Guinea)
  , ("sle", .final) -- Samba Leko
  , ("slg", .final) -- Sulung
  , ("sml", .noQuestionParticle) -- Semelai
  , ("smn", .noQuestionParticle) -- Seminole
  , ("sna", .noQuestionParticle) -- Shina
  , ("sng", .final) -- Sinaugoro
  , ("snm", .noQuestionParticle) -- Sanuma
  , ("snn", .final) -- Soninke
  , ("so", .final) -- So
  , ("sob", .final) -- Sobei
  , ("som", .otherPosition) -- Somali
  , ("son", .initial) -- Sonsorol-Tobi
  , ("spa", .noQuestionParticle) -- Spanish
  , ("squ", .secondPosition) -- Squamish
  , ("src", .noQuestionParticle) -- Sarcee
  , ("srd", .initial) -- Sardinian
  , ("sre", .final) -- Sre
  , ("srn", .final) -- Sirionó
  , ("sro", .final) -- Siroi
  , ("sta", .noQuestionParticle) -- Santa
  , ("sti", .final) -- Stieng
  , ("stl", .noQuestionParticle) -- Santali
  , ("sud", .noQuestionParticle) -- Sudest
  , ("sue", .noQuestionParticle) -- Suena
  , ("sul", .noQuestionParticle) -- Sulka
  , ("sun", .initial) -- Sundanese
  , ("sup", .final) -- Supyire
  , ("svs", .noQuestionParticle) -- Savosavo
  , ("swa", .initial) -- Swahili
  , ("swe", .noQuestionParticle) -- Swedish
  , ("swt", .final) -- Swati
  , ("syu", .noQuestionParticle) -- Salt-Yui
  , ("tab", .noQuestionParticle) -- Taba
  , ("tac", .initial) -- Tacana
  , ("taf", .noQuestionParticle) -- Taiof
  , ("tag", .secondPosition) -- Tagalog
  , ("tah", .secondPosition) -- Tahitian
  , ("tai", .noQuestionParticle) -- Tuareg (Air)
  , ("taj", .final) -- Tajik
  , ("tak", .final) -- Takia
  , ("tam", .final) -- Tamang (Eastern)
  , ("tao", .final) -- Tarao
  , ("tar", .noQuestionParticle) -- Tariana
  , ("tau", .final) -- Tauya
  , ("tbo", .otherPosition) -- Tboli
  , ("tbt", .noQuestionParticle) -- Tobati
  , ("tbu", .final) -- Tubu
  , ("tbw", .noQuestionParticle) -- Tabwa
  , ("tbx", .noQuestionParticle) -- Tangbe
  , ("tee", .initial) -- Tepehua (Huehuetla)
  , ("tel", .noQuestionParticle) -- Telugu
  , ("ten", .noQuestionParticle) -- Tennet
  , ("teo", .noQuestionParticle) -- Teop
  , ("ter", .final) -- Tera
  , ("tet", .final) -- Tetela
  , ("tgk", .final) -- Tigak
  , ("tgl", .final) -- Tshangla
  , ("tha", .final) -- Thai
  , ("tho", .inEitherOfTwoPositions) -- Thompson
  , ("thy", .noQuestionParticle) -- Kuuk Thaayorre
  , ("tib", .final) -- Tibetan (Standard Spoken)
  , ("tid", .noQuestionParticle) -- Tidore
  , ("tin", .otherPosition) -- Tinrin
  , ("tir", .noQuestionParticle) -- Tiriyo
  , ("tiw", .final) -- Tiwi
  , ("tja", .final) -- Tiipay (Jamul)
  , ("tke", .noQuestionParticle) -- Tokelauan
  , ("tkl", .secondPosition) -- Takelma
  , ("tla", .initial) -- Tolai
  , ("tlp", .initial) -- Tlapanec
  , ("tml", .noQuestionParticle) -- Tamil
  , ("tmo", .noQuestionParticle) -- Tibetan (Modern Literary)
  , ("tna", .final) -- Turkana
  , ("tne", .final) -- Temne
  , ("tni", .noQuestionParticle) -- Tinani
  , ("tnn", .final) -- Tunen
  , ("tny", .final) -- Tenyer
  , ("tob", .noQuestionParticle) -- Toba
  , ("ton", .noQuestionParticle) -- Tonkawa
  , ("tpn", .secondPosition) -- Tepehuan (Northern)
  , ("tps", .noQuestionParticle) -- Tepehuan (Southeastern)
  , ("trb", .final) -- Teribe
  , ("tri", .final) -- Trique (Copala)
  , ("tsf", .noQuestionParticle) -- Tsafiki
  , ("tsh", .secondPosition) -- Tümpisa Shoshone
  , ("tsi", .noQuestionParticle) -- Tsimshian (Coast)
  , ("tsk", .initial) -- Tamashek
  , ("tsn", .inEitherOfTwoPositions) -- Tsonga
  , ("tsz", .noQuestionParticle) -- Tsez
  , ("tte", .noQuestionParticle) -- Tutelo
  , ("ttn", .final) -- Tetun
  , ("ttu", .secondPosition) -- Tsova-Tush
  , ("tuc", .noQuestionParticle) -- Tucano
  , ("tuk", .final) -- Tukang Besi
  , ("tun", .noQuestionParticle) -- Tunica
  , ("tur", .final) -- Turkish
  , ("tus", .secondPosition) -- Tuscarora
  , ("tuv", .final) -- Tuvan
  , ("tuy", .noQuestionParticle) -- Tuyuca
  , ("tvl", .noQuestionParticle) -- Tuvaluan
  , ("tvt", .final) -- Tutsa
  , ("txj", .initial) -- Totonac (Xicotepec de Juárez)
  , ("tzo", .initial) -- Tzotzil
  , ("tzu", .initial) -- Tzutujil
  , ("uby", .noQuestionParticle) -- Ubykh
  , ("udh", .noQuestionParticle) -- Udihe
  , ("ukr", .initial) -- Ukrainian
  , ("uld", .final) -- Uldeme
  , ("uli", .noQuestionParticle) -- Ulithian
  , ("una", .noQuestionParticle) -- Una
  , ("urd", .initial) -- Urdu
  , ("urk", .final) -- Urubú-Kaapor
  , ("url", .final) -- Urak Lawoi'
  , ("urt", .final) -- Urat
  , ("usa", .noQuestionParticle) -- Usan
  , ("usr", .noQuestionParticle) -- Usarufa
  , ("ute", .secondPosition) -- Ute
  , ("uzb", .noQuestionParticle) -- Uzbek
  , ("vie", .final) -- Vietnamese
  , ("vnm", .noQuestionParticle) -- Vinmavis
  , ("wah", .final) -- Wahgi
  , ("wak", .noQuestionParticle) -- Wakhi
  , ("wal", .final) -- Walman
  , ("wao", .noQuestionParticle) -- Waorani
  , ("wap", .noQuestionParticle) -- Wappo
  , ("war", .noQuestionParticle) -- Wari'
  , ("was", .final) -- Washo
  , ("way", .secondPosition) -- Wayampi
  , ("wch", .initial) -- Wichí
  , ("wel", .initial) -- Welsh
  , ("wem", .noQuestionParticle) -- Wembawemba
  , ("wik", .initial) -- Wikchamni
  , ("wiy", .secondPosition) -- Wiyot
  , ("wlf", .initial) -- Wolof
  , ("wly", .noQuestionParticle) -- Wolaytta
  , ("wma", .noQuestionParticle) -- West Makian
  , ("wn", .final) -- Wik Ngathana
  , ("wol", .noQuestionParticle) -- Woleaian
  , ("wra", .noQuestionParticle) -- Warao
  , ("wrg", .noQuestionParticle) -- Warrgamay
  , ("wrk", .noQuestionParticle) -- Warekena
  , ("wrl", .secondPosition) -- Warlpiri
  , ("wrn", .noQuestionParticle) -- Warndarang
  , ("wth", .initial) -- Wathawurrung
  , ("wtm", .noQuestionParticle) -- Watam
  , ("wwa", .final) -- Waama
  , ("xas", .inEitherOfTwoPositions) -- Xasonga
  , ("xav", .initial) -- Xavánte
  , ("xbi", .noQuestionParticle) -- Kombio
  , ("xoo", .initial) -- !Xóõ
  , ("yag", .secondPosition) -- Yagua
  , ("yal", .noQuestionParticle) -- Yale (Kosarek)
  , ("yap", .noQuestionParticle) -- Yapese
  , ("yaq", .initial) -- Yaqui
  , ("yar", .final) -- Yareba
  , ("ygr", .final) -- Yagaria
  , ("yid", .noQuestionParticle) -- Yidiny
  , ("yin", .final) -- Yindjibarndi
  , ("yko", .noQuestionParticle) -- Yukaghir (Kolyma)
  , ("yng", .noQuestionParticle) -- Yingkarta
  , ("yok", .initial) -- Yokuts (Yaudanchi)
  , ("yor", .noQuestionParticle) -- Yoruba
  , ("ypk", .secondPosition) -- Yup'ik (Central)
  , ("yuc", .secondPosition) -- Yuchi
  , ("yuk", .initial) -- Yukulta
  , ("yul", .final) -- Yulu
  , ("yur", .secondPosition) -- Yurok
  , ("yuw", .initial) -- Yuwaalaraay
  , ("ywl", .initial) -- Yawelmani
  , ("zag", .noQuestionParticle) -- Beria
  , ("zai", .final) -- Zapotec (Isthmus)
  , ("zap", .initial) -- Zapotec (Mitla)
  , ("zay", .noQuestionParticle) -- Zayse
  , ("zaz", .noQuestionParticle) -- Zazaki
  , ("zch", .noQuestionParticle) -- Zoque (Chimalapa)
  , ("zhn", .final) -- Zhuang (Northern)
  , ("zqc", .noQuestionParticle) -- Zoque (Copainalá)
  , ("zul", .final) -- Zulu
  , ("zya", .initial) -- Zapotec (Yatzachi)
  , ("zzo", .noQuestionParticle) -- Zapotec (Zoogocho)
  ]

/-- The WALS 92A coding: each language's value, keyed by its WALS code (884 languages). -/
def allData : List (String × QuestionParticlePosition) := allData_0 ++ allData_1

end Data.WALS.F92A
