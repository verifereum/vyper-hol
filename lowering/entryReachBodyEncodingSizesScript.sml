Theory entryReachBodyEncodingSizes
Ancestors
  contractABI arithmetic list rich_list words byte
Libs
  wordsLib

Theorem entry_enc_tuple_length[local]:
  !ts vs hl tl hds tls.
    LENGTH ts = LENGTH vs ==>
    LENGTH (enc_tuple hl tl ts vs hds tls) =
      SUM (MAP LENGTH hds) + SUM (MAP LENGTH tls) +
      SUM (MAP2 (\ty av. LENGTH (enc ty av) +
                           (if is_dynamic ty then 32 else 0)) ts vs)
Proof
  Induct_on `ts` >> Cases_on `vs` >>
  simp[Once enc_def, LENGTH_FLAT, REV_REVERSE_LEM,
       MAP_REVERSE, SUM_REVERSE, SUM_APPEND] >>
  rpt strip_tac >> rename1 `is_dynamic ty` >> Cases_on `is_dynamic ty` >>
  simp[LENGTH_word_to_bytes]
QED

Theorem entry_tuple_encoding_length:
  LENGTH tys = LENGTH avs ==>
  LENGTH (enc (Tuple tys) (ListV avs)) =
    SUM (MAP2 (\ty av. LENGTH (enc ty av) +
                         (if is_dynamic ty then 32 else 0)) tys avs)
Proof
  strip_tac >> simp[Once enc_def, entry_enc_tuple_length]
QED

Theorem entry_tuple_encoding_child_bound:
  !tys avs i. LENGTH tys = LENGTH avs /\ i < LENGTH tys ==>
  LENGTH (enc (EL i tys) (EL i avs)) <=
    LENGTH (enc (Tuple tys) (ListV avs))
Proof
  simp[entry_tuple_encoding_length] >>
  Induct_on `tys` >> Cases_on `avs` >> simp[] >>
  rpt gen_tac >> Cases_on `i` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> disch_then (qspec_then `n` mp_tac) >>
  simp[] >> decide_tac
QED

Theorem entry_tuple_encoding_cardinality:
  !tys avs. LENGTH tys = LENGTH avs /\
  (!i. i < LENGTH tys ==> 0 < LENGTH (enc (EL i tys) (EL i avs))) ==>
  LENGTH avs <= LENGTH (enc (Tuple tys) (ListV avs))
Proof
  simp[entry_tuple_encoding_length] >>
  Induct_on `tys` >> Cases_on `avs` >> simp[] >> rpt strip_tac >>
  `0 < LENGTH (enc h' h)` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `!i. i < LENGTH tys ==> 0 < LENGTH (enc (EL i tys) (EL i t))` by
    (rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
  first_x_assum drule_all >> simp[] >> decide_tac
QED
