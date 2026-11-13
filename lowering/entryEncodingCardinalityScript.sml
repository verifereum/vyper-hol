Theory entryEncodingCardinality
Ancestors
  arithmetic list rich_list words byte contractABI abiCanonicalWindows abiDecodeRanges

Theorem tuple_parts_encoding_sum[local]:
  !tys avs hl tl. LENGTH tys = LENGTH avs ==>
    SUM (MAP2 (\ty av. LENGTH (enc ty av)) tys avs) <=
    LENGTH (FLAT (abi_tuple_heads hl tl tys avs)) +
    LENGTH (FLAT (abi_tuple_tails tys avs))
Proof
  Induct >> Cases_on `avs` >> simp[abi_tuple_heads_def, abi_tuple_tails_def] >>
  rpt strip_tac >> rename1 `enc ty av` >>
  Cases_on `is_dynamic ty` >>
  gvs[abi_tuple_heads_def, abi_tuple_tails_def, abi_member_tail_size_def] >>
  first_x_assum (qspecl_then [`t`, `hl`, `tl + abi_member_tail_size ty av`] mp_tac) >>
  simp[abi_member_tail_size_def] >> decide_tac
QED

Theorem tuple_encoding_member_sum_bound:
  LENGTH tys = LENGTH avs ==>
    SUM (MAP2 (\ty av. LENGTH (enc ty av)) tys avs) <=
    LENGTH (enc (Tuple tys) (ListV avs))
Proof
  strip_tac >> simp[Once enc_def, enc_tuple_parts] >>
  once_rewrite_tac[ADD_COMM] >> irule tuple_parts_encoding_sum >> simp[]
QED

Theorem encoding_index_sum_bound[local]:
  !tys avs i. LENGTH tys = LENGTH avs /\ i < LENGTH tys ==>
    LENGTH (enc (EL i tys) (EL i avs)) <=
    SUM (MAP2 (\ty av. LENGTH (enc ty av)) tys avs)
Proof
  Induct >> Cases_on `avs` >> simp[] >>
  Cases_on `i` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >>
  disch_then (qspec_then `n` mp_tac) >> simp[] >> decide_tac
QED

Theorem tuple_encoding_member_bound:
  LENGTH tys = LENGTH avs /\ i < LENGTH tys ==>
    LENGTH (enc (EL i tys) (EL i avs)) <=
    LENGTH (enc (Tuple tys) (ListV avs))
Proof
  strip_tac >> drule_all encoding_index_sum_bound >>
  drule tuple_encoding_member_sum_bound >> decide_tac
QED

Theorem positive_encoding_count_sum[local]:
  !tys avs. LENGTH tys = LENGTH avs /\
    EVERY (\p. 0 < LENGTH (enc (FST p) (SND p))) (ZIP (tys,avs)) ==>
    LENGTH tys <= SUM (MAP2 (\ty av. LENGTH (enc ty av)) tys avs)
Proof
  Induct >> Cases_on `avs` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> decide_tac
QED

Theorem tuple_encoding_positive_member_count:
  LENGTH tys = LENGTH avs /\
  EVERY (\p. 0 < LENGTH (enc (FST p) (SND p))) (ZIP (tys,avs)) /\
  LENGTH (enc (Tuple tys) (ListV avs)) < dimword (:256) ==>
  LENGTH tys < dimword (:256)
Proof
  strip_tac >> drule_all positive_encoding_count_sum >>
  drule tuple_encoding_member_sum_bound >> decide_tac
QED
