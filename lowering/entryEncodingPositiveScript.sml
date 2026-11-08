Theory entryEncodingPositive
Ancestors
  entryEncodingCardinality abiCanonicalHeadSize abiDecodeRanges contractABI byte

Theorem positive_encoding_sum[local]:
  !tys avs. LENGTH tys = LENGTH avs /\
    EXISTS (\p. 0 < LENGTH (enc (FST p) (SND p))) (ZIP (tys,avs)) ==>
    0 < SUM (MAP2 (\ty av. LENGTH (enc ty av)) tys avs)
Proof
  Induct >> Cases_on `avs` >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `t` mp_tac) >> simp[] >> decide_tac
QED

Theorem tuple_encoding_positive_member:
  LENGTH tys = LENGTH avs /\
  EXISTS (\p. 0 < LENGTH (enc (FST p) (SND p))) (ZIP (tys,avs)) ==>
  0 < LENGTH (enc (Tuple tys) (ListV avs))
Proof
  strip_tac >> drule_all positive_encoding_sum >>
  drule tuple_encoding_member_sum_bound >> decide_tac
QED

Theorem dynamic_array_encoding_positive:
  0 < LENGTH (enc (Array NONE aty) (ListV avs))
Proof
  pure_rewrite_tac[canonical_array_tuple] >>
  simp[enc_number_def, LENGTH_word_to_bytes, Excl "enc_def"]
QED

Theorem fixed_array_encoding_positive:
  avs <> [] /\ EVERY (\av. 0 < LENGTH (enc aty av)) avs ==>
  0 < LENGTH (enc (Array (SOME n) aty) (ListV avs))
Proof
  strip_tac >> pure_rewrite_tac[canonical_array_tuple] >> simp[Excl "enc_def"] >>
  irule tuple_encoding_positive_member >> simp[] >>
  Cases_on `avs` >> gvs[]
QED
