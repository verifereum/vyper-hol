Theory abiEncodeTupleCongruence
Ancestors
  contractABI abiDecodeRanges list pair arithmetic

Theorem abi_encode_tuple_parts_cong[local]:
  !ats avs bts bvs hl tl hds tls.
    LENGTH ats = LENGTH avs /\ LENGTH bts = LENGTH bvs /\
    LIST_REL (\(at,av) (bt,bv).
      enc at av = enc bt bv /\ is_dynamic at = is_dynamic bt /\
      abi_member_head_size at = abi_member_head_size bt)
      (ZIP (ats,avs)) (ZIP (bts,bvs)) ==>
    enc_tuple hl tl ats avs hds tls = enc_tuple hl tl bts bvs hds tls
Proof
  Induct >> Cases_on `avs` >> Cases_on `bts` >> Cases_on `bvs` >>
  simp[] >> rpt strip_tac >>
  simp[Once enc_def]
QED

Theorem abi_encode_tuple_heads_cong[local]:
  !ats avs bts bvs.
    LENGTH ats = LENGTH avs /\ LENGTH bts = LENGTH bvs /\
    LIST_REL (\(at,av) (bt,bv).
      enc at av = enc bt bv /\ is_dynamic at = is_dynamic bt /\
      abi_member_head_size at = abi_member_head_size bt)
      (ZIP (ats,avs)) (ZIP (bts,bvs)) ==>
    SUM (MAP abi_member_head_size ats) = SUM (MAP abi_member_head_size bts)
Proof
  Induct >> Cases_on `avs` >> Cases_on `bts` >> Cases_on `bvs` >>
  simp[] >> metis_tac[]
QED

Theorem abi_encode_tuple_congruence:
  LENGTH ats = LENGTH avs /\ LENGTH bts = LENGTH bvs /\
  LIST_REL (\(at,av) (bt,bv).
    enc at av = enc bt bv /\ is_dynamic at = is_dynamic bt /\
    abi_member_head_size at = abi_member_head_size bt)
    (ZIP (ats,avs)) (ZIP (bts,bvs)) ==>
  enc (Tuple ats) (ListV avs) = enc (Tuple bts) (ListV bvs)
Proof
  strip_tac >> drule_all abi_encode_tuple_heads_cong >> strip_tac >>
  simp[Once enc_def, head_lengths_acc] >>
  irule abi_encode_tuple_parts_cong >> simp[]
QED
