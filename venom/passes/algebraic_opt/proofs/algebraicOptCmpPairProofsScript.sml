Theory algebraicOptCmpPairProofs
Ancestors
  algebraicOptCmpScanProofs algebraicOptDefs dfgDefs venomInst list

Definition ao_cmp_pairs_def:
  ao_cmp_pairs dfg xs fs rs ins <=>
    EVERY (\f. ?i. MEM i xs /\ ao_cmp_flip_cert dfg i f /\
      ((?r. MEM r rs /\ ao_cmp_remove_cert dfg i r) \/
       (?a. MEM a ins /\ ao_cmp_insert_cert dfg i a))) fs /\
    EVERY (\r. ?i f. MEM i xs /\ MEM f fs /\
      ao_cmp_remove_cert dfg i r /\ ao_cmp_flip_cert dfg i f) rs /\
    EVERY (\a. ?i f. MEM i xs /\ MEM f fs /\
      ao_cmp_insert_cert dfg i a /\ ao_cmp_flip_cert dfg i f) ins
End

Theorem ao_cmp_pairs_empty:
  ao_cmp_pairs dfg [] [] [] []
Proof
  simp[ao_cmp_pairs_def]
QED

Theorem ao_cmp_pairs_extend:
  ao_cmp_pairs dfg xs fs rs ins ==>
  ao_cmp_pairs dfg (h::xs) fs rs ins
Proof
  simp[ao_cmp_pairs_def, EVERY_MEM] >> metis_tac[]
QED

Theorem ao_cmp_pairs_remove:
  ao_cmp_pairs dfg xs fs rs ins /\
  ao_cmp_flip_cert dfg h f /\ ao_cmp_remove_cert dfg h r ==>
  ao_cmp_pairs dfg (h::xs) (f::fs) (r::rs) ins
Proof
  simp[ao_cmp_pairs_def, EVERY_MEM] >> metis_tac[]
QED

Theorem ao_cmp_pairs_insert:
  ao_cmp_pairs dfg xs fs rs ins /\
  ao_cmp_flip_cert dfg h f /\ ao_cmp_insert_cert dfg h a ==>
  ao_cmp_pairs dfg (h::xs) (f::fs) rs (a::ins)
Proof
  simp[ao_cmp_pairs_def, EVERY_MEM] >> metis_tac[]
QED

Theorem ao_cmp_pairs_head:
  ao_cmp_flip_scan dfg xs = (fs,rs,ins) /\
  ao_cmp_pairs dfg xs fs rs ins /\
  ao_cmp_flip_scan dfg (h::xs) = (fs',rs',ins') ==>
  ao_cmp_pairs dfg (h::xs) fs' rs' ins'
Proof
  strip_tac >>
  drule ao_cmp_pairs_extend >>
  disch_then (qspec_then `h` assume_tac) >>
  qpat_x_assum `ao_cmp_flip_scan dfg (h::xs) = _` mp_tac >>
  simp[Once ao_cmp_flip_scan_def] >> disch_tac >>
  Cases_on `is_comparator h.inst_opcode` >> gvs[] >>
  Cases_on `h.inst_operands` >> gvs[] >>
  rename1 `h.inst_operands = op::ops` >>
  Cases_on `ops` >> gvs[] >>
  rename1 `h.inst_operands = op::arg::ops` >>
  Cases_on `ops` >> gvs[] >>
  Cases_on `arg` >> gvs[] >>
  Cases_on `h.inst_outputs` >> gvs[] >>
  rename1 `h.inst_outputs = v::outs` >>
  Cases_on `outs` >> gvs[] >>
  Cases_on `LENGTH (dfg_get_uses dfg v) = 1` >> gvs[] >>
  Cases_on `(HD (dfg_get_uses dfg v)).inst_opcode = ISZERO \/
            (HD (dfg_get_uses dfg v)).inst_opcode = ASSERT`
  >- (pairarg_tac >> gvs[] >>
      Cases_on `c = never` >> gvs[] >>
      `dfg_get_uses dfg v = [HD (dfg_get_uses dfg v)]` by
        (Cases_on `dfg_get_uses dfg v` >> gvs[] >>
         rename1 `LENGTH tail = 0` >> Cases_on `tail` >> gvs[]) >>
      `ao_cmp_source dfg h op c v (HD (dfg_get_uses dfg v))` by
        (simp[ao_cmp_source_def] >> metis_tac[]) >>
      Cases_on `(HD (dfg_get_uses dfg v)).inst_opcode = ISZERO` >> gvs[]
      >- (Cases_on `(HD (dfg_get_uses dfg v)).inst_outputs` >> gvs[] >>
          rename1 `(HD (dfg_get_uses dfg v)).inst_outputs = iz::outs` >>
          Cases_on `outs` >> gvs[] >>
          Cases_on `LENGTH (dfg_get_uses dfg iz) = 1` >> gvs[] >>
          Cases_on `(HD (dfg_get_uses dfg iz)).inst_opcode = ASSERT` >> gvs[] >>
          irule ao_cmp_pairs_remove >>
          metis_tac[ao_cmp_flip_cert_intro, ao_cmp_remove_cert_intro]) >>
      irule ao_cmp_pairs_insert >>
      metis_tac[ao_cmp_flip_cert_intro, ao_cmp_insert_cert_intro]) >>
  gvs[]
QED

Theorem ao_cmp_flip_scan_pairs:
  !xs dfg fs rs ins.
    ao_cmp_flip_scan dfg xs = (fs,rs,ins) ==>
    ao_cmp_pairs dfg xs fs rs ins
Proof
  Induct >> rpt gen_tac
  >- simp[ao_cmp_flip_scan_def, ao_cmp_pairs_empty] >>
  Cases_on `ao_cmp_flip_scan dfg xs` >>
  rename1 `ao_cmp_flip_scan dfg xs = (fs0, rest)` >>
  Cases_on `rest` >> strip_tac >>
  irule ao_cmp_pairs_head >> metis_tac[]
QED

Theorem ao_cmp_flip_scan_flip_pair:
  ao_cmp_flip_scan dfg xs = (fs,rs,ins) /\ MEM f fs ==>
  ?i. MEM i xs /\ ao_cmp_flip_cert dfg i f /\
      ((?r. MEM r rs /\ ao_cmp_remove_cert dfg i r) \/
       (?a. MEM a ins /\ ao_cmp_insert_cert dfg i a))
Proof
  strip_tac >> drule ao_cmp_flip_scan_pairs >>
  simp[ao_cmp_pairs_def, EVERY_MEM] >> metis_tac[]
QED

Theorem ao_cmp_flip_scan_remove_pair:
  ao_cmp_flip_scan dfg xs = (fs,rs,ins) /\ MEM r rs ==>
  ?i f. MEM i xs /\ MEM f fs /\
    ao_cmp_remove_cert dfg i r /\ ao_cmp_flip_cert dfg i f
Proof
  strip_tac >> drule ao_cmp_flip_scan_pairs >>
  simp[ao_cmp_pairs_def, EVERY_MEM] >> metis_tac[]
QED

Theorem ao_cmp_flip_scan_insert_pair:
  ao_cmp_flip_scan dfg xs = (fs,rs,ins) /\ MEM a ins ==>
  ?i f. MEM i xs /\ MEM f fs /\
    ao_cmp_insert_cert dfg i a /\ ao_cmp_flip_cert dfg i f
Proof
  strip_tac >> drule ao_cmp_flip_scan_pairs >>
  simp[ao_cmp_pairs_def, EVERY_MEM] >> metis_tac[]
QED

