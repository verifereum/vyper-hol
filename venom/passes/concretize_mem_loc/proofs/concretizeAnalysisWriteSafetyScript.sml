Theory concretizeAnalysisWriteSafety
Ancestors
  ptrDiscipline arithmetic list finite_map

Theorem confined_full_interval_start:
  !b off sz:num. b <= off /\ off + sz <= b + sz ==> off = b
Proof
  decide_tac
QED

Theorem access_ok_full_write_start:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  FLOOKUP G v = SOME (b,sz) /\
  MEM (off,sz) (source_memory_write_ranges inst s) /\ sz <> 0 ==>
  off = b
Proof
  rpt strip_tac >> gvs[access_ok_def, op_prov_def] >>
  qpat_x_assum `!off' len. MEM (off',len) (source_memory_write_ranges inst s) /\ _ ==> _`
    (qspecl_then [`off`,`sz`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem access_ok_full_write_covers:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  FLOOKUP G v = SOME (b,sz) /\
  MEM (off,sz) (source_memory_write_ranges inst s) /\ sz <> 0 /\
  b <= x /\ x < b + sz ==>
  off <= x /\ x < off + sz
Proof
  metis_tac[access_ok_full_write_start]
QED
