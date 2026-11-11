Theory lowerDloadAccessClassification
Ancestors
  lowerDloadPairedBoundary lowerDloadRelocation lowerDloadOwnership
  ptrDiscipline memLocDefs venomState finite_map list words

Theorem ld_access_read_classification:
  access_ok lo (ld_erase AG) fn inst s /\ ~in_revert_forward fn s /\
  MEM (off,len) (source_memory_read_ranges inst s) /\ len <> 0 ==>
  (off+len <= lo /\ (!ops. mem_read_ops inst = SOME ops ==>
    op_prov (ld_erase AG) ops.iao_ofst = NONE)) \/
  (?ops v owner bs sz. mem_read_ops inst = SOME ops /\
    ops.iao_ofst = Var v /\ FLOOKUP AG v = SOME(owner,(bs,sz)) /\
    bs <= off /\ off+len <= bs+sz)
Proof
  strip_tac >>
  Cases_on `lo < off+len \/ ?ops. mem_read_ops inst = SOME ops /\
    op_prov (ld_erase AG) ops.iao_ofst <> NONE`
  >- (disj2_tac >> fs[access_ok_def] >>
      qpat_x_assum `!off len. MEM (off,len) (source_memory_read_ranges _ _) /\ _ ==> _`
        (qspecl_then [`off`,`len`] mp_tac) >>
      simp[] >> strip_tac >>
      gvs[ld_erase_lookup, optionTheory.OPTION_MAP_EQ_SOME] >>
      metis_tac[pairTheory.PAIR]) >>
  disj1_tac >> gvs[]
QED

Theorem ld_access_write_classification:
  access_ok lo (ld_erase AG) fn inst s /\ ~in_revert_forward fn s /\
  MEM (off,len) (source_memory_write_ranges inst s) /\ len <> 0 ==>
  (off+len <= lo /\ (!ops. mem_write_ops inst = SOME ops ==>
    op_prov (ld_erase AG) ops.iao_ofst = NONE)) \/
  (?ops v owner bs sz. mem_write_ops inst = SOME ops /\
    ops.iao_ofst = Var v /\ FLOOKUP AG v = SOME(owner,(bs,sz)) /\
    bs <= off /\ off+len <= bs+sz)
Proof
  strip_tac >>
  Cases_on `lo < off+len \/ ?ops. mem_write_ops inst = SOME ops /\
    op_prov (ld_erase AG) ops.iao_ofst <> NONE`
  >- (disj2_tac >> fs[access_ok_def] >>
      qpat_x_assum `!off len. MEM (off,len) (source_memory_write_ranges _ _) /\ _ ==> _`
        (qspecl_then [`off`,`len`] mp_tac) >>
      simp[] >> strip_tac >>
      gvs[ld_erase_lookup, optionTheory.OPTION_MAP_EQ_SOME] >>
      metis_tac[pairTheory.PAIR]) >>
  disj1_tac >> gvs[]
QED

Theorem ld_owned_address_transport:
  ld_owned_vars V E AG AH tn un s t /\ v IN V /\
  FLOOKUP AG v = SOME(owner,(bs,sz)) /\
  eval_operand (Var v) s = SOME x /\ eval_operand (Var v) t = SOME y /\
  bs <= w2n x /\ w2n x+len <= bs+sz /\ 0<len /\
  bs+sz < dimword(:256) /\
  (!bt. ld_site_entry E owner bs bt sz ==> bt+sz < dimword(:256)) ==>
  ?bt. ld_site_entry E owner bs bt sz /\
    FLOOKUP AH v = SOME(owner,(bt,sz)) /\
    w2n y = bt+(w2n x-bs) /\ w2n y+len <= bt+sz
Proof
  strip_tac >>
  drule ld_owned_operand_value >>
  disch_then (qspecl_then [`y`,`x`,`Var v`] mp_tac) >>
  simp[ld_op_prov_def, ld_owned_value_def] >> strip_tac >>
  qexists_tac `bt` >> simp[] >>
  `w2n x <= bs+sz` by decide_tac >>
  `bt+sz < dimword(:256)` by metis_tac[] >>
  drule_all ld_ptr_rel_endpoint >> strip_tac >> simp[] >> decide_tac
QED
