Theory concretizePtrKillBoundary
Ancestors
  concretizePtrReadCoverage concretizeMemLocDefs memLocDefs
  ptrDiscipline codegenRel venomExecSemantics venomState

Theorem ptr_literal_write_range_size:
  !inst s n off len.
    inst_write_size inst = SOME n /\
    MEM (off,len) (source_memory_write_ranges inst s) ==> len = n
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_opcode` >>
  simp[inst_write_size_def, mem_write_ops_def,
       source_memory_write_ranges_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), fixed_source_write_range_def,
      sized_source_write_range_def] >>
  gvs[eval_operand_def, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >>
  qpat_x_assum `MEM _ _` mp_tac >>
  Cases_on `eval_operand dst s` >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Theorem ptr_guarded_kill_exact:
  !a bp sizes inst lo G fn s ops v b sz off len.
    ptr_ml_can_kill a bp sizes inst /\ sizes a = SOME sz /\
    mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP G v = SOME (b,sz) /\ access_ok lo G fn inst s /\
    ~in_revert_forward fn s /\
    MEM (off,len) (source_memory_write_ranges inst s) /\ len <> 0 ==>
    (off,len) = (b,sz)
Proof
  rpt strip_tac >>
  `inst_write_size inst = SOME sz` by gvs[ptr_ml_can_kill_def] >>
  `len = sz` by metis_tac[ptr_literal_write_range_size] >>
  gvs[access_ok_def, op_prov_def] >>
  qpat_x_assum `!off' len'. MEM _ (source_memory_write_ranges _ _) /\ _ ==> _`
    (qspecl_then [`off`, `len`] mp_tac) >>
  simp[]
QED
