(* Shared physical preparation for the joint Extract32 judgment. *)
Theory bodyFullExtract32Prepare
Ancestors
  bodyFullUnwrapRun bodyFullGhostFrame bodyPtrTypeBuiltinsExtract32HeaderFrame
  bodyPtrSignedConvertSourceCompile bodyMemTbExtract32Source
  exprPtrCtorImmStore typedCopyLoopHeaderPtr bodyPtrSignedConvertLoad
  bodyPtrSignedConvertSourcePrefix exprSimExtract32Post
  fragExecMem instMemFrontier fragGasSeqPtr venomInstProofs
  typedCopyPtr ptrDiscipline ptrSafeRun compileEnv venomState words
  venomExecSemantics venomInst bodyPtrDefs finite_map list fragExec wordLoadStorePtr
  emitHelperProps exprLoweringProps ghostPcTransportPtr codegenRel contextCodegenRel
  instIdxIndep rawCallBufferPtr gasOutcomeFull vyperStorageTrace
  vyperStorageFootprint exprSimMemDefs allocaHistory

Theorem extract32_prepare_checks[local]:
  ALL_DISTINCT [src;len;data] /\ lookup_var src s = SOME a /\
  ptr_covers G tn src s capacity /\ 32 <= capacity /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?u G2 tn2.
    run_inst_seq [mk_inst id MLOAD [Var src] [len];
      mk_inst (id+1) ADD [Var src; Lit 32w] [data]] s = OK u /\
    (!D lo. allocas_from lo s ==>
      inst_seq_ptr D lo ctx func PG G tn
        [mk_inst id MLOAD [Var src] [len];
         mk_inst (id+1) ADD [Var src; Lit 32w] [data]] s G2 tn2) /\
    lookup_var len u = SOME (mload (w2n a) s) /\
    lookup_var data u = SOME (a+32w) /\
    op_taint tn2 (Var len) = {} /\ op_prov G2 (Var len) = NONE /\
    tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
    tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm /\
    u = s with vs_vars := u.vs_vars /\
    (!p. p <> len /\ p <> data ==> lookup_var p u = lookup_var p s /\
      FLOOKUP G2 p = FLOOKUP G p /\
      op_taint tn2 (Var p) = op_taint tn (Var p)) /\
    (!n. 32 < capacity /\ 32+n <= capacity /\ w2n a+32 < dimword(:256) ==>
      ptr_covers G2 tn2 data u n)
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `run_inst_seq [i1;i2] s` >>
  qabbrev_tac `s1 = update_var len (mload (w2n a) s) s` >>
  qabbrev_tac `G1 = step_prov PG G i1 s1` >>
  qabbrev_tac `tn1 = step_taint i1 s s1 tn` >>
  `step_inst_base i1 s = OK s1` by
    simp[Abbr `i1`, Abbr `s1`, step_MLOAD, eval_operand_def] >>
  `src <> len /\ src <> data /\ len <> data` by gvs[ALL_DISTINCT] >>
  `lookup_var src s1 = SOME a` by
    fs[Abbr `s1`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `op_taint tn1 (Var src) = {} /\ ptr_covers G1 tn1 src s1 capacity` by
    (gvs[ptr_covers_def, Abbr `G1`, Abbr `tn1`, Abbr `i1`, Abbr `s1`,
         mload_ambient_frame, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `op_taint tn1 (Var len) = {}` by
    (simp[Abbr `tn1`, Abbr `i1`, Abbr `s1`] >>
     irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def]) >>
  qabbrev_tac `s2 = update_var data (a+32w) s1` >>
  qabbrev_tac `G2 = step_prov PG G1 i2 s2` >>
  qabbrev_tac `tn2 = step_taint i2 s1 s2 tn1` >>
  `step_inst_base i2 s1 = OK s2` by
    simp[Abbr `i2`, Abbr `s2`, step_ADD, eval_operand_def] >>
  `!n. 32 < capacity /\ 32+n <= capacity /\ w2n a+32 < dimword(:256) ==>
    ptr_covers G2 tn2 data s2 n` by
    (rpt strip_tac >>
     simp[Abbr `G2`, Abbr `tn2`, Abbr `i2`, Abbr `s2`] >>
     irule typed_copy_loop_dynamic_offset_covers >>
     simp[eval_operand_def] >> qexists_tac `capacity` >> simp[arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`s2`,`G2`,`tn2`] >>
  conj_tac >- simp[run_inst_seq_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `ptr_covers G tn src s 32` by
        (gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      `ptr_inst_ok D lo 0 ctx func G tn i1 s` by
        (simp[Abbr `i1`] >> irule ptr_inst_ok_mload_lo >> simp[]) >>
      simp[inst_seq_ptr_def] >>
      `allocas_from lo (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
        simp[Abbr `s1`, update_var_def, allocas_from_def] >>
      simp[Abbr `G2`, Abbr `tn2`] >>
      conj_tac
      >- (simp[Abbr `i2`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
               mk_inst_def, source_memory_write_ranges_def,
               source_memory_read_ranges_def, op_taint_def,
               step_inst_non_invoke, step_ADD, eval_operand_def] >>
          conj_tac >- (gen_tac >> Cases_on `op = Var src` >> simp[GSYM op_taint_def] >> Cases_on `op = Lit 32w` >> simp[op_taint_def]) >>
          simp[GSYM mk_inst_def, step_inst_inst_idx_indep, is_terminator_def,
               exec_result_map_def, Abbr `s2`, update_var_def]) >>
      `~is_terminator i2.inst_opcode` by simp[Abbr `i2`, mk_inst_def, is_terminator_def] >>
      simp[step_inst_inst_idx_indep, exec_result_map_def]) >>
  simp[] >>
  simp[Abbr `G2`, Abbr `tn2`, Abbr `i2`, Abbr `s2`,
       copy_len_binop_ghost_frame, Abbr `G1`, Abbr `tn1`, Abbr `i1`,
       Abbr `s1`, mload_ambient_frame, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, step_taint_def, mk_inst_def, set_var_taint_def,
       imm_taint_def, op_prov_def, step_prov_def, out_prov_def, set_prov_def,
       FLOOKUP_DRESTRICT] >>
  simp[mem_taint_def, store_taint_def, adopt_reset_def,
       new_site_bytes_def, step_writes_def, written_taint_def, range_bytes_def,
       source_memory_write_ranges_def, GSYM finite_mapTheory.FLOOKUP_DEF,
       pred_setTheory.EXTENSION] >> simp[FLOOKUP_DEF] >> metis_tac[]
QED

Theorem extract32_prepare_full:
  compile_bytestring_src (Var sv) sm = ((lenop,dataop),sn) /\
  not_fresh_at sm sv /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx src es sa sm s0 ee (BytesV bs) (Var sv) s /\
    expr_store_bound cx (expr_type src) (BytesV bs) (Var sv) s /\
    ptr_val_ok cx (expr_type src) (BytesV bs) (Var sv) G tn s /\
    ptr_buf_ok cenv src (Var sv) G s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
  ?p u G2 tn2 len data.
    lenop = Var len /\ dataop = Var data /\
    not_fresh_at sn sv /\ not_fresh_at sn len /\ not_fresh_at sn data /\
    op_taint tn2 (Var len) = {} /\ op_prov G2 (Var len) = NONE /\
    u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
    tn2.t_mem = tn.t_mem /\
    eval_operand (Var sv) u = SOME (n2w p) /\
    eval_operand lenop u = SOME (n2w (LENGTH bs)) /\
    eval_operand dataop u = SOME (n2w (p+32)) /\
    mem_word_at p u.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (p+32) (LENGTH bs) u.vs_memory = bs /\
    p+32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
    p+32+LENGTH bs <= u.vs_alloca_next /\
    (!n. 0 < LENGTH bs /\ n <= LENGTH bs ==> ptr_covers G2 tn2 data u n) /\
    u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\ alloca_history func u /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,G2,tn2) /\
      expr_post H ctx func cenv cx src es sa sn s0 ee (BytesV bs) (Var sv) u /\
      expr_store_bound cx (expr_type src) (BytesV bs) (Var sv) u /\
      ptr_val_ok cx (expr_type src) (BytesV bs) (Var sv) G2 tn2 u /\
      ptr_buf_ok cenv src (Var sv) G2 u /\
      ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 u /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    gvs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all bodyMemTbExtract32SourceTheory.extract32_source_post_view >>
  disch_then (qx_choose_then `p` strip_assume_tac) >>
  `ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) G tn s /\
   op_taint tn (Var sv) = {}` by gvs[ptr_val_ok_def, is_word_type_def] >>
  drule_all ptr_mem_ok_dynamic_bytes_site >> strip_tac >>
  drule_all ptr_mem_ok_dynamic_bytes_clean >> strip_tac >>
  suspend "physical"
QED

Resume extract32_prepare_full[physical]:
  `ptr_covers G tn sv s (32+LENGTH bs)` by
    (gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  drule_all compile_bytestring_src_shape_fresh >> strip_tac >>
  `lookup_var sv s = SOME (n2w p)` by gvs[eval_operand_def] >>
  `32 <= 32+LENGTH bs` by simp[] >>
  drule_all extract32_prepare_checks >>
  disch_then (qspecl_then [`sm.cs_next_id`,`func`,`PG`] strip_assume_tac) >>
  `!z. Var sv = Var z ==> not_fresh_at sm z` by simp[] >>
  drule_all extract32_source_snapshot >> strip_tac >>
  `t = u` by metis_tac[exec_result_11] >>
  qpat_x_assum `t = u` SUBST_ALL_TAC >>
  drule_all extract32_prepare_site >> strip_tac >>
  qabbrev_tac `v = u with vs_inst_idx := LENGTH sn.cs_current_insts` >>
  `v = s with <|vs_vars := v.vs_vars; vs_inst_idx := v.vs_inst_idx|>` by
    (simp[Abbr `v`] >> qpat_x_assum `u = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `!z. not_fresh_at sm z ==> lookup_var z v = lookup_var z s /\
    FLOOKUP G2 z = FLOOKUP G z /\ op_taint tn2 (Var z) = op_taint tn (Var z)` by
    (rpt strip_tac >> `z <> len /\ z <> data` by metis_tac[] >>
     simp[Abbr `v`, lookup_var_def] >>
     metis_tac[lookup_var_def]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `alloca_history func v` by
    (simp[Abbr `v`, NoAsms] >> irule emitted_alloca_history >> simp[] >>
     qexistsl_tac [`emitted_insts sm sn`,`s`,`sm`] >>
     simp[mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`p`,`v`,`G2`,`tn2`,`len`,`data`] >>
  simp[Abbr `v`, eval_operand_def, lookup_var_def] >>
  suspend "posts"
QED

Resume extract32_prepare_full[posts]:
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  conj_tac
  >- (qpat_assum `LENGTH sn.cs_current_insts = _` (fn th => rewrite_tac[GSYM th]) >>
      irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
      simp[NoAsms] >> conj_tac >- simp[] >>
      qexistsl_tac [`emitted_insts sm sn`,`sm`] >>
      simp[mk_inst_def, is_terminator_def] >>
      qpat_assum `!D lo. allocas_from lo s ==> _`
        (qspecl_then [`DF H`,`lo`] mp_tac) >>
      gvs[ghost_inv_at_def, mk_inst_def]) >>
  conj_tac
  >- (irule extract32_prepare_post_readonly >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`s`,`sm`] >>
      gvs[eval_operand_def, lookup_var_def] >>
      qpat_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
      simp[]) >>
  conj_tac
  >- (gvs[expr_store_bound_def, eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[ptr_val_ok_def, ptr_mem_ok_def, is_word_type_def,
          eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[ptr_buf_ok_def, eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  conj_tac
  >- (irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G`,`ee`,`s`,`sm`,`tn`] >>
      qpat_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
      simp[] >> gvs[]) >>
  irule ghost_kept_at_clean_suffix >>
  qexistsl_tac [`G`,`tn`] >> simp[] >>
  qx_gen_tac `z` >> strip_tac >>
  `not_fresh_at sm z` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  metis_tac[]
QED

Finalise extract32_prepare_full
