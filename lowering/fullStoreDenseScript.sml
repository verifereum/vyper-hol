(* Dense memory-to-slot stores, with one joint execution witness. *)
Theory fullStoreDense
Ancestors
  fragGasCopyLoop fragGasOriginPtrDead fragGasSeqPtr
  placeStoreCopyPath bodyMemAssignTopCopyPaths
  wordLoadStorePtr assignBasePtrWordStore stmtSimStoreCopy decoderGhostFramePtr
  context emitHelper emitHelperProps compileEnv codegenRel contextCodegenRel
  unitTransformDefs exprLoweringProps exprSimPtrTopLevelStorageCopy loweringStateRelDefs
  ptrDiscipline bodyPtrDefs instMemFrontier fragExecMem memSafeRun fragExec
  venomExecSemantics venomState venomInst
  finite_map pred_set list rich_list arithmetic words

Theorem dense_single_inst_seq_ptr:
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME a /\
  eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
  (!x. dst = Var x ==> x <> tmp) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_call_ctx.cc_static ==>
  !D func PG id tr.
  inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst id MLOAD [Var root] [tmp];
     mk_inst (id+1) (if tr then TSTORE else SSTORE) [dst;Var tmp] []] s
    (DRESTRICT G (COMPL {tmp}))
    (if tr then (tn with t_var := tn.t_var |+ (tmp,mem_word_taint tn.t_mem (w2n a)))
       with t_trans := key_update tn.t_trans k (mem_word_taint tn.t_mem (w2n a))
     else (tn with t_var := tn.t_var |+ (tmp,mem_word_taint tn.t_mem (w2n a)))
       with t_stor := key_update tn.t_stor k (mem_word_taint tn.t_mem (w2n a)))
Proof
  strip_tac >> rpt gen_tac >>
  `ptr_inst_ok D 0 0 ctx func G tn (mk_inst id MLOAD [Var root] [tmp]) s` by
    (irule ptr_inst_ok_mload >> simp[]) >>
  `eval_operand dst (update_var tmp (mload (w2n a) s) s) = SOME k` by
    (Cases_on `dst` >> gvs[eval_operand_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE]) >>
  `op_taint (step_taint (mk_inst id MLOAD [Var root] [tmp]) s
       (update_var tmp (mload (w2n a) s) s) tn) dst = {}` by
    (Cases_on `dst` >> gvs[step_taint_other_output, mk_inst_def, op_taint_def]) >>
  `ptr_inst_ok D 0 0 ctx func
     (step_prov PG G (mk_inst id MLOAD [Var root] [tmp])
       (update_var tmp (mload (w2n a) s) s))
     (step_taint (mk_inst id MLOAD [Var root] [tmp]) s
       (update_var tmp (mload (w2n a) s) s) tn)
     (mk_inst (id+1) (if tr then TSTORE else SSTORE) [dst;Var tmp] [])
     (update_var tmp (mload (w2n a) s) s with vs_inst_idx := SUC s.vs_inst_idx)` by
    ((irule assign_base_ptr_inst_ok_storage_word >>
     simp[allocas_below_fmp_def, update_var_def] >> Cases_on `tr` >> simp[] >> (gvs[allocas_below_fmp_def, update_var_def, assign_base_ptr_inst_ok_storage_word]))) >>
  Cases_on `tr` >>
  gvs[inst_seq_ptr_def, step_inst_base_opcode_eqs, mk_inst_def,
    exec_read1_def, exec_write2_def, eval_operand_def, update_var_def,
    lookup_var_def, step_prov_def, set_prov_def, out_prov_def,
    step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
    mem_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
    step_writes_def, source_memory_write_ranges_def, written_taint_def,
    range_bytes_def, new_site_bytes_def, FLOOKUP_UPDATE, SF CONJ_ss,
    sstore_def, tstore_def, FLOOKUP_DEF, DRESTRICT_UNIV,
    SF ETA_ss] >> simp[taint_component_equality]
QED

Theorem dense_single_origin_ptr:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id MLOAD [Var root] [tmp];
    mk_inst (id+1) (if tr then TSTORE else SSTORE) [dst;Var tmp] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME a /\
  eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
  (!x. dst = Var x ==> x <> tmp) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  allocas_from lo s /\ w2n a + 32 <= s.vs_alloca_next /\
  ~s.vs_call_ctx.cc_static ==>
  !D explicit PG.
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK ((if tr then tstore else sstore) k (mload (w2n a) s)
        (update_var tmp (mload (w2n a) s) s) with vs_inst_idx := s.vs_inst_idx+2),
     DRESTRICT G (COMPL {tmp}),
     if tr then (tn with t_var := tn.t_var |+ (tmp,mem_word_taint tn.t_mem (w2n a)))
       with t_trans := key_update tn.t_trans k (mem_word_taint tn.t_mem (w2n a))
     else (tn with t_var := tn.t_var |+ (tmp,mem_word_taint tn.t_mem (w2n a)))
       with t_stor := key_update tn.t_stor k (mem_word_taint tn.t_mem (w2n a)))
Proof
  strip_tac >> rpt gen_tac >>
  drule_all dense_single_inst_seq_ptr >>
  disch_then (qspecl_then [`D`,`func`,`PG`,`id`,`tr`] assume_tac) >>
  `eval_operand dst (update_var tmp (mload (w2n a) s) s) = SOME k` by
    (Cases_on `dst` >> gvs[eval_operand_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE]) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) run_inst_seq_origin_ptr_lift >>
  disch_then (qspecl_then [`(if tr then tstore else sstore) k (mload (w2n a) s)
    (update_var tmp (mload (w2n a) s) s)`, `lo`, `explicit`] mp_tac) >>
  fs[mk_inst_def, is_terminator_def] >>
  (impl_tac >-
    (Cases_on `tr` >>
     fs[run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, mk_inst_def, is_terminator_def,
       exec_read1_def, exec_write2_def, eval_operand_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE, sstore_def, tstore_def])) >>
  simp[]
QED

Theorem dense_single_compiled_origin_ptr_uniform:
  (do loaded <- emit_op MLOAD [Var root];
      emit_void (if tr then TSTORE else SSTORE) [dst;loaded]
   od) sa = (z,sb) /\ fn_has_code sa sb func /\
  not_fresh_at sa root /\ (!x. dst = Var x ==> not_fresh_at sa x) /\
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME a /\
  eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  w2n a + 32 <= s.vs_alloca_next /\ ~s.vs_call_ctx.cc_static /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    store_copy_frame sa (if tr then LocTransient else LocStorage) a k s 1 t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
    toplevel_copy_source_taint (if tr then LocTransient else LocStorage) tnf =
      key_update (toplevel_copy_source_taint (if tr then LocTransient else LocStorage) tn)
        k (mem_word_taint tn.t_mem (w2n a)) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `?tmp. sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id MLOAD [Var root] [tmp];
       mk_inst (sa.cs_next_id+1) (if tr then TSTORE else SSTORE) [dst;Var tmp] []] /\
    (!x. not_fresh_at sa x ==> x <> tmp)` by
    (qpat_x_assum `_ sa = _` mp_tac >>
     simp[emit_op_def, emit_void_def, emit_inst_def, comp_ignore_bind_def,
       comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[] >> qexists_tac `STRING #"%" (toString sa.cs_next_var)` >>
     simp[not_fresh_at_def]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `isPREFIX [mk_inst sa.cs_next_id MLOAD [Var root] [tmp];
       mk_inst (sa.cs_next_id+1) (if tr then TSTORE else SSTORE) [dst;Var tmp] []]
      (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   (!x. dst = Var x ==> x <> tmp)` by metis_tac[] >>
  qexistsl_tac [
    `(if tr then tstore else sstore) k (mload (w2n a) s)
      (update_var tmp (mload (w2n a) s) s) with vs_inst_idx := s.vs_inst_idx+2`,
    `DRESTRICT G (COMPL {tmp})`,
    `if tr then (tn with t_var := tn.t_var |+ (tmp,mem_word_taint tn.t_mem (w2n a)))
       with t_trans := key_update tn.t_trans k (mem_word_taint tn.t_mem (w2n a))
     else (tn with t_var := tn.t_var |+ (tmp,mem_word_taint tn.t_mem (w2n a)))
       with t_stor := key_update tn.t_stor k (mem_word_taint tn.t_mem (w2n a))`] >>
  conj_tac >- (rpt gen_tac >> drule_all dense_single_origin_ptr >> simp[]) >>
  Cases_on `tr` >>
  simp[store_copy_frame_def, store_copy_normalize_def, store_copy_prefix_def,
    COUNT_LIST_def, sstore_def, tstore_def, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, toplevel_copy_source_taint_def,
    op_taint_def, EVAL ``COUNT_LIST 1``] >>
  fs[WORD_ADD_0, WORD_MULT_CLAUSES, venom_state_component_equality]
QED

Theorem dense_single_compiled_origin_ptr:
  (do loaded <- emit_op MLOAD [Var root];
      emit_void (if tr then TSTORE else SSTORE) [dst;loaded]
   od) sa = (z,sb) /\ fn_has_code sa sb func /\
  not_fresh_at sa root /\ (!x. dst = Var x ==> not_fresh_at sa x) /\
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME a /\
  eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  w2n a + 32 <= s.vs_alloca_next /\ ~s.vs_call_ctx.cc_static /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    store_copy_frame sa (if tr then LocTransient else LocStorage) a k s 1 t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
    toplevel_copy_source_taint (if tr then LocTransient else LocStorage) tnf =
      key_update (toplevel_copy_source_taint (if tr then LocTransient else LocStorage) tn)
        k (mem_word_taint tn.t_mem (w2n a)) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all dense_single_compiled_origin_ptr_uniform >>
  metis_tac[]
QED

Theorem dense_loop_compiled_origin_ptr:
  compile_word_copy_loop (Var x) dst n LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\ (loc = LocStorage \/ loc = LocTransient) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_call_ctx.cc_static /\
  not_fresh_at sa x /\ (!y. dst = Var y ==> not_fresh_at sa y) /\
  lookup_var x s = SOME b /\ ptr_covers G tn x s (32*n) /\
  eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
  n < dimword(:256) /\ w2n b + 32*n < dimword(:256) /\
  w2n b + 32*n <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    store_copy_frame sa loc b k s n t /\ ~t.vs_halted /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\

    (!y. not_fresh_at sa y ==> FLOOKUP Gf y = FLOOKUP G y /\
                               op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if loc = LocStorage then tnf.t_trans = tn.t_trans else tnf.t_stor = tn.t_stor) /\
    toplevel_copy_source_taint loc tnf SUBSET
      (toplevel_copy_source_taint loc tn DIFF {(k + n2w i, j) | (i,j) | i < n}) UNION
      {(k + n2w i, j) | (i,j) | i < n /\ j < 32 /\ w2n b + 32*i + j IN tn.t_mem}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all memory_copy_loop_origin_ptr >>
  disch_then (qspecl_then
    [`explicit`, `PG`,
     `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
     strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[] >>
  metis_tac[gas_origin_ptr_path_from_no_dead,
    place_store_copy_frame_observations, topcopy_frame_frontier]
QED

Theorem dense_store_slots_origin_ptr:
  ~is_abi_dynamic cenv.ce_struct_fields ty /\
  compile_store_slots cenv (Var x) dst ty tr sa = (u,sb) /\
  fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_call_ctx.cc_static /\
  not_fresh_at sa x /\ (!y. dst = Var y ==> not_fresh_at sa y) /\
  lookup_var x s = SOME b /\
  ptr_covers G tn x s (32*(type_memory_bytes cenv ty DIV 32)) /\
  eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
  type_memory_bytes cenv ty DIV 32 < dimword(:256) /\
  w2n b + 32*(type_memory_bytes cenv ty DIV 32) < dimword(:256) /\
  w2n b + 32*(type_memory_bytes cenv ty DIV 32) <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    store_copy_frame sa (if tr then LocTransient else LocStorage) b k s
      (type_memory_bytes cenv ty DIV 32) t /\ ~t.vs_halted /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gf y = FLOOKUP G y /\
                               op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
    toplevel_copy_source_taint (if tr then LocTransient else LocStorage) tnf SUBSET
      (toplevel_copy_source_taint (if tr then LocTransient else LocStorage) tn DIFF
        {(k + n2w i, j) | (i,j) | i < type_memory_bytes cenv ty DIV 32}) UNION
      {(k + n2w i, j) | (i,j) | i < type_memory_bytes cenv ty DIV 32 /\ j < 32 /\
        w2n b + 32*i + j IN tn.t_mem}
Proof
  strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def] >>
  Cases_on `type_memory_bytes cenv ty DIV 32 = 1`
  >- (simp[] >> strip_tac >> fs[] >>
      drule_all dense_single_compiled_origin_ptr >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[] >>
      simp[key_update_def, mem_word_taint_def, SUBSET_DEF, IN_UNION,
        IN_DIFF, PULL_EXISTS, WORD_ADD_0] >> rpt strip_tac >> gvs[])
  >> Cases_on `tr` >>
  simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `type_memory_bytes cenv ty DIV 32 < dimword(:256)` by decide_tac
  >~ [`store_copy_frame _ LocTransient _ _ _ _ _`]
  >- (drule_all (SRULE [] (Q.INST [`loc` |-> `LocTransient`]
        dense_loop_compiled_origin_ptr)) >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      qexistsl_tac [`t`,`Gf`,`tnf`] >> gvs[]) >>
  drule_all (SRULE [] (Q.INST [`loc` |-> `LocStorage`]
    dense_loop_compiled_origin_ptr)) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> gvs[]
QED
