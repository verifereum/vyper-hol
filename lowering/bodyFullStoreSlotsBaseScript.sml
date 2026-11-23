Theory bodyFullStoreSlotsBase
Ancestors arithmetic[qualified,ignore_grammar]
  bodyFullStoreSlotsOperandLoop bodyFullStoreSlotsTaintStore
  bodyFullStoreSlotsTaintFold bodyFullStoreSlotsOffset fullStoreDense
  bodyFullStoreSlotsFrame
  bodyFullStoreSlotsAddresses fragGasOriginPtrDead augAssignPtrScalarProbe
  typedCopyOriginPtrDynArray bodyPtrSignedConvertScalarOps bytestringCopyExecution
  fragGasSeqPtr fragGasOriginPtr fragExecMem venomExecSemantics
  venomState venomInst ptrDiscipline memSafeRun
  instMemFrontier fragExec fragGasCopyLoop fragGasCopySeqLiftProps fragGasSeq exprLoweringProps
Libs
  stepInstBaseLib

val _ = diminish_srw_ss ["sizes"];

Theorem store_cnt_shr_joint[local]:
  isPREFIX [mk_inst id SHR [Lit 5w;sum] [out]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  eval_operand sum s = SOME w /\ op_taint tn sum = {} /\
  op_prov G sum = NONE /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  allocas_from lo s /\ ~s.vs_halted ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var out (w >>> 5) s with vs_inst_idx := s.vs_inst_idx + 1),
      step_prov PG G (mk_inst id SHR [Lit 5w;sum] [out])
        (update_var out (w >>> 5) s),
      step_taint (mk_inst id SHR [Lit 5w;sum] [out]) s
        (update_var out (w >>> 5) s) tn)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id SHR [Lit 5w;sum] [out]) s =
    OK (update_var out (w >>> 5) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def,
      wordsTheory.dimword_def] >>
  `ptr_inst_ok D 0 0 ctx func G tn
    (mk_inst id SHR [Lit 5w;sum] [out]) s` by
    (simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
       mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       allocas_from_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
     rpt strip_tac >> gvs[op_prov_def, op_taint_def, finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]) >>
  `run_inst_seq_mem_ok [mk_inst id SHR [Lit 5w;sum] [out]] s` by
    (simp[run_inst_seq_mem_ok_last, inst_dload_in_section_def, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  `inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst id SHR [Lit 5w;sum] [out]] s
    (step_prov PG G (mk_inst id SHR [Lit 5w;sum] [out]) (update_var out (w >>> 5) s))
    (step_taint (mk_inst id SHR [Lit 5w;sum] [out]) s (update_var out (w >>> 5) s) tn)` by
    simp[inst_seq_ptr_def] >>
  `run_inst_seq [mk_inst id SHR [Lit 5w;sum] [out]] s =
    OK (update_var out (w >>> 5) s)` by simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
    [mk_inst id SHR [Lit 5w;sum] [out]]` by simp[mk_inst_def, is_terminator_def] >>
  `(ctx_has_dalloca ctx ==> !pre i post u.
    [mk_inst id SHR [Lit 5w;sum] [out]] = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     Cases_on `pre` >> gvs[mk_inst_def]) >>
  drule_all_then (qspec_then `explicit` mp_tac) run_inst_seq_origin_ptr_lift >>
  simp[run_inst_seq_def, mk_inst_def, is_terminator_def]
QED

Theorem store_cnt_shr_uniform[local]:
  emit_op SHR [Lit 5w;sum] a = (op,b) /\ fn_has_code a b func /\
  eval_operand sum s = SOME w /\ op_taint tn sum = {} /\
  op_prov G sum = NONE /\ allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?out t Gf tf.
    op = Var out /\ not_fresh_at b out /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand op t = SOME (w >>> 5) /\ op_prov Gf op = NONE /\
    op_taint tf op = {} /\ allocas_from lo t /\ ~t.vs_halted /\
    t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    store_copy_normalize s t = s /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. not_fresh_at a p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `?out. op = Var out /\ ~not_fresh_at a out /\ not_fresh_at b out /\
    b.cs_current_bb = a.cs_current_bb /\
    b.cs_current_insts = a.cs_current_insts ++
      [mk_inst a.cs_next_id SHR [Lit 5w;sum] [out]]` by
    gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
      compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
      compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
      compileEnvTheory.emit_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX [mk_inst a.cs_next_id SHR [Lit 5w;sum] [out]]
      (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def,
       rich_listTheory.IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
       exprLoweringPropsTheory.DROP_PREFIX] >> simp[]) >>
  qabbrev_tac `u = update_var out (w >>> 5) s` >>
  qabbrev_tac `i = mk_inst a.cs_next_id SHR [Lit 5w;sum] [out]` >>
  qexistsl [`out`,`u with vs_inst_idx := s.vs_inst_idx + 1`,
    `step_prov PG G i u`,`step_taint i s u tn`] >>
  simp[Abbr `i`, Abbr `u`] >>
  conj_tac >- (gen_tac >> drule_all store_cnt_shr_joint >> simp[]) >>
  `step_inst_base (mk_inst a.cs_next_id SHR [Lit 5w;sum] [out]) s =
    OK (update_var out (w >>> 5) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def,
      wordsTheory.dimword_def] >>
  `step_taint (mk_inst a.cs_next_id SHR [Lit 5w;sum] [out]) s
     (update_var out (w >>> 5) s) tn = (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule convert_scalar_ghost_update >> simp[op_taint_def] >>
     goal_assum (drule_at Any)) >>
  `allocas_from lo (update_var out (w >>> 5) s with
    vs_inst_idx := LENGTH a.cs_current_insts + 1)` by
    (gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  simp[stmtSimStoreCopyTheory.store_copy_normalize_def,
    venomStateTheory.venom_state_component_equality,
    convert_scalar_output_prov, listTheory.MEM, op_taint_def,
    eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[convert_scalar_ghost_frame, lookup_var_def, update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem store_cnt_round_uniform[local]:
  emit_op ADD [loaded;Lit 63w] a = (sum,b) /\
  emit_op SHR [Lit 5w;sum] b = (cnt,c) /\ fn_has_code a c func /\
  eval_operand loaded s = SOME w /\ op_taint tn loaded = {} /\
  op_prov G loaded = NONE /\ allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?out t Gf tf.
    cnt = Var out /\ not_fresh_at c out /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand cnt t = SOME ((w+63w) >>> 5) /\ op_prov Gf cnt = NONE /\
    op_taint tf cnt = {} /\ allocas_from lo t /\ ~t.vs_halted /\
    t.vs_current_bb = c.cs_current_bb /\
    t.vs_inst_idx = LENGTH c.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    store_copy_normalize s t = s /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. not_fresh_at a p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `cs_extends a b /\ cs_extends b c` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono,
      exprLoweringPropsTheory.ci_mono_def] >>
  `fn_has_code a b func /\ fn_has_code b c func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `eval_operand (Lit 63w) s = SOME 63w /\ op_taint tn (Lit 63w) = {}` by
    simp[eval_operand_def,op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`]
    store_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choose_then `tmp` strip_assume_tac)) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK s1,G1,tn1)` >>
  `op_prov G1 sum = NONE` by
    (simp[Abbr `G1`] >> irule (cj 1 add_sub_clean_metadata) >> simp[op_prov_def]) >>
  `eval_operand sum s1 = SOME (w+63w) /\ ~s1.vs_halted /\
    s1.vs_current_bb = b.cs_current_bb /\
    s1.vs_inst_idx = LENGTH b.cs_current_insts` by
    simp[Abbr `s1`, update_var_def] >>
  `allocas_from lo s1` by
    simp[Abbr `s1`,update_var_def,ptrDisciplineTheory.allocas_from_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s1)` by
    (simp[Abbr `s1`,allocas_below_fmp_def,update_var_def] >>
     metis_tac[allocas_below_fmp_def]) >>
  drule_all store_cnt_shr_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`G1`,`s1`,`tn1`] >> simp[]) >>
  qexistsl [`out`,`t`,`Gf`,`tf`] >>
  gvs[Abbr `s1`, update_var_def] >>
  `!p. not_fresh_at a p ==> not_fresh_at b p` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `a` >>
     qpat_x_assum `emit_op ADD _ _ = _` (mp_tac o
       MATCH_MP typedMemoryCopyTheory.typed_copy_emit_op_mono) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  conj_tac >-
    (qpat_x_assum `store_copy_normalize _ t = _` mp_tac >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def,
       venomStateTheory.venom_state_component_equality]) >>
  metis_tac[]
QED

Theorem store_cnt_producer_uniform[local]:
  emit_op MLOAD [Var xs] a = (Var lv,b) /\
  emit_op ADD [Var lv;Lit 63w] b = (sum,c) /\
  emit_op SHR [Lit 5w;sum] c = (cnt,d) /\ fn_has_code a d func /\
  not_fresh_at a xs /\ lookup_var xs s = SOME sw /\
  ptr_covers G tn xs s 32 /\
  w2n sw + 32 < dimword (:256) /\ w2n sw + 32 <= s.vs_alloca_next /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n sw) mem = n2w N) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?out t Gf tf.
    cnt = Var out /\ not_fresh_at d out /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand cnt t = SOME ((n2w N+63w) >>> 5) /\ op_prov Gf cnt = NONE /\
    op_taint tf cnt = {} /\ allocas_from lo t /\ ~t.vs_halted /\
    t.vs_current_bb = d.cs_current_bb /\
    t.vs_inst_idx = LENGTH d.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    store_copy_normalize s t = s /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. not_fresh_at a p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `cs_extends a b /\ cs_extends b c /\ cs_extends c d` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono,
      exprLoweringPropsTheory.ci_mono_def] >>
  `fn_has_code a b func /\ fn_has_code b d func` by
    metis_tac[fragExecTheory.fn_has_code_split,
      compileEnvTheory.cs_extends_trans] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by simp[] >>
  drule_all typed_copy_origin_ptr_dyn_read_path >>
  disch_then (qspecl_then [`0`,`0`,`explicit`,`PG`] strip_assume_tac) >>
  rename1 `gas_origin_ptr_path _ _ [] (OK u,Gu,tu)` >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_labels = s.vs_labels /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_call_ctx = s.vs_call_ctx /\ store_copy_normalize s u = s /\
   allocas_from lo u` by
    (gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
       venomStateTheory.venom_state_component_equality,
       stmtSimStoreCopyTheory.store_copy_normalize_def, allocas_from_def] >>
     metis_tac[]) >>
  `op_prov Gu (Var lv) = NONE` by simp[op_prov_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    metis_tac[typedCopyOriginPtrBaseTheory.typed_copy_state_frame_allocas_below_fmp] >>
  drule_all store_cnt_round_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl [`out`,`t`,`Gf`,`tf`] >> simp[] >>
  conj_tac >-
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`Gu`,`u`,`tu`] >> simp[] >>
     irule gas_origin_ptr_path_from_no_dead >> goal_assum (drule_at Any)) >>
  conj_tac >-
    metis_tac[placeStoreSlotsTheory.store_slots_normalize_compose] >>
  rpt strip_tac >>
  `not_fresh_at b p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `a` >>
     qpat_x_assum `emit_op MLOAD _ _ = _` (mp_tac o
       MATCH_MP typedMemoryCopyTheory.typed_copy_emit_op_mono) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  metis_tac[]
QED

Theorem store_cnt_compile_uniform[local]:
  compile_bytestring_word_count (Var xs) a = (cnt,d) /\ fn_has_code a d func /\
  not_fresh_at a xs /\ lookup_var xs s = SOME sw /\
  ptr_covers G tn xs s 32 /\ N + 63 < dimword (:256) /\
  w2n sw + 32 < dimword (:256) /\ w2n sw + 32 <= s.vs_alloca_next /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n sw) mem = n2w N) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?out t Gf tf.
    cnt = Var out /\ not_fresh_at d out /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand cnt t = SOME (n2w (1+word_size N)) /\ op_prov Gf cnt = NONE /\
    op_taint tf cnt = {} /\ allocas_from lo t /\ ~t.vs_halted /\
    t.vs_current_bb = d.cs_current_bb /\
    t.vs_inst_idx = LENGTH d.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    store_copy_normalize s t = s /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. not_fresh_at a p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qpat_x_assum `compile_bytestring_word_count _ _ = _` mp_tac >>
  simp[contextTheory.compile_bytestring_word_count_def,
    compileEnvTheory.comp_bind_def] >>
  Cases_on `emit_op MLOAD [Var xs] a` >>
  rename1 `emit_op MLOAD [Var xs] a = (loaded,b)` >>
  Cases_on `emit_op ADD [loaded;Lit 63w] b` >> simp[] >> strip_tac >>
  `?lv. loaded = Var lv` by
    metis_tac[exprLoweringPropsTheory.emitted_insts_emit_op_local] >>
  gvs[] >> drule_all store_cnt_producer_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl [`out`,`t`,`Gf`,`tf`] >> simp[bytestring_word_count_exact]
QED

Theorem store_slots_prefix_linear[local]:
  w2n sw + 32*n < dimword (:256) ==>
  store_copy_prefix (if tr then LocTransient else LocStorage) sw dw s n =
    FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
      (mload (w2n sw+32*j) s) q) s (COUNT_LIST n)
Proof
  strip_tac >> simp[stmtSimStoreCopyTheory.store_copy_prefix_def] >>
  irule listTheory.FOLDL_CONG >> simp[rich_listTheory.MEM_COUNT_LIST] >>
  rpt strip_tac >>
  `32*x + w2n sw < dimword (:256)` by decide_tac >>
  `sw + n2w x * 32w = n2w (32*x + w2n sw)` by
    (pure_rewrite_tac[GSYM wordsTheory.word_add_n2w,
      GSYM wordsTheory.word_mul_n2w, wordsTheory.n2w_w2n] >>
     wordsLib.WORD_DECIDE_TAC) >>
  Cases_on `tr` >> simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> gvs[]
QED

Theorem store_slots_operand_loop[local]:
  compile_word_copy_loop_op src dst cnt LocMemory
    (if tr then LocTransient else LocStorage) F sa = (result,sb) /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  ~s.vs_call_ctx.cc_static /\
  (!y. dst = Var y ==> not_fresh_at sa y) /\
  (n <> 0 ==> ?x. src = Var x /\ not_fresh_at sa x /\
     lookup_var x s = SOME sw /\ ptr_covers G tn x s (32*n)) /\
  eval_operand dst s = SOME dw /\ op_taint tn dst = {} /\
  eval_operand cnt s = SOME (n2w n) /\ op_taint tn cnt = {} /\
  op_prov G cnt = NONE /\ (!y. cnt = Var y ==> not_fresh_at sa y) /\
  n < dimword(:256) /\ w2n sw + 32*n < dimword(:256) /\
  (n <> 0 ==> w2n sw + 32*n <= s.vs_alloca_next) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
        (mload (w2n sw+32*j) s) q) s (COUNT_LIST n) /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    (if tr then tf.t_stor = tn.t_stor else tf.t_trans = tn.t_trans) /\
    (if tr then tf.t_trans else tf.t_stor) SUBSET
      FOLDL (\X j. key_update X (dw+n2w j)
        (mem_word_taint tn.t_mem (w2n sw+32*j)))
        (if tr then tn.t_trans else tn.t_stor) (COUNT_LIST n) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  SUBGOAL_THEN
    ``(if tr then LocTransient else LocStorage) = LocStorage \/
      (if tr then LocTransient else LocStorage) = LocTransient`` assume_tac
  >- (Cases_on `tr` >> simp[]) >>
  Cases_on `n = 0`
  >- (`eval_operand cnt s = SOME 0w` by simp[] >>
      drule_all memory_copy_loop_zero_origin_ptr_uniform >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
       t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
       t.vs_call_ctx = s.vs_call_ctx` by
        (qpat_x_assum `store_copy_normalize s t = s` mp_tac >>
         simp[stmtSimStoreCopyTheory.store_copy_normalize_def,
           venomStateTheory.venom_state_component_equality]) >>
      qexistsl [`t`,`Gf`,`tnf`] >> Cases_on `tr` >>
      simp[rich_listTheory.COUNT_LIST_def]) >>
  qpat_x_assum `n <> 0 ==> ?x. _` mp_tac >>
  simp[] >> strip_tac >> qpat_x_assum `src = Var _` SUBST_ALL_TAC >>
  `w2n sw + 32*n <= s.vs_alloca_next` by simp[] >>
  drule_all memory_copy_loop_operand_origin_ptr_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule placeStoreCopyPathTheory.place_store_frame_fields >> strip_tac >>
  qexistsl [`t`,`Gf`,`tnf`] >> simp[] >>
  `store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
      (mload (w2n sw+32*j) s) q) s (COUNT_LIST n)` by
    metis_tac[stmtSimStoreCopyTheory.store_copy_frame_def,store_slots_prefix_linear] >>
  simp[] >>
  `!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s` by
    metis_tac[stmtSimStoreCopyTheory.store_copy_frame_def] >>
  qspec_then `n` mp_tac store_slots_taint_count_fold >>
  simp[Once arithmeticTheory.ADD_COMM] >>
  disch_then (qspecl_then [`if tr then tn.t_trans else tn.t_stor`,
    `dw`,`w2n sw`,`tn.t_mem`] assume_tac) >>
  Cases_on `tr` >>
  gvs[exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_source_taint_def]
QED


Theorem store_slots_single_loop[local]:
  (do loaded <- emit_op MLOAD [Var x];
      emit_void (if tr then TSTORE else SSTORE) [dst;loaded] od) sa = (z,sb) /\
  fn_has_code sa sb func /\ not_fresh_at sa x /\
  (!y. dst = Var y ==> not_fresh_at sa y) /\
  lookup_var x s = SOME sw /\ ptr_covers G tn x s 32 /\
  eval_operand dst s = SOME dw /\ op_taint tn dst = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  w2n sw + 32 <= s.vs_alloca_next /\ ~s.vs_call_ctx.cc_static /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
        (mload (w2n sw+32*j) s) q) s [0] /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    (if tr then tf.t_stor = tn.t_stor else tf.t_trans = tn.t_trans) /\
    (if tr then tf.t_trans else tf.t_stor) SUBSET
      FOLDL (\X j. key_update X (dw+n2w j)
        (mem_word_taint tn.t_mem (w2n sw+32*j)))
        (if tr then tn.t_trans else tn.t_stor) [0] /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all dense_single_compiled_origin_ptr_uniform >> strip_tac >>
  drule placeStoreCopyPathTheory.place_store_frame_fields >> strip_tac >>
  `!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s` by
    metis_tac[stmtSimStoreCopyTheory.store_copy_frame_def] >>
  `store_copy_normalize s t =
    (if tr then tstore else sstore) dw (mload (w2n sw) s) s` by
    (qpat_x_assum `store_copy_frame _ _ _ _ _ _ _` mp_tac >>
     Cases_on `tr` >>
     simp[stmtSimStoreCopyTheory.store_copy_frame_def,
       stmtSimStoreCopyTheory.store_copy_prefix_def,
       rich_listTheory.COUNT_LIST_def,EVAL ``COUNT_LIST 1``]) >>
  qexistsl [`t`,`Gf`,`tnf`] >>
  Cases_on `tr` >>
  gvs[exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_source_taint_def]
QED

Theorem compile_store_slots_base_origin_ptr_path:
 !cenv tenv ty tv v src dst tr sa sb s sw dw tn G writes func ctx lo explicit PG.
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
              sz = type_memory_size rt) fields) /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  (~is_abi_dynamic cenv.ce_struct_fields ty \/ is_bytestring_type ty) /\
  compile_store_slots cenv src dst ty tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (type_memory_size tv <> 0 ==>
     ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  (type_memory_size tv = 0 \/
   w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t ks Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
         (mload (w2n sw+32*j) s) q) s ks /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
    (if tr then tnf.t_trans else tnf.t_stor) SUBSET
      FOLDL (\X j. key_update X (dw+n2w j)
         (mem_word_taint tn.t_mem (w2n sw+32*j)))
        (if tr then tn.t_trans else tn.t_stor) ks /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_abi_dynamic cenv.ce_struct_fields ty`
  >- suspend "bytes" >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (irule typedMemoryCopyTheory.typed_copy_memory_size >> metis_tac[]) >>
  `~vyper_is_dynamic tenv ty` by
    (drule_all abiTypeBoundPropsTheory.abi_props_vyper_typed >> simp[]) >>
  `!j. MEM j (MAP FST writes) <=> j < type_slot_size tv` by
    (gen_tac >> eq_tac
     >- metis_tac[CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded] >>
     strip_tac >> irule vyperStorageCoverageTheory.encode_value_live_written >>
     metis_tac[]) >>
  `type_memory_bytes cenv ty DIV 32 = type_slot_size tv` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_slots_def] >>
  Cases_on `type_slot_size tv = 1`
  >- suspend "single" >>
  suspend "static_loop"
QED

Resume compile_store_slots_base_origin_ptr_path[static_loop]:
  simp[compileEnvTheory.comp_ignore_bind_def,compileEnvTheory.comp_bind_def,
    compileEnvTheory.comp_return_def] >>
  pairarg_tac >> strip_tac >> gnvs[] >>
  rename1 `_ sa = (result,sb)` >>
  `compile_word_copy_loop_op src dst (Lit (n2w (type_slot_size tv)))
    LocMemory (if tr then LocTransient else LocStorage) F sa = (result,sb)` by
    (Cases_on `tr` >>
     gvs[contextTheory.compile_memory_to_storage_def,
       contextTheory.compile_memory_to_transient_def,
       contextTheory.compile_word_copy_loop_def]) >>
  `type_slot_size tv < dimword (:256) /\
   w2n sw + 32 * type_slot_size tv < dimword (:256) /\
   (type_slot_size tv <> 0 ==>
    w2n sw + 32 * type_slot_size tv <= s.vs_alloca_next)` by
    (fs[valueEncodingPropsTheory.type_memory_size_slots] >> decide_tac) >>
  `type_slot_size tv <> 0 ==>
    ?x. src = Var x /\ not_fresh_at sa x /\ lookup_var x s = SOME sw /\
      ptr_covers G tn x s (32 * type_slot_size tv)` by
    (strip_tac >>
     `type_memory_size tv <> 0` by
       simp[valueEncodingPropsTheory.type_memory_size_slots] >>
     qpat_x_assum `type_memory_size tv <> 0 ==> _` drule >> strip_tac >>
     qexists `x` >> gvs[eval_operand_def,valueEncodingPropsTheory.type_memory_size_slots]) >>
  `(!y. dst = Var y ==> not_fresh_at sa y) /\
   eval_operand (Lit (n2w (type_slot_size tv))) s = SOME (n2w (type_slot_size tv)) /\
   op_taint tn (Lit (n2w (type_slot_size tv))) = {} /\
   op_prov G (Lit (n2w (type_slot_size tv))) = NONE /\
   (!y. Lit (n2w (type_slot_size tv)) = Var y ==> not_fresh_at sa y)` by
    simp[eval_operand_def,op_taint_def,op_prov_def] >>
  drule_all store_slots_operand_loop >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl [`t`,`COUNT_LIST (type_slot_size tv)`,`Gf`,`tf`] >>
  simp[rich_listTheory.MEM_COUNT_LIST] >>
  qpat_x_assum `_ SUBSET FOLDL _ _ _` mp_tac >>
  simp[Once arithmeticTheory.ADD_COMM]
QED

Resume compile_store_slots_base_origin_ptr_path[single]:
  strip_tac >>
  `type_memory_size tv = 32` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  `?x. src = Var x /\ ptr_covers G tn x s 32` by
    (qpat_x_assum `type_memory_size tv <> 0 ==> _` mp_tac >> simp[]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  `lookup_var x s = SOME sw` by gvs[eval_operand_def] >>
  `not_fresh_at sa x /\ (!y. dst = Var y ==> not_fresh_at sa y) /\
   w2n sw + 32 <= s.vs_alloca_next` by metis_tac[] >>
  drule_all store_slots_single_loop >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl [`t`,`[0]`,`Gf`,`tf`] >> simp[] >> gvs[]
QED

Resume compile_store_slots_base_origin_ptr_path[bytes]:
  `is_bytestring_type ty` by metis_tac[] >>
  `?cap. tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)` by
    (Cases_on `ty` >> gvs[compileEnvTheory.is_bytestring_type_def,vyperValueTheory.evaluate_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[compileEnvTheory.is_bytestring_type_def,vyperValueTheory.evaluate_type_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     gvs[compileEnvTheory.is_bytestring_type_def,vyperValueTheory.evaluate_type_def]) >>
  `val_in_memory tv v (w2n sw) s.vs_memory` by
    (qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ _` mp_tac >>
     disch_then (qspec_then `s.vs_memory` mp_tac) >>
     simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  drule_at (Pat `val_in_memory _ _ _ _`) placeStoreSlotsTheory.store_slots_bytes_footprint >>
  disch_then (qspecl_then [`writes`,`cap`] mp_tac) >> simp[] >> strip_tac >>
  suspend "bytes_footprint"
QED

Resume compile_store_slots_base_origin_ptr_path[bytes_footprint]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_slots_def,compileEnvTheory.comp_bind_def,
    compileEnvTheory.comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gnvs[] >>
  rename1 `compile_bytestring_word_count src sa = (cnt,sm)` >>
  fs[compileEnvTheory.comp_bind_def,compileEnvTheory.comp_ignore_bind_def,
     compileEnvTheory.comp_return_def] >>
  pairarg_tac >> gnvs[] >>
  rename1 `compile_bytestring_word_count (Var x) sa = (cnt,sm)` >>
  rename1 `compile_word_copy_loop_op _ _ _ _ _ _ sm = (res,sb)` >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    metis_tac[stmtLoweringMonoTheory.ci_mono_compile_bytestring_word_count,
      exprLoweringPropsTheory.ci_mono_compile_word_copy_loop_op,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
  `lookup_var x s = SOME sw /\ not_fresh_at sa x` by
    gvs[eval_operand_def] >>
  `ptr_covers G tn x s 32 /\ w2n sw + 32 < dimword (:256) /\
   w2n sw + 32 <= s.vs_alloca_next` by
    (fs[bodyPtrDefsTheory.ptr_covers_def] >> rpt conj_tac >> decide_tac) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    mem_word_at (w2n sw) mem = n2w L` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ _` drule >>
     Cases_on `v` >> gvs[valueEncodingDefsTheory.val_in_memory_def,
       vyperTypingTheory.value_has_type_def]) >>
  drule_all store_cnt_compile_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  suspend "bytes_produced")
QED

Resume compile_store_slots_base_origin_ptr_path[bytes_produced]:
  markerLib.RESUME_TAC >> (
  `not_fresh_at sm x /\ (!y. dst = Var y ==> not_fresh_at sm y)` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  `lookup_var x t = SOME sw` by metis_tac[] >>
  `ptr_covers Gf tf x t (32*(1+word_size L))` by
    (fs[bodyPtrDefsTheory.ptr_covers_def] >> gvs[] >> decide_tac) >>
  `eval_operand dst t = SOME dw /\ op_taint tf dst = {}` by
    (Cases_on `dst` >> gvs[eval_operand_def,op_taint_def]) >>
  `1+word_size L < dimword (:256) /\
   w2n sw + 32*(1+word_size L) < dimword (:256) /\
   (1+word_size L <> 0 ==> w2n sw + 32*(1+word_size L) <= t.vs_alloca_next)` by
    (fs[] >> decide_tac) >>
  `1+word_size L <> 0 ==> ?y. Var x = Var y /\ not_fresh_at sm y /\
    lookup_var y t = SOME sw /\ ptr_covers Gf tf y t (32*(1+word_size L))` by
    gvs[] >>
  `(!y. cnt = Var y ==> not_fresh_at sm y) /\ ~t.vs_call_ctx.cc_static` by
    simp[] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    metis_tac[store_slots_normalize_allocas_below_fmp] >>
  drule_all store_slots_operand_loop >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  suspend "bytes_loop")
QED

Resume compile_store_slots_base_origin_ptr_path[bytes_loop]:
  markerLib.RESUME_TAC >> (
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t',Gf',tf')` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`Gf`,`t`,`tf`] >> simp[]) >>
  `store_copy_normalize s t' =
    FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
      (mload (w2n sw+32*j) s) q) s (COUNT_LIST (1+word_size L))` by
    (qpat_x_assum `store_copy_normalize t t' = _`
      (mp_tac o AP_TERM ``store_copy_normalize s``) >>
     simp[placeStoreSlotsTheory.store_slots_normalize_compose,
       placeStoreSlotsTheory.store_slots_normalize_fold, mload_def]) >>
  qexistsl [`t'`,`COUNT_LIST (1+word_size L)`,`Gf'`,`tf'`] >>
  `!j:num. 32*j+w2n sw = w2n sw+32*j` by
    (metisTools.METIS_TAC [arithmeticTheory.ADD_COMM]) >>
  `word_size L+1 = 1+word_size L` by decide_tac >>
  asm_rewrite_tac[rich_listTheory.MEM_COUNT_LIST] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> metis_tac[ci_mono_def]) >>
  rpt conj_tac >> metis_tac[] )
QED

Finalise compile_store_slots_base_origin_ptr_path
