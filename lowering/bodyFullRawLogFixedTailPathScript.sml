(* Concrete pointer checks for RawLog's fixed-data continuation. *)
Theory bodyFullRawLogFixedTailPath
Ancestors
  bodyFullRawLogFixedBoundary rawLogPtrInst bodyPtrDefs ptrDiscipline
  ptrSafeRun venomState venomInst venomExecSemantics words list
  rawLogCoreFrame fragGasSeqPtr wordLoadStorePtr exprPtrUnwrapCopyEdges
  bodyFullUnwrapSlotPost bodyFullGhostFrame
  instMemFrontier emitHelper compileEnv fragExecMem fragExec
  loweringPosts byte valueEncoding vyperEvent
  venomMemDefs valueEncodingProps rich_list finite_map arithmetic venomStepProps venomInstProofs

Theorem raw_log_fixed_log_inst_ok:
  LENGTH topics < dimword (:256) /\
  eval_operand pop s = SOME off /\
  eval_operands topics s = SOME vals /\
  (?p b sz. pop = Var p /\ FLOOKUP G p = SOME (b,sz) /\
    b <= w2n off /\ w2n off + 32 <= b + sz) /\
  EVERY (\op. op_taint tn op = {}) topics /\
  op_taint tn pop = {} /\
  (!i. w2n off <= i /\ i < w2n off + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  stor_taint_ok_at D tn s /\
  step_inst_base
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s = OK t ==>
  ptr_inst_ok D lo fuel ctx fn G tn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s
Proof
  strip_tac >>
  `access_ok 0 G fn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s` by
    (irule log_access_ok >> simp[eval_operand_def, dimword_def] >> metis_tac[]) >>
  `access_ok lo G fn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s` by
    (gvs[access_ok_def] >> rpt strip_tac >> metis_tac[arithmeticTheory.ADD_EQ_0]) >>
  `taint_ok fn tn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s` by
    (irule log_taint_ok >> simp[eval_operand_def, op_taint_def, dimword_def] >> metis_tac[]) >>
  gvs[ptr_inst_ok_def, stor_taint_ok_at_def, mk_inst_def, step_inst_non_invoke]
QED

Theorem raw_log_fixed_store_step:
  emit_void MSTORE [Var p;data_op] sm = ((),s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var p]) [] s1 = ((),sb) /\
  eval_operand (Var p) s = SOME w /\ eval_operand data_op s = SOME word /\
  ptr_covers G tn p s 32 /\ op_taint tn data_op = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst id MSTORE [Var p;data_op] [];
      t = mstore (w2n w) word s;
      tf = step_taint i s t tn
  in
    step_inst_base i s = OK t /\ ptr_inst_ok D lo 0 ctx func G tn i s /\
    step_prov PG G i t = G /\
    tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = tn.t_mem DIFF {j | w2n w <= j /\ j < w2n w + 32} /\
    ptr_covers G tf p t 32 /\
    EVERY (\op. op_taint tf op = {}) ops = EVERY (\op. op_taint tn op = {}) ops /\
    (!j. w2n w <= j /\ j < w2n w+32 ==> j NOTIN tf.t_mem) /\
    allocas_from lo t /\ stor_taint_ok_at D tn s = stor_taint_ok_at D tf t
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  `lookup_var p s = SOME w` by gvs[eval_operand_def] >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`,`G`,`id`] strip_assume_tac) >>
  simp[] >> conj_tac
  >- simp[mk_inst_def, step_inst_base_opcode_eqs, exec_write2_def, eval_operand_def] >>
  conj_tac >- (irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  ` (step_taint (mk_inst id MSTORE [Var p;data_op] []) s
      (mstore (w2n w) word s) tn).t_imm = tn.t_imm` by
    simp[step_taint_def, mk_inst_def, imm_taint_def] >>
  gvs[ptr_covers_def, mstore_def, lookup_var_def, allocas_from_def,
       stor_taint_ok_at_def, op_taint_def] >> metis_tac[]
QED

Theorem raw_log_fixed_sequence_path:
  emit_void MSTORE [pop;data_op] sm = ((),s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;pop]) [] s1 = ((),sb) /\
  fn_has_code sm sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (let i = mk_inst sm.cs_next_id MSTORE [pop;data_op] [];
       j = mk_inst s1.cs_next_id LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;pop]) []
   in step_inst_base i s = OK t /\
      step_inst_base j (t with vs_inst_idx := SUC s.vs_inst_idx) = OK v /\
      inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
      ptr_inst_ok D lo 0 ctx func G tn i s /\
      inst_mem_below_frontier j (t with vs_inst_idx := SUC s.vs_inst_idx) /\
      inst_dload_in_section j (t with vs_inst_idx := SUC s.vs_inst_idx) /\
      ptr_inst_ok D lo 0 ctx func
        (step_prov PG G i t) (step_taint i s t tn) j (t with vs_inst_idx := SUC s.vs_inst_idx) /\
      step_prov PG (step_prov PG G i t) j v = G1 /\
      step_taint j (t with vs_inst_idx := SUC s.vs_inst_idx) v (step_taint i s t tn) = tn1) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (v with vs_inst_idx := LENGTH sb.cs_current_insts),G1,tn1) /\
  (v with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb = sb.cs_current_bb
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_inst_base i s = OK t` >>
  qmatch_asmsub_abbrev_tac `step_inst_base j _ = OK v` >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ [i;j]` by
    (gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, emit_def, Abbr `i`, Abbr `j`]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `get_instruction bb s.vs_inst_idx = SOME i /\
   get_instruction bb (SUC s.vs_inst_idx) = SOME j` by
    (gvs[IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN] >> simp[]) >>
  `step_inst 0 ctx i s = OK t` by
    simp[step_inst_non_invoke, Abbr `i`, mk_inst_def] >>
  `~is_terminator i.inst_opcode` by simp[Abbr `i`, mk_inst_def, is_terminator_def] >>
  drule_all step_preserves_control_flow >> strip_tac >>
  `~t.vs_halted` by metis_tac[step_preserves_halted] >>
  `step_inst 0 ctx j (t with vs_inst_idx := SUC s.vs_inst_idx) = OK v` by
    simp[step_inst_non_invoke, Abbr `j`, mk_inst_def] >>
  `~is_terminator j.inst_opcode` by simp[Abbr `j`, mk_inst_def, is_terminator_def] >>
  `v.vs_current_bb = s.vs_current_bb` by
    (drule_at (Pat `step_inst _ _ j _ = _`) step_preserves_control_flow >> simp[]) >>
  `i.inst_opcode <> INVOKE /\ j.inst_opcode <> INVOKE` by
    simp[Abbr `i`, Abbr `j`, mk_inst_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx),step_prov PG G i t,step_taint i s t tn)` by
    (drule_all straight_line_origin_ptr_edge >>
     simp[Abbr `i`, mk_inst_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
     (t with vs_inst_idx := SUC s.vs_inst_idx,step_prov PG G i t,step_taint i s t tn) []
     (OK (v with vs_inst_idx := SUC (SUC s.vs_inst_idx)),G1,tn1)` by
    (`j.inst_opcode <> GAS` by simp[Abbr `j`, mk_inst_def] >>
     gvs[] >> drule_at (Pat `step_inst_base j _ = _`) straight_line_origin_ptr_edge >>
     simp[] >> disch_then drule_all >> simp[]) >>
  `~v.vs_halted` by
    (drule_at (Pat `step_inst _ _ j _ = _`) step_preserves_halted >> simp[]) >>
  `LENGTH sb.cs_current_insts = SUC (SUC s.vs_inst_idx)` by simp[] >>
  simp[] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
    (SPEC_ALL (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules)))) >>
  goal_assum (drule_at Any) >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
    (SPEC_ALL (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules)))) >>
  goal_assum (drule_at Any) >>
  simp[] >> irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]
QED

Theorem raw_log_fixed_tail_path:
  !buf data_op sm s1 ops sb alloc_sa data_sa func cenv ctx sa data ann es_call dflt
      cx st0 ee DF lo explicit PG es s0 bs s G tn G0 tn0 d word p w vals.
    emit_void MSTORE [buf.buf_operand;data_op] sm = ((),s1) /\
    emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
    compile_alloc_buffer 32 alloc_sa = (buf,data_sa) /\ fn_has_code alloc_sa data_sa func /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\
    LENGTH ops < dimword (:256) /\ sa.cs_next_id <= alloc_sa.cs_next_id /\
    sa.cs_next_var <= sm.cs_next_var /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) (buf.buf_operand::data_op::ops) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    expr_type data = BaseT (BytesT (Fixed 32)) /\ post_value_type cenv data = expr_type data /\
    expr_type (Call ann RawLog es_call dflt) = NoneT /\
    post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
    expr_has_effect (Call ann RawLog es_call dflt) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
      expr_store_bound cx (expr_type data) (BytesV bs) data_op s /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
      ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G tn s /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ alloca_history func s /\
      s0.vs_alloca_next <= s.vs_alloca_next /\ LENGTH bs = 32 /\
      eval_operand data_op s = SOME word /\ TAKE 32 (word_to_bytes_be word) = bs /\
      buf.buf_operand = Var p /\ eval_operand buf.buf_operand s = SOME w /\ ptr_covers G tn p s 32 /\
      FLOOKUP s.vs_allocas alloc_sa.cs_next_id = SOME (w2n w,32) /\ w2n w + 32 < dimword (:256) /\
      (!name b n. local_region cenv ee.scopes s name b n ==> regions_disjoint (w2n w) 32 b n) /\
      (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
        regions_disjoint (w2n w) 32 b n) /\
      eval_operands ops s = SOME (MAP event_value_to_word vals) /\
      EVERY (\op. op_taint tn op = {}) ops /\ ~s.vs_halted /\
      s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts) ==>
    ?u G2 tn2. !H. valid_horizon cx st0 H ee.storage_trace ==>
      u = ((mstore (w2n w) word s) with
        <|vs_logs := s.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs];
          vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
      (let i = mk_inst sm.cs_next_id MSTORE [buf.buf_operand;data_op] [];
           j = mk_inst s1.cs_next_id LOG
             (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [];
           t = mstore (w2n w) word s;
           t1 = t with vs_inst_idx := SUC s.vs_inst_idx;
           v = t1 with vs_logs := s.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs]
       in G2 = step_prov PG (step_prov PG G i t) j v /\
          tn2 = step_taint j t1 v (step_taint i s t tn)) /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G2,tn2) /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv_at (DF H) lo d cenv cx
        (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) G2 tn2 u /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `i = mk_inst sm.cs_next_id MSTORE [buf.buf_operand;data_op] []` >>
  qabbrev_tac `j = mk_inst s1.cs_next_id LOG
    (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) []` >>
  qabbrev_tac `t = mstore (w2n w) word s` >>
  qabbrev_tac `t1 = t with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = t1 with vs_logs := s.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs]` >>
  qexistsl [`v with vs_inst_idx := LENGTH sb.cs_current_insts`,
    `step_prov PG (step_prov PG G i t) j v`,
    `step_taint j t1 v (step_taint i s t tn)`] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> strip_tac >>
  `op_taint tn data_op = {}` by gvs[ptr_val_ok_def] >>
  `allocas_from lo s /\ stor_taint_ok_at (DF H) tn s` by
    gvs[ghost_inv_at_def] >>
  `step_inst_base i s = OK t /\ ptr_inst_ok (DF H) lo 0 ctx func G tn i s /\
   step_prov PG G i t = G` by
    (gvs[] >> drule_all (SRULE [] raw_log_fixed_store_step) >>
     simp[Abbr `i`, Abbr `t`] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx ee s` by gvs[expr_post_def] >>
  `~s.vs_call_ctx.cc_static /\ s.vs_call_ctx.cc_address = cx.txn.target` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
        loweringStateRelDefsTheory.call_ctx_rel_def] >>
  `mem_bytes_at (w2n w) 32 t.vs_memory = bs` by
    (qpat_x_assum `TAKE 32 _ = bs` mp_tac >>
     `LENGTH (word_to_bytes_be word) = 32` by
       simp[word_to_bytes_be_def, byteTheory.LENGTH_word_to_bytes] >>
     `TAKE 32 (word_to_bytes_be word) = word_to_bytes_be word` by
       metis_tac[listTheory.TAKE_LENGTH_ID] >>
     simp[Abbr `t`, mem_bytes_at_mstore_same, word_to_bytes_be_def]) >>
  `eval_operands ops t1 = SOME (MAP event_value_to_word vals) /\
   eval_operand buf.buf_operand t1 = SOME w` by
    (`!xs. eval_operands xs t1 = eval_operands xs s` by
       (Induct >> simp[eval_operands_def] >>
        `!op. eval_operand op t1 = eval_operand op s` by
          (Cases >> simp[Abbr `t1`, Abbr `t`, mstore_def,
                         eval_operand_def, lookup_var_def]) >> simp[]) >>
     simp[] >> Cases_on `buf.buf_operand` >>
     gvs[Abbr `t1`, Abbr `t`, mstore_def, eval_operand_def, lookup_var_def]) >>
  `step_inst_base j t1 = OK v` by
    (mp_tac (Q.INST [`inst` |-> `j`, `sz` |-> `Lit 32w`, `pop` |-> `buf.buf_operand`,
                    `ops` |-> `ops`, `s` |-> `t1`, `off` |-> `w`,
                    `len` |-> `32w`, `topics` |-> `MAP event_value_to_word vals`] raw_log_core_step) >>
     simp[Abbr `j`, mk_inst_def, eval_operand_def] >>
     impl_tac >- simp[Abbr `t1`, Abbr `t`, mstore_def] >>
     `t1.vs_memory = t.vs_memory /\ t1.vs_logs = s.vs_logs /\
      t1.vs_call_ctx = s.vs_call_ctx` by
       simp[Abbr `t1`, Abbr `t`, mstore_def] >>
     gvs[Abbr `v`, valueEncodingDefsTheory.mem_bytes_at_def,
          encode_raw_event_values_def, encode_raw_event_def]) >>
  `alloca_next_valid s` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, alloca_inv_def] >>
  `w2n w + 32 <= s.vs_alloca_next` by
    (irule alloca_region_below_frontier >> simp[] >>
     qexistsl [`alloc_sa.cs_next_id`, `w2n w`, `32`] >> simp[]) >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
   inst_mem_below_frontier j t1 /\ inst_dload_in_section j t1` by
    (simp[Abbr `i`, Abbr `j`, below_frontier_MSTORE,
          memSafeRunTheory.inst_dload_in_section_other] >>
     simp[SRULE [] (Q.SPECL [`s1.cs_next_id`, `LENGTH ops`, `REVERSE ops`]
                    below_frontier_LOG), eval_operand_def] >>
     simp[Abbr `t1`, Abbr `t`, mstore_def, eval_operand_def, lookup_var_def] >>
     gvs[eval_operand_def, lookup_var_def]) >>
  qabbrev_tac `tf = step_taint i s t tn` >>
  `ptr_covers G tf p t 32 /\
   EVERY (\op. op_taint tf op = {}) ops /\
   (!k. w2n w <= k /\ k < w2n w + 32 ==> k NOTIN tf.t_mem) /\
   allocas_from lo t /\ stor_taint_ok_at (DF H) tf t` by
    (gvs[] >> drule_all (SRULE [] raw_log_fixed_store_step) >>
     simp[Abbr `i`, Abbr `t`, Abbr `tf`] >> metis_tac[]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tf j t1` by
    (simp[Abbr `j`] >> irule (SRULE [] raw_log_fixed_log_inst_ok) >>
     simp[Abbr `t1`, allocas_from_def, stor_taint_ok_at_def] >>
     gvs[ptr_covers_def, eval_operand_def, allocas_from_def,
         stor_taint_ok_at_def] >> metis_tac[]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (v with vs_inst_idx := LENGTH sb.cs_current_insts),
      step_prov PG (step_prov PG G i t) j v, step_taint j t1 v tf) /\
   (v with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb = sb.cs_current_bb` by
    (simp[] >> irule (SRULE [] raw_log_fixed_sequence_path) >>
     gvs[Abbr `i`, Abbr `j`, Abbr `t1`, Abbr `tf`] >>
     goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_inst _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `step_inst_base _ _ = _`)) >> simp[]) >>
  `step_prov PG G j v = G /\ step_taint j t1 v tf = tf` by
    simp[Abbr `j`, Abbr `v`, log_ghost] >>
  `tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\
   tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
   tf.t_mem = tn.t_mem DIFF {k | w2n w <= k /\ k < w2n w + 32}` by
    (gvs[] >> drule_all (SRULE [] raw_log_fixed_store_step) >>
     simp[Abbr `i`, Abbr `t`, Abbr `tf`] >> metis_tac[]) >>
  `lo <= w2n w` by (fs[allocas_from_def] >> metis_tac[]) >>
  `local_ptrs_rel func cenv ee.scopes s` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def,
        loweringStateRelDefsTheory.state_rel_def] >>
  `ghost_inv_at (DF H) lo d cenv cx ee G tf t` by
    (irule unwrap_slot_copy_ghost_inv_at >>
     (conj_tac >- (simp[Abbr `t`, mstore_def] >> decide_tac)) >>
     simp[] >>
     goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
     qexistsl [`func`, `32`, `sm`, `w2n w`] >>
     simp[Abbr `t`, lookup_var_def, op_taint_def,
          mstore_mem_bytes_at_disjoint] >>
     conj_tac
     >- (rpt strip_tac >> first_x_assum drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
     rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G tf` by
    (irule unwrap_slot_copy_ghost_kept_at >>
     goal_assum (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
     simp[op_taint_def]) >>
  gvs[] >>
  simp[Abbr `v`, Abbr `t1`] >>
  irule ghost_inv_at_exterior_frame >>
  simp[] >>
  goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
  qexists `sm` >> simp[lookup_var_def]
QED
