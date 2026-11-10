(* Counted execution boundaries for RawLog body continuations. *)
Theory bodySimRawLogTails
Ancestors
  bodySimRawLogBodySource exprSimRawLog exprSimHash gasSummary
  exprBopSimProps exprSimProps exprSimAlloc context ASCIInumbers
  bodySim exprSimSend exprSimHyps vyperTypeSystem vyperAST list
  exprSimAggregateSource vyperInterpreter vyperValue vyperState vyperContext
  exprSimWordArgs exprLowering compileEnv loweringStateRelDefs emitHelper venomExecSemantics
  exprLoweringProps venomState venomMemDefs exprSimDefs exprSimStack loweringPosts
  exprSimHypsDefs exprSimSource vyperEvent fragExec venomInst
Libs
  pairLib

Theorem raw_log_dynamic_tail_counted:
  expr_has_effect e /\
  emit_op MLOAD [data_op] sm = (len_op, s1) /\
  emit_op ADD [data_op; Lit 32w] s1 = (ptr_op, s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [len_op; ptr_op])) [] s2 = (u, sb) /\
  (!x. data_op = Var x ==> not_fresh_at sm x) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) ops /\
  LENGTH ops <= 4 /\
  eval_operand data_op s = SOME (n2w b) /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  mload b s = n2w (LENGTH bs) /\
  TAKE (LENGTH bs) (DROP (b + 32) s.vs_memory ++
    REPLICATE (LENGTH bs) 0w) = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  wb_frame cenv es0 sa s0 s /\ sa.cs_next_var <= sm.cs_next_var /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT /\ fn_has_code sm sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    expr_post ctx func cenv cx e es0 sa sb s0
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w) t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all raw_log_dynamic_prepare_frame >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb) = [] /\
   emitted_insts sm sb = emitted_insts sm s2 ++
     [mk_inst s2.cs_next_id LOG (Lit (n2w (LENGTH ops)) ::
       (REVERSE ops ++ [len_op; ptr_op])) []]` by
    (gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
         fresh_var_def, fresh_id_def, emit_def, comp_return_def,
         emitted_insts_def] >>
     CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
     simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  `?t'. step_inst_base (mk_inst s2.cs_next_id LOG
      (Lit (n2w (LENGTH ops)) :: (REVERSE ops ++ [len_op; ptr_op])) []) t = OK t' /\
    stmt_state_rel ctx func cenv cx
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bs]) t' /\
    wb_frame cenv es0 sa s0 t'` by
    (irule raw_log_core_frame >> simp[mk_inst_def] >>
     qexistsl_tac [`ops`, `len_op`, `ptr_op`,
                  `n2w (b + 32)`, `n2w (LENGTH bs)`] >>
     simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
          wordsTheory.dimword_def]) >>
  `run_inst_seq (emitted_insts sm sb) s = OK t'` by
    (asm_rewrite_tac[] >> drule run_inst_seq_append >>
     disch_then (fn th => rewrite_tac[th]) >>
     simp[run_inst_seq_def]) >>
  drule_all hash_run_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t' with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac >- metis_tac[listTheory.LENGTH] >> simp[] >>
  irule expr_post_none_intro >> simp[stmt_state_rel_inst_idx] >>
  fs[wb_frame_def, locals_kept_def, lookup_var_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem raw_log_fixed_tail_counted:
  expr_has_effect e /\
  emit_void MSTORE [ptr_op; data_op] sm = (u, s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [Lit 32w; ptr_op])) [] s1 = (u', sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand data_op s = SOME w /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\ LENGTH ops <= 4 /\
  LENGTH bs = 32 /\ TAKE 32 (word_to_bytes_be w) = bs /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sa s0 s /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n p,32) /\
  (!aid b sz. aid < sa.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n p) 32 b sz) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
     regions_disjoint (w2n p) 32 b sz) /\ post_value_type cenv e = expr_type e /\ expr_type e = NoneT /\
  fn_has_code sm sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    expr_post ctx func cenv cx e es0 sa sb s0
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w) t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all raw_log_fixed_store_frame >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++
    [mk_inst sm.cs_next_id MSTORE [ptr_op; data_op] [];
     mk_inst s1.cs_next_id LOG (Lit (n2w (LENGTH ops)) ::
       (REVERSE ops ++ [Lit 32w; ptr_op])) []]` by
    gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_return_def,
        fresh_id_def, emit_def] >>
  `emitted_insts sm sb = emitted_insts sm s1 ++
     [mk_inst s1.cs_next_id LOG (Lit (n2w (LENGTH ops)) ::
       (REVERSE ops ++ [Lit 32w; ptr_op])) []] /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb) = []` by
    (gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_return_def,
         fresh_id_def, emit_def, emitted_insts_def] >>
     CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
     simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  `eval_operand ptr_op (mstore (w2n p) w s) = SOME p /\
   eval_operands ops (mstore (w2n p) w s) = SOME (MAP event_value_to_word vals)` by
    (`eval_operands ops (mstore (w2n p) w s) = eval_operands ops s` by
       (rpt (pop_assum kall_tac) >> Induct_on `ops` >>
        simp[eval_operands_def] >>
        Cases_on `h` >> simp[eval_operand_def, mstore_def, lookup_var_def]) >>
     simp[] >> Cases_on `ptr_op` >>
     gvs[eval_operand_def, mstore_def, lookup_var_def]) >>
  `?t. step_inst_base (mk_inst s1.cs_next_id LOG
      (Lit (n2w (LENGTH ops)) :: (REVERSE ops ++ [Lit 32w; ptr_op])) [])
      (mstore (w2n p) w s) = OK t /\
    stmt_state_rel ctx func cenv cx
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bs]) t /\
    wb_frame cenv es0 sa s0 t` by
    (irule raw_log_core_frame >> simp[mk_inst_def] >>
     qexists_tac `32w` >> simp[eval_operand_def, wordsTheory.dimword_def]) >>
  `run_inst_seq (emitted_insts sm sb) s = OK t` by
    (asm_rewrite_tac[] >> drule run_inst_seq_append >>
     disch_then (fn th => rewrite_tac[th]) >> simp[run_inst_seq_def]) >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    (pure_rewrite_tac[emitted_insts_def] >>
     qpat_x_assum `sb.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms, rich_listTheory.DROP_LENGTH_APPEND]) >>
  drule_all hash_run_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac >- metis_tac[listTheory.LENGTH] >> simp[] >>
  irule expr_post_none_intro >> simp[stmt_state_rel_inst_idx] >>
  qpat_x_assum `wb_frame cenv es0 sa s0 t` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[wb_frame_def, locals_kept_def, lookup_var_def] >>
  metis_tac[]
QED

(* The post-data source suffix consumes no gas observations. *)
Theorem raw_log_tail_summary:
  dest_BytesV dv = SOME bs /\ LENGTH vals <= 4 /\
  gas_marked_path F ctx func s 0 (OK t) /\
  Q (INL NoneV)
    ((es with logs := es.logs ++
       [encode_raw_event_values cx.txn.target vals bs]) with gas_obs := []) t ==>
  gas_summary_at F (ctx,func) []
    (do bs' <- lift_option_type (dest_BytesV dv) "raw_log data";
        type_check (LENGTH vals <= 4) "raw_log too many topics";
        push_log (encode_raw_event_values cx.txn.target vals bs');
        return NoneV od) (es,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INL NoneV`,
    `es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]`,
    `OK t`] >>
  simp[bind_def, ignore_bind_def, lift_option_type_def, type_check_def,
       push_log_def, return_def, assert_def,
       vyperStateTheory.evaluation_state_component_equality] >>
  disj1_tac >> Cases_on `es` >> gvs[]
QED

Theorem raw_log_data_post_transport:
  wb_args_post ctx func cenv cx es0 sa s0 es1 ops vals t /\
  expr_post ctx func cenv cx data es1 sm sn t es2 v data_op u /\
  stmt_state_rel ctx func cenv cx es0 s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sm x) /\
               (!l. op <> Label l)) ops ==>
  wb_frame cenv es0 sa s0 u /\
  LIST_REL (\op v. eval_operand op u = SOME (val_to_w256 v)) ops vals
Proof
  strip_tac >>
  `wb_frame cenv es1 sm t u` by metis_tac[expr_post_frame] >>
  gvs[wb_args_post_def] >> conj_tac
  >- (irule wb_frame_trans >> simp[] >> conj_tac
      >- (qexistsl_tac [`es1`, `sm`, `t`] >> simp[]) >>
      qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `LIST_REL _ ops vals` mp_tac >>
  qpat_x_assum `EVERY _ ops` mp_tac >>
  qid_spec_tac `vals` >> Induct_on `ops` >> simp[] >>
  gen_tac >> Cases_on `vals` >> simp[] >> rpt strip_tac
  >- (irule exprBopSimPropsTheory.eval_operand_frame >> simp[] >>
      qexistsl_tac [`sm`, `t`] >> simp[] >> metis_tac[wb_frame_vars]) >>
  first_x_assum irule >> simp[]
QED

Theorem raw_log_fixed_buffer_after_data:
  expr_post ctx func cenv cx data es sm sn t es' v data_op s /\
  stmt_state_rel ctx func cenv cx es t /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  not_fresh_at sm pvar /\ lookup_var pvar t = SOME p /\
  FLOOKUP t.vs_allocas aid = SOME (w2n p,32) /\ sa.cs_next_id <= aid /\
  (!n b sz. local_region cenv es.scopes t n b sz ==>
     regions_disjoint (w2n p) 32 b sz) ==>
  eval_operand (Var pvar) s = SOME p /\
  FLOOKUP s.vs_allocas aid = SOME (w2n p,32) /\
  (!old b sz. old < sa.cs_next_id /\
     FLOOKUP s.vs_allocas old = SOME (b,sz) ==>
     regions_disjoint (w2n p) 32 b sz) /\
  (!n b sz. local_region cenv es'.scopes s n b sz ==>
     regions_disjoint (w2n p) 32 b sz)
Proof
  strip_tac >>
  `wb_frame cenv es sm t s` by metis_tac[expr_post_frame] >>
  `lookup_var pvar s = SOME p /\
   FLOOKUP s.vs_allocas aid = SOME (w2n p,32)` by
    (fs[wb_frame_def] >> metis_tac[]) >>
  simp[eval_operand_def] >> conj_tac
  >- (rpt strip_tac >>
      `allocas_non_overlapping s` by
        fs[expr_post_def, stmt_state_rel_def, alloca_inv_def] >>
      `aid <> old` by decide_tac >>
      fs[allocas_non_overlapping_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
      metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `!n b sz. local_region _ es.scopes t _ _ _ ==> _` irule >>
  qexists_tac `n` >> irule exprSimPropsTheory.local_region_frame >>
  simp[] >> conj_tac
  >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
  qexistsl_tac [`sm`, `es'.scopes`, `s`] >> simp[] >>
  metis_tac[wb_frame_vars]
QED

Theorem raw_log_alloc_counted:
  compile_alloc_buffer sz sm = (buf,sn) /\ fn_has_code sm sn func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ sz < dimword (:256) /\
  wb_frame cenv es0 sa s0 s /\ sa.cs_next_var <= sm.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t w. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es0 sa s0 t /\
    eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ t.vs_memory = s.vs_memory /\
    sm.cs_next_id < sn.cs_next_id /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sm.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv es.scopes t name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sn p) /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `wb_frame cenv es0 sa s0 t` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sm`, `s`] >> simp[]) >>
  `sn.cs_current_bb = sm.cs_current_bb /\
   sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sn) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sn) = []` by
    (gvs[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
         comp_bind_def, comp_return_def, comp_ignore_bind_def,
         fresh_id_def, fresh_var_def, emit_def,
         emitted_insts_def] >>
     simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  drule_all hash_run_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sn.cs_current_insts`, `w`] >>
  conj_tac >- metis_tac[listTheory.LENGTH] >>
  simp[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def,
       local_region_def] >>
  conj_tac
  >- (qpat_x_assum `wb_frame cenv es0 sa s0 t` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[wb_frame_def, locals_kept_def, lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `sn.cs_current_insts = _` kall_tac >>
  fs[lookup_var_def, local_region_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem raw_log_post_gas_obs:
  expr_post ctx func cenv cx e es0 sa sb s0 ee v op t ==>
  expr_post ctx func cenv cx e es0 sa sb s0 (ee with gas_obs := gs) v op t
Proof
  simp[expr_post_def, expr_val_at_def, expr_val_own_def] >> strip_tac >> simp[] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := gs) t` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`t.vs_gas_readings`, `t.vs_inst_idx`, `gs`] mp_tac) >>
     simp[]) >> simp[]
QED

Theorem raw_log_alloc_return_summary:
  gas_marked_path F ctx func s 0 (OK t) /\
  Q (INL ()) (es with gas_obs := []) t ==>
  gas_summary_at F (ctx,func) [] (return ()) (es,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INL ()`, `es`, `OK t`] >> simp[return_def]
QED
