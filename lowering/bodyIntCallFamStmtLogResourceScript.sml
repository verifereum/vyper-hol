(* Resource transport for the instruction-only Log suffix. *)
Theory bodyIntCallFamStmtLogResource
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtLogSuffix
  exprSimHypsDefs vyperTypeInvariants vyperTypeExtCallSoundness
  vyperTypeEvalStoragePreservation vyperTypeStoragePreservation
  exprSimProps exprLoweringProps stmtSimProps bodyMemoryDefs
  compileEnv loweringStateRelDefs loweringPosts intCallFrame venomState list rich_list
  fragGasSeq entrySinkExtraction emitHelperProps loweringSlice fragExec

Theorem log_expr_sim_inv:
  expr_sim_inv ce cx env es ==>
  expr_sim_inv ce cx env (es with logs := es.logs ++ ls)
Proof
  `env_consistent env cx (es with logs := es.logs ++ ls) =
   env_consistent env cx es` by
    simp[env_consistent_def, env_scopes_consistent_def,
         env_immutables_consistent_def] >>
  `oracle_storage_ok cx es ==>
   oracle_storage_ok cx (es with logs := es.logs ++ ls)` by
    (simp[oracle_storage_ok_def, EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> disch_then drule >> strip_tac >>
     drule contract_storage_well_formed_logs >>
     disch_then (qspec_then `K (es.logs ++ ls)` mp_tac) >> simp[]) >>
  simp[expr_sim_inv_def] >>
  metis_tac[state_well_typed_logs_append, contract_storage_well_formed_logs,
            combinTheory.K_THM]
QED

(* A frame indexed by allocation ids also protects every window below lo,
   whether or not those allocation ids were already present at entry. *)
Theorem allocation_frame_below:
  allocas_above lo t /\
  (!a k. (!aid b z. first <= aid /\ aid < last /\
                   FLOOKUP t.vs_allocas aid = SOME (b,z) ==>
                   a + k <= b \/ b + z <= a) ==>
         mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  !a k. a + k <= lo ==>
    mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory
Proof
  simp[allocas_above_def] >> rpt strip_tac >>
  first_x_assum irule >> rpt strip_tac >>
  disj1_tac >> first_x_assum drule >> simp[]
QED

Theorem intcall_joint_res_log_frame:
  intcall_joint_res fp ce env es sa s /\
  intcall_frame_ok fp /\ sa.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx
    (es with logs := es.logs ++ ls) t /\
  allocas_above fp.jc_lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x t = SOME w) /\
  (!a k. fp.jc_prot a k ==>
         mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  intcall_joint_res fp ce env (es with logs := es.logs ++ ls) sb t
Proof
  strip_tac >>
  `expr_sim_inv ce fp.jc_cx env (es with logs := es.logs ++ ls)` by
    (irule log_expr_sim_inv >> fs[intcall_joint_res_def, intcall_expr_res_def]) >>
  `local_ptrs_reserved ce sb` by
    (fs[intcall_joint_res_def, intcall_expr_res_def] >> drule_all local_ptrs_reserved_next_var >> simp[]) >>
  `ret_pc_ok ce sb t` by
    (irule ret_pc_ok_frame >> fs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
  `return_buf_frame fp.jc_rb ce sb t` by
    (irule return_buf_frame_frame >> fs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
  `!n b sz. local_region ce es.scopes t n b sz ==>
            local_region ce es.scopes s n b sz` by
    (rpt strip_tac >> irule local_region_frame >>
     fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  fs[intcall_joint_res_def, intcall_expr_res_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `?x w. op = Var x /\ lookup_var x fp.jc_oorig = SOME w` by
        metis_tac[intcall_frame_ok_def] >>
      gvs[eval_operand_def] >> metis_tac[eval_operand_def])
  >- (rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono])
  >- (rpt strip_tac >> metis_tac[])
  >> `fp.jc_reserved fp.jc_rpc` by fs[intcall_frame_ok_def] >>
  `?x w. fp.jc_rpc = Var x /\ lookup_var x fp.jc_oorig = SOME w` by
    metis_tac[intcall_frame_ok_def] >>
  gvs[eval_operand_def] >> metis_tac[eval_operand_def]
QED

Theorem intcall_log_suffix_resource_run:
  ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all ce args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sm s /\
  sm.cs_next_var <= sb.cs_next_var /\
  fn_has_code sm sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
             (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel ce fp.jc_cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv fp.jc_cx) (SND arg) = SOME tv /\
         value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics /\
  SUM (MAP (type_memory_bytes ce) (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  vyper_to_abi_list (get_tenv fp.jc_cx) (log_non_indexed_types flags (MAP SND xs))
    (log_non_indexed_values flags vs) = SOME avs ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    intcall_joint_res fp ce env
      (es with logs := es.logs ++ [<|logger := w2w fp.jc_cx.txn.target;
        topics := n2w h::topics;
        data := enc (Tuple (vyper_to_abi_types (get_tenv fp.jc_cx)
          (log_non_indexed_types flags (MAP SND xs)))) (ListV avs)|>]) sb t /\
    inst_extends sm sb /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sm /\ allocas_above fp.jc_lo s` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  drule_all intcall_log_suffix_run >> strip_tac >>
  `!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
         lookup_var x t = SOME w` by
    (rpt strip_tac >>
     qpat_x_assum `!op w. _ ==> eval_operand op t = SOME w`
       (qspec_then `Var x` mp_tac) >> simp[eval_operand_def]) >>
  qexists_tac `t` >> simp[] >>
  irule intcall_joint_res_log_frame >> simp[] >>
  reverse conj_tac >- fs[] >>
  qexistsl_tac [`s`, `sm`] >> simp[] >>
  rpt strip_tac >>
  `a + k <= fp.jc_lo` by metis_tac[intcall_frame_ok_def] >>
  drule_all allocation_frame_below >> simp[]
QED

Theorem intcall_joint_res_inst_idx:
  intcall_joint_res fp ce env es sa (s with vs_inst_idx := k) <=>
  intcall_joint_res fp ce env es sa s
Proof
  simp[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_inst_idx, allocas_above_def,
       eval_operand_def, lookup_var_def, local_region_def,
       ret_pc_ok_def, return_buf_frame_def] >>
  Cases_on `fp.jc_rb` >> simp[return_buf_frame_def] >>
  rename1 `fp.jc_rb = SOME rb` >> PairCases_on `rb` >>
  simp[return_buf_frame_def, lookup_var_def]
QED

(* Position a straight-line resource endpoint in its containing function. *)
Theorem intcall_resource_run_gas_path:
  fn_has_code sa sb fp.jc_func /\ same_blocks sa sb /\
  inst_extends sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  intcall_joint_res fp ce env es sb t ==>
  ?u. gas_path fp.jc_ctx fp.jc_func s
        (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))) (OK u) /\
    intcall_joint_res fp ce env es sb u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_vars = t.vs_vars /\ u.vs_allocas = t.vs_allocas /\
    u.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb fp.jc_func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, same_blocks_def, inst_extends_def] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  drule_all tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`fp.jc_ctx`] mp_tac) >>
  strip_tac >> qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[intcall_joint_res_inst_idx, same_blocks_def] >> metis_tac[]
QED
