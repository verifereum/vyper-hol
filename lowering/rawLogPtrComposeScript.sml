(* Source and post-data boundaries shared by both RawLog branches. *)
Theory rawLogPtrCompose
Ancestors
  rawLogPtrDynamicTail rawLogPtrFixed bodySimRawLogTails gasSummaryComposePtr
  fragGasPathPtr wordArgsPtr exprSimWordArgs exprSimProps loweringPosts
  vyperInterpreter vyperValue vyperState vyperContext vyperEvent gasCount
  bodyPtrDefs compileEnv exprLoweringProps list finite_map venomState
  exprSimRawLog venomInst venomExecSemantics words emitHelper context
  emitHelperProps exprSimStack exprSimDefs exprSimHash rich_list exprSimSend

Theorem raw_log_tail_summary_ptr:
  dest_BytesV dv = SOME bs /\ LENGTH vals <= 4 /\
  gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
  Q (INL NoneV)
    ((es with logs := es.logs ++
       [encode_raw_event_values cx.txn.target vals bs]) with gas_obs := []) G' tn' t ==>
  gas_summary_ptr_at D (ctx,func) PG []
    (do bs' <- lift_option_type (dest_BytesV dv) "raw_log data";
        type_check (LENGTH vals <= 4) "raw_log too many topics";
        push_log (encode_raw_event_values cx.txn.target vals bs');
        return NoneV od) (es,s,G,tn) Q R
Proof
  strip_tac >> rewrite_tac[gas_summary_ptr_at_marked, gas_marked_exec_ptr_def] >>
  qexistsl_tac [`INL NoneV`,
    `es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]`,
    `G'`, `tn'`, `OK t`] >>
  simp[bind_def, ignore_bind_def, lift_option_type_def, type_check_def,
       push_log_def, return_def, assert_def,
       vyperStateTheory.evaluation_state_component_equality] >>
  disj1_tac >> Cases_on `es` >> gvs[]
QED

Theorem raw_log_data_post_transport_ptr:
  wb_args_post ctx func cenv cx es0 sa s0 es1 ops vals t /\
  expr_post ctx func cenv cx data es1 sm sn t es2 v data_op u /\
  stmt_state_rel ctx func cenv cx es0 s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sm x) /\
               (!l. op <> Label l)) ops /\
  EVERY (\op. op_taint tn1 op = {}) ops /\
  ghost_kept cenv es0 sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sm G1 tn1 t G2 tn2 ==>
  wb_frame cenv es0 es2 sa s0 u /\
  eval_operands ops u = SOME (MAP event_value_to_word vals) /\
  EVERY (\op. op_taint tn2 op = {}) ops /\
  ghost_kept cenv es0 sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >> drule_all raw_log_data_post_transport >> strip_tac >>
  `ghost_kept cenv es0 sa G0 tn0 s0 G2 tn2` by
    (`wb_frame cenv es0 es1 sa s0 t` by fs[wb_args_post_def] >>
     drule_all ghost_kept_wb_trans >> simp[]) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `LIST_REL _ ops vals` mp_tac >>
      rpt (pop_assum kall_tac) >> qid_spec_tac `vals` >>
      Induct_on `ops` >> Cases_on `vals` >>
      simp[eval_operands_def, e2eDefsTheory.event_value_to_word_eq_val_to_w256] >>
      rpt strip_tac >> first_x_assum drule >> simp[]) >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  `op_taint tn2 op = op_taint tn1 op` by
    (irule ghost_kept_operand >> metis_tac[]) >> metis_tac[]
QED

(* Determinism identifies the semantic post with the checked run endpoint. *)
Theorem raw_log_run_suffix_frame:
  run_inst_seq prefix s = OK mid /\
  run_inst_seq (prefix ++ [inst]) s = OK t /\
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit (n2w (LENGTH ops)) :: (REVERSE ops ++ [sz;pop]) /\
  LENGTH ops < dimword (:256) /\
  eval_operand pop mid = SOME off /\ eval_operand sz mid = SOME len /\
  eval_operands ops mid = SOME (MAP event_value_to_word vals) /\
  TAKE (w2n len) (DROP (w2n off) mid.vs_memory ++ REPLICATE (w2n len) 0w) = bytes /\
  stmt_state_rel ctx func cenv cx es mid /\ wb_frame cenv es0 es sa s0 mid ==>
  stmt_state_rel ctx func cenv cx
    (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bytes]) t /\
  wb_frame cenv es0
    (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bytes]) sa s0 t
Proof
  strip_tac >> drule_all raw_log_core_frame >> strip_tac >>
  qpat_assum `run_inst_seq prefix s = OK mid` (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `[inst]` mp_tac) >>
  simp[run_inst_seq_def] >> strip_tac >> gvs[]
QED

Theorem emitted_insts_final_emit:
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  emit_inst opc ops outs sm = (u,sb) ==>
  emitted_insts sa sb = emitted_insts sa sm ++ [mk_inst sm.cs_next_id opc ops outs]
Proof
  strip_tac >> Cases_on `u` >>
  `sb.cs_current_insts = sm.cs_current_insts ++ [mk_inst sm.cs_next_id opc ops outs]` by
    gvs[emit_inst_def, comp_bind_def, comp_return_def, fresh_id_def, emit_def] >>
  pure_rewrite_tac[emitted_insts_def] >>
  qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
  qpat_x_assum `sm.cs_current_insts = _` SUBST1_TAC >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC
QED

(* Consumers pass the concrete endpoint returned by the pointer tail. *)
Theorem raw_log_dynamic_counted_post_ptr:
  expr_has_effect e /\
  post_value_type cenv e = expr_type e /\
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op; Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = (u,sb) /\
  (!x. data_op = Var x ==> not_fresh_at sm x) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) ops /\
  LENGTH ops < dimword (:256) /\
  eval_operand data_op s = SOME (n2w b) /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  mload b s = n2w (LENGTH bs) /\
  TAKE (LENGTH bs) (DROP (b+32) s.vs_memory ++ REPLICATE (LENGTH bs) 0w) = bs /\
  b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  wb_frame cenv es0 es sa s0 s /\ sa.cs_next_var <= sm.cs_next_var /\
  expr_type e = NoneT /\
  run_inst_seq (emitted_insts sm sb) s = OK t /\
  gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ghost_inv d cenv cx (es with logs := es.logs ++
    [encode_raw_event_values cx.txn.target vals bs]) G' tn'
    (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ghost_kept cenv es sm G tn s G' tn' ==>
  expr_post ctx func cenv cx e es0 sa sb s0
    (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs])
    NoneV (Lit 0w) (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ghost_inv d cenv cx (es with logs := es.logs ++
    [encode_raw_event_values cx.txn.target vals bs]) G' tn'
    (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ghost_kept cenv es sm G tn s G' tn'
Proof
  strip_tac >>
  qpat_x_assum `post_value_type cenv e = _` (fn th =>
    qpat_assum `expr_type e = NoneT` (fn th2 => assume_tac (TRANS th th2))) >>
  simp[] >>
  drule_all raw_log_dynamic_prepare_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm s2) s = OK mid` >>
  `s2.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm s2` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >> gvs[] >>
     pure_rewrite_tac[emitted_insts_def] >> simp[NoAsms] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC) >>
  drule_all emitted_insts_final_emit >> strip_tac >>
  `stmt_state_rel ctx func cenv cx
      (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) t /\
   wb_frame cenv es0
     (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) sa s0 t` by
    (`run_inst_seq (emitted_insts sm s2 ++
        [mk_inst s2.cs_next_id LOG
          (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) []]) s = OK t`
       by metis_tac[] >>
     drule_at (Pat `run_inst_seq (prefix ++ [inst]) s = OK t`)
       raw_log_run_suffix_frame >>
     simp[mk_inst_def] >>
     disch_then irule >> simp[]) >>
  irule expr_post_none_intro >> simp[stmt_state_rel_inst_idx] >>
  qpat_x_assum `expr_has_effect e` mp_tac >>
  qpat_x_assum `wb_frame cenv es0 _ sa s0 t` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[wb_frame_def, locals_kept_def, popped_kept_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem raw_log_fixed_counted_post_ptr:
  expr_has_effect e /\
  post_value_type cenv e = expr_type e /\
  emit_void MSTORE [ptr_op; data_op] sm = (u,s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;ptr_op]) [] s1 = (u',sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand data_op s = SOME w /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  LENGTH ops < dimword (:256) /\ LENGTH bs = 32 /\ TAKE 32 (word_to_bytes_be w) = bs /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 es sa s0 s /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n p,32) /\
  (!aid b sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n p) 32 b sz) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
    regions_disjoint (w2n p) 32 b sz) /\ expr_type e = NoneT /\
  run_inst_seq (emitted_insts sm sb) s = OK t /\
  gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ghost_inv d cenv cx (es with logs := es.logs ++
    [encode_raw_event_values cx.txn.target vals bs]) G' tn'
    (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ghost_kept cenv es sm G tn s G' tn' ==>
  expr_post ctx func cenv cx e es0 sa sb s0
    (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs])
    NoneV (Lit 0w) (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ghost_inv d cenv cx (es with logs := es.logs ++
    [encode_raw_event_values cx.txn.target vals bs]) G' tn'
    (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ghost_kept cenv es sm G tn s G' tn'
Proof
  strip_tac >>
  qpat_x_assum `post_value_type cenv e = _` (fn th =>
    qpat_assum `expr_type e = NoneT` (fn th2 => assume_tac (TRANS th th2))) >>
  simp[] >> drule_all raw_log_fixed_store_frame >> strip_tac >>
  `s1.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm s1` by
    (qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_void_def, emit_inst_def, comp_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
     pure_rewrite_tac[emitted_insts_def] >> simp[NoAsms, DROP_LENGTH_APPEND]) >>
  drule_all emitted_insts_final_emit >> strip_tac >>
  `eval_operand ptr_op (mstore (w2n p) w s) = SOME p /\
   eval_operands ops (mstore (w2n p) w s) = SOME (MAP event_value_to_word vals)` by
    (`eval_operands ops (mstore (w2n p) w s) = eval_operands ops s` by
       (rpt (pop_assum kall_tac) >> Induct_on `ops` >>
        simp[eval_operands_def] >> Cases_on `h` >>
        simp[eval_operand_def, mstore_def, lookup_var_def]) >>
     simp[] >> Cases_on `ptr_op` >>
     gvs[eval_operand_def, mstore_def, lookup_var_def]) >>
  `stmt_state_rel ctx func cenv cx
      (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) t /\
   wb_frame cenv es0
     (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) sa s0 t` by
    (`run_inst_seq (emitted_insts sm s1 ++
        [mk_inst s1.cs_next_id LOG
          (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;ptr_op]) []]) s = OK t`
       by metis_tac[] >>
     drule_at (Pat `run_inst_seq (prefix ++ [inst]) s = OK t`)
       raw_log_run_suffix_frame >>
     `32 MOD dimword (:256) = 32` by simp[dimword_def] >>
     simp[mk_inst_def, eval_operand_def] >>
     disch_then irule >> simp[]) >>
  irule expr_post_none_intro >> simp[stmt_state_rel_inst_idx] >>
  qpat_x_assum `expr_has_effect e` mp_tac >>
  qpat_x_assum `wb_frame cenv es0 _ sa s0 t` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[wb_frame_def, locals_kept_def, popped_kept_def, lookup_var_def] >>
  metis_tac[]
QED
