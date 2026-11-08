(* Memory-enabled endpoints for the RawLog data continuation. *)
Theory bodyMemRawLogCompose
Ancestors
  bodyMemRawLogExecution bodyMemRawLogStages bodyMemRawLogAllocation bodySimRawLogTails
  bodyMemBiKeccakBounds stmtSimLogSuffix exprSimHash exprSimRawLog
  exprSimProps exprSimHyps exprSimMemDefs gasSummary fragGasMode gasOutcome
  vyperTyping vyperValue vyperState valueEncoding venomState e2eDefs list

Theorem raw_log_data_operands_mem:
  wb_args_post ctx func cenv cx es0 sa s0 es1 ops vals t /\
  expr_post ctx func cenv cx data es1 sm sn t es2 v data_op u /\
  stmt_state_rel ctx func cenv cx es0 s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sm x) /\
               (!l. op <> Label l)) ops ==>
  wb_frame cenv es0 sa s0 u /\
  eval_operands ops u = SOME (MAP event_value_to_word vals)
Proof
  strip_tac >> drule_all raw_log_data_post_transport >> strip_tac >> simp[] >>
  irule log_operands_values >>
  simp[LIST_REL_MAP2, event_value_to_word_eq_val_to_w256]
QED

Theorem raw_log_dynamic_data_bounds_mem:
  expr_body_pre cenv cx env data es /\
  expr_type data = BaseT (BytesT (Dynamic cap)) /\
  gas_marked_exec T (ctx,func)
    (bind (eval_expr cx data) (read_result cx)) (es,t) marks (INL v) ee r /\
  expr_post ctx func cenv cx data es1 sm sn t (ee with gas_obs := []) v data_op u /\
  expr_store_bound cx (expr_type data) v data_op u ==>
  ?bs b. v = BytesV bs /\
    eval_operand data_op u = SOME (n2w b) /\
    mload b u = n2w (LENGTH bs) /\
    TAKE (LENGTH bs) (DROP (b + 32) u.vs_memory ++
      REPLICATE (LENGTH bs) 0w) = bs /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    b + 32 <= u.vs_alloca_next /\
    (LENGTH bs = 0 \/ b + 32 + LENGTH bs <= u.vs_alloca_next)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env data
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by simp[] >>
  `bind (eval_expr cx data) (read_result cx)
     (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
     (INL v, ee with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all (SRULE [SF ETA_ss] expr_body_pre_base_result) >> strip_tac >>
  `?bs. v = BytesV bs` by
    (qpat_x_assum `!v'. INL v = _ ==> _` mp_tac >>
     simp[] >> Cases_on `v` >> simp[value_has_type_def]) >>
  gvs[] >>
  `evaluate_type (get_tenv cx) (expr_type data) =
     SOME (BaseTV (BytesT (Dynamic cap)))` by
    (drule expr_body_pre_type_evaluates >>
     simp[evaluate_type_def, AllCaseEqs()]) >>
  `expr_store_bound cx (expr_type data) (BytesV bs) data_op u` by simp[] >>
  drule_all keccak_dynamic_post_bounds >> strip_tac >>
  qexists_tac `b` >>
  fs[mload_def, mem_word_at_def, mem_bytes_at_def]
QED

Theorem raw_log_tail_summary_mem[local]:
  dest_BytesV dv = SOME bs /\ LENGTH vals <= 4 /\
  gas_path_mem ctx func s 0 (OK t) /\
  Q (INL NoneV)
    ((es with logs := es.logs ++
       [encode_raw_event_values cx.txn.target vals bs]) with gas_obs := []) t ==>
  gas_summary_at T (ctx,func) []
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
       push_log_def, return_def, assert_def, gas_marked_path_def,
       evaluation_state_component_equality] >>
  disj1_tac >> Cases_on `es` >> gvs[]
QED

Theorem raw_log_dynamic_continuation_mem:
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op; Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = (u,sb) /\
  (!x. data_op = Var x ==> not_fresh_at sm x) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) ops /\ LENGTH ops <= 4 /\
  LENGTH vals <= 4 /\
  eval_operand data_op s = SOME (n2w b) /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  mload b s = n2w (LENGTH bs) /\
  TAKE (LENGTH bs) (DROP (b + 32) s.vs_memory ++ REPLICATE (LENGTH bs) 0w) = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  wb_frame cenv es0 sa s0 s /\ sa.cs_next_var <= sm.cs_next_var /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT /\
  fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  b + 32 <= s.vs_alloca_next /\
  (LENGTH bs = 0 \/ b + 32 + LENGTH bs <= s.vs_alloca_next) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_outcome T tops (ctx,func)
    (do bs' <- lift_option_type (dest_BytesV (BytesV bs)) "raw_log data";
        type_check (LENGTH vals <= 4) "raw_log too many topics";
        push_log (encode_raw_event_values cx.txn.target vals bs');
        return NoneV od) (es,s)
    (\res ee t. res = INL NoneV /\
       expr_post ctx func cenv cx e es0 sa sb s0 ee NoneV (Lit 0w) t /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_log_dynamic_tail_mem_counted >> strip_tac >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  irule raw_log_tail_summary_mem >> simp[dest_BytesV_def] >>
  qexists_tac `t` >> simp[] >>
  drule raw_log_post_gas_obs >>
  disch_then (qspec_then `[]` mp_tac) >> simp[]
QED

Theorem raw_log_fixed_data_view_mem:
  expr_body_pre cenv cx env data es /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  gas_marked_exec T (ctx,func)
    (bind (eval_expr cx data) (read_result cx)) (es,t) marks (INL v) ee r /\
  expr_post ctx func cenv cx data es1 sm sn t (ee with gas_obs := []) v data_op u ==>
  ?bs w. v = BytesV bs /\ LENGTH bs = 32 /\
    eval_operand data_op u = SOME w /\ TAKE 32 (word_to_bytes_be w) = bs
Proof
  strip_tac >>
  `expr_body_pre cenv cx env data
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by simp[] >>
  `bind (eval_expr cx data) (read_result cx)
     (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
     (INL v, ee with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all (SRULE [SF ETA_ss] expr_body_pre_base_result) >> strip_tac >>
  `?bs. v = BytesV bs` by
    (qpat_x_assum `!v'. INL v = _ ==> _` mp_tac >>
     simp[] >> Cases_on `v` >> simp[value_has_type_def]) >>
  gvs[] >> drule hash_fixed_post_view >> simp[] >> metis_tac[]
QED

Theorem raw_log_fixed_continuation_mem:
  emit_void MSTORE [ptr_op; data_op] sm = (u,s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;ptr_op]) [] s1 = (u',sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand data_op s = SOME w /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\ LENGTH ops <= 4 /\
  LENGTH vals <= 4 /\ LENGTH bs = 32 /\ TAKE 32 (word_to_bytes_be w) = bs /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sa s0 s /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n p,32) /\
  (!aid b sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n p) 32 b sz) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
     regions_disjoint (w2n p) 32 b sz) /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  w2n p + 32 <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_outcome T tops (ctx,func)
    (do bs' <- lift_option_type (dest_BytesV (BytesV bs)) "raw_log data";
        type_check (LENGTH vals <= 4) "raw_log too many topics";
        push_log (encode_raw_event_values cx.txn.target vals bs');
        return NoneV od) (es,s)
    (\res ee t. res = INL NoneV /\
       expr_post ctx func cenv cx e es0 sa sb s0 ee NoneV (Lit 0w) t /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_log_fixed_tail_mem_counted >> strip_tac >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  irule raw_log_tail_summary_mem >> simp[dest_BytesV_def] >>
  qexists_tac `t` >> simp[] >>
  drule raw_log_post_gas_obs >>
  disch_then (qspec_then `[]` mp_tac) >> simp[]
QED
