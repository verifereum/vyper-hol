(* Actual CALLDATASIZE execution, prefix safety and body memory closure. *)
Theory bodyCalldataMemory
Ancestors
  exprSimSource exprSimMemoryValues fragGasPathMem fragGasSeqMem gasCount gasContext
  exprSimMemoryStack bodyMemoryDefs bodyMemoryPreds exprSimCalldata exprSimHypsDefs
  exprSimProps gasNormalPrefix gasSummary fragGasMode loweringPosts exprSimMemDefs
  fragExecMem instMemFrontier allocaHistoryFragment emitHelperProps
  exprLoweringProps emitHelper venomInst venomState words list rich_list
  compileEnv fragExec exprSimDefs valueEncoding vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState vyperTyping vyperTypeSystem

Theorem body_calldatasize_prefix_mem_ok[local]:
  emit_op CALLDATASIZE [] sm = (dst,sn) ==>
  run_inst_seq_mem_ok (emitted_insts sm sn) s
Proof
  cheat
QED

Theorem body_calldatasize_run[local]:
  emit_op CALLDATASIZE [] sm = (dst,sn) ==>
  run_inst_seq (emitted_insts sm sn) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var))
                   (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s)
Proof
  cheat
QED

Theorem body_calldatasize_history[local]:
  emit_op CALLDATASIZE [] sm = (dst,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sn) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)
Proof
  cheat
QED

Theorem body_calldatasize_gas_path[local]:
  emit_op CALLDATASIZE [] sm = (dst,sn) /\ fn_has_code sm sn func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sn) s = OK q ==>
  gas_path_mem ctx func s 0
    (OK (q with vs_inst_idx := LENGTH sn.cs_current_insts))
Proof
  cheat
QED

Theorem body_calldatasize_state_post[local]:
  emit_op CALLDATASIZE [] sm = (dst,sn) /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx es s ==>
  ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
      stmt_state_rel ctx func cenv cx es q /\
      eval_operand dst q = SOME (val_to_w256 (IntV &LENGTH cx.txn.calldata)) /\
      (!z v. not_fresh_at sm z /\ lookup_var z s = SOME v ==>
             lookup_var z q = SOME v) /\
      q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
      q.vs_alloca_next = s.vs_alloca_next
Proof
  cheat
QED

Theorem body_calldatasize_frag_mem[local]:
  emit_op CALLDATASIZE [] sm = (dst,sn) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
         alloca_history func s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (val_to_w256 (IntV &LENGTH cx.txn.calldata)) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R
Proof
  cheat
QED

Theorem body_calldatasize_mem_prefix[local]:
  lower_value compile_expr cenv ty (Builtin (BaseT (UintT 256)) CalldataLen []) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_value_prefix T (ctx,func,cenv,cx)
    (ty,Builtin (BaseT (UintT 256)) CalldataLen [])
    (sa,sb,op) (es,s0) [] (IntV &LENGTH cx.txn.calldata,es,t)
Proof
  cheat
QED

(* Prior successful uncounted proof, retained for reference.
Theorem compile_calldatasize_body_sim_mem:
  !ctx func cenv cx env ty ann args es.
    expr_body_pre cenv cx env (Builtin ann CalldataLen args) es ==>
    expr_sim_mem ctx func cenv cx ty (Builtin ann CalldataLen args) es
Proof
  rpt gen_tac >> strip_tac >>
  `args = [] /\ ann = BaseT (UintT 256)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >>
  `!st. eval_expr cx (Builtin (BaseT (UintT 256)) CalldataLen []) st =
        (INL (Value (IntV &LENGTH cx.txn.calldata)), st)` by
    (gen_tac >>
     Cases_on `eval_expr cx (Builtin (BaseT (UintT 256)) CalldataLen []) st` >>
     drule eval_expr_calldata_len >> simp[] >> strip_tac >> gvs[]) >>
  rw[expr_sim_mem_def] >>
  gvs[bind_def, read_result_def, return_def, lower_value_calldata_len] >>
  drule_all body_calldatasize_frag_mem >>
  disch_then (qspecl_then [`es`, `s0`, `cx`, `ctx`,
    `expr_exit (INL (IntV &LENGTH cx.txn.calldata))`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
  disch_then irule >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, is_word_type_def, typed_val_to_w256_word_value,
       word_value_def, locals_kept_mem] >> rpt strip_tac >> simp[]
QED

*)

Theorem compile_calldatasize_body_sim_mem:
  !ctx func cenv cx env ty ann args es.
    expr_body_pre cenv cx env (Builtin ann CalldataLen args) es ==>
    expr_sim_mem ctx func cenv cx ty (Builtin ann CalldataLen args) es
Proof
  cheat
QED

Theorem compile_calldatasize_body_vv_sim_mem:
  !ctx func cenv cx env ty ann args es.
    expr_body_pre cenv cx env (Builtin ann CalldataLen args) es ==>
    expr_vv_sim_mem ctx func cenv cx ty (Builtin ann CalldataLen args) es
Proof
  cheat
QED

Theorem body_calldatalen_mem_case:
  !cx ann args. body_expr_mem_ok cx (Builtin ann CalldataLen args)
Proof
  cheat
QED

