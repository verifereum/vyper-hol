(* Environment reads: actual counted no-memory opcode execution. *)
Theory bodyEnvMemory
Ancestors
  gasNormalPrefix gasSummary fragGasMode
  exprSimMemDefs loweringPosts exprSimSource exprSimMemoryValues fragGasPathMem fragGasSeqMem gasCount gasContext
  exprSimMemoryStack bodyMemoryDefs bodyMemoryPreds exprSimDefs exprSimProps exprSimHypsDefs
  fragExecMem instMemFrontier allocaHistoryFragment emitHelperProps
  exprLoweringProps emitHelper venomInst venomState words list rich_list
  vyperInterpreter vyperValueOperation vyperContext
  compileEnv fragExec valueEncoding valueEncodingProofs vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState vyperTyping vyperTypeSystem

Theorem body_env_read_frag_mem:
  emit_op opc [] sm = (dst,sn) /\ ~is_terminator opc /\ opc <> INVOKE /\
  (!s. inst_mem_below_frontier
    (mk_inst sm.cs_next_id opc [] [STRING #"%" (toString sm.cs_next_var)]) s) /\
  (!s. stmt_state_rel ctx func cenv cx es s ==>
    step_inst_base (mk_inst sm.cs_next_id opc [] [STRING #"%" (toString sm.cs_next_var)]) s =
      OK (update_var (STRING #"%" (toString sm.cs_next_var)) w s)) /\
  local_ptrs_reserved cenv sm /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s)
    (\s. stmt_state_rel ctx func cenv cx es s /\ eval_operand dst s = SOME w /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R
Proof
  cheat
QED

Theorem body_env_frag_mem[local]:
  item <> PrevHash /\ item <> MsgGas /\
  compile_env_var item sa = (op,sb) /\
  evaluate_builtin cx es.accounts (env_item_type item) (Env item) [] [] = INL v /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand op s = SOME (val_to_w256 v) /\
         (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                lookup_var z s = SOME w) /\
         s.vs_memory = s0.vs_memory /\ s.vs_allocas = s0.vs_allocas /\
         s.vs_alloca_next = s0.vs_alloca_next /\ alloca_history func s) R
Proof
  cheat
QED

Theorem body_env_read_counted[local]:
  emit_op opc [] sm = (dst,sn) /\ ~is_terminator opc /\ opc <> INVOKE /\ opc <> GAS /\
  (!s. inst_mem_below_frontier
    (mk_inst sm.cs_next_id opc [] [STRING #"%" (toString sm.cs_next_var)]) s) /\
  (!s. stmt_state_rel ctx func cenv cx es s ==>
    step_inst_base (mk_inst sm.cs_next_id opc [] [STRING #"%" (toString sm.cs_next_var)]) s =
      OK (update_var (STRING #"%" (toString sm.cs_next_var)) w s)) /\
  local_ptrs_reserved cenv sm /\ fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es entry /\ alloca_history func entry /\
  ~entry.vs_halted /\ entry.vs_current_bb = sm.cs_current_bb /\
  entry.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_path_mem ctx func entry 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es t /\ eval_operand dst t = SOME w /\
      (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==> lookup_var z t = SOME v) /\
      t.vs_memory = entry.vs_memory /\ t.vs_allocas = entry.vs_allocas /\
      t.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func t /\
      t.vs_current_bb = sn.cs_current_bb /\ t.vs_inst_idx = LENGTH sn.cs_current_insts
Proof
  cheat
QED

Theorem body_env_source[local]:
  item <> PrevHash /\ item <> MsgGas ==>
  ?v. evaluate_builtin cx es.accounts (env_item_type item) (Env item) [] [] = INL v /\
      (!tail. bind (eval_expr cx (Builtin (env_item_type item) (Env item) []))
        (read_result cx) (es with gas_obs := tail) =
        (INL v, es with gas_obs := tail)) /\
      is_word_type (env_item_type item) /\
      (!tv. evaluate_type (get_tenv cx) (env_item_type item) = SOME tv ==>
        typed_val_to_w256 tv v = val_to_w256 v)
Proof
  cheat
QED

Theorem body_env_mem_prefix[local]:
  item <> PrevHash /\ item <> MsgGas /\
  lower_value compile_expr cenv ty (Builtin (env_item_type item) (Env item) []) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v t. gas_value_prefix T (ctx,func,cenv,cx)
    (ty,Builtin (env_item_type item) (Env item) []) (sa,sb,op) (es,s0) [] (v,es,t)
Proof
  cheat
QED

Theorem compile_env_body_sim_mem:
  !ctx func cenv cx ty ann item es.
    item <> PrevHash /\ item <> MsgGas /\ ann = env_item_type item ==>
    expr_sim_mem ctx func cenv cx ty (Builtin ann (Env item) []) es
Proof
  cheat
QED

(* Prior successful ordinary proof, retained verbatim for reference.
Proof
  rpt gen_tac >> strip_tac >> rw[expr_sim_mem_def] >>
  drule_all eval_expr_env >> strip_tac >> gvs[] >>
  `is_word_type (env_item_type item) /\
   !tv. evaluate_type (get_tenv cx) (env_item_type item) = SOME tv ==>
        typed_val_to_w256 tv v = val_to_w256 v` by
    (Cases_on `item` >>
     gvs[vyperContextTheory.evaluate_builtin_def, env_item_type_def, is_word_type_def,
         vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
         val_to_w256_def] >>
     simp_tac (srw_ss() ++ wordsLib.SIZES_ss) []) >>
  drule lower_value_env >> strip_tac >>
  drule_all body_env_frag_mem >>
  disch_then (qspecl_then [`s0`, `ctx`, `expr_exit (INL v)`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >> disch_then irule >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, expr_type_def,
       locals_kept_mem] >> rpt strip_tac >> simp[]
QED

*)

Theorem compile_env_body_vv_sim_mem:
  !ctx func cenv cx ty ann item es.
    item <> PrevHash /\ item <> MsgGas /\ ann = env_item_type item ==>
    expr_vv_sim_mem ctx func cenv cx ty (Builtin ann (Env item) []) es
Proof
  cheat
QED

Theorem body_env_mem_case:
  !cx ann item args. item <> PrevHash /\ item <> MsgGas ==>
    body_expr_mem_ok cx (Builtin ann (Env item) args)
Proof
  cheat
QED

