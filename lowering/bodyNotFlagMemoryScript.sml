(* Memory-safe unary lowering. *)
Theory bodyNotFlagMemory
Ancestors
  exprSimSource exprSimHypsDefs exprSimProps exprSimUnopProps
  exprSimMemoryStack exprSimMemoryValues exprSimMemDefs loweringPosts
  gasNormalPrefix gasSummary gasSummaryCompose gasContext gasCount fragGasMode
  fragGasPathMem fragGasSeqMem gasExemptCert
  bodyMemoryDefs emitHelperProps fragExecMem instMemFrontier allocaHistoryFragment
  exprLoweringProps emitHelper venomInst venomState words list rich_list
  compileEnv fragExec exprSimDefs valueEncoding vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState vyperExprNoControl
  builtinSimple freshWrites varsExt vyperTyping vyperValueOperation integer_word

Theorem body_xor_prefix_mem_ok:
  emit_op XOR ops sm = (dst,sn) ==>
  run_inst_seq_mem_ok (emitted_insts sm sn) s
Proof
  cheat
QED

Theorem body_xor_run:
  emit_op XOR [x; Lit mask] sm = (dst,sn) /\ eval_operand x s = SOME w ==>
  run_inst_seq (emitted_insts sm sn) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var)) (word_xor w mask) s)
Proof
  cheat
QED

Theorem body_xor_history:
  emit_op XOR ops sm = (dst,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sn) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)
Proof
  cheat
QED

Theorem body_xor_state_post:
  emit_op XOR [x; Lit mask] sm = (dst,sn) /\ eval_operand x s = SOME w /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx es s ==>
  ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
      stmt_state_rel ctx func cenv cx es q /\
      eval_operand dst q = SOME (word_xor w mask) /\
      (!z v. not_fresh_at sm z /\ lookup_var z s = SOME v ==>
             lookup_var z q = SOME v) /\
      q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
      q.vs_alloca_next = s.vs_alloca_next
Proof
  cheat
QED

Theorem body_xor_frag_mem_at:
  emit_op XOR [x; Lit mask] sm = (dst,sn) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
         eval_operand x s = SOME w /\ alloca_history func s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (word_xor w mask) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R
Proof
  cheat
QED

Theorem body_not_flag_tail_mem[local]:
  emit_op XOR [x; Lit (n2w (2 ** m - 1))] sm = (op,sb) /\
  local_ptrs_reserved cenv sm /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  evaluate_type (get_tenv cx) (FlagT nsid) = SOME (FlagTV m) /\
  value_has_type (FlagTV m) v1 /\ expr_type e = FlagT nsid /\
  sa.cs_next_var <= sm.cs_next_var /\
  expr_post ctx func cenv cx e es sa sm s0 es' v1 x entry /\
  alloca_history func entry /\ s0.vs_alloca_next <= entry.vs_alloca_next /\
  res = unop_result cx (FlagT nsid) Not [expr_type e] v1 es' ==>
  frag_exec_mem ctx sm sb (\s. s = entry)
    (\s. ?v. res = INL v /\
         expr_post ctx func cenv cx (Builtin (FlagT nsid) Not [e]) es
           sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (expr_exit res)
Proof
  cheat
QED

Theorem compile_not_flag_sim_mem:
  is_flag_type (expr_type e) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin (expr_type e) Not [e]) es
Proof
  cheat
QED

Theorem compile_not_flag_vv_sim_mem:
  is_flag_type (expr_type e) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin (expr_type e) Not [e]) es
Proof
  cheat
QED

