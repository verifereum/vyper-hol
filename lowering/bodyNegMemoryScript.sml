(* Actual Neg opcode suffix; independent of source numeric correctness. *)
Theory bodyNegMemory
Ancestors
  exprSimUnopProps exprSimHypsDefs exprSimProps exprSimMemoryStack
  exprSimMemoryValues exprSimMemDefs loweringPosts gasNormalPrefix gasSummary
  gasSummaryCompose gasContext gasCount fragGasMode fragGasPathMem fragGasSeqMem gasExemptCert
  exprSimUnopProps
  exprSimSource
  bodyMemoryDefs   emitHelperProps
  fragExecMem instMemFrontier allocaHistoryFragment
  exprLoweringProps emitHelper venomInst venomState words list rich_list
  compileEnv fragExec exprSimDefs valueEncoding vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState freshWrites varsExt integer_word
  arithmeticProps vyperArith vyperTypeSystem vyperTyping
  exprBopLowering

Theorem body_neg_no_ranges_seq[local]:
  !is s. EVERY (\i. !q. inst_mem_below_frontier i q) is ==>
         run_inst_seq_mem_ok is s
Proof
  cheat
QED

Theorem body_neg_prefix_mem_ok:
  compile_neg x ty sm = (dst,sn) ==>
  run_inst_seq_mem_ok (emitted_insts sm sn) s
Proof
  cheat
QED

Theorem body_neg_emitted:
  compile_neg x ty sm = (dst,sn) ==>
  emitted_insts sm sn =
    [mk_inst sm.cs_next_id SGT [x; Lit (FST (type_bounds ty))]
       ["%" ++ toString sm.cs_next_var];
     mk_inst (sm.cs_next_id + 1) ASSERT [Var ("%" ++ toString sm.cs_next_var)] [];
     mk_inst (sm.cs_next_id + 2) SUB [Lit 0w; x]
       ["%" ++ toString (sm.cs_next_var + 1)]]
Proof
  cheat
QED

Theorem body_neg_straight_fresh[local]:
  straight_fresh (compile_neg x ty)
Proof
  cheat
QED

Theorem body_neg_shape:
  compile_neg x ty sm = (dst,sn) ==>
  sn.cs_blocks = sm.cs_blocks /\ sn.cs_current_bb = sm.cs_current_bb /\
  sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
  sm.cs_next_var <= sn.cs_next_var /\
  writes_fresh sm (emitted_insts sm sn) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             ~is_ext_call_op i.inst_opcode) (emitted_insts sm sn)
Proof
  cheat
QED

Theorem body_neg_history:
  compile_neg x ty sm = (dst,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sn) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)
Proof
  cheat
QED

Theorem body_neg_state_post:
  compile_neg x ty sm = (dst,sn) /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx es s /\
  run_inst_seq (emitted_insts sm sn) s = OK q ==>
  stmt_state_rel ctx func cenv cx es q /\
  (!z v. not_fresh_at sm z /\ lookup_var z s = SOME v ==>
         lookup_var z q = SOME v) /\
  q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
  q.vs_alloca_next = s.vs_alloca_next
Proof
  cheat
QED

Theorem body_neg_result:
  compile_neg x ty sm = (dst,sn) ==>
  dst = Var ("%" ++ toString (sm.cs_next_var + 1))
Proof
  cheat
QED

Theorem body_neg_old_operand[local]:
  (!z. x = Var z ==> not_fresh_at sm z) ==>
  eval_operand x (update_var ("%" ++ toString sm.cs_next_var) v s) =
  eval_operand x s
Proof
  cheat
QED

Theorem body_neg_run:
  compile_neg x ty sm = (dst,sn) /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ eval_operand x s = SOME w ==>
  (word_gt w (FST (type_bounds ty)) ==>
    ?t. run_inst_seq (emitted_insts sm sn) s = OK t /\
        eval_operand dst t = SOME (0w - w)) /\
  (~word_gt w (FST (type_bounds ty)) ==>
    run_inst_seq (emitted_insts sm sn) s =
      Abort Revert_abort (revert_state (set_returndata []
        (update_var ("%" ++ toString sm.cs_next_var) 0w s))))
Proof
  cheat
QED

Theorem body_neg_frag_mem_at:
  compile_neg x ty sm = (dst,sn) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  (~word_gt w (FST (type_bounds ty)) ==> !q. R (Abort Revert_abort q)) ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
         eval_operand x s = SOME w /\ alloca_history func s)
    (\s. word_gt w (FST (type_bounds ty)) /\
         stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (0w - w) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R
Proof
  cheat
QED

Theorem body_neg_signed_interval:
  0 < n ==>
  (within_int_bound (Signed n) i <=>
   -&(2 ** (n - 1)) <= i /\ i < &(2 ** (n - 1)))
Proof
  cheat
QED

Theorem body_neg_signed_comparison:
  0 < n /\ n <= 256 /\ within_int_bound (Signed n) i ==>
  (word_gt (i2w i : bytes32) (i2w (-&(2 ** (n - 1)))) <=>
   within_int_bound (Signed n) (-i))
Proof
  cheat
QED

Theorem body_neg_source_value:
  is_numeric_type ann /\ ~is_uint_type ann /\
  0 < type_bits ann /\ type_bits ann <= 256 /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  word_gt (typed_val_to_w256 tv v) (FST (type_bounds ann)) ==>
  ?out. unop_result cx ann Neg [ann] v es = INL out /\
        value_has_type tv out /\
        typed_val_to_w256 tv out = 0w - typed_val_to_w256 tv v
Proof
  cheat
QED

Theorem body_neg_source_abort:
  is_numeric_type ann /\ ~is_uint_type ann /\
  0 < type_bits ann /\ type_bits ann <= 256 /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  ~word_gt (typed_val_to_w256 tv v) (FST (type_bounds ann)) ==>
  !q. expr_exit (unop_result cx ann Neg [ann] v es) (Abort Revert_abort q)
Proof
  cheat
QED

Theorem expr_body_pre_neg:
  expr_body_pre cenv cx env (Builtin ann Neg [e]) es ==>
  ann = expr_type e /\ expr_body_pre cenv cx env e es /\
  is_numeric_type ann /\ ~is_uint_type ann /\
  0 < type_bits ann /\ type_bits ann <= 256 /\ is_word_type ann
Proof
  cheat
QED

Theorem body_neg_tail_mem:
  compile_neg x ann sm = (op,sb) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  is_numeric_type ann /\ ~is_uint_type ann /\ is_word_type ann /\
  0 < type_bits ann /\ type_bits ann <= 256 /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v1 /\
  expr_type e = ann /\ sa.cs_next_var <= sm.cs_next_var /\
  expr_post ctx func cenv cx e es sa sm s0 es' v1 x entry /\
  alloca_history func entry /\ s0.vs_alloca_next <= entry.vs_alloca_next /\
  res = unop_result cx ann Neg [ann] v1 es' ==>
  frag_exec_mem ctx sm sb (\s. s = entry)
    (\s. ?v. res = INL v /\
         expr_post ctx func cenv cx (Builtin ann Neg [e]) es
           sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (expr_exit res)
Proof
  cheat
QED

Theorem body_compile_expr_neg[local]:
  compile_expr cenv ty (Builtin ann Neg [e]) sa =
  compile_builtin_dispatch cenv ann ty Neg [e] sa
Proof
  cheat
QED

Theorem body_lower_value_neg[local]:
  lower_value compile_expr cenv ty (Builtin ann Neg [e]) sa = (op,sb) ==>
  ?x sm. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
         compile_neg x (expr_type e) sm = (op,sb)
Proof
  cheat
QED

Theorem body_compile_neg_stack[local]:
  !sa. ?t op sb. compile_expr cenv ty (Builtin ann Neg [e]) sa =
                (StackValue t op,sb)
Proof
  cheat
QED

Theorem compile_neg_sim_mem:
  expr_body_pre cenv cx env (Builtin ann Neg [e]) es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin ann Neg [e]) es
Proof
  cheat
QED

Theorem compile_neg_vv_sim_mem:
  expr_body_pre cenv cx env (Builtin ann Neg [e]) es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann Neg [e]) es
Proof
  cheat
QED

