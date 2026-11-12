(* Physical postconditions at the very endpoint of unsigned scaling. *)
Theory bodyPtrWordBuiltinsScalingPost
Ancestors bodyPtrWordBuiltinsScaling exprSimWordBuiltins
  fragGasFresh fragGasSeqAbort exprLoweringProps fragExec freshWrites varsExt
  compileEnv list venomState venomExecSemantics

Theorem word_scale_actual_post:
  compile_as_wei_value_int v m F sa = (op,sb) /\
  0 < m /\ m < dimword (:256) /\ w2n w * m < dimword (:256) /\
  (!z. v = Var z ==> not_fresh_at sa z) /\ eval_operand v s = SOME w /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  eval_operand op (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME (w * n2w m) /\
  (!z a. not_fresh_at sa z /\ lookup_var z s = SOME a ==>
    lookup_var z (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME a) /\
  (!aid bl. FLOOKUP s.vs_allocas aid = SOME bl ==> FLOOKUP t.vs_allocas aid = SOME bl) /\
  t.vs_memory = s.vs_memory /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `straight_fresh (compile_as_wei_value_int v m F)` by simp[straight_fresh_as_wei_value_int] >>
  `eval_operand v (drop_fresh sa s) = SOME w` by simp[eval_operand_drop_fresh] >>
  drule_all compile_as_wei_value_int_run >> strip_tac >>
  `?t0. run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t0 /\
        eval_operand op t0 = SOME (w * n2w m)` by metis_tac[] >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> gvs[]
QED

Theorem word_scale_cursor_length:
  compile_as_wei_value_int v m F sa = (op,sb) ==>
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + (if m = 1 then 0 else 6)
Proof
  strip_tac >> drule word_scale_current_block >> simp[]
QED
