(* Physical frames on the same rounding run as the counted pointer path. *)
Theory bodyPtrWordBuiltinsRoundingPost
Ancestors bodyPtrWordBuiltinsRounding builtinProps exprSimWordBuiltins
  fragGasFresh fragGasSeqAbort exprLoweringProps fragExec freshWrites varsExt
  compileEnv list venomState venomExecSemantics

Theorem word_round_clean_run:
  (if up then compile_ceil else compile_floor) v divisor sa = (op,sb) /\
  eval_operand v s = SOME w /\ fresh_vars_wrt sa s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME
      (safe_sdiv (if word_lt w 0w then
         (if up then w else w - n2w (divisor-1))
       else (if up then w + n2w (divisor-1) else w)) (n2w divisor))
Proof
  Cases_on `up` >> simp[] >> strip_tac
  >- (drule_all compile_ceil_correct >> simp[]) >>
  drule_all compile_floor_correct >> simp[]
QED

Theorem word_round_actual_post:
  (if up then compile_ceil else compile_floor) v divisor sa = (op,sb) /\
  (!z. v = Var z ==> not_fresh_at sa z) /\ eval_operand v s = SOME w /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  eval_operand op (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME
    (safe_sdiv (if word_lt w 0w then
       (if up then w else w - n2w (divisor-1))
     else (if up then w + n2w (divisor-1) else w)) (n2w divisor)) /\
  (!z a. not_fresh_at sa z /\ lookup_var z s = SOME a ==>
    lookup_var z (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME a) /\
  (!aid bl. FLOOKUP s.vs_allocas aid = SOME bl ==> FLOOKUP t.vs_allocas aid = SOME bl) /\
  t.vs_memory = s.vs_memory /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `straight_fresh ((if up then compile_ceil else compile_floor) v divisor)` by
    (Cases_on `up` >> simp[straight_fresh_ceil, straight_fresh_floor]) >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand v (drop_fresh sa s) = SOME w` by simp[eval_operand_drop_fresh] >>
  drule_all word_round_clean_run >> strip_tac >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> gvs[]
QED

Theorem word_round_cursor_length:
  (if up then compile_ceil else compile_floor) v divisor sa = (op,sb) ==>
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 6
Proof
  strip_tac >> drule word_round_current_block >> strip_tac >>
  drule word_round_emitted_shape >> simp[]
QED
