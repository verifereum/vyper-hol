(* Scalar posts on the actual normal arithmetic run. *)
Theory bodyPtrWordBuiltinsModularPost
Ancestors bodyPtrWordBuiltinsModular bodyPtrWordBuiltinsModularSource
  exprSimWordBuiltins exprSimWordArgs fragGasFresh fragGasSeqAbort
  exprLoweringProps fragExec freshWrites varsExt
  compileEnv list venomState venomExecSemantics

Theorem word_modular_actual_post:
  (if is_mul then compile_mulmod else compile_addmod) a b c sa = (op,sb) /\
  (!z. a = Var z ==> not_fresh_at sa z) /\
  (!z. b = Var z ==> not_fresh_at sa z) /\
  (!z. c = Var z ==> not_fresh_at sa z) /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  eval_operand c s = SOME vc /\ vc <> 0w /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  eval_operand op (t with vs_inst_idx := LENGTH sb.cs_current_insts) =
    SOME ((if is_mul then mulmod else addmod) va vb vc) /\
  (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==>
    lookup_var z (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME v) /\
  (!aid bl. FLOOKUP s.vs_allocas aid = SOME bl ==>
    FLOOKUP t.vs_allocas aid = SOME bl) /\
  t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `straight_fresh ((if is_mul then compile_mulmod else compile_addmod) a b c)` by
    (Cases_on `is_mul` >> simp[straight_fresh_compile_modular]) >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand a (drop_fresh sa s) = SOME va /\
   eval_operand b (drop_fresh sa s) = SOME vb /\
   eval_operand c (drop_fresh sa s) = SOME vc` by simp[eval_operand_drop_fresh] >>
  drule_all compile_modular_run >> simp[] >> strip_tac >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> gvs[]
QED

Theorem word_pow_actual_post:
  compile_pow_mod256 a b sa = (op,sb) /\
  (!z. a = Var z ==> not_fresh_at sa z) /\
  (!z. b = Var z ==> not_fresh_at sa z) /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  eval_operand op (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME (word_exp va vb) /\
  (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==>
    lookup_var z (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME v) /\
  (!aid bl. FLOOKUP s.vs_allocas aid = SOME bl ==> FLOOKUP t.vs_allocas aid = SOME bl) /\
  t.vs_memory = s.vs_memory /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `straight_fresh (compile_pow_mod256 a b)` by simp[straight_fresh_compile_modular] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand a (drop_fresh sa s) = SOME va /\
   eval_operand b (drop_fresh sa s) = SOME vb` by simp[eval_operand_drop_fresh] >>
  drule_all compile_pow_mod256_run >> strip_tac >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> gvs[]
QED

Theorem word_pow_cursor_length:
  compile_pow_mod256 a b sa = (op,sb) ==>
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 1
Proof
  strip_tac >>
  `straight_fresh (compile_pow_mod256 a b)` by simp[straight_fresh_compile_modular] >>
  drule_all (iffLR straight_fresh_def) >> strip_tac >>
  drule word_pow_emitted_shape >> simp[]
QED

Theorem word_modular_cursor_length:
  (if is_mul then compile_mulmod else compile_addmod) a b c sa = (op,sb) ==>
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 2
Proof
  strip_tac >>
  `straight_fresh ((if is_mul then compile_mulmod else compile_addmod) a b c)` by
    (Cases_on `is_mul` >> simp[straight_fresh_compile_modular]) >>
  drule_all (iffLR straight_fresh_def) >> strip_tac >>
  drule word_modular_emitted_shape >> simp[]
QED
