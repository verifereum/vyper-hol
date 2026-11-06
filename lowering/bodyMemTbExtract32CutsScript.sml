(* Compiler and counted snapshot boundaries for extract32. *)
Theory bodyMemTbExtract32Cuts
Ancestors
  bodyMemTbExtract32Source fragGasSeqMem fragExec exprLoweringProps
  builtinBytes emitHelper emitHelperProps compileEnv venomInst rich_list
  exprLowering exprSimHyps exprCallbackContracts exprCallBounds

Theorem extract32_snapshot_shape:
  compile_bytestring_src src sa = ((len,data),sb) ==>
  LENGTH (emitted_insts sa sb) = 2 /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  simp[compile_bytestring_src_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem extract32_snapshot_gas_path:
  compile_bytestring_src src sa = ((len_op,data_op),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w len /\
  b + 32 < dimword (:256) /\ len < dimword (:256) /\
  b + 32 + len <= s.vs_alloca_next /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path_mem ctx func s 0
        (OK (t with vs_inst_idx := s.vs_inst_idx + 2)) /\
      eval_operand len_op t = SOME (n2w len) /\
      eval_operand data_op t = SOME (n2w (b + 32)) /\
      w2n (n2w (b + 32):bytes32) + w2n (n2w len:bytes32) <= t.vs_alloca_next /\
      (t with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!x. len_op = Var x \/ data_op = Var x ==> not_fresh_at sb x)
Proof
  strip_tac >> drule_all extract32_source_snapshot >> strip_tac >>
  drule extract32_snapshot_shape >> strip_tac >>
  qexists_tac `t` >>
  conj_tac >- (drule_all run_inst_seq_gas_path_mem >> simp[]) >>
  metis_tac[]
QED

Theorem extract32_compile_equations:
  compile_expr cenv ty (TypeBuiltin ann Extract32 ret [src;off]) sa = (vv,sb) ==>
  ?src_op s1 len data s2 off_op s3 raw s4 op.
    lower_value compile_expr cenv (expr_type src) src sa = (src_op,s1) /\
    compile_bytestring_src src_op s1 = ((len,data),s2) /\
    lower_value compile_expr cenv ty off s2 = (off_op,s3) /\
    compile_extract32_load len data off_op s3 = (raw,s4) /\
    compile_clamp_basetype raw ret s4 = (op,sb) /\
    vv = StackValue ann op
Proof
  simp[exprSimHypsTheory.compile_expr_type_builtin_dispatch,
       Once exprLoweringTheory.compile_expr_def,
       exprLoweringTheory.compile_type_builtin_dispatch_body_def] >>
  `!e aty. MEM e [src;off] ==>
     lower_value (expr_child_callback (expr_size off + (expr_size src + 2)) compile_expr)
       cenv aty e = lower_value compile_expr cenv aty e` by
    (rpt strip_tac >> irule lower_value_callback_contract >>
     irule expr_child_callback_agrees >> simp[] >> gvs[] >> simp[]) >>
  simp[] >>
  Cases_on `lower_value compile_expr cenv (expr_type src) src sa` >>
  rename1 `_ = (src_op,s1)` >>
  Cases_on `compile_bytestring_src src_op s1` >>
  rename1 `_ = (ld,s2)` >> PairCases_on `ld` >>
  Cases_on `lower_value compile_expr cenv ty off s2` >>
  rename1 `_ = (off_op,s3)` >>
  Cases_on `compile_extract32_load ld0 ld1 off_op s3` >>
  rename1 `_ = (raw,s4)` >>
  Cases_on `compile_clamp_basetype raw ret s4` >>
  simp[as_stack_val_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem extract32_compile_cuts:
  lower_value compile_expr cenv (expr_type src) src sa = (src_op,s1) /\
  compile_bytestring_src src_op s1 = ((len,data),s2) /\
  lower_value compile_expr cenv ty off s2 = (off_op,s3) /\
  compile_extract32_load len data off_op s3 = (raw,s4) /\
  compile_clamp_basetype raw ret s4 = (op,sb) /\
  fn_has_code sa sb func ==>
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\
  ci_mono s3 s4 /\ ci_mono s4 sb /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 s4 func /\
  fn_has_code s4 sb func /\ fn_has_code s1 sb func /\
  fn_has_code s2 sb func /\ fn_has_code s3 sb func
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\
   ci_mono s3 s4 /\ ci_mono s4 sb` by
    metis_tac[ci_mono_lower_value_compile_expr, ci_mono_compile_bytestring_src,
              ci_mono_compile_extract32_load, ci_mono_compile_clamp_basetype, pairTheory.SND] >>
  simp[] >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
   cs_extends s3 s4 /\ cs_extends s4 sb` by fs[ci_mono_def] >>
  `cs_extends s3 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends s2 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED
