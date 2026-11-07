(* Fixed bytes to Address: reuse unsigned fixed-integer code, not its semantic post. *)
Theory bodyPtrTypeBuiltinsFixedAddressContinue
Ancestors bodyPtrTypeBuiltinsScalarSemantic bodyPtrTypeBuiltinsScalarContinue
  bodyPtrTypeBuiltinsScalarArithmetic bodyPtrTypeBuiltinsAddressContinue
  convertScalarBytesRun exprSimConvert exprLowering
  exprLoweringProps compileEnv vyperValue vyperValueOperation vyperTyping
  valueEncoding varsExt freshWrites venomState words byte rich_list list
  exprSimDefs exprSimHyps exprSimProps exprSimWordArgs loweringPosts
  bodyPtrDefs fragGasPathPtr ptrDiscipline emitHelperProps instIdxIndep finite_map
  vyperAST bodyPtrTypeBuiltinsUintCounted bodyPtrTypeBuiltinsUintContinue fragExec
  bodyPtrTypeBuiltinsSourceFrame

Theorem scalar_fixed_address_raw_semantic:
  LENGTH bs = m /\ m <= 32 /\
  compile_type_convert x (ConvBytesToAddress m) sa = (r,sb) /\
  eval_operand x ss = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
  fresh_vars_wrt sa ss ==>
  case convert_result cx (BaseT (BytesT (Fixed m))) (BaseT AddressT) (BytesV bs) of
    INL out => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 (BaseTV AddressT) out)
  | INR ex => (?msg. ex = Error (RuntimeError msg)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def] >>
  qmatch_goalsub_abbrev_tac `u < bound` >>
  `bound = 2 ** 160` by simp[Abbr `bound`] >>
  pop_assum SUBST_ALL_TAC >>
  Cases_on `u < 2 ** 160` >> simp[]
  >- (`u = w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32)` by simp[Abbr `u`] >>
      drule_all scalar_bytes_address_run_ok >> strip_tac >>
      goal_assum (drule_at Any) >>
      `u < dimword(:256)` by simp[Abbr `u`, wordsTheory.w2n_lt] >>
      `w2n (n2w u : bytes32) = u` by
        (pure_rewrite_tac[w2n_n2w] >> metis_tac[arithmeticTheory.LESS_MOD]) >>
      mp_tac (Q.INST [`x` |-> `n2w u : bytes32`] bytes_address_encoding) >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  `u = w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32)` by simp[Abbr `u`] >>
  drule_all scalar_bytes_address_run_abort >> simp[]
QED

Theorem scalar_fixed_address_typed_actual:
  evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv /\
  value_has_type tv v /\
  compile_type_convert x (ConvBytesToAddress m) sa = (r,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x ss = SOME (typed_val_to_w256 tv v) ==>
  case convert_result cx (BaseT (BytesT (Fixed m))) (BaseT AddressT) v of
    INL out => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 (BaseTV AddressT) out) /\
      (sf with vs_vars := ss.vs_vars) = ss /\
      (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
  | INR ex => (?msg. ex = Error (RuntimeError msg)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac >> gvs[] >>
  Cases_on `v` >> fs[value_has_type_def, AllCaseEqs()] >>
  `fresh_vars_wrt sa (drop_fresh sa ss)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh sa ss) = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV l))` by
    simp[eval_operand_drop_fresh] >>
  drule_all scalar_fixed_address_raw_semantic >>
  disch_then (qspec_then `cx` mp_tac) >>
  Cases_on `convert_result cx (BaseT (BytesT (Fixed m))) (BaseT AddressT) (BytesV l)` >>
  simp[] >> strip_tac >>
  `compile_type_convert x (ConvBytesToInt m F 160) sa = (r,sb)` by
    fs[GSYM convert_bytes_address_eq] >>
  drule scalar_fixed_int_replay >> disch_then (qspec_then `ss` mp_tac) >>
  simp[vars_ext_result_def] >> strip_tac >> gvs[]
  >- (rename1 `run_inst_seq (emitted_insts sa sb) ss = OK actual` >> conj_tac
      >- (fs[vars_ext_def] >>
          qpat_x_assum `actual = _ with vs_vars := _` SUBST1_TAC >>
          simp[eval_operand_vars_ext]) >>
      irule convert_bytes_int_runtime_frame >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any)) >> simp[]
QED

Theorem scalar_fixed_address_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert (BaseT AddressT) [e]) es /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  compile_type_convert x (mk_convert_op (expr_type e) (BaseT AddressT)) s1 = (op,sb) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v1 /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ local_ptrs_reserved cenv s1 /\
  sa.cs_next_var <= s1.cs_next_var /\ ~ctx_has_dalloca ctx /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
  ptr_val_ok cx (expr_type e) v1 x G tn t0 /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) (BaseT AddressT) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert (BaseT AddressT) [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT AddressT) v op H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >>
  `ann = BaseT AddressT` by (drule expr_body_pre_convert >> simp[]) >> gvs[] >>
  `m <= 32` by fs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `eval_operand x t0 = SOME (typed_val_to_w256 tv v1)` by
    fs[expr_post_def, expr_val_rel_def, is_word_type_def] >>
  `compile_type_convert x (ConvBytesToAddress m) s1 = (op,sb)` by
    fs[mk_convert_op_def, is_bytestring_type_def] >>
  drule_all scalar_fixed_address_typed_actual >>
  `compile_type_convert x (ConvBytesToInt m F 160) s1 = (op,sb)` by
    fs[GSYM convert_bytes_address_eq] >>
  drule_all scalar_fixed_int_compile_frame >> strip_tac >>
  `?bb. lookup_block t0.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts s1 sb) (DROP t0.vs_inst_idx bb.bb_instructions)` by
    (irule fn_code_emitted_prefix >> simp[] >> metis_tac[]) >>
  `op_prov G x = NONE /\ op_taint tn x = {}` by
    fs[ptr_val_ok_def, is_word_type_def] >>
  Cases_on `convert_result cx (BaseT (BytesT (Fixed m))) (BaseT AddressT) v1` >>
  simp[] >> strip_tac
  >- suspend "success"
  >> suspend "abort"
QED

Resume scalar_fixed_address_continuation[abort]:
  drule_all scalar_fixed_int_abort_zero_counted >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR y`,`ee`,`H`,`th`,`Abort Revert_abort (sf with vs_inst_idx := j)`] >>
  simp[exit_result_def, expr_exit_def]
QED

Resume scalar_fixed_address_continuation[success]:
  drule_all scalar_fixed_int_counted_success >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `sf = t0 with vs_vars := sf.vs_vars` by fs[venom_state_component_equality] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) sf` by
    (irule stmt_state_rel_readonly_vars_pc >>
     qexistsl_tac [`t0`,`s1`] >> simp[] >> reverse conj_tac
     >- fs[expr_post_def, stmt_state_rel_gas_obs] >>
     qpat_x_assum `sf = t0 with vs_vars := _` SUBST1_TAC >>
     simp[venom_state_component_equality]) >>
  `expr_post ctx func cenv cx
    (TypeBuiltin (BaseT AddressT) Convert (BaseT AddressT) [e])
    es sa sb s0 (ee with gas_obs := []) x' op
      (sf with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule scalar_suffix_expr_post >>
     simp[expr_type_def, is_word_type_def, stmt_state_rel_inst_idx, eval_op_inst_idx,
          vyperValueTheory.evaluate_type_def] >>
     conj_tac >- fs[stmt_state_rel_gas_obs] >>
     qexistsl_tac [`e`,`s1`,`t0`,`v1`,`x`] >> simp[lookup_var_def] >>
     conj_tac >- (fs[lookup_var_def] >> metis_tac[]) >>
     qpat_x_assum `sf = t0 with vs_vars := _` SUBST1_TAC >> simp[]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL x'`,`ee`,`H`,`th`,
    `OK (sf with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  gvs[ptr_val_ok_def, is_word_type_def, arithmeticTheory.ADD_COMM] >>
  qpat_x_assum `sf = t0 with vs_vars := _` SUBST_ALL_TAC >>
  gvs[venom_state_component_equality]
QED

Finalise scalar_fixed_address_continuation
