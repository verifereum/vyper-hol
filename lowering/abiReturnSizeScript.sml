(* The size guard and capped payload bound preceding return decoding. *)
Theory abiReturnSize
Ancestors
  exprLoweringProps emitHelperProps builtinProps builtinSimple arithmeticProps
  convertScalarChecks
  exprLowering emitHelper compileEnv venomExecSemantics venomState venomInst
  words list rich_list

Theorem abi_return_size_code:
  compile_return_value_decode lo cap sa = (hi,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  simp[compile_return_value_decode_def, builtinSimpleTheory.compile_select_def,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >>
  gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[same_blocks_def, emitted_insts_def, GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem abi_return_size_opcodes[local]:
  compile_return_value_decode lo cap sa = (hi,sb) ==>
  !i. MEM i (emitted_insts sa sb) ==>
    MEM i.inst_opcode [RETURNDATASIZE; LT; ISZERO; ASSERT; XOR; MUL]
Proof
  simp[compile_return_value_decode_def, builtinSimpleTheory.compile_select_def,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pure_rewrite_tac[emitted_insts_def] >>
  simp_tac (srw_ss()) [] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  simp_tac (srw_ss()) [mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem abi_return_size_frame:
  compile_return_value_decode lo cap sa = (hi,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t = s with vs_vars := t.vs_vars
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`emitted_insts sa sb`, `\x:string. F`, `s`, `t`]
    run_inst_seq_protected_frame) >> simp[] >>
  impl_tac >- (
    rpt strip_tac >>
    `MEM i.inst_opcode [RETURNDATASIZE; LT; ISZERO; ASSERT; XOR; MUL]` by
      metis_tac[abi_return_size_opcodes] >>
    Cases_on `i.inst_opcode = RETURNDATASIZE`
    >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
        simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()] >>
        strip_tac >> gvs[update_var_def, venom_state_component_equality]) >>
    irule (cj 1 step_pure_opcode_frame) >>
    goal_assum (drule_at Any) >> gvs[]) >> simp[]
QED

Theorem abi_return_size_run:
  compile_return_value_decode lo cap sa = (hi,sb) /\
  fresh_vars_wrt sa s /\ lo < dimword (:256) /\ cap < dimword (:256) /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  (if LENGTH s.vs_returndata < lo then
     ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
   else
     ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand hi t = SOME (n2w (MIN (LENGTH s.vs_returndata) cap)) /\
       fresh_vars_wrt sb t /\
       (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
       (?vars. t = s with vs_vars := vars))
Proof
  strip_tac >>
  qpat_x_assum `compile_return_value_decode _ _ _ = _` mp_tac >>
  simp[compile_return_value_decode_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `emit_void ASSERT [_] _ = (unit_result,_)` >>
  Cases_on `unit_result` >>
  rename1 `emit_op RETURNDATASIZE [] sa = (rds, sc1)` >>
  rename1 `emit_op LT [rds; Lit (n2w lo)] sc1 = (small, sc2)` >>
  rename1 `emit_op ISZERO [small] sc2 = (good, sc3)` >>
  rename1 `emit_void ASSERT [good] sc3 = ((),sc4)` >>
  rename1 `emit_op LT [rds; Lit (n2w cap)] sc4 = (cmp, sc5)` >>
  `?u. run_inst_seq (emitted_insts sa sc1) s = OK u /\
       eval_operand rds u = SOME (n2w (LENGTH s.vs_returndata)) /\
       fresh_vars_wrt sc1 u /\
       (!op w. eval_operand op s = SOME w ==> eval_operand op u = SOME w)` by
    (drule emit_op_read0_correct >>
     disch_then (qspecl_then [`\z. n2w (LENGTH z.vs_returndata)`, `s`] mp_tac) >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def] >> metis_tac[]) >>
  `eval_operand (Lit (n2w lo)) u = SOME (n2w lo)` by simp[eval_operand_def] >>
  drule_all emit_op_LT_correct >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  `eval_operand small v = SOME (bool_to_word (LENGTH s.vs_returndata < lo))` by
    gvs[w2n_n2w] >>
  imp_res_tac emit_op_extends >> imp_res_tac compile_select_extends >>
  drule_all scalar_assert_zero_extends >> strip_tac >>
  `run_inst_seq (emitted_insts sa sc2) s = OK v /\
   sc2.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc2` by
    (drule_all run_inst_seq_chain >> simp[]) >>
  Cases_on `LENGTH s.vs_returndata < lo` >> simp[]
  >- ( `eval_operand small v = SOME 1w` by gvs[bool_to_word_def] >>
       `1w <> (0w:bytes32)` by simp[] >>
       drule_all scalar_assert_zero_abort >>
       disch_then (qx_choose_then `a` assume_tac) >>
       `run_inst_seq (emitted_insts sa sc4) s = Abort Revert_abort a /\
        sc4.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc4` by
         (drule_all run_inst_seq_chain >> simp[]) >>
       `emitted_insts sa sb = emitted_insts sa sc4 ++ emitted_insts sc4 sb` by
         (irule emitted_insts_prefix_split >> simp[] >>
          qexists_tac `emitted_insts sc4 sc5 ++ emitted_insts sc5 sb` >>
          metis_tac[APPEND_ASSOC]) >>
       qexists_tac `a` >> simp[run_inst_seq_append_err] ) >>
  `eval_operand small v = SOME 0w` by gvs[bool_to_word_def] >>
  drule_all scalar_assert_zero_ok >>
  disch_then (qx_choose_then `w` strip_assume_tac) >>
  `eval_operand rds w = SOME (n2w (LENGTH s.vs_returndata))` by metis_tac[] >>
  `eval_operand (Lit (n2w cap)) w = SOME (n2w cap)` by simp[eval_operand_def] >>
  drule_all emit_op_LT_correct >>
  disch_then (qx_choose_then `x` strip_assume_tac) >>
  `eval_operand rds x = SOME (n2w (LENGTH s.vs_returndata))` by metis_tac[] >>
  `?t. run_inst_seq (emitted_insts sc5 sb) x = OK t /\
    eval_operand hi t = SOME
      (if w2n (n2w (LENGTH s.vs_returndata):bytes32) < w2n (n2w cap:bytes32)
       then n2w (LENGTH s.vs_returndata) else n2w cap) /\
    fresh_vars_wrt sb t /\
    (!op z. eval_operand op x = SOME z ==> eval_operand op t = SOME z)` by
    (irule compile_select_correct >> simp[] >>
     qexistsl_tac [`cmp`, `Lit (n2w cap)`, `rds`] >> simp[eval_operand_def]) >>
  `run_inst_seq (emitted_insts sa sc4) s = OK w /\
   sc4.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc4` by
    (drule_all run_inst_seq_chain >> simp[]) >>
  `run_inst_seq (emitted_insts sa sc5) s = OK x /\
   sc5.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc5` by
    (drule_all run_inst_seq_chain >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK t` by
    (drule_all run_inst_seq_chain >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  conj_tac >- (gvs[w2n_n2w] >> simp[arithmeticTheory.MIN_DEF] >>
               Cases_on `LENGTH s.vs_returndata < cap` >> simp[]) >>
  reverse conj_tac
  >- (qexists_tac `t.vs_vars` >> irule abi_return_size_frame >>
      goal_assum (drule_at Any) >>
      qexistsl_tac [`cap`, `hi`, `lo`] >>
      simp[compile_return_value_decode_def, comp_bind_def, comp_ignore_bind_def]) >>
  rpt strip_tac >>
  qpat_x_assum `!op z. eval_operand op x = SOME z ==> _` irule >>
  qpat_x_assum `!op z. eval_operand op w = SOME z ==> _` irule >>
  qpat_x_assum `!op z. eval_operand op v = SOME z ==> _` irule >>
  qpat_x_assum `!op z. eval_operand op u = SOME z ==> _` irule >>
  simp[]
QED
